// Copyright Consensys Software Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
// the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0

// Package zkcverifier bridges zkc (github.com/LFDT-Lineth/zkc) programs into
// loom, as a basis for a loom verifier written in zkc.
//
// It targets the zkc AIR semantics of v1.2.32 and later, which differ from the
// go-corset v1.2.16 semantics handled in integration_test/go_corset:
//   - every module is front-padded to a power of two, and constraints hold on
//     padding rows, so no IS_REAL selector is needed;
//   - a global constraint holds on rows [Start, H-End) of its bounds;
//   - lookups relate registers, not arbitrary terms.
package zkcverifier

import (
	"fmt"
	"math/bits"
	"sort"
	"strings"

	gnark_kb "github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"

	"github.com/LFDT-Lineth/zkc/pkg/ir/air"
	"github.com/LFDT-Lineth/zkc/pkg/schema"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/lookup"
	"github.com/LFDT-Lineth/zkc/pkg/schema/register"
	gc_trace "github.com/LFDT-Lineth/zkc/pkg/trace"
	kb "github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
)

// Bridge translates a zkc air.Schema into a loom board.Builder.
type Bridge struct {
	Builder *board.Builder
	Schema  *air.Schema[kb.Element]

	// lookups groups the lookup constraints by target vectors, see
	// addLookups.
	lookups     map[string]*lookupGroup
	lookupOrder []string

	// natives are the #[native] function modules, by module name.
	natives map[string]*nativeModule
}

// lookupGroup is the union of the sources of every lookup constraint sharing
// the same target vectors.
type lookupGroup struct {
	targets []lookup.Vector
	sources []lookup.Vector
}

// NewBridge creates one loom module per non-empty schema module and translates
// every constraint. Constraints are translated in lexicographic Lisp order so
// the resulting program is deterministic. Native function modules are defined
// by the gadget registered under their name.
func NewBridge(builder *board.Builder, s *air.Schema[kb.Element], gadgets Gadgets) (*Bridge, error) {
	b := &Bridge{Builder: builder, Schema: s, lookups: map[string]*lookupGroup{}, natives: map[string]*nativeModule{}}
	for _, m := range s.RawModules() {
		if m.Width() == 0 {
			continue
		}
		builder.AddModule(board.NewModule(m.Name()))
	}
	// Gadgets are defined once every module exists, since they may refer to
	// other modules (e.g. a gadget looking up permutations in p2_perm).
	for _, m := range s.RawModules() {
		if m.Width() == 0 || !m.IsNative() {
			continue
		}
		g, ok := gadgets[m.Name()]
		if !ok {
			return nil, fmt.Errorf("native module %q has no gadget", m.Name())
		}
		nm := &nativeModule{gadget: g, io: map[string]bool{}}
		for _, r := range m.Registers() {
			name := qualify(m.Name(), r.Name())
			switch {
			case r.IsInput():
				nm.inputs = append(nm.inputs, name)
			case r.IsOutput():
				nm.outputs = append(nm.outputs, name)
			default:
				continue
			}
			nm.io[name] = true
		}
		if err := g.Define(builder, m.Name(), nm.inputs, nm.outputs); err != nil {
			return nil, fmt.Errorf("native module %q: %w", m.Name(), err)
		}
		b.natives[m.Name()] = nm
	}

	css := s.Constraints().Collect()
	names := make([]string, len(css))
	for i, cs := range css {
		names[i] = cs.Lisp(s).String(false)
	}
	order := make([]int, len(css))
	for i := range order {
		order[i] = i
	}
	sort.Slice(order, func(i, j int) bool { return names[order[i]] < names[order[j]] })

	for _, i := range order {
		if err := b.addConstraint(names[i], css[i]); err != nil {
			return nil, err
		}
	}
	if err := b.addLookups(); err != nil {
		return nil, err
	}
	return b, nil
}

func (b *Bridge) moduleName(id uint) string {
	return b.Schema.Module(id).Name()
}

func (b *Bridge) module(id uint) (*board.Module, error) {
	name := b.moduleName(id)
	m, ok := b.Builder.Modules[name]
	if !ok {
		return nil, fmt.Errorf("module %q not found in builder", name)
	}
	return m, nil
}

func (b *Bridge) colName(moduleID uint, regID register.Id) string {
	return qualify(b.moduleName(moduleID), b.Schema.Module(moduleID).Register(regID).Name())
}

func qualify(moduleName, registerName string) string {
	if moduleName == "" {
		return registerName
	}
	return moduleName + "." + registerName
}

// regExpr returns the loom expression reading register regID of moduleID at
// the given row shift. Constant registers are inlined, and registers of static
// modules are setup columns.
func (b *Bridge) regExpr(moduleID uint, regID register.Id, shift int) expr.Expr {
	mod := b.Schema.Module(moduleID)
	reg := mod.Register(regID)
	if reg.IsU1Const() {
		var v gnark_kb.Element
		v.SetUint64(uint64(reg.ConstValue()))
		return expr.Const(v)
	}
	var opts []expr.LeafOption
	if shift != 0 {
		opts = append(opts, expr.WithShift(shift))
	}
	name := b.colName(moduleID, regID)
	if mod.IsStatic() {
		return expr.Setup(name, opts...)
	}
	return expr.Col(name, opts...)
}

func toGnark(e kb.Element) gnark_kb.Element {
	var r gnark_kb.Element
	r.SetUint64(uint64(e.ToUint32()))
	return r
}

// termToExpr converts an AIR term. Loom evaluates shifts cyclically; the
// wrapped rows are exactly those excluded by the constraint's bounds.
func (b *Bridge) termToExpr(t air.Term[kb.Element], moduleID uint) expr.Expr {
	switch v := t.(type) {
	case *air.ColumnAccess[kb.Element]:
		return b.regExpr(moduleID, v.Register(), v.RelativeShift())
	case *air.Constant[kb.Element]:
		return expr.Const(toGnark(v.Value))
	case *air.Add[kb.Element]:
		return b.fold(v.Args, moduleID, gnark_kb.Element{}, expr.Expr.Add)
	case *air.Sub[kb.Element]:
		return b.fold(v.Args, moduleID, gnark_kb.Element{}, expr.Expr.Sub)
	case *air.Mul[kb.Element]:
		return b.fold(v.Args, moduleID, gnark_kb.One(), expr.Expr.Mul)
	default:
		panic(fmt.Sprintf("termToExpr: unsupported AIR term type %T", t))
	}
}

func (b *Bridge) fold(args []air.Term[kb.Element], moduleID uint, empty gnark_kb.Element,
	op func(expr.Expr, expr.Expr) expr.Expr) expr.Expr {
	if len(args) == 0 {
		return expr.Const(empty)
	}
	res := b.termToExpr(args[0], moduleID)
	for _, arg := range args[1:] {
		res = op(res, b.termToExpr(arg, moduleID))
	}
	return res
}

func (b *Bridge) addConstraint(name string, cs schema.Constraint[kb.Element]) error {
	one := expr.Const(gnark_kb.One())

	switch c := cs.(type) {
	case air.VanishingConstraint[kb.Element]:
		vc := c.Unwrap()
		m, err := b.module(vc.Context)
		if err != nil {
			return fmt.Errorf("constraint %q: %w", name, err)
		}
		relation := b.termToExpr(vc.Constraint.Term, vc.Context)

		if vc.Domain.IsEmpty() {
			// Global: exclude the first Start and the last End rows.
			bounds := c.Bounds(vc.Context)
			for i := range int(bounds.Start) {
				relation = relation.Mul(one.Sub(m.LagrangeCol(i)))
			}
			for j := range int(bounds.End) {
				relation = relation.Mul(one.Sub(m.LagrangeColRelative(j)))
			}
			m.AssertZero(relation)
			return nil
		}
		// Local: row d, or row H+d when d is negative (H = padded height = N).
		if d := vc.Domain.Unwrap(); d >= 0 {
			m.AssertZeroAt(relation, d)
		} else {
			m.AssertZeroRelativeAt(relation, -d-1)
		}
		return nil

	case air.LookupConstraint[kb.Element]:
		lc := c.Unwrap()
		if len(lc.Sources) == 0 || len(lc.Targets) == 0 || lc.Sources[0].Len() == 0 {
			return fmt.Errorf("constraint %q: empty lookup", name)
		}
		key := vectorsKey(lc.Targets)
		g, ok := b.lookups[key]
		if !ok {
			g = &lookupGroup{targets: lc.Targets}
			b.lookups[key] = g
			b.lookupOrder = append(b.lookupOrder, key)
		}
		g.sources = append(g.sources, lc.Sources...)
		return nil

	case air.RangeConstraint[kb.Element]:
		rc := c.Unwrap()
		modName := b.moduleName(rc.Context)
		for i, src := range rc.Sources {
			col := board.Column{Module: modName, In: b.regExpr(rc.Context, src, 0)}
			if err := arguments.Range(b.Builder, col, uint64(1)<<rc.Bitwidths[i]); err != nil {
				return fmt.Errorf("constraint %q: %w", name, err)
			}
		}
		return nil

	case air.BusConstraint[kb.Element]:
		return fmt.Errorf("constraint %q: bus constraints are not supported (avoid #[global] functions)", name)

	default:
		return fmt.Errorf("constraint %q: unknown constraint type %T", name, cs)
	}
}

// addLookups translates the grouped lookup constraints. zkc emits one lookup
// per source (e.g. one per range-checked limb, or one per call site), many of
// them into the same target; proving them as one union lookup per target gives
// the target a single multiplicity and logup column instead of one per source.
func (b *Bridge) addLookups() error {
	for _, key := range b.lookupOrder {
		g := b.lookups[key]
		width := int(g.sources[0].Len())
		filtered := false
		for _, v := range append(append([]lookup.Vector(nil), g.sources...), g.targets...) {
			filtered = filtered || v.HasSelector()
			if int(v.Len()) != width {
				return fmt.Errorf("lookup into %s: inconsistent widths", key)
			}
		}
		S, selS := b.lookupTables(g.sources, width)
		T, selT := b.lookupTables(g.targets, width)
		var err error
		switch {
		case width == 1 && !filtered:
			err = arguments.LookupUnion(b.Builder, tablesToColumns(S), tablesToColumns(T))
		case width == 1:
			err = arguments.CLookupUnion(b.Builder, selS, selT, tablesToColumns(S), tablesToColumns(T))
		case !filtered:
			err = arguments.LookupUnionTuple(b.Builder, S, T)
		default:
			err = arguments.CLookupUnionTuple(b.Builder, selS, selT, S, T)
		}
		if err != nil {
			return fmt.Errorf("lookup into %s: %w", key, err)
		}
	}
	return nil
}

// vectorsKey identifies lookup vectors by module, selector and registers.
func vectorsKey(vs []lookup.Vector) string {
	var sb strings.Builder
	for _, v := range vs {
		fmt.Fprintf(&sb, "[%d", v.Module)
		if v.HasSelector() {
			fmt.Fprintf(&sb, " sel=%d", v.Selector.Unwrap().Unwrap())
		}
		for i := range v.Len() {
			fmt.Fprintf(&sb, " %d", v.Ith(i).Unwrap())
		}
		sb.WriteString("]")
	}
	return sb.String()
}

func (b *Bridge) lookupTables(vs []lookup.Vector, width int) ([]board.Table, []expr.Expr) {
	tables := make([]board.Table, len(vs))
	sels := make([]expr.Expr, len(vs))
	for i, v := range vs {
		tables[i] = board.NewTable(b.moduleName(v.Module), width)
		for j := range width {
			tables[i].In[j] = b.regExpr(v.Module, v.Ith(uint(j)), 0)
		}
		if v.HasSelector() {
			sels[i] = b.regExpr(v.Module, v.Selector.Unwrap(), 0)
		} else {
			sels[i] = expr.Const(gnark_kb.One())
		}
	}
	return tables, sels
}

func tablesToColumns(ts []board.Table) []board.Column {
	cols := make([]board.Column, len(ts))
	for i, t := range ts {
		cols[i] = board.Column{Module: t.Module, In: t.In[0]}
	}
	return cols
}

// TraceToLoom converts a single-shard expanded zkc trace into a loom trace.
// Expanded modules are already padded to a power-of-two height. Static modules
// are absent from the trace; their contents are taken from the schema. Native
// modules keep only their I/O columns, and their gadgets fill the rest.
func (b *Bridge) TraceToLoom(tr gc_trace.Trace[kb.Element]) (trace.Trace, error) {
	s := b.Schema
	if len(tr) != 1 {
		return trace.Trace{}, fmt.Errorf("TraceToLoom: expected 1 shard, got %d", len(tr))
	}
	shard := tr[0]
	res := trace.New()
	for i := range shard.Width() {
		mod := shard.Module(i)
		h := mod.Height()
		if mod.Width() == 0 {
			continue
		}
		if sm := s.RawModules()[i]; sm.IsStatic() {
			if err := staticToLoom(&res, sm); err != nil {
				return trace.Trace{}, err
			}
			continue
		}
		if h == 0 || bits.OnesCount(h) != 1 {
			return trace.Trace{}, fmt.Errorf("TraceToLoom: module %q has height %d, not a power of two", mod.Name(), h)
		}
		native := b.natives[mod.Name()]
		for j := range mod.Width() {
			name := qualify(mod.Name(), mod.Descriptor().Columns[j].Name)
			if native != nil && !native.io[name] {
				continue // internal register of the zkc reference body
			}
			col := mod.Column(j)
			poly := make([]gnark_kb.Element, h)
			for r := range h {
				poly[r] = toGnark(col.Get(r))
			}
			res.SetBase(name, poly)
		}
		if native != nil {
			if err := native.gadget.Fill(res, mod.Name(), native.inputs, native.outputs); err != nil {
				return trace.Trace{}, fmt.Errorf("native module %q: %w", mod.Name(), err)
			}
		}
	}
	return res, nil
}

func staticToLoom(res *trace.Trace, m air.Module[kb.Element]) error {
	rows := m.StaticContents()
	h := uint(len(rows))
	if h == 0 || bits.OnesCount(h) != 1 {
		return fmt.Errorf("static module %q has %d rows, not a power of two", m.Name(), h)
	}
	for j, reg := range m.Registers() {
		poly := make([]gnark_kb.Element, h)
		for r, row := range rows {
			if len(row) != len(m.Registers()) {
				return fmt.Errorf("static module %q row %d has width %d, expected %d", m.Name(), r, len(row), len(m.Registers()))
			}
			poly[r] = toGnark(row[j])
		}
		res.SetBase(qualify(m.Name(), reg.Name()), poly)
	}
	return nil
}

// SetSize sets each program module's size N from the trace.
func SetSize(program *board.Program, tr trace.Trace) {
	for name, cm := range program.Modules {
		for colName, col := range tr.Base {
			if moduleOf(colName) == name {
				cm.N = len(col)
				cm.D = fft.NewDomain(uint64(cm.N))
				program.Modules[name] = cm
				break
			}
		}
	}
}

func moduleOf(colName string) string {
	for i := range len(colName) {
		if colName[i] == '.' {
			return colName[:i]
		}
	}
	return ""
}
