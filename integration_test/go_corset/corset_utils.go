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

package gocorset

import (
	"fmt"
	"sort"
	"strings"

	"github.com/LFDT-Lineth/zkc/pkg/ir"
	"github.com/LFDT-Lineth/zkc/pkg/ir/air"
	"github.com/LFDT-Lineth/zkc/pkg/schema"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/bus"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/lookup"
	"github.com/LFDT-Lineth/zkc/pkg/schema/register"
	gc_trace "github.com/LFDT-Lineth/zkc/pkg/trace"
	gocorset_kb "github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
	"github.com/consensys/gnark-crypto/ecc"
	gnark_kb "github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"
)

// ====================== Loom bridge =========================
//
// zkc pads every module of a trace at the front, to a power of two, with rows
// that satisfy its constraints, and checks them on all rows (lookups, buses)
// or on the rows where they are well defined (vanishing constraints, see
// AddConstraintInLoom). A zkc trace is therefore a loom trace as is: loom
// evaluates on the same rows, cyclically, and the boundary rows are excluded
// by Lagrange selectors.

// CorsetBridge translates a zkc air.Schema into a loom board.Builder.
type CorsetBridge struct {
	Builder *board.Builder
	Schema  *air.Schema[gocorset_kb.Element]
	// Lookups collects the lookup constraints, built together by
	// BuildLookups, grouped by target.
	Lookups *arguments.Lookups
}

// NewCorsetBridge initialises a bridge.
func NewCorsetBridge(
	builder *board.Builder,
	s *air.Schema[gocorset_kb.Element],
) *CorsetBridge {
	return &CorsetBridge{Builder: builder, Schema: s, Lookups: arguments.NewLookups()}
}

// SetupModules creates one loom Module per zkc schema module and registers it
// in the builder. Must be called before ScanConstraints. Modules with no
// registers are skipped: they hold no column and no constraint.
func (b *CorsetBridge) SetupModules() {
	for _, m := range b.Schema.Modules().Collect() {
		if m.Width() == 0 {
			continue
		}
		if m.IsNative() {
			panic(fmt.Sprintf("SetupModules: native module %q is not supported", m.Name()))
		}
		b.Builder.AddModule(board.NewModule(m.Name()))
	}
}

// loomModuleName returns the loom module name for a schema module ID.
func (b *CorsetBridge) loomModuleName(moduleID uint) string {
	return b.Schema.Module(moduleID).Name()
}

// colName returns the loom column name "module.register" for a (moduleID,
// registerID) pair.
func (b *CorsetBridge) colName(moduleID uint, regID register.Id) string {
	mod := b.Schema.Module(moduleID)
	return qualifyColumnName(mod.Name(), mod.Register(regID).Name())
}

// regExpr returns the loom leaf of a register: a constant for zkc's constant
// registers, a setup column for a static module, a committed column otherwise.
func (b *CorsetBridge) regExpr(moduleID uint, regID register.Id, shift int) expr.Expr {
	mod := b.Schema.Module(moduleID)
	reg := mod.Register(regID)
	if reg.IsU1Const() {
		var val gnark_kb.Element
		val.SetUint64(uint64(reg.ConstValue()))
		return expr.Const(val)
	}
	name := b.colName(moduleID, regID)
	var opts []expr.LeafOption
	if shift != 0 {
		opts = append(opts, expr.WithShift(shift))
	}
	if mod.IsStatic() {
		return expr.Setup(name, opts...)
	}
	return expr.Col(name, opts...)
}

// toGnarkElement converts a zkc koalabear field element to the gnark-crypto
// representation used by loom.
func toGnarkElement(e gocorset_kb.Element) gnark_kb.Element {
	var result gnark_kb.Element
	result.SetUint64(uint64(e.ToUint32()))
	return result
}

// termToExpr recursively converts a zkc AIR term of module moduleID to a loom
// expr.Expr. Shifts are cyclic: the callers exclude the rows where they wrap.
func (b *CorsetBridge) termToExpr(t air.Term[gocorset_kb.Element], moduleID uint) expr.Expr {
	switch v := t.(type) {

	case *air.ColumnAccess[gocorset_kb.Element]:
		return b.regExpr(moduleID, v.Register(), v.RelativeShift())

	case *air.Constant[gocorset_kb.Element]:
		return expr.Const(toGnarkElement(v.Value))

	case *air.Add[gocorset_kb.Element]:
		if len(v.Args) == 0 {
			return expr.Const(gnark_kb.Element{})
		}
		result := b.termToExpr(v.Args[0], moduleID)
		for _, arg := range v.Args[1:] {
			result = result.Add(b.termToExpr(arg, moduleID))
		}
		return result

	case *air.Sub[gocorset_kb.Element]:
		if len(v.Args) == 0 {
			return expr.Const(gnark_kb.Element{})
		}
		result := b.termToExpr(v.Args[0], moduleID)
		for _, arg := range v.Args[1:] {
			result = result.Sub(b.termToExpr(arg, moduleID))
		}
		return result

	case *air.Mul[gocorset_kb.Element]:
		if len(v.Args) == 0 {
			return expr.Const(gnark_kb.One())
		}
		result := b.termToExpr(v.Args[0], moduleID)
		for _, arg := range v.Args[1:] {
			result = result.Mul(b.termToExpr(arg, moduleID))
		}
		return result

	default:
		panic(fmt.Sprintf("termToExpr: unsupported AIR term type %T", t))
	}
}

// vectorTable returns the loom table of a lookup vector, with its selector
// (none when the vector has none).
func (b *CorsetBridge) vectorTable(v lookup.Vector) board.CTable {
	t := board.CTable{Table: board.NewTable(b.loomModuleName(v.Module), len(v.Registers))}
	for j, r := range v.Registers {
		t.In[j] = b.regExpr(v.Module, r, 0)
	}
	if v.HasSelector() {
		t.Sel = b.regExpr(v.Module, v.Selector.Unwrap(), 0)
	}
	return t
}

// AddConstraintInLoom translates a single zkc constraint into the loom
// builder. Returns an error for unsupported constraint forms; panics only for
// truly unexpected term types.
func (b *CorsetBridge) AddConstraintInLoom(name string, corsetCS schema.Constraint[gocorset_kb.Element]) error {

	switch cs := corsetCS.(type) {

	// ── Vanishing (polynomial identity) ───────────────────────────────────
	case *air.VanishingConstraint[gocorset_kb.Element]:
		modName := b.loomModuleName(cs.Context)
		m, ok := b.Builder.Modules[modName]
		if !ok {
			return fmt.Errorf("constraint %q: module %q not found in builder", name, modName)
		}
		relation := b.termToExpr(cs.Constraint.Term, cs.Context)

		if cs.Domain.IsEmpty() {
			// Global: zkc checks rows [Start, N−End), where every shift is
			// well defined (no wrap). Loom evaluates on all N rows, so the
			// first Start and the last End rows are excluded by
			// (1 − L_i)·(1 − L_{N−1−j}).
			bounds := cs.Bounds(cs.Context)
			one := expr.Const(gnark_kb.One())
			for i := range int(bounds.Start) {
				relation = relation.Mul(one.Sub(m.LagrangeCol(i)))
			}
			for j := range int(bounds.End) {
				relation = relation.Mul(one.Sub(m.LagrangeColRelative(j)))
			}
			m.AssertZero(relation)
			return nil
		}

		// Local: holds on one row, counted from the end when negative.
		if position := cs.Domain.Unwrap(); position >= 0 {
			m.AssertZeroAt(relation, position)
		} else {
			m.AssertZeroRelativeAt(relation, -position-1)
		}
		return nil

	// ── Lookup (subset argument) ──────────────────────────────────────────
	// Collected, and built by BuildLookups with the others into its target.
	case *air.LookupConstraint[gocorset_kb.Element]:
		if len(cs.Sources) != 1 || len(cs.Targets) != 1 {
			return fmt.Errorf("constraint %q: lookup of %d sources into %d targets, want 1 and 1", name, len(cs.Sources), len(cs.Targets))
		}
		if cs.Sources[0].Len() == 0 {
			return fmt.Errorf("constraint %q: empty lookup vector", name)
		}
		if err := b.Lookups.Add(b.vectorTable(cs.Sources[0]), b.vectorTable(cs.Targets[0])); err != nil {
			return fmt.Errorf("constraint %q: %w", name, err)
		}
		return nil

	// ── Bus (multiset balance) ────────────────────────────────────────────
	case *air.BusConstraint[gocorset_kb.Element]:
		// A port sends (receives) its registers on every row where its
		// selector is nonzero; zkc's selectors are boolean, so the selector
		// is the row's multiplicity.
		ports := func(ps []bus.Port) ([]board.Table, []expr.Expr) {
			tables, sels := make([]board.Table, len(ps)), make([]expr.Expr, len(ps))
			for i, p := range ps {
				t := b.vectorTable(lookup.FilteredVector(p.Module, p.Selector, p.Registers...))
				tables[i], sels[i] = t.Table, t.Sel
			}
			return tables, sels
		}
		S, selS := ports(cs.Sends)
		R, selR := ports(cs.Receives)
		return arguments.Bus(b.Builder, selS, selR, S, R)

	// ── Range constraint ──────────────────────────────────────────────────
	case *air.RangeConstraint[gocorset_kb.Element]:
		modName := b.loomModuleName(cs.Context)
		S := board.Column{Module: modName, In: b.regExpr(cs.Context, cs.Source, 0)}
		return arguments.Range(b.Builder, S, uint64(1)<<cs.Bitwidth)

	default:
		return fmt.Errorf("constraint %q: unknown constraint type %T", name, corsetCS)
	}
}

// ====================== Scanning =========================

// BuildLookups adds the collected lookups to the builder, grouped by target.
// ScanConstraints calls it; call it once after adding constraints one by one
// with AddConstraintInLoom.
func (b *CorsetBridge) BuildLookups() error {
	return b.Lookups.Build(b.Builder)
}

// ScanConstraints translates all constraints in the air schema into the loom
// builder attached to bridge, then builds the collected lookups. Constraints
// are processed in deterministic (lexicographic Lisp-name) order. Panics on
// the first error.
func ScanConstraints(bridge *CorsetBridge) {
	s := bridge.Schema
	corsetCSS := s.Constraints().Collect()

	indices := make([]int, len(corsetCSS))
	for i := range indices {
		indices[i] = i
	}

	names := make([]string, len(corsetCSS))
	for i, cs := range corsetCSS {
		names[i] = cs.Lisp(s).String(false)
	}

	sort.SliceStable(indices, func(i, j int) bool {
		return names[indices[i]] < names[indices[j]]
	})

	for _, idx := range indices {
		if err := bridge.AddConstraintInLoom(names[idx], corsetCSS[idx]); err != nil {
			panic(fmt.Sprintf("ScanConstraints: %v", err))
		}
	}
	if err := bridge.BuildLookups(); err != nil {
		panic(fmt.Sprintf("ScanConstraints: %v", err))
	}
}

// ====================== Trace loading =========================

// PaddingAtLeast returns zkc's next-power-of-two padding strategy with a
// floor: every module is padded (at the front, with zkc's padding rows) to a
// power of two of at least minRows rows. A size-oblivious verifier needs it,
// whose dynamic modules must be larger than twice their largest shift.
func PaddingAtLeast(minRows uint) ir.PaddingStrategy {
	return func(height, multiplier uint) uint {
		return max(uint(ecc.NextPowerOfTwo(uint64(height))), minRows) * multiplier
	}
}

// MinModuleRows is the smallest module size: loom's FRI has no level of size 1.
const MinModuleRows = 2

// ShardToLoom converts a zkc trace shard into a loom trace. Dynamic modules
// are taken from the shard, whose heights are powers of two (zkc's
// next-power-of-two padding). A module of fewer than MinModuleRows rows is
// padded at the front by repeating its first row: a one-row module holds only
// zkc's padding row (zkc pads at the front, with rows satisfying the module's
// constraints), and an empty module becomes rows of zeros.
// Static modules are not traced by zkc: their columns are built from the
// schema (see StaticColumns), and are setup columns in loom.
func ShardToLoom(
	shard gc_trace.Shard[gocorset_kb.Element],
	airSchema *air.Schema[gocorset_kb.Element],
) (trace.Trace, error) {
	t := trace.New()
	for i := range shard.Width() {
		scMod := airSchema.Module(i)
		if scMod.Width() == 0 {
			continue
		}
		if scMod.IsStatic() {
			cols, err := StaticColumns(scMod.Name(), registerNames(scMod), scMod.StaticContents())
			if err != nil {
				return trace.Trace{}, err
			}
			for name, col := range cols {
				t.SetBase(name, col)
			}
			continue
		}
		mod := shard.Module(i)
		if mod.Name() != scMod.Name() {
			return trace.Trace{}, fmt.Errorf("ShardToLoom: shard module %d is %q, schema module is %q", i, mod.Name(), scMod.Name())
		}
		h := mod.Height()
		if ecc.NextPowerOfTwo(uint64(max(h, 1))) != uint64(max(h, 1)) {
			return trace.Trace{}, fmt.Errorf("ShardToLoom: module %q has height %d, not a power of two", mod.Name(), h)
		}
		n := max(h, MinModuleRows)
		pad := n - h // front rows repeating row 0
		for j := range mod.Width() {
			key := qualifyColumnName(mod.Name(), mod.Descriptor().Columns[j].Name)
			poly := make([]gnark_kb.Element, n)
			if col := mod.Column(j); col != nil && h > 0 {
				for r := range n {
					poly[r] = toGnarkElement(col.Get(max(r, pad) - pad))
				}
			}
			t.SetBase(key, poly)
		}
	}
	return t, nil
}

// StaticColumns returns the loom columns of a static zkc module, from its rows
// (contents[r][c] is column c of row r). They are padded to a power of two by
// repeating the first row, which leaves the module's set of rows unchanged:
// static modules are lookup tables.
func StaticColumns(moduleName string, columns []string, contents [][]gocorset_kb.Element) (map[string][]gnark_kb.Element, error) {
	rows := len(contents)
	if rows == 0 {
		return nil, fmt.Errorf("StaticColumns: static module %q is empty", moduleName)
	}
	n := int(ecc.NextPowerOfTwo(uint64(rows)))
	res := make(map[string][]gnark_kb.Element, len(columns))
	for c, name := range columns {
		poly := make([]gnark_kb.Element, n)
		for r := range n {
			row := contents[0]
			if r < rows {
				row = contents[r]
			}
			if len(row) != len(columns) {
				return nil, fmt.Errorf("StaticColumns: static module %q row %d has %d values, want %d", moduleName, r, len(row), len(columns))
			}
			poly[r] = toGnarkElement(row[c])
		}
		res[qualifyColumnName(moduleName, name)] = poly
	}
	return res, nil
}

func registerNames(mod schema.Module[gocorset_kb.Element]) []string {
	regs := mod.Registers()
	res := make([]string, len(regs))
	for i, r := range regs {
		res[i] = r.Name()
	}
	return res
}

// ====================== Size setting =========================

// SetSize sets the size of every module of the program from the trace.
func SetSize(program *board.Program, tr trace.Trace) {
	moduleSizes := map[string]int{}
	for colName, col := range tr.Base {
		idx := strings.IndexByte(colName, '.')
		if idx < 0 {
			// root module column (no dot) — maps to module with empty name
			moduleSizes[""] = len(col)
		} else {
			modName := colName[:idx]
			moduleSizes[modName] = len(col)
		}
	}
	for name, cm := range program.Modules {
		n, ok := moduleSizes[name]
		if !ok {
			continue
		}
		cm.N = n
		cm.D = fft.NewDomain(uint64(n))
		program.Modules[name] = cm
	}
}
