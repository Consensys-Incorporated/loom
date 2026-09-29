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

package zkcverifier

import (
	"errors"
	"fmt"
	"os"
	"sort"
	"strings"

	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	loomfield "github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/protocol"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/trace"

	"github.com/LFDT-Lineth/zkc/pkg/ir"
	"github.com/LFDT-Lineth/zkc/pkg/util/field"
	kb "github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
	"github.com/LFDT-Lineth/zkc/pkg/util/source"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/compiler"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/compiler/ast"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/compiler/codegen"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/constraints"
	zkc_util "github.com/LFDT-Lineth/zkc/pkg/zkc/util"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/vm"
)

// Field is the zkc field configuration used throughout: KoalaBear with 16-bit
// registers.
var Field = field.KOALABEAR_16

// CompileFiles compiles zkc source files (includes are resolved relative to
// each file) into a binary file.
func CompileFiles(filenames ...string) (*constraints.BinaryFile[kb.Element], error) {
	files := make([]source.File, len(filenames))
	for i, name := range filenames {
		data, err := os.ReadFile(name)
		if err != nil {
			return nil, err
		}
		files[i] = *source.NewSourceFile(name, data)
	}
	config := codegen.DEFAULT_CONFIG.Field(Field)
	prog, _, errs := compiler.Compile(Field, config.GetMaxStaticHeight(), files...)
	if len(errs) > 0 {
		return nil, fmt.Errorf("compile: %s", formatSyntaxErrors(errs))
	}
	raw, errs := ast.Compile(prog, config)
	if len(errs) > 0 {
		return nil, fmt.Errorf("codegen: %s", formatSyntaxErrors(errs))
	}
	return constraints.NewBinaryFile[kb.Element](nil, nil, raw), nil
}

// Program is a zkc program compiled to a loom program.
type Program struct {
	Binary *constraints.BinaryFile[kb.Element]
	Loom   board.Program
	bridge *Bridge
}

// NewProgram translates a zkc binary into a loom program. gadgets define the
// program's #[native] functions.
func NewProgram(binf *constraints.BinaryFile[kb.Element], gadgets Gadgets) (*Program, error) {
	schema := binf.AirConstraints()
	builder := board.NewBuilder()
	bridge, err := NewBridge(&builder, &schema, gadgets)
	if err != nil {
		return nil, err
	}
	pg, err := board.Compile(&builder)
	if err != nil {
		return nil, fmt.Errorf("board.Compile: %w", err)
	}
	return &Program{Binary: binf, Loom: pg, bridge: bridge}, nil
}

// Trace executes the program on input (a zkc JSON input map) and returns the
// loom trace and the program outputs (raw big-endian bytes per output memory).
// The program's module sizes are updated to match the trace.
func (p *Program) Trace(input map[string][]byte) (trace.Trace, map[string][]byte, error) {
	input, _ = vm.FilterInputs(p.Binary.RawProgram(), input)
	cfg := vm.DEFAULT_TRACE_CONFIG.WithParallelism(false).WithPadding(minHeightPadding)
	outputs, tr, errs := p.Binary.Trace(input, cfg)
	if len(errs) > 0 {
		return trace.Trace{}, nil, fmt.Errorf("trace: %w", errors.Join(errs...))
	}
	lt, err := p.bridge.TraceToLoom(tr)
	if err != nil {
		return trace.Trace{}, nil, err
	}
	SetSize(&p.Loom, lt)
	return lt, outputs, nil
}

// MinModuleHeight is the smallest module height produced by Trace. Loom's
// multi-degree FRI cannot introduce a size-1 level (its introduction round
// would equal the number of folding rounds), so every module is padded to at
// least this height.
const MinModuleHeight = 4

// minHeightPadding is zkc's next-power-of-two padding, with a floor of
// MinModuleHeight rows.
func minHeightPadding(height, multiplier uint) uint {
	return max(ir.NextPowerOfTwoPadding(height, 1), MinModuleHeight) * multiplier
}

// ProveAndVerify runs setup, prove and verify (with full FRI) on the trace.
func (p *Program) ProveAndVerify(tr trace.Trace) (proof.Proof, error) {
	pk, vk, err := loom.Setup(tr, p.Loom)
	if err != nil {
		return proof.Proof{}, fmt.Errorf("setup: %w", err)
	}
	statement := loom.Statement{Program: p.Loom, VerificationKey: vk, PublicInputs: public.Inputs{}}
	prf, err := loom.Prove(statement, loom.Witness{Trace: tr, ProvingKey: pk})
	if err != nil {
		return proof.Proof{}, fmt.Errorf("prove: %w", err)
	}
	if err := loom.Verify(statement, prf); err != nil {
		return proof.Proof{}, fmt.Errorf("verify: %w", err)
	}
	return prf, nil
}

// ModuleStats describes the size of one loom module.
type ModuleStats struct {
	Name    string
	N       int
	Columns int
}

// Cells returns N times the number of columns.
func (m ModuleStats) Cells() int { return m.N * m.Columns }

// Stats returns the per-module sizes of the trace, sorted by decreasing cells.
func Stats(tr trace.Trace) []ModuleStats {
	byModule := map[string]*ModuleStats{}
	for name, col := range tr.Base {
		mod := moduleOf(name)
		s, ok := byModule[mod]
		if !ok {
			s = &ModuleStats{Name: mod, N: len(col)}
			byModule[mod] = s
		}
		s.Columns++
	}
	res := make([]ModuleStats, 0, len(byModule))
	for _, s := range byModule {
		res = append(res, *s)
	}
	sort.Slice(res, func(i, j int) bool {
		if res[i].Cells() != res[j].Cells() {
			return res[i].Cells() > res[j].Cells()
		}
		return res[i].Name < res[j].Name
	})
	return res
}

// FormatStats renders module statistics as an aligned table.
func FormatStats(stats []ModuleStats) string {
	var sb strings.Builder
	total := 0
	fmt.Fprintf(&sb, "%-40s %10s %8s %12s\n", "module", "N", "columns", "cells")
	for _, s := range stats {
		fmt.Fprintf(&sb, "%-40s %10d %8d %12d\n", s.Name, s.N, s.Columns, s.Cells())
		total += s.Cells()
	}
	fmt.Fprintf(&sb, "%-40s %10s %8s %12d\n", "TOTAL", "", "", total)
	return sb.String()
}

func formatSyntaxErrors(errs []source.SyntaxError) string {
	msgs := make([]string, len(errs))
	for i, err := range errs {
		msgs[i] = err.Error()
	}
	return strings.Join(msgs, "; ")
}

// Result is the outcome of Run.
type Result struct {
	// Outputs are the raw big-endian bytes of each output memory.
	Outputs map[string][]byte
	// Stats are the per-module sizes of the loom trace.
	Stats []ModuleStats
	// Leaf is what verifying a loom proof of this trace costs in leaf
	// hashing, per query.
	Leaf LeafCost
	// LeafModules breaks Leaf.Elements down by module.
	LeafModules []LeafBreakdown
}

// LeafCost is the per-query leaf hashing work of verifying a loom proof: every
// committed polynomial (setup, trace, logup, AIR-quotient chunk) is opened at
// every query, as one row pair per (tree, group).
type LeafCost struct {
	// Elements is the number of field elements opened per query: 2 per base
	// polynomial and 12 per extension polynomial.
	Elements int
	// Perms is the number of Poseidon2 permutations hashing them: one sponge
	// of 3 + Elements(group) elements per (tree, group).
	Perms int
}

// LeafBreakdown is the per-query leaf elements of one module, by column kind.
type LeafBreakdown struct {
	Module                       string
	Trace, Logup, Mult, Quotient int
}

// Total returns the module's leaf elements per query.
func (l LeafBreakdown) Total() int { return l.Trace + l.Logup + l.Mult + l.Quotient }

// LeafBreakdownOf returns the leaf elements per query of each module, sorted
// by decreasing total.
func LeafBreakdownOf(program board.Program) []LeafBreakdown {
	per := map[string]*LeafBreakdown{}
	get := func(m string) *LeafBreakdown {
		if per[m] == nil {
			per[m] = &LeafBreakdown{Module: m}
		}
		return per[m]
	}
	for _, r := range program.Rounds {
		for _, c := range r.Staged {
			w := 2
			if c.Field == loomfield.Ext {
				w = 12
			}
			l := get(c.Module)
			switch {
			case strings.Contains(c.Name, "logup"):
				l.Logup += w
			case strings.HasPrefix(c.Name, "Mult_"):
				l.Mult += w
			default:
				l.Trace += w
			}
		}
	}
	layout := protocol.BuildLayout(program, 0)
	for name := range layout.AIRChunkSlot {
		get(moduleOf(name)).Quotient += 12
	}
	res := make([]LeafBreakdown, 0, len(per))
	for _, l := range per {
		res = append(res, *l)
	}
	sort.Slice(res, func(i, j int) bool {
		if res[i].Total() != res[j].Total() {
			return res[i].Total() > res[j].Total()
		}
		return res[i].Module < res[j].Module
	})
	return res
}

// LeafCostOf computes the leaf cost of a program whose module sizes are set.
func LeafCostOf(program board.Program) LeafCost {
	layout := protocol.BuildLayout(program, 0)
	type key struct{ tree, group int }
	width := map[key]int{}
	add := func(s protocol.Slot) {
		w := 2
		if s.Field == loomfield.Ext {
			w = 12
		}
		width[key{s.TreeIdx, s.GroupIdx}] += w
	}
	for _, s := range layout.ColSlot {
		add(s)
	}
	for _, s := range layout.AIRChunkSlot {
		add(s)
	}
	var res LeafCost
	for _, w := range width {
		res.Elements += w
		res.Perms += (3 + w + 15) / 16
	}
	return res
}

// Measure compiles the zkc files and executes them on a JSON input, without
// proving. It returns the outputs and the trace sizes.
func Measure(input []byte, files ...string) (Result, error) {
	return MeasureWith(input, nil, files...)
}

// MeasureWith is Measure with gadgets for the program's #[native] functions.
func MeasureWith(input []byte, gadgets Gadgets, files ...string) (Result, error) {
	binf, err := CompileFiles(files...)
	if err != nil {
		return Result{}, err
	}
	pg, err := NewProgram(binf, gadgets)
	if err != nil {
		return Result{}, err
	}
	in, err := zkc_util.ParseJsonInputFile(input)
	if err != nil {
		return Result{}, err
	}
	tr, outputs, err := pg.Trace(in)
	if err != nil {
		return Result{}, err
	}
	return Result{Outputs: outputs, Stats: Stats(tr), Leaf: LeafCostOf(pg.Loom), LeafModules: LeafBreakdownOf(pg.Loom)}, nil
}

// Run compiles the zkc files, executes them on a JSON input (zkc input file
// format), and proves and verifies the trace with full FRI.
func Run(input []byte, files ...string) (Result, error) {
	return RunWith(input, nil, files...)
}

// RunWith is Run with gadgets for the program's #[native] functions.
func RunWith(input []byte, gadgets Gadgets, files ...string) (Result, error) {
	binf, err := CompileFiles(files...)
	if err != nil {
		return Result{}, err
	}
	pg, err := NewProgram(binf, gadgets)
	if err != nil {
		return Result{}, err
	}
	in, err := zkc_util.ParseJsonInputFile(input)
	if err != nil {
		return Result{}, err
	}
	tr, outputs, err := pg.Trace(in)
	if err != nil {
		return Result{}, err
	}
	res := Result{Outputs: outputs, Stats: Stats(tr), Leaf: LeafCostOf(pg.Loom), LeafModules: LeafBreakdownOf(pg.Loom)}
	if _, err := pg.ProveAndVerify(tr); err != nil {
		return res, err
	}
	return res, nil
}
