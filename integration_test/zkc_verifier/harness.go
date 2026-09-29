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
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/trace"

	"github.com/LFDT-Lineth/zkc/pkg/util/field"
	"github.com/LFDT-Lineth/zkc/pkg/util/source"
	kb "github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/compiler"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/compiler/ast"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/compiler/codegen"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/constraints"
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
}

// NewProgram translates a zkc binary into a loom program.
func NewProgram(binf *constraints.BinaryFile[kb.Element]) (*Program, error) {
	schema := binf.AirConstraints()
	builder := board.NewBuilder()
	if _, err := NewBridge(&builder, &schema); err != nil {
		return nil, err
	}
	pg, err := board.Compile(&builder)
	if err != nil {
		return nil, fmt.Errorf("board.Compile: %w", err)
	}
	return &Program{Binary: binf, Loom: pg}, nil
}

// Trace executes the program on input (a zkc JSON input map) and returns the
// loom trace and the program outputs (raw big-endian bytes per output memory).
// The program's module sizes are updated to match the trace.
func (p *Program) Trace(input map[string][]byte) (trace.Trace, map[string][]byte, error) {
	input, _ = vm.FilterInputs(p.Binary.RawProgram(), input)
	cfg := vm.DEFAULT_TRACE_CONFIG.WithParallelism(false)
	outputs, tr, errs := p.Binary.Trace(input, cfg)
	if len(errs) > 0 {
		return trace.Trace{}, nil, fmt.Errorf("trace: %w", errors.Join(errs...))
	}
	schema := p.Binary.AirConstraints()
	lt, err := TraceToLoom(tr, &schema)
	if err != nil {
		return trace.Trace{}, nil, err
	}
	SetSize(&p.Loom, lt)
	return lt, outputs, nil
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
