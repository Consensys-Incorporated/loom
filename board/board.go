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

package board

import (
	"fmt"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/proof"
)

type LogupBus = proof.LogupBus
type Proof = proof.Proof

type ExposedEntry = proof.ExposedEntry
type ExposedValue = proof.ExposedValue

// NewLogupBus returns the bus asserting that the logup totals sum to zero.
func NewLogupBus(totals []string) LogupBus {
	return LogupBus{Totals: totals}
}

// ColumnRef identifies a column by its bare name and the module it belongs to.
// The module name is needed to recover the column's polynomial size from
// program.Modules, which is required for multi-degree FRI (commitments are
// grouped per size).
type ColumnRef struct {
	Name   string
	Module string
	Field  field.Kind
}

// Builder accumulates the modules, their relations, and the rounds of the
// protocol (see rounds.go).
type Builder struct {
	Modules  map[string]*Module
	LogupBus []LogupBus
	rounds   []builderRound
}

func NewBuilder() Builder {
	var res Builder
	res.Modules = make(map[string]*Module)
	res.LogupBus = make([]LogupBus, 0)
	return res
}

func (b *Builder) AddModule(m Module) {
	b.Modules[m.Name] = &m
}

func (b *Builder) AddLogupBus(cm LogupBus) {
	b.LogupBus = append(b.LogupBus, cm)
}

func (b *Builder) AssertEqualAt(module string, A, B expr.Expr, i int) error {
	m, ok := b.Modules[module]
	if !ok {
		return fmt.Errorf("module %s not found in the list", module)
	}
	m.AssertEqualAt(A, B, i)
	b.Modules[module] = m
	return nil
}

func (b *Builder) AssertZero(module string, relation expr.Expr) error {
	m, ok := b.Modules[module]
	if !ok {
		return fmt.Errorf("module %s not found in the list", module)
	}
	m.AssertZero(relation)
	b.Modules[module] = m
	return nil
}

type Table struct {
	Module string
	In     []expr.Expr
}

func NewTable(module string, size int) Table {
	return Table{Module: module, In: make([]expr.Expr, size)}
}

type Column struct {
	Module string
	In     expr.Expr
	Field  field.Kind
}

func (c Column) FieldKind() field.Kind {
	if c.In == nil {
		return c.Field
	}
	return field.Join(c.Field, expr.FieldOf(c.In))
}

type Output struct {
	Module  string
	ColName string
}

func (b *Builder) addExposeValuesConstraint(module string, E expr.Expr, sel, out string) {
	selExpr := expr.Col(sel)
	outExpr := expr.Exposed(out)
	rel := E.Mul(selExpr).Sub(outExpr)
	m := b.Modules[module]
	m.AssertZero(rel)
	b.Modules[module] = m
}

func (b *Builder) AddExposeValuesStep(r int, module string, E expr.Expr, selector, out string, idx []int) {
	m := b.Modules[module]
	ctx := ExposeEntriesCtx{Idx: idx, N: m.N}
	pvStep := ProverStep{
		Ctx:  ctx,
		Ins:  []expr.Expr{E},
		Outs: []string{out},
		Step: ExposeEntriesStep,
	}
	b.AddStepAt(r, pvStep)

	genSel := SelectorGen{Idx: idx, Name: selector}
	m.GenCol = append(m.GenCol, genSel)
	b.Modules[module] = m
	b.addExposeValuesConstraint(module, E, selector, out)
}

func (b *Builder) addExposeIthValueConstraint(module string, E expr.Expr, output string, pos int) {
	m := b.Modules[module]
	v := expr.Exposed(output)
	m.AssertEqualAt(E, v, pos)
}

// AddExposeLastEntryStep syntactic sugar for AddExposeRelativeIthValueStep(module, E, out, 0)
func (b *Builder) AddExposeLastEntryStep(r int, module string, E expr.Expr, out string) {
	ctx := ExposeRelativeIthValueCtx{Pos: 0, Module: module}
	pvStep := ProverStep{
		Ctx:  ctx,
		Ins:  []expr.Expr{E},
		Outs: []string{out},
		Step: ExposeRelativeIthValueStep,
	}
	b.AddStepAt(r, pvStep)
	b.addExposeRelativeIthValuePublicConstraint(module, E, out, 0)
}

// AddExposeIthValue adds a constraint Lagrange_pos * (expr - expr[pos]), and stores expr[pos] in the proof so the verifier has access to it
// the 1 entry column expr[pos] is registered in the trace
func (b *Builder) AddExposeRelativeIthValueStep(r int, module string, E expr.Expr, out string, pos int) {
	ctx := ExposeRelativeIthValueCtx{Pos: pos, Module: module}
	pvStep := ProverStep{
		Ctx:  ctx,
		Ins:  []expr.Expr{E},
		Outs: []string{out},
		Step: ExposeRelativeIthValueStep,
	}
	b.AddStepAt(r, pvStep)
	b.addExposeRelativeIthValuePublicConstraint(module, E, out, pos)
}

func (b *Builder) addExposeRelativeIthValuePublicConstraint(module string, E expr.Expr, output string, pos int) {
	m := b.Modules[module]
	v := expr.Exposed(output)
	m.AssertEqualRelativeAt(E, v, pos)
}

// AddExposeIthValueStep adds a constraint Lagrange_pos * (expr - expr[pos]), and stores expr[pos] in the proof so the verifier has access to it
// the 1 entry column expr[pos] is registered in the trace
func (b *Builder) AddExposeIthValueStep(r int, module string, E expr.Expr, out string, pos int) {
	ctx := ExposeIthValueCtx{Pos: pos}
	pvStep := ProverStep{
		Ctx:  ctx,
		Ins:  []expr.Expr{E},
		Outs: []string{out},
		Step: ExposeIthValue,
	}
	b.AddStepAt(r, pvStep)
	b.addExposeIthValueConstraint(module, E, out, pos)
}

// AddLookupMultiplicityStep registers the computation of the multiplicity
// columns of the lookup {S[j] | selS[j] != 0} ⊂ {T[k] | selT[k] != 0}, where
// S[j], T[k] are tuples of the same width. selS and selT may be nil (all ones).
// One output column per target, named MultiplicityChunkName(output, k).
func (b *Builder) AddLookupMultiplicityStep(r int, selS, selT []expr.Expr, S, T [][]expr.Expr, output string) {
	ctx := LMCtx{NbSources: len(S), NbTargets: len(T), Width: len(S[0]), HasSelS: selS != nil, HasSelT: selT != nil}
	ins := append(append([]expr.Expr(nil), selS...), selT...)
	for _, s := range S {
		ins = append(ins, s...)
	}
	for _, t := range T {
		ins = append(ins, t...)
	}
	outs := make([]string, len(T))
	for i := range T {
		outs[i] = constants.MultiplicityChunkName(output, i)
	}
	b.AddStepAt(r, NewProverStep(ins, outs, LookupMultiplicityStep, ctx))
}

func (b *Builder) addGrandProductConstraint(module string, N, D expr.Expr, output string) {
	m := b.Modules[module]
	gp := expr.Col(output)
	gpshifted := expr.Col(output, expr.WithShift(1))
	recurrence := gpshifted.Mul(D).Sub(gp.Mul(N))
	m.AssertZero(recurrence)

	// GP[0] = 1
	boundary := gp.Sub(expr.Const(koalabear.One()))
	m.AssertZeroAt(boundary, 0)
}

func (b *Builder) AddGrandProductStep(r int, module string, N, D expr.Expr, output string) {
	gpStep := NewProverStep([]expr.Expr{N, D}, []string{output}, GrandProductStep, GPCtx{})
	b.AddStepAt(r, gpStep)
	b.addGrandProductConstraint(module, N, D, output)
}
