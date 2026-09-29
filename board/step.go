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
	"sync"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/trace"
)

type Step func([]expr.Expr, []string, trace.Trace, *Program, *proof.Proof, *sync.Mutex, StepContext) error

type StepContext any

type ProverStep struct {
	Ctx  StepContext
	Ins  []expr.Expr
	Outs []string
	Step Step
}

func (ps *ProverStep) Execute(trace trace.Trace, prog *Program, proof *proof.Proof, mu *sync.Mutex) error {
	step := ps.Step
	return step(ps.Ins, ps.Outs, trace, prog, proof, mu, ps.Ctx)
}

func NewProverStep(ins []expr.Expr, outs []string, step Step, ctx StepContext) ProverStep {
	return ProverStep{
		Ins:  ins,
		Outs: outs,
		Step: step,
		Ctx:  ctx,
	}
}

func shouldRunExtStep(prog *Program, out string) bool {
	return prog.ColumnFields[out] == field.Ext
}

type ExposeEntriesCtx struct {
	Idx []int // indices of the entries to make public
	N   int
}

func ExposeEntriesStep(ins []expr.Expr, outs []string, t trace.Trace, prog *Program, proof *proof.Proof, mu *sync.Mutex, ctx StepContext) error {

	_ctx, ok := ctx.(ExposeEntriesCtx)
	if !ok {
		return fmt.Errorf("[ExposeEntriesStep] wrong context type")
	}

	out := outs[0]
	C := ins[0]
	if shouldRunExtStep(prog, out) {
		res, err := poly.BuildPointwiseEvaluationMixed(t.Base, t.Ext, prog.ColumnFields, C, mu)
		if err != nil {
			return err
		}

		var publicColumnInfo ExposedValue
		// publicColumnInfo.N = _ctx.N
		publicColumnInfo.Entries = make([]ExposedEntry, len(_ctx.Idx))
		for j, i := range _ctx.Idx {
			publicColumnInfo.Entries[j].Idx = i
			publicColumnInfo.Entries[j].SetExt(res[i])
		}
		proof.ExposedValues[out] = publicColumnInfo

		sparseCol := make(trace.ExtPolynomial, _ctx.N)
		for _, i := range _ctx.Idx {
			sparseCol[i].Set(&res[i])
		}
		if err := t.PutExt(out, sparseCol); err != nil {
			panic(fmt.Sprintf("[ExposeEntriesStep] register public column %s: %v", out, err))
		}

		return nil
	}

	res, err := poly.BuildPointwiseEvaluation(t.Base, C, mu)
	if err != nil {
		return err
	}

	var publicColumnInfo ExposedValue
	// publicColumnInfo.N = _ctx.N
	publicColumnInfo.Entries = make([]ExposedEntry, len(_ctx.Idx))
	for j, i := range _ctx.Idx {
		publicColumnInfo.Entries[j].Idx = i
		publicColumnInfo.Entries[j].SetBase(res[i])
	}
	proof.ExposedValues[out] = publicColumnInfo

	// The constraint L_pos*(E - Public(out))=0 requires Public(out) to be the sparse
	// polynomial with E[pos] at index pos and 0 elsewhere, matching what computePublicColumns
	// reconstructs on the verifier side via Lagrange interpolation.
	sparseCol := make([]koalabear.Element, _ctx.N)
	for _, i := range _ctx.Idx {
		sparseCol[i].Set(&res[i])
	}
	if err := t.PutBase(out, sparseCol); err != nil {
		panic(fmt.Sprintf("[ExposeIthValue] register public column %s: %v", out, err))
	}

	return nil
}

type ExposeRelativeIthValueCtx struct {
	Module string
	Pos    int // relative position of the value to pick in a column -> the position module.N - 1 - Pos. It allows to refer to N, so N can be modified
}

// ExposeRelativeIthValueStep adds a constraint Lagrange_pos * (expr - expr[pos]), and stores expr[pos] in the proof so the verifier has access to it
func ExposeRelativeIthValueStep(ins []expr.Expr, outs []string, t trace.Trace, pg *Program, proof *proof.Proof, mu *sync.Mutex, ctx StepContext) error {

	_ctx, ok := ctx.(ExposeRelativeIthValueCtx)
	if !ok {
		return fmt.Errorf("[PickLocalValueStep] wrong context type")
	}

	out := outs[0]
	C := ins[0]
	m := pg.Modules[_ctx.Module]
	pos := m.N - 1 - _ctx.Pos
	if shouldRunExtStep(pg, out) {
		res, err := poly.BuildPointwiseEvaluationMixed(t.Base, t.Ext, pg.ColumnFields, C, mu)
		if err != nil {
			return err
		}

		var publicColumnInfo ExposedValue
		// publicColumnInfo.N = m.N
		publicColumnInfo.Entries = make([]ExposedEntry, 1)
		publicColumnInfo.Entries[0].Idx = pos
		publicColumnInfo.Entries[0].SetExt(res[pos])
		proof.ExposedValues[out] = publicColumnInfo

		sparseCol := make(trace.ExtPolynomial, m.N)
		sparseCol[pos].Set(&res[pos])
		if err := t.PutExt(out, sparseCol); err != nil {
			panic(fmt.Sprintf("[ExposeRelativeIthValueStep] register public column %s: %v", out, err))
		}

		return nil
	}

	res, err := poly.BuildPointwiseEvaluation(t.Base, C, mu)
	if err != nil {
		return err
	}

	var publicColumnInfo ExposedValue
	// publicColumnInfo.N = m.N
	publicColumnInfo.Entries = make([]ExposedEntry, 1)
	publicColumnInfo.Entries[0].Idx = pos
	publicColumnInfo.Entries[0].SetBase(res[pos])
	proof.ExposedValues[out] = publicColumnInfo

	// The constraint L_pos*(E - Public(out))=0 requires Public(out) to be the sparse
	// polynomial with E[m.N-1-_ctx.Pos] at index m.N-1-_ctx.Pos and 0 elsewhere, matching what computePublicColumns
	// reconstructs on the verifier side via Lagrange interpolation.
	sparseCol := make([]koalabear.Element, m.N)
	sparseCol[pos].Set(&res[pos])
	if err := t.PutBase(out, sparseCol); err != nil {
		panic(fmt.Sprintf("[ExposeIthValue] register public column %s: %v", out, err))
	}

	return nil
}

type ExposeIthValueCtx struct {
	Module string
	Pos    int // position of the value to pick in a column
}

// ExposeIthValue adds a constraint Lagrange_pos * (expr - expr[pos]), and stores expr[pos] in the proof so the verifier has access to it
func ExposeIthValue(ins []expr.Expr, outs []string, t trace.Trace, pg *Program, proof *proof.Proof, mu *sync.Mutex, ctx StepContext) error {

	_ctx, ok := ctx.(ExposeIthValueCtx)
	if !ok {
		return fmt.Errorf("[PickLocalValueStep] wrong context type")
	}

	out := outs[0]
	C := ins[0]
	m := pg.Modules[_ctx.Module]
	if shouldRunExtStep(pg, out) {
		res, err := poly.BuildPointwiseEvaluationMixed(t.Base, t.Ext, pg.ColumnFields, C, mu)
		if err != nil {
			return err
		}

		var publicColumnInfo ExposedValue
		// publicColumnInfo.N = m.N
		publicColumnInfo.Entries = make([]ExposedEntry, 1)
		publicColumnInfo.Entries[0].Idx = _ctx.Pos
		publicColumnInfo.Entries[0].SetExt(res[_ctx.Pos])
		proof.ExposedValues[out] = publicColumnInfo

		sparseCol := make(trace.ExtPolynomial, m.N)
		sparseCol[_ctx.Pos].Set(&res[_ctx.Pos])
		if err := t.PutExt(out, sparseCol); err != nil {
			panic(fmt.Sprintf("[ExposeIthValue] register public column %s: %v", out, err))
		}

		return nil
	}

	res, err := poly.BuildPointwiseEvaluation(t.Base, C, mu)
	if err != nil {
		return err
	}

	var publicColumnInfo ExposedValue
	// publicColumnInfo.N = m.N
	publicColumnInfo.Entries = make([]ExposedEntry, 1)
	publicColumnInfo.Entries[0].Idx = _ctx.Pos
	publicColumnInfo.Entries[0].SetBase(res[_ctx.Pos])
	proof.ExposedValues[out] = publicColumnInfo

	// The constraint L_pos*(E - Public(out))=0 requires Public(out) to be the sparse
	// polynomial with E[pos] at index pos and 0 elsewhere, matching what computePublicColumns
	// reconstructs on the verifier side via Lagrange interpolation.
	sparseCol := make([]koalabear.Element, m.N)
	sparseCol[_ctx.Pos].Set(&res[_ctx.Pos])
	if err := t.PutBase(out, sparseCol); err != nil {
		panic(fmt.Sprintf("[ExposeIthValue] register public column %s: %v", out, err))
	}

	return nil
}

type LMCtx struct {
	NbSources, NbTargets, Width int
	HasSelS, HasSelT            bool
}

// LookupMultiplicityStep computes the multiplicity columns of a (possibly
// conditional) tuple lookup on the raw tuples, see poly.BuildLookupMultiplicities.
// ins: [ selS (if HasSelS) || selT (if HasSelT) || S (row-major tuples) || T (row-major tuples) ]
func LookupMultiplicityStep(ins []expr.Expr, outs []string, t trace.Trace, _ *Program, proof *proof.Proof, mu *sync.Mutex, ctx StepContext) error {

	_ctx, ok := ctx.(LMCtx)
	if !ok {
		return fmt.Errorf("[LookupMultiplicityStep] wrong context type")
	}

	var selS, selT []expr.Expr
	if _ctx.HasSelS {
		selS, ins = ins[:_ctx.NbSources], ins[_ctx.NbSources:]
	}
	if _ctx.HasSelT {
		selT, ins = ins[:_ctx.NbTargets], ins[_ctx.NbTargets:]
	}
	tuples := func(n int) [][]expr.Expr {
		res := make([][]expr.Expr, n)
		for i := range res {
			res[i], ins = ins[:_ctx.Width], ins[_ctx.Width:]
		}
		return res
	}
	S := tuples(_ctx.NbSources)
	T := tuples(_ctx.NbTargets)

	res, err := poly.BuildLookupMultiplicities(t.Base, selS, S, selT, T, mu)
	if err != nil {
		return err
	}
	for i := range T {
		if err := t.PutBase(outs[i], res[i]); err != nil {
			panic(fmt.Sprintf("[LookupMultiplicityStep] register multiplicity column %s: %v", outs[i], err))
		}
	}

	return nil
}

type LogUpCtx struct{}

// _LogUpStep computes the running sum M/E where
// ins[0] = E, ins[1] = M
func LogUpStep(ins []expr.Expr, outs []string, t trace.Trace, prog *Program, proof *proof.Proof, mu *sync.Mutex, _ StepContext) error {

	out := outs[0]
	E := ins[0]
	M := ins[1]

	if shouldRunExtStep(prog, out) {
		res, err := poly.BuildLogupMixed(t.Base, t.Ext, prog.ColumnFields, E, M, mu)
		if err != nil {
			return err
		}
		if err := t.PutExt(out, res); err != nil {
			panic(fmt.Sprintf("[_LogUpStep] register logup column %s: %v", out, err))
		}
		return nil
	}

	res, err := poly.BuildLogup(t.Base, E, M, mu)
	if err != nil {
		return err
	}
	if err := t.PutBase(out, res); err != nil {
		panic(fmt.Sprintf("[_LogUpStep] register logup column %s: %v", out, err))
	}

	return nil
}

type GPCtx struct{}

// _GrandProductStep computes the running product N/D where
// ins[0] = N, ins[1] = D
func GrandProductStep(ins []expr.Expr, outs []string, t trace.Trace, prog *Program, proof *proof.Proof, mu *sync.Mutex, _ StepContext) error {

	out := outs[0]
	N := ins[0]
	D := ins[1]

	if shouldRunExtStep(prog, out) {
		res, err := poly.BuildGrandProductMixed(t.Base, t.Ext, prog.ColumnFields, N, D, mu)
		if err != nil {
			return err
		}
		if err := t.PutExt(out, res); err != nil {
			panic(fmt.Sprintf("[_GrandProductStep] register grand product column %s: %v", out, err))
		}
		return nil
	}

	res, err := poly.BuildGrandProduct(t.Base, N, D, mu)
	if err != nil {
		return err
	}
	if err := t.PutBase(out, res); err != nil {
		panic(fmt.Sprintf("[_GrandProductStep] register grand product column %s: %v", out, err))
	}

	return nil
}
