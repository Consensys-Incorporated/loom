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
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/trace"
)

// LogupTerm is one fraction M/E of a logup column.
type LogupTerm struct {
	E, M expr.Expr
}

// MaxLogupDegree bounds the degree of the constraint of a batched logup
// column, see LogupConstraintDegree.
const MaxLogupDegree = 4

// LogupConstraintDegree returns the degree of the constraint of a cyclic logup
// column batching terms:
//
//	(L − L_{−1} + C) · Π_j E_j − Σ_j M_j · Π_{i≠j} E_i
func LogupConstraintDegree(terms []LogupTerm) int {
	sumE := 0
	for _, t := range terms {
		sumE += t.E.Degree()
	}
	deg := 1 + sumE
	for _, t := range terms {
		deg = max(deg, t.M.Degree()+sumE-t.E.Degree())
	}
	return deg
}

// CyclicLogUpCtx is the context of CyclicLogUpStep.
type CyclicLogUpCtx struct {
	NbTerms int
}

// LogupTotalName is the name under which the total of the cyclic logup column
// output is exposed, and of the constant column total/N.
func LogupTotalName(output string) string {
	return output + "_total"
}

// AddCyclicLogupStep registers, at round r, a logup column batching terms and
// its constraint, and returns the name of its exposed total.
//
// The column L sums Σ_j M_j/E_j along the rows, cyclically: with v_i the sum
// of the terms at row i, T = Σ_i v_i the exposed total and C the constant
// column T/N (a verifier column, see expr.ExposedAverage),
//
//	L_i − L_{i−1} = v_i − C   on every row, row 0 reading L_{N−1}.
//
// Summed over the rows, the left side telescopes to 0, so the constraint
// holds exactly when T = Σ_i v_i. It needs no boundary selector, hence its
// degree is LogupConstraintDegree(terms). The total must be bound to the
// transcript before the challenge that folds the relations, see
// BindExposedValues.
func (b *Builder) AddCyclicLogupStep(r int, module string, terms []LogupTerm, output string) (string, error) {
	if len(terms) == 0 {
		return "", fmt.Errorf("AddCyclicLogupStep %s: no terms", output)
	}
	if d := LogupConstraintDegree(terms); d > MaxLogupDegree {
		return "", fmt.Errorf("AddCyclicLogupStep %s: constraint degree %d exceeds %d", output, d, MaxLogupDegree)
	}
	m, ok := b.Modules[module]
	if !ok {
		return "", fmt.Errorf("AddCyclicLogupStep %s: module %q not found", output, module)
	}
	total := LogupTotalName(output)

	ins := make([]expr.Expr, 0, 2*len(terms))
	for _, t := range terms {
		ins = append(ins, t.E, t.M)
	}
	b.AddStepAt(r, NewProverStep(ins, []string{output, total}, CyclicLogUpStep, CyclicLogUpCtx{NbTerms: len(terms)}))

	// Each factor is cloned so that no subtree is shared between the terms.
	prodE := func(skip int) expr.Expr {
		var res expr.Expr
		for i, t := range terms {
			if i == skip {
				continue
			}
			e := expr.Clone(t.E)
			if res == nil {
				res = e
			} else {
				res = res.Mul(e)
			}
		}
		return res
	}
	increment := expr.Col(output).Sub(expr.Col(output, expr.WithShift(-1))).Add(expr.ExposedAverage(total))
	relation := increment.Mul(prodE(-1))
	for j, t := range terms {
		num := expr.Clone(t.M)
		if len(terms) > 1 {
			num = num.Mul(prodE(j))
		}
		relation = relation.Sub(num)
	}
	m.AssertZero(relation)
	return total, nil
}

// CyclicLogUpStep computes a cyclic logup column and its total, see
// AddCyclicLogupStep. ins are [E_0, M_0, E_1, M_1, ...]; outs are the column
// and the total, which is exposed and also set as the constant column total/N.
func CyclicLogUpStep(ins []expr.Expr, outs []string, t trace.Trace, prog *Program, prf *proof.Proof, mu *sync.Mutex, ctx StepContext) error {
	c, ok := ctx.(CyclicLogUpCtx)
	if !ok || len(ins) != 2*c.NbTerms || len(outs) != 2 {
		return fmt.Errorf("[CyclicLogUpStep] wrong context or arity")
	}

	// v_i: running sums of every term, added up
	var sums poly.ExtPolynomial
	for j := 0; j < c.NbTerms; j++ {
		rs, err := poly.BuildLogupMixed(t.Base, t.Ext, prog.ColumnFields, ins[2*j], ins[2*j+1], mu)
		if err != nil {
			return fmt.Errorf("[CyclicLogUpStep] %s term %d: %w", outs[0], j, err)
		}
		if sums == nil {
			sums = rs
			continue
		}
		if len(rs) != len(sums) {
			return fmt.Errorf("[CyclicLogUpStep] %s: terms have different sizes", outs[0])
		}
		for i := range sums {
			sums[i].Add(&sums[i], &rs[i])
		}
	}
	n := len(sums)
	total := sums[n-1]

	// L_i = Σ_{r≤i} v_r − (i+1)·T/N, and the constant column T/N
	var invN koalabear.Element
	invN.SetUint64(uint64(n))
	invN.Inverse(&invN)
	var avg ext.E6
	avg.MulByElement(&total, &invN)
	col := make(poly.ExtPolynomial, n)
	avgCol := make(poly.ExtPolynomial, n)
	var shift ext.E6
	for i := range col {
		shift.Add(&shift, &avg)
		col[i].Sub(&sums[i], &shift)
		avgCol[i] = avg
	}

	var exposed ExposedValue
	exposed.Entries = make([]ExposedEntry, 1)
	exposed.Entries[0].SetExt(total)
	mu.Lock()
	prf.ExposedValues[outs[1]] = exposed
	mu.Unlock()
	if err := t.PutExt(outs[0], col); err != nil {
		return fmt.Errorf("[CyclicLogUpStep] register %s: %w", outs[0], err)
	}
	if err := t.PutExt(outs[1], avgCol); err != nil {
		return fmt.Errorf("[CyclicLogUpStep] register %s: %w", outs[1], err)
	}
	return nil
}

// ExposedOutputs returns the outputs of the step that are exposed in the
// proof.
func (ps ProverStep) ExposedOutputs() []string {
	switch ps.Ctx.(type) {
	case CyclicLogUpCtx:
		return ps.Outs[1:2]
	case ExposeEntriesCtx, ExposeIthValueCtx, ExposeRelativeIthValueCtx:
		return ps.Outs[:1]
	default:
		return nil
	}
}

// ExposedValueNames returns, in step order, the names of the values the
// round's steps expose.
func (r ProverRound) ExposedValueNames() []string {
	var res []string
	for _, s := range r.Steps {
		res = append(res, s.ExposedOutputs()...)
	}
	return res
}

// ExposedValueElements is the transcript encoding of an exposed value: for
// each entry, its index and its value as an extension element.
func ExposedValueElements(v ExposedValue) []koalabear.Element {
	var res []koalabear.Element
	for _, e := range v.Entries {
		res = append(res, hash.NewElement(uint64(e.Idx)))
		res = append(res, hash.ExtToElements(e.ExtValue())...)
	}
	return res
}
