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
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/trace"
)

// RunningRatioCtx is the context of RunningRatioStep: whether it has
// numerators and denominators (a missing product is 1, and not a step input).
type RunningRatioCtx struct {
	HasNum, HasDen bool
}

// RunningRatioEndName is the name under which the end of the running-ratio
// column output is exposed, and of its sparse column P·L_0.
func RunningRatioEndName(output string) string {
	return output + "_end"
}

// RunningRatioConstraintDegree returns the degree of the constraints of a
// running-ratio column of the factors num/den (see AddRunningRatioStep):
// max(2 + Σ deg den, 1 + Σ deg num).
func RunningRatioConstraintDegree(num, den []expr.Expr) int {
	dNum, dDen := 1, 2
	for _, f := range num {
		dNum += f.Degree()
	}
	for _, f := range den {
		dDen += f.Degree()
	}
	return max(dNum, dDen)
}

// AddRunningRatioStep registers, at round r, a running-ratio column of the
// factors num/den and its constraints, and returns the name of its exposed
// end. num or den may be empty (a product of 1).
//
// With n_i, d_i the products of the numerators and of the denominators at row
// i, the column is Z_i = Π_{k≤i} n_k/d_k and its end P = Z_{N−1} is exposed at
// index 0, so that the verifier column E = Exposed(P) is P·L_0. The
// constraints are, on every row (row 0 reading Z_{N−1} as Z_{−1}):
//
//	Z·d·(1 − L_0 + E) − Z_{−1}·n = 0    row 0: Z_0·d_0·P = Z_{N−1}·n_0, else Z_i·d_i = Z_{i−1}·n_i
//	L_0·Z_{−1} − E = 0                   Z_{N−1} = P
//
// For P ≠ 0 and nonzero denominators, they hold exactly when Z_0 = n_0/d_0,
// Z_i = Z_{i−1}·n_i/d_i and P = Π_i n_i/d_i. The product bus checks that the
// ends multiply to 1, so that none is zero; the denominators are randomized by
// the caller. Their degree is RunningRatioConstraintDegree(num, den). The end
// must be bound to the transcript before the challenge that folds the
// relations, see BindExposedValues.
func (b *Builder) AddRunningRatioStep(r int, module string, num, den []expr.Expr, output string) (string, error) {
	if len(num) == 0 && len(den) == 0 {
		return "", fmt.Errorf("AddRunningRatioStep %s: no factors", output)
	}
	if d := RunningRatioConstraintDegree(num, den); d > MaxLogupDegree {
		return "", fmt.Errorf("AddRunningRatioStep %s: constraint degree %d exceeds %d", output, d, MaxLogupDegree)
	}
	m, ok := b.Modules[module]
	if !ok {
		return "", fmt.Errorf("AddRunningRatioStep %s: module %q not found", output, module)
	}
	end := RunningRatioEndName(output)

	// The products are cloned so that no subtree is shared between the step's
	// inputs and the constraint.
	one := expr.Const(koalabear.One())
	product := func(fs []expr.Expr) expr.Expr {
		var res expr.Expr = one
		for i, f := range fs {
			if i == 0 {
				res = expr.Clone(f)
			} else {
				res = res.Mul(expr.Clone(f))
			}
		}
		return res
	}
	var ins []expr.Expr
	if len(num) > 0 {
		ins = append(ins, product(num))
	}
	if len(den) > 0 {
		ins = append(ins, product(den))
	}
	ctx := RunningRatioCtx{HasNum: len(num) > 0, HasDen: len(den) > 0}
	b.AddStepAt(r, NewProverStep(ins, []string{output, end}, RunningRatioStep, ctx))

	z, zPrev := expr.Col(output), expr.Col(output, expr.WithShift(-1))
	e := expr.Exposed(end)
	lhs := z.Mul(one.Sub(m.LagrangeCol(0)).Add(e))
	if len(den) > 0 {
		lhs = lhs.Mul(product(den))
	}
	rhs := expr.Expr(zPrev)
	if len(num) > 0 {
		rhs = rhs.Mul(product(num))
	}
	m.AssertZero(lhs.Sub(rhs))
	m.AssertZero(m.LagrangeCol(0).Mul(zPrev).Sub(e))
	return end, nil
}

// RunningRatioStep computes a running-ratio column and its end, see
// AddRunningRatioStep. ins are the numerator product n and the denominator
// product d, each when present; outs are the column and the end, which is
// exposed (at index 0) and set as the sparse column P·L_0.
func RunningRatioStep(ins []expr.Expr, outs []string, t trace.Trace, prog *Program, prf *proof.Proof, mu *sync.Mutex, ctx StepContext) error {
	c, ok := ctx.(RunningRatioCtx)
	nIns := 0
	if c.HasNum {
		nIns++
	}
	if c.HasDen {
		nIns++
	}
	if !ok || nIns == 0 || len(ins) != nIns || len(outs) != 2 {
		return fmt.Errorf("[RunningRatioStep] wrong context or arity")
	}
	evals := make([]poly.ExtPolynomial, len(ins))
	for i, in := range ins {
		v, err := poly.BuildPointwiseEvaluationMixed(t.Base, t.Ext, prog.ColumnFields, in, mu)
		if err != nil {
			return fmt.Errorf("[RunningRatioStep] %s: %w", outs[0], err)
		}
		evals[i] = v
	}
	n := len(evals[0])
	ones := func() poly.ExtPolynomial {
		res := make(poly.ExtPolynomial, n)
		for i := range res {
			res[i].SetOne()
		}
		return res
	}
	num, den := ones(), ones()
	if c.HasNum {
		num = evals[0]
	}
	if c.HasDen {
		den = evals[len(evals)-1]
	}
	if len(num) != n || len(den) != n {
		return fmt.Errorf("[RunningRatioStep] %s: numerator and denominator have different sizes", outs[0])
	}
	for i := range den {
		if den[i].IsZero() {
			return fmt.Errorf("[RunningRatioStep] %s: zero denominator at row %d", outs[0], i)
		}
	}
	inv := ext.BatchInvertE6(den)
	col := make(poly.ExtPolynomial, n)
	for i := range col {
		col[i].Mul(&num[i], &inv[i])
		if i > 0 {
			col[i].Mul(&col[i], &col[i-1])
		}
	}
	end := col[n-1]

	var exposed ExposedValue
	exposed.Entries = make([]ExposedEntry, 1)
	exposed.Entries[0].Idx = 0
	exposed.Entries[0].SetExt(end)
	mu.Lock()
	prf.ExposedValues[outs[1]] = exposed
	mu.Unlock()

	sparse := make(poly.ExtPolynomial, n)
	sparse[0] = end
	if err := t.PutExt(outs[0], col); err != nil {
		return fmt.Errorf("[RunningRatioStep] register %s: %w", outs[0], err)
	}
	if err := t.PutExt(outs[1], sparse); err != nil {
		return fmt.Errorf("[RunningRatioStep] register %s: %w", outs[1], err)
	}
	return nil
}
