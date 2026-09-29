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

package poly

import (
	"fmt"
	"sync"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/dag"
	fieldhash "github.com/consensys/loom/internal/hash"
)

// BuildPointwiseEvaluation evaluates E point-wise over Pi and returns the N results as a
// freshly allocated slice. N is the size of the polynomials in Pi (all must
// have the same size, except constants which have size 1).
func BuildPointwiseEvaluation(Pi map[string]Polynomial, E expr.Expr, mu *sync.Mutex) ([]koalabear.Element, error) {
	leaves := E.LeavesFull(expr.NewConfig(expr.WithoutChallenges()))
	_c := Pi[leaves[0].Name]
	N := len(_c)
	dst := make([]koalabear.Element, N)
	return dst, evalPointWiseInto(Pi, E, N, mu, dst)
}

// BuildPointwiseEvaluationMixed evaluates E point-wise over mixed base and
// extension columns and returns E6 values. Base columns stay on the base rail
// while the DAG evaluator lifts them at extension-valued parents.
func BuildPointwiseEvaluationMixed(PiBase map[string]Polynomial, PiExt map[string]ExtPolynomial, columnFields map[string]field.Kind, E expr.Expr, mu *sync.Mutex) (ExtPolynomial, error) {
	N, err := inferNMixed(PiBase, PiExt, E)
	if err != nil {
		return nil, err
	}
	dst := make(ExtPolynomial, N)
	return dst, evalPointWiseMixedInto(PiBase, PiExt, columnFields, E, N, mu, dst)
}

// inferN returns the size N of the domain by inspecting the polynomials in P.
// It prefers polynomials with length > 1 (unambiguous non-constant), but falls
// back to length 1 if a named leaf is present in P (N=1 single-row trace).
// Constant expressions (leaves absent from P) and challenges are ignored.
func inferN(P map[string]Polynomial, exprs ...expr.Expr) (int, error) {
	noChallenge := expr.NewConfig(expr.WithoutChallenges())
	foundOne := false
	for _, e := range exprs {
		if e == nil {
			continue
		}
		for _, leaf := range e.LeavesFull(noChallenge) {
			if p, ok := P[leaf.Name]; ok {
				if len(p) != 1 {
					return len(p), nil
				}
				foundOne = true // len==1 could be N=1 trace, not a constant
			}
		}
	}
	if foundOne {
		return 1, nil
	}
	return 0, fmt.Errorf("inferN: could not determine N — all leaves are constant or missing from trace")
}

// inferNMixed is inferN's mixed-rail counterpart. Challenge leaves are ignored
// because Fiat-Shamir challenges are scalar columns of length 1 and do not
// determine the trace domain size.
func inferNMixed(PiBase map[string]Polynomial, PiExt map[string]ExtPolynomial, exprs ...expr.Expr) (int, error) {
	noChallenge := expr.NewConfig(expr.WithoutChallenges())
	foundOne := false
	for _, e := range exprs {
		if e == nil {
			continue
		}
		for _, leaf := range e.LeavesFull(noChallenge) {
			if p, ok := PiBase[leaf.Name]; ok {
				if len(p) != 1 {
					return len(p), nil
				}
				foundOne = true
			}
			if p, ok := PiExt[leaf.Name]; ok {
				if len(p) != 1 {
					return len(p), nil
				}
				foundOne = true
			}
		}
	}
	if foundOne {
		return 1, nil
	}
	return 0, fmt.Errorf("inferNMixed: could not determine N — all leaves are constant or missing from trace")
}

// BuildLogupMixed returns the running sum M/E for mixed base and extension
// inputs. The output is always an extension polynomial.
func BuildLogupMixed(PiBase map[string]Polynomial, PiExt map[string]ExtPolynomial, columnFields map[string]field.Kind, E, M expr.Expr, mu *sync.Mutex) (ExtPolynomial, error) {
	N, err := inferNMixed(PiBase, PiExt, E, M)
	if err != nil {
		return nil, err
	}

	D := make(ExtPolynomial, N)
	if err := evalPointWiseMixedInto(PiBase, PiExt, columnFields, E, N, mu, D); err != nil {
		return nil, err
	}
	D = ext.BatchInvertE6(D)

	Mp := make(ExtPolynomial, N)
	if err := evalPointWiseMixedInto(PiBase, PiExt, columnFields, M, N, mu, Mp); err != nil {
		return nil, err
	}
	for i := 0; i < N; i++ {
		D[i].Mul(&D[i], &Mp[i])
	}

	return accumulateSumsExt(D, N)
}

// BuildGrandProduct returns R such that R[0]=1, R[i+1] = R[i] * E1(P[i]) / E2(P[i])
// N = size of the polynomials in P
// Polynomials in P must have the same basis, same layout
func BuildGrandProduct(P map[string]Polynomial, E1, E2 expr.Expr, mu *sync.Mutex) (Polynomial, error) {

	// pick first non length(1) entry of one of the leafs of type Col of E1 or E2, let N be that value
	N, err := inferN(P, E1, E2)
	if err != nil {
		return Polynomial{}, fmt.Errorf("BuildGrandProduct: %w", err)
	}

	// Q0 and Q1 are intermediate buffers: pooled because they are fully consumed by divPointwise.
	Q0 := getBuf(N)
	if err := evalPointWiseInto(P, E1, N, mu, Q0); err != nil {
		putBuf(Q0)
		return Polynomial{}, fmt.Errorf("failed to evaluate numerator expression: %w", err)
	}

	Q1 := getBuf(N)
	if err := evalPointWiseInto(P, E2, N, mu, Q1); err != nil {
		putBuf(Q0)
		putBuf(Q1)
		return Polynomial{}, fmt.Errorf("failed to evaluate denominator expression: %w", err)
	}

	ratio, err := divPointwise(Q0, Q1, N)
	putBuf(Q0)
	putBuf(Q1)
	if err != nil {
		return Polynomial{}, fmt.Errorf("failed to compute pointwise ratio: %w", err)
	}

	return accumulateProducts(ratio, N)
}

// BuildGrandProductMixed returns R such that R[0]=1 and
// R[i+1]=R[i]*E1(P[i])/E2(P[i]) for mixed base and extension inputs.
func BuildGrandProductMixed(PiBase map[string]Polynomial, PiExt map[string]ExtPolynomial, columnFields map[string]field.Kind, E1, E2 expr.Expr, mu *sync.Mutex) (ExtPolynomial, error) {
	N, err := inferNMixed(PiBase, PiExt, E1, E2)
	if err != nil {
		return nil, fmt.Errorf("BuildGrandProductMixed: %w", err)
	}

	Q0 := make(ExtPolynomial, N)
	if err := evalPointWiseMixedInto(PiBase, PiExt, columnFields, E1, N, mu, Q0); err != nil {
		return nil, fmt.Errorf("failed to evaluate numerator expression: %w", err)
	}

	Q1 := make(ExtPolynomial, N)
	if err := evalPointWiseMixedInto(PiBase, PiExt, columnFields, E2, N, mu, Q1); err != nil {
		return nil, fmt.Errorf("failed to evaluate denominator expression: %w", err)
	}

	ratio, err := divPointwiseExt(Q0, Q1, N)
	if err != nil {
		return nil, fmt.Errorf("failed to compute pointwise ratio: %w", err)
	}

	return accumulateProductsExt(ratio, N)
}

// evalPointWiseMixedInto evaluates E over mixed rails and writes N extension
// values into dst. Leaf.Idx is assigned rail-locally by bare column name, so
// rotated and unrotated references share the same source polynomial.
func evalPointWiseMixedInto(PiBase map[string]Polynomial, PiExt map[string]ExtPolynomial, columnFields map[string]field.Kind, E expr.Expr, N int, mu *sync.Mutex, dst []ext.E6) error {
	if len(dst) != N {
		return fmt.Errorf("evalPointWiseMixedInto: dst length %d, want %d", len(dst), N)
	}

	d := dag.ExprToDAGWithColumnFields(E, columnFields)
	if d.Root.Field == field.Base {
		tmp := make(Polynomial, N)
		if err := evalPointWiseInto(PiBase, E, N, mu, tmp); err != nil {
			return err
		}
		for i := 0; i < N; i++ {
			dst[i] = fieldhash.LiftBaseToExt(tmp[i])
		}
		return nil
	}

	baseToIdx := make(map[string]int)
	extToIdx := make(map[string]int)
	var PiBaseByIdx []Polynomial
	var PiExtByIdx []ExtPolynomial

	if mu != nil {
		mu.Lock()
	}

	for _, n := range d.Nodes {
		if n.Kind != dag.KindLeaf || n.Leaf.Type == expr.ConstantColumn {
			continue
		}
		name := n.Leaf.Name
		if n.Field == field.Ext {
			idx, ok := extToIdx[name]
			if !ok {
				p, ok := PiExt[name]
				if !ok {
					base, baseOK := PiBase[name]
					if !baseOK {
						if mu != nil {
							mu.Unlock()
						}
						return fmt.Errorf("evalPointWiseMixedInto: extension column %q not found", name)
					}
					p = liftPolynomialToExt(base)
				}
				if len(p) != N && len(p) != 1 {
					if mu != nil {
						mu.Unlock()
					}
					return fmt.Errorf("evalPointWiseMixedInto: extension column %q has length %d, want %d or 1", name, len(p), N)
				}
				idx = len(PiExtByIdx)
				extToIdx[name] = idx
				PiExtByIdx = append(PiExtByIdx, p)
			}
			n.Leaf.Idx = idx
			continue
		}

		idx, ok := baseToIdx[name]
		if !ok {
			p, ok := PiBase[name]
			if !ok {
				if mu != nil {
					mu.Unlock()
				}
				return fmt.Errorf("evalPointWiseMixedInto: base column %q not found", name)
			}
			if len(p) != N && len(p) != 1 {
				if mu != nil {
					mu.Unlock()
				}
				return fmt.Errorf("evalPointWiseMixedInto: base column %q has length %d, want %d or 1", name, len(p), N)
			}
			idx = len(PiBaseByIdx)
			baseToIdx[name] = idx
			PiBaseByIdx = append(PiBaseByIdx, p)
		}
		n.Leaf.Idx = idx
	}
	if mu != nil {
		mu.Unlock()
	}

	values := d.EvalOnAllEntriesMixed(PiBaseByIdx, PiExtByIdx, N)
	copy(dst, values)
	return nil
}

func liftPolynomialToExt(p Polynomial) ExtPolynomial {
	res := make(ExtPolynomial, len(p))
	for i := range p {
		res[i] = fieldhash.LiftBaseToExt(p[i])
	}
	return res
}

func divPointwiseExt(P1, P2 ExtPolynomial, N int) (ExtPolynomial, error) {
	for i := 0; i < len(P2); i++ {
		if P2[i].IsZero() {
			return nil, fmt.Errorf("division by zero")
		}
	}
	res := ext.BatchInvertE6(P2)
	for i := 0; i < N; i++ {
		res[i].Mul(&P1[i], &res[i])
	}
	return res, nil
}

func accumulateSumsExt(P ExtPolynomial, N int) (ExtPolynomial, error) {
	result := make(ExtPolynomial, N)
	result[0].Set(&P[0])
	for i := 1; i < N; i++ {
		result[i].Add(&result[i-1], &P[i])
	}
	return result, nil
}

func accumulateProductsExt(P ExtPolynomial, N int) (ExtPolynomial, error) {
	result := make(ExtPolynomial, N)
	result[0].SetOne()
	for i := 1; i < N; i++ {
		result[i].Mul(&result[i-1], &P[i-1])
	}
	return result, nil
}
