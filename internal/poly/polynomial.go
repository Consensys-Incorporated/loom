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

// /!\ In this package, every inputs polynomials must be in lagrange basis (the inputs come from columns of a trace).

package poly

import (
	"fmt"
	"math/bits"
	"sync"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/dag"
)

// Polynomial is a wrapper around EPolynomial that includes additional metadata such as shift.
type Polynomial = []koalabear.Element

// evalBufPool pools []koalabear.Element slices used as temporary buffers inside
// BuildGrandProduct and BuildGrandSum. koalabear.Element contains no pointers,
// so pooled slices do not prevent GC of other objects.
var evalBufPool sync.Pool

func getBuf(n int) []koalabear.Element {
	if v := evalBufPool.Get(); v != nil {
		if b := v.([]koalabear.Element); cap(b) >= n {
			return b[:n]
		}
	}
	return make([]koalabear.Element, n)
}

func putBuf(b []koalabear.Element) {
	evalBufPool.Put(b[:cap(b)])
}

// evalPointWiseInto is the core implementation: it evaluates E point-wise over
// Pi and writes the N results into dst (which must have length N).
func evalPointWiseInto(Pi map[string]Polynomial, E expr.Expr, N int, mu *sync.Mutex, dst []koalabear.Element) error {
	type varKey struct {
		name  string
		shift int
	}
	varToIdx := make(map[string]int)
	allLeaves := E.LeavesFull(expr.NewConfig())
	leaves := make([]*expr.Leaf, 0, len(allLeaves))
	for _, l := range allLeaves {
		if idx, ok := varToIdx[l.Name]; ok {
			l.Idx = idx
		} else {
			l.Idx = len(leaves)
			varToIdx[l.Name] = l.Idx
			leaves = append(leaves, l)
		}
	}

	if mu != nil {
		mu.Lock()
	}
	_Pi := make([]Polynomial, len(leaves))
	for _, l := range leaves {
		_Pi[l.Idx] = Pi[l.Name]
	}
	if mu != nil {
		mu.Unlock()
	}

	for i := 0; i < N; i++ {
		dst[i] = E.EvaluateOnIthEntry(_Pi, i)
	}
	return nil
}

// divPointwise computes the resulting polynomial from dividing pointwise.
// N = size of polynomials. All polynomials must be of the same size, same basis, same layout
func divPointwise(P1, P2 Polynomial, N int) (Polynomial, error) {

	for i := 0; i < len(P2); i++ {
		if P2[i].IsZero() {
			return Polynomial{}, fmt.Errorf("division by zero")
		}
	}
	res := koalabear.BatchInvert(P2)

	// Build result polynomial pointwise: R[i] = P_1[i] / P_2[i]
	for i := 0; i < N; i++ {
		res[i].Mul(&P1[i], &res[i])
	}
	return res, nil
}

// invertPointwiseInPlace inverts in place P
func invertPointwiseInPlace(P Polynomial) {
	for i := 0; i < len(P); i++ {
		P[i].Inverse(&P[i])
	}
}

// accumulateProducts returns R such that R[i+1] = R[i]*P[i], R[0]=1
// N = size of P
func accumulateProducts(P Polynomial, N int) (Polynomial, error) {

	// build the result R in lagrange basis of size targetSize such that:
	// R[0] = 1
	// R[i] = R[i-1]*P[i-1] for i > 0
	result := make([]koalabear.Element, N)
	result[0].SetOne()
	for i := 1; i < N; i++ {
		pi := P[i-1]
		result[i].Mul(&result[i-1], &pi)
	}
	return result, nil
}

// Evaluate evaluates a polynomial p in Lagrange form at zeta
// the domain d is assumed to be correctly formed
func Evaluate(p Polynomial, d *fft.Domain, zeta koalabear.Element) koalabear.Element {
	n := len(p)
	_p := getBuf(n)
	copy(_p, p)
	nn := uint64(64 - bits.TrailingZeros64(uint64(n)))
	d.FFTInverse(_p, fft.DIF)
	var res koalabear.Element
	for i := n - 1; i >= 0; i-- {
		iRev := bits.Reverse64(uint64(i)) >> nn
		res.Mul(&res, &zeta)
		res.Add(&res, &_p[iRev])
	}
	putBuf(_p)
	return res
}

// Eval evaluates vanishingRelation pointwise on Pi and returns the N results
// as a Polynomial in Lagrange normal form.
// All polynomials in Pi must be in Lagrange normal form with the same size N
// (constants of length 1 are also accepted).
// Used for testing only
func Eval(Pi map[string]Polynomial, vanishingRelation dag.DAG, N int) (Polynomial, error) {

	// Assign Leaf.Idx by column name, same convention as ComputeQuotient.
	nameToIdx := make(map[string]int)
	for _, n := range vanishingRelation.Nodes {
		if n.Kind != dag.KindLeaf || n.Leaf.Type == expr.ConstantColumn {
			continue
		}
		l := n.Leaf
		if _, ok := nameToIdx[l.Name]; !ok {
			col, ok2 := Pi[l.Name]
			if !ok2 {
				return Polynomial{}, fmt.Errorf("Eval: column %q not found in Pi", l.Name)
			}
			if len(col) != N && len(col) != 1 {
				return Polynomial{}, fmt.Errorf("Eval: column %q has length %d, want %d or 1", l.Name, len(col), N)
			}
			nameToIdx[l.Name] = len(nameToIdx)
		}
		l.Idx = nameToIdx[l.Name]
	}

	_Pi := make([][]koalabear.Element, len(nameToIdx))
	for name, idx := range nameToIdx {
		_Pi[idx] = Pi[name]
	}

	return vanishingRelation.EvalOnAllEntries(_Pi, N), nil
}

// EvalMixed evaluates vanishingRelation pointwise on mixed base/extension
// columns and returns N extension-field results in Lagrange normal form.
// Base columns referenced from extension-valued nodes are lifted on demand.
// Used for testing only.
func EvalMixed(PiBase map[string]Polynomial, PiExt map[string]ExtPolynomial, vanishingRelation dag.DAG, N int) (ExtPolynomial, error) {
	if vanishingRelation.Root.Field == field.Base {
		baseVals, err := Eval(PiBase, vanishingRelation, N)
		if err != nil {
			return nil, err
		}
		return liftPolynomialToExt(baseVals), nil
	}

	baseToIdx := make(map[string]int)
	extToIdx := make(map[string]int)
	var piBaseByIdx []Polynomial
	var piExtByIdx []ExtPolynomial

	for _, n := range vanishingRelation.Nodes {
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
						return nil, fmt.Errorf("EvalMixed: extension column %q not found", name)
					}
					p = liftPolynomialToExt(base)
				}
				if len(p) != N && len(p) != 1 {
					return nil, fmt.Errorf("EvalMixed: extension column %q has length %d, want %d or 1", name, len(p), N)
				}
				idx = len(piExtByIdx)
				extToIdx[name] = idx
				piExtByIdx = append(piExtByIdx, p)
			}
			n.Leaf.Idx = idx
			continue
		}

		idx, ok := baseToIdx[name]
		if !ok {
			p, ok := PiBase[name]
			if !ok {
				return nil, fmt.Errorf("EvalMixed: base column %q not found", name)
			}
			if len(p) != N && len(p) != 1 {
				return nil, fmt.Errorf("EvalMixed: base column %q has length %d, want %d or 1", name, len(p), N)
			}
			idx = len(piBaseByIdx)
			baseToIdx[name] = idx
			piBaseByIdx = append(piBaseByIdx, p)
		}
		n.Leaf.Idx = idx
	}

	return vanishingRelation.EvalOnAllEntriesMixed(piBaseByIdx, piExtByIdx, N), nil
}
