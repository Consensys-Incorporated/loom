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
	"encoding/binary"
	"fmt"
	"sync"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/expr"
)

// BuildLookupMultiplicities returns one multiplicity column m_k per target
// table T[k] such that, for every tuple v,
//
//	Σ_k Σ_{i: T[k][i]=v} m_k[i]·selT[k][i] = Σ_j Σ_{i: S[j][i]=v} selS[j][i].
//
// Tuples are compared on their base-field values, so the result does not
// depend on any folding challenge. The whole weight of v is assigned to its
// first target row (in the order T[0], T[1], …) with a non-zero selector,
// which keeps the sums balanced when target rows are duplicated. selS and selT
// may be nil, meaning every selector is 1.
//
// It returns an error if a selected source tuple has no selected target row.
func BuildLookupMultiplicities(Pi map[string]Polynomial, selS []expr.Expr, S [][]expr.Expr, selT []expr.Expr, T [][]expr.Expr, mu *sync.Mutex) ([]Polynomial, error) {
	if selS != nil && len(selS) != len(S) {
		return nil, fmt.Errorf("BuildLookupMultiplicities: %d source selectors for %d sources", len(selS), len(S))
	}
	if selT != nil && len(selT) != len(T) {
		return nil, fmt.Errorf("BuildLookupMultiplicities: %d target selectors for %d targets", len(selT), len(T))
	}

	// 1 - accumulate the selected weight of every source tuple
	weights := make(map[string]koalabear.Element)
	var order []string // first-seen order, for deterministic error reporting
	for j, s := range S {
		cols, sel, err := evalTable(Pi, s, selectorAt(selS, j), mu)
		if err != nil {
			return nil, fmt.Errorf("BuildLookupMultiplicities: S[%d]: %w", j, err)
		}
		for i := range sel {
			if sel[i].IsZero() {
				continue
			}
			key := tupleKey(cols, i)
			w, ok := weights[key]
			if !ok {
				order = append(order, key)
			}
			w.Add(&w, &sel[i])
			weights[key] = w
		}
	}

	// 2 - assign each weight to the first selected matching target row
	res := make([]Polynomial, len(T))
	assigned := make(map[string]bool, len(weights))
	for k, t := range T {
		cols, sel, err := evalTable(Pi, t, selectorAt(selT, k), mu)
		if err != nil {
			return nil, fmt.Errorf("BuildLookupMultiplicities: T[%d]: %w", k, err)
		}
		res[k] = make(Polynomial, len(sel))
		for i := range sel {
			if sel[i].IsZero() {
				continue
			}
			key := tupleKey(cols, i)
			w, ok := weights[key]
			if !ok || assigned[key] {
				continue
			}
			var inv koalabear.Element
			inv.Inverse(&sel[i])
			res[k][i].Mul(&w, &inv)
			assigned[key] = true
		}
	}

	// 3 - every selected source tuple must have been matched
	for _, key := range order {
		if w := weights[key]; !assigned[key] && !w.IsZero() {
			return nil, fmt.Errorf("BuildLookupMultiplicities: source tuple %v not found in any target", decodeTupleKey(key))
		}
	}

	return res, nil
}

func selectorAt(sel []expr.Expr, i int) expr.Expr {
	if sel == nil {
		return nil
	}
	return sel[i]
}

// evalTable evaluates the columns of a table and its selector (all ones if sel
// is nil) over a common domain.
func evalTable(Pi map[string]Polynomial, cols []expr.Expr, sel expr.Expr, mu *sync.Mutex) ([]Polynomial, Polynomial, error) {
	n, err := inferN(Pi, append(append([]expr.Expr(nil), cols...), sel)...)
	if err != nil {
		return nil, nil, err
	}
	res := make([]Polynomial, len(cols))
	for i, c := range cols {
		res[i] = make(Polynomial, n)
		if err := evalPointWiseInto(Pi, c, n, mu, res[i]); err != nil {
			return nil, nil, err
		}
	}
	s := make(Polynomial, n)
	if sel == nil {
		for i := range s {
			s[i].SetOne()
		}
	} else if err := evalPointWiseInto(Pi, sel, n, mu, s); err != nil {
		return nil, nil, err
	}
	return res, s, nil
}

func tupleKey(cols []Polynomial, row int) string {
	buf := make([]byte, 4*len(cols))
	for j, c := range cols {
		binary.LittleEndian.PutUint32(buf[4*j:], c[row].Bits()[0])
	}
	return string(buf)
}

func decodeTupleKey(key string) []uint32 {
	res := make([]uint32, len(key)/4)
	for j := range res {
		res[j] = binary.LittleEndian.Uint32([]byte(key[4*j : 4*j+4]))
	}
	return res
}
