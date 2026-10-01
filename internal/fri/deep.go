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

package fri

import (
	"fmt"
	"math/big"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/parallel"
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/internal/reedsolomon"
)

// deepShiftTerm is one requested opening point for one polynomial in the
// per-polynomial DEEP quotient.
type deepShiftTerm struct {
	zs          ext.E6 // z_s = zeta * omega_N^shift
	scaledValue ext.E6 // alpha^i times the claimed value P(z_s)
}

// deepPolyBundle groups all requested shifts for one polynomial. The shifts are
// summed first, then one alpha_DEEP power folds that polynomial bundle with the
// other bundles of the same native size.
type deepPolyBundle struct {
	field field.Kind
	scale ext.E6

	baseCol poly.Polynomial
	extCol  poly.ExtPolynomial
	shifts  []deepShiftTerm
}

type deepDenominatorPlan struct {
	points  []ext.E6
	indexes [][]int
}

// computeDeepQuotientCodewordsByPolynomial builds one DEEP-quotient codeword
// per DEEP class (see deepPlan) using the per-polynomial convention. For each
// polynomial P_i, all requested shifts are first summed:
//
//	B_i(X) = sum_s (v_i,s - P_i(X)) / (z_i,s - X)
//
// Then the per-class quotient folds those polynomial bundles with alpha powers:
//
//	DQ_c(X) = sum_i alpha^i * B_i(X)
//
// The DEEP quotient polynomial has degree < N (the class's size) and is built
// directly on the size-N trace subgroup before being RS-encoded to size
// rate*N for FRI. The result is indexed by class.
//
// The alpha counter resets at each class and runs in deterministic order:
// batch declaration order, group declaration order, base rail then extension
// rail.
func computeDeepQuotientCodewordsByPolynomial(
	batches []Batch,
	shifts []BatchShifts,
	claimedValues []BatchClaimedValues,
	alpha ext.E6,
	zeta ext.E6,
	rate uint64,
	plan deepPlan,
	domainCache *poly.DomainCache,
) ([][]ext.E6, error) {
	if len(claimedValues) != len(batches) {
		return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: claimedValues has %d entries, batches has %d", len(claimedValues), len(batches))
	}
	if rate == 0 || rate&(rate-1) != 0 {
		return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: rate %d must be a positive power of two", rate)
	}
	if err := validateBatchShifts(batches, shifts); err != nil {
		return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: %w", err)
	}
	if len(plan.classOf) != len(batches) {
		return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: DEEP plan has %d batches, got %d", len(plan.classOf), len(batches))
	}

	deepByClass := make([][]ext.E6, plan.numClasses())
	for class, N := range plan.sizes {
		ratN := uint64(rate) * uint64(N)
		traceDomain := domainCache.Get(uint64(N))

		bundles, err := deepPolyBundlesForClass(class, N, batches, plan, shifts, claimedValues, alpha, zeta, traceDomain)
		if err != nil {
			return nil, err
		}

		deepLagrange := make(poly.ExtPolynomial, N)
		accumulateDeepQuotientByPolynomialOnTrace(deepLagrange, bundles, traceDomain)

		encoder := reedsolomon.NewEncoder(ratN, reedsolomon.WithCache(domainCache))
		deepByClass[class] = encoder.EncodeExt(deepLagrange, traceDomain)
	}
	return deepByClass, nil
}

func deepPolyBundlesForClass(
	class, N int,
	batches []Batch,
	plan deepPlan,
	shifts []BatchShifts,
	claimedValues []BatchClaimedValues,
	alpha ext.E6,
	zeta ext.E6,
	traceDomain *fft.Domain,
) ([]deepPolyBundle, error) {
	var bundles []deepPolyBundle
	var alphaRunning ext.E6
	alphaRunning.SetOne()

	for b, batch := range batches {
		if len(claimedValues[b]) != len(batch) {
			return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: claimedValues[%d] has %d groups, batches[%d] has %d", b, len(claimedValues[b]), b, len(batch))
		}
		for g, group := range batch {
			if plan.classOf[b][g] != class {
				continue
			}
			gShifts := shifts[b][g]
			gValues := claimedValues[b][g]
			if len(gValues.Base) != len(group.Base) {
				return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: claimedValues[%d][%d].Base has %d entries, group has %d base polys", b, g, len(gValues.Base), len(group.Base))
			}
			if len(gValues.Ext) != len(group.Ext) {
				return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: claimedValues[%d][%d].Ext has %d entries, group has %d ext polys", b, g, len(gValues.Ext), len(group.Ext))
			}

			for i, col := range group.Base {
				if len(gValues.Base[i]) != len(gShifts.Base[i]) {
					return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: claimedValues[%d][%d].Base[%d] has %d values, shifts has %d", b, g, i, len(gValues.Base[i]), len(gShifts.Base[i]))
				}
				bundles = append(bundles, deepPolyBundle{
					field:   field.Base,
					scale:   alphaRunning,
					baseCol: col,
					shifts:  deepShiftTerms(gShifts.Base[i], gValues.Base[i], N, zeta, alphaRunning, traceDomain),
				})
				alphaRunning.Mul(&alphaRunning, &alpha)
			}
			for i, col := range group.Ext {
				if len(gValues.Ext[i]) != len(gShifts.Ext[i]) {
					return nil, fmt.Errorf("fri: computeDeepQuotientCodewordsByPolynomial: claimedValues[%d][%d].Ext[%d] has %d values, shifts has %d", b, g, i, len(gValues.Ext[i]), len(gShifts.Ext[i]))
				}
				bundles = append(bundles, deepPolyBundle{
					field:  field.Ext,
					scale:  alphaRunning,
					extCol: col,
					shifts: deepShiftTerms(gShifts.Ext[i], gValues.Ext[i], N, zeta, alphaRunning, traceDomain),
				})
				alphaRunning.Mul(&alphaRunning, &alpha)
			}
		}
	}
	return bundles, nil
}

func deepShiftTerms(shifts []int, values []ext.E6, N int, zeta ext.E6, scale ext.E6, traceDomain *fft.Domain) []deepShiftTerm {
	terms := make([]deepShiftTerm, len(shifts))
	for i, s := range shifts {
		var omegaShift koalabear.Element
		omegaShift.Exp(traceDomain.Generator, big.NewInt(int64(normalizeShift(s, N))))
		terms[i].zs.MulByElement(&zeta, &omegaShift)
		terms[i].scaledValue.Mul(&scale, &values[i])
	}
	return terms
}

func newDeepDenominatorPlan(bundles []deepPolyBundle) deepDenominatorPlan {
	byPoint := make(map[ext.E6]int)
	plan := deepDenominatorPlan{
		indexes: make([][]int, len(bundles)),
	}
	for b := range bundles {
		bun := &bundles[b]
		plan.indexes[b] = make([]int, len(bun.shifts))
		for t, sh := range bun.shifts {
			idx, ok := byPoint[sh.zs]
			if !ok {
				idx = len(plan.points)
				byPoint[sh.zs] = idx
				plan.points = append(plan.points, sh.zs)
			}
			plan.indexes[b][t] = idx
		}
	}
	return plan
}

func accumulateDeepQuotientByPolynomialOnTrace(deep poly.ExtPolynomial, bundles []deepPolyBundle, traceDomain *fft.Domain) {
	N := len(deep)
	if N == 0 || len(bundles) == 0 {
		return
	}

	denomPlan := newDeepDenominatorPlan(bundles)
	nbShiftPoints := len(denomPlan.points)

	parallel.Execute(N, func(start, end int) {
		chunkLen := end - start

		denoms := make([]ext.E6, chunkLen*nbShiftPoints)
		var omegaX koalabear.Element
		if start == 0 {
			omegaX.SetOne()
		} else {
			omegaX.Exp(traceDomain.Generator, big.NewInt(int64(start)))
		}
		for row := 0; row < chunkLen; row++ {
			xExt := hash.LiftBaseToExt(omegaX)
			rowDenoms := denoms[row*nbShiftPoints : (row+1)*nbShiftPoints]
			for s, zs := range denomPlan.points {
				rowDenoms[s].Sub(&zs, &xExt)
			}
			omegaX.Mul(&omegaX, &traceDomain.Generator)
		}
		invs := ext.BatchInvertE6(denoms)
		numerators := make([]ext.E6, nbShiftPoints)

		for x := start; x < end; x++ {
			for s := range numerators {
				numerators[s] = ext.E6{}
			}

			for b := range bundles {
				bun := &bundles[b]
				shiftIndexes := denomPlan.indexes[b]

				var scaledPx ext.E6
				if bun.field == field.Base {
					scaledPx.MulByElement(&bun.scale, &bun.baseCol[x])
				} else {
					scaledPx.Mul(&bun.scale, &bun.extCol[x])
				}
				for t, sh := range bun.shifts {
					idx := shiftIndexes[t]
					numerators[idx].Add(&numerators[idx], &sh.scaledValue)
					numerators[idx].Sub(&numerators[idx], &scaledPx)
				}
			}

			row := x - start
			invRow := invs[row*nbShiftPoints : (row+1)*nbShiftPoints]
			for s := range numerators {
				var term ext.E6
				term.Mul(&numerators[s], &invRow[s])
				deep[x].Add(&deep[x], &term)
			}
		}
	})
}
