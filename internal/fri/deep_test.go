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
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/poly"
)

// TestComputeDeepQuotientCodewordsByPolynomialMatchesReference exercises the
// optimized per-polynomial DEEP-quotient builder against an unambiguous slow
// reference implementation on a two-size fixture with base and extension rails.
//
//	Batch 0  (size 8): 1 base poly + 1 ext poly, shifts {Base: [[0,1]], Ext: [[0]]}
//	Batch 1  (size 4): 1 base poly,              shifts {Base: [[0]]}
//
// Alpha powers are assigned once per polynomial and reset per size:
//   - Size 8, batch 0 group 0 base 0 -> alpha^0 over shifts {0,1}
//   - Size 8, batch 0 group 0 ext  0 -> alpha^1 over shift {0}
//   - Size 4, batch 1 group 0 base 0 -> alpha^0 over shift {0}
func TestComputeDeepQuotientCodewordsByPolynomialMatchesReference(t *testing.T) {
	const rate uint64 = 2

	basePoly8 := poly.Polynomial{
		baseElement(2), baseElement(3), baseElement(5), baseElement(7),
		baseElement(11), baseElement(13), baseElement(17), baseElement(19),
	}
	extPoly8 := poly.ExtPolynomial{
		extElement(101, 102, 103, 104),
		extElement(201, 202, 203, 204),
		extElement(301, 302, 303, 304),
		extElement(401, 402, 403, 404),
		extElement(501, 502, 503, 504),
		extElement(601, 602, 603, 604),
		extElement(701, 702, 703, 704),
		extElement(801, 802, 803, 804),
	}
	basePoly4 := poly.Polynomial{
		baseElement(21), baseElement(23), baseElement(29), baseElement(31),
	}

	batches := []Batch{
		{{Base: []poly.Polynomial{basePoly8}, Ext: []poly.ExtPolynomial{extPoly8}}},
		{{Base: []poly.Polynomial{basePoly4}}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0, 1}}, Ext: [][]int{{0}}}},
		{{Base: [][]int{{0}}}},
	}

	// zeta with a non-zero extension component so it is not in any
	// base-field subgroup -- guarantees (zeta - omega^k) != 0 for every k.
	var zeta ext.E6
	zeta.B0.A0.SetUint64(13)
	zeta.B1.A1.SetUint64(17)
	zeta.B2.A0.SetUint64(19)

	var alpha ext.E6
	alpha.B0.A0.SetUint64(2)
	alpha.B1.A0.SetUint64(3)
	alpha.B2.A1.SetUint64(5)

	var cache poly.DomainCache
	pcs := NewPCS(rate, DefaultLeafHasher, DefaultNodeHasher)
	committed := make([]Committed, len(batches))
	for b := range batches {
		c, err := pcs.Commit(batches[b], WithDomainCache(&cache))
		if err != nil {
			t.Fatalf("Commit(batches[%d]): %v", b, err)
		}
		committed[b] = c
	}

	cv, err := computeClaimedValues(batches, shifts, zeta, &cache)
	if err != nil {
		t.Fatalf("computeClaimedValues: %v", err)
	}

	gotMap, gotSizes, err := deepCodewordsBySize(
		batches, shifts, cv, alpha, zeta, rate, &cache,
	)
	if err != nil {
		t.Fatalf("deepCodewordsBySize: %v", err)
	}

	// The reference deliberately uses committed[b].Sources to read
	// encoded values on the size-rate*N subgroup and divides pointwise there.
	// The optimized path builds DQ in Lagrange form on the size-N subgroup and
	// encodes once. Two completely different arithmetic paths to the same
	// RS-encoded codeword make a strong parity check.
	wantMap, wantSizes := referenceDeepQuotientByPolynomial(
		t, batches, committed, shifts, cv, alpha, zeta, rate, &cache,
	)

	assertDeepQuotientCodewordsEqual(t, gotMap, gotSizes, wantMap, wantSizes)
}

// TestComputeDeepQuotientCodewordsShapeMismatch covers the input-length and
// rate validation paths of the optimized helper. Per-polynomial shift
// invariants are exercised by the shape-helper tests.
func TestComputeDeepQuotientCodewordsShapeMismatch(t *testing.T) {
	batches := []Batch{
		{{Base: []poly.Polynomial{makeBasePoly(4)}}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0}}}},
	}

	var cache poly.DomainCache
	cv, err := computeClaimedValues(batches, shifts, ext.E6{}, &cache)
	if err != nil {
		t.Fatal(err)
	}

	var alpha, zeta ext.E6
	alpha.SetOne()

	t.Run("shifts length mismatch", func(t *testing.T) {
		_, _, err := deepCodewordsBySize(
			batches, []BatchShifts{}, cv, alpha, zeta, 2, &cache,
		)
		if err == nil {
			t.Fatal("expected shifts-length mismatch error")
		}
	})
	t.Run("claimedValues length mismatch", func(t *testing.T) {
		_, _, err := deepCodewordsBySize(
			batches, shifts, []BatchClaimedValues{}, alpha, zeta, 2, &cache,
		)
		if err == nil {
			t.Fatal("expected claimedValues-length mismatch error")
		}
	})
	t.Run("rate must be power of two", func(t *testing.T) {
		_, _, err := deepCodewordsBySize(
			batches, shifts, cv, alpha, zeta, 3, &cache,
		)
		if err == nil {
			t.Fatal("expected rate-not-power-of-two error")
		}
	})
}

func TestComputeDeepQuotientCodewordsByPolynomialMultiShiftMatchesReference(t *testing.T) {
	const rate uint64 = 2

	basePoly8 := poly.Polynomial{
		baseElement(2), baseElement(3), baseElement(5), baseElement(7),
		baseElement(11), baseElement(13), baseElement(17), baseElement(19),
	}
	extPoly8 := poly.ExtPolynomial{
		extElement(101, 102, 103, 104, 105, 106),
		extElement(201, 202, 203, 204, 205, 206),
		extElement(301, 302, 303, 304, 305, 306),
		extElement(401, 402, 403, 404, 405, 406),
		extElement(501, 502, 503, 504, 505, 506),
		extElement(601, 602, 603, 604, 605, 606),
		extElement(701, 702, 703, 704, 705, 706),
		extElement(801, 802, 803, 804, 805, 806),
	}
	basePoly4 := poly.Polynomial{
		baseElement(21), baseElement(23), baseElement(29), baseElement(31),
	}

	batches := []Batch{
		{{Base: []poly.Polynomial{basePoly8}, Ext: []poly.ExtPolynomial{extPoly8}}},
		{{Base: []poly.Polynomial{basePoly4}}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0, 1}}, Ext: [][]int{{0}}}},
		{{Base: [][]int{{0}}}},
	}

	var zeta ext.E6
	zeta.B0.A0.SetUint64(13)
	zeta.B1.A1.SetUint64(17)
	zeta.B2.A0.SetUint64(19)

	var alpha ext.E6
	alpha.B0.A0.SetUint64(2)
	alpha.B1.A0.SetUint64(3)
	alpha.B2.A1.SetUint64(5)

	var cache poly.DomainCache
	pcs := NewPCS(rate, DefaultLeafHasher, DefaultNodeHasher)
	committed := make([]Committed, len(batches))
	for b := range batches {
		c, err := pcs.Commit(batches[b], WithDomainCache(&cache))
		if err != nil {
			t.Fatalf("Commit(batches[%d]): %v", b, err)
		}
		committed[b] = c
	}

	cv, err := computeClaimedValues(batches, shifts, zeta, &cache)
	if err != nil {
		t.Fatalf("computeClaimedValues: %v", err)
	}

	newMap, newSizes, err := deepCodewordsBySize(
		batches, shifts, cv, alpha, zeta, rate, &cache,
	)
	if err != nil {
		t.Fatalf("deepCodewordsBySize: %v", err)
	}

	wantMap, wantSizes := referenceDeepQuotientByPolynomial(
		t, batches, committed, shifts, cv, alpha, zeta, rate, &cache,
	)
	assertDeepQuotientCodewordsEqual(t, newMap, newSizes, wantMap, wantSizes)
}

func assertDeepQuotientCodewordsEqual(
	t *testing.T,
	gotMap map[int][]ext.E6,
	gotSizes []int,
	wantMap map[int][]ext.E6,
	wantSizes []int,
) {
	t.Helper()

	if len(gotSizes) != len(wantSizes) {
		t.Fatalf("sizesDesc length mismatch: got %v, want %v", gotSizes, wantSizes)
	}
	for i := range gotSizes {
		if gotSizes[i] != wantSizes[i] {
			t.Fatalf("sizesDesc[%d] = %d, want %d", i, gotSizes[i], wantSizes[i])
		}
	}

	for _, N := range gotSizes {
		got, want := gotMap[N], wantMap[N]
		if len(got) != len(want) {
			t.Fatalf("size %d: codeword length got %d want %d", N, len(got), len(want))
		}
		for k := range got {
			if !got[k].Equal(&want[k]) {
				t.Fatalf("size %d k=%d: got %s, want %s", N, k, got[k].String(), want[k].String())
			}
		}
	}
}

// referenceDeepQuotientByPolynomial is intentionally pointwise over committed
// encoded rows: for each polynomial, sum all its shift terms first, then apply
// one alpha power to that polynomial bundle.
func referenceDeepQuotientByPolynomial(
	t *testing.T,
	batches []Batch,
	committed []Committed,
	shifts []BatchShifts,
	claimedValues []BatchClaimedValues,
	alpha ext.E6,
	zeta ext.E6,
	rate uint64,
	domainCache *poly.DomainCache,
) (map[int][]ext.E6, []int) {
	t.Helper()

	sizes, err := groupNativeSizesFromBatches(batches)
	if err != nil {
		t.Fatalf("groupNativeSizesFromBatches: %v", err)
	}
	sizesDesc := sizesDescFromSizes(sizes)
	out := make(map[int][]ext.E6, len(sizesDesc))

	for _, N := range sizesDesc {
		ratN := int(rate) * N
		encDomain := domainCache.Get(uint64(ratN))
		traceDomain := domainCache.Get(uint64(N))

		srcForBatch := make([]*LeafSource, len(batches))
		for b := range batches {
			for k := range committed[b].Sources {
				src := &committed[b].Sources[k]
				if leafSourceRows(*src) == ratN {
					srcForBatch[b] = src
					break
				}
			}
		}

		deep := make([]ext.E6, ratN)
		var alphaRunning ext.E6
		alphaRunning.SetOne()

		for b, batch := range batches {
			for g := range batch {
				if sizes[b][g] != N {
					continue
				}
				src := srcForBatch[b]
				if src == nil {
					t.Fatalf("missing committed source for batch %d size %d", b, N)
				}
				gShifts := shifts[b][g]
				gValues := claimedValues[b][g]

				for i, polyShifts := range gShifts.Base {
					addReferenceDeepPolyBundle(
						deep,
						encDomain.Generator,
						traceDomain.Generator,
						N,
						src.Base[i],
						nil,
						polyShifts,
						gValues.Base[i],
						alphaRunning,
						zeta,
					)
					alphaRunning.Mul(&alphaRunning, &alpha)
				}
				for i, polyShifts := range gShifts.Ext {
					addReferenceDeepPolyBundle(
						deep,
						encDomain.Generator,
						traceDomain.Generator,
						N,
						nil,
						src.Ext[i],
						polyShifts,
						gValues.Ext[i],
						alphaRunning,
						zeta,
					)
					alphaRunning.Mul(&alphaRunning, &alpha)
				}
			}
		}

		out[N] = deep
	}
	return out, sizesDesc
}

func addReferenceDeepPolyBundle(
	deep []ext.E6,
	encodedGenerator koalabear.Element,
	traceGenerator koalabear.Element,
	N int,
	baseCol poly.Polynomial,
	extCol poly.ExtPolynomial,
	shifts []int,
	values []ext.E6,
	scale ext.E6,
	zeta ext.E6,
) {
	ratN := len(deep)
	for k := 0; k < ratN; k++ {
		var omegaX koalabear.Element
		omegaX.ExpInt64(encodedGenerator, int64(bitReverseIndex(k, ratN)))
		xExt := hash.LiftBaseToExt(omegaX)

		var px ext.E6
		if baseCol != nil {
			px = hash.LiftBaseToExt(baseCol[k])
		} else {
			px.Set(&extCol[k])
		}

		var bundle ext.E6
		for sIdx, s := range shifts {
			zs := shiftedZetaForTest(zeta, traceGenerator, s, N)
			var num, denom, denomInv, term ext.E6
			num.Sub(&values[sIdx], &px)
			denom.Sub(&zs, &xExt)
			denomInv.Inverse(&denom)
			term.Mul(&num, &denomInv)
			bundle.Add(&bundle, &term)
		}

		bundle.Mul(&bundle, &scale)
		deep[k].Add(&deep[k], &bundle)
	}
}

func shiftedZetaForTest(zeta ext.E6, traceGenerator koalabear.Element, shift, N int) ext.E6 {
	var omegaShift koalabear.Element
	omegaShift.Exp(traceGenerator, big.NewInt(int64(normalizeShift(shift, N))))

	var zs ext.E6
	zs.MulByElement(&zeta, &omegaShift)
	return zs
}

// deepCodewordsBySize runs computeDeepQuotientCodewordsByPolynomial with the
// default classes (one per size) and indexes the codewords by size.
func deepCodewordsBySize(
	batches []Batch,
	shifts []BatchShifts,
	claimedValues []BatchClaimedValues,
	alpha, zeta ext.E6,
	rate uint64,
	cache *poly.DomainCache,
) (map[int][]ext.E6, []int, error) {
	sizes, err := groupNativeSizesFromBatches(batches)
	if err != nil {
		return nil, nil, err
	}
	plan, err := newDeepPlan(sizes, nil)
	if err != nil {
		return nil, nil, err
	}
	byClass, err := computeDeepQuotientCodewordsByPolynomial(batches, shifts, claimedValues, alpha, zeta, rate, plan, cache)
	if err != nil {
		return nil, nil, err
	}
	res := make(map[int][]ext.E6, len(byClass))
	for c, cw := range byClass {
		res[plan.sizes[c]] = cw
	}
	return res, plan.sizes, nil
}
