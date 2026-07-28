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
	"sort"
	"sync/atomic"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/field"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/parallel"
)

// PCS.Verify checks an OpeningProof produced by PCS.Open against:
//
//   - roots: one Merkle root per Batch (in the same declaration order the
//     prover handed to Open). The caller is responsible for assembling
//     setup roots (from a verification key) and witness roots (from the
//     outer proof) into the right slice.
//   - shapes: the per-Batch / per-Group shape descriptor (Rows,
//     BaseWidth, ExtWidth). The verifier reconstructs every Group's
//     native size from Rows and the PCS's rate.
//   - shifts: the same per-poly shift schedule the prover used.
//   - zeta: the out-of-domain evaluation point.
//   - fs: a transcript already in the same state the prover's transcript
//     was in when Open was invoked. Verify registers alpha_DEEP and the
//     FRI-internal challenge names itself; the caller MUST NOT have
//     pre-registered any of those names.
//
// Verify performs four checks in sequence:
//
//  1. Shape validation against the proof.
//  2. Re-derives alpha_DEEP by replaying the same per-polynomial binding
//     sequence Open used.
//  3. Multi-degree FRI verification on the DEEP-quotient roots.
//  4. The bridge: for every FRI query position and every distinct
//     native size, recompute DQ_N(omega^x) and DQ_N(-omega^x) from the
//     opened raw rows and the claimed values, then compare to the
//     FRI proof's level leaves at that query.
//
// Any of the checks failing yields a non-nil error explaining the
// failure mode.
func (pcs *PCS) Verify(
	roots []hash.Digest,
	shapes []BatchShapes,
	shifts []BatchShifts,
	zeta ext.E6,
	proof OpeningProof,
	fs *fiatshamir.Transcript,
) error {
	if pcs.params == nil {
		return fmt.Errorf("fri: PCS.Verify requires Params; construct PCS via NewPCSWithParams")
	}
	if fs == nil {
		return fmt.Errorf("fri: PCS.Verify: fs transcript is required")
	}
	if len(roots) != len(shapes) {
		return fmt.Errorf("fri: PCS.Verify: roots has %d entries, shapes has %d", len(roots), len(shapes))
	}
	if len(shifts) != len(shapes) {
		return fmt.Errorf("fri: PCS.Verify: shifts has %d entries, shapes has %d", len(shifts), len(shapes))
	}
	if len(proof.ClaimedValues) != len(shapes) {
		return fmt.Errorf("fri: PCS.Verify: ClaimedValues has %d entries, shapes has %d", len(proof.ClaimedValues), len(shapes))
	}

	// 1- Validate verifier-side shape metadata and the shift schedule.
	if err := validateBatchShiftsFromShapes(shapes, shifts, pcs.rate); err != nil {
		return err
	}
	sizes, err := groupNativeSizesFromShapes(shapes, pcs.rate)
	if err != nil {
		return err
	}

	// 2- Validate the OpeningProof's nested shapes against shapes/shifts/sizes.
	if err := validateOpeningProofShape(&proof, shapes, shifts, sizes, pcs.params.NumQueries); err != nil {
		return err
	}

	// 3- Replay the prover's alpha_DEEP derivation: register, bind values
	//    in per-polynomial order, sample.
	if err := fs.NewChallenge(deepAlphaName); err != nil {
		return fmt.Errorf("fri: PCS.Verify: register alpha_DEEP: %w", err)
	}
	if err := bindClaimedValuesByPolynomialOrder(fs, proof.ClaimedValues, shifts, sizes); err != nil {
		return err
	}
	alphaOut, err := fs.ComputeChallenge(deepAlphaName)
	if err != nil {
		return fmt.Errorf("fri: PCS.Verify: sample alpha_DEEP: %w", err)
	}
	alpha := hash.OutputToExt(alphaOut)

	// 4- Verify the multi-degree FRI proof on the declared DEEP roots.
	sizesDesc := sizesDescFromSizes(sizes)
	if err := Verify(*pcs.params, proof.DeepQuotientRoots, sizesDesc, proof.FRIProof, fs); err != nil {
		return fmt.Errorf("fri: PCS.Verify: FRI proof: %w", err)
	}

	// 5- Extract per-query FRI positions from the proof. The FRI prover
	//    records each full-domain query row in the first FRI layer; these
	//    rows drive both committed-tree sampling and the DEEP bridge.
	queryPositions, err := extractFRIQueryPositions(proof.FRIProof, pcs.params.NumQueries)
	if err != nil {
		return fmt.Errorf("fri: PCS.Verify: %w", err)
	}

	// 6- Authenticate every (query, batch) Merkle opening against the
	//    declared roots. For multi-group batches this also re-hashes the
	//    per-injection-level raw rows and matches them against the
	//    Proof.InjectionLeaves crossed by each complete path.
	if err := verifyAllPointSamplings(pcs, roots, shapes, queryPositions, proof.PointSamplings); err != nil {
		return err
	}

	// 7- Bridge: recompute DQ_N(X), DQ_N(-X) from raw rows + claimed
	//    values in per-polynomial order, compare to FRI level leaves.
	if err := checkFRIBridgeByPolynomial(pcs, &proof, sizes, shapes, shifts, alpha, zeta, queryPositions); err != nil {
		return err
	}

	return nil
}

// validateOpeningProofShape checks that the nested ClaimedValues /
// PointSamplings / DeepQuotientRoots shapes line up with shapes/shifts
// and with the distinct-size count derived from verifier-side shapes.
func validateOpeningProofShape(
	proof *OpeningProof,
	shapes []BatchShapes,
	shifts []BatchShifts,
	sizes [][]int,
	numQueries int,
) error {
	for b, batchSh := range shifts {
		cv := proof.ClaimedValues[b]
		if len(cv) != len(batchSh) {
			return fmt.Errorf("fri: PCS.Verify: ClaimedValues[%d] has %d groups, shifts[%d] has %d", b, len(cv), b, len(batchSh))
		}
		for g, gShifts := range batchSh {
			if len(cv[g].Base) != len(gShifts.Base) {
				return fmt.Errorf("fri: PCS.Verify: ClaimedValues[%d][%d].Base width %d != %d", b, g, len(cv[g].Base), len(gShifts.Base))
			}
			if len(cv[g].Ext) != len(gShifts.Ext) {
				return fmt.Errorf("fri: PCS.Verify: ClaimedValues[%d][%d].Ext width %d != %d", b, g, len(cv[g].Ext), len(gShifts.Ext))
			}
			for i, ss := range gShifts.Base {
				if len(cv[g].Base[i]) != len(ss) {
					return fmt.Errorf("fri: PCS.Verify: ClaimedValues[%d][%d].Base[%d] = %d values, shifts %d", b, g, i, len(cv[g].Base[i]), len(ss))
				}
			}
			for i, ss := range gShifts.Ext {
				if len(cv[g].Ext[i]) != len(ss) {
					return fmt.Errorf("fri: PCS.Verify: ClaimedValues[%d][%d].Ext[%d] = %d values, shifts %d", b, g, i, len(cv[g].Ext[i]), len(ss))
				}
			}
		}
	}

	sizesDesc := sizesDescFromSizes(sizes)
	if len(proof.DeepQuotientRoots) != len(sizesDesc) {
		return fmt.Errorf("fri: PCS.Verify: DeepQuotientRoots has %d entries, expected %d (distinct sizes)", len(proof.DeepQuotientRoots), len(sizesDesc))
	}

	if len(proof.PointSamplings) != numQueries {
		return fmt.Errorf("fri: PCS.Verify: PointSamplings has %d queries, expected %d", len(proof.PointSamplings), numQueries)
	}
	for q, qSamples := range proof.PointSamplings {
		if len(qSamples) != len(shapes) {
			return fmt.Errorf("fri: PCS.Verify: PointSamplings[%d] has %d batches, expected %d", q, len(qSamples), len(shapes))
		}
		for b, wp := range qSamples {
			injOrder := injectionOrderForBatch(shapes[b])
			if len(injOrder) == 0 {
				return fmt.Errorf("fri: PCS.Verify: PointSamplings[%d][%d] has no group shapes", q, b)
			}
			if len(wp.Injections) != len(injOrder)-1 {
				return fmt.Errorf("fri: PCS.Verify: PointSamplings[%d][%d] has %d Injections, expected %d", q, b, len(wp.Injections), len(injOrder)-1)
			}
			topShape := shapes[b][injOrder[0]]
			if err := checkRawRowWidth(wp.TopRows.Lo, topShape); err != nil {
				return fmt.Errorf("fri: PCS.Verify: PointSamplings[%d][%d].TopRows.Lo: %w", q, b, err)
			}
			if err := checkRawRowWidth(wp.TopRows.Hi, topShape); err != nil {
				return fmt.Errorf("fri: PCS.Verify: PointSamplings[%d][%d].TopRows.Hi: %w", q, b, err)
			}
			for k, declIdx := range injOrder[1:] {
				gs := shapes[b][declIdx]
				rows := wp.Injections[k].Rows
				if err := checkRawRowWidth(rows.Lo, gs); err != nil {
					return fmt.Errorf("fri: PCS.Verify: PointSamplings[%d][%d].Injections[%d].Rows.Lo: %w", q, b, k, err)
				}
				if err := checkRawRowWidth(rows.Hi, gs); err != nil {
					return fmt.Errorf("fri: PCS.Verify: PointSamplings[%d][%d].Injections[%d].Rows.Hi: %w", q, b, k, err)
				}
			}
		}
	}
	return nil
}

// injectionOrderForBatch returns, for one batch's GroupShape slice, the
// indices into shapes in *decreasing row-count* order -- the same
// order PCS.Commit places the per-Group LeafSources in Committed.Sources.
// WMerkleProof stores order[0] in TopRows and order[1:] in Injections.
func injectionOrderForBatch(batchShapes BatchShapes) []int {
	order := make([]int, len(batchShapes))
	for i := range order {
		order[i] = i
	}
	sort.SliceStable(order, func(a, b int) bool {
		return batchShapes[order[a]].Rows > batchShapes[order[b]].Rows
	})
	return order
}

// extractFRIQueryPositions reads the per-query positions out of the FRI
// proof. The query position for query q is the Row of the first layer of
// FRIQueries[q] (a property the FRI prover establishes; the verifier
// re-derives the same s via the transcript inside fri.Verify but does not
// expose it, so we read it back from the proof).
func extractFRIQueryPositions(prf Proof, numQueries int) ([]int, error) {
	if len(prf.FRIQueries) != numQueries {
		return nil, fmt.Errorf("FRIQueries has %d entries, expected %d", len(prf.FRIQueries), numQueries)
	}
	out := make([]int, numQueries)
	for q := range prf.FRIQueries {
		if len(prf.FRIQueries[q].Layers) == 0 {
			return nil, fmt.Errorf("FRIQueries[%d].Layers is empty", q)
		}
		out[q] = prf.FRIQueries[q].Layers[0].Row
	}
	return out, nil
}

// verifyAllPointSamplings authenticates every (query, batch) compact Merkle
// opening in proof.PointSamplings against the corresponding batch root.
// For multi-group batches, the compact verifier folds path-side injected rows
// directly and checks companion injected rows against the sibling digest on the
// shared top Merkle path.
func verifyAllPointSamplings(
	pcs *PCS,
	roots []hash.Digest,
	shapes []BatchShapes,
	queryPositions []int,
	pointSamplings [][]WMerkleProof,
) error {
	for q, sQ := range queryPositions {
		for b, wp := range pointSamplings[q] {
			if err := verifyOneWMerkleProof(pcs.leafHasher, pcs.nodeHasher, roots[b], shapes[b], wp, sQ, pcs.params.N); err != nil {
				return fmt.Errorf("fri: PCS.Verify: query %d, batch %d: %w", q, b, err)
			}
		}
	}
	return nil
}

// verifyOneWMerkleProof checks one WMerkleProof against the batch's
// Merkle root using the batch's per-Group shapes for size routing.
func verifyOneWMerkleProof(
	leafHasher LeafHasher,
	nodeHasher NodeHasher,
	root hash.Digest,
	batchShapes BatchShapes,
	wp WMerkleProof,
	sFull int,
	maxRows int,
) error {
	if sFull < 0 {
		return fmt.Errorf("query row %d must be non-negative", sFull)
	}
	if maxRows <= 0 || maxRows&(maxRows-1) != 0 {
		return fmt.Errorf("maxRows=%d must be a positive power of two", maxRows)
	}

	// Re-order the GroupShape entries to match the compact proof's
	// decreasing-size convention.
	injOrder := injectionOrderForBatch(batchShapes)
	if len(injOrder) == 0 {
		return fmt.Errorf("WMerkleProof has no group shapes")
	}
	topRows := batchShapes[injOrder[0]].Rows
	if topRows <= 0 || topRows&(topRows-1) != 0 {
		return fmt.Errorf("top rows %d must be a positive power of two", topRows)
	}
	topPairLeaves, err := pairLeafCount(topRows)
	if err != nil {
		return fmt.Errorf("top rows: %w", err)
	}
	if topRows > maxRows {
		return fmt.Errorf("top rows %d exceeds maxRows %d", topRows, maxRows)
	}

	injectionWidths := make([]int, len(injOrder)-1)
	injectionByWidth := make(map[int]int, len(injOrder)-1)
	prevWidth := topPairLeaves
	for k := 1; k < len(injOrder); k++ {
		rows := batchShapes[injOrder[k]].Rows
		if rows <= 0 || rows&(rows-1) != 0 {
			return fmt.Errorf("injection %d rows %d must be a positive power of two", k-1, rows)
		}
		if rows > maxRows {
			return fmt.Errorf("injection %d rows %d exceeds maxRows %d", k-1, rows, maxRows)
		}
		width, err := pairLeafCount(rows)
		if err != nil {
			return fmt.Errorf("injection %d rows: %w", k-1, err)
		}
		if width >= prevWidth {
			return fmt.Errorf("injection pair leaves must be strictly decreasing (got %d after %d)", width, prevWidth)
		}
		injIdx := k - 1
		injectionWidths[injIdx] = width
		injectionByWidth[width] = injIdx
		prevWidth = width
	}

	if len(wp.Injections) != len(injectionWidths) {
		return fmt.Errorf("WMerkleProof has %d injections, expected %d", len(wp.Injections), len(injectionWidths))
	}
	if len(wp.Path.InjectionLeaves) != 0 && len(wp.Path.InjectionLeaves) != len(injectionWidths) {
		return fmt.Errorf("top path has %d injection leaves, expected 0 or %d", len(wp.Path.InjectionLeaves), len(injectionWidths))
	}

	topReductionGlobal := log2(maxRows) - log2(topRows)
	if topReductionGlobal < 0 {
		return fmt.Errorf("top rows %d exceeds maxRows %d", topRows, maxRows)
	}
	topRow := sFull >> topReductionGlobal
	topLo, topHi := siblingRows(topRow)
	if topHi >= topRows {
		return fmt.Errorf("top row pair (%d,%d) out of range [0,%d)", topLo, topHi, topRows)
	}
	topPairIdx := topLo / 2
	if wp.Path.LeafIdx != topPairIdx {
		return fmt.Errorf("top Path.LeafIdx = %d, want %d", wp.Path.LeafIdx, topPairIdx)
	}
	depth := log2(topPairLeaves)
	if len(wp.Path.Siblings) != depth {
		return fmt.Errorf("top path has %d siblings, expected %d", len(wp.Path.Siblings), depth)
	}

	h := hashRawRowPair(leafHasher, wp.TopRows)
	pathIdx := wp.Path.LeafIdx
	for k, sibling := range wp.Path.Siblings {
		if pathIdx&1 == 0 {
			h = nodeHasher.HashNode(h, sibling)
		} else {
			h = nodeHasher.HashNode(sibling, h)
		}
		pathIdx >>= 1

		width := 1 << (depth - k - 1)
		injIdx, ok := injectionByWidth[width]
		if !ok {
			continue
		}

		rows, err := rawRowsForInjection(wp, injIdx)
		if err != nil {
			return err
		}
		groupShapeIdx := injOrder[injIdx+1]
		groupRows := batchShapes[groupShapeIdx].Rows
		groupIdx := injIdx + 1
		globalReduction := log2(maxRows) - log2(groupRows)
		if globalReduction < 0 {
			return fmt.Errorf("group %d rows %d exceeds maxRows %d", groupIdx, groupRows, maxRows)
		}
		row := sFull >> globalReduction
		lo, hi := siblingRows(row)
		if hi >= groupRows {
			return fmt.Errorf("group %d row pair (%d,%d) out of range [0,%d)", groupIdx, lo, hi, groupRows)
		}
		pairIdx := lo / 2
		pathPairAtWidth := pathIdx
		if pathPairAtWidth != pairIdx {
			return fmt.Errorf("group %d path pair at width = %d, want %d", groupIdx, pathPairAtWidth, pairIdx)
		}

		pairDigest := hashRawRowPair(leafHasher, rows)
		if len(wp.Path.InjectionLeaves) != 0 && pairDigest != wp.Path.InjectionLeaves[injIdx] {
			return fmt.Errorf("group %d injection pair hash mismatch", groupIdx)
		}
		h = nodeHasher.HashNode(h, pairDigest)
	}

	if h != root {
		return fmt.Errorf("Merkle path does not authenticate under the given root")
	}

	return nil
}

func checkRawRowWidth(row RawRow, shape GroupShape) error {
	if len(row.RawRowBase) != shape.BaseWidth {
		return fmt.Errorf("RawRowBase width %d != %d", len(row.RawRowBase), shape.BaseWidth)
	}
	if len(row.RawRowExt) != shape.ExtWidth {
		return fmt.Errorf("RawRowExt width %d != %d", len(row.RawRowExt), shape.ExtWidth)
	}
	return nil
}

func rawRowsForInjection(wp WMerkleProof, injIdx int) (RawRowPair, error) {
	if injIdx < 0 || injIdx >= len(wp.Injections) {
		return RawRowPair{}, fmt.Errorf("injection index %d out of compact proof range", injIdx)
	}
	return wp.Injections[injIdx].Rows, nil
}

func rawRowsForGroup(wp WMerkleProof, groupIdx int) (RawRowPair, error) {
	if groupIdx == 0 {
		return wp.TopRows, nil
	}
	rows, err := rawRowsForInjection(wp, groupIdx-1)
	if err != nil {
		return RawRowPair{}, fmt.Errorf("group index %d: %w", groupIdx, err)
	}
	return rows, nil
}

// checkFRIBridgeByPolynomial is the verifier-side counterpart of
// computeDeepQuotientCodewordsByPolynomial. For each native size N, alpha
// powers are consumed once per polynomial in batch/group declaration order.
// Multiple shifts of the same polynomial are summed before applying the
// polynomial's alpha power.
func checkFRIBridgeByPolynomial(
	pcs *PCS,
	proof *OpeningProof,
	sizes [][]int,
	shapes [][]GroupShape,
	shifts []BatchShifts,
	alpha ext.E6,
	zeta ext.E6,
	queryPositions []int,
) error {
	// Per-batch injection-order maps, computed once.
	injOrderByBatch := make([][]int, len(shapes))
	for b, batchShapes := range shapes {
		injOrderByBatch[b] = injectionOrderForBatch(batchShapes)
	}
	declToInjIdx := func(b, g int) int {
		for injIdx, declIdx := range injOrderByBatch[b] {
			if declIdx == g {
				return injIdx
			}
		}
		return -1
	}

	sizesDesc := sizesDescFromSizes(sizes)

	// Precompute per-size generators and omega-shift tables so that
	// koalabear.Generator (which internally calls Exp) and the per-shift Exp
	// are not repeated once per query.
	type sizePrecomp struct {
		ratGen      koalabear.Element
		omegaTable  map[int]koalabear.Element // normalizedShift → traceGen^shift
		totalShifts int                        // sum of len(shifts) for all polys of this N
	}
	sizePrecomps := make(map[int]sizePrecomp, len(sizesDesc))
	for _, N := range sizesDesc {
		ratN := int(pcs.rate) * N
		ratGen, err := koalabear.Generator(uint64(ratN))
		if err != nil {
			return fmt.Errorf("fri: PCS.Verify: precompute ratGen for N=%d: %w", N, err)
		}
		traceGen, err := koalabear.Generator(uint64(N))
		if err != nil {
			return fmt.Errorf("fri: PCS.Verify: precompute traceGen for N=%d: %w", N, err)
		}
		omegaTable := make(map[int]koalabear.Element)
		var totalShifts int
		for b, batchSizes := range sizes {
			for g, groupSize := range batchSizes {
				if groupSize != N {
					continue
				}
				gShifts := shifts[b][g]
				for _, ss := range gShifts.Base {
					totalShifts += len(ss)
					for _, s := range ss {
						ns := normalizeShift(s, N)
						if _, ok := omegaTable[ns]; !ok {
							var om koalabear.Element
							om.ExpInt64(traceGen, int64(ns))
							omegaTable[ns] = om
						}
					}
				}
				for _, ss := range gShifts.Ext {
					totalShifts += len(ss)
					for _, s := range ss {
						ns := normalizeShift(s, N)
						if _, ok := omegaTable[ns]; !ok {
							var om koalabear.Element
							om.ExpInt64(traceGen, int64(ns))
							omegaTable[ns] = om
						}
					}
				}
			}
		}
		sizePrecomps[N] = sizePrecomp{ratGen: ratGen, omegaTable: omegaTable, totalShifts: totalShifts}
	}

	// Largest denom buffer needed: 2 entries per shift, for the largest size group.
	maxTotalShifts := 0
	for _, sp := range sizePrecomps {
		if sp.totalShifts > maxTotalShifts {
			maxTotalShifts = sp.totalShifts
		}
	}

	// Each query is independent: it reads a disjoint slice of the proof
	// (PointSamplings[q], FRIQueries[q], LevelQueries[*][q]) and writes only
	// to goroutine-local accumulators. We parallelise over queries and collect
	// the first failure via an atomic.
	var bridgeErr atomic.Value
	parallel.Execute(len(queryPositions), func(start, end int) {
		// One denom scratch buffer per goroutine, reused across (q, N) iterations
		// to avoid one allocation per inner loop iteration.
		denomsBuf := make([]ext.E6, 2*maxTotalShifts)

		for q := start; q < end; q++ {
			sFull := queryPositions[q]
			for sizeIdx, N := range sizesDesc {
				ratN := int(pcs.rate) * N
				bitsReduced := log2(pcs.params.N) - log2(ratN)
				if bitsReduced < 0 {
					bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: bridge size %d has ratN=%d larger than max rows %d", N, ratN, pcs.params.N))
					return
				}
				row := sFull >> bitsReduced
				lo, hi := siblingRows(row)

				// X = omega_{rate*N}^bitrev(lo) (base), lifted; -X is the
				// companion row hi under bit-reversed row ordering.
				sp := sizePrecomps[N]
				var XBase, negXBase, hiBase koalabear.Element
				XBase.ExpInt64(sp.ratGen, int64(bitReverseIndex(lo, ratN)))
				hiBase.ExpInt64(sp.ratGen, int64(bitReverseIndex(hi, ratN)))
				negXBase.Neg(&XBase)
				if !hiBase.Equal(&negXBase) {
					bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: bridge row companion mismatch for ratN=%d lo=%d hi=%d", ratN, lo, hi))
					return
				}
				X := hash.LiftBaseToExt(XBase)
				negX := hash.LiftBaseToExt(negXBase)

				// Pass 1: fill all denominators for this (query, size) in poly-declaration order.
				// denoms[2k]   = zeta*omega^s - X
				// denoms[2k+1] = zeta*omega^s - negX
				denoms := denomsBuf[:2*sp.totalShifts]
				k := 0
				for b, batchSizes := range sizes {
					for g, groupSize := range batchSizes {
						if groupSize != N {
							continue
						}
						gShifts := shifts[b][g]
						for _, ss := range gShifts.Base {
							for _, s := range ss {
								omegaShift := sp.omegaTable[normalizeShift(s, N)]
								var zs ext.E6
								zs.MulByElement(&zeta, &omegaShift)
								denoms[2*k].Sub(&zs, &X)
								denoms[2*k+1].Sub(&zs, &negX)
								k++
							}
						}
						for _, ss := range gShifts.Ext {
							for _, s := range ss {
								omegaShift := sp.omegaTable[normalizeShift(s, N)]
								var zs ext.E6
								zs.MulByElement(&zeta, &omegaShift)
								denoms[2*k].Sub(&zs, &X)
								denoms[2*k+1].Sub(&zs, &negX)
								k++
							}
						}
					}
				}
				invDenoms := ext.BatchInvertE6(denoms)

				// Pass 2: accumulate DQ_P and DQ_Q using the batch-inverted denominators.
				var DQ_P, DQ_Q ext.E6
				var alphaRunning ext.E6
				alphaRunning.SetOne()
				k = 0
				for b, batchSizes := range sizes {
					for g, groupSize := range batchSizes {
						if groupSize != N {
							continue
						}
						injIdx := declToInjIdx(b, g)
						if injIdx < 0 {
							bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: cannot map (batch=%d, group=%d) to compact proof group index", b, g))
							return
						}
						raw, err := rawRowsForGroup(proof.PointSamplings[q][b], injIdx)
						if err != nil {
							bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: compact proof group %d: %w", injIdx, err))
							return
						}
						gShifts := shifts[b][g]
						gValues := proof.ClaimedValues[b][g]
						for i, ss := range gShifts.Base {
							leafP := hash.LiftBaseToExt(raw.Lo.RawRowBase[i])
							leafQ := hash.LiftBaseToExt(raw.Hi.RawRowBase[i])
							accumulateBridgeBundle(ss, gValues.Base[i], alphaRunning, leafP, leafQ, invDenoms[2*k:], &DQ_P, &DQ_Q)
							k += len(ss)
							alphaRunning.Mul(&alphaRunning, &alpha)
						}
						for i, ss := range gShifts.Ext {
							var leafP, leafQ ext.E6
							leafP.Set(&raw.Lo.RawRowExt[i])
							leafQ.Set(&raw.Hi.RawRowExt[i])
							accumulateBridgeBundle(ss, gValues.Ext[i], alphaRunning, leafP, leafQ, invDenoms[2*k:], &DQ_P, &DQ_Q)
							k += len(ss)
							alphaRunning.Mul(&alphaRunning, &alpha)
						}
					}
				}

				var actualP, actualQ ext.E6
				if sizeIdx == 0 {
					layer := proof.FRIProof.FRIQueries[q].Layers[0]
					if layer.Field != field.Ext {
						bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: bridge query %d level 0: expected ext FRI layer, got %s", q, layer.Field))
						return
					}
					actualP = layer.LeafPExt
					actualQ = layer.LeafQExt
				} else {
					if sizeIdx-1 >= len(proof.FRIProof.LevelQueries) || q >= len(proof.FRIProof.LevelQueries[sizeIdx-1]) {
						bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: bridge query %d level %d: missing LevelQueries entry", q, sizeIdx))
						return
					}
					lq := proof.FRIProof.LevelQueries[sizeIdx-1][q]
					if lq.Field != field.Ext {
						bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: bridge query %d level %d: expected ext FRI level query, got %s", q, sizeIdx, lq.Field))
						return
					}
					actualP = lq.LeafPExt
					actualQ = lq.LeafQExt
				}

				if !DQ_P.Equal(&actualP) {
					bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: bridge query %d level %d (N=%d): DQ(X) mismatch: got %s, want %s", q, sizeIdx, N, DQ_P.String(), actualP.String()))
					return
				}
				if !DQ_Q.Equal(&actualQ) {
					bridgeErr.CompareAndSwap(nil, fmt.Errorf("fri: PCS.Verify: bridge query %d level %d (N=%d): DQ(-X) mismatch: got %s, want %s", q, sizeIdx, N, DQ_Q.String(), actualQ.String()))
					return
				}
			}
		}
	})
	if err, _ := bridgeErr.Load().(error); err != nil {
		return err
	}
	return nil
}

// accumulateBridgeBundle adds to DQ_P and DQ_Q the contribution of one
// polynomial's shift bundle, using denominators that were already batch-inverted.
// invDenoms must have at least 2*len(shifts) elements where:
//
//	invDenoms[2k]   = 1 / (zeta·ω^shifts[k] - X)
//	invDenoms[2k+1] = 1 / (zeta·ω^shifts[k] - negX)
func accumulateBridgeBundle(
	shifts []int,
	values []ext.E6,
	scale ext.E6,
	leafP, leafQ ext.E6,
	invDenoms []ext.E6,
	DQ_P, DQ_Q *ext.E6,
) {
	var bundleP, bundleQ ext.E6
	for k := range shifts {
		var num ext.E6
		num.Sub(&values[k], &leafP)
		num.Mul(&num, &invDenoms[2*k])
		bundleP.Add(&bundleP, &num)

		num.Sub(&values[k], &leafQ)
		num.Mul(&num, &invDenoms[2*k+1])
		bundleQ.Add(&bundleQ, &num)
	}
	bundleP.Mul(&bundleP, &scale)
	DQ_P.Add(DQ_P, &bundleP)
	bundleQ.Mul(&bundleQ, &scale)
	DQ_Q.Add(DQ_Q, &bundleQ)
}
