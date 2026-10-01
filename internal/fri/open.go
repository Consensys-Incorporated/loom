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

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/poly"
)

// deepAlphaName is the transcript challenge name under which Open binds
// the per-polynomial claimed evaluations and from which the DEEP batching
// challenge alpha_DEEP is sampled. Kept as a private
// constant so the existing outer-prover code (which uses
// constants.DEEP_ALPHA with the same string value) remains source-
// compatible until the migration PR rewires it.
const deepAlphaName = "alpha_DEEP"

// OpenConfig configures an Open call.
type OpenConfig struct {
	DomainCache *poly.DomainCache
	DeepClasses [][]int // see WithDeepClasses; nil = one class per size
}

// OpenOption configures Open.
type OpenOption func(c *OpenConfig) error

// WithOpenDomainCache lets Open reuse a domain cache shared with Commit
// so FFT-domain pre-computations are not duplicated across calls.
func WithOpenDomainCache(cache *poly.DomainCache) OpenOption {
	return func(c *OpenConfig) error {
		c.DomainCache = cache
		return nil
	}
}

// ClaimedValuesOnly evaluates every polynomial in batches at every shift
// listed in shifts and returns the per-batch BatchClaimedValues. No
// transcript activity, no DEEP-quotient construction, no FRI. Suited to
// SkipFRI-style smoke tests where the caller wants the AIR-check-side
// values without paying for the PCS proof.
//
// The output shape mirrors shifts: a value per (batch, group, base/ext
// rail, polyIdx, kth_shift) tuple, evaluated at zeta * omega_N^shift.
// Identical content to the OpeningProof.ClaimedValues that pcs.Open
// would have produced for the same inputs.
func (pcs *PCS) ClaimedValuesOnly(
	batches []Batch,
	shifts []BatchShifts,
	zeta ext.E6,
	opts ...OpenOption,
) ([]BatchClaimedValues, error) {
	var config OpenConfig
	for _, opt := range opts {
		if err := opt(&config); err != nil {
			return nil, err
		}
	}
	domainCache := config.DomainCache
	if domainCache == nil {
		domainCache = &poly.DomainCache{}
	}
	if err := validateBatchShifts(batches, shifts); err != nil {
		return nil, err
	}
	return computeClaimedValues(batches, shifts, zeta, domainCache)
}

// Open produces an OpeningProof that every polynomial in batches
// evaluates to the listed values at zeta and at the rotation shifts in
// shifts. committed[b] must have been returned by Commit(batches[b], ...).
// The shared Fiat-Shamir transcript fs must already have absorbed each
// committed[b].Tree.Root() at the round the caller chose, and must have
// sampled zeta.
//
// Open registers alpha_DEEP and FRI-internal challenge names on fs
// itself; the caller MUST NOT pre-register any of those names. Open is
// responsible for binding claimed values in per-polynomial DEEP order,
// sampling alpha_DEEP, building per-size DEEP-quotient codewords,
// committing them as multi-degree FRI levels, running fri.Prove, and
// packaging per-query / per-batch Merkle openings.
func (pcs *PCS) Open(
	batches []Batch,
	committed []Committed,
	shifts []BatchShifts,
	zeta ext.E6,
	fs *fiatshamir.Transcript,
	opts ...OpenOption,
) (OpeningProof, error) {
	if pcs.params == nil {
		return OpeningProof{}, fmt.Errorf("fri: PCS.Open requires Params; construct PCS via NewPCSWithParams")
	}
	if len(committed) != len(batches) {
		return OpeningProof{}, fmt.Errorf("fri: PCS.Open: committed has %d entries, batches has %d", len(committed), len(batches))
	}
	if fs == nil {
		return OpeningProof{}, fmt.Errorf("fri: PCS.Open: fs transcript is required")
	}

	var config OpenConfig
	for _, opt := range opts {
		if err := opt(&config); err != nil {
			return OpeningProof{}, err
		}
	}
	domainCache := config.DomainCache
	if domainCache == nil {
		domainCache = &poly.DomainCache{}
	}

	// 1- Validate shape alignment + per-poly shift invariants (non-empty,
	//    no duplicates), then derive the size order used for both
	//    alpha_DEEP bindings and multi-degree FRI levels.
	if err := validateBatchShifts(batches, shifts); err != nil {
		return OpeningProof{}, err
	}
	sizes, err := groupNativeSizesFromBatches(batches)
	if err != nil {
		return OpeningProof{}, err
	}
	plan, err := newDeepPlan(sizes, config.DeepClasses)
	if err != nil {
		return OpeningProof{}, err
	}

	// 2- Claimed values at zeta * omega_N^s for every (b, g, i, s) in
	//    the schedule.
	claimedValues, err := computeClaimedValues(batches, shifts, zeta, domainCache)
	if err != nil {
		return OpeningProof{}, err
	}

	// 3- Pre-register alpha_DEEP. FRI-internal names (fri_fold_*,
	//    fri_level_*_gamma, fri_query_*) are registered inside fri.Prove.
	if err := fs.NewChallenge(deepAlphaName); err != nil {
		return OpeningProof{}, fmt.Errorf("fri: PCS.Open: register alpha_DEEP: %w", err)
	}

	// 4- Bind every claimed value to alpha_DEEP in per-polynomial order: DEEP
	//    class order, batch declaration order, group declaration order, base
	//    polys then ext polys, and shifts in the user's declared order.
	if err := bindClaimedValuesByPolynomialOrder(fs, claimedValues, shifts, plan); err != nil {
		return OpeningProof{}, err
	}

	// 5- Sample alpha_DEEP.
	alphaOut, err := fs.ComputeChallenge(deepAlphaName)
	if err != nil {
		return OpeningProof{}, fmt.Errorf("fri: PCS.Open: sample alpha_DEEP: %w", err)
	}
	alpha := hash.OutputToExt(alphaOut)

	// 6- Build one DEEP-quotient codeword per DEEP class, on the RS-encoded
	//    subgroup of size rate*N of the class's size N.
	deepByClass, err := computeDeepQuotientCodewordsByPolynomial(
		batches, shifts, claimedValues, alpha, zeta, pcs.rate, plan, domainCache,
	)
	if err != nil {
		return OpeningProof{}, err
	}

	// 7- Commit each class's DQ as a fresh FRI level, in level order
	//    (decreasing size, equal sizes in class order). Each level enters at
	//    the round whose running polynomial bound matches its D.
	levels := make([]Level, plan.numClasses())
	deepRoots := make([]hash.Digest, plan.numClasses())
	for l, c := range plan.classAt {
		tree, err := pcs.params.BuildLevelTreeExt(deepByClass[c])
		if err != nil {
			return OpeningProof{}, fmt.Errorf("fri: PCS.Open: BuildLevelTreeExt class %d: %w", c, err)
		}
		levels[l] = Level{
			D:     plan.sizes[c],
			Evals: LevelEvals{Ext: deepByClass[c]},
			Tree:  tree,
		}
		deepRoots[l] = tree.Root()
	}

	// 8- Run multi-degree FRI on the level set.
	friProof, queryPositions, err := Prove(*pcs.params, levels, fs)
	if err != nil {
		return OpeningProof{}, fmt.Errorf("fri: PCS.Open: fri.Prove: %w", err)
	}

	// 9- For each query position, open every committed batch's tree at
	//    the matching folded position and package one compact Merkle proof.
	pointSamplings := make([][]WMerkleProof, len(queryPositions))
	for q, sQ := range queryPositions {
		pointSamplings[q] = make([]WMerkleProof, len(committed))
		for b := range committed {
			wp, err := openCommittedAt(committed[b], sQ, pcs.params.N)
			if err != nil {
				return OpeningProof{}, fmt.Errorf("fri: PCS.Open: query %d, batch %d: %w", q, b, err)
			}
			pointSamplings[q][b] = wp
		}
	}

	return OpeningProof{
		ClaimedValues:     claimedValues,
		DeepQuotientRoots: deepRoots,
		FRIProof:          friProof,
		PointSamplings:    pointSamplings,
	}, nil
}

// bindClaimedValuesByPolynomialOrder binds every claimed value using the
// per-polynomial order. The order matches computeDeepQuotientCodewordsByPolynomial:
// DEEP class order, batch declaration order, group declaration order, base rail
// then extension rail. Inside one polynomial, all requested shifts are bound in
// the user's declared order, while the DEEP quotient consumes only one alpha
// power for that polynomial.
func bindClaimedValuesByPolynomialOrder(
	fs *fiatshamir.Transcript,
	claimedValues []BatchClaimedValues,
	shifts []BatchShifts,
	plan deepPlan,
) error {
	if len(claimedValues) != len(plan.classOf) {
		return fmt.Errorf("fri: bind claimed values: claimedValues has %d entries, batches has %d", len(claimedValues), len(plan.classOf))
	}
	if len(shifts) != len(plan.classOf) {
		return fmt.Errorf("fri: bind claimed values: shifts has %d entries, batches has %d", len(shifts), len(plan.classOf))
	}

	for class, N := range plan.sizes {
		for b, batchClasses := range plan.classOf {
			if len(claimedValues[b]) != len(batchClasses) {
				return fmt.Errorf("fri: bind claimed values: claimedValues[%d] has %d groups, batch %d has %d", b, len(claimedValues[b]), b, len(batchClasses))
			}
			if len(shifts[b]) != len(batchClasses) {
				return fmt.Errorf("fri: bind claimed values: shifts[%d] has %d groups, batch %d has %d", b, len(shifts[b]), b, len(batchClasses))
			}
			for g, groupClass := range batchClasses {
				if groupClass != class {
					continue
				}
				gValues := claimedValues[b][g]
				gShifts := shifts[b][g]
				if len(gValues.Base) != len(gShifts.Base) {
					return fmt.Errorf("fri: bind claimed values: claimedValues[%d][%d].Base has %d polys, shifts has %d", b, g, len(gValues.Base), len(gShifts.Base))
				}
				if len(gValues.Ext) != len(gShifts.Ext) {
					return fmt.Errorf("fri: bind claimed values: claimedValues[%d][%d].Ext has %d polys, shifts has %d", b, g, len(gValues.Ext), len(gShifts.Ext))
				}

				for i, ss := range gShifts.Base {
					if len(gValues.Base[i]) != len(ss) {
						return fmt.Errorf("fri: bind claimed values: claimedValues[%d][%d].Base[%d] has %d values, shifts has %d", b, g, i, len(gValues.Base[i]), len(ss))
					}
					for k, s := range ss {
						v := gValues.Base[i][k]
						if err := fs.Bind(deepAlphaName, hash.ExtToElements(v)); err != nil {
							return fmt.Errorf("fri: bind claimed value (size=%d batch=%d group=%d field=base poly=%d shift=%d): %w",
								N, b, g, i, s, err)
						}
					}
				}
				for i, ss := range gShifts.Ext {
					if len(gValues.Ext[i]) != len(ss) {
						return fmt.Errorf("fri: bind claimed values: claimedValues[%d][%d].Ext[%d] has %d values, shifts has %d", b, g, i, len(gValues.Ext[i]), len(ss))
					}
					for k, s := range ss {
						v := gValues.Ext[i][k]
						if err := fs.Bind(deepAlphaName, hash.ExtToElements(v)); err != nil {
							return fmt.Errorf("fri: bind claimed value (size=%d batch=%d group=%d field=ext poly=%d shift=%d): %w",
								N, b, g, i, s, err)
						}
					}
				}
			}
		}
	}
	return nil
}

// openCommittedAt opens a Committed batch at the full FRI query row sQ. It
// builds the compact proof shape: one top-level row pair, one Merkle path from
// the top row-pair leaf, and one raw row pair per injected smaller group.
func openCommittedAt(c Committed, sQ int, maxRows int) (WMerkleProof, error) {
	if c.Tree.Tree == nil {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: WMerkleTree is uninitialised")
	}
	topPairLeaves := c.Tree.NumLeaves()
	if topPairLeaves == 0 {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: empty WMerkleTree")
	}
	if len(c.Sources) == 0 {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: no LeafSources retained")
	}
	if maxRows <= 0 || maxRows&(maxRows-1) != 0 {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: maxRows=%d must be a positive power of two", maxRows)
	}

	topRows := leafSourceRows(c.Sources[0])
	topPairLeavesFromSource, err := pairLeafCount(topRows)
	if err != nil {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: top source rows: %w", err)
	}
	if topPairLeavesFromSource != topPairLeaves {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: top source pair leaves %d != tree leaves %d", topPairLeavesFromSource, topPairLeaves)
	}
	if topRows > maxRows {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: top rows %d exceeds maxRows %d", topRows, maxRows)
	}

	topGlobalReduction := log2(maxRows) - log2(topRows)
	if topGlobalReduction < 0 {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: top rows %d exceeds maxRows %d", topRows, maxRows)
	}
	topRow := sQ >> topGlobalReduction
	topLo, topHi := siblingRows(topRow)
	topRowPair, err := rawRowPairFromSource(c.Sources[0], topLo, topHi)
	if err != nil {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: top rows: %w", err)
	}
	topPairIdx := topLo / 2
	path, err := c.Tree.OpenProof(topPairIdx)
	if err != nil {
		return WMerkleProof{}, fmt.Errorf("openCommittedAt: top proof pair=%d: %w", topPairIdx, err)
	}

	injections := make([]WMerkleInjectionOpening, 0, len(c.Sources)-1)
	for k, src := range c.Sources[1:] {
		sourceIdx := k + 1
		groupRows := leafSourceRows(src)
		if groupRows <= 0 {
			return WMerkleProof{}, fmt.Errorf("openCommittedAt: source %d has insufficient encoded rows %d", sourceIdx, groupRows)
		}
		if groupRows > maxRows {
			return WMerkleProof{}, fmt.Errorf("openCommittedAt: source %d rows %d exceeds maxRows %d", sourceIdx, groupRows, maxRows)
		}
		if groupRows&(groupRows-1) != 0 {
			return WMerkleProof{}, fmt.Errorf("openCommittedAt: source %d rows %d is not a power of two", sourceIdx, groupRows)
		}
		groupPairLeaves, err := pairLeafCount(groupRows)
		if err != nil {
			return WMerkleProof{}, fmt.Errorf("openCommittedAt: source %d rows: %w", sourceIdx, err)
		}

		globalReduction := log2(maxRows) - log2(groupRows)
		row := sQ >> globalReduction
		lo, hi := siblingRows(row)
		rows, err := rawRowPairFromSource(src, lo, hi)
		if err != nil {
			return WMerkleProof{}, fmt.Errorf("openCommittedAt: source %d rows: %w", sourceIdx, err)
		}

		topReduction := log2(topPairLeavesFromSource) - log2(groupPairLeaves)
		if topReduction < 0 {
			return WMerkleProof{}, fmt.Errorf("openCommittedAt: source %d rows %d exceeds top rows %d", sourceIdx, groupRows, topRows)
		}
		pathPairAtWidth := topPairIdx >> topReduction
		if want := lo / 2; pathPairAtWidth != want {
			return WMerkleProof{}, fmt.Errorf("openCommittedAt: source %d path pair at width = %d, want %d", sourceIdx, pathPairAtWidth, want)
		}

		injections = append(injections, WMerkleInjectionOpening{
			Rows: rows,
		})
	}

	return WMerkleProof{
		TopRows:    topRowPair,
		Path:       path,
		Injections: injections,
	}, nil
}

func leafSourceRows(src LeafSource) int {
	if len(src.Base) > 0 {
		return len(src.Base[0])
	}
	if len(src.Ext) > 0 {
		return len(src.Ext[0])
	}
	return 0
}

func rawRowPairFromSource(src LeafSource, lo int, hi int) (RawRowPair, error) {
	loRow, err := rawRowFromSource(src, lo)
	if err != nil {
		return RawRowPair{}, fmt.Errorf("lo row %d: %w", lo, err)
	}
	hiRow, err := rawRowFromSource(src, hi)
	if err != nil {
		return RawRowPair{}, fmt.Errorf("hi row %d: %w", hi, err)
	}
	return RawRowPair{Lo: loRow, Hi: hiRow}, nil
}

func rawRowFromSource(src LeafSource, row int) (RawRow, error) {
	rows := leafSourceRows(src)
	if row < 0 || row >= rows {
		return RawRow{}, fmt.Errorf("row out of range [0, %d)", rows)
	}
	baseRow := make([]koalabear.Element, len(src.Base))
	for i, p := range src.Base {
		baseRow[i].Set(&p[row])
	}
	extRow := make([]ext.E6, len(src.Ext))
	for i, p := range src.Ext {
		extRow[i].Set(&p[row])
	}
	return RawRow{RawRowBase: baseRow, RawRowExt: extRow}, nil
}
