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

	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
)

// PCS is a batch polynomial commitment scheme built on top of RSCommit and
// multi-degree FRI. It is the entry point intended to subsume direct use of
// RSCommit and the prover-side DEEP/FRI machinery: callers Commit each
// independent batch of polynomials, bind the returned root to their
// transcript at the appropriate Fiat-Shamir round, and hand the whole list
// to Open at zeta to produce one OpeningProof.
//
// PCS keeps no global state across Commit calls -- the per-batch Committed
// blob carries the Merkle tree and the per-Group RS-encoded LeafSources
// that Open consumes.
//
// Open requires multi-degree FRI parameters; build the PCS via
// NewPCSWithParams when Open will be called. The minimal NewPCS
// constructor is enough for Commit-only callers (e.g. setup-time fixed
// column commitments).
type PCS struct {
	leafHasher LeafHasher
	nodeHasher NodeHasher
	rate       uint64

	// params carries the multi-degree FRI configuration consumed by Open and
	// Verify. nil when the PCS was constructed via NewPCS for Commit-only use.
	params *Params
}

// NewPCS constructs a PCS bound to a Reed-Solomon blowup factor (rate) and
// the leaf/node hashers used at every Merkle tree level. Suitable for
// Commit-only callers. Open and Verify require Params -- use NewPCSWithParams
// when the PCS will be opened or verified.
func NewPCS(rate uint64, leafHasher LeafHasher, nodeHasher NodeHasher) PCS {
	return PCS{
		leafHasher: leafHasher,
		nodeHasher: nodeHasher,
		rate:       rate,
	}
}

// NewPCSWithParams constructs a PCS bound to the multi-degree FRI
// parameters (carrying the leaf/node hashers and the rate = params.N /
// params.D). The returned PCS supports Commit, Open, and Verify.
func NewPCSWithParams(params Params) PCS {
	return PCS{
		leafHasher: params.LeafHasher,
		nodeHasher: params.NodeHasher,
		rate:       uint64(params.N / params.D),
		params:     &params,
	}
}

// Committed is the per-batch prover-side blob returned by Commit. Tree
// carries the Merkle root the caller binds to its transcript; Sources
// retains, per Group in decreasing-size order, the RS-encoded row
// evaluations Open will need to build the DEEP quotient and to open the
// committed polynomials at FRI query positions. Shapes is in Batch
// declaration order, so it lines up with the caller's BatchShifts and is
// the verifier-side shape metadata to pass to PCS.Verify.
type Committed struct {
	Tree    WMerkleTree
	Sources []LeafSource
	Shapes  BatchShapes
}

// GroupShifts assigns a list of rotation shifts to each polynomial of a
// Group. Base[i] is the shift list for the i-th base polynomial of the
// Group; Ext[i] is the shift list for the i-th extension polynomial.
//
// A shift s means the polynomial is opened at zeta * omega_N^s where
// omega_N is the generator of the polynomial's native size-N domain (the
// Group's size). Shift lists must be non-empty and contain no duplicate
// opening points modulo N; Open and Verify reject inputs violating either rule.
type GroupShifts struct {
	Base [][]int
	Ext  [][]int
}

// BatchShifts gives, for every Group in a Batch (in declaration order),
// the per-polynomial shift list. Shape must align with the corresponding
// Batch: same number of Groups, same Base/Ext widths per Group.
type BatchShifts = []GroupShifts

// GroupClaimedValues holds the claimed polynomial evaluations produced by
// Open for one Group of one Batch. The shape mirrors the matching
// GroupShifts exactly:
//   - Base[i][k] is the claimed value of the i-th base polynomial at
//     zeta * omega_N^shifts.Base[i][k];
//   - Ext[i][k] is the claimed value of the i-th extension polynomial at
//     zeta * omega_N^shifts.Ext[i][k].
type GroupClaimedValues struct {
	Base [][]ext.E6
	Ext  [][]ext.E6
}

// BatchClaimedValues is one GroupClaimedValues per Group of a Batch.
type BatchClaimedValues = []GroupClaimedValues

// OpeningProof bundles everything Verify needs to convince the verifier
// that every polynomial in every committed Batch evaluates to the listed
// ClaimedValues at zeta times the requested rotation shifts.
//
//   - ClaimedValues[b] is the GroupClaimedValues slice for batches[b], in
//     the same order Open / Verify received batches and shifts.
//   - FRIProof is the multi-degree FRI proof on the DEEP-quotient
//     codewords, one level per DEEP class (one per distinct native size by
//     default, see WithDeepClasses), in level order: decreasing size, equal
//     sizes in class order. FRIProof.LevelsRoot commits all of them.
//   - PointSamplings[q][b] is the WMerkleProof opening batches[b] at the
//     q-th FRI query position. Each WMerkleProof carries one top lo/hi
//     RawRowPair, one top Merkle path, and one compact injected row pair
//     per smaller Group in decreasing-size order.
type OpeningProof struct {
	ClaimedValues  []BatchClaimedValues
	FRIProof       Proof
	PointSamplings [][]WMerkleProof
}

// Commit commits to one Batch of polynomials and returns the per-batch
// prover-side blob. The current implementation is a thin wrapper over
// RSCommit; PCS keeps no state across Commit calls -- callers stash one
// Committed per Commit invocation and hand the whole slice to Open.
//
// The caller is responsible for binding committed.Tree.Root() to the
// shared Fiat-Shamir transcript at the appropriate round before invoking
// Open: Commit does not bind anything itself.
func (pcs *PCS) Commit(batch Batch, opts ...CommitOption) (Committed, error) {
	if len(batch) == 0 {
		return Committed{}, fmt.Errorf("PCS.Commit: empty batch")
	}
	shapes, err := batchShapesInDeclarationOrder(batch, pcs.rate)
	if err != nil {
		return Committed{}, err
	}
	// The transient RSCommit's primary Encoder is just a fast path for
	// whichever Group happens to share its size; encoderForSize handles
	// every other size on the fly. We seed it with the first Group's
	// size so the single-group hot path matches the legacy direct-
	// RSCommit call site exactly.
	primaryN, err := groupNativeSize(batch[0])
	if err != nil {
		return Committed{}, fmt.Errorf("PCS.Commit: batch[0]: %w", err)
	}
	rs := NewRSCommit(uint64(primaryN), pcs.rate, pcs.leafHasher, pcs.nodeHasher)
	tree, sources, err := rs.Commit(batch, opts...)
	if err != nil {
		return Committed{}, err
	}
	return Committed{Tree: tree, Sources: sources, Shapes: shapes}, nil
}

func batchShapesInDeclarationOrder(batch Batch, rate uint64) (BatchShapes, error) {
	if rate == 0 {
		return nil, fmt.Errorf("PCS.Commit: rate must be positive")
	}
	shapes := make(BatchShapes, len(batch))
	for g, group := range batch {
		N, err := groupNativeSize(group)
		if err != nil {
			return nil, fmt.Errorf("PCS.Commit: batch[%d]: %w", g, err)
		}
		shapes[g] = GroupShape{
			Rows:      int(rate) * N,
			BaseWidth: len(group.Base),
			ExtWidth:  len(group.Ext),
		}
	}
	return shapes, nil
}
