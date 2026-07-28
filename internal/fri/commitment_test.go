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
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/merkle"
	"github.com/consensys/loom/internal/poly"
)

func TestRSCommitDualRailProof(t *testing.T) {
	basePolys := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4)},
		{baseElement(5), baseElement(6), baseElement(7), baseElement(8)},
	}
	extPolys := []poly.ExtPolynomial{
		{
			extElement(1, 2, 3, 4),
			extElement(5, 6, 7, 8),
			extElement(9, 10, 11, 12),
			extElement(13, 14, 15, 16),
		},
	}

	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	committed, err := pcs.Commit([]Group{{Base: basePolys, Ext: extPolys}})
	if err != nil {
		t.Fatal(err)
	}
	tree := committed.Tree
	if got := tree.NumRows(); got != 8 {
		t.Fatalf("NumRows = %d, want 8", got)
	}
	if got := tree.NumLeaves(); got != 4 {
		t.Fatalf("NumLeaves = %d, want 4", got)
	}
	if got := tree.BaseWidth(); got != len(basePolys) {
		t.Fatalf("base rail width = %d, want %d", got, len(basePolys))
	}
	if got := tree.ExtWidth(); got != len(extPolys) {
		t.Fatalf("ext rail width = %d, want %d", got, len(extPolys))
	}

	const pairIdx = 1
	proof, err := tree.OpenProof(pairIdx)
	if err != nil {
		t.Fatal(err)
	}
	lo, hi := pairRowsForIndex(pairIdx)
	pair, err := rawRowPairFromSource(committed.Sources[0], lo, hi)
	if err != nil {
		t.Fatal(err)
	}
	leaf := hashRawRowPair(DefaultLeafHasher, pair)
	if !merkle.Verify(tree.Root(), proof, leaf, DefaultNodeHasher) {
		t.Fatal("dual-rail Merkle proof did not verify")
	}
}

func TestWMerkleTreeOpenProof(t *testing.T) {
	basePolys := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4)},
		{baseElement(5), baseElement(6), baseElement(7), baseElement(8)},
	}
	extPolys := []poly.ExtPolynomial{
		{
			extElement(1, 2, 3, 4),
			extElement(5, 6, 7, 8),
			extElement(9, 10, 11, 12),
			extElement(13, 14, 15, 16),
		},
	}

	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	committed, err := pcs.Commit([]Group{{Base: basePolys, Ext: extPolys}})
	if err != nil {
		t.Fatal(err)
	}
	tree := committed.Tree

	const pairIdx = 2
	proof, err := tree.OpenProof(pairIdx)
	if err != nil {
		t.Fatal(err)
	}

	lo, hi := pairRowsForIndex(pairIdx)
	pair, err := rawRowPairFromSource(committed.Sources[0], lo, hi)
	if err != nil {
		t.Fatal(err)
	}
	leaf := hashRawRowPair(DefaultLeafHasher, pair)
	if !merkle.Verify(tree.Root(), proof, leaf, DefaultNodeHasher) {
		t.Fatal("opened Merkle proof did not verify")
	}
}

func TestRSCommitWithDomainCache(t *testing.T) {
	basePolys := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4)},
		{baseElement(5), baseElement(6), baseElement(7), baseElement(8)},
	}

	var cache poly.DomainCache
	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	committed, err := pcs.Commit([]Group{{Base: basePolys}}, WithDomainCache(&cache))
	if err != nil {
		t.Fatal(err)
	}
	tree := committed.Tree
	if got := tree.NumRows(); got != 8 {
		t.Fatalf("NumRows = %d, want 8", got)
	}
	if got := tree.NumLeaves(); got != 4 {
		t.Fatalf("NumLeaves = %d, want 4", got)
	}
	if got := cache.Get(4); got != cache.Get(4) {
		t.Fatalf("DomainCache did not reuse input domain: %p vs %p", got, cache.Get(4))
	}
}

func TestRSCommitBatchLeafHasherMatchesScalarRoot(t *testing.T) {
	basePolys := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4)},
		{baseElement(5), baseElement(6), baseElement(7), baseElement(8)},
	}
	extPolys := []poly.ExtPolynomial{
		{
			extElement(1, 2, 3, 4),
			extElement(5, 6, 7, 8),
			extElement(9, 10, 11, 12),
			extElement(13, 14, 15, 16),
		},
	}

	tests := []struct {
		name string
		lh   LeafHasher
		nh   NodeHasher
	}{
		{
			name: "poseidon2",
			lh:   DefaultLeafHasher,
			nh:   DefaultNodeHasher,
		},
		{
			name: "sha256",
			lh:   SHA256LeafHasher{},
			nh:   SHA256NodeHasher{},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			batchPCS := NewPCS(2, tt.lh, tt.nh)
			batchCommitted, err := batchPCS.Commit([]Group{{Base: basePolys, Ext: extPolys}})
			if err != nil {
				t.Fatal(err)
			}

			scalarPCS := NewPCS(2, scalarOnlyLeafHasher{inner: tt.lh}, tt.nh)
			scalarCommitted, err := scalarPCS.Commit([]Group{{Base: basePolys, Ext: extPolys}})
			if err != nil {
				t.Fatal(err)
			}

			if batchCommitted.Tree.Root() != scalarCommitted.Tree.Root() {
				t.Fatalf("batched root differs from scalar root: got %v, want %v", batchCommitted.Tree.Root(), scalarCommitted.Tree.Root())
			}
		})
	}
}

func TestPairLeafHelpers(t *testing.T) {
	for _, tc := range []struct {
		rows int
		want int
	}{
		{rows: 2, want: 1},
		{rows: 4, want: 2},
		{rows: 16, want: 8},
	} {
		got, err := pairLeafCount(tc.rows)
		if err != nil {
			t.Fatalf("pairLeafCount(%d): %v", tc.rows, err)
		}
		if got != tc.want {
			t.Fatalf("pairLeafCount(%d) = %d, want %d", tc.rows, got, tc.want)
		}
	}

	for _, rows := range []int{-2, 0, 1, 3, 6} {
		if _, err := pairLeafCount(rows); err == nil {
			t.Fatalf("pairLeafCount(%d) should reject invalid row count", rows)
		}
	}

	for row := 0; row < 16; row++ {
		pairIdx := pairLeafIndexForRow(row)
		lo, hi := pairRowsForIndex(pairIdx)
		wantLo, wantHi := siblingRows(row)
		if lo != wantLo || hi != wantHi {
			t.Fatalf("row %d maps to pair rows (%d,%d), want (%d,%d)", row, lo, hi, wantLo, wantHi)
		}
	}
}

func TestHashRawRowPair(t *testing.T) {
	pair := RawRowPair{
		Lo: RawRow{
			RawRowBase: []koalabear.Element{baseElement(1), baseElement(2)},
			RawRowExt:  []ext.E6{extElement(10, 11, 12, 13)},
		},
		Hi: RawRow{
			RawRowBase: []koalabear.Element{baseElement(3), baseElement(4)},
			RawRowExt:  []ext.E6{extElement(20, 21, 22, 23)},
		},
	}

	for _, tc := range []struct {
		name string
		lh   LeafHasher
	}{
		{name: "poseidon2", lh: DefaultLeafHasher},
		{name: "sha256", lh: SHA256LeafHasher{}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got := hashRawRowPair(tc.lh, pair)
			want := tc.lh.HashLeafPair(pair.Lo, pair.Hi)
			if got != want {
				t.Fatalf("hashRawRowPair digest mismatch")
			}
		})
	}
}

func TestHashLeafPairsParallelScalarFallback(t *testing.T) {
	const pairs = hash.Poseidon2SpongeBatchSize + 3
	src := testLeafSource(2*pairs, 2, 1)

	gotPoseidon2 := make([]hash.Digest, pairs)
	HashLeafPairsParallel(DefaultLeafHasher, gotPoseidon2, src)
	for pairIdx := range gotPoseidon2 {
		lo, hi := pairRowsForIndex(pairIdx)
		pair, err := rawRowPairFromSource(src, lo, hi)
		if err != nil {
			t.Fatalf("pair %d: %v", pairIdx, err)
		}
		if want := hashRawRowPair(DefaultLeafHasher, pair); gotPoseidon2[pairIdx] != want {
			t.Fatalf("pair %d: Poseidon2 parallel digest differs from direct pair hash", pairIdx)
		}
	}

	got := make([]hash.Digest, pairs)
	HashLeafPairsParallel(SHA256LeafHasher{}, got, src)

	for pairIdx := range got {
		lo, hi := pairRowsForIndex(pairIdx)
		pair, err := rawRowPairFromSource(src, lo, hi)
		if err != nil {
			t.Fatalf("pair %d: %v", pairIdx, err)
		}
		if want := hashRawRowPair(SHA256LeafHasher{}, pair); got[pairIdx] != want {
			t.Fatalf("pair %d: scalar fallback digest differs from direct pair hash", pairIdx)
		}
	}
}

func TestPoseidon2BatchNodeHasherMatchesScalarHash(t *testing.T) {
	const n = hash.Poseidon2SpongeBatchSize
	left := make([]hash.Digest, n)
	right := make([]hash.Digest, n)
	for i := 0; i < n; i++ {
		for j := 0; j < len(left[i]); j++ {
			left[i][j].SetUint64(uint64(0xabcd0000 + i*16 + j))
			right[i][j].SetUint64(uint64(0xdcba0000 + i*16 + j))
		}
	}

	got := make([]hash.Digest, n)
	DefaultNodeHasher.HashNodes(got, left, right)

	for i := 0; i < n; i++ {
		want := DefaultNodeHasher.HashNode(left[i], right[i])
		if got[i] != want {
			t.Fatalf("pair %d: batched node digest differs from scalar digest:\n got  %v\n want %v", i, got[i], want)
		}
	}
}

func TestRSCommitEmptyRails(t *testing.T) {
	basePolys := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4)},
	}
	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	baseCommitted, err := pcs.Commit([]Group{{Base: basePolys}})
	if err != nil {
		t.Fatal(err)
	}
	baseTree := baseCommitted.Tree
	if got := baseTree.ExtWidth(); got != 0 {
		t.Fatalf("base-only tree ext rail width = %d, want 0", got)
	}

	extPolys := []poly.ExtPolynomial{
		{
			extElement(1, 2, 3, 4),
			extElement(5, 6, 7, 8),
			extElement(9, 10, 11, 12),
			extElement(13, 14, 15, 16),
		},
	}
	extCommitted, err := pcs.Commit([]Group{{Ext: extPolys}})
	if err != nil {
		t.Fatal(err)
	}
	extTree := extCommitted.Tree
	if got := extTree.BaseWidth(); got != 0 {
		t.Fatalf("ext-only tree base rail width = %d, want 0", got)
	}
	if got := extTree.NumRows(); got != 8 {
		t.Fatalf("ext-only NumRows = %d, want 8", got)
	}
	if got := extTree.NumLeaves(); got != 4 {
		t.Fatalf("ext-only NumLeaves = %d, want 4", got)
	}
}

// TestRSCommitMultiGroupOpenProof exercises the multi-size single-tree path:
// two groups of different native sizes are committed in one Commit call, and
// proofs for both the leaf-level group and the injection-level group are
// verified through the merkle injection schedule.
func TestRSCommitMultiGroupOpenProof(t *testing.T) {
	// Top group: size 8 (the actual Merkle leaves).
	topBase := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4),
			baseElement(5), baseElement(6), baseElement(7), baseElement(8)},
	}
	topExt := []poly.ExtPolynomial{
		{
			extElement(11, 12, 13, 14),
			extElement(21, 22, 23, 24),
			extElement(31, 32, 33, 34),
			extElement(41, 42, 43, 44),
			extElement(51, 52, 53, 54),
			extElement(61, 62, 63, 64),
			extElement(71, 72, 73, 74),
			extElement(81, 82, 83, 84),
		},
	}

	// Smaller group: size 4 (introduced as a level injection).
	smallBase := []poly.Polynomial{
		{baseElement(100), baseElement(200), baseElement(300), baseElement(400)},
	}

	// rate=2 ⇒ encoded row domains are 16 and 8.
	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	// Deliberately declare the smaller group first: PCS verifier metadata
	// must stay in declaration order, while the Merkle tree internally sorts
	// groups by decreasing row count for injections.
	committed, err := pcs.Commit([]Group{
		{Base: smallBase},
		{Base: topBase, Ext: topExt},
	})
	if err != nil {
		t.Fatal(err)
	}
	tree := committed.Tree
	sources := committed.Sources

	// Shape sanity.
	shapes := tree.Groups()
	if len(shapes) != 2 {
		t.Fatalf("Groups length = %d, want 2", len(shapes))
	}
	if shapes[0].Rows != 16 || shapes[0].BaseWidth != 1 || shapes[0].ExtWidth != 1 {
		t.Fatalf("top group shape = %+v", shapes[0])
	}
	if shapes[1].Rows != 8 || shapes[1].BaseWidth != 1 || shapes[1].ExtWidth != 0 {
		t.Fatalf("small group shape = %+v", shapes[1])
	}
	if got := tree.NumRows(); got != 16 {
		t.Fatalf("NumRows = %d, want 16", got)
	}
	if got := tree.NumLeaves(); got != 8 {
		t.Fatalf("NumLeaves = %d, want 8", got)
	}
	if widths := tree.InjectionWidths(); len(widths) != 1 || widths[0] != 4 {
		t.Fatalf("InjectionWidths = %v, want [4]", widths)
	}

	// Public PCS shapes stay in declaration order, unlike tree.Groups().
	if len(committed.Shapes) != 2 {
		t.Fatalf("Committed.Shapes length = %d, want 2", len(committed.Shapes))
	}
	if committed.Shapes[0].Rows != 8 || committed.Shapes[0].BaseWidth != 1 || committed.Shapes[0].ExtWidth != 0 {
		t.Fatalf("declared small group shape = %+v", committed.Shapes[0])
	}
	if committed.Shapes[1].Rows != 16 || committed.Shapes[1].BaseWidth != 1 || committed.Shapes[1].ExtWidth != 1 {
		t.Fatalf("declared top group shape = %+v", committed.Shapes[1])
	}

	// Commit's returned LeafSources must be in decreasing-size order — same
	// order as Groups() — and each source's width must match the
	// corresponding GroupShape.
	if len(sources) != 2 {
		t.Fatalf("len(sources) = %d, want 2", len(sources))
	}
	for k, src := range sources {
		if got, want := len(src.Base), shapes[k].BaseWidth; got != want {
			t.Fatalf("sources[%d].Base width = %d, want %d", k, got, want)
		}
		if got, want := len(src.Ext), shapes[k].ExtWidth; got != want {
			t.Fatalf("sources[%d].Ext width = %d, want %d", k, got, want)
		}
	}

	injectionWidths := tree.InjectionWidths()

	// Verify an opening for every pair-leaf index: at each idx, the path
	// crosses the size-4 injection level at pair position idx>>1, and both
	// the top pair hash and the injection pair leaf must reconstruct the
	// published root.
	for pairIdx := 0; pairIdx < tree.NumLeaves(); pairIdx++ {
		proof, err := tree.OpenProof(pairIdx)
		if err != nil {
			t.Fatalf("OpenProof(%d): %v", pairIdx, err)
		}
		if len(proof.InjectionLeaves) != 1 {
			t.Fatalf("pair %d: InjectionLeaves length = %d, want 1", pairIdx, len(proof.InjectionLeaves))
		}

		// Compute the top-group pair leaf hash that the verifier consumes.
		topLo, topHi := pairRowsForIndex(pairIdx)
		topPair, err := rawRowPairFromSource(sources[0], topLo, topHi)
		if err != nil {
			t.Fatalf("top pair %d: %v", pairIdx, err)
		}
		leaf := hashRawRowPair(DefaultLeafHasher, topPair)
		smallLo, smallHi := pairRowsForIndex(pairIdx >> 1)
		smallPair, err := rawRowPairFromSource(sources[1], smallLo, smallHi)
		if err != nil {
			t.Fatalf("small pair %d: %v", pairIdx>>1, err)
		}
		injectionLeaf := hashRawRowPair(DefaultLeafHasher, smallPair)
		if proof.InjectionLeaves[0] != injectionLeaf {
			t.Fatalf("pair %d: injection leaf digest mismatch at small pair %d", pairIdx, pairIdx>>1)
		}

		if !merkle.VerifyWithInjections(tree.Root(), proof, leaf, injectionWidths, DefaultNodeHasher) {
			t.Fatalf("pair %d: VerifyWithInjections rejected a valid proof", pairIdx)
		}

		// Cross-check: the legacy Verify (no injection support) must reject,
		// since the proof carries InjectionLeaves the bare path can't fold in.
		if merkle.Verify(tree.Root(), proof, leaf, DefaultNodeHasher) {
			t.Fatalf("pair %d: legacy Verify unexpectedly accepted an injection-bearing proof", pairIdx)
		}

		badLeaf := leaf
		badLeaf[0].SetUint64(0xdeadbeef)
		if merkle.VerifyWithInjections(tree.Root(), proof, badLeaf, injectionWidths, DefaultNodeHasher) {
			t.Fatalf("pair %d: VerifyWithInjections accepted a tampered top pair", pairIdx)
		}

		badProof := proof
		badProof.InjectionLeaves = append([]hash.Digest{}, proof.InjectionLeaves...)
		badProof.InjectionLeaves[0][0].SetUint64(0xdeadbeef)
		if merkle.VerifyWithInjections(tree.Root(), badProof, leaf, injectionWidths, DefaultNodeHasher) {
			t.Fatalf("pair %d: VerifyWithInjections accepted a tampered injected pair", pairIdx)
		}
	}
}

func TestRSCommitPairLeafEdgeTopTwoEncodedRows(t *testing.T) {
	polys := []poly.Polynomial{{baseElement(7)}}

	for _, tt := range []struct {
		name string
		lh   LeafHasher
		nh   NodeHasher
	}{
		{name: "poseidon2", lh: DefaultLeafHasher, nh: DefaultNodeHasher},
		{name: "sha256", lh: SHA256LeafHasher{}, nh: SHA256NodeHasher{}},
	} {
		t.Run(tt.name, func(t *testing.T) {
			pcs := NewPCS(2, tt.lh, tt.nh)
			committed, err := pcs.Commit([]Group{{Base: polys}})
			if err != nil {
				t.Fatal(err)
			}
			if got, want := committed.Tree.NumRows(), 2; got != want {
				t.Fatalf("NumRows = %d, want %d", got, want)
			}
			if got, want := committed.Tree.NumLeaves(), 1; got != want {
				t.Fatalf("NumLeaves = %d, want %d", got, want)
			}
			if widths := committed.Tree.InjectionWidths(); widths != nil {
				t.Fatalf("InjectionWidths = %v, want nil", widths)
			}

			proof, err := committed.Tree.OpenProof(0)
			if err != nil {
				t.Fatal(err)
			}
			if got := len(proof.Siblings); got != 0 {
				t.Fatalf("path siblings = %d, want 0", got)
			}
			pair, err := rawRowPairFromSource(committed.Sources[0], 0, 1)
			if err != nil {
				t.Fatal(err)
			}
			if !merkle.Verify(committed.Tree.Root(), proof, hashRawRowPair(tt.lh, pair), tt.nh) {
				t.Fatal("single pair-leaf proof did not verify")
			}

			wp, err := openCommittedAt(committed, 1, committed.Tree.NumRows())
			if err != nil {
				t.Fatal(err)
			}
			if err := verifyOneWMerkleProof(tt.lh, tt.nh, committed.Tree.Root(), committed.Shapes, wp, 1, committed.Tree.NumRows()); err != nil {
				t.Fatalf("verifyOneWMerkleProof rejected 2-row top tree: %v", err)
			}
		})
	}
}

func TestRSCommitPairLeafEdgeMixedRowsSixteenEightTwo(t *testing.T) {
	topBase := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4),
			baseElement(5), baseElement(6), baseElement(7), baseElement(8)},
	}
	midBase := []poly.Polynomial{
		{baseElement(101), baseElement(102), baseElement(103), baseElement(104)},
	}
	tinyBase := []poly.Polynomial{
		{baseElement(201)},
	}

	for _, tt := range []struct {
		name string
		lh   LeafHasher
		nh   NodeHasher
	}{
		{name: "poseidon2", lh: DefaultLeafHasher, nh: DefaultNodeHasher},
		{name: "sha256", lh: SHA256LeafHasher{}, nh: SHA256NodeHasher{}},
	} {
		t.Run(tt.name, func(t *testing.T) {
			pcs := NewPCS(2, tt.lh, tt.nh)
			committed, err := pcs.Commit([]Group{
				{Base: tinyBase},
				{Base: topBase},
				{Base: midBase},
			})
			if err != nil {
				t.Fatal(err)
			}
			tree := committed.Tree
			if got, want := tree.NumRows(), 16; got != want {
				t.Fatalf("NumRows = %d, want %d", got, want)
			}
			if got, want := tree.NumLeaves(), 8; got != want {
				t.Fatalf("NumLeaves = %d, want %d", got, want)
			}
			if got, want := tree.InjectionWidths(), []int{4, 1}; len(got) != len(want) || got[0] != want[0] || got[1] != want[1] {
				t.Fatalf("InjectionWidths = %v, want %v", got, want)
			}
			if got, want := len(committed.Sources), 3; got != want {
				t.Fatalf("sources = %d, want %d", got, want)
			}
			for i, wantRows := range []int{16, 8, 2} {
				if got := leafSourceRows(committed.Sources[i]); got != wantRows {
					t.Fatalf("source %d rows = %d, want %d", i, got, wantRows)
				}
			}

			for _, sFull := range []int{0, 5, 15} {
				wp, err := openCommittedAt(committed, sFull, tree.NumRows())
				if err != nil {
					t.Fatalf("openCommittedAt(%d): %v", sFull, err)
				}
				if got, want := len(wp.Injections), 2; got != want {
					t.Fatalf("s=%d Injections = %d, want %d", sFull, got, want)
				}
				if err := verifyOneWMerkleProof(tt.lh, tt.nh, tree.Root(), committed.Shapes, wp, sFull, tree.NumRows()); err != nil {
					t.Fatalf("verifyOneWMerkleProof(%d): %v", sFull, err)
				}
				if got, want := wp.Path.InjectionLeaves[1], hashRawRowPair(tt.lh, wp.Injections[1].Rows); got != want {
					t.Fatalf("s=%d width-1 injection digest mismatch", sFull)
				}
			}
		})
	}
}

func TestWMerkleProofCompactShapeSingleSize(t *testing.T) {
	basePolys := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4)},
	}

	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	committed, err := pcs.Commit([]Group{{Base: basePolys}})
	if err != nil {
		t.Fatal(err)
	}

	const sFull = 5
	topRows := committed.Tree.NumRows()
	topRow := sFull
	lo, hi := siblingRows(topRow)
	topRowPair, err := rawRowPairFromSource(committed.Sources[0], lo, hi)
	if err != nil {
		t.Fatal(err)
	}
	pairIdx := lo / 2
	path, err := committed.Tree.OpenProof(pairIdx)
	if err != nil {
		t.Fatal(err)
	}

	proof := WMerkleProof{
		TopRows: topRowPair,
		Path:    path,
	}

	if got, want := proof.Path.LeafIdx, pairIdx; got != want {
		t.Fatalf("Path.LeafIdx = %d, want %d", got, want)
	}
	if got := len(proof.Injections); got != 0 {
		t.Fatalf("len(Injections) = %d, want 0", got)
	}
	if !proof.TopRows.Lo.RawRowBase[0].Equal(&committed.Sources[0].Base[0][lo]) {
		t.Fatal("TopRows.Lo mismatch")
	}
	if !proof.TopRows.Hi.RawRowBase[0].Equal(&committed.Sources[0].Base[0][hi]) {
		t.Fatal("TopRows.Hi mismatch")
	}
	if !merkle.Verify(committed.Tree.Root(), proof.Path, hashRawRowPair(DefaultLeafHasher, proof.TopRows), DefaultNodeHasher) {
		t.Fatal("pair-leaf Merkle proof did not verify")
	}
	if topRows != 8 {
		t.Fatalf("top rows = %d, want 8", topRows)
	}
}

func TestWMerkleProofCompactShapeTwoSizeInjection(t *testing.T) {
	topBase := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4),
			baseElement(5), baseElement(6), baseElement(7), baseElement(8)},
	}
	smallBase := []poly.Polynomial{
		{baseElement(100), baseElement(200), baseElement(300), baseElement(400)},
	}

	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	committed, err := pcs.Commit([]Group{
		{Base: smallBase},
		{Base: topBase},
	})
	if err != nil {
		t.Fatal(err)
	}

	const sFull = 11
	topRows := committed.Tree.NumRows()
	topRow := sFull
	topLo, topHi := siblingRows(topRow)
	topRowPair, err := rawRowPairFromSource(committed.Sources[0], topLo, topHi)
	if err != nil {
		t.Fatal(err)
	}
	topPairIdx := topLo / 2
	path, err := committed.Tree.OpenProof(topPairIdx)
	if err != nil {
		t.Fatal(err)
	}

	smallRows := leafSourceRows(committed.Sources[1])
	smallRow := sFull >> (log2(topRows) - log2(smallRows))
	smallLo, smallHi := siblingRows(smallRow)
	smallRowPair, err := rawRowPairFromSource(committed.Sources[1], smallLo, smallHi)
	if err != nil {
		t.Fatal(err)
	}

	proof := WMerkleProof{
		TopRows: topRowPair,
		Path:    path,
		Injections: []WMerkleInjectionOpening{{
			Rows: smallRowPair,
		}},
	}

	if got, want := proof.Path.LeafIdx, topPairIdx; got != want {
		t.Fatalf("Path.LeafIdx = %d, want %d", got, want)
	}
	if got, want := len(proof.Injections), 1; got != want {
		t.Fatalf("len(Injections) = %d, want %d", got, want)
	}
	if !proof.Injections[0].Rows.Lo.RawRowBase[0].Equal(&committed.Sources[1].Base[0][smallLo]) {
		t.Fatal("injected Rows.Lo mismatch")
	}
	if !proof.Injections[0].Rows.Hi.RawRowBase[0].Equal(&committed.Sources[1].Base[0][smallHi]) {
		t.Fatal("injected Rows.Hi mismatch")
	}

	topPairLeaves := committed.Tree.NumLeaves()
	smallPairLeaves := mustPairLeafCount(smallRows)
	topReduction := log2(topPairLeaves) - log2(smallPairLeaves)
	pathPairAtWidth := topPairIdx >> topReduction
	if got, want := pathPairAtWidth, smallLo/2; got != want {
		t.Fatalf("path pair at injection width = %d, want %d", got, want)
	}
	if got, want := proof.Path.InjectionLeaves[0], hashRawRowPair(DefaultLeafHasher, proof.Injections[0].Rows); got != want {
		t.Fatalf("injection pair digest mismatch: got %v, want %v", got, want)
	}
}

func TestWMerkleProofCompactDigestAccounting(t *testing.T) {
	topRows := 16
	groupRows := []int{16, 8, 4}
	topPathDepth := log2(mustPairLeafCount(topRows))

	oldSiblingDigests := 2 * len(groupRows) * topPathDepth
	compactPathSiblings := topPathDepth
	compactInjectionDigests := len(groupRows) - 1
	compactTotalDigests := compactPathSiblings + compactInjectionDigests

	if got, want := oldSiblingDigests, 18; got != want {
		t.Fatalf("old sibling digests = %d, want %d", got, want)
	}
	if got, want := compactPathSiblings, 3; got != want {
		t.Fatalf("compact path siblings = %d, want %d", got, want)
	}
	if got, want := compactInjectionDigests, 2; got != want {
		t.Fatalf("compact injection digests = %d, want %d", got, want)
	}
	if got, want := compactTotalDigests, 5; got != want {
		t.Fatalf("compact total digests = %d, want %d", got, want)
	}
	if compactTotalDigests >= oldSiblingDigests {
		t.Fatalf("compact proof digest count did not shrink: compact=%d old=%d", compactTotalDigests, oldSiblingDigests)
	}
}

// TestRSCommitDuplicateGroupSize ensures that Commit rejects two groups of
// the same native size, since the merkle layer requires distinct LevelWidths
// for injections.
func TestRSCommitDuplicateGroupSize(t *testing.T) {
	polys := []poly.Polynomial{
		{baseElement(1), baseElement(2), baseElement(3), baseElement(4)},
	}
	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	if _, err := pcs.Commit([]Group{
		{Base: polys},
		{Base: polys},
	}); err == nil {
		t.Fatal("Commit should reject two groups with the same native size")
	}
}

type scalarOnlyLeafHasher struct {
	inner LeafHasher
}

func (h scalarOnlyLeafHasher) HashLeafPair(lo, hi RawRow) hash.Digest {
	return h.inner.HashLeafPair(lo, hi)
}

func testLeafSource(nLeaves, nbBase, nbExt int) LeafSource {
	src := LeafSource{
		Base: make([]poly.Polynomial, nbBase),
		Ext:  make([]poly.ExtPolynomial, nbExt),
	}
	for j := range src.Base {
		src.Base[j] = make(poly.Polynomial, nLeaves)
		for i := range src.Base[j] {
			src.Base[j][i] = baseElement(uint64(1000*(j+1) + i + 1))
		}
	}
	for j := range src.Ext {
		src.Ext[j] = make(poly.ExtPolynomial, nLeaves)
		for i := range src.Ext[j] {
			v := uint64(10000*(j+1) + 10*(i+1))
			src.Ext[j][i] = extElement(v+1, v+2, v+3, v+4)
		}
	}
	return src
}

func leafFromSource(src LeafSource, i int) ([]koalabear.Element, []ext.E6) {
	baseLeaf := make([]koalabear.Element, len(src.Base))
	for j := range src.Base {
		baseLeaf[j].Set(&src.Base[j][i])
	}

	extLeaf := make([]ext.E6, len(src.Ext))
	for j := range src.Ext {
		extLeaf[j].Set(&src.Ext[j][i])
	}

	return baseLeaf, extLeaf
}

func baseElement(v uint64) koalabear.Element {
	var e koalabear.Element
	e.SetUint64(v)
	return e
}

func extElement(a0, a1, b0, b1 uint64, b2 ...uint64) ext.E6 {
	var e ext.E6
	e.B0.A0.SetUint64(a0)
	e.B0.A1.SetUint64(a1)
	e.B1.A0.SetUint64(b0)
	e.B1.A1.SetUint64(b1)
	if len(b2) > 0 {
		e.B2.A0.SetUint64(b2[0])
	}
	if len(b2) > 1 {
		e.B2.A1.SetUint64(b2[1])
	}
	return e
}
