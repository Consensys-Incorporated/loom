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

	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/poly"
)

// TestPCSVerifyRoundtrip is the full Open + Verify roundtrip on a small
// fixture matching deep_test.go / open_test.go: two batches at sizes
// {8, 4}, three polynomials, two distinct shifts at size 8.
//
// Verify must accept the OpeningProof produced by Open when the
// verifier-side transcript was driven through the same external pre-Open
// activity (register zeta, bind roots, sample zeta).
func TestPCSVerifyRoundtrip(t *testing.T) {
	batches, shifts, committed, openProof, params, zeta := buildVerifyFixture(t)

	roots, shapes := rootsAndShapes(committed)
	verifierFS := buildVerifierTranscript(t, committed)

	pcs := NewPCSWithParams(params)
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, verifierFS); err != nil {
		t.Fatalf("PCS.Verify rejected a valid OpeningProof: %v", err)
	}
	_ = batches // exercised via openProof
}

func TestPCSVerifyRoundtripSingleSizeBaseExtMultiShift(t *testing.T) {
	const rate uint64 = 2
	const numQueries = 4

	batches := []Batch{
		{{
			Base: []poly.Polynomial{
				{baseElement(2), baseElement(3), baseElement(5), baseElement(7),
					baseElement(11), baseElement(13), baseElement(17), baseElement(19)},
				{baseElement(23), baseElement(29), baseElement(31), baseElement(37),
					baseElement(41), baseElement(43), baseElement(47), baseElement(53)},
			},
			Ext: []poly.ExtPolynomial{
				{
					extElement(101, 102, 103, 104),
					extElement(201, 202, 203, 204),
					extElement(301, 302, 303, 304),
					extElement(401, 402, 403, 404),
					extElement(501, 502, 503, 504),
					extElement(601, 602, 603, 604),
					extElement(701, 702, 703, 704),
					extElement(801, 802, 803, 804),
				},
			},
		}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0, 2}, {1}}, Ext: [][]int{{0, 3}}}},
	}

	committed, openProof, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries)
	roots, shapes := rootsAndShapes(committed)
	verifierFS := buildVerifierTranscript(t, committed)

	pcs := NewPCSWithParams(params)
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, verifierFS); err != nil {
		t.Fatalf("PCS.Verify rejected a valid single-size OpeningProof: %v", err)
	}
	if got, want := len(openProof.FRIProof.LevelQueries)+1, 1; got != want {
		t.Fatalf("DEEP levels = %d, want %d", got, want)
	}
	if got, want := len(openProof.FRIProof.LevelQueries), 0; got != want {
		t.Fatalf("FRIProof.LevelQueries = %d, want %d", got, want)
	}
}

func TestPCSVerifyRoundtripMultiSizeBatch(t *testing.T) {
	const rate uint64 = 2
	const numQueries = 4

	batches, shifts, committed, openProof, params, zeta := buildMultiSizeBatchVerifyFixture(t, rate, numQueries)
	roots, shapes := rootsAndShapes(committed)
	verifierFS := buildVerifierTranscript(t, committed)

	pcs := NewPCSWithParams(params)
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, verifierFS); err != nil {
		t.Fatalf("PCS.Verify rejected a valid multi-size OpeningProof: %v", err)
	}
	if got, want := len(openProof.FRIProof.LevelQueries)+1, 2; got != want {
		t.Fatalf("DEEP levels = %d, want %d", got, want)
	}
	if got, want := len(openProof.FRIProof.LevelQueries), 1; got != want {
		t.Fatalf("FRIProof.LevelQueries = %d, want %d", got, want)
	}
	if got, want := len(openProof.FRIProof.LevelQueries[0]), numQueries; got != want {
		t.Fatalf("FRIProof.LevelQueries[0] = %d, want %d", got, want)
	}

	for q, query := range openProof.FRIProof.FRIQueries {
		if len(query.Layers) == 0 {
			t.Fatalf("query %d has no FRI layers", q)
		}
		sFull := query.Layers[0].Row
		if got, want := openProof.FRIProof.LevelQueries[0][q].Row, sFull>>1; got != want {
			t.Fatalf("query %d extra FRI level row = %d, want %d", q, got, want)
		}
		wp := openProof.PointSamplings[q][0]
		if got, want := len(wp.Injections), 1; got != want {
			t.Fatalf("query %d Injections = %d, want %d", q, got, want)
		}

		topSourceRows := leafSourceRows(committed[0].Sources[0])
		rowTop := sFull >> (log2(params.N) - log2(topSourceRows))
		topLo, topHi := siblingRows(rowTop)
		topPairIdx := topLo / 2
		if got, want := wp.Path.LeafIdx, topPairIdx; got != want {
			t.Fatalf("query %d top Path.LeafIdx = %d, want %d", q, got, want)
		}
		if len(wp.Path.Siblings) == 0 {
			t.Fatalf("query %d top path has no siblings", q)
		}
		if !wp.TopRows.Lo.RawRowBase[0].Equal(&committed[0].Sources[0].Base[0][topLo]) {
			t.Fatalf("query %d top lo row mismatch", q)
		}
		if !wp.TopRows.Hi.RawRowBase[0].Equal(&committed[0].Sources[0].Base[0][topHi]) {
			t.Fatalf("query %d top hi row mismatch", q)
		}

		smallRows := leafSourceRows(committed[0].Sources[1])
		rowSmall := sFull >> (log2(params.N) - log2(smallRows))
		lo, hi := siblingRows(rowSmall)
		smallOpening := wp.Injections[0]
		if !smallOpening.Rows.Lo.RawRowBase[0].Equal(&committed[0].Sources[1].Base[0][lo]) {
			t.Fatalf("query %d small lo row mismatch", q)
		}
		if !smallOpening.Rows.Hi.RawRowBase[0].Equal(&committed[0].Sources[1].Base[0][hi]) {
			t.Fatalf("query %d small hi row mismatch", q)
		}

		topPairLeaves := committed[0].Tree.NumLeaves()
		smallPairLeaves := mustPairLeafCount(smallRows)
		topReduction := log2(topPairLeaves) - log2(smallPairLeaves)
		pathPairAtWidth := topPairIdx >> topReduction
		if got, want := pathPairAtWidth, lo/2; got != want {
			t.Fatalf("query %d small path pair at width = %d, want %d", q, got, want)
		}
		if len(wp.Path.InjectionLeaves) == 0 {
			t.Fatalf("query %d path has no injection leaves", q)
		}
		if got, want := wp.Path.InjectionLeaves[0], hashRawRowPair(DefaultLeafHasher, smallOpening.Rows); got != want {
			t.Fatalf("query %d small injection pair hash mismatch", q)
		}
	}

	t.Run("rejects tampered largest group row", func(t *testing.T) {
		committed, tampered, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries)
		roots, shapes := rootsAndShapes(committed)
		pcs := NewPCSWithParams(params)
		tampered.PointSamplings[0][0].TopRows.Lo.RawRowBase[0].SetUint64(0xdeadbeef)
		verifierFS := buildVerifierTranscript(t, committed)
		if err := pcs.Verify(roots, shapes, shifts, zeta, tampered, verifierFS); err == nil {
			t.Fatal("PCS.Verify accepted a multi-size proof with a tampered largest-group row")
		}
	})

	t.Run("rejects tampered injected group row", func(t *testing.T) {
		committed, tampered, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries)
		roots, shapes := rootsAndShapes(committed)
		pcs := NewPCSWithParams(params)
		tampered.PointSamplings[0][0].Injections[0].Rows.Hi.RawRowBase[0].SetUint64(0xdeadbeef)
		verifierFS := buildVerifierTranscript(t, committed)
		if err := pcs.Verify(roots, shapes, shifts, zeta, tampered, verifierFS); err == nil {
			t.Fatal("PCS.Verify accepted a multi-size proof with a tampered injected-group row")
		}
	})
}

func TestCheckFRIBridgeUsesCompactRows(t *testing.T) {
	const rate uint64 = 2
	const numQueries = 4

	_, shifts, committed, openProof, params, zeta := buildMultiSizeBatchVerifyFixture(t, rate, numQueries)
	_, shapes := rootsAndShapes(committed)
	pcs, sizes, alpha, queryPositions := bridgeInputsForTest(t, committed, openProof, params, shapes, shifts)

	if err := checkFRIBridgeByPolynomial(&pcs, &openProof, mustDeepPlan(t, sizes), shapes, shifts, alpha, zeta, queryPositions); err != nil {
		t.Fatalf("checkFRIBridge rejected valid compact rows: %v", err)
	}

	t.Run("largest group row", func(t *testing.T) {
		tampered := openProof
		tampered.PointSamplings = clonePointSamplings(openProof.PointSamplings)
		tampered.PointSamplings[0][0].TopRows.Lo.RawRowBase[0].SetUint64(0xdeadbeef)
		if err := checkFRIBridgeByPolynomial(&pcs, &tampered, mustDeepPlan(t, sizes), shapes, shifts, alpha, zeta, queryPositions); err == nil {
			t.Fatal("checkFRIBridge accepted a tampered largest-group compact row")
		}
	})

	t.Run("injected group row", func(t *testing.T) {
		tampered := openProof
		tampered.PointSamplings = clonePointSamplings(openProof.PointSamplings)
		tampered.PointSamplings[0][0].Injections[0].Rows.Hi.RawRowBase[0].SetUint64(0xdeadbeef)
		if err := checkFRIBridgeByPolynomial(&pcs, &tampered, mustDeepPlan(t, sizes), shapes, shifts, alpha, zeta, queryPositions); err == nil {
			t.Fatal("checkFRIBridge accepted a tampered injected compact row")
		}
	})
}

func TestVerifyOneWMerkleProofRejectsCompactTampering(t *testing.T) {
	committed := buildCompactVerifyCommitted(t)
	maxRows := committed.Tree.NumRows()
	smallRows := leafSourceRows(committed.Sources[1])
	topReduction := log2(committed.Tree.NumLeaves()) - log2(mustPairLeafCount(smallRows))

	for _, tc := range []struct {
		name   string
		sFull  int
		tamper func(t *testing.T, wp *WMerkleProof)
	}{
		{
			name:  "top lo row",
			sFull: 1,
			tamper: func(_ *testing.T, wp *WMerkleProof) {
				wp.TopRows.Lo.RawRowBase[0].SetUint64(0xdeadbeef)
			},
		},
		{
			name:  "top hi row",
			sFull: 1,
			tamper: func(_ *testing.T, wp *WMerkleProof) {
				wp.TopRows.Hi.RawRowBase[0].SetUint64(0xdeadbeef)
			},
		},
		{
			name:  "injected lo row",
			sFull: 1,
			tamper: func(_ *testing.T, wp *WMerkleProof) {
				wp.Injections[0].Rows.Lo.RawRowBase[0].SetUint64(0xdeadbeef)
			},
		},
		{
			name:  "injected hi row",
			sFull: 2,
			tamper: func(_ *testing.T, wp *WMerkleProof) {
				wp.Injections[0].Rows.Hi.RawRowBase[0].SetUint64(0xdeadbeef)
			},
		},
		{
			name:  "normal sibling above injection",
			sFull: 1,
			tamper: func(t *testing.T, wp *WMerkleProof) {
				siblingIdx := topReduction + 1
				if siblingIdx >= len(wp.Path.Siblings) {
					t.Fatalf("test fixture has no normal sibling above injection: idx=%d siblings=%d", siblingIdx, len(wp.Path.Siblings))
				}
				wp.Path.Siblings[siblingIdx][0].SetUint64(0xdeadbeef)
			},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			wp, err := openCommittedAt(committed, tc.sFull, maxRows)
			if err != nil {
				t.Fatal(err)
			}
			if err := verifyOneWMerkleProof(DefaultLeafHasher, DefaultNodeHasher, committed.Tree.Root(), committed.Shapes, wp, tc.sFull, maxRows); err != nil {
				t.Fatalf("valid compact opening rejected before tampering: %v", err)
			}

			tc.tamper(t, &wp)
			if err := verifyOneWMerkleProof(DefaultLeafHasher, DefaultNodeHasher, committed.Tree.Root(), committed.Shapes, wp, tc.sFull, maxRows); err == nil {
				t.Fatal("verifyOneWMerkleProof accepted a tampered compact opening")
			}
		})
	}
}

func buildCompactVerifyCommitted(t *testing.T) Committed {
	t.Helper()
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
	return committed
}

func buildMultiSizeBatchVerifyFixture(
	t *testing.T,
	rate uint64,
	numQueries int,
) ([]Batch, []BatchShifts, []Committed, OpeningProof, Params, ext.E6) {
	t.Helper()

	batches := []Batch{{
		{
			Base: []poly.Polynomial{
				{baseElement(21), baseElement(23), baseElement(29), baseElement(31)},
			},
		},
		{
			Base: []poly.Polynomial{
				{baseElement(2), baseElement(3), baseElement(5), baseElement(7),
					baseElement(11), baseElement(13), baseElement(17), baseElement(19)},
			},
			Ext: []poly.ExtPolynomial{
				{
					extElement(101, 102, 103, 104),
					extElement(201, 202, 203, 204),
					extElement(301, 302, 303, 304),
					extElement(401, 402, 403, 404),
					extElement(501, 502, 503, 504),
					extElement(601, 602, 603, 604),
					extElement(701, 702, 703, 704),
					extElement(801, 802, 803, 804),
				},
			},
		},
	}}
	shifts := []BatchShifts{{
		{Base: [][]int{{0}}},
		{Base: [][]int{{0, 1}}, Ext: [][]int{{0}}},
	}}

	committed, openProof, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries)
	return batches, shifts, committed, openProof, params, zeta
}

func bridgeInputsForTest(
	t *testing.T,
	committed []Committed,
	openProof OpeningProof,
	params Params,
	shapes []BatchShapes,
	shifts []BatchShifts,
) (PCS, [][]int, ext.E6, []int) {
	t.Helper()

	pcs := NewPCSWithParams(params)
	sizes, err := groupNativeSizesFromShapes(shapes, pcs.rate)
	if err != nil {
		t.Fatal(err)
	}

	fs := buildVerifierTranscript(t, committed)
	if err := fs.NewChallenge(deepAlphaName); err != nil {
		t.Fatal(err)
	}
	if err := bindClaimedValuesByPolynomialOrder(fs, openProof.ClaimedValues, shifts, mustDeepPlan(t, sizes)); err != nil {
		t.Fatal(err)
	}
	alphaOut, err := fs.ComputeChallenge(deepAlphaName)
	if err != nil {
		t.Fatal(err)
	}
	alpha := hash.OutputToExt(alphaOut)

	queryPositions, err := extractFRIQueryPositions(openProof.FRIProof, params.NumQueries)
	if err != nil {
		t.Fatal(err)
	}

	return pcs, sizes, alpha, queryPositions
}

func clonePointSamplings(in [][]WMerkleProof) [][]WMerkleProof {
	out := make([][]WMerkleProof, len(in))
	for q := range in {
		out[q] = make([]WMerkleProof, len(in[q]))
		for b, wp := range in[q] {
			out[q][b] = wp
			out[q][b].TopRows = cloneRawRowPair(wp.TopRows)
			out[q][b].Path.Siblings = append(wp.Path.Siblings[:0:0], wp.Path.Siblings...)
			out[q][b].Path.InjectionLeaves = append(wp.Path.InjectionLeaves[:0:0], wp.Path.InjectionLeaves...)
			out[q][b].Injections = append(wp.Injections[:0:0], wp.Injections...)
			for i := range out[q][b].Injections {
				out[q][b].Injections[i].Rows = cloneRawRowPair(wp.Injections[i].Rows)
			}
		}
	}
	return out
}

func cloneRawRowPair(in RawRowPair) RawRowPair {
	return RawRowPair{
		Lo: cloneRawRow(in.Lo),
		Hi: cloneRawRow(in.Hi),
	}
}

func cloneRawRow(in RawRow) RawRow {
	return RawRow{
		RawRowBase: append(in.RawRowBase[:0:0], in.RawRowBase...),
		RawRowExt:  append(in.RawRowExt[:0:0], in.RawRowExt...),
	}
}

// TestPCSVerifyRejectsTamperedClaimedValue confirms Verify fails when
// any claimed value is flipped after Open. The break can manifest as
// either the FRI proof failing (because alpha_DEEP changes) or the
// bridge check failing -- both are correct rejections.
func TestPCSVerifyRejectsTamperedClaimedValue(t *testing.T) {
	_, shifts, committed, openProof, params, zeta := buildVerifyFixture(t)

	// Flip the first claimed value of batch 0's first base poly at the
	// first shift.
	openProof.ClaimedValues[0][0].Base[0][0].B0.A0.SetUint64(0xdeadbeef)

	roots, shapes := rootsAndShapes(committed)
	verifierFS := buildVerifierTranscript(t, committed)

	pcs := NewPCSWithParams(params)
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, verifierFS); err == nil {
		t.Fatal("PCS.Verify accepted a proof with a tampered claimed value")
	}
}

// TestPCSVerifyRejectsTamperedRoot confirms Verify fails when one of
// the batch commitments has its root replaced. The break manifests as
// the Merkle-path check for that batch failing.
func TestPCSVerifyRejectsTamperedRoot(t *testing.T) {
	_, shifts, committed, openProof, params, zeta := buildVerifyFixture(t)

	roots, shapes := rootsAndShapes(committed)
	// Corrupt the first byte of batch 0's root.
	roots[0][0].SetUint64(0xdeadbeef)

	verifierFS := buildVerifierTranscript(t, committed)

	pcs := NewPCSWithParams(params)
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, verifierFS); err == nil {
		t.Fatal("PCS.Verify accepted a proof against a tampered root")
	}
}

// TestPCSVerifyRejectsTamperedRawRow confirms Verify fails when one of
// the raw rows in PointSamplings is flipped. The break manifests as
// the Merkle-path authentication failing for that (query, batch).
func TestPCSVerifyRejectsTamperedRawRow(t *testing.T) {
	_, shifts, committed, openProof, params, zeta := buildVerifyFixture(t)

	// Flip the first base raw lo row of the first query, first batch.
	openProof.PointSamplings[0][0].TopRows.Lo.RawRowBase[0].SetUint64(0xdeadbeef)

	roots, shapes := rootsAndShapes(committed)
	verifierFS := buildVerifierTranscript(t, committed)

	pcs := NewPCSWithParams(params)
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, verifierFS); err == nil {
		t.Fatal("PCS.Verify accepted a proof with a tampered raw row")
	}
}

func TestPCSVerifyRejectsTamperedRawHiRow(t *testing.T) {
	_, shifts, committed, openProof, params, zeta := buildVerifyFixture(t)

	openProof.PointSamplings[0][0].TopRows.Hi.RawRowBase[0].SetUint64(0xdeadbeef)

	roots, shapes := rootsAndShapes(committed)
	verifierFS := buildVerifierTranscript(t, committed)

	pcs := NewPCSWithParams(params)
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, verifierFS); err == nil {
		t.Fatal("PCS.Verify accepted a proof with a tampered raw hi row")
	}
}

// TestPCSVerifyRejectsCommitOnlyPCS confirms Verify errors out when
// invoked on a PCS that was built without Params.
func TestPCSVerifyRejectsCommitOnlyPCS(t *testing.T) {
	_, shifts, committed, openProof, _, zeta := buildVerifyFixture(t)

	roots, shapes := rootsAndShapes(committed)
	fs := freshTranscriptForTest()

	commitOnly := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	if err := commitOnly.Verify(roots, shapes, shifts, zeta, openProof, fs); err == nil {
		t.Fatal("expected Verify to reject a PCS without Params")
	}
}

// TestPCSVerifyShapeMismatch exercises the top-level length-alignment
// rejections. Per-poly invariants (empty / duplicate shift lists) are
// covered by the shape-helper tests.
func TestPCSVerifyShapeMismatch(t *testing.T) {
	_, shifts, committed, openProof, params, zeta := buildVerifyFixture(t)
	roots, shapes := rootsAndShapes(committed)
	pcs := NewPCSWithParams(params)

	t.Run("roots length mismatch", func(t *testing.T) {
		fs := buildVerifierTranscript(t, committed)
		// One extra root.
		bad := append([]hash.Digest{}, roots...)
		bad = append(bad, hash.Digest{})
		if err := pcs.Verify(bad, shapes, shifts, zeta, openProof, fs); err == nil {
			t.Fatal("expected roots-length mismatch error")
		}
	})

	t.Run("shifts length mismatch", func(t *testing.T) {
		fs := buildVerifierTranscript(t, committed)
		bad := append([]BatchShifts{}, shifts...)
		bad = append(bad, BatchShifts{})
		if err := pcs.Verify(roots, shapes, bad, zeta, openProof, fs); err == nil {
			t.Fatal("expected shifts-length mismatch error")
		}
	})

	t.Run("ClaimedValues length mismatch", func(t *testing.T) {
		fs := buildVerifierTranscript(t, committed)
		tampered := openProof
		tampered.ClaimedValues = append([]BatchClaimedValues{}, openProof.ClaimedValues...)
		tampered.ClaimedValues = append(tampered.ClaimedValues, nil)
		if err := pcs.Verify(roots, shapes, shifts, zeta, tampered, fs); err == nil {
			t.Fatal("expected ClaimedValues-length mismatch error")
		}
	})

	t.Run("DEEP level count mismatch", func(t *testing.T) {
		fs := buildVerifierTranscript(t, committed)
		tampered := openProof
		tampered.FRIProof.LevelQueries = append(append([][]QueryLayer{}, openProof.FRIProof.LevelQueries...), openProof.FRIProof.LevelQueries...)
		tampered.FRIProof.LevelQueries = append(tampered.FRIProof.LevelQueries, nil)
		if err := pcs.Verify(roots, shapes, shifts, zeta, tampered, fs); err == nil {
			t.Fatal("expected DEEP level count mismatch error")
		}
	})
}

// buildVerifyFixture sets up the standard Open fixture and returns
// everything needed to drive Verify.
func buildVerifyFixture(t *testing.T) (
	[]Batch, []BatchShifts, []Committed, OpeningProof, Params, ext.E6,
) {
	t.Helper()
	const rate uint64 = 2
	const numQueries = 4

	batches := []Batch{
		{{
			Base: []poly.Polynomial{
				{baseElement(2), baseElement(3), baseElement(5), baseElement(7),
					baseElement(11), baseElement(13), baseElement(17), baseElement(19)},
			},
			Ext: []poly.ExtPolynomial{
				{
					extElement(101, 102, 103, 104),
					extElement(201, 202, 203, 204),
					extElement(301, 302, 303, 304),
					extElement(401, 402, 403, 404),
					extElement(501, 502, 503, 504),
					extElement(601, 602, 603, 604),
					extElement(701, 702, 703, 704),
					extElement(801, 802, 803, 804),
				},
			},
		}},
		{{
			Base: []poly.Polynomial{
				{baseElement(21), baseElement(23), baseElement(29), baseElement(31)},
			},
		}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0, 1}}, Ext: [][]int{{0}}}},
		{{Base: [][]int{{0}}}},
	}

	committed, openProof, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries)
	return batches, shifts, committed, openProof, params, zeta
}

// rootsAndShapes derives the verifier-side `roots` and `shapes` inputs
// from the per-batch Committed blobs the prover holds. In production
// callers, the outer protocol assembles these (setup roots from a
// verification key, witness roots from the proof).
func rootsAndShapes(committed []Committed) ([]hash.Digest, []BatchShapes) {
	roots := make([]hash.Digest, len(committed))
	shapes := make([]BatchShapes, len(committed))
	for b, c := range committed {
		roots[b] = c.Tree.Root()
		if len(c.Shapes) > 0 {
			shapes[b] = append(BatchShapes{}, c.Shapes...)
		} else {
			shapes[b] = append(BatchShapes{}, c.Tree.Groups()...)
		}
	}
	return roots, shapes
}

// buildVerifierTranscript re-runs the exact pre-Open transcript activity
// the prover did via runOpenFixture: register "test_zeta", bind every
// committed tree root, sample zeta. Leaves the transcript in the state
// PCS.Verify expects.
func buildVerifierTranscript(t *testing.T, committed []Committed) *fiatshamir.Transcript {
	t.Helper()
	fs := freshTranscriptForTest()
	if err := fs.NewChallenge(testZetaName); err != nil {
		t.Fatal(err)
	}
	for _, c := range committed {
		root := c.Tree.Root()
		if err := fs.Bind(testZetaName, root[:]); err != nil {
			t.Fatal(err)
		}
	}
	if _, err := fs.ComputeChallenge(testZetaName); err != nil {
		t.Fatal(err)
	}
	return fs
}

// TestPCSVerifyRoundtripEqualSizes opens a batch with two groups at each of
// two sizes: one large group is a leaf-level injection, and the two small
// groups are injected at the same level.
func TestPCSVerifyRoundtripEqualSizes(t *testing.T) {
	const rate uint64 = 2
	const numQueries = 4
	big := func(o uint64) poly.Polynomial {
		return poly.Polynomial{baseElement(o), baseElement(o + 3), baseElement(o + 5), baseElement(o + 7),
			baseElement(o + 11), baseElement(o + 13), baseElement(o + 17), baseElement(o + 19)}
	}
	small := func(o uint64) poly.Polynomial {
		return poly.Polynomial{baseElement(o), baseElement(o + 2), baseElement(o + 9), baseElement(o + 4)}
	}
	batches := []Batch{{
		{Base: []poly.Polynomial{big(1)}},
		{Base: []poly.Polynomial{small(20)}},
		{Base: []poly.Polynomial{big(40), big(50)}, Ext: []poly.ExtPolynomial{{
			extElement(101, 102, 103, 104), extElement(201, 202, 203, 204),
			extElement(301, 302, 303, 304), extElement(401, 402, 403, 404),
			extElement(501, 502, 503, 504), extElement(601, 602, 603, 604),
			extElement(701, 702, 703, 704), extElement(801, 802, 803, 804),
		}}},
		{Base: []poly.Polynomial{small(60)}},
	}}
	shifts := []BatchShifts{{
		{Base: [][]int{{0, 1}}},
		{Base: [][]int{{0}}},
		{Base: [][]int{{0}, {0, 1}}, Ext: [][]int{{0}}},
		{Base: [][]int{{0, 3}}},
	}}
	committed, openProof, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries)
	roots, shapes := rootsAndShapes(committed)
	pcs := NewPCSWithParams(params)
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, buildVerifierTranscript(t, committed)); err != nil {
		t.Fatalf("PCS.Verify rejected a valid equal-size OpeningProof: %v", err)
	}
	if got := len(openProof.PointSamplings[0][0].Injections); got != 3 {
		t.Fatalf("Injections = %d, want 3", got)
	}

	tampers := map[string]func(*OpeningProof){
		"leaf-level injection": func(p *OpeningProof) {
			p.PointSamplings[1][0].Injections[0].Rows.Lo.RawRowBase[1].SetUint64(0xdeadbeef)
		},
		"first equal-size injection": func(p *OpeningProof) {
			p.PointSamplings[2][0].Injections[1].Rows.Hi.RawRowBase[0].SetUint64(0xdeadbeef)
		},
		"second equal-size injection": func(p *OpeningProof) {
			p.PointSamplings[3][0].Injections[2].Rows.Lo.RawRowBase[0].SetUint64(0xdeadbeef)
		},
	}
	for name, tamper := range tampers {
		t.Run(name, func(t *testing.T) {
			committed, tampered, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries)
			roots, shapes := rootsAndShapes(committed)
			tamper(&tampered)
			pcs := NewPCSWithParams(params)
			if err := pcs.Verify(roots, shapes, shifts, zeta, tampered, buildVerifierTranscript(t, committed)); err == nil {
				t.Fatal("tampered proof accepted")
			}
		})
	}
}

func mustDeepPlan(t *testing.T, sizes [][]int) deepPlan {
	t.Helper()
	plan, err := newDeepPlan(sizes, nil)
	if err != nil {
		t.Fatal(err)
	}
	return plan
}

// TestPCSVerifyDeepClasses opens two batches whose groups fall in three DEEP
// classes: two classes of the same size (they share FRI round 0) and a
// smaller one. Class ids are sparse and the first class is not the largest.
func TestPCSVerifyDeepClasses(t *testing.T) {
	const rate uint64 = 2
	const numQueries = 4
	big := func(o uint64) poly.Polynomial {
		return poly.Polynomial{baseElement(o), baseElement(o + 3), baseElement(o + 5), baseElement(o + 7),
			baseElement(o + 11), baseElement(o + 13), baseElement(o + 17), baseElement(o + 19)}
	}
	small := func(o uint64) poly.Polynomial {
		return poly.Polynomial{baseElement(o), baseElement(o + 2), baseElement(o + 9), baseElement(o + 4)}
	}
	batches := []Batch{
		{{Base: []poly.Polynomial{small(1)}}, {Base: []poly.Polynomial{big(20)}}, {Base: []poly.Polynomial{big(40)}}},
		{{Base: []poly.Polynomial{big(60), big(70)}}, {Base: []poly.Polynomial{small(80)}}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0, 1}}}, {Base: [][]int{{0}}}, {Base: [][]int{{0, 2}}}},
		{{Base: [][]int{{0}, {1}}}, {Base: [][]int{{0}}}},
	}
	// classes: 2 = small groups, 5 = first big class, 9 = second big class
	classes := [][]int{{2, 5, 9}, {9, 2}}
	committed, openProof, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries, WithDeepClasses(classes))
	roots, shapes := rootsAndShapes(committed)
	pcs := NewPCSWithParams(params)
	if got := len(openProof.FRIProof.LevelQueries) + 1; got != 3 {
		t.Fatalf("DEEP levels = %d, want 3", got)
	}
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, buildVerifierTranscript(t, committed), WithDeepClasses(classes)); err != nil {
		t.Fatalf("PCS.Verify rejected valid DEEP classes: %v", err)
	}
	// The verifier must use the prover's classes.
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, buildVerifierTranscript(t, committed)); err == nil {
		t.Fatal("PCS.Verify accepted the proof with the default classes")
	}
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, buildVerifierTranscript(t, committed), WithDeepClasses([][]int{{2, 9, 5}, {9, 2}})); err == nil {
		t.Fatal("PCS.Verify accepted the proof with other classes")
	}
	// A class must have a single size.
	if err := pcs.Verify(roots, shapes, shifts, zeta, openProof, buildVerifierTranscript(t, committed), WithDeepClasses([][]int{{5, 5, 9}, {9, 2}})); err == nil {
		t.Fatal("PCS.Verify accepted a class mixing two sizes")
	}
	// A row of the second big class, which enters FRI at round 0 next to
	// level 0.
	tampered := openProof
	tampered.PointSamplings = clonePointSamplings(openProof.PointSamplings)
	tampered.PointSamplings[0][1].TopRows.Hi.RawRowBase[1].SetUint64(0xdeadbeef)
	if err := pcs.Verify(roots, shapes, shifts, zeta, tampered, buildVerifierTranscript(t, committed), WithDeepClasses(classes)); err == nil {
		t.Fatal("tampered row accepted")
	}
}
