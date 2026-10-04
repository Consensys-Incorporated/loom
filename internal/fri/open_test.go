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
	"github.com/consensys/loom/field"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/poly"
)

// TestOpenShape pins down OpeningProof's structural contract on a small
// fixture matching deep_test.go: two batches at sizes {8, 4}, three
// polynomials total, two distinct shifts at size 8.
//
// What we check:
//   - ClaimedValues mirrors `shifts` shape exactly.
//   - number of DEEP levels == number of distinct native sizes.
//   - FRIProof is structurally populated (non-nil FinalPoly, query count
//     matches Params.NumQueries).
//   - PointSamplings has shape [NumQueries][len(batches)] and each
//     WMerkleProof carries one compact top-row opening plus any injected rows.
func TestOpenShape(t *testing.T) {
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

	committed, openProof, _, _ := runOpenFixture(t, batches, shifts, rate, numQueries)

	// 1- ClaimedValues shape mirrors shifts.
	if got, want := len(openProof.ClaimedValues), len(shifts); got != want {
		t.Fatalf("ClaimedValues outer length = %d, want %d", got, want)
	}
	for b := range shifts {
		if got, want := len(openProof.ClaimedValues[b]), len(shifts[b]); got != want {
			t.Fatalf("ClaimedValues[%d] groups = %d, want %d", b, got, want)
		}
		for g := range shifts[b] {
			gv, gs := openProof.ClaimedValues[b][g], shifts[b][g]
			if got, want := len(gv.Base), len(gs.Base); got != want {
				t.Fatalf("ClaimedValues[%d][%d].Base width = %d, want %d", b, g, got, want)
			}
			if got, want := len(gv.Ext), len(gs.Ext); got != want {
				t.Fatalf("ClaimedValues[%d][%d].Ext width = %d, want %d", b, g, got, want)
			}
			for i := range gs.Base {
				if got, want := len(gv.Base[i]), len(gs.Base[i]); got != want {
					t.Fatalf("ClaimedValues[%d][%d].Base[%d] shifts = %d, want %d", b, g, i, got, want)
				}
			}
			for i := range gs.Ext {
				if got, want := len(gv.Ext[i]), len(gs.Ext[i]); got != want {
					t.Fatalf("ClaimedValues[%d][%d].Ext[%d] shifts = %d, want %d", b, g, i, got, want)
				}
			}
		}
	}

	// 2- One DEEP level per distinct native size {8, 4}.
	if got, want := len(openProof.FRIProof.LevelQueries)+1, 2; got != want {
		t.Fatalf("DEEP levels = %d, want %d", got, want)
	}

	// 3- FRIProof is populated. The DEEP-quotient rail is extension, so
	//    FinalField must be Ext and FinalPolyExt must be non-empty.
	if openProof.FRIProof.FinalField != field.Ext {
		t.Fatalf("FRIProof.FinalField = %s, want %s", openProof.FRIProof.FinalField, field.Ext)
	}
	if len(openProof.FRIProof.FinalPolyExt) == 0 {
		t.Fatal("FRIProof.FinalPolyExt is empty")
	}
	if got, want := len(openProof.FRIProof.FRIQueries), numQueries; got != want {
		t.Fatalf("FRIProof.FRIQueries = %d, want %d", got, want)
	}

	// 4- PointSamplings has [NumQueries][len(batches)] shape; each
	//    WMerkleProof carries one compact top-row opening plus any injected rows.
	if got, want := len(openProof.PointSamplings), numQueries; got != want {
		t.Fatalf("PointSamplings outer length = %d, want %d", got, want)
	}
	for q := range openProof.PointSamplings {
		if got, want := len(openProof.PointSamplings[q]), len(batches); got != want {
			t.Fatalf("PointSamplings[%d] length = %d, want %d", q, got, want)
		}
		for b := range openProof.PointSamplings[q] {
			wp := openProof.PointSamplings[q][b]
			if got := len(wp.Injections); got != len(committed[b].Sources)-1 {
				t.Fatalf("PointSamplings[%d][%d].Injections = %d, want %d",
					q, b, got, len(committed[b].Sources)-1)
			}
			// Top-group row widths must match the batch's top Group.
			top := wp.TopRows.Lo
			topGroup := batches[b][0] // single-group batch in this fixture
			if got, want := len(top.RawRowBase), len(topGroup.Base); got != want {
				t.Fatalf("PointSamplings[%d][%d].RawRowBase width = %d, want %d",
					q, b, got, want)
			}
			if got, want := len(top.RawRowExt), len(topGroup.Ext); got != want {
				t.Fatalf("PointSamplings[%d][%d].RawRowExt width = %d, want %d",
					q, b, got, want)
			}
		}
	}
}

func TestOpenCommittedAtCompactTwoSizeBranches(t *testing.T) {
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

	maxRows := committed.Tree.NumRows()
	smallRows := leafSourceRows(committed.Sources[1])
	topReduction := log2(maxRows) - log2(smallRows)

	for _, tc := range []struct {
		name  string
		sFull int
	}{
		{name: "small-pair-lo-row", sFull: 1},
		{name: "small-pair-hi-row", sFull: 2},
	} {
		t.Run(tc.name, func(t *testing.T) {
			wp, err := openCommittedAt(committed, tc.sFull, maxRows)
			if err != nil {
				t.Fatal(err)
			}
			if err := verifyOneWMerkleProof(DefaultLeafHasher, DefaultNodeHasher, committed.Tree.Root(), committed.Shapes, wp, tc.sFull, maxRows); err != nil {
				t.Fatalf("verifyOneWMerkleProof rejected compact opening: %v", err)
			}
			if got, want := len(wp.Injections), 1; got != want {
				t.Fatalf("len(Injections) = %d, want %d", got, want)
			}

			topLo, topHi := siblingRows(tc.sFull)
			topPairIdx := topLo / 2
			if got, want := wp.Path.LeafIdx, topPairIdx; got != want {
				t.Fatalf("Path.LeafIdx = %d, want %d", got, want)
			}
			if !wp.TopRows.Lo.RawRowBase[0].Equal(&committed.Sources[0].Base[0][topLo]) {
				t.Fatal("TopRows.Lo mismatch")
			}
			if !wp.TopRows.Hi.RawRowBase[0].Equal(&committed.Sources[0].Base[0][topHi]) {
				t.Fatal("TopRows.Hi mismatch")
			}

			smallRow := tc.sFull >> topReduction
			smallLo, smallHi := siblingRows(smallRow)
			inj := wp.Injections[0]
			if !inj.Rows.Lo.RawRowBase[0].Equal(&committed.Sources[1].Base[0][smallLo]) {
				t.Fatal("injected Rows.Lo mismatch")
			}
			if !inj.Rows.Hi.RawRowBase[0].Equal(&committed.Sources[1].Base[0][smallHi]) {
				t.Fatal("injected Rows.Hi mismatch")
			}

			topPairLeaves := committed.Tree.NumLeaves()
			smallPairLeaves := mustPairLeafCount(smallRows)
			pairReduction := log2(topPairLeaves) - log2(smallPairLeaves)
			pathPairAtWidth := topPairIdx >> pairReduction
			if got, want := pathPairAtWidth, smallLo/2; got != want {
				t.Fatalf("path pair at injection width = %d, want %d", got, want)
			}
			if got, want := wp.Path.InjectionLeaves[0], hashRawRowPair(DefaultLeafHasher, inj.Rows); got != want {
				t.Fatalf("injection pair leaf mismatch")
			}
		})
	}
}

// TestOpenFRIVerifyRoundtrip exercises the strongest roundtrip available
// before PR6 lands Verify: rebuild the prover's transcript state up to
// the point where fri.Prove was invoked (bind tree roots, sample zeta,
// register + bind claimed values, sample alpha_DEEP), then call
// fri.Verify on the OpeningProof's FRI proof against the returned
// DeepQuotientRoots. The roundtrip succeeds iff Open's transcript
// bindings and FRI invocation match the public fri.Verify spec.
func TestOpenFRIVerifyRoundtrip(t *testing.T) {
	const rate uint64 = 2
	const numQueries = 4

	batches := []Batch{
		{{
			Base: []poly.Polynomial{
				{baseElement(2), baseElement(3), baseElement(5), baseElement(7),
					baseElement(11), baseElement(13), baseElement(17), baseElement(19)},
			},
		}},
		{{
			Base: []poly.Polynomial{
				{baseElement(21), baseElement(23), baseElement(29), baseElement(31)},
			},
		}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0, 1}}}},
		{{Base: [][]int{{0}}}},
	}

	committed, openProof, params, zeta := runOpenFixture(t, batches, shifts, rate, numQueries)

	// Rebuild a verifier-side transcript replaying the same bindings as
	// the prover did up to (but not including) fri.Prove. We only need
	// to mirror what Open does internally before delegating to FRI.
	verifierFS := freshTranscriptForTest()

	// Same external setup the prover did via runOpenFixture: register
	// "test_zeta", bind every committed[b].Tree.Root() to it, then
	// sample zeta.
	if err := verifierFS.NewChallenge(testZetaName); err != nil {
		t.Fatal(err)
	}
	for _, c := range committed {
		root := c.Tree.Root()
		if err := verifierFS.Bind(testZetaName, root[:]); err != nil {
			t.Fatal(err)
		}
	}
	if _, err := verifierFS.ComputeChallenge(testZetaName); err != nil {
		t.Fatal(err)
	}

	// Replay Open's internal bindings: alpha_DEEP registration, claimed
	// values bound in per-polynomial order, sample alpha_DEEP.
	if err := verifierFS.NewChallenge(DeepAlphaName); err != nil {
		t.Fatal(err)
	}
	sizes, err := groupNativeSizesFromBatches(batches)
	if err != nil {
		t.Fatal(err)
	}
	if err := bindClaimedValuesByPolynomialOrder(verifierFS, openProof.ClaimedValues, shifts, mustDeepPlan(t, sizes)); err != nil {
		t.Fatal(err)
	}
	if _, err := verifierFS.ComputeChallenge(DeepAlphaName); err != nil {
		t.Fatal(err)
	}

	// sizesDesc is just the set of distinct group sizes in descending
	// order -- the same enumeration Open used to build FRI levels.
	sizesDesc := sizesDescFromSizes(sizes)
	if got := len(openProof.FRIProof.LevelQueries) + 1; got != len(sizesDesc) {
		t.Fatalf("DEEP levels = %d, sizesDesc = %d", got, len(sizesDesc))
	}

	if err := Verify(params, sizesDesc, openProof.FRIProof, verifierFS); err != nil {
		t.Fatalf("fri.Verify: %v", err)
	}

	_ = zeta // silence unused
}

// TestOpenRejectsCommitOnlyPCS confirms Open errors out when the PCS was
// built via NewPCS (no Params) -- only NewPCSWithParams supports Open.
func TestOpenRejectsCommitOnlyPCS(t *testing.T) {
	batches := []Batch{
		{{Base: []poly.Polynomial{
			{baseElement(1), baseElement(2), baseElement(3), baseElement(4)},
		}}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0}}}},
	}

	pcs := NewPCS(2, DefaultLeafHasher, DefaultNodeHasher)
	committed, err := pcs.Commit(batches[0])
	if err != nil {
		t.Fatal(err)
	}
	fs := freshTranscriptForTest()
	_, err = pcs.Open(batches, []Committed{committed}, shifts, ext.E6{}, fs)
	if err == nil {
		t.Fatal("expected Open to reject a PCS without Params")
	}
}

// TestOpenRejectsShapeMismatch confirms Open propagates shape-helper
// mismatches before computing claimed values.
func TestOpenRejectsShapeMismatch(t *testing.T) {
	batches := []Batch{
		{{Base: []poly.Polynomial{{baseElement(1), baseElement(2), baseElement(3), baseElement(4)}}}},
	}
	shifts := []BatchShifts{
		{{Base: [][]int{{0}}}},
		{}, // extra
	}

	params, err := NewParams(8, 4, 4, DefaultLeafHasher, DefaultNodeHasher)
	if err != nil {
		t.Fatal(err)
	}
	pcs := NewPCSWithParams(params)
	committed, err := pcs.Commit(batches[0])
	if err != nil {
		t.Fatal(err)
	}
	fs := freshTranscriptForTest()
	if _, err := pcs.Open(batches, []Committed{committed}, shifts, ext.E6{}, fs); err == nil {
		t.Fatal("expected Open to reject shape-mismatched inputs")
	}
}

// runOpenFixture is the shared test setup: builds Params, instantiates a
// PCS, commits every batch, binds tree roots to a fresh transcript and
// samples zeta, calls Open, returns everything the caller might want to
// inspect.
func runOpenFixture(
	t *testing.T,
	batches []Batch,
	shifts []BatchShifts,
	rate uint64,
	numQueries int,
	opts ...OpenOption,
) ([]Committed, OpeningProof, Params, ext.E6) {
	t.Helper()

	maxN := 0
	for _, b := range batches {
		for _, g := range b {
			N, err := groupNativeSize(g)
			if err != nil {
				t.Fatal(err)
			}
			if N > maxN {
				maxN = N
			}
		}
	}

	params, err := NewParams(int(rate)*maxN, maxN, numQueries, DefaultLeafHasher, DefaultNodeHasher)
	if err != nil {
		t.Fatal(err)
	}
	pcs := NewPCSWithParams(params)

	var domainCache poly.DomainCache
	committed := make([]Committed, len(batches))
	for b := range batches {
		c, err := pcs.Commit(batches[b], WithDomainCache(&domainCache))
		if err != nil {
			t.Fatalf("Commit(batches[%d]): %v", b, err)
		}
		committed[b] = c
	}

	// Minimal outer-protocol transcript activity: register "test_zeta",
	// bind every tree root, sample zeta.
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
	zetaOut, err := fs.ComputeChallenge(testZetaName)
	if err != nil {
		t.Fatal(err)
	}
	zeta := hash.OutputToExt(zetaOut)

	openProof, err := pcs.Open(batches, committed, shifts, zeta, fs, append([]OpenOption{WithOpenDomainCache(&domainCache)}, opts...)...)
	if err != nil {
		t.Fatalf("Open: %v", err)
	}
	return committed, openProof, params, zeta
}

// Test-only constants and helpers shared between Open tests.
const testZetaName = "test_zeta"

func freshTranscriptForTest() *fiatshamir.Transcript {
	hasher := hash.NewPoseidon2SpongeHasher()
	return fiatshamir.NewTranscript(&hasher)
}
