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

package fri_test

import (
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
)

func freshTS() *fiatshamir.Transcript {
	hasher := hash.NewPoseidon2SpongeHasher()
	return fiatshamir.NewTranscript(&hasher)
}

func randomPoly(n int) []koalabear.Element {
	elems := make([]koalabear.Element, n)
	for i := range elems {
		elems[i].SetRandom()
	}
	return elems
}

func randomExtPoly(n int) []ext.E6 {
	elems := make([]ext.E6, n)
	for i := range elems {
		elems[i].MustSetRandom()
	}
	return elems
}

func testParams(t *testing.T, N, D, queries int) fri.Params {
	t.Helper()
	return testParamsWithOptions(t, N, D, queries)
}

func testParamsWithOptions(t *testing.T, N, D, queries int, opts ...fri.Option) fri.Params {
	t.Helper()
	p, err := fri.NewParams(N, D, queries, fri.DefaultLeafHasher, fri.DefaultNodeHasher, opts...)
	if err != nil {
		t.Fatalf("NewParams(%d,%d,%d): %v", N, D, queries, err)
	}
	return p
}

// TestProveVerify runs prove+verify for several (N, D, Q) parameter sets.
func TestProveVerify(t *testing.T) {
	cases := []struct{ N, D, Q int }{
		{16, 2, 1},
		{16, 4, 2},
		{64, 4, 4},
		{64, 8, 3},
		{256, 16, 5},
	}
	for _, tc := range cases {
		tc := tc
		t.Run(fmt.Sprintf("N%d_D%d_Q%d", tc.N, tc.D, tc.Q), func(t *testing.T) {
			p := testParams(t, tc.N, tc.D, tc.Q)

			poly := randomPoly(tc.D)
			evals, err := p.Encode(poly)
			if err != nil {
				t.Fatalf("Encode: %v", err)
			}

			tsP := freshTS()
			prf, _, err := fri.Prove(p, []fri.Level{{
				D:     p.D,
				Evals: fri.LevelEvals{Base: evals},
			}}, tsP)
			if err != nil {
				t.Fatalf("Prove: %v", err)
			}

			tsV := freshTS()
			if err := fri.Verify(p, []int{p.D}, prf, tsV); err != nil {
				t.Fatalf("Verify: %v", err)
			}
		})
	}
}

func TestProveVerifyExtRail(t *testing.T) {
	p := testParams(t, 64, 4, 4)

	poly := randomExtPoly(p.D)
	evals, err := p.EncodeExt(poly)
	if err != nil {
		t.Fatalf("EncodeExt: %v", err)
	}

	tsP := freshTS()
	prf, _, err := fri.Prove(p, []fri.Level{{
		D:     p.D,
		Evals: fri.LevelEvals{Ext: evals},
	}}, tsP)
	if err != nil {
		t.Fatalf("Prove: %v", err)
	}

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D}, prf, tsV); err != nil {
		t.Fatalf("Verify: %v", err)
	}
}

func TestProveVerifyExtRailWithExtraLevel(t *testing.T) {
	p := testParams(t, 64, 16, 4)
	pSmall := testParams(t, 16, 4, 4)

	poly0 := randomExtPoly(p.D)
	evals0, err := p.EncodeExt(poly0)
	if err != nil {
		t.Fatalf("EncodeExt level 0: %v", err)
	}
	poly1 := randomExtPoly(pSmall.D)
	evals1, err := pSmall.EncodeExt(poly1)
	if err != nil {
		t.Fatalf("EncodeExt extra level: %v", err)
	}

	tsP := freshTS()
	prf, _, err := fri.Prove(p, []fri.Level{
		{
			D:     p.D,
			Evals: fri.LevelEvals{Ext: evals0},
		},
		{
			D:     pSmall.D,
			Evals: fri.LevelEvals{Ext: evals1},
		},
	}, tsP)
	if err != nil {
		t.Fatalf("Prove: %v", err)
	}
	if len(prf.LevelQueries) != 1 {
		t.Fatalf("LevelQueries length = %d, want 1", len(prf.LevelQueries))
	}

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D, pSmall.D}, prf, tsV); err != nil {
		t.Fatalf("Verify: %v", err)
	}
}

func TestProveVerifyWithGrinding(t *testing.T) {
	const grindingBits = 6

	p := testParamsWithOptions(t, 64, 4, 3, fri.WithGrinding(grindingBits))
	evals, err := p.Encode(randomPoly(p.D))
	if err != nil {
		t.Fatalf("Encode: %v", err)
	}

	tsP := freshTS()
	prf, _, err := fri.Prove(p, []fri.Level{{
		D:     p.D,
		Evals: fri.LevelEvals{Base: evals},
	}}, tsP)
	if err != nil {
		t.Fatalf("Prove: %v", err)
	}
	if got, want := len(prf.PoW), log2ForTest(p.D); got != want {
		t.Fatalf("PoW entries = %d, want %d", got, want)
	}

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D}, prf, tsV); err != nil {
		t.Fatalf("Verify: %v", err)
	}

	missingPoW := prf
	missingPoW.PoW = nil
	tsMissing := freshTS()
	if err := fri.Verify(p, []int{p.D}, missingPoW, tsMissing); err == nil {
		t.Fatalf("Verify accepted a proof missing FRI proof of work")
	}

	badPoW := prf
	badPoW.PoW = copyPoW(prf.PoW)
	for name, pow := range badPoW.PoW {
		pow.NbBits = grindingBits + 1
		badPoW.PoW[name] = pow
		break
	}
	tsBad := freshTS()
	if err := fri.Verify(p, []int{p.D}, badPoW, tsBad); err == nil {
		t.Fatalf("Verify accepted a proof with mismatched FRI proof of work")
	}
}

func TestProveVerifyExtRailWithGrinding(t *testing.T) {
	const grindingBits = 6

	p := testParamsWithOptions(t, 64, 4, 3, fri.WithGrinding(grindingBits))
	evals, err := p.EncodeExt(randomExtPoly(p.D))
	if err != nil {
		t.Fatalf("EncodeExt: %v", err)
	}

	tsP := freshTS()
	prf, _, err := fri.Prove(p, []fri.Level{{
		D:     p.D,
		Evals: fri.LevelEvals{Ext: evals},
	}}, tsP)
	if err != nil {
		t.Fatalf("Prove: %v", err)
	}
	if got, want := len(prf.PoW), log2ForTest(p.D); got != want {
		t.Fatalf("PoW entries = %d, want %d", got, want)
	}

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D}, prf, tsV); err != nil {
		t.Fatalf("Verify: %v", err)
	}
}

// TestVerifyRejectsWrongRoot ensures Verify fails when root0 doesn't match the proof.
func TestVerifyRejectsWrongRoot(t *testing.T) {
	p := testParams(t, 64, 4, 4)
	evals, _ := p.Encode(randomPoly(p.D))

	tsP := freshTS()
	prf, _, _ := fri.Prove(p, []fri.Level{{
		D:     p.D,
		Evals: fri.LevelEvals{Base: evals},
	}}, tsP)

	for i := range prf.LevelsRoot {
		prf.LevelsRoot[i].SetRandom()
	}

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D}, prf, tsV); err == nil {
		t.Fatal("Verify accepted a proof with a wrong root0")
	}
}

// TestVerifyRejectsFlippedLeaf corrupts one leaf in a QueryLayer and expects rejection.
func TestVerifyRejectsFlippedLeaf(t *testing.T) {
	p := testParams(t, 64, 4, 4)
	evals, _ := p.Encode(randomPoly(p.D))

	tsP := freshTS()
	prf, _, err := fri.Prove(p, []fri.Level{{
		D:     p.D,
		Evals: fri.LevelEvals{Base: evals},
	}}, tsP)
	if err != nil {
		t.Fatalf("Prove: %v", err)
	}

	// Flip the first leaf of the first query, first layer.
	prf.FRIQueries[0].Layers[0].LeafPBase.SetRandom()

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D}, prf, tsV); err == nil {
		t.Fatal("Verify accepted a proof with a corrupted leaf")
	}
}

func TestVerifyRejectsFlippedLeafQ(t *testing.T) {
	p := testParams(t, 64, 4, 4)
	evals, _ := p.Encode(randomPoly(p.D))

	tsP := freshTS()
	prf, _, err := fri.Prove(p, []fri.Level{{
		D:     p.D,
		Evals: fri.LevelEvals{Base: evals},
	}}, tsP)
	if err != nil {
		t.Fatalf("Prove: %v", err)
	}

	prf.FRIQueries[0].Layers[0].LeafQBase.SetRandom()

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D}, prf, tsV); err == nil {
		t.Fatal("Verify accepted a proof with a corrupted second leaf")
	}
}

func TestVerifyRejectsFlippedExtLeaf(t *testing.T) {
	p := testParams(t, 64, 4, 4)
	evals, _ := p.EncodeExt(randomExtPoly(p.D))

	tsP := freshTS()
	prf, _, err := fri.Prove(p, []fri.Level{{
		D:     p.D,
		Evals: fri.LevelEvals{Ext: evals},
	}}, tsP)
	if err != nil {
		t.Fatalf("Prove: %v", err)
	}

	prf.FRIQueries[0].Layers[0].LeafPExt.MustSetRandom()

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D}, prf, tsV); err == nil {
		t.Fatal("Verify accepted a proof with a corrupted ext leaf")
	}
}

func TestVerifyRejectsFlippedExtLeafQ(t *testing.T) {
	p := testParams(t, 64, 4, 4)
	evals, _ := p.EncodeExt(randomExtPoly(p.D))

	tsP := freshTS()
	prf, _, err := fri.Prove(p, []fri.Level{{
		D:     p.D,
		Evals: fri.LevelEvals{Ext: evals},
	}}, tsP)
	if err != nil {
		t.Fatalf("Prove: %v", err)
	}

	prf.FRIQueries[0].Layers[0].LeafQExt.MustSetRandom()

	tsV := freshTS()
	if err := fri.Verify(p, []int{p.D}, prf, tsV); err == nil {
		t.Fatal("Verify accepted a proof with a corrupted second ext leaf")
	}
}

func copyPoW(src map[string]fiatshamir.ProofOfWork) map[string]fiatshamir.ProofOfWork {
	dst := make(map[string]fiatshamir.ProofOfWork, len(src))
	for name, pow := range src {
		dst[name] = pow
	}
	return dst
}

func log2ForTest(n int) int {
	k := 0
	for n > 1 {
		n >>= 1
		k++
	}
	return k
}

// sharedLevels builds levels of the given sizes D (decreasing), encoded at the
// rate of p, on the extension or the base rail.
func sharedLevels(t *testing.T, p fri.Params, ds []int, extRail bool) []fri.Level {
	t.Helper()
	rate := p.N / p.D
	var levels []fri.Level
	for _, d := range ds {
		pl := testParams(t, rate*d, d, p.NumQueries)
		lvl := fri.Level{D: d}
		if extRail {
			evals, err := pl.EncodeExt(randomExtPoly(d))
			if err != nil {
				t.Fatal(err)
			}
			lvl.Evals = fri.LevelEvals{Ext: evals}
		} else {
			evals, err := pl.Encode(randomPoly(d))
			if err != nil {
				t.Fatal(err)
			}
			lvl.Evals = fri.LevelEvals{Base: evals}
		}
		levels = append(levels, lvl)
	}
	return levels
}

// TestProveVerifySharedIntroRounds has three levels entering at round 0 and
// two entering at round 2, all committed in the levels tree.
func TestProveVerifySharedIntroRounds(t *testing.T) {
	ds := []int{16, 16, 16, 4, 4}
	for _, extRail := range []bool{true, false} {
		t.Run(fmt.Sprintf("ext=%v", extRail), func(t *testing.T) {
			p := testParams(t, 64, 16, 4)
			prf, _, err := fri.Prove(p, sharedLevels(t, p, ds, extRail), freshTS())
			if err != nil {
				t.Fatalf("Prove: %v", err)
			}
			if err := fri.Verify(p, ds, prf, freshTS()); err != nil {
				t.Fatalf("Verify: %v", err)
			}
			for k, q := range prf.FRIQueries {
				if n := len(q.Layers[0].Path.InjectionLeaves); n != 0 {
					t.Fatalf("query %d: round-0 path carries %d injection leaves, want 0", k, n)
				}
				for l := range prf.LevelQueries {
					if n := len(prf.LevelQueries[l][k].Path.Siblings); n != 0 {
						t.Fatalf("query %d level %d: opening carries a path", k, l+1)
					}
				}
			}

			clone := func() fri.Proof {
				bad := prf
				bad.LevelQueries = make([][]fri.QueryLayer, len(prf.LevelQueries))
				for i := range prf.LevelQueries {
					bad.LevelQueries[i] = append([]fri.QueryLayer(nil), prf.LevelQueries[i]...)
				}
				bad.FRIQueries = append([]fri.Query(nil), prf.FRIQueries...)
				bad.FRIQueries[0].Layers = append([]fri.QueryLayer(nil), prf.FRIQueries[0].Layers...)
				return bad
			}
			// level 2 enters at round 0, level 4 is the second level of round 2
			for _, l := range []int{2, 4} {
				bad := clone()
				q := &bad.LevelQueries[l-1][0]
				q.LeafQExt.B0.A0.SetUint64(7)
				q.LeafQBase.SetUint64(7)
				if err := fri.Verify(p, ds, bad, freshTS()); err == nil {
					t.Fatalf("tampered level %d opening accepted", l)
				}
			}
			bad := clone()
			bad.FRIQueries[0].Layers[0].LeafPExt.B1.A1.SetUint64(7)
			bad.FRIQueries[0].Layers[0].LeafPBase.SetUint64(7)
			if err := fri.Verify(p, ds, bad, freshTS()); err == nil {
				t.Fatal("tampered level 0 opening accepted")
			}
			bad = clone()
			bad.LevelsRoot[3].SetUint64(7)
			if err := fri.Verify(p, ds, bad, freshTS()); err == nil {
				t.Fatal("tampered levels root accepted")
			}
			if err := fri.Verify(p, []int{16, 16, 4, 4, 4}, prf, freshTS()); err == nil {
				t.Fatal("other level sizes accepted")
			}
			if err := fri.Verify(p, []int{16, 4, 16, 4, 16}, prf, freshTS()); err == nil {
				t.Fatal("increasing level sizes accepted")
			}
		})
	}
}

// TestProveVerifyLeadingEmptyRounds runs FRI over a domain larger than its
// largest level: with p.D = 64 (6 rounds) and levels of D = 16, 16 and 4, the
// largest level enters at round r0 = 2. The rounds 0 and 1 have no layer, so
// the proof holds layers and roots for the rounds 2..5 only, while the query
// positions stay full-domain.
func TestProveVerifyLeadingEmptyRounds(t *testing.T) {
	ds := []int{16, 16, 4}
	const first = 2
	for _, extRail := range []bool{true, false} {
		for _, grinding := range []int{0, 4} {
			t.Run(fmt.Sprintf("ext=%v/grinding=%d", extRail, grinding), func(t *testing.T) {
				p := testParamsWithOptions(t, 256, 64, 4, fri.WithGrinding(grinding))
				prf, positions, err := fri.Prove(p, sharedLevels(t, p, ds, extRail), freshTS())
				if err != nil {
					t.Fatalf("Prove: %v", err)
				}
				if err := fri.Verify(p, ds, prf, freshTS()); err != nil {
					t.Fatalf("Verify: %v", err)
				}

				// Shape: no root and no layer for the empty rounds.
				if got, want := len(prf.FRIRoots), 6-1-first; got != want {
					t.Fatalf("FRIRoots: %d, want %d (rounds %d+1..5)", got, want, first)
				}
				for k, q := range prf.FRIQueries {
					if got, want := len(q.Layers), 6-first; got != want {
						t.Fatalf("query %d: %d layers, want %d", k, got, want)
					}
					if positions[k] >= p.N {
						t.Fatalf("query %d: position %d outside the full domain %d", k, positions[k], p.N)
					}
					if q.Layers[0].Row != positions[k]>>first {
						t.Fatalf("query %d: first layer row %d, want the position %d >> %d", k, q.Layers[0].Row, positions[k], first)
					}
				}
				if grinding > 0 {
					if _, ok := prf.PoW[fri.FoldName(0)]; !ok {
						t.Fatal("an empty round's fold challenge carries no proof of work")
					}
				}

				clone := func() fri.Proof {
					bad := prf
					bad.FRIRoots = append([]hash.Digest(nil), prf.FRIRoots...)
					bad.FRIQueries = append([]fri.Query(nil), prf.FRIQueries...)
					bad.FRIQueries[0].Layers = append([]fri.QueryLayer(nil), prf.FRIQueries[0].Layers...)
					return bad
				}
				bad := clone()
				bad.LevelsRoot[3].SetUint64(7)
				if err := fri.Verify(p, ds, bad, freshTS()); err == nil {
					t.Fatal("tampered levels root accepted")
				}
				bad = clone()
				bad.FRIRoots[1][0].SetUint64(7)
				if err := fri.Verify(p, ds, bad, freshTS()); err == nil {
					t.Fatal("tampered layer root accepted")
				}
				bad = clone()
				bad.FRIQueries[0].Layers[0].LeafPExt.B1.A1.SetUint64(7)
				bad.FRIQueries[0].Layers[0].LeafPBase.SetUint64(7)
				if err := fri.Verify(p, ds, bad, freshTS()); err == nil {
					t.Fatal("tampered level 0 opening accepted")
				}
				bad = clone()
				bad.FRIQueries[0].Layers[2].LeafQExt.B0.A1.SetUint64(7)
				bad.FRIQueries[0].Layers[2].LeafQBase.SetUint64(7)
				if err := fri.Verify(p, ds, bad, freshTS()); err == nil {
					t.Fatal("tampered layer opening accepted")
				}
				bad = clone()
				bad.FRIRoots = bad.FRIRoots[1:]
				if err := fri.Verify(p, ds, bad, freshTS()); err == nil {
					t.Fatal("proof with a missing layer root accepted")
				}
				// The same proof under other level sizes: another first round.
				if err := fri.Verify(p, []int{32, 32, 8}, prf, freshTS()); err == nil {
					t.Fatal("proof accepted under larger level sizes")
				}
				if err := fri.Verify(p, []int{8, 8, 2}, prf, freshTS()); err == nil {
					t.Fatal("proof accepted under smaller level sizes")
				}
			})
		}
	}
}

// TestProveRejectsLevelLargerThanDomain: the largest level must fit the
// domain of Params.
func TestProveRejectsLevelLargerThanDomain(t *testing.T) {
	p := testParams(t, 64, 16, 4)
	big := testParams(t, 128, 32, 4)
	if _, _, err := fri.Prove(p, sharedLevels(t, big, []int{32}, true), freshTS()); err == nil {
		t.Fatal("level larger than p.D accepted")
	}
}
