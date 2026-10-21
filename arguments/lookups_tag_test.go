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

package arguments

import (
	"sync"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/trace"
)

// TestLookupsTagsSeparateTargets is the attack the tags prevent. Module m
// looks s1 up into tab1 = {1, 2, 3, 4} and s2 into tab2 = {5, 6, 7, 8}; the
// prover swaps the values, s1 = 5 and s2 = 1, and commits the multiplicities
// the swap balances (4 for tab1's 1, 4 for tab2's 5), with a cheating
// multiplicity step. On one untagged bus, the fractions of s2 cancel those of
// tab1 and the fractions of s1 those of tab2, and the proof is accepted; with
// the tags, it is rejected.
func TestLookupsTagsSeparateTargets(t *testing.T) {
	const n = 4
	build := func(t *testing.T, tagged bool) board.Program {
		t.Helper()
		b := board.NewBuilder()
		for _, name := range []string{"m", "tab1", "tab2"} {
			mod := board.NewModule(name)
			mod.N = n
			b.AddModule(mod)
		}
		col := func(module, c string) board.CTable {
			return board.CTable{Table: board.Table{Module: module, In: []expr.Expr{expr.Col(module + "." + c)}}}
		}
		l := NewLookups()
		if err := l.Add(col("m", "s1"), col("tab1", "t")); err != nil {
			t.Fatal(err)
		}
		if err := l.Add(col("m", "s2"), col("tab2", "t")); err != nil {
			t.Fatal(err)
		}
		if err := l.build(&b, tagged); err != nil {
			t.Fatal(err)
		}
		pg, err := board.Compile(&b)
		if err != nil {
			t.Fatal(err)
		}
		// m's two fractions, of different targets, share one logup column
		if len(pg.LogupBus) != 1 || len(pg.LogupBus[0].Totals) != 3 {
			t.Fatalf("got buses %v, want one bus with 3 totals (m, tab1, tab2)", pg.LogupBus)
		}
		return pg
	}
	cheat := func(pg board.Program) {
		for r := range pg.Rounds {
			for i, s := range pg.Rounds[r].Steps {
				if _, ok := s.Ctx.(board.LMCtx); !ok {
					continue
				}
				pg.Rounds[r].Steps[i].Step = func(_ []expr.Expr, outs []string, tr trace.Trace, _ *board.Program, _ *proof.Proof, _ *sync.Mutex, _ board.StepContext) error {
					m := make([]koalabear.Element, n)
					m[0].SetUint64(4) // tab1's 1 (s2), tab2's 5 (s1)
					return tr.PutBase(outs[0], m)
				}
			}
		}
	}
	values := func(v ...uint64) []koalabear.Element {
		res := make([]koalabear.Element, len(v))
		for i, x := range v {
			res[i].SetUint64(x)
		}
		return res
	}
	verify := func(t *testing.T, pg board.Program, s1, s2 uint64) error {
		t.Helper()
		tr := trace.New()
		tr.SetBase("tab1.t", values(1, 2, 3, 4))
		tr.SetBase("tab2.t", values(5, 6, 7, 8))
		tr.SetBase("m.s1", values(s1, s1, s1, s1))
		tr.SetBase("m.s2", values(s2, s2, s2, s2))
		pk, vk, err := loom.Setup(tr, pg)
		if err != nil {
			t.Fatal(err)
		}
		st := loom.Statement{Program: pg, VerificationKey: vk, PublicInputs: public.Inputs{}}
		prf, err := loom.Prove(st, loom.Witness{Trace: tr, ProvingKey: pk})
		if err != nil {
			return err
		}
		return loom.Verify(st, prf)
	}

	// honest: s1 = 1 in tab1, s2 = 5 in tab2
	if err := verify(t, build(t, true), 1, 5); err != nil {
		t.Fatalf("valid proof rejected: %v", err)
	}
	// the swap, without tags: accepted
	untagged := build(t, false)
	cheat(untagged)
	if err := verify(t, untagged, 5, 1); err != nil {
		t.Fatalf("the swap is rejected without the tags, the test does not exercise them: %v", err)
	}
	// the swap, with tags: rejected
	tagged := build(t, true)
	cheat(tagged)
	if err := verify(t, tagged, 5, 1); err == nil {
		t.Fatal("the swap is accepted with the tags")
	}
}
