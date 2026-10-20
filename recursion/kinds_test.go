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

package recursion

import (
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
)

// Typed cells (recursion_bugs.txt, 1): every cell's lanes beyond its kind are
// zero, enforced by its writer. The cheats below are consistent on the bus:
// the cells' values are changed, then the run is traced again, so that only
// the kind constraints can reject them.

// kindsProgram: one input of each kind, each copied by a Select (which reads
// all 8 lanes, so that nothing but the witness chip types them). It returns
// the program, its inputs, and the inputs' and copies' cells.
func kindsProgram() (b *builder, ins, copies []int) {
	b = &builder{}
	one := b.inputKind(ScalarCell(koalabear.One()), KindScalar)
	c := cellAt(1)
	var e6 Cell
	copy(e6[:KindE6], c[:KindE6])
	ins = []int{
		b.inputKind(ScalarCell(c[0]), KindScalar),
		b.inputKind(e6, KindE6),
		b.inputKind(c, KindDigest),
	}
	for _, x := range ins {
		copies = append(copies, b.Select(one, x, x))
	}
	return b, ins, copies
}

// cellAt returns a cell of 8 distinct nonzero lanes.
func cellAt(seed uint64) Cell {
	var c Cell
	for i := range c {
		c[i].SetUint64(seed*100 + uint64(i) + 1)
	}
	return c
}

// TestWitnessKinds: typed inputs prove; an input with a nonzero lane beyond
// its kind does not execute, and a prover writing one anyway, consistently on
// the bus, is rejected.
func TestWitnessKinds(t *testing.T) {
	b, _, _ := kindsProgram()
	p, r := b.run(t)
	if err := prove(t, p, r); err != nil {
		t.Fatalf("typed inputs rejected: %v", err)
	}

	for name, tamper := range map[string]struct{ input, lane int }{
		"scalar, lane 1": {0, 1},
		"scalar, lane 5": {0, 5},
		"scalar, lane 7": {0, 7},
		"E6, lane 6":     {1, 6},
		"E6, lane 7":     {1, 7},
	} {
		t.Run(name, func(t *testing.T) {
			b, ins, copies := kindsProgram()
			p, r := b.run(t)
			bad := append([]Cell(nil), b.in...)
			bad[1+tamper.input][tamper.lane].SetUint64(5) // after the input one
			if _, err := p.Execute(bad); err == nil {
				t.Fatal("a mistyped input executed")
			}
			v := r.values[ins[tamper.input]]
			v[tamper.lane].SetUint64(5)
			r.values[ins[tamper.input]], r.values[copies[tamper.input]] = v, v
			if err := p.trace(r); err != nil {
				t.Fatal(err)
			}
			if err := prove(t, p, r); err == nil {
				t.Fatal("a mistyped input accepted")
			}
		})
	}
}

// TestLanesKinds: a Lanes output (written by its window row) with a nonzero
// lane beyond its kind is rejected by its row's strict form.
func TestLanesKinds(t *testing.T) {
	for name, tamper := range map[string]struct{ kind, lane int }{
		"E6, lane 6":     {KindE6, 6},
		"scalar, lane 3": {KindScalar, 3},
	} {
		t.Run(name, func(t *testing.T) {
			b := &builder{}
			d := b.inputKind(cellAt(2), KindDigest)
			out := b.Lanes(d, 1, tamper.kind)
			p, r := b.run(t)
			if err := prove(t, p, r); err != nil {
				t.Fatalf("honest Lanes rejected: %v", err)
			}
			r.values[out][tamper.lane].SetUint64(5)
			if err := p.trace(r); err != nil {
				t.Fatal(err)
			}
			if err := prove(t, p, r); err == nil {
				t.Fatal("a Lanes output beyond its kind accepted")
			}
		})
	}
}

// TestPackItemKind: an E6 cell packed as a scalar proves only if its lanes
// 1..5 are zero: its window reads it zero beyond the packed kind, since the
// stream (and its hash) holds lane 0 only.
func TestPackItemKind(t *testing.T) {
	var x Cell
	x[0].SetUint64(3)
	build := func(v Cell) *builder {
		b := &builder{}
		b.Pack([]int{b.inputKind(v, KindE6)}, []int{KindScalar})
		return b
	}
	if err := compileAndProve(t, build(x), nil); err != nil {
		t.Fatalf("an E6 value in the base field rejected: %v", err)
	}
	x[1].SetUint64(4)
	if err := compileAndProve(t, build(x), nil); err == nil {
		t.Fatal("lane 1 of an E6 cell packed as a scalar accepted")
	}
}

// TestScalarLanesBound is the attack on untyped scalars: a scalar s, bound to
// the transcript as a scalar (packed, so through lane 0 only), used in E6
// arithmetic, where its lanes 1..5 count. The program claims v·e = w for
// w ≠ v·e; the prover picks s' = (v, t1..t5), whose lane 0 is still v, and
// w = s'·e. Every hash, every E6 row and the bus are consistent. Two checks
// reject it, each on its own: the witness chip's typing of s (a scalar
// input), and the strict form of s's window, which reads it zero beyond the
// packed kind. With both disabled, the false claim verifies.
func TestScalarLanesBound(t *testing.T) {
	rnd := rand.New(rand.NewPCG(7, 8))
	v, e := koalabear.NewElement(11), randE6(rnd)
	var sp ext.E6 // s' = (v, t1..t5)
	sp.B0.A0 = v
	sp.B0.A1.SetUint64(1)
	sp.B2.A1.SetUint64(2)
	var w ext.E6
	w.Mul(&sp, &e)

	b := &builder{}
	s, ein := b.inputKind(ScalarCell(v), KindScalar), b.inputKind(E6Cell(e), KindE6)
	stream, _ := b.Pack([]int{s}, []int{KindScalar})
	b.AssertEq(stream[0], b.Const(ScalarCell(v))) // s is the transcript's v
	mul := b.Mul(s, ein)
	b.AssertEq(mul, b.Const(E6Cell(w)))
	p, r := b.run(t)
	if err := prove(t, p, r); err == nil {
		t.Fatal("v·e = w accepted, honestly")
	}

	// the cheat: s' instead of s, its product, the stream unchanged (lane 0)
	r.values[s] = E6Cell(sp)
	r.values[mul] = E6Cell(w)
	if err := p.trace(r); err != nil {
		t.Fatal(err)
	}
	if err := prove(t, p, r); err == nil {
		t.Fatal("v·e = w accepted, with s' = (v, t1..t5)")
	}
}
