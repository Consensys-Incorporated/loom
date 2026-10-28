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
	"fmt"
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/trace"
)

// Witness columns of the P2 core: the permutation's input and output lanes.
// The AIR's round columns sit next to them, see poseidon2AIR.
const (
	p2S = "s" // lanes
	p2R = "r" // lanes
)

func p2Ins() []string {
	res := make([]string, width)
	for i := range res {
		res[i] = p2Mod + "." + laneName(p2S, i)
	}
	return res
}

func p2Outs() []string {
	res := make([]string, width)
	for i := range res {
		res[i] = p2Mod + "." + laneName(p2R, i)
	}
	return res
}

// p2Table returns the core's lookup target (inputs, then the first nOut
// outputs).
func p2Table(nOut int) board.Table {
	t := board.NewTable(p2Mod, width+nOut)
	for i := range width {
		t.In[i] = col(p2Mod, laneName(p2S, i))
	}
	for i := range nOut {
		t.In[width+i] = col(p2Mod, laneName(p2R, i))
	}
	return t
}

// p2Chip: the P2 core, one Poseidon2 permutation per row, constrained by
// poseidon2AIR, carrying the control of the two chips that drive it on the
// same module. Its rows are, in order:
//
//	the sponges' blocks        sp_active = 1   (see chip_sponge.go)
//	the Merkle paths' steps    mk_active = 1   (see chip_merkle.go)
//	the dynamic paths' compressions, for which the core is a lookup target
//	padding, the genuine instance P(0)
//
// The sponge and the Merkle path used to be modules of their own, each
// committing the permutation's input and output a second time and tying the
// two copies with a lookup. Folding their control in deletes those copies,
// both lookups and both modules' own setup, quotient and logup columns. One
// core rather than two keeps poseidon2AIR's 189 columns instantiated once:
// two cores cost the same per row but are 189 columns wider, and width is
// what the next recursion level pays per query.
//
// Each chip asks for the permutation input it needs, and the ask is enforced
// only where that chip is active:
//
//	sp_active·(s_l − spongeInput(l)) = 0
//	mk_active·(s_l − merkleInput(l)) = 0
//
// so s is free on the rows of neither — which is where the dynamic paths'
// compressions are traced — and zero on padding rows.
//
// The core keeps poseidon2AIR's degree, p2Degree: every control constraint has
// degree at most 3, and the bus batches the core's accesses within it (see
// Bus.LimitDegree). The core is the largest module, and its quotient, hence
// the domain its 189-column AIR is evaluated on, follows its highest degree:
// degree 5 would double that domain, for no saving in committed cells.
type p2Chip struct{ m *Machine }

// p2Degree is the degree of poseidon2AIR's constraints (S-box degree 3), and of
// every constraint on the P2 core.
const p2Degree = 3

func (c p2Chip) name() string { return p2Mod }

// rows counts the sponges' blocks, the Merkle paths' steps and an upper bound
// on the dynamic paths' compressions (their rows before the first leaf do not
// hash).
func (c p2Chip) rows() int {
	n := c.m.spongeBlocks() + c.m.pathStepRows()
	for _, d := range c.m.dpaths {
		n += d.p.Siblings.Len() + d.p.Order.Len()
	}
	return n
}

func (c p2Chip) define(b *board.Builder, bus *Bus) error {
	if err := loomP2AIR().Define(b, p2Mod, p2Ins(), p2Outs()); err != nil {
		return err
	}
	mm := b.Modules[p2Mod]
	bus.LimitDegree(p2Mod, p2Degree)
	spActive, mkActive := setupCol(p2Mod, spongeActive), setupCol(p2Mod, merkleActive)
	for l := range width {
		s := col(p2Mod, laneName(p2S, l))
		mm.AssertZero(spActive.Mul(s.Sub(spongeInput(l))))
		mm.AssertZero(mkActive.Mul(s.Sub(merkleInput(l))))
	}

	bus.Read(p2Mod, setupCol(p2Mod, spongeAddrA), cellCols(p2Mod, spongeX, 0), spActive)
	bus.Read(p2Mod, setupCol(p2Mod, spongeAddrB), cellCols(p2Mod, spongeX, CellWidth), spActive)
	bus.Write(p2Mod, setupCol(p2Mod, spongeOutAddr), cellCols(p2Mod, p2R, 0), setupCol(p2Mod, spongeOutMult))
	merkleDefine(mm, bus)
	return nil
}

func (c p2Chip) setup(cs *cols) {
	c.spongeSetup(cs)
	c.merkleSetup(cs, c.m.spongeBlocks())
}

// trace fills the three kinds of row, then the AIR's round columns.
func (c p2Chip) trace(cs *cols, r *Run) error {
	cs.declareLanes(p2S, width)
	cs.declareLanes(p2R, width)
	perm := newPerm()
	row, err := c.spongeTrace(cs, r, perm)
	if err != nil {
		return err
	}
	if row, err = c.merkleTrace(cs, r, perm, row); err != nil {
		return err
	}
	for _, in := range r.p2 {
		if row >= cs.n {
			return fmt.Errorf("%d permutations, at most %d rows", row+1, cs.n)
		}
		if _, err := setPermRow(cs, perm, row, in); err != nil {
			return err
		}
		row++
	}
	return fillP2(cs)
}

// setPermRow writes the permutation of in on a row, and returns its output.
func setPermRow(cs *cols, perm *poseidon2.Permutation, row int, in [width]koalabear.Element) ([width]koalabear.Element, error) {
	out := in
	if err := perm.Permutation(out[:]); err != nil {
		return out, err
	}
	for l := range width {
		cs.setElem(laneName(p2S, l), row, in[l])
		cs.setElem(laneName(p2R, l), row, out[l])
	}
	return out, nil
}

// fillP2 fills the AIR's round columns from the traced inputs and outputs.
// The AIR fills its columns from a trace: run it on these columns and take
// its own back. Rows whose inputs and outputs are all zero are padding: the
// AIR makes them the genuine instance P(0).
func fillP2(cs *cols) error {
	tmp := trace.New()
	cs.store(tmp, p2Mod)
	if err := loomP2AIR().Fill(tmp, p2Mod, p2Ins(), p2Outs()); err != nil {
		return err
	}
	for name, v := range tmp.Base {
		cs.vals[strings.TrimPrefix(name, p2Mod+".")] = v
	}
	return nil
}

func newPerm() *poseidon2.Permutation { return hash.Poseidon2SpongePermutation() }
