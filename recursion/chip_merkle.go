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

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

// Setup columns of the merkle chip.
const (
	merkleFirst    = "first"
	merkleLast     = "last"
	merkleActive   = "active"
	merkleInj      = "inj"
	merkleLvl0     = "lvl0"
	merkleLeafAddr = "leaf_addr"
	merkleIdxAddr  = "idx_addr"
	merkleSibAddr  = "sib_addr"
	merkleRootAddr = "root_addr"
	merkleG        = "g"
	merkleXbAddr   = "xb_addr"
	merkleXbMult   = "xb_mult"
)

// Witness columns of the merkle chip.
const (
	merkleB   = "b"
	merkleIdx = "idx"
	merkleX   = "x"
	merkleB0  = "b0"
	merkleCur = "cur" // lanes
	merkleS   = "s"   // lanes
	merkleOut = "out" // lanes
)

type pathInst struct {
	leaf, index, root int
	siblings          []int // one per level, leaf level first
	steps             []pathStep
	gens              []koalabear.Element // x⁻¹ accumulator constants per level, nil if unused
	xb                int                 // address of [x⁻¹, b0], if gens != nil
}

// pathStep is one row of a path: a level (compress the running hash with the
// sibling, ordered by the index bit) or an injection (compress it with the
// injection leaf, running hash on the left).
type pathStep struct {
	sib int  // the sibling or injection leaf
	lvl int  // the level, for a level step
	inj bool // an injection step
}

// Injection is a leaf hash folded into a Merkle path at the level whose width
// (number of nodes) is Width, as merkle.LevelInjection: after the level's
// compression, the running hash h becomes compress(h, Leaf). A width equal to
// the number of leaves folds it into the leaf itself.
type Injection struct {
	Width int
	Leaf  int
}

// MerklePath checks that the digest at leaf is the leaf of index (lane 0 of
// the index cell) under the root, with siblings leaf-level first, and the
// injections of a mixed-height tree (in schedule order: non-increasing
// widths, as merkle.VerifyWithInjections).
func (m *Machine) MerklePath(leaf int, siblings []int, index int, root int, injections ...Injection) {
	steps, err := pathSteps(siblings, injections)
	if err != nil {
		panic(fmt.Sprintf("MerklePath: %v", err))
	}
	if len(steps) == 0 {
		panic("MerklePath: no level and no injection")
	}
	m.read(leaf)
	m.read(index)
	m.read(root)
	for _, st := range steps {
		m.read(st.sib)
	}
	m.paths = append(m.paths, pathInst{leaf: leaf, index: index, root: root, siblings: siblings, steps: steps, xb: -1})
	m.record(instrPath, len(m.paths)-1)
}

// pathSteps orders the rows of a path: the leaf-level injections, then every
// level followed by the injections at the width above it.
func pathSteps(siblings []int, injections []Injection) ([]pathStep, error) {
	d := len(siblings)
	prev := 1 << d
	for k, inj := range injections {
		w := inj.Width
		if w <= 0 || w&(w-1) != 0 || w > prev {
			return nil, fmt.Errorf("injection %d: width %d after %d (widths must be non-increasing powers of two, at most 2^depth)", k, w, prev)
		}
		prev = w
	}
	var steps []pathStep
	next := 0
	fold := func(width int) {
		for ; next < len(injections) && injections[next].Width == width; next++ {
			steps = append(steps, pathStep{sib: injections[next].Leaf, inj: true})
		}
	}
	fold(1 << d)
	for k, s := range siblings {
		steps = append(steps, pathStep{sib: s, lvl: k})
		fold(1 << (d - k - 1))
	}
	if next != len(injections) {
		return nil, fmt.Errorf("injection of width %d does not fit a path of depth %d", injections[next].Width, d)
	}
	return steps, nil
}

// MerklePathX is MerklePath for the Merkle tree of a FRI layer over a domain
// of generator g⁻¹ = gInv: it also returns the cell [x⁻¹, b0], where x⁻¹ =
// gInv^bitrev(index) (bit-reversed over the path depth) is the inverse of the
// fold point of the queried pair, and b0 is the index's low bit.
func (m *Machine) MerklePathX(leaf int, siblings []int, index int, root int, gInv koalabear.Element, injections ...Injection) int {
	m.MerklePath(leaf, siblings, index, root, injections...)
	p := &m.paths[len(m.paths)-1]
	d := len(siblings)
	for lvl := range d {
		g := gInv
		for range d - 1 - lvl {
			g.Square(&g)
		}
		p.gens = append(p.gens, g)
	}
	p.xb = m.alloc()
	return p.xb
}

// execPath computes the [x⁻¹, b0] cell of a MerklePathX.
func (m *Machine) execPath(p pathInst, r *Run) {
	if p.gens == nil {
		return
	}
	idx := r.values[p.index][0].Uint64()
	var xb Cell
	xb[0].SetOne()
	for lvl, g := range p.gens {
		if idx>>lvl&1 == 1 {
			xb[0].Mul(&xb[0], &g)
		}
	}
	xb[1].SetUint64(idx & 1)
	r.values[p.xb] = xb
}

// merkleChip: one row per step of a Merkle path (see pathSteps): a level,
// leaf level first, or an injection.
//
// Columns: cur0..7 (the running hash entering the row), s0..7 (the sibling,
// or the injection leaf), b (the direction bit), idx (the index left to
// consume), out0..7, x (the x⁻¹ accumulator), b0 (the index's low bit).
// Setup: first, last, active, inj (an injection row), lvl0 (the first level
// row), leaf_addr, idx_addr, sib_addr, root_addr, g (the accumulator constant
// of the level, 1 on injection rows), xb_addr and xb_mult (the cell [x⁻¹, b0],
// written on the last row).
//
// Constraints:
//
//	b·(b − 1) = 0,  inj·b = 0
//	idx = b + (2 − inj)·idx[+1]  on every row but the last of a path: a level
//	                             consumes a bit, an injection none
//	idx = b                      on the last row (the index is below 2^depth)
//	                             and on padding rows
//	cur = out[−1]                on every row but the first of a path
//	x = 1 + b·(g − 1)            on the first row
//	x = x[−1]·(1 + b·(g − 1))    on the others
//	b0 = b on the first level row, b0 = b0[−1] on the following rows
//
// and out = compress(b ? (s, cur) : (cur, s)), looked up in the P2 core. The
// first row reads the leaf digest and the index (lane 0 of its cell); the last
// row reads the root with its own output.
type merkleChip struct{ m *Machine }

func (c merkleChip) name() string { return merkleMod }

func (c merkleChip) rows() int {
	n := 0
	for _, p := range c.m.paths {
		n += len(p.steps)
	}
	return n
}

func (c merkleChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[merkleMod]
	first, last, active := setupCol(merkleMod, merkleFirst), setupCol(merkleMod, merkleLast), setupCol(merkleMod, merkleActive)
	inj, lvl0 := setupCol(merkleMod, merkleInj), setupCol(merkleMod, merkleLvl0)
	bit, idx := col(merkleMod, merkleB), col(merkleMod, merkleIdx)
	mm.AssertZero(bit.Mul(bit.Sub(one())))
	mm.AssertZero(inj.Mul(bit))
	// (active − last) is 1 on every path row but the last, 0 elsewhere, so the
	// recurrence never reads across a path end or the wrap-around.
	mm.AssertZero(idx.Sub(bit).Sub(active.Sub(last).Mul(constE(2).Sub(inj)).Mul(colShift(merkleMod, merkleIdx, 1))))
	for i := range digest {
		cur, prev := col(merkleMod, laneName(merkleCur, i)), colShift(merkleMod, laneName(merkleOut, i), -1)
		mm.AssertZero(one().Sub(first).Mul(cur.Sub(prev)))
	}
	// x⁻¹ = Π_lvl (b_lvl ? g_lvl : 1), with g_lvl = gInv^(2^(depth−1−lvl)).
	x, b0 := col(merkleMod, merkleX), col(merkleMod, merkleB0)
	factor := one().Add(bit.Mul(setupCol(merkleMod, merkleG).Sub(one())))
	notFirst := active.Sub(first)
	mm.AssertZero(first.Mul(x.Sub(factor)))
	mm.AssertZero(notFirst.Mul(x.Sub(colShift(merkleMod, merkleX, -1).Mul(factor))))
	mm.AssertZero(lvl0.Mul(b0.Sub(bit)))
	mm.AssertZero(notFirst.Mul(one().Sub(lvl0)).Mul(b0.Sub(colShift(merkleMod, merkleB0, -1))))

	bus.Read(merkleMod, setupCol(merkleMod, merkleLeafAddr), cellCols(merkleMod, merkleCur, 0), first)
	bus.Read(merkleMod, setupCol(merkleMod, merkleIdxAddr), cellOf(idx), first)
	bus.Read(merkleMod, setupCol(merkleMod, merkleSibAddr), cellCols(merkleMod, merkleS, 0), active)
	bus.Read(merkleMod, setupCol(merkleMod, merkleRootAddr), cellCols(merkleMod, merkleOut, 0), last)
	bus.Write(merkleMod, setupCol(merkleMod, merkleXbAddr), cellOf(x, b0), setupCol(merkleMod, merkleXbMult))

	src := board.NewTable(merkleMod, width+digest)
	src.In[0] = constE(nodeTag)
	for i := 1; i < digest; i++ {
		src.In[i] = expr.Const(koalabear.Element{})
	}
	for i := range digest {
		cur, sib := col(merkleMod, laneName(merkleCur, i)), col(merkleMod, laneName(merkleS, i))
		src.In[digest+i] = cur.Add(bit.Mul(sib.Sub(cur)))
		src.In[2*digest+i] = sib.Add(bit.Mul(cur.Sub(sib)))
		src.In[width+i] = col(merkleMod, laneName(merkleOut, i))
	}
	return arguments.CLookupTuple(b, src, p2Table(digest), active, one())
}

func (c merkleChip) setup(cs *cols) {
	cs.declare(merkleFirst, merkleLast, merkleActive, merkleInj, merkleLvl0, merkleLeafAddr, merkleIdxAddr, merkleSibAddr, merkleRootAddr, merkleG, merkleXbAddr, merkleXbMult)
	row := 0
	for _, p := range c.m.paths {
		for k, st := range p.steps {
			cs.set(merkleActive, row, 1)
			cs.set(merkleSibAddr, row, uint64(st.sib))
			if k == 0 {
				cs.set(merkleFirst, row, 1)
				cs.set(merkleLeafAddr, row, uint64(p.leaf))
				cs.set(merkleIdxAddr, row, uint64(p.index))
			}
			g := koalabear.One()
			if st.inj {
				cs.set(merkleInj, row, 1)
			} else {
				if st.lvl == 0 {
					cs.set(merkleLvl0, row, 1)
				}
				if p.gens != nil {
					g = p.gens[st.lvl]
				}
			}
			cs.setElem(merkleG, row, g)
			if k == len(p.steps)-1 {
				cs.set(merkleLast, row, 1)
				cs.set(merkleRootAddr, row, uint64(p.root))
				if p.gens != nil {
					cs.set(merkleXbAddr, row, uint64(p.xb))
					cs.set(merkleXbMult, row, uint64(c.m.reads[p.xb]))
				}
			}
			row++
		}
	}
}

// trace fills the steps, and records the compressions for the P2 core.
func (c merkleChip) trace(cs *cols, r *Run) error {
	cs.declare(merkleB, merkleIdx, merkleX, merkleB0)
	cs.declareLanes(merkleCur, digest)
	cs.declareLanes(merkleS, digest)
	cs.declareLanes(merkleOut, digest)
	perm := newPerm()
	row := 0
	var prevOut Cell
	for _, p := range c.m.paths {
		cur := r.values[p.leaf]
		index := r.values[p.index][0].Uint64()
		b0 := index & 1
		var x koalabear.Element
		x.SetOne()
		for _, st := range p.steps {
			sib := r.values[st.sib]
			bitV := index & 1
			if st.inj {
				bitV = 0
			}
			cs.set(merkleB, row, bitV)
			cs.set(merkleIdx, row, index)
			cs.set(merkleB0, row, b0)
			if bitV == 1 {
				g := koalabear.One()
				if p.gens != nil {
					g = p.gens[st.lvl]
				}
				x.Mul(&x, &g)
			}
			cs.setElem(merkleX, row, x)
			var in [width]koalabear.Element
			in[0].SetUint64(nodeTag)
			left, right := cur, sib
			if bitV == 1 {
				left, right = sib, cur
			}
			copy(in[digest:], left[:digest])
			copy(in[2*digest:], right[:digest])
			r.p2 = append(r.p2, in)
			out := in
			if err := perm.Permutation(out[:]); err != nil {
				return err
			}
			for i := range digest {
				cs.setElem(laneName(merkleCur, i), row, cur[i])
				cs.setElem(laneName(merkleS, i), row, sib[i])
				cs.setElem(laneName(merkleOut, i), row, out[i])
			}
			copy(prevOut[:], out[:digest])
			copy(cur[:], out[:digest])
			if !st.inj {
				index >>= 1
			}
			row++
		}
	}
	// Padding rows keep cur = out[−1] (their outputs stay zero).
	for ; row < cs.n; row++ {
		for i := range digest {
			cs.setElem(laneName(merkleCur, i), row, prevOut[i])
		}
		prevOut = Cell{}
	}
	return nil
}
