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
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

// The Merkle path's columns on the P2 core (see p2Chip), prefixed so they do
// not meet the sponge's. Setup:
const (
	merkleActive   = "mk_active"
	merkleFirst    = "mk_first"
	merkleLast     = "mk_last"
	merkleInj      = "mk_inj"
	merkleLvl0     = "mk_lvl0"
	merkleLeafAddr = "mk_leaf_addr"
	merkleIdxAddr  = "mk_idx_addr"
	merkleSibAddr  = "mk_sib_addr"
	merkleRootAddr = "mk_root_addr"
	merkleG        = "mk_g"
	merkleXbAddr   = "mk_xb_addr"
	merkleXbMult   = "mk_xb_mult"
)

// and witness.
const (
	merkleB   = "mk_b"   // the direction bit
	merkleIdx = "mk_idx" // the index left to consume
	merkleX   = "mk_x"   // the x⁻¹ accumulator
	merkleB0  = "mk_b0"  // the index's low bit
	merkleF   = "mk_f"   // the accumulator's factor, 1 + b·(g − 1)
	merkleCur = "mk_cur" // lanes: the running hash entering the row
	merkleSib = "mk_sib" // lanes: the sibling, or the injection leaf
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

// pathStepRows is the number of rows the Merkle paths take on the core.
func (m *Machine) pathStepRows() int {
	n := 0
	for _, p := range m.paths {
		n += len(p.steps)
	}
	return n
}

// merkleInput is the permutation input the Merkle path asks for on lane l:
// the node compression of the running hash and the sibling, ordered by the
// direction bit.
//
//	s0 = nodeTag,  s1..7 = 0
//	s_{8+i}  = cur_i + b·(sib_i − cur_i)
//	s_{16+i} = sib_i + b·(cur_i − sib_i)
func merkleInput(l int) expr.Expr {
	if l == 0 {
		return constE(nodeTag)
	}
	if l < digest {
		return zero()
	}
	i := l % digest
	bit := col(p2Mod, merkleB)
	cur, sib := col(p2Mod, laneName(merkleCur, i)), col(p2Mod, laneName(merkleSib, i))
	if l < 2*digest {
		return cur.Add(bit.Mul(sib.Sub(cur)))
	}
	return sib.Add(bit.Mul(cur.Sub(sib)))
}

// merkleDefine adds the path's constraints and bus accesses. Each is gated by
// a setup selector that is zero outside the Merkle rows, so the rows above
// (the sponge's), below (the dynamic paths') and the padding rows are left
// alone.
//
//	b·(b − 1) = 0,  inj·b = 0
//	idx = b + (2 − inj)·idx[+1]  on every Merkle row but the last of a path:
//	                             a level consumes a bit, an injection none
//	idx = b                      on the last row (the index is below 2^depth)
//	                             and on every non-Merkle row
//	cur = r[−1]                  on every Merkle row but the first of a path
//	f = 1 + b·(g − 1)            on every row (1 outside the Merkle rows)
//	x = f                        on the first row
//	x = x[−1]·f                  on the others (f keeps it at degree 3)
//	b0 = b on the first level row, b0 = b0[−1] on the following rows
//
// The first row reads the leaf digest and the index (lane 0 of its cell); the
// last row reads the root with the permutation's first digest lanes.
func merkleDefine(mm *board.Module, bus *Bus) {
	first, last, active := setupCol(p2Mod, merkleFirst), setupCol(p2Mod, merkleLast), setupCol(p2Mod, merkleActive)
	inj, lvl0 := setupCol(p2Mod, merkleInj), setupCol(p2Mod, merkleLvl0)
	bit, idx := col(p2Mod, merkleB), col(p2Mod, merkleIdx)
	mm.AssertZero(bit.Mul(bit.Sub(one())))
	mm.AssertZero(inj.Mul(bit))
	// (active − last) is 1 on every Merkle row but the last of a path, 0
	// elsewhere, so the recurrence never reads across a path end, into another
	// chip's rows or across the wrap-around.
	mm.AssertZero(idx.Sub(bit).Sub(active.Sub(last).Mul(constE(2).Sub(inj)).Mul(colShift(p2Mod, merkleIdx, 1))))
	notFirst := active.Sub(first)
	for i := range digest {
		cur, prev := col(p2Mod, laneName(merkleCur, i)), colShift(p2Mod, laneName(p2R, i), -1)
		mm.AssertZero(notFirst.Mul(cur.Sub(prev)))
	}
	// x⁻¹ = Π_lvl (b_lvl ? g_lvl : 1), with g_lvl = gInv^(2^(depth−1−lvl)).
	x, b0 := col(p2Mod, merkleX), col(p2Mod, merkleB0)
	factor := col(p2Mod, merkleF)
	mm.AssertZero(factor.Sub(one().Add(bit.Mul(setupCol(p2Mod, merkleG).Sub(one())))))
	mm.AssertZero(first.Mul(x.Sub(factor)))
	mm.AssertZero(notFirst.Mul(x.Sub(colShift(p2Mod, merkleX, -1).Mul(factor))))
	mm.AssertZero(lvl0.Mul(b0.Sub(bit)))
	mm.AssertZero(notFirst.Mul(one().Sub(lvl0)).Mul(b0.Sub(colShift(p2Mod, merkleB0, -1))))

	bus.Read(p2Mod, setupCol(p2Mod, merkleLeafAddr), cellCols(p2Mod, merkleCur, 0), first)
	bus.Read(p2Mod, setupCol(p2Mod, merkleIdxAddr), cellOf(idx), first)
	bus.Read(p2Mod, setupCol(p2Mod, merkleSibAddr), cellCols(p2Mod, merkleSib, 0), active)
	bus.Read(p2Mod, setupCol(p2Mod, merkleRootAddr), cellCols(p2Mod, p2R, 0), last)
	bus.Write(p2Mod, setupCol(p2Mod, merkleXbAddr), cellOf(x, b0), setupCol(p2Mod, merkleXbMult))
}

// merkleSetup fills the paths' setup columns, from row off.
func (c p2Chip) merkleSetup(cs *cols, off int) {
	cs.declare(merkleFirst, merkleLast, merkleActive, merkleInj, merkleLvl0, merkleLeafAddr, merkleIdxAddr, merkleSibAddr, merkleRootAddr, merkleG, merkleXbAddr, merkleXbMult)
	row := off
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

// merkleTrace fills the paths' steps and their compressions from row off, and
// returns the first row after them.
func (c p2Chip) merkleTrace(cs *cols, r *Run, perm *poseidon2.Permutation, off int) (int, error) {
	cs.declare(merkleB, merkleIdx, merkleX, merkleB0, merkleF)
	for row := range cs.n {
		cs.set(merkleF, row, 1) // b = 0 outside the Merkle rows and on their b = 0 rows
	}
	cs.declareLanes(merkleCur, digest)
	cs.declareLanes(merkleSib, digest)
	row := off
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
				cs.setElem(merkleF, row, g)
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
			out, err := setPermRow(cs, perm, row, in)
			if err != nil {
				return 0, err
			}
			for i := range digest {
				cs.setElem(laneName(merkleCur, i), row, cur[i])
				cs.setElem(laneName(merkleSib, i), row, sib[i])
			}
			copy(cur[:], out[:digest])
			if !st.inj {
				index >>= 1
			}
			row++
		}
	}
	return row, nil
}
