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

type pathInst struct {
	leaf, index, root int
	siblings          []int
	gens              []koalabear.Element // x⁻¹ accumulator constants, nil if unused
	xb                int                 // address of [x⁻¹, b0], if gens != nil
}

// MerklePath checks that the digest at leaf is the leaf of index (lane 0 of
// the index cell) under the root, with siblings leaf-level first.
func (m *Machine) MerklePath(leaf int, siblings []int, index int, root int) {
	m.read(leaf)
	m.read(index)
	m.read(root)
	for _, s := range siblings {
		m.read(s)
	}
	m.paths = append(m.paths, pathInst{leaf: leaf, index: index, root: root, siblings: siblings, xb: -1})
	m.record(instrPath, len(m.paths)-1)
}

// MerklePathX is MerklePath for the Merkle tree of a FRI layer over a domain
// of generator g⁻¹ = gInv: it also returns the cell [x⁻¹, b0], where x⁻¹ =
// gInv^bitrev(index) (bit-reversed over the path depth) is the inverse of the
// fold point of the queried pair, and b0 is the index's low bit.
func (m *Machine) MerklePathX(leaf int, siblings []int, index int, root int, gInv koalabear.Element) int {
	m.MerklePath(leaf, siblings, index, root)
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

// merkleChip: one row per level of a Merkle path, leaf level first.
//
// Columns: cur0..7 (the digest entering the level), s0..7 (the sibling), b
// (the direction bit), idx (the index at this level), out0..7, x (the x⁻¹
// accumulator), b0 (the index's low bit). Setup: first, last, active,
// leaf_addr, idx_addr, sib_addr, root_addr, g (the accumulator constant of the
// level), xb_addr and xb_mult (the cell [x⁻¹, b0], written on the last row).
//
// Constraints:
//
//	b·(b − 1) = 0
//	idx = b + 2·idx[+1]        on every row but the last of a path
//	idx = b                    on the last row (the index is below 2^depth)
//	                           and on padding rows
//	cur = out[−1]              on every row but the first of a path
//	x = 1 + b·(g − 1)          on the first row
//	x = x[−1]·(1 + b·(g − 1))  on the others
//	b0 = b on the first row, b0 = b0[−1] on the others
//
// and out = compress(b ? (s, cur) : (cur, s)), looked up in the P2 core. The
// first row reads the leaf digest and the index (lane 0 of its cell); the last
// row reads the root with its own output.
type merkleChip struct{ m *Machine }

func (c merkleChip) name() string { return merkleMod }

func (c merkleChip) rows() int {
	n := 0
	for _, p := range c.m.paths {
		n += len(p.siblings)
	}
	return n
}

func (c merkleChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[merkleMod]
	first, last, active := setupCol(merkleMod, "first"), setupCol(merkleMod, "last"), setupCol(merkleMod, "active")
	bit, idx := col(merkleMod, "b"), col(merkleMod, "idx")
	mm.AssertZero(bit.Mul(bit.Sub(one())))
	// (active − last) is 1 on every path row but the last, 0 elsewhere, so the
	// recurrence never reads across a path end or the wrap-around.
	mm.AssertZero(idx.Sub(bit).Sub(active.Sub(last).Mul(constE(2)).Mul(colShift(merkleMod, "idx", 1))))
	for i := range digest {
		cur, prev := col(merkleMod, fmt.Sprintf("cur%d", i)), colShift(merkleMod, fmt.Sprintf("out%d", i), -1)
		mm.AssertZero(one().Sub(first).Mul(cur.Sub(prev)))
	}
	// x⁻¹ = Π_lvl (b_lvl ? g_lvl : 1), with g_lvl = gInv^(2^(depth−1−lvl)).
	x, b0 := col(merkleMod, "x"), col(merkleMod, "b0")
	factor := one().Add(bit.Mul(setupCol(merkleMod, "g").Sub(one())))
	notFirst := active.Sub(first)
	mm.AssertZero(first.Mul(x.Sub(factor)))
	mm.AssertZero(notFirst.Mul(x.Sub(colShift(merkleMod, "x", -1).Mul(factor))))
	mm.AssertZero(first.Mul(b0.Sub(bit)))
	mm.AssertZero(notFirst.Mul(b0.Sub(colShift(merkleMod, "b0", -1))))

	bus.Read(merkleMod, setupCol(merkleMod, "leaf_addr"), cellCols(merkleMod, "cur", 0), first)
	bus.Read(merkleMod, setupCol(merkleMod, "idx_addr"), cellOf(idx), first)
	bus.Read(merkleMod, setupCol(merkleMod, "sib_addr"), cellCols(merkleMod, "s", 0), active)
	bus.Read(merkleMod, setupCol(merkleMod, "root_addr"), cellCols(merkleMod, "out", 0), last)
	bus.Write(merkleMod, setupCol(merkleMod, "xb_addr"), cellOf(x, b0), setupCol(merkleMod, "xb_mult"))

	src := board.NewTable(merkleMod, width+digest)
	src.In[0] = constE(nodeTag)
	for i := 1; i < digest; i++ {
		src.In[i] = expr.Const(koalabear.Element{})
	}
	for i := range digest {
		cur, sib := col(merkleMod, fmt.Sprintf("cur%d", i)), col(merkleMod, fmt.Sprintf("s%d", i))
		src.In[digest+i] = cur.Add(bit.Mul(sib.Sub(cur)))
		src.In[2*digest+i] = sib.Add(bit.Mul(cur.Sub(sib)))
		src.In[width+i] = col(merkleMod, fmt.Sprintf("out%d", i))
	}
	return arguments.CLookupTuple(b, src, p2Table(digest), active, one())
}

func (c merkleChip) setup(cs *cols) {
	cs.declare("first", "last", "active", "leaf_addr", "idx_addr", "sib_addr", "root_addr", "g", "xb_addr", "xb_mult")
	row := 0
	for _, p := range c.m.paths {
		for lvl, sAddr := range p.siblings {
			cs.set("active", row, 1)
			cs.set("sib_addr", row, uint64(sAddr))
			if lvl == 0 {
				cs.set("first", row, 1)
				cs.set("leaf_addr", row, uint64(p.leaf))
				cs.set("idx_addr", row, uint64(p.index))
			}
			g := koalabear.One()
			if p.gens != nil {
				g = p.gens[lvl]
			}
			cs.setElem("g", row, g)
			if lvl == len(p.siblings)-1 {
				cs.set("last", row, 1)
				cs.set("root_addr", row, uint64(p.root))
				if p.gens != nil {
					cs.set("xb_addr", row, uint64(p.xb))
					cs.set("xb_mult", row, uint64(c.m.reads[p.xb]))
				}
			}
			row++
		}
	}
}

// trace fills the levels, and records the compressions for the P2 core.
func (c merkleChip) trace(cs *cols, r *Run) error {
	cs.declare("b", "idx", "x", "b0")
	cs.declareLanes("cur", digest)
	cs.declareLanes("s", digest)
	cs.declareLanes("out", digest)
	perm := newPerm()
	row := 0
	var prevOut Cell
	for _, p := range c.m.paths {
		cur := r.values[p.leaf]
		index := r.values[p.index][0].Uint64()
		b0 := index & 1
		var x koalabear.Element
		x.SetOne()
		for lvl, sAddr := range p.siblings {
			sib := r.values[sAddr]
			bitV := index & 1
			cs.set("b", row, bitV)
			cs.set("idx", row, index)
			cs.set("b0", row, b0)
			if bitV == 1 {
				g := koalabear.One()
				if p.gens != nil {
					g = p.gens[lvl]
				}
				x.Mul(&x, &g)
			}
			cs.setElem("x", row, x)
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
				cs.setElem(fmt.Sprintf("cur%d", i), row, cur[i])
				cs.setElem(fmt.Sprintf("s%d", i), row, sib[i])
				cs.setElem(fmt.Sprintf("out%d", i), row, out[i])
			}
			copy(prevOut[:], out[:digest])
			copy(cur[:], out[:digest])
			index >>= 1
			row++
		}
	}
	// Padding rows keep cur = out[−1] (their outputs stay zero).
	for ; row < cs.n; row++ {
		for i := range digest {
			cs.setElem(fmt.Sprintf("cur%d", i), row, prevOut[i])
		}
		prevOut = Cell{}
	}
	return nil
}
