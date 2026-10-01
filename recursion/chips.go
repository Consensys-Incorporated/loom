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
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"
	"github.com/consensys/loom/zkc"
)

// spongeChip: one row per 16-element block of a sponge.
//
// Columns: x0..15 (the block, read from two cells), out0..23 (the permutation
// output). Setup: first, last, active, data_j (lane j is input), keep_j =
// (1 − data_j)·(1 − first), keep_cap = 1 − first, addr_a, addr_b (the two
// data cells), out_addr and out_mult (the digest, written on the last row).
//
// The permutation input is data_j·x_j + keep_j·out_j[−1] on the rate lanes and
// keep_cap·out_j[−1] on the capacity: the state chains from row to row, and a
// trailing partial block keeps the previous state on its unused lanes, as
// loom's overwrite-mode sponge does.
func (m *Machine) spongeChip(b *board.Builder, bus *Bus, t trace.Trace, p2 *[][width]koalabear.Element) error {
	rows := 0
	for _, s := range m.sponges {
		rows += len(s.data) / 2
	}
	n := height(rows)
	mod := board.NewModule(spongeMod)
	mod.N = n
	b.AddModule(mod)

	active := setupCol(spongeMod, "active")
	bus.Read(spongeMod, setupCol(spongeMod, "addr_a"), cellCols(spongeMod, "x", 0), active)
	bus.Read(spongeMod, setupCol(spongeMod, "addr_b"), cellCols(spongeMod, "x", CellWidth), active)
	bus.Write(spongeMod, setupCol(spongeMod, "out_addr"), cellCols(spongeMod, "out", 0), setupCol(spongeMod, "out_mult"))

	src := board.NewTable(spongeMod, 2*width)
	for l := range width {
		prev := colShift(spongeMod, fmt.Sprintf("out%d", l), -1)
		if l < rate {
			src.In[l] = setupCol(spongeMod, fmt.Sprintf("data%d", l)).Mul(col(spongeMod, fmt.Sprintf("x%d", l))).
				Add(setupCol(spongeMod, fmt.Sprintf("keep%d", l)).Mul(prev))
		} else {
			src.In[l] = setupCol(spongeMod, "keep_cap").Mul(prev)
		}
		src.In[width+l] = col(spongeMod, fmt.Sprintf("out%d", l))
	}
	if err := arguments.CLookupTuple(b, src, p2Table(width), active, one()); err != nil {
		return err
	}

	c := newCols(n)
	c.declare("first", "last", "active", "keep_cap", "addr_a", "addr_b", "out_addr", "out_mult")
	for j := range rate {
		c.declare(fmt.Sprintf("x%d", j), fmt.Sprintf("data%d", j), fmt.Sprintf("keep%d", j))
	}
	for l := range width {
		c.declare(fmt.Sprintf("out%d", l))
	}
	perm := poseidon2.NewPermutation(width, zkc.P2FullRounds, zkc.P2PartialRounds)
	row := 0
	for _, s := range m.sponges {
		var state [width]koalabear.Element
		blocks := len(s.data) / 2
		for blk := 0; blk < blocks; blk++ {
			c.set("active", row, 1)
			c.set("addr_a", row, uint64(s.data[2*blk]))
			c.set("addr_b", row, uint64(s.data[2*blk+1]))
			if blk == 0 {
				c.set("first", row, 1)
				state = [width]koalabear.Element{}
			} else {
				c.set("keep_cap", row, 1)
			}
			lo, hi := m.cells[s.data[2*blk]], m.cells[s.data[2*blk+1]]
			for j := range rate {
				x := lo[j%CellWidth]
				if j >= CellWidth {
					x = hi[j-CellWidth]
				}
				c.setElem(fmt.Sprintf("x%d", j), row, x)
				if blk*rate+j < s.length {
					c.set(fmt.Sprintf("data%d", j), row, 1)
					state[j] = x
				} else if blk > 0 {
					c.set(fmt.Sprintf("keep%d", j), row, 1)
				}
			}
			*p2 = append(*p2, state)
			if err := perm.Permutation(state[:]); err != nil {
				return err
			}
			for l := range width {
				c.setElem(fmt.Sprintf("out%d", l), row, state[l])
			}
			if blk == blocks-1 {
				c.set("last", row, 1)
				c.set("out_addr", row, uint64(s.out))
				c.set("out_mult", row, uint64(m.reads[s.out]))
			}
			row++
		}
	}
	c.store(t, spongeMod)
	return nil
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
func (m *Machine) merkleChip(b *board.Builder, bus *Bus, t trace.Trace, p2 *[][width]koalabear.Element) error {
	rows := 0
	for _, p := range m.paths {
		rows += len(p.siblings)
	}
	n := height(rows)
	mod := board.NewModule(merkleMod)
	mod.N = n
	b.AddModule(mod)
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
	var xbCell [CellWidth]expr.Expr
	xbCell[0], xbCell[1] = x, b0
	for i := 2; i < CellWidth; i++ {
		xbCell[i] = expr.Const(koalabear.Element{})
	}
	bus.Write(merkleMod, setupCol(merkleMod, "xb_addr"), xbCell, setupCol(merkleMod, "xb_mult"))

	var idxCell [CellWidth]expr.Expr
	idxCell[0] = idx
	for i := 1; i < CellWidth; i++ {
		idxCell[i] = expr.Const(koalabear.Element{})
	}
	bus.Read(merkleMod, setupCol(merkleMod, "leaf_addr"), cellCols(merkleMod, "cur", 0), first)
	bus.Read(merkleMod, setupCol(merkleMod, "idx_addr"), idxCell, first)
	bus.Read(merkleMod, setupCol(merkleMod, "sib_addr"), cellCols(merkleMod, "s", 0), active)
	bus.Read(merkleMod, setupCol(merkleMod, "root_addr"), cellCols(merkleMod, "out", 0), last)

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
	if err := arguments.CLookupTuple(b, src, p2Table(digest), active, one()); err != nil {
		return err
	}

	c := newCols(n)
	c.declare("first", "last", "active", "leaf_addr", "idx_addr", "sib_addr", "root_addr", "b", "idx",
		"x", "b0", "g", "xb_addr", "xb_mult")
	for i := range digest {
		c.declare(fmt.Sprintf("cur%d", i), fmt.Sprintf("s%d", i), fmt.Sprintf("out%d", i))
	}
	perm := poseidon2.NewPermutation(width, zkc.P2FullRounds, zkc.P2PartialRounds)
	row := 0
	var prevOut Cell
	for _, p := range m.paths {
		cur := m.cells[p.leaf]
		index := m.cells[p.index][0].Uint64()
		b0 := index & 1
		var x koalabear.Element
		x.SetOne()
		for lvl, sAddr := range p.siblings {
			sib := m.cells[sAddr]
			bitV := index & 1
			c.set("active", row, 1)
			c.set("sib_addr", row, uint64(sAddr))
			if lvl == 0 {
				c.set("first", row, 1)
				c.set("leaf_addr", row, uint64(p.leaf))
				c.set("idx_addr", row, uint64(p.index))
			}
			c.set("b", row, bitV)
			c.set("idx", row, index)
			c.set("b0", row, b0)
			g := koalabear.One()
			if p.gens != nil {
				g = p.gens[lvl]
			}
			c.setElem("g", row, g)
			if bitV == 1 {
				x.Mul(&x, &g)
			}
			c.setElem("x", row, x)
			var in [width]koalabear.Element
			in[0].SetUint64(nodeTag)
			left, right := cur, sib
			if bitV == 1 {
				left, right = sib, cur
			}
			copy(in[digest:], left[:])
			copy(in[2*digest:], right[:])
			*p2 = append(*p2, in)
			out := in
			if err := perm.Permutation(out[:]); err != nil {
				return err
			}
			for i := range digest {
				c.setElem(fmt.Sprintf("cur%d", i), row, cur[i])
				c.setElem(fmt.Sprintf("s%d", i), row, sib[i])
				c.setElem(fmt.Sprintf("out%d", i), row, out[i])
			}
			if lvl == len(p.siblings)-1 {
				c.set("last", row, 1)
				c.set("root_addr", row, uint64(p.root))
				if p.gens != nil {
					c.set("xb_addr", row, uint64(p.xb))
					c.set("xb_mult", row, uint64(m.reads[p.xb]))
				}
			}
			copy(prevOut[:], out[:digest])
			copy(cur[:], out[:digest])
			index >>= 1
			row++
		}
	}
	// Padding rows keep cur = out[−1] (their outputs stay zero).
	for ; row < n; row++ {
		for i := range digest {
			c.setElem(fmt.Sprintf("cur%d", i), row, prevOut[i])
		}
		prevOut = Cell{}
	}
	c.store(t, merkleMod)
	return nil
}

// cols accumulates the columns of a module.
type cols struct {
	n    int
	vals map[string][]koalabear.Element
}

func newCols(n int) *cols { return &cols{n: n, vals: map[string][]koalabear.Element{}} }

func (c *cols) declare(names ...string) {
	for _, n := range names {
		c.get(n)
	}
}

func (c *cols) get(name string) []koalabear.Element {
	v, ok := c.vals[name]
	if !ok {
		v = make([]koalabear.Element, c.n)
		c.vals[name] = v
	}
	return v
}

func (c *cols) set(name string, row int, v uint64) { c.get(name)[row].SetUint64(v) }

func (c *cols) setInt(name string, row int, v int64) { c.get(name)[row].SetInt64(v) }

func (c *cols) setElem(name string, row int, v koalabear.Element) { c.get(name)[row] = v }

func (c *cols) store(t trace.Trace, module string) {
	for name, v := range c.vals {
		t.SetBase(module+"."+name, v)
	}
}
