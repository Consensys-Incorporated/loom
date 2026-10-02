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
	"github.com/consensys/loom/trace"
)

// witnessChip: one row per cell the prover writes freely: the inputs, and the
// streams of Pack (whose windows check them against their items).
//
// Setup: addr, mult. Columns: v0..7.
type witnessChip struct{ m *Machine }

func (c witnessChip) name() string { return witnessMod }

func (c witnessChip) cells() []int {
	res := append([]int(nil), c.m.inputs...)
	for _, p := range c.m.packs {
		res = append(res, p.stream...)
	}
	return res
}

func (c witnessChip) rows() int { return len(c.cells()) }

func (c witnessChip) define(b *board.Builder, bus *Bus) error {
	bus.Write(witnessMod, setupCol(witnessMod, "addr"), cellCols(witnessMod, "v", 0), setupCol(witnessMod, "mult"))
	return nil
}

func (c witnessChip) setup(cs *cols) {
	cs.declare("addr", "mult")
	for row, a := range c.cells() {
		cs.set("addr", row, uint64(a))
		cs.set("mult", row, uint64(c.m.reads[a]))
	}
}

func (c witnessChip) trace(cs *cols, r *Run) error {
	cs.declareLanes("v", CellWidth)
	for row, a := range c.cells() {
		cs.setCell("v", row, r.values[a])
	}
	return nil
}

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
type spongeChip struct{ m *Machine }

func (c spongeChip) name() string { return spongeMod }

func (c spongeChip) rows() int {
	n := 0
	for _, s := range c.m.sponges {
		n += len(s.data) / 2
	}
	return n
}

func (c spongeChip) define(b *board.Builder, bus *Bus) error {
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
	return arguments.CLookupTuple(b, src, p2Table(width), active, one())
}

func (c spongeChip) setup(cs *cols) {
	cs.declare("first", "last", "active", "keep_cap", "addr_a", "addr_b", "out_addr", "out_mult")
	for j := range rate {
		cs.declare(fmt.Sprintf("data%d", j), fmt.Sprintf("keep%d", j))
	}
	row := 0
	for _, s := range c.m.sponges {
		blocks := len(s.data) / 2
		for blk := range blocks {
			cs.set("active", row, 1)
			cs.set("addr_a", row, uint64(s.data[2*blk]))
			cs.set("addr_b", row, uint64(s.data[2*blk+1]))
			if blk == 0 {
				cs.set("first", row, 1)
			} else {
				cs.set("keep_cap", row, 1)
			}
			for j := range rate {
				if blk*rate+j < s.length {
					cs.set(fmt.Sprintf("data%d", j), row, 1)
				} else if blk > 0 {
					cs.set(fmt.Sprintf("keep%d", j), row, 1)
				}
			}
			if blk == blocks-1 {
				cs.set("last", row, 1)
				cs.set("out_addr", row, uint64(s.out))
				cs.set("out_mult", row, uint64(c.m.reads[s.out]))
			}
			row++
		}
	}
}

// trace fills the blocks and the chained states, and records the
// permutations for the P2 core.
func (c spongeChip) trace(cs *cols, r *Run) error {
	cs.declareLanes("x", rate)
	cs.declareLanes("out", width)
	perm := newPerm()
	row := 0
	for _, s := range c.m.sponges {
		var state [width]koalabear.Element
		for blk := range len(s.data) / 2 {
			lo, hi := r.values[s.data[2*blk]], r.values[s.data[2*blk+1]]
			for j := range rate {
				x := lo[j%CellWidth]
				if j >= CellWidth {
					x = hi[j-CellWidth]
				}
				cs.setElem(fmt.Sprintf("x%d", j), row, x)
				if blk*rate+j < s.length {
					state[j] = x
				}
			}
			r.p2 = append(r.p2, state)
			if err := perm.Permutation(state[:]); err != nil {
				return err
			}
			for l := range width {
				cs.setElem(fmt.Sprintf("out%d", l), row, state[l])
			}
			row++
		}
	}
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

// TODO maybe put the cols code in trace/
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
