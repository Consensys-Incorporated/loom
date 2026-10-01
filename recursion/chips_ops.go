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
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"
)

// A chip whose instance list is empty adds no module.

func zero() expr.Expr { return expr.Const(koalabear.Element{}) }

func constElem(v koalabear.Element) expr.Expr { return expr.Const(v) }

func setupCellCols(module, prefix string) [CellWidth]expr.Expr {
	var res [CellWidth]expr.Expr
	for i := range res {
		res[i] = setupCol(module, fmt.Sprintf("%s%d", prefix, i))
	}
	return res
}

// e6Cols returns the 6 columns prefix0..5, shifted by s.
func e6Cols(module, prefix string, s int) []expr.Expr {
	res := make([]expr.Expr, 6)
	for i := range res {
		res[i] = colShift(module, fmt.Sprintf("%s%d", prefix, i), s)
	}
	return res
}

// cellOf pads lanes to a cell tuple with zero lanes.
func cellOf(lanes ...expr.Expr) [CellWidth]expr.Expr {
	var res [CellWidth]expr.Expr
	for i := range res {
		if i < len(lanes) {
			res[i] = lanes[i]
		} else {
			res[i] = zero()
		}
	}
	return res
}

func newChipModule(b *board.Builder, name string, rows int) int {
	n := height(rows)
	mod := board.NewModule(name)
	mod.N = n
	b.AddModule(mod)
	return n
}

func (c *cols) setE6(prefix string, row int, x ext.E6) {
	cell := E6Cell(x)
	for i := range 6 {
		c.setElem(fmt.Sprintf("%s%d", prefix, i), row, cell[i])
	}
}

func (c *cols) setCell(prefix string, row int, v Cell) {
	for i := range CellWidth {
		c.setElem(fmt.Sprintf("%s%d", prefix, i), row, v[i])
	}
}

func (c *cols) declareLanes(prefix string, n int) {
	for i := range n {
		c.declare(fmt.Sprintf("%s%d", prefix, i))
	}
}

// constChip: one row per constant cell, all setup: addr, mult, v0..v7.
func (m *Machine) constChip(b *board.Builder, bus *Bus, t trace.Trace) error {
	if len(m.constList) == 0 {
		return nil
	}
	n := newChipModule(b, constMod, len(m.constList))
	bus.Write(constMod, setupCol(constMod, "addr"), setupCellCols(constMod, "v"), setupCol(constMod, "mult"))
	c := newCols(n)
	c.declare("addr", "mult")
	c.declareLanes("v", CellWidth)
	for row, a := range m.constList {
		c.set("addr", row, uint64(a))
		c.set("mult", row, uint64(m.reads[a]))
		c.setCell("v", row, m.cells[a])
	}
	c.store(t, constMod)
	return nil
}

// windowChip: one row per item of a packed stream.
//
// Columns: p0..7, q0..7 (two consecutive stream cells, the window W = p‖q),
// i0..7 (the item). Setup: active, addr_p, addr_q, sel_q (q is read), addr_i,
// off0..7 (one-hot offset of the item in p), k6 (the item has at least 6
// lanes), k8 (8 lanes). For each lane k of the item,
//
//	mask_k·(i_k − Σ_o off_o·W_{o+k}) = 0,
//
// with mask_0 = 1, mask_1..5 = k6, mask_6,7 = k8. The item's other lanes are
// left to its readers, whose tuples fix them to zero.
func (m *Machine) windowChip(b *board.Builder, bus *Bus, t trace.Trace) error {
	if len(m.windows) == 0 {
		return nil
	}
	n := newChipModule(b, windowMod, len(m.windows))
	mm := b.Modules[windowMod]
	active := setupCol(windowMod, "active")
	bus.Read(windowMod, setupCol(windowMod, "addr_p"), cellCols(windowMod, "p", 0), active)
	bus.Read(windowMod, setupCol(windowMod, "addr_q"), cellCols(windowMod, "q", 0), setupCol(windowMod, "sel_q"))
	bus.Read(windowMod, setupCol(windowMod, "addr_i"), cellCols(windowMod, "i", 0), active)

	window := func(j int) expr.Expr {
		if j < CellWidth {
			return col(windowMod, fmt.Sprintf("p%d", j))
		}
		return col(windowMod, fmt.Sprintf("q%d", j-CellWidth))
	}
	for k := range CellWidth {
		var mask expr.Expr
		switch {
		case k == 0:
			mask = one()
		case k < KindE6:
			mask = setupCol(windowMod, "k6")
		default:
			mask = setupCol(windowMod, "k8")
		}
		var sum expr.Expr = zero()
		for o := range CellWidth {
			sum = sum.Add(setupCol(windowMod, fmt.Sprintf("off%d", o)).Mul(window(o + k)))
		}
		mm.AssertZero(mask.Mul(col(windowMod, fmt.Sprintf("i%d", k)).Sub(sum)))
	}

	c := newCols(n)
	c.declare("active", "addr_p", "addr_q", "sel_q", "addr_i", "k6", "k8")
	c.declareLanes("off", CellWidth)
	c.declareLanes("p", CellWidth)
	c.declareLanes("q", CellWidth)
	c.declareLanes("i", CellWidth)
	for row, w := range m.windows {
		c.set("active", row, 1)
		c.set("addr_p", row, uint64(w.p))
		c.setCell("p", row, m.cells[w.p])
		if w.q >= 0 {
			c.set("addr_q", row, uint64(w.q))
			c.set("sel_q", row, 1)
			c.setCell("q", row, m.cells[w.q])
		}
		c.set("addr_i", row, uint64(w.item))
		c.setCell("i", row, m.cells[w.item])
		c.set(fmt.Sprintf("off%d", w.off), row, 1)
		if w.kind >= KindE6 {
			c.set("k6", row, 1)
		}
		if w.kind == KindDigest {
			c.set("k8", row, 1)
		}
	}
	c.store(t, windowMod)
	return nil
}

// koalaHigh is the value of the top 7 bits (24..30) of p − 1 = 127·2^24: a
// 31-bit integer is below p iff its top 7 bits are not all set, or its low 24
// bits are zero.
const koalaHigh = 127

// bitsChip: BitsWidth rows per decomposition, row i for bit i.
//
// Columns: b (bit i), w (the low bits, Σ_{k<i} b_k·2^k), r ((v mod 2^n) >> i,
// zero for i ≥ n), v (the decomposed value), inv (at row 24, the inverse of
// 127 − (v − w)/2^24 if nonzero). Setup: first, last, active, pow (2^i), inlow
// (i < n), chk (i = 24), addr_v (read on the first row), r_addr, r_mult,
// b_addr, b_mult (the writes of r and b).
//
//	b·(b − 1) = 0
//	w = 0                          on the first row
//	w[+1] = w + b·pow, v[+1] = v   on every row but the last
//	v = w + b·pow                  on the last row
//	r = inlow·(b + 2·r[+1])
//	chk·w·(1 − z·inv) = 0,  z = 127 − (v − w)/2^24   (canonical: v < p)
func (m *Machine) bitsChip(b *board.Builder, bus *Bus, t trace.Trace) error {
	if len(m.bits) == 0 {
		return nil
	}
	n := newChipModule(b, bitsMod, BitsWidth*len(m.bits))
	mm := b.Modules[bitsMod]
	first, last, active := setupCol(bitsMod, "first"), setupCol(bitsMod, "last"), setupCol(bitsMod, "active")
	bit, w, r, v, inv := col(bitsMod, "b"), col(bitsMod, "w"), col(bitsMod, "r"), col(bitsMod, "v"), col(bitsMod, "inv")
	pow := setupCol(bitsMod, "pow")
	notLast := active.Sub(last)

	mm.AssertZero(bit.Mul(bit.Sub(one())))
	mm.AssertZero(first.Mul(w))
	mm.AssertZero(notLast.Mul(colShift(bitsMod, "w", 1).Sub(w).Sub(bit.Mul(pow))))
	mm.AssertZero(notLast.Mul(colShift(bitsMod, "v", 1).Sub(v)))
	mm.AssertZero(last.Mul(v.Sub(w).Sub(bit.Mul(pow))))
	mm.AssertZero(r.Sub(setupCol(bitsMod, "inlow").Mul(bit.Add(constE(2).Mul(colShift(bitsMod, "r", 1))))))
	var inv24 koalabear.Element
	inv24.SetUint64(1 << 24)
	inv24.Inverse(&inv24)
	z := constE(koalaHigh).Sub(v.Sub(w).Mul(constElem(inv24)))
	mm.AssertZero(setupCol(bitsMod, "chk").Mul(w).Mul(one().Sub(z.Mul(inv))))

	bus.Read(bitsMod, setupCol(bitsMod, "addr_v"), cellOf(v), first)
	bus.Write(bitsMod, setupCol(bitsMod, "r_addr"), cellOf(r), setupCol(bitsMod, "r_mult"))
	bus.Write(bitsMod, setupCol(bitsMod, "b_addr"), cellOf(bit), setupCol(bitsMod, "b_mult"))

	c := newCols(n)
	c.declare("b", "w", "r", "v", "inv", "first", "last", "active", "pow", "inlow", "chk",
		"addr_v", "r_addr", "r_mult", "b_addr", "b_mult")
	for k, inst := range m.bits {
		x := m.cells[inst.v][0].Uint64()
		low := x & (1<<inst.n - 1)
		for i := range BitsWidth {
			row := k*BitsWidth + i
			c.set("active", row, 1)
			c.set("pow", row, 1<<i)
			c.set("b", row, x>>i&1)
			c.set("w", row, x&(1<<i-1))
			c.set("v", row, x)
			switch i {
			case 0:
				c.set("first", row, 1)
				c.set("addr_v", row, uint64(inst.v))
			case 24:
				c.set("chk", row, 1)
				var zv koalabear.Element
				zv.SetUint64(koalaHigh - x>>24)
				if !zv.IsZero() {
					zv.Inverse(&zv)
				}
				c.setElem("inv", row, zv)
			case BitsWidth - 1:
				c.set("last", row, 1)
			}
			if i < inst.n {
				c.set("inlow", row, 1)
				c.set("r", row, low>>i)
				c.set("r_addr", row, uint64(inst.out.Shr[i]))
				c.set("r_mult", row, uint64(m.reads[inst.out.Shr[i]]))
				c.set("b_addr", row, uint64(inst.out.Bit[i]))
				c.set("b_mult", row, uint64(m.reads[inst.out.Bit[i]]))
			}
		}
	}
	c.store(t, bitsMod)
	return nil
}

// e6Chip: one E6 operation per row,
//
//	o = mul·(a·b) + add·a + bs·b + hor·(o[−1]·a),
//
// over the columns a0..5, b0..5, o0..5. Setup: mul, add, bs (−1, 0 or 1), hor,
// and per operand x ∈ {a, b, o} addr_x and the signed multiplicity m_x (−1
// read, the read count for a write, 0 unused).
func (m *Machine) e6Chip(b *board.Builder, bus *Bus, t trace.Trace) error {
	if len(m.e6Rows) == 0 {
		return nil
	}
	n := newChipModule(b, e6Mod, len(m.e6Rows))
	mm := b.Modules[e6Mod]
	a, bb, o := e6Cols(e6Mod, "a", 0), e6Cols(e6Mod, "b", 0), e6Cols(e6Mod, "o", 0)
	ab := e6MulExprs(a, bb)
	prevA := e6MulExprs(e6Cols(e6Mod, "o", -1), a)
	mul, add, bs, hor := setupCol(e6Mod, "mul"), setupCol(e6Mod, "add"), setupCol(e6Mod, "bs"), setupCol(e6Mod, "hor")
	for i := range 6 {
		rhs := mul.Mul(ab[i]).Add(add.Mul(a[i])).Add(bs.Mul(bb[i])).Add(hor.Mul(prevA[i]))
		mm.AssertZero(o[i].Sub(rhs))
	}
	for _, x := range []string{"a", "b", "o"} {
		bus.Write(e6Mod, setupCol(e6Mod, "addr_"+x), cellOf(e6Cols(e6Mod, x, 0)...), setupCol(e6Mod, "m_"+x))
	}

	c := newCols(n)
	c.declare("mul", "add", "bs", "hor", "addr_a", "m_a", "addr_b", "m_b", "addr_o", "m_o")
	for _, x := range []string{"a", "b", "o"} {
		c.declareLanes(x, 6)
	}
	for row, r := range m.e6Rows {
		c.setInt("mul", row, r.mul)
		c.setInt("add", row, r.add)
		c.setInt("bs", row, r.bs)
		c.setInt("hor", row, r.hor)
		for _, op := range []struct {
			name string
			s    slot
			v    ext.E6
		}{{"a", r.a, r.va}, {"b", r.b, r.vb}, {"o", r.o, r.vo}} {
			c.setE6(op.name, row, op.v)
			if op.s.role != roleNone {
				c.set("addr_"+op.name, row, uint64(op.s.addr))
				c.setInt("m_"+op.name, row, m.mult(op.s))
			}
		}
	}
	c.store(t, e6Mod)
	return nil
}

// foldChip: one row per FRI round of a query, and a terminal row holding the
// final value in p and q.
//
// Columns: p0..5, q0..5 (the opened pair), al0..5 (α), xi (x⁻¹), bn (selects
// p or q in the next row), j0..5 (the injected term). Setup: active, last (the
// terminal row), addr_p, addr_q, addr_al, addr_xb, addr_j. On every row but
// the terminal one,
//
//	(p + q)/2 + α·(p − q)·xi/2 + j = p[+1] + bn·(q[+1] − p[+1]).
func (m *Machine) foldChip(b *board.Builder, bus *Bus, t trace.Trace) error {
	rows := 0
	for _, ch := range m.folds {
		rows += len(ch)
	}
	if rows == 0 {
		return nil
	}
	n := newChipModule(b, foldMod, rows)
	mm := b.Modules[foldMod]
	active, last := setupCol(foldMod, "active"), setupCol(foldMod, "last")
	notLast := active.Sub(last)
	p, q, al, j := e6Cols(foldMod, "p", 0), e6Cols(foldMod, "q", 0), e6Cols(foldMod, "al", 0), e6Cols(foldMod, "j", 0)
	pn, qn := e6Cols(foldMod, "p", 1), e6Cols(foldMod, "q", 1)
	xi, bn := col(foldMod, "xi"), col(foldMod, "bn")
	var half koalabear.Element
	half.SetUint64(2)
	half.Inverse(&half)
	diff := make([]expr.Expr, 6)
	for i := range diff {
		diff[i] = p[i].Sub(q[i]).Mul(xi).Mul(constElem(half))
	}
	odd := e6MulExprs(al, diff)
	for i := range 6 {
		lhs := p[i].Add(q[i]).Mul(constElem(half)).Add(odd[i]).Add(j[i])
		rhs := pn[i].Add(bn.Mul(qn[i].Sub(pn[i])))
		mm.AssertZero(notLast.Mul(lhs.Sub(rhs)))
	}
	bus.Read(foldMod, setupCol(foldMod, "addr_p"), cellOf(p...), active)
	bus.Read(foldMod, setupCol(foldMod, "addr_q"), cellOf(q...), active)
	bus.Read(foldMod, setupCol(foldMod, "addr_al"), cellOf(al...), notLast)
	bus.Read(foldMod, setupCol(foldMod, "addr_xb"), cellOf(xi, bn), notLast)
	bus.Read(foldMod, setupCol(foldMod, "addr_j"), cellOf(j...), notLast)

	c := newCols(n)
	c.declare("active", "last", "addr_p", "addr_q", "addr_al", "addr_xb", "addr_j", "xi", "bn")
	for _, x := range []string{"p", "q", "al", "j"} {
		c.declareLanes(x, 6)
	}
	row := 0
	for _, ch := range m.folds {
		for _, r := range ch {
			c.set("active", row, 1)
			c.set("addr_p", row, uint64(r.p))
			c.set("addr_q", row, uint64(r.q))
			c.setE6("p", row, m.e6(r.p))
			c.setE6("q", row, m.e6(r.q))
			if r.alpha < 0 {
				c.set("last", row, 1)
				row++
				continue
			}
			c.set("addr_al", row, uint64(r.alpha))
			c.set("addr_xb", row, uint64(r.xb))
			c.set("addr_j", row, uint64(r.inj))
			c.setE6("al", row, m.e6(r.alpha))
			c.setE6("j", row, m.e6(r.inj))
			c.setElem("xi", row, m.cells[r.xb][0])
			c.setElem("bn", row, m.cells[r.xb][1])
			row++
		}
	}
	c.store(t, foldMod)
	return nil
}
