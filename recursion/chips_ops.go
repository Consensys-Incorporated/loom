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
)

// A chip whose instruction list is empty adds no module.

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
type constChip struct{ m *Machine }

func (c constChip) name() string { return constMod }
func (c constChip) rows() int    { return len(c.m.constList) }

func (c constChip) define(b *board.Builder, bus *Bus) error {
	bus.Write(constMod, setupCol(constMod, "addr"), setupCellCols(constMod, "v"), setupCol(constMod, "mult"))
	return nil
}

func (c constChip) setup(cs *cols) {
	cs.declare("addr", "mult")
	cs.declareLanes("v", CellWidth)
	for row, a := range c.m.constList {
		cs.set("addr", row, uint64(a))
		cs.set("mult", row, uint64(c.m.reads[a]))
		cs.setCell("v", row, c.m.constVal[a])
	}
}

func (c constChip) trace(*cols, *Run) error { return nil }

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
type windowChip struct{ m *Machine }

func (c windowChip) name() string { return windowMod }
func (c windowChip) rows() int    { return len(c.m.windows) }

func (c windowChip) define(b *board.Builder, bus *Bus) error {
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
	return nil
}

func (c windowChip) setup(cs *cols) {
	cs.declare("active", "addr_p", "addr_q", "sel_q", "addr_i", "k6", "k8")
	cs.declareLanes("off", CellWidth)
	for row, w := range c.m.windows {
		cs.set("active", row, 1)
		cs.set("addr_p", row, uint64(w.p))
		if w.q >= 0 {
			cs.set("addr_q", row, uint64(w.q))
			cs.set("sel_q", row, 1)
		}
		cs.set("addr_i", row, uint64(w.item))
		cs.set(fmt.Sprintf("off%d", w.off), row, 1)
		if w.kind >= KindE6 {
			cs.set("k6", row, 1)
		}
		if w.kind == KindDigest {
			cs.set("k8", row, 1)
		}
	}
}

func (c windowChip) trace(cs *cols, r *Run) error {
	cs.declareLanes("p", CellWidth)
	cs.declareLanes("q", CellWidth)
	cs.declareLanes("i", CellWidth)
	for row, w := range c.m.windows {
		cs.setCell("p", row, r.values[w.p])
		if w.q >= 0 {
			cs.setCell("q", row, r.values[w.q])
		}
		cs.setCell("i", row, r.values[w.item])
	}
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
type bitsChip struct{ m *Machine }

func (c bitsChip) name() string { return bitsMod }
func (c bitsChip) rows() int    { return BitsWidth * len(c.m.bits) }

func (c bitsChip) define(b *board.Builder, bus *Bus) error {
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
	return nil
}

func (c bitsChip) setup(cs *cols) {
	cs.declare("first", "last", "active", "pow", "inlow", "chk", "addr_v", "r_addr", "r_mult", "b_addr", "b_mult")
	for k, inst := range c.m.bits {
		for i := range BitsWidth {
			row := k*BitsWidth + i
			cs.set("active", row, 1)
			cs.set("pow", row, 1<<i)
			switch i {
			case 0:
				cs.set("first", row, 1)
				cs.set("addr_v", row, uint64(inst.v))
			case 24:
				cs.set("chk", row, 1)
			case BitsWidth - 1:
				cs.set("last", row, 1)
			}
			if i < inst.n {
				cs.set("inlow", row, 1)
				cs.set("r_addr", row, uint64(inst.out.Shr[i]))
				cs.set("r_mult", row, uint64(c.m.reads[inst.out.Shr[i]]))
				cs.set("b_addr", row, uint64(inst.out.Bit[i]))
				cs.set("b_mult", row, uint64(c.m.reads[inst.out.Bit[i]]))
			}
		}
	}
}

func (c bitsChip) trace(cs *cols, r *Run) error {
	cs.declare("b", "w", "r", "v", "inv")
	for k, inst := range c.m.bits {
		x := r.values[inst.v][0].Uint64()
		low := x & (1<<inst.n - 1)
		for i := range BitsWidth {
			row := k*BitsWidth + i
			cs.set("b", row, x>>i&1)
			cs.set("w", row, x&(1<<i-1))
			cs.set("v", row, x)
			if i == 24 {
				var zv koalabear.Element
				zv.SetUint64(koalaHigh - x>>24)
				if !zv.IsZero() {
					zv.Inverse(&zv)
				}
				cs.setElem("inv", row, zv)
			}
			if i < inst.n {
				cs.set("r", row, low>>i)
			}
		}
	}
	return nil
}

// e6Chip: one E6 operation per row,
//
//	o = mul·(a·b) + add·a + bs·b + hor·(o[−1]·a),
//
// over the columns a0..5, b0..5, o0..5. Setup: mul, add, bs (−1, 0 or 1), hor,
// and per operand x ∈ {a, b, o} addr_x and the signed multiplicity m_x (−1
// read, the read count for a write, 0 unused).
type e6Chip struct{ m *Machine }

func (c e6Chip) name() string { return e6Mod }
func (c e6Chip) rows() int    { return len(c.m.e6Rows) }

func (c e6Chip) define(b *board.Builder, bus *Bus) error {
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
	return nil
}

func (c e6Chip) setup(cs *cols) {
	cs.declare("mul", "add", "bs", "hor", "addr_a", "m_a", "addr_b", "m_b", "addr_o", "m_o")
	for row, r := range c.m.e6Rows {
		cs.setInt("mul", row, r.mul)
		cs.setInt("add", row, r.add)
		cs.setInt("bs", row, r.bs)
		cs.setInt("hor", row, r.hor)
		for _, op := range []struct {
			name string
			s    slot
		}{{"a", r.a}, {"b", r.b}, {"o", r.o}} {
			if op.s.role != roleNone {
				cs.set("addr_"+op.name, row, uint64(op.s.addr))
				cs.setInt("m_"+op.name, row, c.m.mult(op.s))
			}
		}
	}
}

// trace reads a and b from their cells (zero when unused) and computes o by
// the row's formula: on a row whose o is read, the bus checks it.
func (c e6Chip) trace(cs *cols, r *Run) error {
	for _, x := range []string{"a", "b", "o"} {
		cs.declareLanes(x, 6)
	}
	var prev ext.E6
	for row, er := range c.m.e6Rows {
		var a, b, o ext.E6
		if er.a.role != roleNone {
			a = CellE6(r.values[er.a.addr])
		}
		if er.b.role != roleNone {
			b = CellE6(r.values[er.b.addr])
		}
		var t ext.E6
		if er.mul != 0 {
			t.Mul(&a, &b)
			o.Add(&o, &t)
		}
		if er.add != 0 {
			o.Add(&o, &a)
		}
		switch er.bs {
		case 1:
			o.Add(&o, &b)
		case -1:
			o.Sub(&o, &b)
		}
		if er.hor != 0 {
			t.Mul(&prev, &a)
			o.Add(&o, &t)
		}
		cs.setE6("a", row, a)
		cs.setE6("b", row, b)
		cs.setE6("o", row, o)
		prev = o
	}
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
type foldChip struct{ m *Machine }

func (c foldChip) name() string { return foldMod }

func (c foldChip) rows() int {
	n := 0
	for _, ch := range c.m.folds {
		n += len(ch)
	}
	return n
}

func (c foldChip) define(b *board.Builder, bus *Bus) error {
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
	return nil
}

func (c foldChip) setup(cs *cols) {
	cs.declare("active", "last", "addr_p", "addr_q", "addr_al", "addr_xb", "addr_j")
	row := 0
	for _, ch := range c.m.folds {
		for _, r := range ch {
			cs.set("active", row, 1)
			cs.set("addr_p", row, uint64(r.p))
			cs.set("addr_q", row, uint64(r.q))
			if r.alpha < 0 {
				cs.set("last", row, 1)
			} else {
				cs.set("addr_al", row, uint64(r.alpha))
				cs.set("addr_xb", row, uint64(r.xb))
				cs.set("addr_j", row, uint64(r.inj))
			}
			row++
		}
	}
}

func (c foldChip) trace(cs *cols, r *Run) error {
	cs.declare("xi", "bn")
	for _, x := range []string{"p", "q", "al", "j"} {
		cs.declareLanes(x, 6)
	}
	row := 0
	for _, ch := range c.m.folds {
		for _, fr := range ch {
			cs.setE6("p", row, CellE6(r.values[fr.p]))
			cs.setE6("q", row, CellE6(r.values[fr.q]))
			if fr.alpha >= 0 {
				cs.setE6("al", row, CellE6(r.values[fr.alpha]))
				cs.setE6("j", row, CellE6(r.values[fr.inj]))
				cs.setElem("xi", row, r.values[fr.xb][0])
				cs.setElem("bn", row, r.values[fr.xb][1])
			}
			row++
		}
	}
	return nil
}
