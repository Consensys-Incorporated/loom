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
)

// e6Row is one row of the E6 chip:
//
//	o = mul·(a·b) + add·a + bs·b + hor·(o[−1]·a)
//
// Unused operands are zero; o is computed by the formula, so on a row whose o
// is read the chip checks the read value.
type e6Row struct {
	mul, add, bs, hor int64
	a, b, o           slot
}

// e6Inst is one E6 instruction: its kind, operands, written cell and rows
// (one, or one per coefficient for Horner).
type e6Inst struct {
	kind int
	args []int // operand addresses
	out  int   // the written cell, or -1
	rows []e6Row
}

const (
	opMul = iota
	opAdd
	opSub
	opDiv
	opEq
	opHorner // args = y, coeffs...
)

func (m *Machine) addE6(kind int, args []int, out int, rows ...e6Row) int {
	m.e6Insts = append(m.e6Insts, e6Inst{kind: kind, args: args, out: out, rows: rows})
	m.record(instrE6, len(m.e6Insts)-1)
	return out
}

// Mul returns a·b.
func (m *Machine) Mul(a, b int) int {
	r := e6Row{mul: 1, a: m.rd(a), b: m.rd(b), o: m.wr()}
	return m.addE6(opMul, []int{a, b}, r.o.addr, r)
}

// Add returns a + b.
func (m *Machine) Add(a, b int) int {
	r := e6Row{add: 1, bs: 1, a: m.rd(a), b: m.rd(b), o: m.wr()}
	return m.addE6(opAdd, []int{a, b}, r.o.addr, r)
}

// Sub returns a − b.
func (m *Machine) Sub(a, b int) int {
	r := e6Row{add: 1, bs: -1, a: m.rd(a), b: m.rd(b), o: m.wr()}
	return m.addE6(opSub, []int{a, b}, r.o.addr, r)
}

// Div returns n/d, checked as d·q = n. Executing it fails if d is zero.
func (m *Machine) Div(n, d int) int {
	r := e6Row{mul: 1, a: m.rd(d), b: m.wr(), o: m.rd(n)}
	return m.addE6(opDiv, []int{n, d}, r.b.addr, r)
}

// AssertEq checks that the cells a and b hold the same E6 value.
func (m *Machine) AssertEq(a, b int) {
	m.addE6(opEq, []int{a, b}, -1, e6Row{add: 1, a: m.rd(a), o: m.rd(b)})
}

// Horner returns Σ_i coeffs[i]·y^(len−1−i), one row per coefficient: the
// first row is o = coeffs[0], the next ones o = o[−1]·y + coeffs[i].
func (m *Machine) Horner(y int, coeffs []int) int {
	if len(coeffs) == 0 {
		panic("Horner: no coefficients")
	}
	rows := make([]e6Row, len(coeffs))
	for i, c := range coeffs {
		rows[i] = e6Row{bs: 1, b: m.rd(c)}
		if i > 0 {
			rows[i].hor, rows[i].a = 1, m.rd(y)
		}
	}
	rows[len(rows)-1].o = m.wr()
	return m.addE6(opHorner, append([]int{y}, coeffs...), rows[len(rows)-1].o.addr, rows...)
}

// PowBits returns Π_i (bits[i] ? gs[i] : 1), for scalar bit cells and
// constants gs: an exponentiation by bits, such as g^bitrev(index).
func (m *Machine) PowBits(bits []int, gs []koalabear.Element) int {
	if len(bits) != len(gs) {
		panic(fmt.Sprintf("PowBits: %d bits, %d constants", len(bits), len(gs)))
	}
	one := koalabear.One()
	acc := m.Const(ScalarCell(one))
	for i, b := range bits {
		var gm1 koalabear.Element
		gm1.Sub(&gs[i], &one)
		f := m.Add(m.Mul(b, m.Const(ScalarCell(gm1))), m.Const(ScalarCell(one)))
		acc = m.Mul(acc, f)
	}
	return acc
}

func (m *Machine) execE6(op e6Inst, r *Run) error {
	v := func(i int) ext.E6 { return CellE6(r.values[op.args[i]]) }
	var z ext.E6
	switch op.kind {
	case opMul:
		x, y := v(0), v(1)
		z.Mul(&x, &y)
	case opAdd:
		x, y := v(0), v(1)
		z.Add(&x, &y)
	case opSub:
		x, y := v(0), v(1)
		z.Sub(&x, &y)
	case opDiv:
		n, d := v(0), v(1)
		if d.IsZero() {
			return fmt.Errorf("Div: zero divisor (cell %d)", op.args[1])
		}
		z.Inverse(&d)
		z.Mul(&z, &n)
	case opEq:
		return nil
	case opHorner:
		y := v(0)
		for i := 1; i < len(op.args); i++ {
			c := v(i)
			z.Mul(&z, &y)
			z.Add(&z, &c)
		}
	}
	r.values[op.out] = E6Cell(z)
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

func (c e6Chip) rows() int {
	n := 0
	for _, in := range c.m.e6Insts {
		n += len(in.rows)
	}
	return n
}

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
	row := -1
	for _, in := range c.m.e6Insts {
		for _, r := range in.rows {
			row++
			c.setupRow(cs, row, r)
		}
	}
}

func (c e6Chip) setupRow(cs *cols, row int, r e6Row) {
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

// trace reads a and b from their cells (zero when unused) and computes o by
// the row's formula: on a row whose o is read, the bus checks it.
func (c e6Chip) trace(cs *cols, r *Run) error {
	for _, x := range []string{"a", "b", "o"} {
		cs.declareLanes(x, 6)
	}
	var prev ext.E6
	row := -1
	for _, in := range c.m.e6Insts {
		for _, er := range in.rows {
			row++
			prev = traceE6Row(cs, row, er, prev, r)
		}
	}
	return nil
}

// traceE6Row fills one row and returns its o, the next row's o[−1].
func traceE6Row(cs *cols, row int, er e6Row, prev ext.E6, r *Run) ext.E6 {
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
	return o
}
