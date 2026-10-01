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
)

// Cell layouts: an E6 value in lanes 0..5 (B0.A0, B0.A1, B1.A0, B1.A1, B2.A0,
// B2.A1), a scalar in lane 0. The other lanes are zero, which every reader
// enforces through the constants of its tuple. A scalar cell is also the E6
// cell of its base-field embedding.

// E6Cell returns the cell of x.
func E6Cell(x ext.E6) Cell {
	return Cell{x.B0.A0, x.B0.A1, x.B1.A0, x.B1.A1, x.B2.A0, x.B2.A1}
}

// CellE6 returns the E6 value of a cell (lanes 0..5).
func CellE6(c Cell) ext.E6 {
	var x ext.E6
	x.B0.A0, x.B0.A1, x.B1.A0, x.B1.A1, x.B2.A0, x.B2.A1 = c[0], c[1], c[2], c[3], c[4], c[5]
	return x
}

// ScalarCell returns the cell of v.
func ScalarCell(v koalabear.Element) Cell { return Cell{v} }

// Value returns the value of the cell at addr.
func (m *Machine) Value(addr int) Cell { return m.cells[addr] }

// Const returns the address of a constant cell of value v, written by the
// const chip (its values are setup columns). Constants are shared.
func (m *Machine) Const(v Cell) int {
	if a, ok := m.consts[v]; ok {
		return a
	}
	if m.consts == nil {
		m.consts = map[Cell]int{}
	}
	a := m.alloc(v)
	m.consts[v] = a
	m.constList = append(m.constList, a)
	return a
}

// ── memory slots ─────────────────────────────────────────────────────────────

const (
	roleNone = iota
	roleRead
	roleWrite
)

// slot is one memory access of a chip row.
type slot struct {
	addr, role int
}

func (m *Machine) rd(addr int) slot { m.read(addr); return slot{addr, roleRead} }
func (m *Machine) wr(v Cell) slot   { return slot{m.alloc(v), roleWrite} }

// mult is the signed bus multiplicity of s: −1 for a read, the read count for
// a write.
func (m *Machine) mult(s slot) int64 {
	switch s.role {
	case roleRead:
		return -1
	case roleWrite:
		return int64(m.reads[s.addr])
	}
	return 0
}

// ── windows (pack / unpack) ──────────────────────────────────────────────────

// Item lengths of the window chip.
const (
	KindScalar = 1
	KindE6     = 6
	KindDigest = 8
)

type windowInst struct {
	p, q, item int // q < 0 when the item fits in p
	off, kind  int
}

// Pack lays the items (cells of the given kinds) out contiguously as a stream
// of witness cells, zero padded to whole sponge blocks, checks every item
// against its window of the stream, and returns the stream cells and its
// length in elements. Hashing the stream with Sponge hashes the items.
func (m *Machine) Pack(items, kinds []int) ([]int, int) {
	if len(items) != len(kinds) {
		panic(fmt.Sprintf("Pack: %d items, %d kinds", len(items), len(kinds)))
	}
	var xs []koalabear.Element
	for i, it := range items {
		checkKind(kinds[i])
		xs = append(xs, m.cells[it][:kinds[i]]...)
	}
	stream := m.WitnessStream(xs)
	g := 0
	for i, it := range items {
		m.Window(stream, g, kinds[i], it)
		g += kinds[i]
	}
	return stream, len(xs)
}

// Window checks that item is the kind elements of the stream starting at
// element offset g.
func (m *Machine) Window(stream []int, g, kind, item int) {
	checkKind(kind)
	c, off := g/CellWidth, g%CellWidth
	w := windowInst{p: stream[c], q: -1, item: item, off: off, kind: kind}
	m.read(w.p)
	if off+kind > CellWidth {
		w.q = stream[c+1]
		m.read(w.q)
	}
	m.read(item)
	m.windows = append(m.windows, w)
}

func checkKind(k int) {
	if k != KindScalar && k != KindE6 && k != KindDigest {
		panic(fmt.Sprintf("item kind %d", k))
	}
}

// ── bits ─────────────────────────────────────────────────────────────────────

// BitsWidth is the number of bits of a canonical KoalaBear element, and the
// number of rows of a decomposition.
const BitsWidth = 31

// Bits is the decomposition of a scalar v: for i < n, Shr[i] is the scalar
// cell (v mod 2^n) >> i and Bit[i] the scalar cell of bit i of v.
type Bits struct {
	Shr, Bit []int
}

type bitsInst struct {
	v, n int
	out  Bits
}

// Bits decomposes the scalar cell v canonically (the bits are those of the
// representative in [0, p)) and returns its low n bits, n < BitsWidth.
func (m *Machine) Bits(v int, n int) Bits {
	if n < 1 || n >= BitsWidth {
		panic(fmt.Sprintf("Bits: n = %d", n))
	}
	m.read(v)
	x := m.cells[v][0].Uint64()
	low := x & (1<<n - 1)
	var out Bits
	for i := range n {
		out.Shr = append(out.Shr, m.alloc(ScalarCell(koalabear.NewElement(low>>i))))
		out.Bit = append(out.Bit, m.alloc(ScalarCell(koalabear.NewElement(x>>i&1))))
	}
	m.bits = append(m.bits, bitsInst{v: v, n: n, out: out})
	return out
}

// ── E6 arithmetic ────────────────────────────────────────────────────────────

// e6Row is one row of the E6 chip:
//
//	o = mul·(a·b) + add·a + bs·b + hor·(o[−1]·a)
type e6Row struct {
	mul, add, bs, hor int64
	a, b, o           slot
	va, vb, vo        ext.E6
}

func (m *Machine) e6(a int) ext.E6 { return CellE6(m.cells[a]) }

// Mul returns a·b.
func (m *Machine) Mul(a, b int) int {
	x, y := m.e6(a), m.e6(b)
	var z ext.E6
	z.Mul(&x, &y)
	r := e6Row{mul: 1, a: m.rd(a), b: m.rd(b), o: m.wr(E6Cell(z)), va: x, vb: y, vo: z}
	m.e6Rows = append(m.e6Rows, r)
	return r.o.addr
}

// Add returns a + b.
func (m *Machine) Add(a, b int) int { return m.lin(a, b, 1) }

// Sub returns a − b.
func (m *Machine) Sub(a, b int) int { return m.lin(a, b, -1) }

func (m *Machine) lin(a, b int, sign int64) int {
	x, y := m.e6(a), m.e6(b)
	var z ext.E6
	if sign > 0 {
		z.Add(&x, &y)
	} else {
		z.Sub(&x, &y)
	}
	r := e6Row{add: 1, bs: sign, a: m.rd(a), b: m.rd(b), o: m.wr(E6Cell(z)), va: x, vb: y, vo: z}
	m.e6Rows = append(m.e6Rows, r)
	return r.o.addr
}

// Div returns n/d, checked as d·q = n. d must be nonzero.
func (m *Machine) Div(n, d int) int {
	x, y := m.e6(d), m.e6(n)
	var q ext.E6
	q.Inverse(&x)
	q.Mul(&q, &y)
	r := e6Row{mul: 1, a: m.rd(d), b: m.wr(E6Cell(q)), o: m.rd(n), va: x, vb: q, vo: y}
	m.e6Rows = append(m.e6Rows, r)
	return r.b.addr
}

// AssertEq checks that the cells a and b hold the same E6 value.
func (m *Machine) AssertEq(a, b int) {
	x := m.e6(a)
	r := e6Row{add: 1, a: m.rd(a), o: m.rd(b), va: x, vo: m.e6(b)}
	m.e6Rows = append(m.e6Rows, r)
}

// Horner returns Σ_i coeffs[i]·y^(len−1−i), one row per coefficient: the
// first row is o = coeffs[0], the next ones o = o[−1]·y + coeffs[i].
func (m *Machine) Horner(y int, coeffs []int) int {
	if len(coeffs) == 0 {
		panic("Horner: no coefficients")
	}
	vy := m.e6(y)
	var acc ext.E6
	for i, c := range coeffs {
		vc := m.e6(c)
		r := e6Row{bs: 1, b: m.rd(c), vb: vc}
		if i == 0 {
			acc = vc
		} else {
			r.hor, r.a, r.va = 1, m.rd(y), vy
			acc.Mul(&acc, &vy)
			acc.Add(&acc, &vc)
		}
		r.vo = acc
		if i == len(coeffs)-1 {
			r.o = m.wr(E6Cell(acc))
		}
		m.e6Rows = append(m.e6Rows, r)
	}
	return m.e6Rows[len(m.e6Rows)-1].o.addr
}

// ── FRI fold ─────────────────────────────────────────────────────────────────

// FoldRound is one round of a FRI query: the opened pair (P, Q) = (f(x),
// f(−x)) of the round's layer, its fold challenge Alpha, the cell XB = [x⁻¹,
// b] written by the layer's Merkle path (b selects P or Q in the next layer),
// and Inj, the term added before the next layer (zero if none).
type FoldRound struct {
	P, Q, Alpha, XB, Inj int
}

type foldRow struct {
	p, q, alpha, xb, inj int // xb, alpha, inj < 0 on the terminal row
}

// FoldChain checks a FRI query: each round folds its pair,
//
//	fold = (P + Q)/2 + α·(P − Q)·x⁻¹/2,
//
// and fold + Inj must be P or Q of the next round (per b), or final after the
// last round.
func (m *Machine) FoldChain(rounds []FoldRound, final int) {
	var chain []foldRow
	for _, r := range rounds {
		for _, a := range []int{r.P, r.Q, r.Alpha, r.XB, r.Inj} {
			m.read(a)
		}
		chain = append(chain, foldRow{r.P, r.Q, r.Alpha, r.XB, r.Inj})
	}
	// The terminal row holds final in both P and Q, so that the last round's
	// selection bit does not matter.
	m.read(final)
	m.read(final)
	chain = append(chain, foldRow{p: final, q: final, alpha: -1, xb: -1, inj: -1})
	m.folds = append(m.folds, chain)
}
