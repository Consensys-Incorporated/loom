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
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/internal/hash"
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

func newPerm() *poseidon2.Permutation { return hash.Poseidon2SpongePermutation() }

// Const returns the address of a constant cell of value v, written by the
// const chip (its values are setup columns). Constants are shared.
func (m *Machine) Const(v Cell) int {
	if a, ok := m.consts[v]; ok {
		return a
	}
	if m.consts == nil {
		m.consts, m.constVal = map[Cell]int{}, map[int]Cell{}
	}
	a := m.alloc()
	m.consts[v] = a
	m.constVal[a] = v
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
func (m *Machine) wr() slot         { return slot{m.alloc(), roleWrite} }

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

// ── sponge ───────────────────────────────────────────────────────────────────

// spongeDigest hashes a sponge's data with loom's overwrite-mode Poseidon2
// sponge: the trailing lanes of a partial block keep the previous state.
func spongeDigest(r *Run, s spongeInst) (Cell, error) {
	var state [width]koalabear.Element
	perm := newPerm()
	for blk := range len(s.data) / 2 {
		lo, hi := r.values[s.data[2*blk]], r.values[s.data[2*blk+1]]
		for j := range rate {
			if blk*rate+j < s.length {
				if j < CellWidth {
					state[j] = lo[j]
				} else {
					state[j] = hi[j-CellWidth]
				}
			}
		}
		if err := perm.Permutation(state[:]); err != nil {
			return Cell{}, err
		}
	}
	var d Cell
	copy(d[:], state[:digest])
	return d, nil
}

// ── Merkle paths ─────────────────────────────────────────────────────────────

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
// of cells, zero padded to whole sponge blocks and written by the witness
// chip, checks every item against its window of the stream, and returns the
// stream cells and its length in elements. Hashing the stream with Sponge
// hashes the items.
func (m *Machine) Pack(items, kinds []int) ([]int, int) {
	if len(items) != len(kinds) {
		panic(fmt.Sprintf("Pack: %d items, %d kinds", len(items), len(kinds)))
	}
	length := 0
	for _, k := range kinds {
		checkKind(k)
		length += k
	}
	stream := make([]int, streamCells(length))
	for i := range stream {
		stream[i] = m.alloc()
	}
	m.packs = append(m.packs, packInst{items: items, kinds: kinds, stream: stream})
	m.record(instrPack, len(m.packs)-1)
	g := 0
	for i, it := range items {
		m.Window(stream, g, kinds[i], it)
		g += kinds[i]
	}
	return stream, length
}

func (m *Machine) execPack(p packInst, r *Run) {
	var xs []koalabear.Element
	for i, it := range p.items {
		xs = append(xs, r.values[it][:p.kinds[i]]...)
	}
	for c, v := range PackElements(xs) {
		r.values[p.stream[c]] = v
	}
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
	var out Bits
	for range n {
		out.Shr = append(out.Shr, m.alloc())
		out.Bit = append(out.Bit, m.alloc())
	}
	m.bits = append(m.bits, bitsInst{v: v, n: n, out: out})
	m.record(instrBits, len(m.bits)-1)
	return out
}

func (m *Machine) execBits(b bitsInst, r *Run) {
	x := r.values[b.v][0].Uint64()
	low := x & (1<<b.n - 1)
	for i := range b.n {
		r.values[b.out.Shr[i]] = ScalarCell(koalabear.NewElement(low >> i))
		r.values[b.out.Bit[i]] = ScalarCell(koalabear.NewElement(x >> i & 1))
	}
}

// ── E6 arithmetic ────────────────────────────────────────────────────────────

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

// e6Op is one E6 instruction: its kind, operands and rows.
type e6Op struct {
	kind       int
	args       []int // operand addresses
	out        int   // the written cell, or -1
	rows, nrow int   // first row in e6Rows, number of rows
}

const (
	opMul = iota
	opAdd
	opSub
	opDiv
	opEq
	opHorner // args = y, coeffs...
)

func (m *Machine) e6Op(kind int, args []int, out int, rows ...e6Row) int {
	m.e6Ops = append(m.e6Ops, e6Op{kind: kind, args: args, out: out, rows: len(m.e6Rows), nrow: len(rows)})
	m.e6Rows = append(m.e6Rows, rows...)
	m.record(instrE6, len(m.e6Ops)-1)
	return out
}

// Mul returns a·b.
func (m *Machine) Mul(a, b int) int {
	r := e6Row{mul: 1, a: m.rd(a), b: m.rd(b), o: m.wr()}
	return m.e6Op(opMul, []int{a, b}, r.o.addr, r)
}

// Add returns a + b.
func (m *Machine) Add(a, b int) int {
	r := e6Row{add: 1, bs: 1, a: m.rd(a), b: m.rd(b), o: m.wr()}
	return m.e6Op(opAdd, []int{a, b}, r.o.addr, r)
}

// Sub returns a − b.
func (m *Machine) Sub(a, b int) int {
	r := e6Row{add: 1, bs: -1, a: m.rd(a), b: m.rd(b), o: m.wr()}
	return m.e6Op(opSub, []int{a, b}, r.o.addr, r)
}

// Div returns n/d, checked as d·q = n. Executing it fails if d is zero.
func (m *Machine) Div(n, d int) int {
	r := e6Row{mul: 1, a: m.rd(d), b: m.wr(), o: m.rd(n)}
	return m.e6Op(opDiv, []int{n, d}, r.b.addr, r)
}

// AssertEq checks that the cells a and b hold the same E6 value.
func (m *Machine) AssertEq(a, b int) {
	m.e6Op(opEq, []int{a, b}, -1, e6Row{add: 1, a: m.rd(a), o: m.rd(b)})
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
	return m.e6Op(opHorner, append([]int{y}, coeffs...), rows[len(rows)-1].o.addr, rows...)
}

func (m *Machine) execE6(op e6Op, r *Run) error {
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
