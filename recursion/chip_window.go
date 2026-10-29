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
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

// Setup columns of the window chip.
const (
	windowActive = "active"
	windowAddrP  = "addr_p"
	windowAddrQ  = "addr_q"
	windowSelQ   = "sel_q"
	windowAddrI  = "addr_i"
	windowMultI  = "m_i" // −1 for a Pack item (read), the read count for a Lanes output (write)
	windowOff    = "off" // lanes
	windowLen    = "len" // lanes
)

// Witness columns of the window chip.
const (
	windowP = "p" // lanes
	windowQ = "q" // lanes
	windowI = "i" // lanes
)

type packInst struct {
	prefix       []koalabear.Element // constant elements at the head of the stream
	items, kinds []int
	stream       []int // the stream cells, written by the stream chip
}

type windowInst struct {
	p, q      int  // q < 0 when the item fits in p
	item      slot // read (a Pack item) or written (a Lanes output)
	off, kind int
}

// Pack lays the items (cells of the given kinds) out contiguously as a stream
// of cells, zero padded to whole sponge blocks and written by the witness
// chip, checks every item against its window of the stream, and returns the
// stream cells and its length in elements. Hashing the stream with Sponge
// hashes the items. An item's kind must cover its cell's kind (KindE6 for an
// E6 cell, not KindScalar): its window reads it with zero lanes beyond the
// item's kind, which are not hashed, so proving fails otherwise.
func (m *Machine) Pack(items, kinds []int) ([]int, int) {
	return m.PackPrefixed(nil, items, kinds)
}

// PackPrefixed is Pack with a run of constant elements at the head of the
// stream. A constant needs no cell and no window row: the stream chip holds
// it in setup and constrains the stream's first cell to it, so a leaf's tag
// and widths cost nothing per leaf. The prefix must fit one cell.
func (m *Machine) PackPrefixed(prefix []koalabear.Element, items, kinds []int) ([]int, int) {
	if len(items) != len(kinds) {
		panic(fmt.Sprintf("Pack: %d items, %d kinds", len(items), len(kinds)))
	}
	if len(prefix) > CellWidth {
		panic(fmt.Sprintf("Pack: a prefix of %d elements", len(prefix)))
	}
	length := len(prefix)
	for _, k := range kinds {
		checkKind(k)
		length += k
	}
	stream := make([]int, streamCells(length))
	for i := range stream {
		stream[i] = m.hint(KindDigest)
	}
	m.packs = append(m.packs, packInst{prefix: prefix, items: items, kinds: kinds, stream: stream})
	m.record(instrPack, len(m.packs)-1)
	g := len(prefix)
	for i, it := range items {
		m.window(stream, g, kinds[i], m.rd(it))
		g += kinds[i]
	}
	return stream, length
}

// packPrefix is the longest constant prefix of any stream, 0 if none: the
// number of lanes the stream chip pins.
func (m *Machine) packPrefix() int {
	n := 0
	for _, p := range m.packs {
		n = max(n, len(p.prefix))
	}
	return n
}

func (m *Machine) execPack(p packInst, r *Run) {
	xs := append([]koalabear.Element(nil), p.prefix...)
	for i, it := range p.items {
		xs = append(xs, r.values[it][:p.kinds[i]]...)
	}
	for c, v := range PackElements(xs) {
		r.values[p.stream[c]] = v
	}
}

type lanesInst struct {
	src, off, kind, out int
}

// Lanes returns a cell of the given kind (scalar or E6) holding lanes
// off..off+kind−1 of the cell src, in its lanes 0..kind−1 and zero elsewhere:
// for instance the E6 value of a challenge digest (Lanes(d, 0, KindE6)), or
// one of its lanes as a scalar. A window row reads src and writes it, zero
// beyond its kind.
func (m *Machine) Lanes(src, off, kind int) int {
	checkCellKind(kind)
	if off < 0 || off+kind > CellWidth {
		panic(fmt.Sprintf("Lanes: lanes %d..%d out of a cell", off, off+kind-1))
	}
	out := m.wr()
	m.lanes = append(m.lanes, lanesInst{src, off, kind, out.addr})
	m.record(instrLanes, len(m.lanes)-1)
	m.window([]int{src}, off, kind, out)
	return out.addr
}

// window adds a window row: the item (read, or written) is the kind elements
// of the stream starting at element offset g, and zero beyond.
func (m *Machine) window(stream []int, g, kind int, item slot) {
	checkKind(kind)
	c, off := g/CellWidth, g%CellWidth
	w := windowInst{p: stream[c], q: -1, item: item, off: off, kind: kind}
	m.read(w.p)
	if off+kind > CellWidth {
		w.q = stream[c+1]
		m.read(w.q)
	}
	m.windows = append(m.windows, w)
}

func checkKind(k int) {
	if k < 1 || k > CellWidth {
		panic(fmt.Sprintf("item kind %d", k))
	}
}

// windowChip: one row per item of a packed stream (read), and per Lanes
// output (written).
//
// Columns: p0..7, q0..7 (two consecutive stream cells, the window W = p‖q),
// i0..7 (the item). Setup: active, addr_p, addr_q, sel_q (q is read), addr_i,
// m_i (the item's signed multiplicity: −1 for a read, the read count for a
// write), off0..7 (one-hot offset of the item in p), and len1..7 (len_k = 1
// when the item has more than k lanes). For each lane k of the item,
//
//	i_k = len_k·Σ_o off_o·W_{o+k},
//
// with len_0 = 1: the item's lanes beyond its kind are zero, so a Lanes output
// is typed by its row, and a Pack item must have no lane beyond the kind it is
// packed with.
type windowChip struct{ m *Machine }

func (c windowChip) name() string { return windowMod }

func (c windowChip) rows() int { return len(c.m.windows) }

func (c windowChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[windowMod]
	active := setupCol(windowMod, windowActive)
	bus.Read(windowMod, setupCol(windowMod, windowAddrP), cellCols(windowMod, windowP, 0), active)
	bus.Read(windowMod, setupCol(windowMod, windowAddrQ), cellCols(windowMod, windowQ, 0), setupCol(windowMod, windowSelQ))
	bus.Write(windowMod, setupCol(windowMod, windowAddrI), cellCols(windowMod, windowI, 0), setupCol(windowMod, windowMultI))

	window := func(j int) expr.Expr {
		if j < CellWidth {
			return col(windowMod, laneName(windowP, j))
		}
		return col(windowMod, laneName(windowQ, j-CellWidth))
	}
	for k := range CellWidth {
		mask := one()
		if k > 0 {
			mask = setupCol(windowMod, laneName(windowLen, k))
		}
		var sum expr.Expr = zero()
		for o := range CellWidth {
			sum = sum.Add(setupCol(windowMod, laneName(windowOff, o)).Mul(window(o + k)))
		}
		mm.AssertZero(col(windowMod, laneName(windowI, k)).Sub(mask.Mul(sum)))
	}
	return nil
}

func (c windowChip) setup(cs *cols) {
	cs.declare(windowActive, windowAddrP, windowAddrQ, windowSelQ, windowAddrI, windowMultI)
	cs.declareLanes(windowOff, CellWidth)
	for k := 1; k < CellWidth; k++ {
		cs.declare(laneName(windowLen, k))
	}
	for row, w := range c.m.windows {
		cs.set(windowActive, row, 1)
		cs.set(windowAddrP, row, uint64(w.p))
		if w.q >= 0 {
			cs.set(windowAddrQ, row, uint64(w.q))
			cs.set(windowSelQ, row, 1)
		}
		cs.set(windowAddrI, row, uint64(w.item.addr))
		cs.setInt(windowMultI, row, c.m.mult(w.item))
		cs.set(laneName(windowOff, w.off), row, 1)
		for k := 1; k < w.kind; k++ {
			cs.set(laneName(windowLen, k), row, 1)
		}
	}
}

func (c windowChip) trace(cs *cols, r *Run) error {
	cs.declareLanes(windowP, CellWidth)
	cs.declareLanes(windowQ, CellWidth)
	cs.declareLanes(windowI, CellWidth)
	for row, w := range c.m.windows {
		cs.setCell(windowP, row, r.values[w.p])
		if w.q >= 0 {
			cs.setCell(windowQ, row, r.values[w.q])
		}
		cs.setCell(windowI, row, r.values[w.item.addr])
	}
	return nil
}
