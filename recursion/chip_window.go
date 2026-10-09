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

type packInst struct {
	items, kinds []int
	stream       []int // the stream cells, written by the witness chip
}

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
	m.hints = append(m.hints, stream...)
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

type lanesInst struct {
	src, off, kind, out int
}

// Lanes returns a cell holding lanes off..off+kind−1 of the cell src, in its
// lanes 0..kind−1 and zero elsewhere: for instance the E6 value of a
// challenge digest (Lanes(d, 0, KindE6)), or one of its lanes as a scalar.
// The witness chip writes it, and a window checks it against src.
func (m *Machine) Lanes(src, off, kind int) int {
	checkKind(kind)
	if off < 0 || off+kind > CellWidth {
		panic(fmt.Sprintf("Lanes: lanes %d..%d out of a cell", off, off+kind-1))
	}
	out := m.alloc()
	m.hints = append(m.hints, out)
	m.lanes = append(m.lanes, lanesInst{src, off, kind, out})
	m.record(instrLanes, len(m.lanes)-1)
	m.Window([]int{src}, off, kind, out)
	return out
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
	if k < 1 || k > CellWidth {
		panic(fmt.Sprintf("item kind %d", k))
	}
}

// windowChip: one row per item of a packed stream.
//
// Columns: p0..7, q0..7 (two consecutive stream cells, the window W = p‖q),
// i0..7 (the item). Setup: active, addr_p, addr_q, sel_q (q is read), addr_i,
// off0..7 (one-hot offset of the item in p), and len1..7 (len_k = 1 when the
// item has more than k lanes). For each lane k of the item,
//
//	len_k·(i_k − Σ_o off_o·W_{o+k}) = 0,
//
// with len_0 = 1. The item's other lanes are left to its readers: their
// tuples fix them to zero, or they do not use them.
type windowChip struct{ m *Machine }

func (c windowChip) name() string { return windowMod }

func (c windowChip) rows() int { return len(c.m.windows) }

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
		mask := one()
		if k > 0 {
			mask = setupCol(windowMod, fmt.Sprintf("len%d", k))
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
	cs.declare("active", "addr_p", "addr_q", "sel_q", "addr_i")
	cs.declareLanes("off", CellWidth)
	for k := 1; k < CellWidth; k++ {
		cs.declare(fmt.Sprintf("len%d", k))
	}
	for row, w := range c.m.windows {
		cs.set("active", row, 1)
		cs.set("addr_p", row, uint64(w.p))
		if w.q >= 0 {
			cs.set("addr_q", row, uint64(w.q))
			cs.set("sel_q", row, 1)
		}
		cs.set("addr_i", row, uint64(w.item))
		cs.set(fmt.Sprintf("off%d", w.off), row, 1)
		for k := 1; k < w.kind; k++ {
			cs.set(fmt.Sprintf("len%d", k), row, 1)
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
