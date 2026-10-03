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
