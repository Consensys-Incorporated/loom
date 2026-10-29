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

	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

// Setup columns of the deep chip.
const (
	deepActive = "active"
	deepFirst  = "first"
	deepAct    = "act" // lanes
	deepSel    = "sel" // lanes
	deepAddrX  = "addr_x"
	deepAddrAl = "addr_al"
	deepAddrO  = "addr_o"
	deepMO     = "m_o"
	deepCont   = "cont"    // the segment continues from addr_in
	deepAddrIn = "addr_in" // the handed-over h, on a continuing segment's first row
)

// Witness columns of the deep chip.
const (
	deepX   = "x"   // lanes
	deepAl  = "al"  // lanes
	deepH   = "h"   // h<j>_0..5, the E6 h after lane j (deepHPrefix)
	deepHIn = "hin" // the E6 h entering the row
)

// DeepRow is one row of a DEEP Horner chain: the cell it reads and, as bit
// masks over its lanes, the lanes that take part (Act) and those whose value
// is added (Sel). A base row reads up to CellWidth base values; an Ext row
// reads an E6 value and has a single step (Act = 1).
type DeepRow struct {
	Cell     int
	Ext      bool
	Act, Sel uint8
}

// deepSeg is a maximal run of rows of one kind within a chain. Base and Ext
// rows live on different modules (see deepChip), so a chain is cut at every
// change of kind and the running h is handed over through a cell: seg.in is
// the cell holding the h the segment starts from, −1 for a chain's first
// segment, and seg.out is where it writes the h it ends with — the chain's
// result on the last segment, the next segment's in otherwise.
type deepSeg struct {
	ext  bool
	rows []DeepRow
	in   int
	out  slot
}

type deepInst struct {
	alpha int
	segs  []deepSeg
	out   slot
}

// DeepHorner returns h after the rows, from h = 0: a base row applies, for
// its active lanes j from CellWidth−1 down to 0,
//
//	h ← h·α + sel_j·x_j,
//
// x_j the j-th lane of its cell (a base value, added to h's first lane); an
// Ext row applies h ← h·α + sel·x, x its cell's E6 value. Over values of
// decreasing index i, this is the Horner Σ_i α^i·sel_i·x_i, CellWidth base
// values per row.
func (m *Machine) DeepHorner(alpha int, rows []DeepRow) int {
	if len(rows) == 0 {
		panic("DeepHorner: no rows")
	}
	for _, r := range rows {
		if r.Act == 0 || r.Sel&^r.Act != 0 || (r.Ext && r.Act != 1) {
			panic(fmt.Sprintf("DeepHorner: row act %08b sel %08b ext %v", r.Act, r.Sel, r.Ext))
		}
		m.read(r.Cell)
		m.read(alpha)
	}
	in := deepInst{alpha: alpha}
	for i := 0; i < len(rows); {
		j := i
		for j < len(rows) && rows[j].Ext == rows[i].Ext {
			j++
		}
		in.segs = append(in.segs, deepSeg{ext: rows[i].Ext, rows: rows[i:j], in: -1})
		i = j
	}
	for k := range in.segs[:len(in.segs)-1] {
		h := m.wr()
		in.segs[k].out = h
		in.segs[k+1].in = m.rd(h.addr).addr
	}
	in.out = m.wr()
	in.segs[len(in.segs)-1].out = in.out
	m.deeps = append(m.deeps, in)
	m.record(instrDeep, len(m.deeps)-1)
	return in.out.addr
}

// deepStep applies one step h ← h·α + x to h.
func deepStep(h, alpha, x *ext.E6) {
	h.Mul(h, alpha)
	h.Add(h, x)
}

// deepRowSteps applies a row to h and returns h after each lane, hs[j] after
// lane j (lanes CellWidth−1 down to 0; an inactive lane keeps h).
func deepRowSteps(h ext.E6, alpha ext.E6, row DeepRow, x Cell) [CellWidth]ext.E6 {
	var hs [CellWidth]ext.E6
	for j := CellWidth - 1; j >= 0; j-- {
		if row.Act>>j&1 == 1 {
			var t ext.E6
			if row.Sel>>j&1 == 1 {
				if row.Ext {
					t = CellE6(x)
				} else {
					t.B0.A0 = x[j]
				}
			}
			deepStep(&h, &alpha, &t)
		}
		hs[j] = h
	}
	return hs
}

// execDeep runs the chain and writes every segment's h, the handed-over cells
// as well as the chain's result.
func (m *Machine) execDeep(in deepInst, r *Run) {
	alpha := CellE6(r.values[in.alpha])
	var h ext.E6
	for _, sg := range in.segs {
		for _, row := range sg.rows {
			h = deepRowSteps(h, alpha, row, r.values[row.Cell])[0]
		}
		r.values[sg.out.addr] = E6Cell(h)
	}
}

// deepChip: one row per DeepRow of its kind,
//
//	h_j = h_{j+1} + act_j·(h_{j+1}·α + t_j − h_{j+1}),   j = lanes−1 … 0,
//
// with h_lanes = hin, t_j = sel_j·x_j on the first lane for j ≥ 1, and t_0 =
// sel_0·x_0 on the first lane plus, on the Ext instance, sel_0·x_k on lane k ≥ 1 (x as an E6
// value on an Ext row).
//
// There are two instances, on two modules. A base row steps through up to
// CellWidth base values, so it needs CellWidth sets of h columns; an Ext row
// consumes a single E6 and steps once, so seven of those eight sets would be
// dead on it. On the two-proof RISC-V verifier at 128 FRI queries Ext rows are
// 74% of the chip, which both wastes those columns and puts the chip over the
// per-module shard limit at five proofs. Splitting them by kind gives each the
// width it needs and keeps both modules inside the limit.
//
// A chain's rows are cut into segments at every change of kind (at most one
// per chain in practice), and the running h crosses from one module to the
// other through a cell, so what is computed is unchanged:
//
//	hin = h<0>[−1]              on a segment's later rows
//	hin = the cell at addr_in   on a continuing segment's first row (cont)
//	hin = 0                     on a chain's first row, and on padding
//
// Columns: x0..7 (the cell read), al0..5 (α), hin0..5, h<j>_0..5 for j <
// lanes. Setup: active, first, cont, act_j, sel_j, addr_x, addr_al,
// addr_in, and addr_o, m_o (h_0 written on a segment's last row). Padding rows
// are first rows with no active lane and no cont, so their h is 0.
// deepDegree is the degree of the deep chip's constraints, on both instances.
const deepDegree = 3

type deepChip struct {
	m      *Machine
	module string
	lanes  int // step slots per row: CellWidth for base rows, 1 for Ext rows
	ext    bool
}

func (c deepChip) name() string { return c.module }

func (c deepChip) rows() int {
	n := 0
	for _, in := range c.m.deeps {
		for _, sg := range in.segs {
			if sg.ext == c.ext {
				n += len(sg.rows)
			}
		}
	}
	return n
}

// deepHPrefix is the prefix of the lanes of h after lane j: h<j>_0..5.
func deepHPrefix(j int) string { return laneName(deepH, j) + "_" }

func (c deepChip) hCols(j, s int) []expr.Expr { return e6Cols(c.module, deepHPrefix(j), s) }

func (c deepChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[c.module]
	active, first := setupCol(c.module, deepActive), setupCol(c.module, deepFirst)
	cont := setupCol(c.module, deepCont)
	// The chip's constraints have degree 3, and the bus batches its accesses
	// within it (see Bus.LimitDegree): degree 5 would double the domain its
	// quotient is evaluated on, and its quotient chunks are a large part of
	// the narrow Ext instance's columns.
	bus.LimitDegree(c.module, deepDegree)
	al := e6Cols(c.module, deepAl, 0)
	x := make([]expr.Expr, CellWidth)
	for k := range x {
		x[k] = col(c.module, laneName(deepX, k))
	}
	// hin, the h the row starts from: the previous row's within a segment, the
	// handed-over cell on a continuing segment's first row, 0 otherwise. The
	// bus read binds it in the cont case.
	hin := e6Cols(c.module, deepHIn, 0)
	for k, h := range c.hCols(0, -1) {
		mm.AssertZero(one().Sub(first).Mul(hin[k].Sub(h)))
		mm.AssertZero(first.Mul(one().Sub(cont)).Mul(hin[k]))
	}
	bus.Read(c.module, setupCol(c.module, deepAddrIn), cellOf(hin...), cont)

	prev := hin
	for j := c.lanes - 1; j >= 0; j-- {
		act, sel := setupCol(c.module, laneName(deepAct, j)), setupCol(c.module, laneName(deepSel, j))
		step := e6MulExprs(prev, al)
		step[0] = step[0].Add(sel.Mul(x[j]))
		if j == 0 && c.ext {
			// an Ext row adds its E6 value, the base lanes stop at lane 0
			for k := 1; k < 6; k++ {
				step[k] = step[k].Add(sel.Mul(x[k]))
			}
		}
		h := c.hCols(j, 0)
		for k := range 6 {
			mm.AssertZero(h[k].Sub(prev[k]).Sub(act.Mul(step[k].Sub(prev[k]))))
		}
		prev = h
	}
	bus.Read(c.module, setupCol(c.module, deepAddrX), cellOf(x...), active)
	bus.Read(c.module, setupCol(c.module, deepAddrAl), cellOf(al...), active)
	bus.Write(c.module, setupCol(c.module, deepAddrO), cellOf(c.hCols(0, 0)...), setupCol(c.module, deepMO))
	return nil
}

func (c deepChip) setup(cs *cols) {
	cs.declare(deepActive, deepFirst, deepCont, deepAddrX, deepAddrAl, deepAddrIn, deepAddrO, deepMO)
	cs.declareLanes(deepAct, c.lanes)
	cs.declareLanes(deepSel, c.lanes)
	row := 0
	for _, in := range c.m.deeps {
		for _, sg := range in.segs {
			if sg.ext != c.ext {
				continue
			}
			for i, r := range sg.rows {
				cs.set(deepActive, row, 1)
				if i == 0 {
					cs.set(deepFirst, row, 1)
					if sg.in >= 0 {
						cs.set(deepCont, row, 1)
						cs.set(deepAddrIn, row, uint64(sg.in))
					}
				}
				for j := range c.lanes {
					cs.set(laneName(deepAct, j), row, uint64(r.Act>>j&1))
					cs.set(laneName(deepSel, j), row, uint64(r.Sel>>j&1))
				}
				cs.set(deepAddrX, row, uint64(r.Cell))
				cs.set(deepAddrAl, row, uint64(in.alpha))
				if i == len(sg.rows)-1 {
					cs.set(deepAddrO, row, uint64(sg.out.addr))
					cs.setInt(deepMO, row, c.m.mult(sg.out))
				}
				row++
			}
		}
	}
	for ; row < cs.n; row++ {
		cs.set(deepFirst, row, 1)
	}
}

func (c deepChip) trace(cs *cols, r *Run) error {
	cs.declareLanes(deepX, CellWidth)
	cs.declareLanes(deepAl, 6)
	cs.declareLanes(deepHIn, 6)
	for j := range c.lanes {
		cs.declareLanes(deepHPrefix(j), 6)
	}
	row := 0
	for _, in := range c.m.deeps {
		alpha := CellE6(r.values[in.alpha])
		for _, sg := range in.segs {
			if sg.ext != c.ext {
				continue
			}
			var h ext.E6
			if sg.in >= 0 {
				h = CellE6(r.values[sg.in])
			}
			for _, dr := range sg.rows {
				x := r.values[dr.Cell]
				hs := deepRowSteps(h, alpha, dr, x)
				cs.setCell(deepX, row, x)
				cs.setE6(deepAl, row, alpha)
				cs.setE6(deepHIn, row, h)
				for j := range c.lanes {
					cs.setE6(deepHPrefix(j), row, hs[j])
				}
				h = hs[0]
				row++
			}
		}
	}
	return nil
}
