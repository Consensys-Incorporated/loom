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

// DeepRow is one row of a DEEP Horner chain: the cell it reads and, as bit
// masks over its lanes, the lanes that take part (Act) and those whose value
// is added (Sel). A base row reads up to CellWidth base values; an Ext row
// reads an E6 value and has a single step (Act = 1).
type DeepRow struct {
	Cell     int
	Ext      bool
	Act, Sel uint8
}

type deepInst struct {
	alpha int
	rows  []DeepRow
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
	in := deepInst{alpha: alpha, rows: rows, out: m.wr()}
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

func (m *Machine) execDeep(in deepInst, r *Run) {
	alpha := CellE6(r.values[in.alpha])
	var h ext.E6
	for _, row := range in.rows {
		h = deepRowSteps(h, alpha, row, r.values[row.Cell])[0]
	}
	r.values[in.out.addr] = E6Cell(h)
}

// deepChip: one row per DeepRow,
//
//	h_j = h_{j+1} + act_j·(h_{j+1}·α + t_j − h_{j+1}),   j = 7 … 0,
//
// with h_8 = (1 − first)·h_0[−1] (the previous row's result, 0 at the start
// of a chain), t_j = sel_j·x_j on the first lane for j ≥ 1, and t_0 = sel_0·x_0
// on the first lane plus ext·sel_0·x_k on lane k ≥ 1 (x as an E6 value on an
// Ext row).
//
// Columns: x0..7 (the cell read), al0..5 (α), h<j>_0..5 (h after lane j).
// Setup: active, first, ext, act0..7, sel0..7, addr_x, addr_al, and addr_o,
// m_o (h_0 written on the last row of a chain). Padding rows are first rows
// with no active lane, so their h is 0.
type deepChip struct{ m *Machine }

func (c deepChip) name() string { return deepMod }

func (c deepChip) rows() int {
	n := 0
	for _, in := range c.m.deeps {
		n += len(in.rows)
	}
	return n
}

func hCols(j, s int) []expr.Expr { return e6Cols(deepMod, fmt.Sprintf("h%d_", j), s) }

func (c deepChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[deepMod]
	active, first, isExt := setupCol(deepMod, "active"), setupCol(deepMod, "first"), setupCol(deepMod, "ext")
	al := e6Cols(deepMod, "al", 0)
	x := make([]expr.Expr, CellWidth)
	for k := range x {
		x[k] = col(deepMod, fmt.Sprintf("x%d", k))
	}
	notFirst := one().Sub(first)
	prev := make([]expr.Expr, 6)
	for k, h := range hCols(0, -1) {
		prev[k] = notFirst.Mul(h)
	}
	for j := CellWidth - 1; j >= 0; j-- {
		act, sel := setupCol(deepMod, fmt.Sprintf("act%d", j)), setupCol(deepMod, fmt.Sprintf("sel%d", j))
		step := e6MulExprs(prev, al)
		step[0] = step[0].Add(sel.Mul(x[j]))
		if j == 0 {
			for k := 1; k < 6; k++ {
				step[k] = step[k].Add(isExt.Mul(sel).Mul(x[k]))
			}
		}
		h := hCols(j, 0)
		for k := range 6 {
			mm.AssertZero(h[k].Sub(prev[k]).Sub(act.Mul(step[k].Sub(prev[k]))))
		}
		prev = h
	}
	bus.Read(deepMod, setupCol(deepMod, "addr_x"), cellOf(x...), active)
	bus.Read(deepMod, setupCol(deepMod, "addr_al"), cellOf(al...), active)
	bus.Write(deepMod, setupCol(deepMod, "addr_o"), cellOf(hCols(0, 0)...), setupCol(deepMod, "m_o"))
	return nil
}

func (c deepChip) setup(cs *cols) {
	cs.declare("active", "first", "ext", "addr_x", "addr_al", "addr_o", "m_o")
	cs.declareLanes("act", CellWidth)
	cs.declareLanes("sel", CellWidth)
	row := 0
	for _, in := range c.m.deeps {
		for i, r := range in.rows {
			cs.set("active", row, 1)
			if i == 0 {
				cs.set("first", row, 1)
			}
			if r.Ext {
				cs.set("ext", row, 1)
			}
			for j := range CellWidth {
				cs.set(fmt.Sprintf("act%d", j), row, uint64(r.Act>>j&1))
				cs.set(fmt.Sprintf("sel%d", j), row, uint64(r.Sel>>j&1))
			}
			cs.set("addr_x", row, uint64(r.Cell))
			cs.set("addr_al", row, uint64(in.alpha))
			if i == len(in.rows)-1 {
				cs.set("addr_o", row, uint64(in.out.addr))
				cs.setInt("m_o", row, c.m.mult(in.out))
			}
			row++
		}
	}
	for ; row < cs.n; row++ {
		cs.set("first", row, 1)
	}
}

func (c deepChip) trace(cs *cols, r *Run) error {
	cs.declareLanes("x", CellWidth)
	cs.declareLanes("al", 6)
	for j := range CellWidth {
		cs.declareLanes(fmt.Sprintf("h%d_", j), 6)
	}
	row := 0
	for _, in := range c.m.deeps {
		alpha := CellE6(r.values[in.alpha])
		var h ext.E6
		for _, dr := range in.rows {
			x := r.values[dr.Cell]
			hs := deepRowSteps(h, alpha, dr, x)
			cs.setCell("x", row, x)
			cs.setE6("al", row, alpha)
			for j := range CellWidth {
				cs.setE6(fmt.Sprintf("h%d_", j), row, hs[j])
			}
			h = hs[0]
			row++
		}
	}
	return nil
}
