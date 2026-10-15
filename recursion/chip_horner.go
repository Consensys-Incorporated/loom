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

// DefaultHornerLanes is the number of base coefficients a Horner row consumes
// when Machine.HornerLanes is not set: a full memory cell.
const DefaultHornerLanes = CellWidth

type hornerInst struct {
	y     int   // the E6 multiplier
	cells []int // the packed coefficient cells, most significant first
	out   int
}

// Lanes returns the number of coefficients one Horner row consumes.
func (m *Machine) hornerLanes() int {
	if m.HornerLanes == 0 {
		return DefaultHornerLanes
	}
	return m.HornerLanes
}

// HornerPacked returns Σ_j c_j·y^(N−1−j) over the N = len(cells)·HornerLanes
// base coefficients packed in cells: lane l of cells[i] is coefficient
// i·HornerLanes + l, lane 0 being the most significant of its cell, and the
// lanes at or above HornerLanes must be zero.
//
// Leading zero coefficients leave the result unchanged, so a chain whose
// length is not a multiple of HornerLanes is front-padded by the caller.
//
// This is the batched form of the accumulation the DEEP-quotient combination
// performs over the opened values of base polynomials. One row consumes a
// whole cell, so the coefficients cost one witness row per HornerLanes of
// them rather than one each.
func (m *Machine) HornerPacked(y int, cells []int) int {
	if len(cells) == 0 {
		panic("HornerPacked: no coefficient cells")
	}
	if k := m.hornerLanes(); k < 1 || k > CellWidth {
		panic(fmt.Sprintf("HornerPacked: HornerLanes = %d, want 1..%d", k, CellWidth))
	}
	// Every row reads y and its own coefficient cell.
	for _, c := range cells {
		m.read(y)
		m.read(c)
	}
	out := m.alloc()
	m.horners = append(m.horners, hornerInst{y: y, cells: cells, out: out})
	m.record(instrHornerBase, len(m.horners)-1)
	return out
}

// HornerBase returns Σ_i coeffs[i]·y^(len−1−i) for scalar coefficient cells.
// It is HornerPacked's unbatched special case and needs HornerLanes = 1; with
// one lane per cell a packed cell is a scalar cell.
func (m *Machine) HornerBase(y int, coeffs []int) int {
	if k := m.hornerLanes(); k != 1 {
		panic(fmt.Sprintf("HornerBase: HornerLanes = %d, want 1 (use HornerPacked)", k))
	}
	return m.HornerPacked(y, coeffs)
}

// hornerPowers returns y^1 … y^k.
func hornerPowers(y ext.E6, k int) []ext.E6 {
	res := make([]ext.E6, k+1)
	res[0].SetOne()
	for j := 1; j <= k; j++ {
		res[j].Mul(&res[j-1], &y)
	}
	return res
}

// hornerValue accumulates the chain's value, and (when rows is non-nil)
// appends the accumulator after each row.
func (m *Machine) hornerValue(h hornerInst, r *Run, rows *[]ext.E6) ext.E6 {
	k := m.hornerLanes()
	pow := hornerPowers(CellE6(r.values[h.y]), k)
	var z ext.E6
	for i, cell := range h.cells {
		if i > 0 {
			z.Mul(&z, &pow[k])
		}
		v := r.values[cell]
		for j := range k {
			var t ext.E6
			t.MulByElement(&pow[k-1-j], &v[j])
			z.Add(&z, &t)
		}
		if rows != nil {
			*rows = append(*rows, z)
		}
	}
	return z
}

func (m *Machine) execHornerBase(h hornerInst, r *Run) {
	r.values[h.out] = E6Cell(m.hornerValue(h, r, nil))
}

// hornerChip: one row per packed coefficient cell of a HornerPacked chain,
// with k = HornerLanes coefficients per row.
//
// Columns: o0..5 (the accumulator), p1_0..5 … pk_0..5 (the powers y^1 … y^k)
// and c0..c_{k−1} (the coefficients of the row), i.e. 6 + 7k. Setup: first,
// last, active, addr_y, addr_c, o_addr, o_mult.
//
//	p_j = p_{j−1}·p_1                for j = 2..k, on every active row
//	o = S                            on the first row of a chain
//	o = o[−1]·p_k + S                on the others
//
// with S = Σ_{j<k} c_j·y^(k−1−j), whose last term c_{k−1} lands on lane 0
// alone (the base-field embedding). Every row reads the y cell and its
// coefficient cell; the last row of a chain writes the result.
//
// The powers are derived in-row from p_1 rather than read, so the row keeps
// the three memory accesses — and hence the degree — of the unbatched chip.
type hornerChip struct{ m *Machine }

func (c hornerChip) name() string { return hornerMod }

func (c hornerChip) rows() int {
	n := 0
	for _, h := range c.m.horners {
		n += len(h.cells)
	}
	return n
}

// powName is the name of lane l of the committed power y^j.
func powName(j, l int) string { return fmt.Sprintf("p%d_%d", j, l) }

// powCols returns the 6 columns of the power y^j.
func powCols(j int) []expr.Expr {
	res := make([]expr.Expr, 6)
	for l := range res {
		res[l] = col(hornerMod, powName(j, l))
	}
	return res
}

func (c hornerChip) define(b *board.Builder, bus *Bus) error {
	k := c.m.hornerLanes()
	mm := b.Modules[hornerMod]
	first, active := setupCol(hornerMod, "first"), setupCol(hornerMod, "active")
	notFirst := active.Sub(first)
	o := e6Cols(hornerMod, "o", 0)

	// The powers y^2..y^k are derived from y in-row, so only y is read.
	p1 := powCols(1)
	for j := 2; j <= k; j++ {
		prod := e6MulExprs(powCols(j-1), p1)
		pj := powCols(j)
		for l := range 6 {
			mm.AssertZero(active.Mul(pj[l].Sub(prod[l])))
		}
	}

	// S = Σ_{j<k} c_j·y^(k−1−j); y^0 = 1 contributes to lane 0 only.
	coeffs := make([]expr.Expr, k)
	sum := make([]expr.Expr, 6)
	for l := range sum {
		sum[l] = zero()
	}
	for j := range k {
		coeffs[j] = col(hornerMod, fmt.Sprintf("c%d", j))
		if e := k - 1 - j; e == 0 {
			sum[0] = sum[0].Add(coeffs[j])
		} else {
			p := powCols(e)
			for l := range 6 {
				sum[l] = sum[l].Add(coeffs[j].Mul(p[l]))
			}
		}
	}

	// (active − first) is 1 on every chain row but the first, 0 on padding, so
	// the recurrence never reads across a chain start or the wrap-around.
	prev := e6MulExprs(e6Cols(hornerMod, "o", -1), powCols(k))
	for l := range 6 {
		mm.AssertZero(first.Mul(o[l].Sub(sum[l])))
		mm.AssertZero(notFirst.Mul(o[l].Sub(prev[l]).Sub(sum[l])))
	}

	bus.Read(hornerMod, setupCol(hornerMod, "addr_y"), cellOf(p1...), active)
	bus.Read(hornerMod, setupCol(hornerMod, "addr_c"), cellOf(coeffs...), active)
	bus.Write(hornerMod, setupCol(hornerMod, "o_addr"), cellOf(o...), setupCol(hornerMod, "o_mult"))
	return nil
}

func (c hornerChip) setup(cs *cols) {
	cs.declare("first", "last", "active", "addr_y", "addr_c", "o_addr", "o_mult")
	row := 0
	for _, h := range c.m.horners {
		for i, cell := range h.cells {
			cs.set("active", row, 1)
			cs.set("addr_y", row, uint64(h.y))
			cs.set("addr_c", row, uint64(cell))
			if i == 0 {
				cs.set("first", row, 1)
			}
			if i == len(h.cells)-1 {
				cs.set("last", row, 1)
				cs.set("o_addr", row, uint64(h.out))
				cs.set("o_mult", row, uint64(c.m.reads[h.out]))
			}
			row++
		}
	}
}

func (c hornerChip) trace(cs *cols, r *Run) error {
	k := c.m.hornerLanes()
	cs.declareLanes("c", k)
	cs.declareLanes("o", 6)
	for j := 1; j <= k; j++ {
		for l := range 6 {
			cs.declare(powName(j, l))
		}
	}
	row := 0
	for _, h := range c.m.horners {
		pow := hornerPowers(CellE6(r.values[h.y]), k)
		var accs []ext.E6
		c.m.hornerValue(h, r, &accs)
		for i, cell := range h.cells {
			v := r.values[cell]
			for j := range k {
				cs.setElem(fmt.Sprintf("c%d", j), row, v[j])
			}
			for j := 1; j <= k; j++ {
				for l, x := range E6Cell(pow[j]) {
					if l < 6 {
						cs.setElem(powName(j, l), row, x)
					}
				}
			}
			cs.setE6("o", row, accs[i])
			row++
		}
		if !E6Cell(accs[len(accs)-1]).equal(r.values[h.out]) {
			return fmt.Errorf("horner chain to cell %d: traced value differs from the executed one", h.out)
		}
	}
	return nil
}

func (c Cell) equal(o Cell) bool {
	for i := range c {
		if !c[i].Equal(&o[i]) {
			return false
		}
	}
	return true
}
