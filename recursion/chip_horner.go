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

type hornerInst struct {
	y      int   // the E6 multiplier
	coeffs []int // the scalar cells, most significant first
	out    int
}

// HornerBase returns Σ_i coeffs[i]·y^(len−1−i) for scalar coefficients, one
// row per coefficient on the Horner chip.
//
// It is the base-coefficient counterpart of Machine.Horner: the coefficients
// are scalar cells (a base value in lane 0) rather than E6 cells, which is
// what the DEEP-quotient combination of opened base polynomials needs. Each
// row multiplies the accumulator by y and adds one base lane, so it carries
// one E6 product instead of the e6 chip's two, over 13 columns instead of 18.
func (m *Machine) HornerBase(y int, coeffs []int) int {
	if len(coeffs) == 0 {
		panic("HornerBase: no coefficients")
	}
	// Every row reads y and its own coefficient.
	for _, c := range coeffs {
		m.read(y)
		m.read(c)
	}
	out := m.alloc()
	m.horners = append(m.horners, hornerInst{y: y, coeffs: coeffs, out: out})
	m.record(instrHornerBase, len(m.horners)-1)
	return out
}

func (m *Machine) execHornerBase(h hornerInst, r *Run) {
	y := CellE6(r.values[h.y])
	var z ext.E6
	for i, c := range h.coeffs {
		if i > 0 {
			z.Mul(&z, &y)
		}
		z.B0.A0.Add(&z.B0.A0, &r.values[c][0])
	}
	r.values[h.out] = E6Cell(z)
}

// hornerChip: one row per coefficient of a HornerBase chain.
//
// Columns: o0..5 (the accumulator), y0..5 (the multiplier), c (the base
// coefficient). Setup: first, last, active, addr_y, addr_c, o_addr, o_mult.
//
//	o = c·e0                on the first row of a chain
//	o = o[−1]·y + c·e0      on the others
//
// with e0 the base-field embedding (lane 0). Every row reads y and the
// coefficient cell; the last row of a chain writes the result.
type hornerChip struct{ m *Machine }

func (c hornerChip) name() string { return hornerMod }

func (c hornerChip) rows() int {
	n := 0
	for _, h := range c.m.horners {
		n += len(h.coeffs)
	}
	return n
}

func (c hornerChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[hornerMod]
	first, active := setupCol(hornerMod, "first"), setupCol(hornerMod, "active")
	o, y := e6Cols(hornerMod, "o", 0), e6Cols(hornerMod, "y", 0)
	coeff := col(hornerMod, "c")
	prevY := e6MulExprs(e6Cols(hornerMod, "o", -1), y)
	// (active − first) is 1 on every chain row but the first, 0 on padding,
	// so the recurrence never reads across a chain start or the wrap-around.
	notFirst := active.Sub(first)
	for i := range 6 {
		var lane expr.Expr = zero()
		if i == 0 {
			lane = coeff
		}
		mm.AssertZero(first.Mul(o[i].Sub(lane)))
		mm.AssertZero(notFirst.Mul(o[i].Sub(prevY[i]).Sub(lane)))
	}

	bus.Read(hornerMod, setupCol(hornerMod, "addr_y"), cellOf(y...), active)
	bus.Read(hornerMod, setupCol(hornerMod, "addr_c"), cellOf(coeff), active)
	bus.Write(hornerMod, setupCol(hornerMod, "o_addr"), cellOf(o...), setupCol(hornerMod, "o_mult"))
	return nil
}

func (c hornerChip) setup(cs *cols) {
	cs.declare("first", "last", "active", "addr_y", "addr_c", "o_addr", "o_mult")
	row := 0
	for _, h := range c.m.horners {
		for k, coeff := range h.coeffs {
			cs.set("active", row, 1)
			cs.set("addr_y", row, uint64(h.y))
			cs.set("addr_c", row, uint64(coeff))
			if k == 0 {
				cs.set("first", row, 1)
			}
			if k == len(h.coeffs)-1 {
				cs.set("last", row, 1)
				cs.set("o_addr", row, uint64(h.out))
				cs.set("o_mult", row, uint64(c.m.reads[h.out]))
			}
			row++
		}
	}
}

func (c hornerChip) trace(cs *cols, r *Run) error {
	cs.declare("c")
	cs.declareLanes("o", 6)
	cs.declareLanes("y", 6)
	row := 0
	for _, h := range c.m.horners {
		y := CellE6(r.values[h.y])
		var z ext.E6
		for k, coeff := range h.coeffs {
			if k > 0 {
				z.Mul(&z, &y)
			}
			v := r.values[coeff][0]
			z.B0.A0.Add(&z.B0.A0, &v)
			cs.setElem("c", row, v)
			cs.setE6("y", row, y)
			cs.setE6("o", row, z)
			row++
		}
		if !E6Cell(z).equal(r.values[h.out]) {
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
