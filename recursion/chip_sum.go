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

// Setup columns of the sum chip.
const (
	sumActive = "active"
	sumFirst  = "first"
	sumLast   = "last"
	sumSel    = "sel"   // sel<j>, lane j carries a term
	sumAddrX  = "addr_" // addr_<j>, the cell of lane j
	sumAddrO  = "addr_o"
	sumMO     = "m_o"
)

// Witness columns of the sum chip.
const (
	sumO = "o" // o0..5, the running total
	sumX = "x" // x<j>_0..5, the term on lane j
)

// DefaultSumLanes is the number of terms a sum row adds when
// Machine.SumLanes is not set.
const DefaultSumLanes = 8

// SumMinTerms is the smallest number of terms for which Sum is cheaper than
// the e6 chip's binary Add. A sum row costs about twice an e6 row, so it pays
// from three additions (four terms) up.
const SumMinTerms = 4

type sumInst struct {
	terms []int
	out   int
}

// sumLanes is the number of terms one sum row adds.
func (m *Machine) sumLanes() int {
	if m.SumLanes == 0 {
		return DefaultSumLanes
	}
	return m.SumLanes
}

// Sum returns the sum of the cells in terms, SumLanes of them per row.
//
// The e6 chip adds two cells per row, so an n-term sum costs n−1 of its rows,
// each 18 columns and three memory accesses to add six base elements. A sum
// row reads SumLanes cells and adds them to the running total at once, which
// is what the n-ary Add nodes of a flattened vanishing relation need.
func (m *Machine) Sum(terms []int) int {
	if len(terms) < 2 {
		panic(fmt.Sprintf("Sum: %d terms, want at least 2", len(terms)))
	}
	for _, t := range terms {
		m.read(t)
	}
	out := m.alloc()
	m.sums = append(m.sums, sumInst{terms: terms, out: out})
	m.record(instrSum, len(m.sums)-1)
	return out
}

func (m *Machine) execSum(s sumInst, r *Run) {
	var z ext.E6
	for _, t := range s.terms {
		v := CellE6(r.values[t])
		z.Add(&z, &v)
	}
	r.values[s.out] = E6Cell(z)
}

// sumRows is the number of rows a chain of n terms needs: k per row.
func sumRows(n, k int) int { return (n + k - 1) / k }

// sumChip: one row per group of k = SumLanes terms of a Sum chain.
//
// Columns: o0..5 (the running total after this row) and x<j>_0..5 for j < k
// (the terms). Setup: first, last, active, sel<j> (lane j carries a term),
// addr_<j> (its cell), addr_o and m_o (the result, written on the last row).
//
//	o = Σ_j sel_j·x_j             on the first row of a chain
//	o = o[−1] + Σ_j sel_j·x_j     on the others
//
// A lane with sel_j = 0 reads nothing and contributes nothing, so the last
// row of a chain may be partly empty. The running total is not written to
// memory between rows: only the last row writes, which is what keeps the
// memory traffic at one access per term plus one.
type sumChip struct{ m *Machine }

func (c sumChip) name() string { return sumMod }

func (c sumChip) rows() int {
	k, n := c.m.sumLanes(), 0
	for _, s := range c.m.sums {
		n += sumRows(len(s.terms), k)
	}
	return n
}

// sumXName is the name of lane l of the term on lane j.
func sumXName(j, l int) string { return fmt.Sprintf("%s%d_%d", sumX, j, l) }

// sumXCols returns the 6 columns of the term on lane j.
func sumXCols(j int) []expr.Expr {
	res := make([]expr.Expr, 6)
	for l := range res {
		res[l] = col(sumMod, sumXName(j, l))
	}
	return res
}

func sumSelName(j int) string  { return fmt.Sprintf("%s%d", sumSel, j) }
func sumAddrName(j int) string { return fmt.Sprintf("%s%d", sumAddrX, j) }

func (c sumChip) define(b *board.Builder, bus *Bus) error {
	k := c.m.sumLanes()
	mm := b.Modules[sumMod]
	first, active := setupCol(sumMod, sumFirst), setupCol(sumMod, sumActive)
	o := e6Cols(sumMod, sumO, 0)

	// Σ_j sel_j·x_j, lane by lane.
	sum := make([]expr.Expr, 6)
	for l := range sum {
		sum[l] = zero()
	}
	for j := range k {
		sel := setupCol(sumMod, sumSelName(j))
		x := sumXCols(j)
		for l := range 6 {
			sum[l] = sum[l].Add(sel.Mul(x[l]))
		}
	}

	// (active − first) is 1 on every chain row but the first and 0 on padding,
	// so the recurrence never reads across a chain start or the wrap-around.
	notFirst := active.Sub(first)
	prev := e6Cols(sumMod, sumO, -1)
	for l := range 6 {
		mm.AssertZero(first.Mul(o[l].Sub(sum[l])))
		mm.AssertZero(notFirst.Mul(o[l].Sub(prev[l]).Sub(sum[l])))
	}

	for j := range k {
		bus.Read(sumMod, setupCol(sumMod, sumAddrName(j)), cellOf(sumXCols(j)...),
			setupCol(sumMod, sumSelName(j)))
	}
	bus.Write(sumMod, setupCol(sumMod, sumAddrO), cellOf(o...), setupCol(sumMod, sumMO))
	return nil
}

func (c sumChip) setup(cs *cols) {
	k := c.m.sumLanes()
	cs.declare(sumFirst, sumLast, sumActive, sumAddrO, sumMO)
	for j := range k {
		cs.declare(sumSelName(j), sumAddrName(j))
	}
	row := 0
	for _, s := range c.m.sums {
		nRows := sumRows(len(s.terms), k)
		for i := range nRows {
			cs.set(sumActive, row, 1)
			if i == 0 {
				cs.set(sumFirst, row, 1)
			}
			for j := range k {
				if t := i*k + j; t < len(s.terms) {
					cs.set(sumSelName(j), row, 1)
					cs.set(sumAddrName(j), row, uint64(s.terms[t]))
				}
			}
			if i == nRows-1 {
				cs.set(sumLast, row, 1)
				cs.set(sumAddrO, row, uint64(s.out))
				cs.set(sumMO, row, uint64(c.m.reads[s.out]))
			}
			row++
		}
	}
}

func (c sumChip) trace(cs *cols, r *Run) error {
	k := c.m.sumLanes()
	cs.declareLanes(sumO, 6)
	for j := range k {
		for l := range 6 {
			cs.declare(sumXName(j, l))
		}
	}
	row := 0
	for _, s := range c.m.sums {
		var acc ext.E6
		nRows := sumRows(len(s.terms), k)
		for i := range nRows {
			for j := range k {
				t := i*k + j
				if t >= len(s.terms) {
					continue
				}
				v := CellE6(r.values[s.terms[t]])
				acc.Add(&acc, &v)
				for l, e := range E6Cell(v) {
					if l < 6 {
						cs.setElem(sumXName(j, l), row, e)
					}
				}
			}
			cs.setE6(sumO, row, acc)
			row++
		}
		if !E6Cell(acc).equalCell(r.values[s.out]) {
			return fmt.Errorf("sum to cell %d: traced value differs from the executed one", s.out)
		}
	}
	return nil
}

func (c Cell) equalCell(o Cell) bool {
	for i := range c {
		if !c[i].Equal(&o[i]) {
			return false
		}
	}
	return true
}
