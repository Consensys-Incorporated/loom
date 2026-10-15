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
	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

// Setup columns of the fold chip.
const (
	foldActive = "active"
	foldLast   = "last"
	foldAddrP  = "addr_p"
	foldAddrQ  = "addr_q"
	foldAddrAl = "addr_al"
	foldAddrXb = "addr_xb"
	foldAddrJ  = "addr_j"
)

// Witness columns of the fold chip.
const (
	foldP  = "p"  // lanes
	foldQ  = "q"  // lanes
	foldAl = "al" // lanes
	foldJ  = "j"  // lanes
	foldXi = "xi"
	foldBn = "bn"
)

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

// foldChip: one row per FRI round of a query, and a terminal row holding the
// final value in p and q.
//
// Columns: p0..5, q0..5 (the opened pair), al0..5 (α), xi (x⁻¹), bn (selects
// p or q in the next row), j0..5 (the injected term). Setup: active, last (the
// terminal row), addr_p, addr_q, addr_al, addr_xb, addr_j. On every row but
// the terminal one,
//
//	(p + q)/2 + α·(p − q)·xi/2 + j = p[+1] + bn·(q[+1] − p[+1]).
type foldChip struct{ m *Machine }

func (c foldChip) name() string { return foldMod }

func (c foldChip) rows() int {
	n := 0
	for _, ch := range c.m.folds {
		n += len(ch)
	}
	return n
}

func (c foldChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[foldMod]
	active, last := setupCol(foldMod, foldActive), setupCol(foldMod, foldLast)
	notLast := active.Sub(last)
	p, q, al, j := e6Cols(foldMod, foldP, 0), e6Cols(foldMod, foldQ, 0), e6Cols(foldMod, foldAl, 0), e6Cols(foldMod, foldJ, 0)
	pn, qn := e6Cols(foldMod, foldP, 1), e6Cols(foldMod, foldQ, 1)
	xi, bn := col(foldMod, foldXi), col(foldMod, foldBn)
	var half koalabear.Element
	half.SetUint64(2)
	half.Inverse(&half)
	diff := make([]expr.Expr, 6)
	for i := range diff {
		diff[i] = p[i].Sub(q[i]).Mul(xi).Mul(constElem(half))
	}
	odd := e6MulExprs(al, diff)
	for i := range 6 {
		lhs := p[i].Add(q[i]).Mul(constElem(half)).Add(odd[i]).Add(j[i])
		rhs := pn[i].Add(bn.Mul(qn[i].Sub(pn[i])))
		mm.AssertZero(notLast.Mul(lhs.Sub(rhs)))
	}
	bus.Read(foldMod, setupCol(foldMod, foldAddrP), cellOf(p...), active)
	bus.Read(foldMod, setupCol(foldMod, foldAddrQ), cellOf(q...), active)
	bus.Read(foldMod, setupCol(foldMod, foldAddrAl), cellOf(al...), notLast)
	bus.Read(foldMod, setupCol(foldMod, foldAddrXb), cellOf(xi, bn), notLast)
	bus.Read(foldMod, setupCol(foldMod, foldAddrJ), cellOf(j...), notLast)
	return nil
}

func (c foldChip) setup(cs *cols) {
	cs.declare(foldActive, foldLast, foldAddrP, foldAddrQ, foldAddrAl, foldAddrXb, foldAddrJ)
	row := 0
	for _, ch := range c.m.folds {
		for _, r := range ch {
			cs.set(foldActive, row, 1)
			cs.set(foldAddrP, row, uint64(r.p))
			cs.set(foldAddrQ, row, uint64(r.q))
			if r.alpha < 0 {
				cs.set(foldLast, row, 1)
			} else {
				cs.set(foldAddrAl, row, uint64(r.alpha))
				cs.set(foldAddrXb, row, uint64(r.xb))
				cs.set(foldAddrJ, row, uint64(r.inj))
			}
			row++
		}
	}
}

func (c foldChip) trace(cs *cols, r *Run) error {
	cs.declare(foldXi, foldBn)
	for _, x := range []string{foldP, foldQ, foldAl, foldJ} {
		cs.declareLanes(x, 6)
	}
	row := 0
	for _, ch := range c.m.folds {
		for _, fr := range ch {
			cs.setE6(foldP, row, CellE6(r.values[fr.p]))
			cs.setE6(foldQ, row, CellE6(r.values[fr.q]))
			if fr.alpha >= 0 {
				cs.setE6(foldAl, row, CellE6(r.values[fr.alpha]))
				cs.setE6(foldJ, row, CellE6(r.values[fr.inj]))
				cs.setElem(foldXi, row, r.values[fr.xb][0])
				cs.setElem(foldBn, row, r.values[fr.xb][1])
			}
			row++
		}
	}
	return nil
}
