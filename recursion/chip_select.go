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

	"github.com/consensys/loom/board"
)

// Setup columns of the select chip.
const (
	selectActive  = "active"
	selectAddrBit = "addr_bit"
	selectAddrA   = "addr_a"
	selectAddrB   = "addr_b"
	selectAddrOut = "addr_out"
	selectMultOut = "m_out"
)

// Witness columns of the select chip.
const (
	selectBit = "bit"
	selectA   = "a"   // lanes
	selectB   = "b"   // lanes
	selectOut = "out" // lanes
)

type selectInst struct {
	bit, a, b int
	out       slot
}

// Select returns a cell holding a if the scalar cell bit is 1, b if it is 0,
// on all CellWidth lanes (a digest, for instance; E6 arithmetic covers 6).
// Executing it fails if bit is neither.
func (m *Machine) Select(bit, a, b int) int {
	m.read(bit)
	m.read(a)
	m.read(b)
	in := selectInst{bit: bit, a: a, b: b, out: m.wr()}
	m.selects = append(m.selects, in)
	m.record(instrSelect, len(m.selects)-1)
	return in.out.addr
}

func (m *Machine) execSelect(s selectInst, r *Run) error {
	switch bit := r.values[s.bit][0]; {
	case bit.IsOne():
		r.values[s.out.addr] = r.values[s.a]
	case bit.IsZero():
		r.values[s.out.addr] = r.values[s.b]
	default:
		return fmt.Errorf("Select: bit %s is not 0 or 1", bit.String())
	}
	return nil
}

// selectChip: one row per Select,
//
//	bit·(bit − 1) = 0,  out = b + bit·(a − b)  on every lane,
//
// reading bit, a and b, writing out.
type selectChip struct{ m *Machine }

func (c selectChip) name() string { return selectMod }

func (c selectChip) rows() int { return len(c.m.selects) }

func (c selectChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[selectMod]
	bit := col(selectMod, selectBit)
	mm.AssertZero(bit.Mul(bit.Sub(one())))
	a, bb, out := cellCols(selectMod, selectA, 0), cellCols(selectMod, selectB, 0), cellCols(selectMod, selectOut, 0)
	for i := range CellWidth {
		mm.AssertZero(out[i].Sub(bb[i]).Sub(bit.Mul(a[i].Sub(bb[i]))))
	}
	active := setupCol(selectMod, selectActive)
	bus.Read(selectMod, setupCol(selectMod, selectAddrBit), cellOf(bit), active)
	bus.Read(selectMod, setupCol(selectMod, selectAddrA), a, active)
	bus.Read(selectMod, setupCol(selectMod, selectAddrB), bb, active)
	bus.Write(selectMod, setupCol(selectMod, selectAddrOut), out, setupCol(selectMod, selectMultOut))
	return nil
}

func (c selectChip) setup(cs *cols) {
	cs.declare(selectActive, selectAddrBit, selectAddrA, selectAddrB, selectAddrOut, selectMultOut)
	for row, s := range c.m.selects {
		cs.set(selectActive, row, 1)
		cs.set(selectAddrBit, row, uint64(s.bit))
		cs.set(selectAddrA, row, uint64(s.a))
		cs.set(selectAddrB, row, uint64(s.b))
		cs.set(selectAddrOut, row, uint64(s.out.addr))
		cs.setInt(selectMultOut, row, c.m.mult(s.out))
	}
}

func (c selectChip) trace(cs *cols, r *Run) error {
	cs.declare(selectBit)
	for _, x := range []string{selectA, selectB, selectOut} {
		cs.declareLanes(x, CellWidth)
	}
	for row, s := range c.m.selects {
		cs.setElem(selectBit, row, r.values[s.bit][0])
		cs.setCell(selectA, row, r.values[s.a])
		cs.setCell(selectB, row, r.values[s.b])
		cs.setCell(selectOut, row, r.values[s.out.addr])
	}
	return nil
}
