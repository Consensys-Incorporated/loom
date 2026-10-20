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

import "github.com/consensys/loom/board"

// Setup columns of the witness chip.
const (
	witnessAddr = "addr"
	witnessMult = "mult"
	witnessZ1   = "z1" // lanes 1..5 are zero (a scalar)
	witnessZ6   = "z6" // lanes 6, 7 are zero (a scalar or an E6 value)
)

// Witness columns of the witness chip.
const (
	witnessV = "v" // lanes
)

// witnessChip: one row per cell the prover writes freely: the inputs, and the
// hints, cells computed during execution whose windows check them (the
// streams of Pack).
//
// Setup: addr, mult, z1, z6 (from the cell's kind). Columns: v0..7. Bus:
// writes [addr ‖ v] with multiplicity mult (the cell's read count). The
// readers check the values; the chip only types them, zeroing the lanes
// beyond the cell's kind:
//
//	z1·v_k = 0  for k = 1..5,    z6·v_k = 0  for k = 6, 7.
type witnessChip struct{ m *Machine }

func (c witnessChip) name() string { return witnessMod }

func (c witnessChip) cells() []typedCell {
	return append(append([]typedCell(nil), c.m.inputs...), c.m.hints...)
}

func (c witnessChip) rows() int { return len(c.cells()) }

func (c witnessChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[witnessMod]
	v := cellCols(witnessMod, witnessV, 0)
	for k := KindScalar; k < CellWidth; k++ {
		z := setupCol(witnessMod, witnessZ1)
		if k >= KindE6 {
			z = setupCol(witnessMod, witnessZ6)
		}
		mm.AssertZero(z.Mul(v[k]))
	}
	bus.Write(witnessMod, setupCol(witnessMod, witnessAddr), v, setupCol(witnessMod, witnessMult))
	return nil
}

func (c witnessChip) setup(cs *cols) {
	cs.declare(witnessAddr, witnessMult, witnessZ1, witnessZ6)
	for row, tc := range c.cells() {
		cs.set(witnessAddr, row, uint64(tc.addr))
		cs.set(witnessMult, row, uint64(c.m.reads[tc.addr]))
		if tc.kind == KindScalar {
			cs.set(witnessZ1, row, 1)
		}
		if tc.kind <= KindE6 {
			cs.set(witnessZ6, row, 1)
		}
	}
}

func (c witnessChip) trace(cs *cols, r *Run) error {
	cs.declareLanes(witnessV, CellWidth)
	for row, tc := range c.cells() {
		cs.setCell(witnessV, row, r.values[tc.addr])
	}
	return nil
}
