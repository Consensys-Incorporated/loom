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
)

// Witness columns of the witness chip.
const (
	witnessV = "v" // lanes
)

// witnessChip: one row per cell the prover writes freely: the inputs, and the
// hints, cells computed during execution whose windows check them (the
// streams of Pack, the outputs of Lanes).
//
// Setup: addr, mult. Columns: v0..7.
type witnessChip struct{ m *Machine }

func (c witnessChip) name() string { return witnessMod }

func (c witnessChip) cells() []int {
	return append(append([]int(nil), c.m.inputs...), c.m.hints...)
}

func (c witnessChip) rows() int { return len(c.cells()) }

func (c witnessChip) define(b *board.Builder, bus *Bus) error {
	bus.Write(witnessMod, setupCol(witnessMod, witnessAddr), cellCols(witnessMod, witnessV, 0), setupCol(witnessMod, witnessMult))
	return nil
}

func (c witnessChip) setup(cs *cols) {
	cs.declare(witnessAddr, witnessMult)
	for row, a := range c.cells() {
		cs.set(witnessAddr, row, uint64(a))
		cs.set(witnessMult, row, uint64(c.m.reads[a]))
	}
}

func (c witnessChip) trace(cs *cols, r *Run) error {
	cs.declareLanes(witnessV, CellWidth)
	for row, a := range c.cells() {
		cs.setCell(witnessV, row, r.values[a])
	}
	return nil
}
