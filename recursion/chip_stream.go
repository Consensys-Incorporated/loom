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

// streamChip: one row per cell of a Pack stream (see Machine.Pack), the
// repacking of a leaf's items into whole cells that Sponge absorbs. The
// windows check every item against its place in the stream, so the chip only
// has to put the cells on the bus.
//
// These cells used to share the witness chip's module, which writes every
// cell the prover supplies. They are split off because the shard limit is per
// module, not per circuit: on the two-proof RISC-V verifier at 128 FRI
// queries they are 46% of that module's rows, and moving them keeps both
// modules under 2^MaxLogModuleSize at four proofs, where the single module
// was 17% over. The stream cells are committed and bussed exactly as before,
// on a module of their own. The split costs that module's overhead: its own
// setup, logup and quotient columns (+9 committed columns on that verifier)
// and one more tree group per query. Its padded rows can differ from the
// single module's, as two modules are each padded to a power of two.
//
// Every stream cell is a full KindDigest cell, so unlike the witness chip
// this one has no lanes to zero and no AIR beyond the bus.
//
// Setup: addr, mult. Columns: v0..7. Bus: writes [addr ‖ v] with
// multiplicity mult (the cell's read count).
type streamChip struct{ m *Machine }

func (c streamChip) name() string { return streamMod }

func (c streamChip) rows() int { return len(c.m.hints) }

func (c streamChip) define(b *board.Builder, bus *Bus) error {
	bus.Write(streamMod, setupCol(streamMod, witnessAddr), cellCols(streamMod, witnessV, 0), setupCol(streamMod, witnessMult))
	return nil
}

func (c streamChip) setup(cs *cols) {
	cs.declare(witnessAddr, witnessMult)
	for row, tc := range c.m.hints {
		cs.set(witnessAddr, row, uint64(tc.addr))
		cs.set(witnessMult, row, uint64(c.m.reads[tc.addr]))
	}
}

func (c streamChip) trace(cs *cols, r *Run) error {
	cs.declareLanes(witnessV, CellWidth)
	for row, tc := range c.m.hints {
		cs.setCell(witnessV, row, r.values[tc.addr])
	}
	return nil
}
