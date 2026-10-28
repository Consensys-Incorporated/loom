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

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/expr"
)

// The sponge's columns on the P2 core (see p2Chip), prefixed so they do not
// meet the Merkle path's. Setup:
const (
	spongeActive  = "sp_active"
	spongeFirst   = "sp_first"
	spongeLast    = "sp_last"
	spongeKeepCap = "sp_keep_cap"
	spongeAddrA   = "sp_addr_a"
	spongeAddrB   = "sp_addr_b"
	spongeOutAddr = "sp_out_addr"
	spongeOutMult = "sp_out_mult"
	spongeData    = "sp_data" // lanes
	spongeKeep    = "sp_keep" // lanes
)

// and witness: the block, read from two cells.
const spongeX = "sp_x" // lanes

type spongeInst struct {
	data   []int // data cells, 2 per block
	length int   // number of input elements
	out    int   // digest address
}

// Sponge hashes the first length elements of the data cells (2 per block,
// as laid out by InputStream or Pack) with loom's Poseidon2 sponge, and
// returns the address of the digest.
func (m *Machine) Sponge(data []int, length int) int {
	if len(data) != streamCells(length) || length == 0 {
		panic(fmt.Sprintf("Sponge: %d cells for %d elements", len(data), length))
	}
	for _, d := range data {
		m.read(d)
	}
	out := m.alloc()
	m.sponges = append(m.sponges, spongeInst{data: data, length: length, out: out})
	m.record(instrSponge, len(m.sponges)-1)
	return out
}

// spongeDigest hashes a sponge's data with loom's overwrite-mode Poseidon2
// sponge: the trailing lanes of a partial block keep the previous state.
func spongeDigest(r *Run, s spongeInst) (Cell, error) {
	var state [width]koalabear.Element
	perm := newPerm()
	for blk := range len(s.data) / 2 {
		lo, hi := r.values[s.data[2*blk]], r.values[s.data[2*blk+1]]
		for j := range rate {
			if blk*rate+j < s.length {
				if j < CellWidth {
					state[j] = lo[j]
				} else {
					state[j] = hi[j-CellWidth]
				}
			}
		}
		if err := perm.Permutation(state[:]); err != nil {
			return Cell{}, err
		}
	}
	var d Cell
	copy(d[:], state[:digest])
	return d, nil
}

// spongeBlocks is the number of rows the sponges take on the core.
func (m *Machine) spongeBlocks() int {
	n := 0
	for _, s := range m.sponges {
		n += len(s.data) / 2
	}
	return n
}

// spongeInput is the permutation input the sponge asks for on lane l:
//
//	data_l·x_l + keep_l·r_l[−1]   on the rate lanes
//	keep_cap·r_l[−1]              on the capacity
//
// so the state chains from row to row, and a trailing partial block keeps the
// previous state on its unused lanes, as loom's overwrite-mode sponge does. A
// sponge's first row has keep = keep_cap = 0, so no chain crosses a sponge
// boundary, the Merkle rows below or the module's wrap-around.
func spongeInput(l int) expr.Expr {
	prev := colShift(p2Mod, laneName(p2R, l), -1)
	if l >= rate {
		return setupCol(p2Mod, spongeKeepCap).Mul(prev)
	}
	return setupCol(p2Mod, laneName(spongeData, l)).Mul(col(p2Mod, laneName(spongeX, l))).
		Add(setupCol(p2Mod, laneName(spongeKeep, l)).Mul(prev))
}

// spongeSetup fills the sponges' setup columns, on the core's first rows.
func (c p2Chip) spongeSetup(cs *cols) {
	cs.declare(spongeFirst, spongeLast, spongeActive, spongeKeepCap, spongeAddrA, spongeAddrB, spongeOutAddr, spongeOutMult)
	for j := range rate {
		cs.declare(laneName(spongeData, j), laneName(spongeKeep, j))
	}
	row := 0
	for _, s := range c.m.sponges {
		blocks := len(s.data) / 2
		for blk := range blocks {
			cs.set(spongeActive, row, 1)
			cs.set(spongeAddrA, row, uint64(s.data[2*blk]))
			cs.set(spongeAddrB, row, uint64(s.data[2*blk+1]))
			if blk == 0 {
				cs.set(spongeFirst, row, 1)
			} else {
				cs.set(spongeKeepCap, row, 1)
			}
			for j := range rate {
				if blk*rate+j < s.length {
					cs.set(laneName(spongeData, j), row, 1)
				} else if blk > 0 {
					cs.set(laneName(spongeKeep, j), row, 1)
				}
			}
			if blk == blocks-1 {
				cs.set(spongeLast, row, 1)
				cs.set(spongeOutAddr, row, uint64(s.out))
				cs.set(spongeOutMult, row, uint64(c.m.reads[s.out]))
			}
			row++
		}
	}
}

// spongeTrace fills the blocks and their chained permutations from row 0, and
// returns the number of rows it used.
func (c p2Chip) spongeTrace(cs *cols, r *Run, perm *poseidon2.Permutation) (int, error) {
	cs.declareLanes(spongeX, rate)
	row := 0
	for _, s := range c.m.sponges {
		var state [width]koalabear.Element
		for blk := range len(s.data) / 2 {
			lo, hi := r.values[s.data[2*blk]], r.values[s.data[2*blk+1]]
			for j := range rate {
				x := lo[j%CellWidth]
				if j >= CellWidth {
					x = hi[j-CellWidth]
				}
				cs.setElem(laneName(spongeX, j), row, x)
				if blk*rate+j < s.length {
					state[j] = x
				}
			}
			for l := range width {
				cs.setElem(laneName(p2S, l), row, state[l])
			}
			if err := perm.Permutation(state[:]); err != nil {
				return 0, err
			}
			for l := range width {
				cs.setElem(laneName(p2R, l), row, state[l])
			}
			row++
		}
	}
	return row, nil
}
