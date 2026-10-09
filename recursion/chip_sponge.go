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
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
)

// Setup columns of the sponge chip.
const (
	spongeFirst   = "first"
	spongeLast    = "last"
	spongeActive  = "active"
	spongeKeepCap = "keep_cap"
	spongeAddrA   = "addr_a"
	spongeAddrB   = "addr_b"
	spongeOutAddr = "out_addr"
	spongeOutMult = "out_mult"
	spongeData    = "data" // lanes
	spongeKeep    = "keep" // lanes
)

// Witness columns of the sponge chip.
const (
	spongeX   = "x"   // lanes
	spongeOut = "out" // lanes
)

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

// spongeChip: one row per 16-element block of a sponge.
//
// Columns: x0..15 (the block, read from two cells), out0..23 (the permutation
// output). Setup: first, last, active, data_j (lane j is input), keep_j =
// (1 − data_j)·(1 − first), keep_cap = 1 − first, addr_a, addr_b (the two
// data cells), out_addr and out_mult (the digest, written on the last row).
//
// The permutation input is data_j·x_j + keep_j·out_j[−1] on the rate lanes and
// keep_cap·out_j[−1] on the capacity: the state chains from row to row, and a
// trailing partial block keeps the previous state on its unused lanes, as
// loom's overwrite-mode sponge does.
type spongeChip struct{ m *Machine }

func (c spongeChip) name() string { return spongeMod }

func (c spongeChip) rows() int {
	n := 0
	for _, s := range c.m.sponges {
		n += len(s.data) / 2
	}
	return n
}

func (c spongeChip) define(b *board.Builder, bus *Bus) error {
	active := setupCol(spongeMod, spongeActive)
	bus.Read(spongeMod, setupCol(spongeMod, spongeAddrA), cellCols(spongeMod, spongeX, 0), active)
	bus.Read(spongeMod, setupCol(spongeMod, spongeAddrB), cellCols(spongeMod, spongeX, CellWidth), active)
	bus.Write(spongeMod, setupCol(spongeMod, spongeOutAddr), cellCols(spongeMod, spongeOut, 0), setupCol(spongeMod, spongeOutMult))

	src := board.NewTable(spongeMod, 2*width)
	for l := range width {
		prev := colShift(spongeMod, laneName(spongeOut, l), -1)
		if l < rate {
			src.In[l] = setupCol(spongeMod, laneName(spongeData, l)).Mul(col(spongeMod, laneName(spongeX, l))).
				Add(setupCol(spongeMod, laneName(spongeKeep, l)).Mul(prev))
		} else {
			src.In[l] = setupCol(spongeMod, spongeKeepCap).Mul(prev)
		}
		src.In[width+l] = col(spongeMod, laneName(spongeOut, l))
	}
	return arguments.CLookupTuple(b, src, p2Table(width), active, one())
}

func (c spongeChip) setup(cs *cols) {
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

// trace fills the blocks and the chained states, and records the
// permutations for the P2 core.
func (c spongeChip) trace(cs *cols, r *Run) error {
	cs.declareLanes(spongeX, rate)
	cs.declareLanes(spongeOut, width)
	perm := newPerm()
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
			r.p2 = append(r.p2, state)
			if err := perm.Permutation(state[:]); err != nil {
				return err
			}
			for l := range width {
				cs.setElem(laneName(spongeOut, l), row, state[l])
			}
			row++
		}
	}
	return nil
}
