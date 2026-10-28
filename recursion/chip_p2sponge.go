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
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

// Setup columns of the sponge core.
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

// Witness columns of the sponge core, next to the P2 core's s and r lanes.
const spongeX = "x" // lanes

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

// p2SpongeChip: the sponge P2 core, one row per 16-element block of a sponge.
// It carries poseidon2AIR and the sponge's chaining on the same module, so the
// permutation's input and output are committed once rather than once in each
// of two modules tied by a lookup.
//
// Columns: x0..15 (the block, read from two cells), s0..23 and r0..23 (the
// permutation, with the AIR's round columns). Setup: first, last, active,
// data_j (lane j is input), keep_j = (1 − data_j)·(1 − first), keep_cap =
// 1 − first, addr_a, addr_b (the two data cells), out_addr and out_mult (the
// digest, written on the last row).
//
// Beside the AIR, one constraint per lane feeds the permutation:
//
//	s_j = data_j·x_j + keep_j·r_j[−1]   on the rate lanes
//	s_j = keep_cap·r_j[−1]              on the capacity
//
// so the state chains from row to row, and a trailing partial block keeps the
// previous state on its unused lanes, as loom's overwrite-mode sponge does. On
// a padding row every setup lane is zero, so s = 0 and the row is the genuine
// instance P(0); a sponge's first row has keep = keep_cap = 0, so no chain
// crosses a sponge boundary or the module's wrap-around.
type p2SpongeChip struct{ m *Machine }

func (c p2SpongeChip) name() string { return p2sMod }

func (c p2SpongeChip) rows() int {
	n := 0
	for _, s := range c.m.sponges {
		n += len(s.data) / 2
	}
	return n
}

func (c p2SpongeChip) define(b *board.Builder, bus *Bus) error {
	if err := (poseidon2AIR{}).Define(b, p2sMod, p2Ins(p2sMod), p2Outs(p2sMod)); err != nil {
		return err
	}
	mm := b.Modules[p2sMod]
	for l := range width {
		prev := colShift(p2sMod, laneName(p2R, l), -1)
		var in expr.Expr
		if l < rate {
			in = setupCol(p2sMod, laneName(spongeData, l)).Mul(col(p2sMod, laneName(spongeX, l))).
				Add(setupCol(p2sMod, laneName(spongeKeep, l)).Mul(prev))
		} else {
			in = setupCol(p2sMod, spongeKeepCap).Mul(prev)
		}
		mm.AssertZero(col(p2sMod, laneName(p2S, l)).Sub(in))
	}

	active := setupCol(p2sMod, spongeActive)
	bus.Read(p2sMod, setupCol(p2sMod, spongeAddrA), cellCols(p2sMod, spongeX, 0), active)
	bus.Read(p2sMod, setupCol(p2sMod, spongeAddrB), cellCols(p2sMod, spongeX, CellWidth), active)
	bus.Write(p2sMod, setupCol(p2sMod, spongeOutAddr), cellCols(p2sMod, p2R, 0), setupCol(p2sMod, spongeOutMult))
	return nil
}

func (c p2SpongeChip) setup(cs *cols) {
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

// trace fills the blocks and the chained permutations, then the AIR's round
// columns.
func (c p2SpongeChip) trace(cs *cols, r *Run) error {
	cs.declareLanes(spongeX, rate)
	cs.declareLanes(p2S, width)
	cs.declareLanes(p2R, width)
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
			for l := range width {
				cs.setElem(laneName(p2S, l), row, state[l])
			}
			if err := perm.Permutation(state[:]); err != nil {
				return err
			}
			for l := range width {
				cs.setElem(laneName(p2R, l), row, state[l])
			}
			row++
		}
	}
	return fillP2(cs, p2sMod)
}
