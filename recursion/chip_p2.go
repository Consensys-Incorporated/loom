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
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/trace"
)

// Witness columns of the p2 chip.
const (
	p2S = "s" // lanes
	p2R = "r" // lanes
)

// numPerms is the number of Poseidon2 permutations: one per sponge block and
// one per Merkle level.
func (m *Machine) numPerms() int {
	n := 0
	for _, s := range m.sponges {
		n += len(s.data) / 2
	}
	for _, p := range m.paths {
		n += len(p.steps)
	}
	return n
}

func p2Ins() []string {
	res := make([]string, width)
	for i := range res {
		res[i] = p2Mod + "." + laneName(p2S, i)
	}
	return res
}

func p2Outs() []string {
	res := make([]string, width)
	for i := range res {
		res[i] = p2Mod + "." + laneName(p2R, i)
	}
	return res
}

// p2Chip: the P2 core, one row per Poseidon2 permutation of the sponge and
// Merkle chips (their lookup target), constrained by poseidon2AIR. Columns:
// s0..23 (input), r0..23 (output), and the AIR's round columns. No setup, no
// memory access.
type p2Chip struct{ m *Machine }

func (c p2Chip) name() string { return p2Mod }

func (c p2Chip) rows() int { return c.m.numPerms() }

func (c p2Chip) define(b *board.Builder, bus *Bus) error {
	return (poseidon2AIR{}).Define(b, p2Mod, p2Ins(), p2Outs())
}

func (c p2Chip) setup(*cols) {}

// trace fills the permutations recorded by the sponge and Merkle traces, then
// the AIR's round columns.
func (c p2Chip) trace(cs *cols, r *Run) error {
	if len(r.p2) != c.rows() {
		return fmt.Errorf("%d permutations recorded, want %d", len(r.p2), c.rows())
	}
	cs.declareLanes(p2S, width)
	cs.declareLanes(p2R, width)
	perm := newPerm()
	for row, in := range r.p2 {
		out := in
		if err := perm.Permutation(out[:]); err != nil {
			return err
		}
		for i := range width {
			cs.setElem(laneName(p2S, i), row, in[i])
			cs.setElem(laneName(p2R, i), row, out[i])
		}
	}
	// The AIR fills its columns from a trace: run it on these columns and
	// take its own back.
	tmp := trace.New()
	cs.store(tmp, p2Mod)
	if err := (poseidon2AIR{}).Fill(tmp, p2Mod, p2Ins(), p2Outs()); err != nil {
		return err
	}
	for name, v := range tmp.Base {
		cs.vals[strings.TrimPrefix(name, p2Mod+".")] = v
	}
	return nil
}

// p2Table returns the P2 core's lookup target (inputs, then the first nOut
// outputs).
func p2Table(nOut int) board.Table {
	t := board.NewTable(p2Mod, width+nOut)
	for i := range width {
		t.In[i] = col(p2Mod, laneName(p2S, i))
	}
	for i := range nOut {
		t.In[width+i] = col(p2Mod, laneName(p2R, i))
	}
	return t
}

func newPerm() *poseidon2.Permutation { return hash.Poseidon2SpongePermutation() }
