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
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/trace"
)

// Witness columns of a P2 core: the permutation's input and output lanes. The
// AIR's round columns sit next to them, see poseidon2AIR.
const (
	p2S = "s" // lanes
	p2R = "r" // lanes
)

// There are two P2 cores, each carrying poseidon2AIR on its own module and
// the control of the single chip that feeds it: the sponge's chaining (p2s)
// and the Merkle path's (p2m). Keeping them apart is what makes merging pay:
// one core holding both chips' control would pay the union of their setup and
// witness columns on all of its rows, instead of each on its own rows.
//
// p2m is also the lookup target of the dynamic-path chip, whose compressions
// occupy the rows after the Merkle paths', with the Merkle control inactive.

func p2Ins(module string) []string {
	res := make([]string, width)
	for i := range res {
		res[i] = module + "." + laneName(p2S, i)
	}
	return res
}

func p2Outs(module string) []string {
	res := make([]string, width)
	for i := range res {
		res[i] = module + "." + laneName(p2R, i)
	}
	return res
}

// p2Table returns a core's lookup target (inputs, then the first nOut
// outputs).
func p2Table(module string, nOut int) board.Table {
	t := board.NewTable(module, width+nOut)
	for i := range width {
		t.In[i] = col(module, laneName(p2S, i))
	}
	for i := range nOut {
		t.In[width+i] = col(module, laneName(p2R, i))
	}
	return t
}

// fillP2 fills the AIR's round columns of a core from its traced inputs and
// outputs. The AIR fills its columns from a trace: run it on these columns and
// take its own back. Rows whose inputs and outputs are all zero are padding:
// the AIR makes them the genuine instance P(0).
func fillP2(cs *cols, module string) error {
	tmp := trace.New()
	cs.store(tmp, module)
	if err := (poseidon2AIR{}).Fill(tmp, module, p2Ins(module), p2Outs(module)); err != nil {
		return err
	}
	for name, v := range tmp.Base {
		cs.vals[strings.TrimPrefix(name, module+".")] = v
	}
	return nil
}

func newPerm() *poseidon2.Permutation { return hash.Poseidon2SpongePermutation() }
