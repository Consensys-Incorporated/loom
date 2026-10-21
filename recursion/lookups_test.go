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
	"testing"
)

// TestP2LookupsShareTargets: the sponge looks its permutations up into the
// P2 core's full outputs, the Merkle and dynamic-path chips their
// compressions into its digests: two targets, so two multiplicity columns,
// the Merkle and dynamic-path chips sharing theirs.
func TestP2LookupsShareTargets(t *testing.T) {
	b := dpathCircuit(dpathTree(t, []int{5, 3, 3, 2}, 0))
	d := func() int { return b.InputDigest() }
	b.MerklePath(d(), []int{d(), d()}, b.InputScalar(), d())
	b.Sponge([]int{b.InputScalar(), b.InputScalar()}, 2)
	p, err := b.Compile()
	if err != nil {
		t.Fatal(err)
	}
	mults := 0
	for _, r := range p.Loom.Rounds {
		for _, c := range r.Staged {
			if strings.Contains(c.Name, "Mult_") {
				mults++
			}
		}
	}
	if mults != 2 {
		t.Fatalf("%d multiplicity columns, want 2", mults)
	}
}
