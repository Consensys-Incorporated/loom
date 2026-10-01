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

package fri

import (
	"testing"

	"github.com/consensys/loom/internal/hash"
)

// Every level is combined with the others, so every γ must come after the
// commitment to all the levels: the first γ binds the levels root, and the
// next ones chain on it.
func TestLevelGammasBindLevelsRoot(t *testing.T) {
	gammasOf := func(root hash.Digest) [][8]uint64 {
		p, err := NewParams(64, 16, 2, DefaultLeafHasher, DefaultNodeHasher, WoFullDomainAllocation())
		if err != nil {
			t.Fatal(err)
		}
		ts := freshTranscriptForTest()
		registerChallenges(p, 3, ts)
		cs, err := deriveLevelGammas(ts, 3, root)
		if err != nil {
			t.Fatal(err)
		}
		res := make([][8]uint64, len(cs))
		for l, c := range cs {
			for i := range c {
				res[l][i] = c[i].Uint64()
			}
		}
		return res
	}
	var a, b hash.Digest
	a[0].SetUint64(1)
	b[0].SetUint64(2)
	ga, gb := gammasOf(a), gammasOf(b)
	for l := 1; l < 3; l++ {
		if ga[l] == gb[l] {
			t.Fatalf("γ_%d does not depend on the levels root", l)
		}
	}
}
