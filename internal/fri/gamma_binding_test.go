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

// A level entering at round 0 is combined with level 0, whose root is
// otherwise bound only at fri_fold_0, after the level's γ. The γ must depend
// on level 0's root, or the prover could choose level 0 after seeing γ.
func TestRound0GammaBindsLevel0Root(t *testing.T) {
	gammaOf := func(root0 hash.Digest) [8]uint64 {
		p, err := NewParams(64, 16, 2, DefaultLeafHasher, DefaultNodeHasher, WoFullDomainAllocation())
		if err != nil {
			t.Fatal(err)
		}
		ts := freshTranscriptForTest()
		levelAtRound := map[int][]int{0: {1}}
		registerChallenges(p, levelAtRound, ts)
		var root1 hash.Digest
		root1[0].SetUint64(11)
		c, err := deriveLevelGamma(ts, 1, root1, true, root0)
		if err != nil {
			t.Fatal(err)
		}
		var res [8]uint64
		for i := range c {
			res[i] = c[i].Uint64()
		}
		return res
	}
	var a, b hash.Digest
	a[0].SetUint64(1)
	b[0].SetUint64(2)
	if gammaOf(a) == gammaOf(b) {
		t.Fatal("the round-0 γ does not depend on level 0's root")
	}
}
