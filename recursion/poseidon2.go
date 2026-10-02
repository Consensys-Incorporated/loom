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
	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
)

// Poseidon2 parameters of loom's sponge and Merkle node hasher
// (internal/hash): width 24, 6 full rounds, 21 partial rounds, x^3, rate 16,
// digest 8; and the Merkle domain tags (internal/fri).
const (
	P2Width          = hash.SPONGE_WIDTH
	P2FullRounds     = hash.NB_FULL_ROUND
	P2PartialRounds  = hash.NB_PARTIAL_ROUNDS
	p2HalfFullRounds = P2FullRounds / 2
	P2Rate           = hash.SPONGE_RATE
	P2Digest         = hash.DIGEST_NB_ELEMENTS

	LeafDomainTag = fri.LeafDomainTag
	NodeDomainTag = fri.NodeDomainTag
)

// The internal matrix diagonal and the linear layers below repeat
// gnark-crypto's (field/koalabear/poseidon2), which does not export them; the
// AIR needs them as constraint coefficients. TestPoseidon2AIR proves
// the AIR against gnark-crypto's permutation, so a drift would fail it.

// p2Diag24 is the diagonal of the width-24 internal matrix, M = 1·1ᵀ + diag,
// as used by gnark-crypto's matMulInternalInPlace.
func p2Diag24() []koalabear.Element {
	var d [P2Width]koalabear.Element
	pow2Inv := func(n int) koalabear.Element {
		var r koalabear.Element
		r.SetUint64(1 << n)
		r.Inverse(&r)
		return r
	}
	set := func(i int, v int64) {
		d[i].SetInt64(v)
	}
	set(0, -2)
	set(1, 1)
	set(2, 2)
	d[3] = pow2Inv(1)
	set(4, 3)
	set(5, 4)
	d[6] = pow2Inv(1)
	d[6].Neg(&d[6])
	set(7, -3)
	set(8, -4)
	for i, n := range []int{8, 2, 3, 4, 5, 6, 24} {
		d[9+i] = pow2Inv(n)
	}
	for i, n := range []int{8, 3, 4, 5, 6, 7, 9, 24} {
		d[16+i] = pow2Inv(n)
		d[16+i].Neg(&d[16+i])
	}
	return d[:]
}
