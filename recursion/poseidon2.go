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

import "github.com/consensys/gnark-crypto/field/koalabear"

// Poseidon2 parameters of loom's sponge and Merkle node hasher
// (internal/hash/hash.go): width 24, 6 full rounds, 21 partial rounds, x^3.
const (
	P2Width          = 24
	P2FullRounds     = 6
	P2PartialRounds  = 21
	p2HalfFullRounds = P2FullRounds / 2

	// P2Rate and P2Digest are the sponge rate and digest size of loom's
	// Poseidon2 sponge (internal/hash/poseidon2.go).
	P2Rate   = 16
	P2Digest = 8

	// Domain tags of loom's Merkle leaves and nodes (internal/fri/commitment.go).
	LeafDomainTag uint64 = 0x4c454146 // "LEAF"
	NodeDomainTag uint64 = 0x4e4f4445 // "NODE"
)

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
