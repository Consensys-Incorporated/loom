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

package proof

import (
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
)

type Commitment struct {
	// Digest  commitment.Digest
	Columns []string
}

// Proof is the prover's output for one statement. Setup roots and per-tree
// shapes are not stored here -- they live in the verifier's
// VerificationKey / Statement. Likewise, claimed-value translation back
// into a canonical-key (leaf.String()) map is the verifier's local
// responsibility; the proof itself carries values inside Opening only.
type Proof struct {
	HashBackendID string

	// ExposedValues are the prover-produced public values reconstructed by
	// the verifier at zeta (e.g. accumulator last entries).
	ExposedValues ExposedValues

	// Commitments holds the Merkle roots of every WMerkleTree the prover
	// commits during the protocol, in canonical order:
	//   trace-round-0 → trace-round-1 → … → trace-round-{r-1} → AIR
	// Each root is a mixed-height tree with one group per module, in sorted
	// module order; setup roots are NOT stored here, they live in the
	// verifier's VerificationKey.
	Commitments []hash.Digest

	// Opening is the multi-degree FRI opening proof for the canonical
	// batch order (setup → trace rounds → AIR). It bundles the claimed
	// values at zeta + shifts, the per-size DEEP-quotient roots, the
	// multi-degree FRI proof, and the per-query Merkle openings.
	Opening fri.OpeningProof
}

func NewProof() Proof {
	var res Proof
	res.ExposedValues = make(map[string]ExposedValue)
	return res
}
