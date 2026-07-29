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

package loom

import (
	"fmt"

	"github.com/consensys/loom/board"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/trace"
	"github.com/consensys/loom/verifier"
)

// Statement contains the verifier-owned public data for one proof instance.
// Proof data produced by the prover, including proof.ExposedValues, does not
// belong here.
type Statement struct {
	Program         board.Program
	VerificationKey VerificationKey
	PublicInputs    PublicInputs
}

// Witness contains prover-owned data used to produce a proof for a Statement.
type Witness struct {
	Trace      trace.Trace
	ProvingKey ProvingKey
}

type PublicInputs = public.Inputs

// ProverOption configures Prove.
type ProverOption = prover.Option

// VerifierOption configures Verify.
type VerifierOption = verifier.Option

// SetupOption configures Setup.
type SetupOption = setup.Option

type HashBackend = fri.HashBackend

type ProvingKey = setup.ProvingKey

type VerificationKey = setup.VerificationKey

func Poseidon2HashBackend() HashBackend {
	return fri.Poseidon2HashBackend()
}

func SHA256HashBackend() HashBackend {
	return fri.SHA256HashBackend()
}

func Blake3HashBackend() HashBackend {
	return fri.Blake3HashBackend()
}

func WithSetupHashBackend(backend HashBackend) SetupOption {
	return setup.WithHashBackend(backend)
}

func WithProverHashBackend(backend HashBackend) ProverOption {
	return prover.WithHashBackend(backend)
}

func WithVerifierHashBackend(backend HashBackend) VerifierOption {
	return verifier.WithHashBackend(backend)
}

// Setup produces the Merkle trees of the precommitted columns + their roots.
func Setup(t trace.Trace, program board.Program, opts ...SetupOption) (ProvingKey, VerificationKey, error) {
	return setup.Setup(t, program, opts...)
}

// Prove produces a proof for statement using witness.
func Prove(statement Statement, witness Witness, opts ...ProverOption) (proof.Proof, error) {
	if err := checkVerificationKey(statement, witness.ProvingKey); err != nil {
		return proof.Proof{}, err
	}
	return prover.Prove(witness.Trace, witness.ProvingKey, statement.PublicInputs, statement.Program, opts...)
}

// Verify checks prf against statement.
func Verify(statement Statement, prf proof.Proof, opts ...VerifierOption) error {
	return verifier.Verify(statement.PublicInputs, statement.VerificationKey, statement.Program, prf, opts...)
}

func checkVerificationKey(statement Statement, witnessKey setup.ProvingKey) error {
	statementKey := statement.VerificationKey
	witnessKeyForVerifier := witnessKey.VerificationKey()
	statementBackend := fri.NormalizeHashBackendID(statementKey.HashBackendID)
	witnessBackend := fri.NormalizeHashBackendID(witnessKeyForVerifier.HashBackendID)
	if statementBackend != witnessBackend {
		return fmt.Errorf("loom: statement uses hash backend %q, witness uses %q", statementBackend, witnessBackend)
	}
	expectedRoots := expectedSetupTreeCount(statement.Program)
	if len(statementKey.Roots) != expectedRoots {
		return fmt.Errorf("loom: statement has %d setup roots, program expects %d setup trees", len(statementKey.Roots), expectedRoots)
	}
	if len(witnessKey.Setup) != expectedRoots {
		return fmt.Errorf("loom: witness has %d setup trees, program expects %d", len(witnessKey.Setup), expectedRoots)
	}
	if len(statementKey.Roots) != len(witnessKeyForVerifier.Roots) {
		return fmt.Errorf("loom: statement has %d setup roots, witness has %d setup trees", len(statementKey.Roots), len(witnessKeyForVerifier.Roots))
	}
	for i := range statementKey.Roots {
		if statementKey.Roots[i] != witnessKeyForVerifier.Roots[i] {
			return fmt.Errorf("loom: statement setup root %d does not match witness setup root", i)
		}
	}
	return nil
}

func expectedSetupTreeCount(program board.Program) int {
	for _, ref := range program.SetupColumns {
		if _, ok := program.Modules[ref.Module]; ok {
			return 1
		}
	}
	return 0
}
