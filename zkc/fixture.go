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

package zkc

import (
	"fmt"
	"math/rand/v2"

	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/internal/constants"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/poly"
)

// ZetaName is the fixture's first transcript challenge: it binds every batch
// root, as loom's "__zeta" binds the AIR roots. alpha_DEEP and the FRI
// challenges follow it.
const ZetaName = "zeta"

// GroupConfig describes one group of a batch: NumBase base and NumExt
// extension polynomials of size 2^LogN, each opened at zeta·ω^s for every s in
// Shifts.
type GroupConfig struct {
	LogN    int
	NumBase int
	NumExt  int
	Shifts  []int
}

// BatchConfig is one committed batch, i.e. one mixed-size Merkle tree. Its
// groups must have distinct sizes.
type BatchConfig []GroupConfig

// FixtureConfig describes a PCS opening to verify.
type FixtureConfig struct {
	Batches    []BatchConfig
	NumQueries int
	Seed       uint64
}

// Fixture is a PCS opening produced by loom's prover and accepted by loom's
// Go verifier.
type Fixture struct {
	Config FixtureConfig
	Params fri.Params
	Roots  []hash.Digest
	Shapes []fri.BatchShapes
	Shifts []fri.BatchShifts
	Zeta   ext.E6
	Proof  fri.OpeningProof
}

// maxLogN returns the log size of the largest group.
func (c FixtureConfig) maxLogN() int {
	m := 0
	for _, b := range c.Batches {
		for _, g := range b {
			m = max(m, g.LogN)
		}
	}
	return m
}

// NewFixture commits random polynomials with loom's PCS, derives zeta from the
// batch roots, opens, and checks the opening with the Go verifier.
func NewFixture(cfg FixtureConfig) (*Fixture, error) {
	rng := rand.New(rand.NewPCG(cfg.Seed, 0x7a6b63))
	maxN := 1 << cfg.maxLogN()
	params, err := fri.NewParams(constants.RATE*maxN, maxN, cfg.NumQueries,
		fri.DefaultLeafHasher, fri.DefaultNodeHasher)
	if err != nil {
		return nil, err
	}
	pcs := fri.NewPCSWithParams(params)

	batches := make([]fri.Batch, len(cfg.Batches))
	shifts := make([]fri.BatchShifts, len(cfg.Batches))
	committed := make([]fri.Committed, len(cfg.Batches))
	for b, bc := range cfg.Batches {
		batches[b] = make(fri.Batch, len(bc))
		shifts[b] = make(fri.BatchShifts, len(bc))
		for g, gc := range bc {
			n := 1 << gc.LogN
			group := &batches[b][g]
			gs := &shifts[b][g]
			for range gc.NumBase {
				p := make(poly.Polynomial, n)
				for i := range p {
					p[i].SetUint64(rng.Uint64())
				}
				group.Base = append(group.Base, p)
				gs.Base = append(gs.Base, append([]int(nil), gc.Shifts...))
			}
			for range gc.NumExt {
				p := make(poly.ExtPolynomial, n)
				for i := range p {
					p[i] = randE6(rng)
				}
				group.Ext = append(group.Ext, p)
				gs.Ext = append(gs.Ext, append([]int(nil), gc.Shifts...))
			}
		}
		if committed[b], err = pcs.Commit(batches[b]); err != nil {
			return nil, fmt.Errorf("commit batch %d: %w", b, err)
		}
	}

	roots := make([]hash.Digest, len(committed))
	shapes := make([]fri.BatchShapes, len(committed))
	for b, c := range committed {
		roots[b] = c.Tree.Root()
		shapes[b] = c.Shapes
	}

	proverFS, zeta, err := zetaTranscript(roots)
	if err != nil {
		return nil, err
	}
	proof, err := pcs.Open(batches, committed, shifts, zeta, proverFS)
	if err != nil {
		return nil, fmt.Errorf("open: %w", err)
	}

	verifierFS, _, err := zetaTranscript(roots)
	if err != nil {
		return nil, err
	}
	if err := pcs.Verify(roots, shapes, shifts, zeta, proof, verifierFS); err != nil {
		return nil, fmt.Errorf("go verifier rejects the fixture: %w", err)
	}

	return &Fixture{
		Config: cfg,
		Params: params,
		Roots:  roots,
		Shapes: shapes,
		Shifts: shifts,
		Zeta:   zeta,
		Proof:  proof,
	}, nil
}

// zetaTranscript returns a transcript in which ZetaName, bound to every root,
// has been computed, and zeta as an extension element.
func zetaTranscript(roots []hash.Digest) (*fiatshamir.Transcript, ext.E6, error) {
	h := hash.NewPoseidon2SpongeHasher()
	fs := fiatshamir.NewTranscript(&h, ZetaName)
	for _, r := range roots {
		if err := fs.Bind(ZetaName, r[:]); err != nil {
			return nil, ext.E6{}, err
		}
	}
	d, err := fs.ComputeChallenge(ZetaName)
	if err != nil {
		return nil, ext.E6{}, err
	}
	return fs, hash.OutputToExt(d), nil
}
