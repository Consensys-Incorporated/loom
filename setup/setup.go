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

package setup

import (
	"fmt"
	"sort"

	"github.com/consensys/loom/board"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/trace"
)

// ProvingKey is the prover-side setup material. Setup contains the per-size
// setup commitments (Merkle tree + retained RS-encoded LeafSources) the prover
// hands to PCS.Open at proof time. Trace contains the fixed columns in
// Lagrange form so the prover can evaluate setup columns without carrying
// them in each witness.
type ProvingKey struct {
	HashBackendID string
	Trace         trace.Trace
	Setup         []fri.Committed
}

// VerificationKey is the verifier-side setup material.
type VerificationKey struct {
	HashBackendID string
	Roots         []hash.Digest // size of at most 1, since the setup outputs a single tree. Leaving it a [] to identify the zero value of the setup
}

// VerificationKey returns the verifier-side roots corresponding to pk.
func (pk ProvingKey) VerificationKey() VerificationKey {
	res := make([]hash.Digest, len(pk.Setup))
	for i, c := range pk.Setup {
		res[i] = c.Tree.Root()
	}
	return VerificationKey{HashBackendID: pk.HashBackendID, Roots: res}
}

type Config struct {
	HashBackend fri.HashBackend
}

type Option func(c *Config) error

func WithHashBackend(backend fri.HashBackend) Option {
	return func(c *Config) error {
		c.HashBackend = backend
		return nil
	}
}

func Setup(t trace.Trace, program board.Program, opts ...Option) (ProvingKey, VerificationKey, error) {
	var config Config
	for _, opt := range opts {
		if err := opt(&config); err != nil {
			return ProvingKey{}, VerificationKey{}, err
		}
	}
	hashBackend, err := fri.ResolveHashBackend(config.HashBackend, "")
	if err != nil {
		return ProvingKey{}, VerificationKey{}, err
	}

	setupTrace, err := setupTraceFromProgram(t, program)
	if err != nil {
		return ProvingKey{}, VerificationKey{}, err
	}

	if len(program.SetupColumns) == 0 {
		pk := ProvingKey{HashBackendID: hashBackend.ID, Trace: setupTrace}
		return pk, pk.VerificationKey(), nil
	}

	// Group setup columns by size in decreasing order, matching BuildLayout.
	// All sizes are committed into a single multi-group tree so the setup
	// section occupies exactly one slot in the canonical layout.
	colsByN := map[int][]board.ColumnRef{}
	for _, c := range program.SetupColumns {
		m, ok := program.Modules[c.Module]
		if !ok {
			continue
		}
		colsByN[m.N] = append(colsByN[m.N], c)
	}
	sizes := make([]int, 0, len(colsByN))
	for n := range colsByN {
		sizes = append(sizes, n)
	}
	sort.Sort(sort.Reverse(sort.IntSlice(sizes)))

	groups := make([]fri.Group, len(sizes))
	for i, N := range sizes {
		refs := colsByN[N]
		sort.Slice(refs, func(i, j int) bool { return refs[i].Name < refs[j].Name })
		var basePolys []poly.Polynomial
		var extPolys []poly.ExtPolynomial
		for _, ref := range refs {
			if ref.Field == field.Base {
				p, ok := setupTrace.Base[ref.Name]
				if !ok {
					return ProvingKey{}, VerificationKey{}, fmt.Errorf("setup: base setup column %q not found", ref.Name)
				}
				basePolys = append(basePolys, p)
			}
		}
		for _, ref := range refs {
			if ref.Field == field.Ext {
				p, ok := setupTrace.Ext[ref.Name]
				if !ok {
					return ProvingKey{}, VerificationKey{}, fmt.Errorf("setup: extension setup column %q not found", ref.Name)
				}
				extPolys = append(extPolys, p)
			}
		}
		groups[i] = fri.Group{Base: basePolys, Ext: extPolys}
		_ = N
	}
	var domainCache poly.DomainCache
	pcs := fri.NewPCS(uint64(constants.RATE), hashBackend.LeafHasher, hashBackend.NodeHasher)
	c, err := pcs.Commit(groups, fri.WithDomainCache(&domainCache))
	if err != nil {
		return ProvingKey{}, VerificationKey{}, err
	}
	pk := ProvingKey{HashBackendID: hashBackend.ID, Trace: setupTrace, Setup: []fri.Committed{c}}
	return pk, pk.VerificationKey(), nil
}

func setupTraceFromProgram(t trace.Trace, program board.Program) (trace.Trace, error) {
	res := trace.New(len(program.SetupColumns))
	for _, ref := range program.SetupColumns {
		switch ref.Field {
		case field.Base:
			p, ok := t.Base[ref.Name]
			if !ok {
				return trace.Trace{}, fmt.Errorf("setup: base setup column %q not found", ref.Name)
			}
			if err := res.PutBase(ref.Name, p); err != nil {
				return trace.Trace{}, err
			}
		case field.Ext:
			p, ok := t.Ext[ref.Name]
			if !ok {
				return trace.Trace{}, fmt.Errorf("setup: extension setup column %q not found", ref.Name)
			}
			if err := res.PutExt(ref.Name, p); err != nil {
				return trace.Trace{}, err
			}
		default:
			return trace.Trace{}, fmt.Errorf("setup: unsupported field kind for setup column %q", ref.Name)
		}
	}
	return res, nil
}
