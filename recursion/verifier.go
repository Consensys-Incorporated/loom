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
	"fmt"
	"sort"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/protocol"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
)

// Shape is what, besides the program and the verification key, fixes the
// circuit of a verifier: the structure of the public inputs and of the
// exposed values. Their indices and values are inputs of each execution.
type Shape struct {
	// PublicInputs, sorted by name.
	PublicInputs []PublicInputShape
	// ExposedEntries is the number of entries of every exposed value.
	ExposedEntries map[string]int
}

// PublicInputShape is the structure of one public input: its name, module and
// the fields of its entries, in their transcript order (Input.SortedEntries).
type PublicInputShape struct {
	Name, Module string
	Fields       []field.Kind
}

// ShapeOf returns the shape of a proof and its public inputs.
func ShapeOf(prf proof.Proof, pi public.Inputs) Shape {
	s := Shape{ExposedEntries: map[string]int{}}
	for name, v := range prf.ExposedValues {
		s.ExposedEntries[name] = len(v.Entries)
	}
	names := make([]string, 0, len(pi))
	for name := range pi {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		ps := PublicInputShape{Name: name, Module: pi[name].Module}
		for _, e := range pi[name].SortedEntries() {
			ps.Fields = append(ps.Fields, e.Field)
		}
		s.PublicInputs = append(s.PublicInputs, ps)
	}
	return s
}

// Verifier is the circuit of loom's verifier for one program (fixed module
// sizes), verification key and shape, on its own Machine. Build it once with
// NewVerifier, then Compile its Machine, and execute it on the inputs of
// every proof (Inputs).
type Verifier struct {
	M       *Machine
	program board.Program
	vk      setup.VerificationKey
	shape   Shape
	layout  protocol.Layout

	// extract[i] reads, from a proof and its public inputs, the value of the
	// i-th input cell.
	extract []func(prf proof.Proof, pi public.Inputs) (Cell, error)

	tr *Transcript
	// Challenges holds the digest cell of every challenge computed so far.
	Challenges map[string]int
	// roots[t] is the root cell of tree t of the layout.
	roots []int
}

// NewVerifier builds the circuit verifying loom proofs of program under vk,
// for proofs of the given shape.
func NewVerifier(program board.Program, vk setup.VerificationKey, shape Shape) (*Verifier, error) {
	backend, err := fri.ResolveHashBackend(fri.HashBackend{}, vk.HashBackendID)
	if err != nil {
		return nil, err
	}
	if backend.ID != fri.HashBackendPoseidon2 {
		return nil, fmt.Errorf("NewVerifier: hash backend %q, the circuit hashes with %q", backend.ID, fri.HashBackendPoseidon2)
	}
	v := &Verifier{
		M:          &Machine{},
		program:    program,
		vk:         vk,
		shape:      shape,
		layout:     protocol.BuildLayout(program, len(vk.Roots)),
		Challenges: map[string]int{},
	}
	if len(vk.Roots) != v.layout.SetupEnd-v.layout.SetupBegin {
		return nil, fmt.Errorf("NewVerifier: %d setup roots, the layout has %d setup trees", len(vk.Roots), v.layout.SetupEnd-v.layout.SetupBegin)
	}
	if err := v.buildTranscript(backend.ID); err != nil {
		return nil, err
	}
	return v, nil
}

// input allocates an input cell whose value extract reads from each proof.
func (v *Verifier) input(extract func(prf proof.Proof, pi public.Inputs) (Cell, error)) int {
	v.extract = append(v.extract, extract)
	return v.M.Input()
}

// Inputs returns the input cells' values for a proof and its public inputs,
// in the order of the Machine's inputs.
func (v *Verifier) Inputs(prf proof.Proof, pi public.Inputs) ([]Cell, error) {
	res := make([]Cell, len(v.extract))
	for i, f := range v.extract {
		c, err := f(prf, pi)
		if err != nil {
			return nil, err
		}
		res[i] = c
	}
	return res, nil
}

// digestCell returns the cell of a digest.
func digestCell(d hash.Digest) Cell {
	var c Cell
	copy(c[:], d[:])
	return c
}

// buildTranscript replays loom's transcript up to zeta: the initial
// challenge (hash backend, module sizes, setup roots, public inputs), then
// every round (its roots, then its exposed values), then zeta (the AIR
// roots). It mirrors verifier.newVerifierRuntime and deriveChallenges.
func (v *Verifier) buildTranscript(backendID string) error {
	m, l := v.M, v.layout
	numRounds := len(v.program.Rounds)
	names := make([]string, 0, numRounds+1)
	for r := range numRounds {
		names = append(names, constants.CanonicalChallengeName(r))
	}
	names = append(names, constants.FINAL_EVALUATION_POINT)
	v.tr = NewTranscript(m, names...)

	// The tree roots: the setup roots are constants of the verifier, the
	// others proof values.
	v.roots = make([]int, l.NumTrees)
	for i, r := range v.vk.Roots {
		v.roots[l.SetupBegin+i] = m.Const(digestCell(r))
	}
	for t := l.SetupEnd; t < l.NumTrees; t++ {
		i := t - l.SetupEnd
		v.roots[t] = v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
			if i >= len(prf.Commitments) {
				return Cell{}, fmt.Errorf("proof has %d commitments, want more than %d", len(prf.Commitments), i)
			}
			return digestCell(prf.Commitments[i]), nil
		})
	}

	initial := constants.InitialChallengeName(numRounds)
	v.tr.BindElements(initial, hash.StringToElements(constants.HASH_BACKEND_DOMAIN_TAG, backendID))
	v.tr.BindElements(initial, protocol.ModuleSizesTranscript(v.program))
	for t := l.SetupBegin; t < l.SetupEnd; t++ {
		v.tr.Bind(initial, Digest(v.roots[t]))
	}
	if len(v.shape.PublicInputs) > 0 {
		v.bindPublicInputs(initial)
	}

	for r, round := range v.program.Rounds {
		name := constants.CanonicalChallengeName(r)
		for t := l.TraceBegin[r]; t < l.TraceEnd[r]; t++ {
			v.tr.Bind(name, Digest(v.roots[t]))
		}
		switch round.FSHook {
		case board.NoFSHook:
		case board.BindExposedValues:
			for _, ev := range round.ExposedValueNames() {
				if err := v.bindExposedValue(name, ev); err != nil {
					return err
				}
			}
		default:
			return fmt.Errorf("NewVerifier: round %d: FS hook %d is not supported", r, round.FSHook)
		}
		v.Challenges[name] = v.tr.Compute(name)
	}

	for t := l.AIRBegin; t < l.AIREnd; t++ {
		v.tr.Bind(constants.FINAL_EVALUATION_POINT, Digest(v.roots[t]))
	}
	v.Challenges[constants.FINAL_EVALUATION_POINT] = v.tr.Compute(constants.FINAL_EVALUATION_POINT)
	return nil
}

// bindPublicInputs binds the public inputs as public.Inputs.TranscriptElements
// encodes them: the names, modules, entry counts and fields are constants of
// the shape; the entries' indices and values are inputs.
func (v *Verifier) bindPublicInputs(name string) {
	ps := v.shape.PublicInputs
	v.tr.BindElements(name, []koalabear.Element{hash.NewElement(public.DomainTag), hash.NewElement(uint64(len(ps)))})
	for _, p := range ps {
		v.tr.BindElements(name, hash.StringToElements(public.DomainTag, p.Name))
		v.tr.BindElements(name, hash.StringToElements(public.DomainTag, p.Module))
		v.tr.BindElements(name, []koalabear.Element{hash.NewElement(uint64(len(p.Fields)))})
		for k, f := range p.Fields {
			entry := func(pi public.Inputs) (public.Entry, error) {
				in, ok := pi[p.Name]
				if !ok {
					return public.Entry{}, fmt.Errorf("public input %q missing", p.Name)
				}
				es := in.SortedEntries()
				if len(es) != len(p.Fields) || es[k].Field != f {
					return public.Entry{}, fmt.Errorf("public input %q does not have the verifier's shape", p.Name)
				}
				return es[k], nil
			}
			idx := v.input(func(_ proof.Proof, pi public.Inputs) (Cell, error) {
				e, err := entry(pi)
				return ScalarCell(koalabear.NewElement(uint64(e.Idx))), err
			})
			v.tr.Bind(name, Scalar(idx))
			v.tr.BindElements(name, []koalabear.Element{hash.NewElement(uint64(f))})
			val := v.input(func(_ proof.Proof, pi public.Inputs) (Cell, error) {
				e, err := entry(pi)
				if f == field.Ext {
					return E6Cell(e.ValueExt), err
				}
				return ScalarCell(e.Value), err
			})
			if f == field.Ext {
				v.tr.Bind(name, E6(val))
			} else {
				v.tr.Bind(name, Scalar(val))
			}
		}
	}
}

// bindExposedValue binds an exposed value as board.ExposedValueElements
// encodes it: for each entry, its index, then its value as an E6.
func (v *Verifier) bindExposedValue(challenge, name string) error {
	n, ok := v.shape.ExposedEntries[name]
	if !ok {
		return fmt.Errorf("NewVerifier: the shape has no exposed value %q", name)
	}
	for k := range n {
		entry := func(prf proof.Proof) (proof.ExposedEntry, error) {
			ev, ok := prf.ExposedValues[name]
			if !ok || len(ev.Entries) != n {
				return proof.ExposedEntry{}, fmt.Errorf("exposed value %q does not have the verifier's shape", name)
			}
			return ev.Entries[k], nil
		}
		idx := v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
			e, err := entry(prf)
			return ScalarCell(koalabear.NewElement(uint64(e.Idx))), err
		})
		val := v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
			e, err := entry(prf)
			return E6Cell(e.ExtValue()), err
		})
		v.tr.Bind(challenge, Scalar(idx), E6(val))
	}
	return nil
}

// ChallengeE6 returns a cell holding the E6 value of a computed challenge
// (lanes 0..5 of its digest, as hash.OutputToExt).
func (v *Verifier) ChallengeE6(name string) int {
	d, ok := v.Challenges[name]
	if !ok {
		panic(fmt.Sprintf("ChallengeE6: challenge %q not computed", name))
	}
	return v.M.Lanes(d, 0, KindE6)
}
