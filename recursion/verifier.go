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
	// NumQueries is the number of FRI queries.
	NumQueries int
}

// PublicInputShape is the structure of one public input: its name, module and
// the fields of its entries, in their transcript order (Input.SortedEntries).
type PublicInputShape struct {
	Name, Module string
	Fields       []field.Kind
}

// ShapeOf returns the shape of a proof and its public inputs.
func ShapeOf(prf proof.Proof, pi public.Inputs) Shape {
	s := Shape{ExposedEntries: map[string]int{}, NumQueries: len(prf.Opening.FRIProof.FRIQueries)}
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
	sched   protocol.CanonicalSchedule

	// extract[i] reads, from a proof and its public inputs, the value of the
	// i-th input cell.
	extract []func(prf proof.Proof, pi public.Inputs) (Cell, error)

	tr *Transcript
	// Challenges holds the digest cell of every challenge computed so far.
	Challenges map[string]int
	// roots[t] is the root cell of tree t of the layout.
	roots []int

	// Claimed[t][g] holds the cells of the claimed values of group g of tree
	// t: Base[i][k] is the E6 value of base polynomial i at its k-th shift,
	// Ext[i][k] likewise (the shapes of the canonical schedule).
	Claimed [][]ClaimedCells
	// FRI: the levels root, the layer roots T_1..T_{r−1}, the final
	// polynomial's coefficients, and the query indices (Queries[k].Shr[0] is
	// the full-domain row s of query k).
	LevelsRoot int
	FRIRoots   []int
	Final      []int
	Queries    []Bits
	fri        friShape
}

// ClaimedCells holds the claimed-value cells of one group.
type ClaimedCells struct {
	Base, Ext [][]int
}

// friShape is the FRI configuration of the verified proofs: domain size N =
// RATE·max N_m, numRounds = log2(max N_m), one level per DEEP class.
type friShape struct {
	logN, numRounds, numLevels int
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
	v.sched = protocol.BuildCanonicalSchedule(program, v.layout)
	if len(vk.Roots) != v.layout.SetupEnd-v.layout.SetupBegin {
		return nil, fmt.Errorf("NewVerifier: %d setup roots, the layout has %d setup trees", len(vk.Roots), v.layout.SetupEnd-v.layout.SetupBegin)
	}
	if err := v.buildTranscript(backend.ID); err != nil {
		return nil, err
	}
	if err := v.buildPCSTranscript(); err != nil {
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

// buildPCSTranscript replays the PCS's transcript (fri.PCS.Verify then
// fri.Verify): alpha_DEEP over the claimed values in DEEP class order, the
// level γs (the first one binds the levels root), the fold challenges (each
// binds its layer root), the final polynomial (bound to the first query),
// the query chain; and decomposes each query challenge into its row.
func (v *Verifier) buildPCSTranscript() error {
	m, l := v.M, v.layout

	// FRI's shape: the domain of the largest module, one level per class.
	maxN := 0
	for _, mod := range v.program.Modules {
		maxN = max(maxN, mod.N)
	}
	classes := l.DeepClasses()
	ids := map[int]bool{}
	for _, tc := range classes {
		for _, c := range tc {
			ids[c] = true
		}
	}
	order := make([]int, 0, len(ids))
	for c := range ids {
		order = append(order, c)
	}
	sort.Ints(order)
	v.fri = friShape{logN: log2(constants.RATE * maxN), numRounds: log2(maxN), numLevels: len(order)}
	if v.fri.logN >= BitsWidth {
		return fmt.Errorf("NewVerifier: FRI domain 2^%d is too large for the query decomposition", v.fri.logN)
	}

	// alpha_DEEP: the claimed values, class by class, then by tree, group,
	// base polynomials then extension ones, shifts in order.
	v.tr.NewChallenge(fri.DeepAlphaName)
	v.Claimed = make([][]ClaimedCells, l.NumTrees)
	for t := range l.NumTrees {
		v.Claimed[t] = make([]ClaimedCells, len(v.sched.Shifts[t]))
		for g, gs := range v.sched.Shifts[t] {
			v.Claimed[t][g] = ClaimedCells{Base: v.claimedInputs(t, g, false, gs.Base), Ext: v.claimedInputs(t, g, true, gs.Ext)}
		}
	}
	for _, class := range order {
		for t := range l.NumTrees {
			for g := range v.Claimed[t] {
				if classes[t][g] != class {
					continue
				}
				for _, rail := range [][][]int{v.Claimed[t][g].Base, v.Claimed[t][g].Ext} {
					for _, cells := range rail {
						for _, c := range cells {
							v.tr.Bind(fri.DeepAlphaName, E6(c))
						}
					}
				}
			}
		}
	}
	v.Challenges[fri.DeepAlphaName] = v.tr.Compute(fri.DeepAlphaName)

	// FRI's challenges, registered as fri.Verify does.
	for lvl := 1; lvl < v.fri.numLevels; lvl++ {
		v.tr.NewChallenge(fri.LevelGammaName(lvl))
	}
	for j := range v.fri.numRounds {
		v.tr.NewChallenge(fri.FoldName(j))
	}
	for k := range v.shape.NumQueries {
		v.tr.NewChallenge(fri.QueryName(k))
	}

	friProof := func(prf proof.Proof) (fri.Proof, error) {
		fp := prf.Opening.FRIProof
		if len(fp.PoW) > 0 {
			return fp, fmt.Errorf("the FRI proof has proofs of work: grinding is not supported")
		}
		if len(fp.FRIRoots) != v.fri.numRounds-1 || len(fp.FinalPolyExt) != 1<<(v.fri.logN-v.fri.numRounds) {
			return fp, fmt.Errorf("the FRI proof does not have the verifier's shape")
		}
		return fp, nil
	}
	v.LevelsRoot = v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
		fp, err := friProof(prf)
		return digestCell(fp.LevelsRoot), err
	})
	for lvl := 1; lvl < v.fri.numLevels; lvl++ {
		name := fri.LevelGammaName(lvl)
		if lvl == 1 {
			v.tr.Bind(name, Digest(v.LevelsRoot))
		}
		v.Challenges[name] = v.tr.Compute(name)
	}
	for j := range v.fri.numRounds {
		root := v.LevelsRoot
		if j > 0 {
			i := j - 1
			root = v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
				fp, err := friProof(prf)
				if err != nil {
					return Cell{}, err
				}
				return digestCell(fp.FRIRoots[i]), nil
			})
			v.FRIRoots = append(v.FRIRoots, root)
		}
		v.tr.Bind(fri.FoldName(j), Digest(root))
		v.Challenges[fri.FoldName(j)] = v.tr.Compute(fri.FoldName(j))
	}

	// The final polynomial: the tag and its length, then its coefficients.
	nFinal := 1 << (v.fri.logN - v.fri.numRounds)
	v.tr.BindElements(fri.QueryName(0), []koalabear.Element{hash.NewElement(fri.ExtPolyDomainTag), hash.NewElement(uint64(nFinal))})
	for i := range nFinal {
		c := v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
			fp, err := friProof(prf)
			if err != nil {
				return Cell{}, err
			}
			return E6Cell(fp.FinalPolyExt[i]), nil
		})
		v.Final = append(v.Final, c)
		v.tr.Bind(fri.QueryName(0), E6(c))
	}

	// The queries: each binds the previous one's digest, and its row is
	// queryIndex = ((c0 << 31) ^ c1) mod N, the low log2(N) bits of lane 1
	// since N ≤ 2^31.
	for k := range v.shape.NumQueries {
		name := fri.QueryName(k)
		if k > 0 {
			v.tr.Bind(name, Digest(v.Challenges[fri.QueryName(k-1)]))
		}
		d := v.tr.Compute(name)
		v.Challenges[name] = d
		v.Queries = append(v.Queries, m.Bits(m.Lanes(d, 1, KindScalar), v.fri.logN))
	}
	return nil
}

// claimedInputs allocates the claimed-value inputs of one rail of group g of
// tree t: one E6 cell per polynomial and shift.
func (v *Verifier) claimedInputs(t, g int, extRail bool, shifts [][]int) [][]int {
	res := make([][]int, len(shifts))
	for i, ss := range shifts {
		for k := range ss {
			res[i] = append(res[i], v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
				cv := prf.Opening.ClaimedValues
				if t >= len(cv) || g >= len(cv[t]) {
					return Cell{}, fmt.Errorf("claimed values do not have the verifier's shape")
				}
				rail := cv[t][g].Base
				if extRail {
					rail = cv[t][g].Ext
				}
				if i >= len(rail) || len(rail[i]) != len(ss) {
					return Cell{}, fmt.Errorf("claimed values do not have the verifier's shape")
				}
				return E6Cell(rail[i][k]), nil
			}))
		}
	}
	return res
}

func log2(n int) int {
	k := 0
	for n > 1 {
		n >>= 1
		k++
	}
	return k
}
