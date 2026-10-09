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
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/dag"
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

	// Openings[k][t][g] holds the cells of the row pair of group g of tree t
	// opened at query k (groups in declaration order).
	Openings [][][]RowPair

	// DEEP[k][c] holds the cells of DQ_c(X) and DQ_c(−X) at query k, for the
	// DEEP class c (class order), X the point of the class's opened pair.
	DEEP [][][2]int

	// The entries of the public inputs and of the exposed values, by name: a
	// scalar index cell and a value cell each (E6 for exposed values).
	publicEntries  map[string][]entryCells
	exposedEntries map[string][]entryCells
}

// entryCells are the cells of one indexed entry.
type entryCells struct {
	idx, val int
}

// RowPair holds the cells of an opened row pair: the rows lo and hi = lo + 1.
type RowPair struct {
	Lo, Hi Row
}

// Row holds the cells of one opened row: the NBase base values packed
// CellWidth per cell in Base (the last cell partial, zero padded), and an E6
// cell per extension column in Ext.
type Row struct {
	Base, Ext []int
	NBase     int
}

// ClaimedCells holds the claimed-value cells of one group.
type ClaimedCells struct {
	Base, Ext [][]int
}

// friShape is the FRI configuration of the verified proofs: domain size N =
// RATE·max N_m, numRounds = log2(max N_m), one level per DEEP class.
type friShape struct {
	logN, numRounds, numLevels int
	// The DEEP classes (fri.WithDeepClasses: one per module), in class order:
	// classOf[t][g] is the class of group g of tree t, classN[c] its size,
	// levelOf[c] its FRI level (levels by decreasing size, stably).
	classOf [][]int
	classN  []int
	levelOf []int
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

		publicEntries:  map[string][]entryCells{},
		exposedEntries: map[string][]entryCells{},
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
	v.buildOpenings()
	v.buildDEEP()
	if err := v.buildFRI(); err != nil {
		return nil, err
	}
	if err := v.buildAIR(); err != nil {
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
			v.publicEntries[p.Name] = append(v.publicEntries[p.Name], entryCells{idx, val})
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
		v.exposedEntries[name] = append(v.exposedEntries[name], entryCells{idx, val})
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
	dense := map[int]int{}
	for i, id := range order {
		dense[id] = i
	}
	v.fri.classN = make([]int, len(order))
	v.fri.classOf = make([][]int, len(classes))
	for t, tc := range classes {
		v.fri.classOf[t] = make([]int, len(tc))
		for g, id := range tc {
			c := dense[id]
			v.fri.classOf[t][g] = c
			v.fri.classN[c] = l.TreeGroups[t][g].N
		}
	}
	byLevel := make([]int, len(order))
	for c := range byLevel {
		byLevel[c] = c
	}
	sort.SliceStable(byLevel, func(a, b int) bool { return v.fri.classN[byLevel[a]] > v.fri.classN[byLevel[b]] })
	v.fri.levelOf = make([]int, len(order))
	for lvl, c := range byLevel {
		v.fri.levelOf[c] = lvl
	}
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

// buildOpenings checks, for every query and tree, the opened row pairs
// against the tree's root (fri's verifyOneWMerkleProof): each group's pair is
// hashed as a leaf (fri.Poseidon2LeafHasher), the largest group's leaf is the
// path's leaf, and the other groups are injections, in decreasing size, equal
// sizes in declaration order. The path's index is the query row shifted to the
// tree's height.
func (v *Verifier) buildOpenings() {
	m, l := v.M, v.layout
	v.Openings = make([][][]RowPair, v.shape.NumQueries)
	for k := range v.shape.NumQueries {
		v.Openings[k] = make([][]RowPair, l.NumTrees)
		for t := range l.NumTrees {
			groups := l.TreeGroups[t]
			order := make([]int, len(groups))
			for g := range order {
				order[g] = g
			}
			sort.SliceStable(order, func(a, b int) bool { return groups[order[a]].N > groups[order[b]].N })
			pos := make([]int, len(groups)) // position of each group in order
			for i, g := range order {
				pos[g] = i
			}

			v.Openings[k][t] = make([]RowPair, len(groups))
			leaves := make([]int, len(groups))
			for g := range groups {
				names := v.sched.ColNamesByTree[t][g]
				nb, ne := len(names.Base), len(names.Ext)
				rows := func(prf proof.Proof) (fri.RawRowPair, error) {
					ps := prf.Opening.PointSamplings
					if k >= len(ps) || t >= len(ps[k]) {
						return fri.RawRowPair{}, fmt.Errorf("point samplings do not have the verifier's shape")
					}
					wp := ps[k][t]
					rp := wp.TopRows
					if i := pos[g]; i > 0 {
						if i-1 >= len(wp.Injections) {
							return fri.RawRowPair{}, fmt.Errorf("point samplings do not have the verifier's shape")
						}
						rp = wp.Injections[i-1].Rows
					}
					for _, r := range []fri.RawRow{rp.Lo, rp.Hi} {
						if len(r.RawRowBase) != nb || len(r.RawRowExt) != ne {
							return fri.RawRowPair{}, fmt.Errorf("opened rows do not have the verifier's shape")
						}
					}
					return rp, nil
				}
				row := func(hi bool) Row {
					res := Row{NBase: nb}
					for c := 0; c < nb; c += CellWidth {
						res.Base = append(res.Base, v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
							rp, err := rows(prf)
							r := rp.Lo
							if hi {
								r = rp.Hi
							}
							if err != nil {
								return Cell{}, err
							}
							var cell Cell
							copy(cell[:], r.RawRowBase[c:min(c+CellWidth, nb)])
							return cell, nil
						}))
					}
					for i := range ne {
						res.Ext = append(res.Ext, v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
							rp, err := rows(prf)
							r := rp.Lo
							if hi {
								r = rp.Hi
							}
							if err != nil {
								return Cell{}, err
							}
							return E6Cell(r.RawRowExt[i]), nil
						}))
					}
					return res
				}
				rp := RowPair{Lo: row(false), Hi: row(true)}
				v.Openings[k][t][g] = rp

				// The leaf: tag, widths, lo base, hi base, lo ext, hi ext.
				items := m.Elements([]koalabear.Element{hash.NewElement(fri.LeafDomainTag), hash.NewElement(uint64(2 * nb)), hash.NewElement(uint64(2 * ne))})
				for _, r := range []Row{rp.Lo, rp.Hi} {
					for c, cell := range r.Base {
						items = append(items, Item{cell, min(CellWidth, nb-c*CellWidth)})
					}
				}
				for _, c := range append(append([]int(nil), rp.Lo.Ext...), rp.Hi.Ext...) {
					items = append(items, E6(c))
				}
				addrs, kinds := make([]int, len(items)), make([]int, len(items))
				for i, it := range items {
					addrs[i], kinds[i] = it.Addr, it.Kind
				}
				stream, n := m.Pack(addrs, kinds)
				leaves[g] = m.Sponge(stream, n)
			}

			// The path, from the largest group's leaf.
			topRows := constants.RATE * groups[order[0]].N
			depth := log2(topRows / 2)
			sibs := make([]int, depth)
			for i := range sibs {
				sibs[i] = v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
					sib := prf.Opening.PointSamplings[k][t].Path.Siblings
					if len(sib) != depth {
						return Cell{}, fmt.Errorf("Merkle path does not have the verifier's shape")
					}
					return digestCell(sib[i]), nil
				})
			}
			var injections []Injection
			for _, g := range order[1:] {
				injections = append(injections, Injection{Width: constants.RATE * groups[g].N / 2, Leaf: leaves[g]})
			}
			// The pair index: the query row at the tree's height, halved.
			index := v.Queries[k].Shr[v.fri.logN-log2(topRows)+1]
			m.MerklePath(leaves[order[0]], sibs, index, v.roots[t], injections...)
		}
	}
}

// deepPoly is one polynomial of a DEEP class: its tree, group, rail and index,
// and its shifts.
type deepPoly struct {
	t, g, i int
	ext     bool
	shifts  []int
}

// buildDEEP computes, for every query and DEEP class, the DEEP quotient at
// the class's opened pair (fri's checkFRIBridgeByPolynomial):
//
//	DQ_c(±X) = Σ_i α^i Σ_s (v_{i,s} − P_i(±X)) / (ζ·ω_N^s − (±X))
//
// over the class's polynomials P_i in alpha_DEEP order, regrouped by shift
// point and divided once by the point's denominator. For each point, the
// numerator Σ_i α^i·(v_{i,s} − P_i(±X)) over the polynomials opened there is
// split into the claimed part Σ_i α^i·v_{i,s}, query-independent and
// computed once by the E6 chip, minus the opened part Σ_i α^i·P_i(±X), a
// Horner on the deep chip, CellWidth base values per row (deepRows).
func (v *Verifier) buildDEEP() {
	m, l := v.M, v.layout
	zeta := v.ChallengeE6(constants.FINAL_EVALUATION_POINT)
	alpha := v.ChallengeE6(fri.DeepAlphaName)
	zero := m.Const(Cell{})

	// α powers, computed on demand (query-independent).
	alphaPow := map[int]int{1: alpha}
	var pow func(e int) int
	pow = func(e int) int {
		if a, ok := alphaPow[e]; ok {
			return a
		}
		alphaPow[e] = m.Mul(pow(e-1), alpha)
		return alphaPow[e]
	}

	numClasses := len(v.fri.classN)
	v.DEEP = make([][][2]int, v.shape.NumQueries)
	for k := range v.DEEP {
		v.DEEP[k] = make([][2]int, numClasses)
	}
	for c := range numClasses {
		N := v.fri.classN[c]
		// The class's polynomials, in alpha_DEEP order: trees, groups, base
		// then extension, columns in order.
		var polys []deepPoly
		for t := range l.NumTrees {
			for g, gs := range v.sched.Shifts[t] {
				if v.fri.classOf[t][g] != c {
					continue
				}
				for i, ss := range gs.Base {
					polys = append(polys, deepPoly{t: t, g: g, i: i, shifts: ss})
				}
				for i, ss := range gs.Ext {
					polys = append(polys, deepPoly{t: t, g: g, i: i, ext: true, shifts: ss})
				}
			}
		}
		// The shift points ζ·ω_N^s, query-independent.
		omegaN, err := koalabear.Generator(uint64(N))
		if err != nil {
			panic(err)
		}
		var points []int
		zs := map[int]int{}
		for _, p := range polys {
			for _, sh := range p.shifts {
				n := ((sh % N) + N) % N
				if _, ok := zs[n]; ok {
					continue
				}
				points = append(points, n)
				if n == 0 {
					zs[n] = zeta
				} else {
					var w koalabear.Element
					w.ExpInt64(omegaN, int64(n))
					zs[n] = m.Mul(zeta, m.Const(ScalarCell(w)))
				}
			}
		}
		sort.Ints(points)

		// X = ω_{rate·N}^bitrev(lo) over w = log2(rate·N) bits, lo the even row
		// of the query row s >> br at the class's height: bit i ≥ 1 of lo is
		// bit br + i of s, and weighs 2^(w−1−i) once reversed.
		ratN := constants.RATE * N
		wBits := log2(ratN)
		br := v.fri.logN - wBits
		g, err := koalabear.Generator(uint64(ratN))
		if err != nil {
			panic(err)
		}
		gens := make([]koalabear.Element, wBits-1)
		for i := 1; i < wBits; i++ {
			gens[i-1] = g
			for range wBits - 1 - i {
				gens[i-1].Square(&gens[i-1])
			}
		}

		// Per point n: the polynomials opened there (their claimed value at
		// n), their index range [lo, hi], and the query-independent
		// C_n = Σ_{i ∈ [lo, hi]} α^(i−lo)·v_{i,n}.
		type pointSet struct {
			lo, hi int
			at     []bool
			c      int
		}
		sets := make(map[int]*pointSet, len(points))
		for _, n := range points {
			ps := &pointSet{lo: -1, at: make([]bool, len(polys))}
			claimedAt := make([]int, len(polys))
			for i, p := range polys {
				for j, sh := range p.shifts {
					if ((sh%N)+N)%N != n {
						continue
					}
					claimed := v.Claimed[p.t][p.g].Base
					if p.ext {
						claimed = v.Claimed[p.t][p.g].Ext
					}
					ps.at[i], claimedAt[i] = true, claimed[p.i][j]
					if ps.lo < 0 {
						ps.lo = i
					}
					ps.hi = i
				}
			}
			coeffs := make([]int, 0, ps.hi-ps.lo+1)
			for i := ps.hi; i >= ps.lo; i-- {
				if ps.at[i] {
					coeffs = append(coeffs, claimedAt[i])
				} else {
					coeffs = append(coeffs, zero)
				}
			}
			ps.c = m.Horner(alpha, coeffs)
			sets[n] = ps
		}

		for k := range v.shape.NumQueries {
			bitCells := make([]int, wBits-1)
			for i := 1; i < wBits; i++ {
				bitCells[i-1] = v.Queries[k].Bit[br+i]
			}
			x := m.PowBits(bitCells, gens)
			negX := m.Sub(zero, x)
			var dq [2]int
			for side, pt := range []int{x, negX} {
				acc := -1
				for _, n := range points {
					// Σ_i α^(i−lo)·(v_{i,n} − P_i(±X)) over the polynomials
					// opened at n, times α^lo: C_n minus the deep chip's
					// Horner over the opened values.
					ps := sets[n]
					opened := m.DeepHorner(alpha, v.deepRows(polys, ps.at, ps.lo, ps.hi, k, side))
					num := m.Sub(ps.c, opened)
					if ps.lo > 0 {
						num = m.Mul(num, pow(ps.lo))
					}
					term := m.Div(num, m.Sub(zs[n], pt))
					if acc < 0 {
						acc = term
					} else {
						acc = m.Add(acc, term)
					}
				}
				dq[side] = acc
			}
			v.DEEP[k][c] = dq
		}
	}
}

// deepRows returns the deep chip rows of the Horner over the opened values
// P_i(±X) of polys[lo..hi], from hi down to lo, at query k on side lo (0) or
// hi (1): the base values of a group share a row per opened cell, CellWidth
// lanes each, and an extension value takes a row; at[i] selects the
// polynomials whose value is added (the others count as 0).
func (v *Verifier) deepRows(polys []deepPoly, at []bool, lo, hi, k, side int) []DeepRow {
	var rows []DeepRow
	cur := -1 // the cell of the last row, if it is a base row
	for i := hi; i >= lo; i-- {
		p := polys[i]
		rp := v.Openings[k][p.t][p.g]
		row := rp.Lo
		if side == 1 {
			row = rp.Hi
		}
		var sel uint8
		if at[i] {
			sel = 1
		}
		if p.ext {
			rows = append(rows, DeepRow{Cell: row.Ext[p.i], Ext: true, Act: 1, Sel: sel})
			cur = -1
			continue
		}
		cell, lane := row.Base[p.i/CellWidth], p.i%CellWidth
		if cell != cur {
			rows = append(rows, DeepRow{Cell: cell})
			cur = cell
		}
		r := &rows[len(rows)-1]
		r.Act |= 1 << lane
		r.Sel |= sel << lane
	}
	return rows
}

// leafE6Pair returns the Merkle leaf of a pair of extension values, as
// fri.Poseidon2LeafHasher hashes a FRI layer's row pair: the LEAF tag, 0 base
// and 2 extension values, then p and q.
func (v *Verifier) leafE6Pair(p, q int) int {
	m := v.M
	items := m.Elements([]koalabear.Element{hash.NewElement(fri.LeafDomainTag), hash.NewElement(0), hash.NewElement(2)})
	items = append(items, E6(p), E6(q))
	addrs, kinds := make([]int, len(items)), make([]int, len(items))
	for i, it := range items {
		addrs[i], kinds[i] = it.Addr, it.Kind
	}
	stream, n := m.Pack(addrs, kinds)
	return m.Sponge(stream, n)
}

// buildFRI checks FRI at every query (fri.Verify and checkQueryExt):
//
//   - round 0 is the levels tree: its leaves are the DEEP quotients of P2.6,
//     DQ_c(±X) for the class of each level, authenticated by one path with
//     the levels l ≥ 1 as injections (so the circuit uses its own DEEP values
//     as the level openings: authenticating them is the bridge check);
//   - round j ≥ 1 opens the pair of layer j, authenticated in its tree;
//   - each round folds its pair (the fold chip), round 0's pair being level
//     0's plus γ_l times the pairs of the other levels entering at round 0,
//     and the result plus the injections of the levels entering at the next
//     round must be the next pair's entry selected by the query bit, or the
//     final polynomial's value at s >> numRounds after the last round.
func (v *Verifier) buildFRI() error {
	m := v.M
	logN, numRounds := v.fri.logN, v.fri.numRounds
	maxN := 1 << numRounds
	numLevels := v.fri.numLevels
	zero := m.Const(Cell{})

	// The levels: class, size and intro round of each, in level order.
	classAt := make([]int, numLevels)
	for c, lvl := range v.fri.levelOf {
		classAt[lvl] = c
	}
	intro := make([]int, numLevels)
	enter := map[int][]int{} // round → levels l ≥ 1 entering at it
	for lvl, c := range classAt {
		intro[lvl] = log2(maxN / v.fri.classN[c])
		if lvl > 0 {
			enter[intro[lvl]] = append(enter[intro[lvl]], lvl)
		}
	}
	gammas := make([]int, numLevels)
	for lvl := 1; lvl < numLevels; lvl++ {
		gammas[lvl] = v.ChallengeE6(fri.LevelGammaName(lvl))
	}
	alphas := make([]int, numRounds)
	for j := range numRounds {
		alphas[j] = v.ChallengeE6(fri.FoldName(j))
	}
	// The domain generators' inverses, one per round.
	gInv := make([]koalabear.Element, numRounds)
	for j := range numRounds {
		g, err := koalabear.Generator(uint64(1) << (logN - j))
		if err != nil {
			return err
		}
		gInv[j].Inverse(&g)
	}
	// The final polynomial, read at s >> numRounds.
	final := m.Table(v.Final)

	for k := range v.shape.NumQueries {
		q := v.Queries[k]
		pair := func(lvl int) [2]int { return v.DEEP[k][classAt[lvl]] }

		var rounds []FoldRound
		for j := range numRounds {
			var p, qv, xb int
			if j == 0 {
				// The levels tree: level 0 is the leaf, the others injections.
				lp := pair(0)
				var injections []Injection
				for lvl := 1; lvl < numLevels; lvl++ {
					pl := pair(lvl)
					injections = append(injections, Injection{Width: (1 << (logN - intro[lvl])) / 2, Leaf: v.leafE6Pair(pl[0], pl[1])})
				}
				sibs := v.friSiblings(k, 0, logN-1)
				xb = m.MerklePathX(v.leafE6Pair(lp[0], lp[1]), sibs, q.Shr[1], v.LevelsRoot, gInv[0], injections...)
				p, qv = lp[0], lp[1]
				for _, lvl := range enter[0] {
					pl := pair(lvl)
					p = m.Add(p, m.Mul(gammas[lvl], pl[0]))
					qv = m.Add(qv, m.Mul(gammas[lvl], pl[1]))
				}
			} else {
				p, qv = v.friLayerValues(k, j)
				sibs := v.friSiblings(k, j, logN-j-1)
				xb = m.MerklePathX(v.leafE6Pair(p, qv), sibs, q.Shr[j+1], v.FRIRoots[j-1], gInv[j])
			}
			// The levels entering at the next round, each at the entry the
			// next row selects: bit j + 1 of s.
			inj := zero
			if j+1 < numRounds {
				for _, lvl := range enter[j+1] {
					pl := pair(lvl)
					sel := m.Add(pl[0], m.Mul(q.Bit[j+1], m.Sub(pl[1], pl[0])))
					term := m.Mul(gammas[lvl], sel)
					if inj == zero {
						inj = term
					} else {
						inj = m.Add(inj, term)
					}
				}
			}
			rounds = append(rounds, FoldRound{P: p, Q: qv, Alpha: alphas[j], XB: xb, Inj: inj})
		}
		m.FoldChain(rounds, m.Lookup(final, q.Shr[numRounds]))
	}
	return nil
}

// friLayerValues allocates the inputs of the pair of FRI layer j ≥ 1 opened at
// query k.
func (v *Verifier) friLayerValues(k, j int) (int, int) {
	layer := func(prf proof.Proof) (fri.QueryLayer, error) {
		fq := prf.Opening.FRIProof.FRIQueries
		if k >= len(fq) || j >= len(fq[k].Layers) {
			return fri.QueryLayer{}, fmt.Errorf("FRI queries do not have the verifier's shape")
		}
		return fq[k].Layers[j], nil
	}
	p := v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
		l, err := layer(prf)
		return E6Cell(l.LeafPExt), err
	})
	q := v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
		l, err := layer(prf)
		return E6Cell(l.LeafQExt), err
	})
	return p, q
}

// friSiblings allocates the inputs of the Merkle path of FRI layer j at
// query k (layer 0 is the levels tree).
func (v *Verifier) friSiblings(k, j, depth int) []int {
	sibs := make([]int, depth)
	for i := range sibs {
		sibs[i] = v.input(func(prf proof.Proof, _ public.Inputs) (Cell, error) {
			fq := prf.Opening.FRIProof.FRIQueries
			if k >= len(fq) || j >= len(fq[k].Layers) || len(fq[k].Layers[j].Path.Siblings) != depth {
				return Cell{}, fmt.Errorf("FRI paths do not have the verifier's shape")
			}
			return digestCell(fq[k].Layers[j].Path.Siblings[i]), nil
		})
	}
	return sibs
}

// buildAIR checks the AIR at zeta, as the Go verifier's loadClaimedValues,
// computeVerifierColumns, checkLogupBus and checkAIRRelations: the values at
// zeta (claimed values, round challenges, verifier columns) by leaf key, the
// logup buses (their totals sum to zero), and for every module
//
//	V(ζ) = (ζ^N − 1)·Σ_i Q_i(ζ)·ζ^(iN)
//
// with V the folded vanishing relation, unrolled into E6 rows, and Q_i the
// quotient chunks.
func (v *Verifier) buildAIR() error {
	m, l := v.M, v.layout
	zero := m.Const(Cell{})
	oneE := koalabear.One()
	one := m.Const(ScalarCell(oneE))
	zeta := v.ChallengeE6(constants.FINAL_EVALUATION_POINT)

	// The values at zeta, by leaf key.
	vals := map[string]int{}
	for t := range l.NumTrees {
		for g, gk := range v.sched.Keys[t] {
			for i, perShift := range gk.Base {
				for k, keys := range perShift {
					for _, key := range keys {
						vals[key] = v.Claimed[t][g].Base[i][k]
					}
				}
			}
			for i, perShift := range gk.Ext {
				for k, keys := range perShift {
					for _, key := range keys {
						vals[key] = v.Claimed[t][g].Ext[i][k]
					}
				}
			}
		}
	}
	for r := range v.program.Rounds {
		name := constants.CanonicalChallengeName(r)
		vals[name] = v.ChallengeE6(name)
	}

	// ζ^(2^k), on demand.
	zetaPow2 := []int{zeta}
	zetaPow := func(logN int) int {
		for len(zetaPow2) <= logN {
			z := zetaPow2[len(zetaPow2)-1]
			zetaPow2 = append(zetaPow2, m.Mul(z, z))
		}
		return zetaPow2[logN]
	}
	// lagrange returns L_i(ζ) = ω^i·(ζ^N − 1) / (N·(ζ − ω^i)) on the domain of
	// size N, for a cell w = ω^i.
	lagrange := func(N, w int) int {
		zn1 := m.Sub(zetaPow(log2(N)), one)
		den := m.Mul(m.Sub(zeta, w), m.Const(ScalarCell(koalabear.NewElement(uint64(N)))))
		return m.Div(m.Mul(zn1, w), den)
	}
	// omegaPow returns a cell ω_N^idx for a scalar index cell, from its low
	// log2(N) bits (ω_N^N = 1).
	omegaPow := func(N, idx int) int {
		n := log2(N)
		omega, err := koalabear.Generator(uint64(N))
		if err != nil {
			panic(err)
		}
		bits := m.Bits(idx, n)
		gs := make([]koalabear.Element, n)
		for b := range gs {
			gs[b] = omega
			for range b {
				gs[b].Square(&gs[b])
			}
		}
		return m.PowBits(bits.Bit, gs)
	}
	// weighted returns Σ entries v·L_idx(ζ).
	weighted := func(N int, entries []entryCells) int {
		acc := zero
		for _, e := range entries {
			term := m.Mul(e.val, lagrange(N, omegaPow(N, e.idx)))
			if acc == zero {
				acc = term
			} else {
				acc = m.Add(acc, term)
			}
		}
		return acc
	}

	// The public input indices are positions of the module: below its size,
	// as the Go verifier checks.
	modules := make([]string, 0, len(v.program.Modules))
	for name := range v.program.Modules {
		modules = append(modules, name)
	}
	sort.Strings(modules)
	for _, p := range v.shape.PublicInputs {
		mod, ok := v.program.Modules[p.Module]
		if !ok {
			return fmt.Errorf("NewVerifier: public input %q of unknown module %q", p.Name, p.Module)
		}
		for _, e := range v.publicEntries[p.Name] {
			m.AssertEq(e.idx, m.Bits(e.idx, log2(mod.N)).Shr[0])
		}
	}

	// The verifier columns of every module's relation (first come, as
	// computeVerifierColumns).
	cfg := expr.NewConfig(expr.OnlyVerifierColumns...)
	for _, name := range modules {
		mod := v.program.Modules[name]
		if mod.VanishingRelation == nil {
			continue
		}
		for _, leaf := range mod.VanishingRelation.LeavesFull(cfg) {
			key := leaf.String()
			if _, ok := vals[key]; ok {
				continue
			}
			switch leaf.Hook {
			case expr.LagrangeHook:
				i := constants.ParseLagrangeName(leaf.Name)
				if i < 0 {
					i += mod.N
				}
				omega, err := koalabear.Generator(uint64(mod.N))
				if err != nil {
					return err
				}
				var w koalabear.Element
				w.ExpInt64(omega, int64(i))
				vals[key] = lagrange(mod.N, m.Const(ScalarCell(w)))
			case expr.PublicInputHook:
				entries, ok := v.publicEntries[leaf.Name]
				if !ok {
					return fmt.Errorf("NewVerifier: public input %q is not in the shape", leaf.Name)
				}
				for _, p := range v.shape.PublicInputs {
					if p.Name == leaf.Name && p.Module != name {
						return fmt.Errorf("NewVerifier: public input %q belongs to module %q, used from module %q", leaf.Name, p.Module, name)
					}
				}
				vals[key] = weighted(mod.N, entries)
			case expr.ExposedValueHook:
				entries, ok := v.exposedEntries[leaf.Name]
				if !ok {
					return fmt.Errorf("NewVerifier: exposed value %q is not bound", leaf.Name)
				}
				vals[key] = weighted(mod.N, entries)
			case expr.ExposedAverageHook:
				entries := v.exposedEntries[leaf.Name]
				if len(entries) != 1 {
					return fmt.Errorf("NewVerifier: exposed average %q must have one entry", leaf.Name)
				}
				var invN koalabear.Element
				invN.SetUint64(uint64(mod.N))
				invN.Inverse(&invN)
				vals[key] = m.Mul(entries[0].val, m.Const(ScalarCell(invN)))
			default:
				return fmt.Errorf("NewVerifier: %s carries unsupported hook %s", key, leaf.Hook)
			}
		}
	}

	// The logup buses: the totals sum to zero.
	for _, bus := range v.program.LogupBus {
		acc := zero
		for _, name := range bus.Totals {
			entries := v.exposedEntries[name]
			if len(entries) != 1 {
				return fmt.Errorf("NewVerifier: logup total %q must have one entry", name)
			}
			if acc == zero {
				acc = entries[0].val
			} else {
				acc = m.Add(acc, entries[0].val)
			}
		}
		m.AssertEq(acc, zero)
	}

	// Every module's relation at zeta against its quotient.
	for _, name := range modules {
		mod := v.program.Modules[name]
		if mod.VanishingRelation == nil {
			continue
		}
		val, err := v.evalDAG(mod.VanishingRelation, vals)
		if err != nil {
			return fmt.Errorf("NewVerifier: module %s: %w", name, err)
		}
		zn := zetaPow(log2(mod.N))
		var chunks []int
		for i := 0; ; i++ {
			c, ok := vals[constants.QuotientChunkName(name, i)]
			if !ok {
				break
			}
			chunks = append(chunks, c)
		}
		// Σ_i Q_i·(ζ^N)^i, by Horner from the last chunk.
		q := zero
		if len(chunks) > 0 {
			rev := make([]int, len(chunks))
			for i, c := range chunks {
				rev[len(chunks)-1-i] = c
			}
			q = m.Horner(zn, rev)
		}
		m.AssertEq(val, m.Mul(m.Sub(zn, one), q))
	}
	return nil
}

// evalDAG unrolls a relation's DAG into E6 rows, children before parents,
// each node once: leaves are the cells of vals (by leaf key) or constants.
func (v *Verifier) evalDAG(d *dag.DAG, vals map[string]int) (int, error) {
	m := v.M
	cell := make(map[*dag.DAGNode]int, len(d.Nodes))
	for _, n := range d.Nodes {
		switch n.Kind {
		case dag.KindLeaf:
			if n.IsConst {
				cell[n] = m.Const(ScalarCell(n.ConstVal))
				continue
			}
			c, ok := vals[n.Leaf.String()]
			if !ok {
				return 0, fmt.Errorf("no value at zeta for %s", n.Leaf.String())
			}
			cell[n] = c
		case dag.KindAdd, dag.KindMul:
			acc := cell[n.Children[0]]
			for _, ch := range n.Children[1:] {
				if n.Kind == dag.KindAdd {
					acc = m.Add(acc, cell[ch])
				} else {
					acc = m.Mul(acc, cell[ch])
				}
			}
			cell[n] = acc
		case dag.KindSub:
			cell[n] = m.Sub(cell[n.Children[0]], cell[n.Children[1]])
		case dag.KindPow:
			base, res := cell[n.Children[0]], -1
			for e := n.Exp; e > 0; e >>= 1 {
				if e&1 == 1 {
					if res < 0 {
						res = base
					} else {
						res = m.Mul(res, base)
					}
				}
				if e > 1 {
					base = m.Mul(base, base)
				}
			}
			if res < 0 {
				res = m.Const(ScalarCell(koalabear.One()))
			}
			cell[n] = res
		default:
			return 0, fmt.Errorf("unknown DAG node kind %d", n.Kind)
		}
	}
	return cell[d.Root], nil
}
