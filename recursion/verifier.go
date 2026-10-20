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
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
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

// Verifier is the circuit of loom's verifier for one program, verification key
// and shape, on its own Machine. The sizes of the modules made dynamic
// (WithDynamicModules) are inputs; the others are the program's. Build it once
// with NewVerifier, then Compile its Machine, and execute it on the inputs of
// every statement (Inputs).
type Verifier struct {
	M         *Machine
	program   board.Program
	vk        setup.VerificationKey
	backendID string
	shape     Shape
	layout    protocol.Layout
	sched     protocol.CanonicalSchedule

	// extract[i] reads the value of the i-th input cell from a statement;
	// sizeInputs[i] is the module of a size input.
	extract    []func(st *statement) (Cell, error)
	sizeInputs map[int]string

	// sizes holds every module's size in circuit; sizeTables the tables of
	// size-dependent constants, by key (see sizeTable).
	sizes      map[string]moduleSize
	sizeTables map[string]Table
	// treeOrders[t] are the heights and order tables of a tree with a dynamic
	// group; queryBits[k] the table of query k's row bits.
	// orders are the canonical orders of trees and of FRI's levels, by key
	// (dynamicOrder); orderInputs[key] the positions of π among the inputs;
	// queryBits[k] the table of query k's row bits.
	orders      map[string]dynOrder
	orderInputs map[string][]int
	queryBits   map[int]Table
	// friDyn is FRI's structure in circuit when a module is dynamic.
	friDyn *friDynamic

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

// friShape is the FRI configuration of the verified proofs: FRI runs over the
// domain of the maximum module size, N = RATE·2^MAX_LOG_MODULE_SIZE, with
// numRounds = MAX_LOG_MODULE_SIZE; the largest module's level enters at round
// first = log2(2^MAX_LOG_MODULE_SIZE / max N_m), and the rounds before it have
// no layer (see fri.Proof). One level per DEEP class.
type friShape struct {
	logN, numRounds, numLevels, first int
	// The DEEP classes (fri.WithDeepClasses: one per module), in class order:
	// classOf[t][g] is the class of group g of tree t, classN[c] its size,
	// levelOf[c] its FRI level (levels by decreasing size, stably).
	classOf  [][]int
	classN   []int
	classMod []string // the module of every class (one class per module)
	levelOf  []int
}

// NewVerifier builds the circuit verifying loom proofs of program under vk,
// for proofs of the given shape.
func NewVerifier(program board.Program, vk setup.VerificationKey, shape Shape, opts ...VerifierOption) (*Verifier, error) {
	v, err := newVerifier(program, vk, shape, opts...)
	if err != nil {
		return nil, err
	}
	if err := v.buildTranscript(); err != nil {
		return nil, err
	}
	if err := v.buildPCSTranscript(); err != nil {
		return nil, err
	}
	v.buildOpenings()
	v.buildDEEP()
	if v.friDyn != nil {
		v.buildFRIDynamic()
	} else if err := v.buildFRI(); err != nil {
		return nil, err
	}
	if err := v.buildAIR(); err != nil {
		return nil, err
	}
	return v, nil
}

// newVerifier checks the verification key and allocates the verifier's
// state and its size inputs, before the circuit's parts are built.
func newVerifier(program board.Program, vk setup.VerificationKey, shape Shape, opts ...VerifierOption) (*Verifier, error) {
	var cfg verifierConfig
	for _, opt := range opts {
		if err := opt(&cfg); err != nil {
			return nil, err
		}
	}
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
	v.backendID = backend.ID
	if err := v.buildSizes(cfg.dynamic); err != nil {
		return nil, err
	}
	return v, nil
}

// statement is what the circuit verifies: a proof, its public inputs and its
// module sizes. pos caches, per tree, the position of every group in the
// tree's order at these sizes (statementGroupPos).
type statement struct {
	prf    proof.Proof
	pi     public.Inputs
	sizes  ModuleSizes
	pos    map[int][]int
	orders map[string][]int // statementOrder's cache
}

// size returns a module's size in the statement: its own for a dynamic
// module, the program's for a fixed one.
func (v *Verifier) statementModuleSize(st *statement, module string) int {
	if v.sizes[module].dynamic {
		return st.sizes[module]
	}
	return v.program.Modules[module].N
}

// statementGroupPos returns the position of every group of tree t in the
// tree's order at the statement's sizes: by decreasing size, equal sizes in
// declaration order — the path's leaf first, then the injections, as the
// proof's WMerkleProof holds them (TopRows, then Injections[pos−1]).
func (v *Verifier) statementGroupPos(st *statement, t int) []int {
	if p, ok := st.pos[t]; ok {
		return p
	}
	groups := v.layout.TreeGroups[t]
	n := make([]int, len(groups))
	order := make([]int, len(groups))
	for g, grp := range groups {
		n[g], order[g] = v.statementModuleSize(st, grp.Module), g
	}
	sort.SliceStable(order, func(a, b int) bool { return n[order[a]] > n[order[b]] })
	pos := make([]int, len(groups))
	for i, g := range order {
		pos[g] = i
	}
	if st.pos == nil {
		st.pos = map[int][]int{}
	}
	st.pos[t] = pos
	return pos
}

// input allocates an input cell of the given kind whose value extract reads
// from each statement.
func (v *Verifier) input(kind int, extract func(st *statement) (Cell, error)) int {
	v.extract = append(v.extract, extract)
	return v.M.Input(kind)
}

// fieldKind returns the kind of the cell of a value of field f.
func fieldKind(f field.Kind) int {
	if f == field.Ext {
		return KindE6
	}
	return KindScalar
}

// Inputs returns the input cells' values for a statement — a proof, its public
// inputs and its module sizes — in the order of the Machine's inputs. sizes
// must give the size of every dynamic module; the size of a fixed module, if
// given, must be the program's.
func (v *Verifier) Inputs(prf proof.Proof, pi public.Inputs, sizes ModuleSizes) ([]Cell, error) {
	for name, n := range sizes {
		s, ok := v.sizes[name]
		if !ok {
			return nil, fmt.Errorf("Inputs: size of the unknown module %q", name)
		}
		if !s.dynamic && n != v.program.Modules[name].N {
			return nil, fmt.Errorf("Inputs: module %q has the fixed size %d, not %d", name, v.program.Modules[name].N, n)
		}
	}
	st := &statement{prf: prf, pi: pi, sizes: sizes}
	res := make([]Cell, len(v.extract))
	for i, f := range v.extract {
		c, err := f(st)
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
func (v *Verifier) buildTranscript() error {
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
		v.roots[t] = v.input(KindDigest, func(st *statement) (Cell, error) {
			prf := st.prf
			if i >= len(prf.Commitments) {
				return Cell{}, fmt.Errorf("proof has %d commitments, want more than %d", len(prf.Commitments), i)
			}
			return digestCell(prf.Commitments[i]), nil
		})
	}

	initial := constants.InitialChallengeName(numRounds)
	v.tr.BindElements(initial, hash.StringToElements(constants.HASH_BACKEND_DOMAIN_TAG, v.backendID))
	v.bindModuleSizes(initial)
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
			idx := v.input(KindScalar, func(st *statement) (Cell, error) {
				pi := st.pi
				e, err := entry(pi)
				return ScalarCell(koalabear.NewElement(uint64(e.Idx))), err
			})
			v.tr.Bind(name, Scalar(idx))
			v.tr.BindElements(name, []koalabear.Element{hash.NewElement(uint64(f))})
			val := v.input(fieldKind(f), func(st *statement) (Cell, error) {
				pi := st.pi
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
		idx := v.input(KindScalar, func(st *statement) (Cell, error) {
			prf := st.prf
			e, err := entry(prf)
			return ScalarCell(koalabear.NewElement(uint64(e.Idx))), err
		})
		val := v.input(KindE6, func(st *statement) (Cell, error) {
			prf := st.prf
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
	v.fri = friShape{
		logN:      log2(constants.RATE) + constants.MAX_LOG_MODULE_SIZE,
		numRounds: constants.MAX_LOG_MODULE_SIZE,
		numLevels: len(order),
		first:     constants.MAX_LOG_MODULE_SIZE - log2(maxN),
	}
	dense := map[int]int{}
	for i, id := range order {
		dense[id] = i
	}
	v.fri.classN = make([]int, len(order))
	v.fri.classMod = make([]string, len(order))
	v.fri.classOf = make([][]int, len(classes))
	for t, tc := range classes {
		v.fri.classOf[t] = make([]int, len(tc))
		for g, id := range tc {
			c := dense[id]
			v.fri.classOf[t][g] = c
			v.fri.classN[c] = l.TreeGroups[t][g].N
			v.fri.classMod[c] = l.TreeGroups[t][g].Module
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
	v.allocClaimed()
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

	friProof := func(st *statement) (fri.Proof, error) {
		fp := st.prf.Opening.FRIProof
		if len(fp.PoW) > 0 {
			return fp, fmt.Errorf("the FRI proof has proofs of work: grinding is not supported")
		}
		if len(fp.FRIRoots) != v.fri.numRounds-1-v.statementFirst(st) || len(fp.FinalPolyExt) != 1<<(v.fri.logN-v.fri.numRounds) {
			return fp, fmt.Errorf("the FRI proof does not have the verifier's shape")
		}
		return fp, nil
	}
	v.LevelsRoot = v.input(KindDigest, func(st *statement) (Cell, error) {
		fp, err := friProof(st)
		return digestCell(fp.LevelsRoot), err
	})
	for lvl := 1; lvl < v.fri.numLevels; lvl++ {
		name := fri.LevelGammaName(lvl)
		if lvl == 1 {
			v.tr.Bind(name, Digest(v.LevelsRoot))
		}
		v.Challenges[name] = v.tr.Compute(name)
	}
	// The fold challenges: the rounds before first have no layer and bind the
	// zero digest, round first binds the levels root, the next ones their
	// layer root.
	if v.anyDynamic() {
		v.buildFoldTranscriptDynamic(friProof)
	}
	zeroDigest := m.Const(Cell{})
	for j := range v.fri.numRounds {
		if v.anyDynamic() {
			break
		}
		root := v.LevelsRoot
		switch {
		case j < v.fri.first:
			root = zeroDigest
		case j > v.fri.first:
			i := j - v.fri.first - 1
			root = v.input(KindDigest, func(st *statement) (Cell, error) {
				fp, err := friProof(st)
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
		c := v.input(KindE6, func(st *statement) (Cell, error) {
			fp, err := friProof(st)
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

// allocClaimed allocates the claimed-value inputs of every group (Claimed).
func (v *Verifier) allocClaimed() {
	l := v.layout
	v.Claimed = make([][]ClaimedCells, l.NumTrees)
	for t := range l.NumTrees {
		v.Claimed[t] = make([]ClaimedCells, len(v.sched.Shifts[t]))
		for g, gs := range v.sched.Shifts[t] {
			v.Claimed[t][g] = ClaimedCells{Base: v.claimedInputs(t, g, false, gs.Base), Ext: v.claimedInputs(t, g, true, gs.Ext)}
		}
	}
}

// layerRoot returns the root cell of FRI layer j > first: the input of round
// j when a module is dynamic (friDynamic), FRIRoots' otherwise.
func (v *Verifier) layerRoot(j int) int {
	if v.friDyn != nil {
		return v.friDyn.layerRoots[j]
	}
	return v.FRIRoots[j-v.fri.first-1]
}

// hintInput returns the position among the inputs of the hint b_j.
func (v *Verifier) hintInput(j int) int { return v.friDyn.bInputs[j] }

// anyDynamic reports whether the circuit has a dynamic module.
func (v *Verifier) anyDynamic() bool {
	for _, s := range v.sizes {
		if s.dynamic {
			return true
		}
	}
	return false
}

// statementFirst returns FRI's first round at the statement's sizes: the
// round MaxLog − ℓ at which the largest class enters (fri.Proof).
func (v *Verifier) statementFirst(st *statement) int {
	maxLog := 0
	for _, mod := range v.fri.classMod {
		maxLog = max(maxLog, log2(v.statementModuleSize(st, mod)))
	}
	return MaxLogModuleSize - maxLog
}

// friDynamic is FRI's structure at the statement's sizes, in circuit: the
// levels' canonical order (classes by decreasing size, equal sizes by class
// index — fri.Prove's level order) with the round each enters, and per round
// j the number b_j of levels entered by j, the indicators p_j = [j ≥ first],
// g_j = [j > first], f_j = [j = first] (scalar cells), and the layer root
// input (rounds ≥ 1).
type friDynamic struct {
	levels     dynOrder
	b          []int
	bInputs    []int // the positions of the b_j among the inputs
	rootInputs []int // rootInputs[j]: the position of layerRoots[j] (j ≥ 1)
	p, f, g    []int
	layerRoots []int // layerRoots[j], j ≥ 1
}

// buildFoldTranscriptDynamic binds FRI's fold challenges for the statement's
// sizes. The levels' order is checked (dynamicOrder), so its first level is a
// largest class, entering at first. Per round j, the hint b_j is checked:
// b_j ≤ n, the level at position b_j (if any) enters after j and the one at
// b_j − 1 (if any) at j or before — through the tables of the entry rounds
// with sentinels. Then p_j = [b_j > 0], and fri_fold_j binds
// Select(f_j, levels root, Select(g_j, layer root j, 0)): the zero digest
// before first, the levels root at first, the layer root after (fri.Proof).
func (v *Verifier) buildFoldTranscriptDynamic(friProof func(*statement) (fri.Proof, error)) {
	m := v.M
	c := func(x int) int { return m.Const(ScalarCell(koalabear.NewElement(uint64(x)))) }
	below := func(x, bits int) { m.AssertEq(x, m.Bits(x, bits).Shr[0]) }
	d := &friDynamic{levels: v.dynamicOrder("fri", v.fri.classMod)}
	n := len(d.levels.intro)
	after := m.Table(append(append([]int(nil), d.levels.intro...), c(1<<7)))
	before := m.Table(append([]int{c(0)}, d.levels.intro...))
	posCells := []int{c(0)}
	for range n {
		posCells = append(posCells, c(1))
	}
	pos := m.Table(posCells)
	zero := m.Const(Cell{})
	for j := range v.fri.numRounds {
		d.bInputs = append(d.bInputs, len(v.extract))
		b := v.input(KindScalar, func(st *statement) (Cell, error) {
			entered := 0
			for _, mod := range v.fri.classMod {
				if MaxLogModuleSize-log2(v.statementModuleSize(st, mod)) <= j {
					entered++
				}
			}
			return ScalarCell(koalabear.NewElement(uint64(entered))), nil
		})
		below(b, 8)
		below(m.Sub(c(n), b), 8)
		below(m.Sub(m.Sub(m.Lookup(after, b), c(j)), c(1)), 8)
		below(m.Sub(c(j), m.Lookup(before, b)), 8)
		d.b = append(d.b, b)
		p := m.Lookup(pos, b)
		g := c(0)
		if j > 0 {
			g = d.p[j-1]
		}
		d.p, d.g, d.f = append(d.p, p), append(d.g, g), append(d.f, m.Sub(p, g))

		root := zero
		if j > 0 {
			for len(d.rootInputs) < j {
				d.rootInputs = append(d.rootInputs, -1)
			}
			d.rootInputs = append(d.rootInputs, len(v.extract))
			layer := v.input(KindDigest, func(st *statement) (Cell, error) {
				fp, err := friProof(st)
				if err != nil {
					return Cell{}, err
				}
				if i := j - v.statementFirst(st) - 1; i >= 0 {
					return digestCell(fp.FRIRoots[i]), nil
				}
				return Cell{}, nil
			})
			for len(d.layerRoots) < j {
				d.layerRoots = append(d.layerRoots, -1)
			}
			d.layerRoots = append(d.layerRoots, layer)
			v.FRIRoots = append(v.FRIRoots, layer)
			root = m.Select(g, layer, zero)
		}
		root = m.Select(d.f[j], v.LevelsRoot, root)
		v.tr.Bind(fri.FoldName(j), Digest(root))
		v.Challenges[fri.FoldName(j)] = v.tr.Compute(fri.FoldName(j))
	}
	v.friDyn = d
}

// claimedInputs allocates the claimed-value inputs of one rail of group g of
// tree t: one E6 cell per polynomial and shift.
func (v *Verifier) claimedInputs(t, g int, extRail bool, shifts [][]int) [][]int {
	res := make([][]int, len(shifts))
	for i, ss := range shifts {
		for k := range ss {
			res[i] = append(res[i], v.input(KindE6, func(st *statement) (Cell, error) {
				prf := st.prf
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
	v.allocOpenings()
	for k := range v.shape.NumQueries {
		for t := range l.NumTrees {
			groups := l.TreeGroups[t]
			order, _ := v.groupOrder(t)
			leaves := make([]int, len(groups))
			for g := range groups {
				rp := v.Openings[k][t][g]
				nb, ne := rp.Lo.NBase, len(rp.Lo.Ext)
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
			if v.dynamicTree(t) {
				v.dynamicOpening(k, t, leaves)
				continue
			}

			// The path, from the largest group's leaf.
			topRows := constants.RATE * groups[order[0]].N
			depth := log2(topRows / 2)
			sibs := make([]int, depth)
			for i := range sibs {
				sibs[i] = v.input(KindDigest, func(st *statement) (Cell, error) {
					prf := st.prf
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

// dynamicTree reports whether tree t has a group of a dynamic module: its
// shape then depends on the statement's sizes (dynamicOpening).
func (v *Verifier) dynamicTree(t int) bool {
	for _, g := range v.layout.TreeGroups[t] {
		if v.sizes[g.Module].dynamic {
			return true
		}
	}
	return false
}

// treeHeightOffset is a group's height in its tree minus its log size: a
// group of size N has RATE·N rows, RATE·N/2 leaves.
var treeHeightOffset = log2(constants.RATE) - 1

// maxTreeHeight is the height of a tree of the maximum module size.
var maxTreeHeight = MaxLogModuleSize + treeHeightOffset

// dynOrder is the canonical order of a list of modules (a tree's groups, or
// FRI's classes): by decreasing size, equal sizes by increasing index.
type dynOrder struct {
	heights, order Table // h by item, π by position
	pi             []int // π_k
	intro          []int // H − h_(π_k): for FRI's levels, the round level k enters
}

// statementOrder returns the canonical order of modules at the statement's
// sizes, cached by key.
func (v *Verifier) statementOrder(st *statement, key string, modules []string) []int {
	if p, ok := st.orders[key]; ok {
		return p
	}
	n := make([]int, len(modules))
	order := make([]int, len(modules))
	for i, mod := range modules {
		n[i], order[i] = v.statementModuleSize(st, mod), i
	}
	sort.SliceStable(order, func(a, b int) bool { return n[order[a]] > n[order[b]] })
	if st.orders == nil {
		st.orders = map[string][]int{}
	}
	st.orders[key] = order
	return order
}

// dynamicOrder returns the canonical order of modules, built once per key:
// the table of their heights in a tree (h = ℓ + log2(RATE) − 1: constants for
// fixed modules, cells for dynamic ones) and of the order π, an input (the
// order at the statement's sizes) checked: every π_k is below G, and the keys
// (H − h_(π_k))·2^8 + π_k strictly increase, so π is that permutation
// (distinct, sorted). The order then cannot depend on the query.
func (v *Verifier) dynamicOrder(key string, modules []string) dynOrder {
	if o, ok := v.orders[key]; ok {
		return o
	}
	m := v.M
	G := len(modules)
	if G > 1<<8 {
		panic(fmt.Sprintf("%s: %d items, above 2^8", key, G))
	}
	c := func(x int) int { return m.Const(ScalarCell(koalabear.NewElement(uint64(x)))) }
	hs := make([]int, G)
	for i, mod := range modules {
		s := v.sizes[mod]
		if s.dynamic {
			hs[i] = m.Add(s.cell, c(treeHeightOffset))
		} else {
			hs[i] = c(s.logN + treeHeightOffset)
		}
	}
	o := dynOrder{heights: m.Table(hs)}
	if v.orderInputs == nil {
		v.orderInputs = map[string][]int{}
	}
	for k := range G {
		v.orderInputs[key] = append(v.orderInputs[key], len(v.extract))
		o.pi = append(o.pi, v.input(KindScalar, func(st *statement) (Cell, error) {
			return ScalarCell(koalabear.NewElement(uint64(v.statementOrder(st, key, modules)[k]))), nil
		}))
	}
	below := func(x, bits int) { m.AssertEq(x, m.Bits(x, bits).Shr[0]) }
	prev := -1
	for k, pi := range o.pi {
		below(pi, 8)
		below(m.Sub(c(G-1), pi), 8)
		intro := m.Sub(c(maxTreeHeight), m.Lookup(o.heights, pi))
		o.intro = append(o.intro, intro)
		key := m.Add(m.Mul(intro, c(1<<8)), pi)
		if k > 0 {
			below(m.Sub(m.Sub(key, prev), c(1)), 13)
		}
		prev = key
	}
	o.order = m.Table(o.pi)
	if v.orders == nil {
		v.orders = map[string]dynOrder{}
	}
	v.orders[key] = o
	return o
}

// treeOrderKey is the dynamicOrder key of tree t.
func treeOrderKey(t int) string { return fmt.Sprintf("tree %d", t) }

// dynamicTreeOrder returns the heights and order tables of tree t's groups.
func (v *Verifier) dynamicTreeOrder(t int) (heights, order Table) {
	groups := v.layout.TreeGroups[t]
	modules := make([]string, len(groups))
	for g, grp := range groups {
		modules[g] = grp.Module
	}
	o := v.dynamicOrder(treeOrderKey(t), modules)
	return o.heights, o.order
}

// dynamicOpening checks the path of query k in tree t, of a dynamic shape:
// the groups' leaves fold at their heights in the tree's canonical order
// (dynamicTreeOrder), through the siblings indexed by height — taken from
// the proof at the statement's top height, zero above it — ordered by the
// bits of the query's full-domain row (MerklePathDynamic).
func (v *Verifier) dynamicOpening(k, t int, leaves []int) {
	m := v.M
	heights, order := v.dynamicTreeOrder(t)
	sibs := make([]int, maxTreeHeight)
	for h := 1; h <= maxTreeHeight; h++ {
		sibs[h-1] = v.input(KindDigest, func(st *statement) (Cell, error) {
			top := 0
			for _, grp := range v.layout.TreeGroups[t] {
				top = max(top, log2(v.statementModuleSize(st, grp.Module))+treeHeightOffset)
			}
			sib := st.prf.Opening.PointSamplings[k][t].Path.Siblings
			if len(sib) != top {
				return Cell{}, fmt.Errorf("Merkle path does not have the verifier's shape")
			}
			if h > top {
				return Cell{}, nil
			}
			return digestCell(sib[top-h]), nil
		})
	}
	bits := v.queryBitsTable(k)
	m.MerklePathDynamic(DynamicPath{
		Leaves: m.Table(leaves), Heights: heights, Order: order,
		Siblings: m.Table(sibs), Bits: bits, L: v.fri.logN, Root: v.roots[t],
	})
}

// queryBitsTable returns the table of the bits of query k's full-domain row,
// built once per query.
func (v *Verifier) queryBitsTable(k int) Table {
	if v.queryBits == nil {
		v.queryBits = map[int]Table{}
	}
	bits, ok := v.queryBits[k]
	if !ok {
		bits = v.M.Table(v.Queries[k].Bit[:v.fri.logN])
		v.queryBits[k] = bits
	}
	return bits
}

// groupOrder returns the groups of tree t by decreasing size, equal sizes in
// declaration order (the path's leaf first, then the injections), and the
// position of each group in that order.
func (v *Verifier) groupOrder(t int) (order, pos []int) {
	groups := v.layout.TreeGroups[t]
	order = make([]int, len(groups))
	for g := range order {
		order[g] = g
	}
	sort.SliceStable(order, func(a, b int) bool { return groups[order[a]].N > groups[order[b]].N })
	pos = make([]int, len(groups))
	for i, g := range order {
		pos[g] = i
	}
	return order, pos
}

// allocOpenings allocates the inputs of the opened row pairs (Openings): for
// every query, tree and group, the rows of the group's top rows or injection.
func (v *Verifier) allocOpenings() {
	l := v.layout
	v.Openings = make([][][]RowPair, v.shape.NumQueries)
	for k := range v.shape.NumQueries {
		v.Openings[k] = make([][]RowPair, l.NumTrees)
		for t := range l.NumTrees {
			v.Openings[k][t] = make([]RowPair, len(l.TreeGroups[t]))
			for g := range l.TreeGroups[t] {
				names := v.sched.ColNamesByTree[t][g]
				nb, ne := len(names.Base), len(names.Ext)
				// The group's rows: TopRows or an injection, by its position
				// in the tree's order at the statement's sizes.
				rows := func(st *statement) (fri.RawRowPair, error) {
					ps := st.prf.Opening.PointSamplings
					if k >= len(ps) || t >= len(ps[k]) {
						return fri.RawRowPair{}, fmt.Errorf("point samplings do not have the verifier's shape")
					}
					wp := ps[k][t]
					rp := wp.TopRows
					if i := v.statementGroupPos(st, t)[g]; i > 0 {
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
						res.Base = append(res.Base, v.input(KindDigest, func(st *statement) (Cell, error) {
							rp, err := rows(st)
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
						res.Ext = append(res.Ext, v.input(KindE6, func(st *statement) (Cell, error) {
							rp, err := rows(st)
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
			}
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
// over the class's polynomials P_i in alpha_DEEP order, regrouped by shift s
// (the point ζ·ω_N^s; two shifts equal mod N stay two terms, as in the sum
// over s) and divided once by the point's denominator. For each point, the
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

	// For a dynamic class, X = X₀^(2^d)·(−1)^(bit d of s), d = MaxLog − ℓ
	// the class's depth, with X₀ = Π_b bit_b(s)·ω_(2^(b+1)) over the bits of
	// the full-domain row s: the bits of s from d up, reversed, weighted for
	// the class's domain, the last factor setting bit d (the pair's even row)
	// to 0. Per query, the tables of X₀^(2^d) and of bit d, for d ≤ MaxLog.
	var xTables, bitTables []Table
	queryTables := func(k int) (Table, Table) {
		if xTables == nil {
			xTables, bitTables = make([]Table, v.shape.NumQueries), make([]Table, v.shape.NumQueries)
			for q := range v.shape.NumQueries {
				bitCells := v.Queries[q].Bit[:v.fri.logN]
				gs := make([]koalabear.Element, len(bitCells))
				for b := range gs {
					g, err := koalabear.Generator(uint64(1) << (b + 1))
					if err != nil {
						panic(err)
					}
					gs[b] = g
				}
				x := m.PowBits(bitCells, gs)
				pows := []int{x}
				for range MaxLogModuleSize {
					x = m.Mul(x, x)
					pows = append(pows, x)
				}
				xTables[q] = m.Table(pows)
				bitTables[q] = m.Table(v.Queries[q].Bit[:MaxLogModuleSize+1])
			}
		}
		return xTables[k], bitTables[k]
	}
	one := m.Const(ScalarCell(koalabear.One()))
	maxLog := m.Const(ScalarCell(koalabear.NewElement(MaxLogModuleSize)))

	numClasses := len(v.fri.classN)
	v.DEEP = make([][][2]int, v.shape.NumQueries)
	for k := range v.DEEP {
		v.DEEP[k] = make([][2]int, numClasses)
	}
	for c := range numClasses {
		N := v.fri.classN[c]
		mod := v.fri.classMod[c]
		size := v.sizes[mod]
		// The class's polynomials, in alpha_DEEP order: trees, groups, base
		// then extension, columns in order.
		var polys []deepPoly
		for t := range l.NumTrees {
			for g, gs := range v.sched.Shifts[t] {
				if v.fri.classOf[t][g] != c {
					continue
				}
				for i, ss := range gs.Base {
					polys = append(polys, deepPoly{t: t, g: g, i: i, shifts: v.classShifts(mod, ss)})
				}
				for i, ss := range gs.Ext {
					polys = append(polys, deepPoly{t: t, g: g, i: i, ext: true, shifts: v.classShifts(mod, ss)})
				}
			}
		}
		// The shift points ζ·ω_N^s, query-independent.
		var points []int
		zs := map[int]int{}
		for _, p := range polys {
			for _, sh := range p.shifts {
				if _, ok := zs[sh]; ok {
					continue
				}
				points = append(points, sh)
				if sh == 0 {
					zs[sh] = zeta
				} else {
					zs[sh] = m.Mul(zeta, v.SizeOmega(mod, sh))
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
					if sh != n {
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

		var depth int // a dynamic class's depth d = MaxLog − ℓ
		if size.dynamic {
			depth = m.Sub(maxLog, size.cell)
		}
		for k := range v.shape.NumQueries {
			var x int
			if size.dynamic {
				xTab, bitTab := queryTables(k)
				bit := m.Lookup(bitTab, depth)
				x = m.Mul(m.Lookup(xTab, depth), m.Sub(one, m.Add(bit, bit)))
			} else {
				bitCells := make([]int, wBits-1)
				for i := 1; i < wBits; i++ {
					bitCells[i-1] = v.Queries[k].Bit[br+i]
				}
				x = m.PowBits(bitCells, gens)
			}
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

// classShifts returns the shifts of a polynomial as the DEEP points use them:
// the schedule's (mod the program's size) for a fixed module, the raw shifts
// for a dynamic one, so that ω_N^s is the statement's.
func (v *Verifier) classShifts(module string, shifts []int) []int {
	if !v.sizes[module].dynamic {
		return shifts
	}
	res := make([]int, len(shifts))
	for i, s := range shifts {
		res[i] = v.rawShift(module, s)
	}
	return res
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
//   - the rounds before first have no layer (fri.Proof): nothing to check;
//   - round first is the levels tree: its leaves are the DEEP quotients of
//     P2.6, DQ_c(±X) for the class of each level, authenticated by one path
//     with the levels l ≥ 1 as injections (so the circuit uses its own DEEP
//     values as the level openings: authenticating them is the bridge check);
//   - round j > first opens the pair of layer j, authenticated in its tree;
//   - each round folds its pair (the fold chip), round first's pair being
//     level 0's plus γ_l times the pairs of the other levels entering there,
//     and the result plus the injections of the levels entering at the next
//     round must be the next pair's entry selected by the query bit, or the
//     final polynomial's value at s >> numRounds after the last round.
func (v *Verifier) buildFRI() error {
	m := v.M
	logN, numRounds, first := v.fri.logN, v.fri.numRounds, v.fri.first
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
	for j := first; j < numRounds; j++ {
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
		for j := first; j < numRounds; j++ {
			var p, qv, xb int
			if j == first {
				// The levels tree: level 0 is the leaf, the others injections.
				lp := pair(0)
				var injections []Injection
				for lvl := 1; lvl < numLevels; lvl++ {
					pl := pair(lvl)
					injections = append(injections, Injection{Width: (1 << (logN - intro[lvl])) / 2, Leaf: v.leafE6Pair(pl[0], pl[1])})
				}
				sibs := v.friSiblings(k, 0, logN-first-1)
				xb = m.MerklePathX(v.leafE6Pair(lp[0], lp[1]), sibs, q.Shr[first+1], v.LevelsRoot, gInv[first], injections...)
				p, qv = lp[0], lp[1]
				for _, lvl := range enter[first] {
					pl := pair(lvl)
					p = m.Add(p, m.Mul(gammas[lvl], pl[0]))
					qv = m.Add(qv, m.Mul(gammas[lvl], pl[1]))
				}
			} else {
				p, qv = v.friLayerValues(k, j-first)
				sibs := v.friSiblings(k, j-first, logN-j-1)
				xb = m.MerklePathX(v.leafE6Pair(p, qv), sibs, q.Shr[j+1], v.layerRoot(j), gInv[j])
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

// zeroTree returns the digests of the all-zero FRI layer: Z[0] the leaf of
// the pair (0, 0), Z[i] the root of a subtree of 2^i such leaves.
func zeroTree(depth int) []hash.Digest {
	var zero ext.E6
	row := fri.RawRow{RawRowExt: []ext.E6{zero}}
	z := []hash.Digest{fri.DefaultLeafHasher.HashLeafPair(row, row)}
	for i := 1; i <= depth; i++ {
		z = append(z, fri.DefaultNodeHasher.HashNode(z[i-1], z[i-1]))
	}
	return z
}

// buildFRIDynamic checks FRI at every query for the statement's sizes, over
// all the rounds 0..numRounds−1 (the structure of P3.5a: friDynamic):
//
//   - the levels tree: a dynamic path over the classes (their heights and
//     canonical order), whose leaves are the DEEP pairs DQ_c(±X), through its
//     siblings by height, to the levels root;
//   - round j's layer: its opened pair, through a path of depth logN − j − 1,
//     to Select(g_j, layer root j, zero-tree root): rounds up to first have no
//     layer, and open (0, 0) in the all-zero tree (zeroTree);
//   - the folded pair of round j: the opened one plus, at first,
//     Σ_(levels at first) γ·DQ — f_j·SL[b_j], SL the prefix sums of γ_k·DQ
//     over the sorted levels (γ_0 = 1) — and, entering round j + 1,
//     SS[b_(j+1)] − SS[b_j], SS the prefix sums of γ_k times the entry of
//     level k's pair selected by the bit of its entry round;
//   - the fold chain over every round, to the final polynomial at s >> numRounds.
func (v *Verifier) buildFRIDynamic() {
	m, d := v.M, v.friDyn
	logN, numRounds := v.fri.logN, v.fri.numRounds
	zero := m.Const(Cell{})
	gammas := []int{m.Const(ScalarCell(koalabear.One()))}
	for k := 1; k < len(d.levels.pi); k++ {
		gammas = append(gammas, v.ChallengeE6(fri.LevelGammaName(k)))
	}
	alphas := make([]int, numRounds)
	gInv := make([]koalabear.Element, numRounds)
	for j := range numRounds {
		alphas[j] = v.ChallengeE6(fri.FoldName(j))
		g, err := koalabear.Generator(uint64(1) << (logN - j))
		if err != nil {
			panic(err)
		}
		gInv[j].Inverse(&g)
	}
	final := m.Table(v.Final)
	z := zeroTree(logN)
	roots := make([]int, numRounds)
	for j := range numRounds {
		roots[j] = m.Const(digestCell(z[logN-j-1]))
		if j > 0 {
			roots[j] = m.Select(d.g[j], d.layerRoots[j], roots[j])
		}
	}

	// layer returns the opening of round j at query k in a statement, nil for a
	// round without layer.
	layer := func(st *statement, k, j int) (*fri.QueryLayer, error) {
		first := v.statementFirst(st)
		fq := st.prf.Opening.FRIProof.FRIQueries
		if k >= len(fq) || len(fq[k].Layers) != numRounds-first {
			return nil, fmt.Errorf("FRI queries do not have the verifier's shape")
		}
		if j < first {
			return nil, nil
		}
		return &fq[k].Layers[j-first], nil
	}

	for k := range v.shape.NumQueries {
		q := v.Queries[k]
		bits := v.queryBitsTable(k)
		nc := len(v.DEEP[k])
		lo, hi, leaves := make([]int, nc), make([]int, nc), make([]int, nc)
		for c, dq := range v.DEEP[k] {
			lo[c], hi[c] = dq[0], dq[1]
			leaves[c] = v.leafE6Pair(dq[0], dq[1])
		}
		dlo, dhi := m.Table(lo), m.Table(hi)

		// The levels tree, its path from the opening of round first.
		sibs := make([]int, maxTreeHeight)
		for h := 1; h <= maxTreeHeight; h++ {
			sibs[h-1] = v.input(KindDigest, func(st *statement) (Cell, error) {
				l, err := layer(st, k, v.statementFirst(st))
				if err != nil {
					return Cell{}, err
				}
				top := logN - v.statementFirst(st) - 1
				if len(l.Path.Siblings) != top {
					return Cell{}, fmt.Errorf("the levels tree path does not have the verifier's shape")
				}
				if h > top {
					return Cell{}, nil
				}
				return digestCell(l.Path.Siblings[top-h]), nil
			})
		}
		m.MerklePathDynamic(DynamicPath{
			Leaves: m.Table(leaves), Heights: d.levels.heights, Order: d.levels.order,
			Siblings: m.Table(sibs), Bits: bits, L: logN, Root: v.LevelsRoot,
		})

		// The prefix sums over the sorted levels.
		sl, sh, ss := []int{zero}, []int{zero}, []int{zero}
		for i, pi := range d.levels.pi {
			l, h := m.Lookup(dlo, pi), m.Lookup(dhi, pi)
			sel := m.Add(l, m.Mul(m.Lookup(bits, d.levels.intro[i]), m.Sub(h, l)))
			sl = append(sl, m.Add(sl[i], m.Mul(gammas[i], l)))
			sh = append(sh, m.Add(sh[i], m.Mul(gammas[i], h)))
			ss = append(ss, m.Add(ss[i], m.Mul(gammas[i], sel)))
		}
		tsl, tsh, tss := m.Table(sl), m.Table(sh), m.Table(ss)

		var rounds []FoldRound
		for j := range numRounds {
			value := func(qside bool) int {
				return v.input(KindE6, func(st *statement) (Cell, error) {
					l, err := layer(st, k, j)
					if err != nil || l == nil || j == v.statementFirst(st) {
						return Cell{}, err
					}
					if qside {
						return E6Cell(l.LeafQExt), nil
					}
					return E6Cell(l.LeafPExt), nil
				})
			}
			p, qv := value(false), value(true)
			depth := logN - j - 1
			path := make([]int, depth)
			for i := range path {
				path[i] = v.input(KindDigest, func(st *statement) (Cell, error) {
					l, err := layer(st, k, j)
					if err != nil {
						return Cell{}, err
					}
					if l == nil || j == v.statementFirst(st) {
						return digestCell(z[i]), nil
					}
					if len(l.Path.Siblings) != depth {
						return Cell{}, fmt.Errorf("FRI paths do not have the verifier's shape")
					}
					return digestCell(l.Path.Siblings[i]), nil
				})
			}
			xb := m.MerklePathX(v.leafE6Pair(p, qv), path, q.Shr[j+1], roots[j], gInv[j])
			P := m.Add(p, m.Mul(d.f[j], m.Lookup(tsl, d.b[j])))
			Q := m.Add(qv, m.Mul(d.f[j], m.Lookup(tsh, d.b[j])))
			inj := zero
			if j+1 < numRounds {
				inj = m.Sub(m.Lookup(tss, d.b[j+1]), m.Lookup(tss, d.b[j]))
			}
			rounds = append(rounds, FoldRound{P: P, Q: Q, Alpha: alphas[j], XB: xb, Inj: inj})
		}
		m.FoldChain(rounds, m.Lookup(final, q.Shr[numRounds]))
	}
}

// friLayerValues allocates the inputs of the pair of the FRI query layer j ≥ 1
// (round first + i) opened at query k.
func (v *Verifier) friLayerValues(k, j int) (int, int) {
	layer := func(prf proof.Proof) (fri.QueryLayer, error) {
		fq := prf.Opening.FRIProof.FRIQueries
		if k >= len(fq) || j >= len(fq[k].Layers) {
			return fri.QueryLayer{}, fmt.Errorf("FRI queries do not have the verifier's shape")
		}
		return fq[k].Layers[j], nil
	}
	p := v.input(KindE6, func(st *statement) (Cell, error) {
		prf := st.prf
		l, err := layer(prf)
		return E6Cell(l.LeafPExt), err
	})
	q := v.input(KindE6, func(st *statement) (Cell, error) {
		prf := st.prf
		l, err := layer(prf)
		return E6Cell(l.LeafQExt), err
	})
	return p, q
}

// friSiblings allocates the inputs of the Merkle path of the FRI query layer j
// (round first + j) at query k (layer 0 is the levels tree).
func (v *Verifier) friSiblings(k, j, depth int) []int {
	sibs := make([]int, depth)
	for i := range sibs {
		sibs[i] = v.input(KindDigest, func(st *statement) (Cell, error) {
			prf := st.prf
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
	// zetaN returns ζ^N for a module: ζ^(2^ℓ), a fixed power for a fixed
	// module, read at ℓ from the table of ζ^(2^k), k ≤ MaxLogModuleSize, for
	// a dynamic one.
	var zetaTable *Table
	zetaN := func(mod string) int {
		s := v.sizes[mod]
		if !s.dynamic {
			return zetaPow(s.logN)
		}
		if zetaTable == nil {
			cells := make([]int, MaxLogModuleSize+1)
			for k := range cells {
				cells[k] = zetaPow(k)
			}
			t := m.Table(cells)
			zetaTable = &t
		}
		return m.Lookup(*zetaTable, s.cell)
	}
	// lagrange returns L_i(ζ) = ω^i·(ζ^N − 1) / (N·(ζ − ω^i)) on the domain of
	// a module, for a cell w = ω^i.
	lagrange := func(mod string, w int) int {
		zn1 := m.Sub(zetaN(mod), one)
		den := m.Mul(m.Sub(zeta, w), v.SizeN(mod))
		return m.Div(m.Mul(zn1, w), den)
	}
	// omegaPow returns a cell ω_N^idx for a scalar index cell and a module's
	// ω_N: from the low log2(N) bits of idx for a fixed module (ω_N^N = 1);
	// for a dynamic one, from its low MaxLogModuleSize bits, bit b weighing
	// ω_N^(2^b) (a cell, 1 for b ≥ ℓ).
	omegaPow := func(mod string, idx int) int {
		s := v.sizes[mod]
		if !s.dynamic {
			n := s.logN
			omega, err := koalabear.Generator(uint64(1) << n)
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
		bits := m.Bits(idx, MaxLogModuleSize)
		acc := one
		for b, bit := range bits.Bit {
			g := v.SizeOmega(mod, 1<<b)
			acc = m.Mul(acc, m.Add(m.Mul(bit, m.Sub(g, one)), one))
		}
		return acc
	}
	// weighted returns Σ entries v·L_idx(ζ).
	weighted := func(mod string, entries []entryCells) int {
		acc := zero
		for _, e := range entries {
			term := m.Mul(e.val, lagrange(mod, omegaPow(mod, e.idx)))
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
	// For a dynamic module: below 2^MaxLogModuleSize, and its value shifted
	// by ℓ (read at ℓ from a table of its shifts) is zero.
	for _, p := range v.shape.PublicInputs {
		s, ok := v.sizes[p.Module]
		if !ok {
			return fmt.Errorf("NewVerifier: public input %q of unknown module %q", p.Name, p.Module)
		}
		for _, e := range v.publicEntries[p.Name] {
			if !s.dynamic {
				m.AssertEq(e.idx, m.Bits(e.idx, s.logN).Shr[0])
				continue
			}
			bits := m.Bits(e.idx, MaxLogModuleSize)
			m.AssertEq(e.idx, bits.Shr[0])
			m.AssertEq(m.Lookup(m.Table(append(bits.Shr[:MaxLogModuleSize:MaxLogModuleSize], zero)), s.cell), zero)
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
				// ω_N^i, i < 0 counting from the end (ω_N^−1 = ω_N^(N−1)).
				i := constants.ParseLagrangeName(leaf.Name)
				vals[key] = lagrange(name, v.SizeOmega(name, i))
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
				vals[key] = weighted(name, entries)
			case expr.ExposedValueHook:
				entries, ok := v.exposedEntries[leaf.Name]
				if !ok {
					return fmt.Errorf("NewVerifier: exposed value %q is not bound", leaf.Name)
				}
				vals[key] = weighted(name, entries)
			case expr.ExposedAverageHook:
				entries := v.exposedEntries[leaf.Name]
				if len(entries) != 1 {
					return fmt.Errorf("NewVerifier: exposed average %q must have one entry", leaf.Name)
				}
				vals[key] = m.Mul(entries[0].val, v.SizeInvN(name))
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
		zn := zetaN(name)
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
		case dag.KindAdd:
			// From SumMinTerms terms up, one sum row per SumLanes of them
			// beats one e6 row per addition; below it the e6 chip is cheaper.
			if len(n.Children) >= SumMinTerms {
				terms := make([]int, len(n.Children))
				for i, ch := range n.Children {
					terms[i] = cell[ch]
				}
				cell[n] = m.Sum(terms)
				break
			}
			acc := cell[n.Children[0]]
			for _, ch := range n.Children[1:] {
				acc = m.Add(acc, cell[ch])
			}
			cell[n] = acc
		case dag.KindMul:
			acc := cell[n.Children[0]]
			for _, ch := range n.Children[1:] {
				acc = m.Mul(acc, cell[ch])
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
