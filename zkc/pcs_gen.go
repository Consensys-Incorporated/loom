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
	"slices"
	"sort"
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/hash"
)

// Transcript names and tags of loom's PCS (internal/fri).
const (
	deepAlphaName  = "alpha_DEEP"
	extPolyTag     = 0x45585450 // "EXTP"
	roundsMemory   = "p_roots"
	proofMemory    = "p_in"
	friQueryFn     = "pcs_query"
	merkleStepFn   = "merkle_step"
	queryParamBase = "base"
)

func foldName(j int) string       { return fmt.Sprintf("fri_fold_%d", j) }
func levelGammaName(l int) string { return fmt.Sprintf("fri_level_%d_gamma", l) }
func queryName(k int) string      { return fmt.Sprintf("fri_query_%d", k) }

// Program is a generated zkc verifier together with its input.
type Program struct {
	// Sources maps file names to zkc sources.
	Sources map[string]string
	// Input is the zkc JSON input.
	Input []byte
	// Gadgets define the program's #[native] functions.
	Gadgets zkcv.Gadgets
	// MainPerms and QueryPerms count the Poseidon2 permutations of main and
	// of one query.
	MainPerms, QueryPerms int
}

// rowWidth is the number of words per address of the proof memories.
const rowWidth = 8

// Helper functions reading one row of p_in (relative to a base row) and of
// p_roots. Reads go through them so that the address and value range checks
// happen in their narrow modules, once per module, rather than in the callers:
// a caller only pays one lookup per row, and receives 𝔽 values, which are not
// range-checked.
const (
	loadFn     = "ld8"
	loadRootFn = "ldroot"
)

// reader emits reads of consecutive words of p_in and records the words
// themselves. Words are grouped in rows of rowWidth, each read with one call to
// ld8(base, row). Reads are relative to the row base when it is not empty.
type reader struct {
	e     *Emitter
	base  string
	words []uint32
	row   []string // variables of the current row
	pos   int      // next slot in row; rowWidth when a new row is needed
}

func newReader(e *Emitter, base string) *reader {
	return &reader{e: e, base: base, pos: rowWidth}
}

// align makes the next read start a new row, and returns its word address.
func (r *reader) align() int {
	for r.pos < rowWidth {
		r.words = append(r.words, 0)
		r.pos++
	}
	return len(r.words)
}

func (r *reader) elem(x koalabear.Element) string {
	if r.pos == rowWidth {
		base := r.base
		if base == "" {
			base = "0"
		}
		r.row = r.e.Call(loadFn, rowWidth, base, fmt.Sprint(len(r.words)/rowWidth))
		r.pos = 0
	}
	r.words = append(r.words, uint32(x.Uint64()))
	v := r.row[r.pos]
	r.pos++
	return v
}

func (r *reader) elems(xs []koalabear.Element) []string {
	res := make([]string, len(xs))
	for i := range xs {
		res[i] = r.elem(xs[i])
	}
	return res
}

// e6 reads an extension element from a fresh row.
func (r *reader) e6(x ext.E6) []string {
	r.align()
	return r.elems(hash.ExtToElements(x))
}

// digest reads a digest from a fresh row.
func (r *reader) digest(d hash.Digest) []string {
	r.align()
	return r.elems(d[:])
}

// loadSources defines the proof memories and their row readers.
func loadSources() string {
	var sb strings.Builder
	w := make([]string, rowWidth)
	for i := range w {
		w[i] = fmt.Sprintf("w%d:u32", i)
	}
	fmt.Fprintf(&sb, "pub input %s(address:u16) -> (%s)\n", roundsMemory, strings.Join(w, ", "))
	fmt.Fprintf(&sb, "input %s(address:u16) -> (%s)\n\n", proofMemory, strings.Join(w, ", "))
	x, ws := paramList("x", rowWidth), paramList("w", rowWidth)
	body := func(read string) string {
		var b strings.Builder
		fmt.Fprintf(&b, "    var %s\n", strings.Join(w, ", "))
		fmt.Fprintf(&b, "    %s = %s\n", strings.Join(ws, ", "), read)
		for i := range x {
			fmt.Fprintf(&b, "    %s = %s as 𝔽\n", x[i], ws[i])
		}
		return b.String()
	}
	fmt.Fprintf(&sb, "fn %s(base:u16, k:u16) -> (%s) {\n%s}\n\n", loadFn, typed(x), body(proofMemory+"[base + k]"))
	fmt.Fprintf(&sb, "fn %s(k:u16) -> (%s) {\n%s}\n", loadRootFn, typed(x), body(roundsMemory+"[k]"))
	return sb.String()
}

// friShape is the shape of the FRI part of a fixture.
type friShape struct {
	L          int         // log2 of the full FRI domain size N = RATE·maxN
	numRounds  int         // log2(maxN)
	numQueries int         // number of FRI queries
	levelAt    map[int]int // folding round -> level index (1-based)
	numLevels  int
}

func newFRIShape(f *Fixture) friShape {
	sizes := map[int]bool{}
	for _, b := range f.Config.Batches {
		for _, g := range b {
			sizes[g.LogN] = true
		}
	}
	logs := make([]int, 0, len(sizes))
	for l := range sizes {
		logs = append(logs, l)
	}
	sort.Sort(sort.Reverse(sort.IntSlice(logs)))
	maxLog := logs[0]
	s := friShape{
		L:          maxLog + log2(constants.RATE),
		numRounds:  maxLog,
		numQueries: f.Config.NumQueries,
		levelAt:    map[int]int{},
		numLevels:  len(logs),
	}
	for l := 1; l < len(logs); l++ {
		s.levelAt[maxLog-logs[l]] = l
	}
	return s
}

func log2(n int) int {
	k := 0
	for n > 1 {
		n >>= 1
		k++
	}
	return k
}

// GeneratePCSVerifier returns a zkc program verifying the fixture's PCS
// opening, as fri.PCS.Verify does: the transcript (zeta, alpha_DEEP, FRI
// challenges and query positions), and per query the FRI layers, the batch
// openings and the DEEP bridge.
func GeneratePCSVerifier(f *Fixture) (*Program, error) {
	shape := newFRIShape(f)
	pshape := newPCSShape(f)
	prf := f.Proof.FRIProof

	sponges := map[string]func() string{}
	mainE := Emitter{Sponges: sponges}
	in := newReader(&mainE, "")

	// zeta binds every batch root; root b is row b of p_roots.
	var rootElems []string
	var rootWords []uint32
	for b, r := range f.Roots {
		rootElems = append(rootElems, mainE.Call(loadRootFn, rowWidth, fmt.Sprint(b))...)
		for _, x := range r {
			rootWords = append(rootWords, uint32(x.Uint64()))
		}
	}
	prev := mainE.Challenge(ZetaName, nil, rootElems)
	zeta := prev[:6]

	// alpha_DEEP binds every claimed value in polynomial order.
	values := in.claimedValues(f, pshape)
	var bindings [][]string
	for _, vs := range values {
		for _, pv := range vs {
			bindings = append(bindings, pv...)
		}
	}
	prev = mainE.Challenge(deepAlphaName, prev, bindings...)
	alphaDeep := prev[:6]
	V := emitDeepSums(&mainE, pshape, values, alphaDeep)

	// Opening gadgets: one native function per (batch, group), starting its
	// powers of alpha_DEEP at α^alphaOff.
	groups := newGroups(f, pshape)
	pbases := make([][]string, len(groups))
	for i, gr := range groups {
		pbases[i] = e6Pow(&mainE, alphaDeep, gr.alphaOff)
	}

	// FRI fold and level challenges.
	dqRoots := make([][]string, len(f.Proof.DeepQuotientRoots))
	dqRootAddr := make([]int, len(dqRoots))
	for l, r := range f.Proof.DeepQuotientRoots {
		dqRootAddr[l] = in.align()
		dqRoots[l] = in.digest(r)
	}
	friRootAddr := make([]int, shape.numRounds)
	friRootAddr[0] = dqRootAddr[0]
	alphas := make([][]string, shape.numRounds)
	gammas := make([][]string, shape.numLevels)
	for j := 0; j < shape.numRounds; j++ {
		root := dqRoots[0]
		if j > 0 {
			if l, ok := shape.levelAt[j]; ok {
				prev = mainE.Challenge(levelGammaName(l), prev, dqRoots[l])
				gammas[l] = prev[:6]
			}
			friRootAddr[j] = in.align()
			root = in.digest(prf.FRIRoots[j-1])
		}
		prev = mainE.Challenge(foldName(j), prev, root)
		alphas[j] = prev[:6]
	}

	// Final polynomial: bound to the first query challenge, and checked to be
	// constant (the Go verifier does not check this).
	var finalElems []string
	finalPoly := make([][]string, len(prf.FinalPolyExt))
	for i, v := range prf.FinalPolyExt {
		finalPoly[i] = in.e6(v)
		finalElems = append(finalElems, finalPoly[i]...)
	}
	for i := 1; i < len(finalPoly); i++ {
		mainE.AssertEqAll(finalPoly[i], finalPoly[0])
	}
	queryBinding := append([]string{fmt.Sprint(extPolyTag), fmt.Sprint(len(finalPoly))}, finalElems...)

	// Query challenges, then one fri_query call per query.
	var queryArgs []string
	for j := 0; j < shape.numRounds; j++ {
		queryArgs = append(queryArgs, alphas[j]...)
	}
	for l := 1; l < shape.numLevels; l++ {
		queryArgs = append(queryArgs, gammas[l]...)
	}
	queryArgs = append(queryArgs, finalPoly[0]...)
	queryArgs = append(queryArgs, zeta...)
	queryArgs = append(queryArgs, alphaDeep...)
	for _, vs := range V {
		for _, v := range vs {
			queryArgs = append(queryArgs, v...)
		}
	}
	for _, pb := range pbases {
		queryArgs = append(queryArgs, pb...)
	}
	offs := map[*groupRef]int{}

	queryE := Emitter{Sponges: sponges}
	var queryBody string
	var queryPerms int
	for k := 0; k < shape.numQueries; k++ {
		if k == 0 {
			prev = mainE.Challenge(queryName(0), prev, queryBinding)
		} else {
			prev = mainE.Challenge(queryName(k), prev, prev)
		}
		qr := newReader(&queryE, queryParamBase)
		emitQuery(qr, shape, pshape, groups, offs, f, k, friRootAddr, dqRootAddr)
		if k == 0 {
			queryBody = queryE.String()
			queryPerms = queryE.Perms
		}
		qr.align()
		base := in.align() / rowWidth
		in.words = append(in.words, qr.words...)
		mainE.Line("%s(%d, %s, %d, %s)", friQueryFn, base, prev[1], k, strings.Join(queryArgs, ", "))
		queryE = Emitter{Sponges: sponges}
	}

	// Assemble the program.
	var src strings.Builder
	if rows := in.align() / rowWidth; rows > 1<<16 {
		return nil, fmt.Errorf("proof has %d rows, more than the 2^16 addressable by p_in", rows)
	}
	src.WriteString(loadSources())
	src.WriteString("\n")
	fmt.Fprintf(&src, "fn main() {\n%s}\n\n", mainE.String())
	var params []string
	params = append(params, queryParamBase+":u16", "c1:𝔽", "qid:𝔽")
	for j := 0; j < shape.numRounds; j++ {
		params = append(params, typedList(fmt.Sprintf("a%d_", j), 6)...)
	}
	for l := 1; l < shape.numLevels; l++ {
		params = append(params, typedList(fmt.Sprintf("g%d_", l), 6)...)
	}
	params = append(params, typedList("f", 6)...)
	if n := len(queryArgs) + 3; n > 255 {
		return nil, fmt.Errorf("%s takes %d arguments, more than zkc's limit of 255", friQueryFn, n)
	}
	params = append(params, typedList("z", 6)...)
	params = append(params, typedList("d", 6)...)
	for si, sr := range pshape.sizes {
		for ki := range sr.shifts {
			params = append(params, typedList(fmt.Sprintf("V%d_%d_", si, ki), 6)...)
		}
	}
	for i := range groups {
		params = append(params, typedList(fmt.Sprintf("pb%d_", i), 6)...)
	}
	fmt.Fprintf(&src, "fn %s(%s) {\n%s}\n", friQueryFn, strings.Join(params, ", "), queryBody)
	src.WriteString(merkleStepSource)
	gadgets := Gadgets()
	for _, gr := range groups {
		src.WriteString(gr.openSource(f, offs[gr], sponges))
		gadgets[gr.fn] = &OpeningGadget{f: f, gr: gr}
	}
	src.WriteString(SpongeSources(sponges))
	src.WriteString(assertSource)

	input := fmt.Sprintf(`{"%s": "%s", "%s": "%s"}`,
		roundsMemory, hexWords(rootWords), proofMemory, hexWords(in.words))
	return &Program{
		Sources: map[string]string{
			"e6.zkc":        E6Source(),
			"poseidon2.zkc": Poseidon2Source(),
			"verifier.zkc":  src.String(),
		},
		Input:      []byte(input),
		Gadgets:    gadgets,
		MainPerms:  mainE.Perms,
		QueryPerms: queryPerms,
	}, nil
}

func typedList(prefix string, n int) []string {
	res := make([]string, n)
	for i := range res {
		res[i] = fmt.Sprintf("%s%d:𝔽", prefix, i)
	}
	return res
}

func paramList(prefix string, n int) []string {
	res := make([]string, n)
	for i := range res {
		res[i] = fmt.Sprintf("%s%d", prefix, i)
	}
	return res
}

// emitQuery emits the body of pcs_query for query k: the Merkle openings of
// every FRI layer and level, the folding checks and the final check, the batch
// openings, and the DEEP bridge.
func emitQuery(r *reader, shape friShape, pshape pcsShape, groups []*groupRef, offs map[*groupRef]int, f *Fixture, k int, friRootAddr, dqRootAddr []int) {
	e := r.e
	fq := f.Proof.FRIProof.FRIQueries[k]

	// Bits of the query position: s = c1 mod 2^L (see fri.queryIndex).
	L := shape.numRounds + log2(constants.RATE)
	bitNames := make([]string, L)
	for i := range bitNames {
		bitNames[i] = fmt.Sprintf("sb%d", i)
	}
	e.Line("var sw:u32 = c1 as u32")
	e.Line("var sh:u%d", 32-L)
	for i := L - 1; i >= 0; i-- {
		e.Line("var %s:u1", bitNames[i])
	}
	parts := []string{"sh"}
	for i := L - 1; i >= 0; i-- {
		parts = append(parts, bitNames[i])
	}
	e.Line("%s = sw", strings.Join(parts, "::"))
	s := make([]string, L)
	for i := range s {
		s[i] = e.Let(bitNames[i] + " as 𝔽")
	}

	// xInv_0 = Π (s_{1+i} ? c_i : 1)
	c := foldPointConstants(L)
	x := "1"
	for i := range c {
		var cm1 koalabear.Element
		one := koalabear.One()
		cm1.Sub(&c[i], &one)
		x = e.Let(fmt.Sprintf("%s * (1 + (%s * %s))", x, s[1+i], felt(cm1)))
	}

	// absRoot re-reads a digest that main read at word address addr (a row
	// start): the same memory row, hence the same value.
	absRoot := func(addr int) []string {
		return e.Call(loadFn, rowWidth, "0", fmt.Sprint(addr/rowWidth))
	}
	// openPair reads the pair (P, Q) of an ext layer of rows s >> layer and
	// checks its Merkle path (index s >> (layer+1)) against the root at rootAddr.
	openPair := func(layer int, P, Q ext.E6, siblings []hash.Digest, rootAddr int) ([]string, []string) {
		p, q := r.e6(P), r.e6(Q)
		h := e.Sponge(slices.Concat([]string{fmt.Sprint(LeafDomainTag), "0", "2"}, p, q))
		for i, sib := range siblings {
			h = e.MerkleStep(h, r.digest(sib), s[layer+1+i])
		}
		e.AssertEqAll(h, absRoot(rootAddr))
		return p, q
	}

	// Open every FRI layer, and every level at its introduction round.
	type pair struct{ p, q []string }
	layers := make([]pair, shape.numRounds)
	levels := map[int]pair{}
	for j := 0; j < shape.numRounds; j++ {
		layer := fq.Layers[j]
		p, q := openPair(j, layer.LeafPExt, layer.LeafQExt, layer.Path.Siblings, friRootAddr[j])
		layers[j] = pair{p, q}
		if l, ok := shape.levelAt[j]; ok && j > 0 {
			ld := f.Proof.FRIProof.LevelQueries[l-1][k]
			lp, lq := openPair(j, ld.LeafPExt, ld.LeafQExt, ld.Path.Siblings, dqRootAddr[l])
			levels[j] = pair{lp, lq}
		}
	}

	// Open every batch at the query, and check the DEEP bridge for each size
	// against the FRI layer 0 (largest size) or the level opened at the size's
	// introduction round.
	pbase := map[*groupRef][]string{}
	for i, gr := range groups {
		pbase[gr] = paramList(fmt.Sprintf("pb%d_", i), 6)
	}
	sums := map[*groupRef]groupSums{}
	for b := range f.Roots {
		root := e.Call(loadRootFn, rowWidth, fmt.Sprint(b))
		emitBatchOpening(r, s, L, f, b, k, root, groups, pbase, offs, sums)
	}
	for si, sr := range pshape.sizes {
		dq := layers[0]
		if si > 0 {
			dq = levels[shape.numRounds-sr.logN]
		}
		V := make([][]string, len(sr.shifts))
		for ki := range sr.shifts {
			V[ki] = paramList(fmt.Sprintf("V%d_%d_", si, ki), 6)
		}
		var sizeGroups []*groupRef
		for _, gr := range groups {
			if gr.logN == sr.logN {
				sizeGroups = append(sizeGroups, gr)
			}
		}
		emitDeepBridge(r, s, L, f, k, sr, sizeGroups, sums, V, paramList("z", 6), dq.p, dq.q)
	}

	// Fold: expected_j = (P+Q)/2 + α_j·(P−Q)/2·xInv_j must equal the next
	// layer's P or Q (by bit s_{j+1}), after adding γ_l·(level P or Q) when a
	// level enters; the last fold must equal the final polynomial.
	inv2 := felt(invTwo())
	for j := 0; j < shape.numRounds; j++ {
		p, q := layers[j].p, layers[j].q
		alpha := paramList(fmt.Sprintf("a%d_", j), 6)
		sum := e.Call("e6_mul_base", 6, append(e.Call("e6_add", 6, slices.Concat(p, q)...), inv2)...)
		diff := e.Call("e6_mul_base", 6, append(e.Call("e6_sub", 6, slices.Concat(p, q)...), inv2)...)
		diff = e.Call("e6_mul_base", 6, append(diff, x)...)
		expected := e.Call("e6_add", 6, slices.Concat(sum, e.Call("e6_mul", 6, slices.Concat(diff, alpha)...))...)

		if j == shape.numRounds-1 {
			e.AssertEqAll(expected, paramList("f", 6))
			break
		}
		if lv, ok := levels[j+1]; ok {
			l := shape.levelAt[j+1]
			leaf := selectE6(e, s[j+1], lv.p, lv.q)
			term := e.Call("e6_mul", 6, slices.Concat(leaf, paramList(fmt.Sprintf("g%d_", l), 6))...)
			expected = e.Call("e6_add", 6, slices.Concat(expected, term)...)
		}
		next := layers[j+1]
		e.AssertEqAll(expected, selectE6(e, s[j+1], next.p, next.q))

		// xInv_{j+1} = xInv_j² · (1 − 2·s_{j+1})
		x = e.Let(fmt.Sprintf("(%s * %s) * (1 - (2 * %s))", x, x, s[j+1]))
	}
}

func selectE6(e *Emitter, b string, x, y []string) []string {
	res := make([]string, len(x))
	for i := range x {
		res[i] = e.Select(b, x[i], y[i])
	}
	return res
}

func invTwo() koalabear.Element {
	var r koalabear.Element
	r.SetUint64(2)
	r.Inverse(&r)
	return r
}

// merkleStepSource defines merkle_step: one level of a Merkle path, hashing
// (h, sib) if the index bit b is 0 and (sib, h) otherwise.
var merkleStepSource = func() string {
	var sb strings.Builder
	h, s, p := paramList("h", 8), paramList("s", 8), paramList("p", 8)
	fmt.Fprintf(&sb, "\nfn %s(%s, %s, b:𝔽) -> (%s) {\n", merkleStepFn,
		strings.Join(typedList("h", 8), ", "), strings.Join(typedList("s", 8), ", "), typed(p))
	var l, r []string
	for i := range h {
		fmt.Fprintf(&sb, "    var l%d:𝔽 = %s + (b * (%s - %s))\n", i, h[i], s[i], h[i])
		fmt.Fprintf(&sb, "    var r%d:𝔽 = %s + (b * (%s - %s))\n", i, s[i], h[i], s[i])
		l = append(l, fmt.Sprintf("l%d", i))
		r = append(r, fmt.Sprintf("r%d", i))
	}
	fmt.Fprintf(&sb, "    %s = p2_node(%s, %s)\n}\n", strings.Join(p, ", "), strings.Join(l, ", "), strings.Join(r, ", "))
	return sb.String()
}()
