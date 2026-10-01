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

package fri

import (
	"fmt"
	"math/bits"
	"sort"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/field"

	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/merkle"
	"github.com/consensys/loom/internal/parallel"
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/internal/reedsolomon"
)

// foldParallelThreshold is the smallest half-layer size at which fan-out
// across goroutines beats the precomputed-xInv seeding overhead per chunk.
const foldParallelThreshold = 1 << 12

// Params holds the FRI configuration and precomputed per-level data.
// Build once with NewParams; reuse across many Prove/Verify calls.
type Params struct {
	N          int // 2^n: size of the evaluation domain
	D          int // 2^m: degree of the purported polynomial
	NumQueries int // number of independent queries (controls soundness error ≈ (1-δ)^Q)
	LeafHasher LeafHasher
	NodeHasher NodeHasher

	numRounds    int // numRounds = m
	invTwo       koalabear.Element
	domains      []*fft.Domain // domains[j] has cardinality N/2^j, generator ωⱼ
	domainsLight []domainLight // domainLight stores only the cardinality and the domain generator
	grinding     int           // grinding bits for PoW, on the alpha
}

type Config struct {
	WoFullDomainAllocation bool
	Grinding               int // grinding bits for PoW. More grinding bits => more cpu work for the prover, but security goes from log_blowup * num_queries to log_blowup * num_queries + query_proof_of_work_bits
}

type Option func(c *Config) error

// WoFullDomainAllocation useful for the verifier -> only the generator of the domain is needed, no need to pre-compute the twiddles.
func WoFullDomainAllocation() Option {
	return func(c *Config) error {
		c.WoFullDomainAllocation = true
		return nil
	}
}

// WithGrinding forces the folding challenges to start with nbBits at zeroes, to increase security
// It lowers the space <wrong proof x miraculously valid challenges>.
// Security goes from log_blowup * num_queries to log_blowup * num_queries + query_proof_of_work_bits.
func WithGrinding(nbBits int) Option {
	return func(c *Config) error {
		c.Grinding = nbBits
		return nil
	}
}

// NewParams constructs and validates a Params, precomputing r+1 domains and inv(2).
func NewParams(N, D, numQueries int, lh LeafHasher, nh NodeHasher, opts ...Option) (Params, error) {
	if N <= 0 || N&(N-1) != 0 {
		return Params{}, fmt.Errorf("fri: N must be a positive power of two, got %d", N)
	}
	if D <= 0 || D&(D-1) != 0 {
		return Params{}, fmt.Errorf("fri: D must be a positive power of two, got %d", D)
	}
	if D >= N {
		return Params{}, fmt.Errorf("fri: D must be < N, got D=%d N=%d", D, N)
	}
	if numQueries <= 0 {
		return Params{}, fmt.Errorf("fri: numQueries must be positive, got %d", numQueries)
	}

	var config Config
	for _, opt := range opts {
		if err := opt(&config); err != nil {
			return Params{}, err
		}
	}

	numRounds := log2(D) // r = m = log₂(D)

	var two, invTwo koalabear.Element
	two.SetUint64(2)
	invTwo.Inverse(&two)

	res := Params{
		N:          N,
		D:          D,
		NumQueries: numQueries,
		LeafHasher: lh,
		NodeHasher: nh,
		numRounds:  numRounds,
		invTwo:     invTwo,
		grinding:   config.Grinding,
	}

	if !config.WoFullDomainAllocation {
		res.domains = make([]*fft.Domain, numRounds+1)
		for j := 0; j <= numRounds; j++ {
			res.domains[j] = fft.NewDomain(uint64(N) >> j)
		}
	}
	res.domainsLight = make([]domainLight, numRounds+1)
	for j := 0; j <= numRounds; j++ {
		g, err := koalabear.Generator(uint64(N) >> j)
		if err != nil {
			return Params{}, err
		}
		res.domainsLight[j] = domainLight{cardinality: uint64(N) >> j, generator: g}

	}

	return res, nil
}

type domainLight struct {
	cardinality uint64
	generator   koalabear.Element
}

// Bit-reversed row convention: every RS-encoded vector committed by FRI is
// stored in bit-reversed evaluation order. If a layer has N rows, row r stores
// the evaluation at omega_N^bitrev_log2(N)(r). The FRI companion row is r^1,
// the oriented pair is lo = r&^1 and hi = lo+1, and the next folded-layer row
// is r>>1.
//
// QueryLayer holds the adjacent row openings for one FRI level. Exactly one
// rail is populated, selected by Field. Row is the sampled full-domain row
// projected to this level; LeafP is the value at row Row&^1 and LeafQ is the
// value at row (Row&^1)+1. Path authenticates the adjacent pair leaf containing
// both values, with Path.LeafIdx == (Row&^1)/2.
type QueryLayer struct {
	Field     field.Kind
	Row       int
	LeafPBase koalabear.Element // populated when Field == field.Base
	LeafQBase koalabear.Element
	LeafPExt  ext.E6 // populated when Field == field.Ext
	LeafQExt  ext.E6
	Path      merkle.Proof // authenticates the adjacent pair containing LeafP and LeafQ
}

// Query holds the opening data for one full query path across all folding
// levels of the running FRI polynomial.
type Query struct {
	Layers []QueryLayer // len = numRounds
}

// ────────────────────────────────────────────────────────────────────────────────
// Multi-degree FRI types (see multi_degree_fri.txt for the full protocol spec)
// ────────────────────────────────────────────────────────────────────────────────

// LevelEvals stores the evaluation vector for one FRI level. Exactly one rail
// must be populated; callers must fold any extra same-degree polynomials before
// invoking FRI.
type LevelEvals struct {
	Base []koalabear.Element
	Ext  []ext.E6
}

// Field returns the populated rail. Invalid mixed/empty values are rejected by
// Prove's validation; the zero value reports field.Base.
func (e LevelEvals) Field() field.Kind {
	if len(e.Ext) > 0 {
		return field.Ext
	}
	return field.Base
}

func (e LevelEvals) checkedField() (field.Kind, error) {
	hasBase := len(e.Base) > 0
	hasExt := len(e.Ext) > 0
	switch {
	case hasBase && hasExt:
		return field.Base, fmt.Errorf("both base and ext rails are populated")
	case !hasBase && !hasExt:
		return field.Base, fmt.Errorf("no rail is populated")
	case hasExt:
		return field.Ext, nil
	default:
		return field.Base, nil
	}
}

func (e LevelEvals) Len() int {
	if e.Field() == field.Ext {
		return len(e.Ext)
	}
	return len(e.Base)
}

// Level holds one polynomial introduced at the folding round where the running
// polynomial's degree matches Level.D. Tree is the pre-built pair-leaf Merkle
// tree for Evals; build it with Params.BuildLevelTree or Params.BuildLevelTreeExt
// so the leaf/node hashers match.
type Level struct {
	D     int
	Evals LevelEvals
	Tree  *merkle.Tree
}

// Proof is the complete multi-degree FRI proof. Level polynomial Merkle roots
// are NOT stored here — they are passed externally to Verify (the caller
// commits to those polynomials before invoking FRI).
type Proof struct {
	// LevelQueries[l-1][k] is the adjacent row opening for levels[l].Evals at
	// outer query k. The stored Row is the full query row shifted to the round
	// where that level is introduced.
	LevelQueries [][]QueryLayer

	// Running-polynomial FRI path.
	FRIRoots      []hash.Digest // Merkle roots for running poly T_1..T_{r-1}
	FinalField    field.Kind
	FinalPolyBase []koalabear.Element               // populated when FinalField == field.Base
	FinalPolyExt  []ext.E6                          // populated when FinalField == field.Ext
	FRIQueries    []Query                           // one full-row query path per FRI query
	PoW           map[string]fiatshamir.ProofOfWork // proof of work in case grinding has nbBits > 0
}

// FullDomainGenerator returns the generator of the full evaluation domain (layer 0, size N).
func (p Params) FullDomainGenerator() koalabear.Element {
	return p.domains[0].Generator
}

// Encode converts a polynomial from Lagrange form (size D) to its evaluation
// on the full domain of size N. The result is a₀, ready to pass to Prove.
func (p Params) Encode(poly []koalabear.Element) ([]koalabear.Element, error) {
	if len(poly) != p.D {
		return nil, fmt.Errorf("fri: Encode: polynomial length %d != D=%d", len(poly), p.D)
	}
	enc := reedsolomon.NewEncoder(uint64(p.N))
	domainD := fft.NewDomain(uint64(p.D))
	return enc.Encode(poly, domainD), nil
}

// EncodeExt is the extension-field counterpart of Encode.
func (p Params) EncodeExt(poly []ext.E6) ([]ext.E6, error) {
	if len(poly) != p.D {
		return nil, fmt.Errorf("fri: EncodeExt: polynomial length %d != D=%d", len(poly), p.D)
	}
	enc := reedsolomon.NewEncoder(uint64(p.N))
	domainD := fft.NewDomain(uint64(p.D))
	return enc.EncodeExt(poly, domainD), nil
}

// BuildLevelTree builds the pair-leaf Merkle tree expected by FRI for a base
// level polynomial: tree leaf k = LeafHasher(layer[2*k], layer[2*k+1]).
func (p Params) BuildLevelTree(layer []koalabear.Element) (*merkle.Tree, error) {
	return buildTreeBase(layer, p.LeafHasher, p.NodeHasher)
}

// BuildLevelTreeExt builds the pair-leaf Merkle tree expected by FRI for an
// extension-field level polynomial.
func (p Params) BuildLevelTreeExt(layer []ext.E6) (*merkle.Tree, error) {
	return buildTreeExt(layer, p.LeafHasher, p.NodeHasher)
}

// ────────────────────────────────────────────────────────────────────────────────
// Prove — multi-degree FRI prover
// ────────────────────────────────────────────────────────────────────────────────

// Prove runs multi-degree FRI (commit + query phase) and returns a Proof together
// with the query positions. levels[0].D must equal p.D and every Level must
// contain one evaluation vector on exactly one rail. levels is sorted in-place
// in decreasing order of D, stably: levels of equal D keep their order.
//
// Level l enters at round j_l = log2(p.D / D_l). Several levels may share a
// round, round 0 included: the running polynomial at round j adds γ_l·level_l
// for every level entering at j, in level order. At round 0 the committed
// layer is levels[0].Tree itself; the levels entering at round 0 are only
// mixed into the polynomial that is folded.
// ts must already have been initialised with any prior-round context.
func Prove(p Params, levels []Level, ts *fiatshamir.Transcript) (Proof, []int, error) {
	sort.SliceStable(levels, func(i, j int) bool { return levels[i].D > levels[j].D })

	plan, err := buildProvePlan(p, levels)
	if err != nil {
		return Proof{}, nil, err
	}
	registerChallenges(p, plan.levelAtRound, ts)

	if plan.rail == field.Ext {
		return proveExt(p, levels, plan, ts)
	}
	return proveBase(p, levels, plan, ts)
}

type provePlan struct {
	rail         field.Kind
	numLevels    int
	levelAtRound map[int][]int // round j → levels entering at j (l ≥ 1), in order
}

func buildProvePlan(p Params, levels []Level) (provePlan, error) {
	var plan provePlan
	if len(levels) == 0 {
		return plan, fmt.Errorf("fri: Prove: at least one level required")
	}
	if levels[0].D != p.D {
		return plan, fmt.Errorf("fri: Prove: levels[0].D=%d must equal p.D=%d", levels[0].D, p.D)
	}
	rail, err := levels[0].Evals.checkedField()
	if err != nil {
		return plan, fmt.Errorf("fri: Prove: levels[0].Evals: %w", err)
	}
	plan.rail = rail
	if levels[0].Evals.Len() != p.N {
		return plan, fmt.Errorf("fri: Prove: levels[0].Evals length %d != N=%d", levels[0].Evals.Len(), p.N)
	}
	if levels[0].Tree == nil {
		return plan, fmt.Errorf("fri: Prove: levels[0].Tree is nil")
	}

	plan.numLevels = len(levels)

	// Build levelAtRound: folding round j → level indices l ≥ 1.
	plan.levelAtRound = make(map[int][]int, plan.numLevels-1)
	for l := 1; l < plan.numLevels; l++ {
		if levels[l].D <= 0 || levels[l].D&(levels[l].D-1) != 0 {
			return plan, fmt.Errorf("fri: Prove: levels[%d].D=%d is not a positive power of two", l, levels[l].D)
		}
		levelRail, err := levels[l].Evals.checkedField()
		if err != nil {
			return plan, fmt.Errorf("fri: Prove: levels[%d].Evals: %w", l, err)
		}
		if levelRail != rail {
			return plan, fmt.Errorf("fri: Prove: levels[%d] is %s, running rail is %s", l, levelRail, rail)
		}
		jl := log2(p.D / levels[l].D)
		if levels[l].D > p.D || jl >= p.numRounds {
			return plan, fmt.Errorf("fri: Prove: levels[%d].D=%d gives intro round %d, must be in 0..%d", l, levels[l].D, jl, p.numRounds-1)
		}
		plan.levelAtRound[jl] = append(plan.levelAtRound[jl], l)
		Nl := p.N >> jl
		if levels[l].Evals.Len() != Nl {
			return plan, fmt.Errorf("fri: Prove: levels[%d].Evals length %d != N_l=%d", l, levels[l].Evals.Len(), Nl)
		}
		if levels[l].Tree == nil {
			return plan, fmt.Errorf("fri: Prove: levels[%d].Tree is nil", l)
		}
	}

	return plan, nil
}

// registerChallenges registers, for each round j, the γ of every level
// entering at j, then the fold challenge of round j, then the queries.
func registerChallenges(p Params, levelAtRound map[int][]int, ts *fiatshamir.Transcript) {
	for j := 0; j < p.numRounds; j++ {
		for _, l := range levelAtRound[j] {
			ts.NewChallenge(levelGammaName(l))
		}
		ts.NewChallenge(foldName(j))
	}
	for k := 0; k < p.NumQueries; k++ {
		ts.NewChallenge(queryName(k))
	}
}

// deriveLevelGamma binds the root of level l to its γ and computes it. The
// first γ of round 0 also binds levelRoot0 first: a level entering at round 0
// is combined with level 0, whose root is otherwise bound only at fri_fold_0,
// after the γ.
func deriveLevelGamma(ts *fiatshamir.Transcript, l int, root hash.Digest, bindRoot0 bool, levelRoot0 hash.Digest) ([8]koalabear.Element, error) {
	gammaName := levelGammaName(l)
	if bindRoot0 {
		if err := ts.Bind(gammaName, levelRoot0[:]); err != nil {
			return [8]koalabear.Element{}, fmt.Errorf("bind level 0 root for γ_%d: %w", l, err)
		}
	}
	if err := ts.Bind(gammaName, root[:]); err != nil {
		return [8]koalabear.Element{}, fmt.Errorf("bind level l=%d: %w", l, err)
	}
	challenge, err := ts.ComputeChallenge(gammaName)
	if err != nil {
		return [8]koalabear.Element{}, fmt.Errorf("compute level gamma l=%d: %w", l, err)
	}
	return challenge, nil
}

func proveBase(p Params, levels []Level, plan provePlan, ts *fiatshamir.Transcript) (Proof, []int, error) {
	// ── Commit phase ─────────────────────────────────────────────────────────

	// running is the current evaluation vector; copy levels[0].Evals.Base so we own it.
	running := make([]koalabear.Element, p.N)
	copy(running, levels[0].Evals.Base)

	layers := make([][]koalabear.Element, p.numRounds+1)
	friTrees := make([]*merkle.Tree, p.numRounds)
	alphas := make([]koalabear.Element, p.numRounds)

	var prf Proof
	if p.numRounds > 1 {
		prf.FRIRoots = make([]hash.Digest, p.numRounds-1)
	}

	for j := 0; j < p.numRounds; j++ {
		// layers[j] = running after batching, before folding (= what T_j
		// commits to). At round 0 the committed layer is levels[0] alone.
		if j == 0 {
			layers[0] = levels[0].Evals.Base
		}
		// Level batching step: mix γ_l·levels[l].Evals into running, for every
		// level entering at round j.
		for i, l := range plan.levelAtRound[j] {
			challenge, err := deriveLevelGamma(ts, l, levels[l].Tree.Root(), j == 0 && i == 0, levels[0].Tree.Root())
			if err != nil {
				return Proof{}, nil, fmt.Errorf("fri: Prove: %w", err)
			}
			var gamma koalabear.Element
			gamma.Set(&challenge[0])
			for k, v := range levels[l].Evals.Base {
				var term koalabear.Element
				term.Mul(&v, &gamma)
				running[k].Add(&running[k], &term)
			}
		}
		if j > 0 {
			layers[j] = running
		}

		var tree *merkle.Tree
		if j == 0 {
			tree = levels[0].Tree // caller-supplied, root must match running pre-fold
		} else {
			var err error
			tree, err = buildTreeBase(running, p.LeafHasher, p.NodeHasher)
			if err != nil {
				return Proof{}, nil, fmt.Errorf("fri: Prove: build tree layer %d: %w", j, err)
			}
		}
		friTrees[j] = tree
		root := tree.Root()

		name := foldName(j)
		if err := ts.Bind(name, root[:]); err != nil {
			return Proof{}, nil, fmt.Errorf("fri: Prove: bind fold %d: %w", j, err)
		}
		challenge, err := computeProverFoldChallenge(ts, name, p.grinding)
		if err != nil {
			return Proof{}, nil, fmt.Errorf("fri: Prove: compute fold challenge %d: %w", j, err)
		}
		alphas[j].Set(&challenge[0])

		// Root of T_0 is passed to Verify separately; only T_1..T_{r-1} go in the proof.
		if j > 0 {
			prf.FRIRoots[j-1] = root
		}

		// foldLayer returns a new slice, so running for round j+1 is independent.
		running = foldLayerBase(running, alphas[j], p.domains[j], p.invTwo)
	}
	layers[p.numRounds] = running
	prf.FinalField = field.Base
	prf.FinalPolyBase = running
	if err := recordFoldProofsOfWork(p, &prf, ts); err != nil {
		return Proof{}, nil, fmt.Errorf("fri: Prove: record proof of work: %w", err)
	}

	if err := ts.Bind(queryName(0), transcriptBasePoly(prf.FinalPolyBase)); err != nil {
		return Proof{}, nil, fmt.Errorf("fri: Prove: bind final poly: %w", err)
	}

	// ── Query phase ───────────────────────────────────────────────────────────

	prf.FRIQueries = make([]Query, p.NumQueries)
	if plan.numLevels > 1 {
		prf.LevelQueries = make([][]QueryLayer, plan.numLevels-1)
		for l := range prf.LevelQueries {
			prf.LevelQueries[l] = make([]QueryLayer, p.NumQueries)
		}
	}

	queryPositions := make([]int, p.NumQueries)
	for k := 0; k < p.NumQueries; k++ {
		challenge, err := ts.ComputeChallenge(queryName(k))
		if err != nil {
			return Proof{}, nil, fmt.Errorf("fri: Prove: compute query challenge %d: %w", k, err)
		}
		s := queryIndex(challenge, p.N)
		queryPositions[k] = s

		if k < p.NumQueries-1 {
			if err := ts.Bind(queryName(k+1), challenge[:]); err != nil {
				return Proof{}, nil, fmt.Errorf("fri: Prove: bind query chain %d: %w", k+1, err)
			}
		}

		q, err := openQueryBase(s, layers, friTrees, p.numRounds)
		if err != nil {
			return Proof{}, nil, fmt.Errorf("fri: Prove: open FRI query %d: %w", k, err)
		}
		prf.FRIQueries[k] = q

		for l := 1; l < plan.numLevels; l++ {
			jl := log2(p.D / levels[l].D)
			row := s >> jl
			lo, hi := siblingRows(row)
			pairIdx := lo / 2

			path, err := levels[l].Tree.OpenProof(pairIdx)
			if err != nil {
				return Proof{}, nil, fmt.Errorf("fri: Prove: open level query l=%d k=%d pair=%d: %w", l, k, pairIdx, err)
			}
			prf.LevelQueries[l-1][k] = QueryLayer{
				Field:     field.Base,
				Row:       row,
				LeafPBase: levels[l].Evals.Base[lo],
				LeafQBase: levels[l].Evals.Base[hi],
				Path:      path,
			}
		}
	}

	return prf, queryPositions, nil
}

func proveExt(p Params, levels []Level, plan provePlan, ts *fiatshamir.Transcript) (Proof, []int, error) {
	running := make([]ext.E6, p.N)
	copy(running, levels[0].Evals.Ext)

	layers := make([][]ext.E6, p.numRounds+1)
	friTrees := make([]*merkle.Tree, p.numRounds)
	alphas := make([]ext.E6, p.numRounds)

	var prf Proof
	if p.numRounds > 1 {
		prf.FRIRoots = make([]hash.Digest, p.numRounds-1)
	}

	for j := 0; j < p.numRounds; j++ {
		if j == 0 {
			layers[0] = levels[0].Evals.Ext
		}
		for i, l := range plan.levelAtRound[j] {
			challenge, err := deriveLevelGamma(ts, l, levels[l].Tree.Root(), j == 0 && i == 0, levels[0].Tree.Root())
			if err != nil {
				return Proof{}, nil, fmt.Errorf("fri: Prove: %w", err)
			}
			gamma := hash.OutputToExt(challenge)
			for k, v := range levels[l].Evals.Ext {
				var term ext.E6
				term.Mul(&v, &gamma)
				running[k].Add(&running[k], &term)
			}
		}
		if j > 0 {
			layers[j] = running
		}

		var tree *merkle.Tree
		if j == 0 {
			tree = levels[0].Tree
		} else {
			var err error
			tree, err = buildTreeExt(running, p.LeafHasher, p.NodeHasher)
			if err != nil {
				return Proof{}, nil, fmt.Errorf("fri: Prove: build tree layer %d: %w", j, err)
			}
		}
		friTrees[j] = tree
		root := tree.Root()

		name := foldName(j)
		if err := ts.Bind(name, root[:]); err != nil {
			return Proof{}, nil, fmt.Errorf("fri: Prove: bind fold %d: %w", j, err)
		}
		challenge, err := computeProverFoldChallenge(ts, name, p.grinding)
		if err != nil {
			return Proof{}, nil, fmt.Errorf("fri: Prove: compute fold challenge %d: %w", j, err)
		}
		alphas[j] = hash.OutputToExt(challenge)

		if j > 0 {
			prf.FRIRoots[j-1] = root
		}

		running = foldLayerExt(running, alphas[j], p.domains[j], p.invTwo)
	}
	layers[p.numRounds] = running
	prf.FinalField = field.Ext
	prf.FinalPolyExt = running
	if err := recordFoldProofsOfWork(p, &prf, ts); err != nil {
		return Proof{}, nil, fmt.Errorf("fri: Prove: record proof of work: %w", err)
	}

	if err := ts.Bind(queryName(0), transcriptExtPoly(prf.FinalPolyExt)); err != nil {
		return Proof{}, nil, fmt.Errorf("fri: Prove: bind final poly: %w", err)
	}

	prf.FRIQueries = make([]Query, p.NumQueries)
	if plan.numLevels > 1 {
		prf.LevelQueries = make([][]QueryLayer, plan.numLevels-1)
		for l := range prf.LevelQueries {
			prf.LevelQueries[l] = make([]QueryLayer, p.NumQueries)
		}
	}

	queryPositions := make([]int, p.NumQueries)
	for k := 0; k < p.NumQueries; k++ {
		challenge, err := ts.ComputeChallenge(queryName(k))
		if err != nil {
			return Proof{}, nil, fmt.Errorf("fri: Prove: compute query challenge %d: %w", k, err)
		}
		s := queryIndex(challenge, p.N)
		queryPositions[k] = s

		if k < p.NumQueries-1 {
			if err := ts.Bind(queryName(k+1), challenge[:]); err != nil {
				return Proof{}, nil, fmt.Errorf("fri: Prove: bind query chain %d: %w", k+1, err)
			}
		}

		q, err := openQueryExt(s, layers, friTrees, p.numRounds)
		if err != nil {
			return Proof{}, nil, fmt.Errorf("fri: Prove: open FRI query %d: %w", k, err)
		}
		prf.FRIQueries[k] = q

		for l := 1; l < plan.numLevels; l++ {
			jl := log2(p.D / levels[l].D)
			row := s >> jl
			lo, hi := siblingRows(row)
			pairIdx := lo / 2

			path, err := levels[l].Tree.OpenProof(pairIdx)
			if err != nil {
				return Proof{}, nil, fmt.Errorf("fri: Prove: open level query l=%d k=%d pair=%d: %w", l, k, pairIdx, err)
			}
			prf.LevelQueries[l-1][k] = QueryLayer{
				Field:    field.Ext,
				Row:      row,
				LeafPExt: levels[l].Evals.Ext[lo],
				LeafQExt: levels[l].Evals.Ext[hi],
				Path:     path,
			}
		}
	}

	return prf, queryPositions, nil
}

// ────────────────────────────────────────────────────────────────────────────────
// Verify — multi-degree FRI verifier
// ────────────────────────────────────────────────────────────────────────────────

// Verify checks a multi-degree FRI proof.
//
// levelRoots[l] is the Merkle root of levels[l].Evals (committed by the caller
// before invoking FRI). levelRoots[0] plays the role of "root0" in
// single-degree FRI.
//
// levelDs[l] is the polynomial-size parameter D for level l; levelDs[0] must
// equal p.D and the slice must be ordered consistently with how Prove was
// called (i.e. decreasing D).
//
// ts must be in the same state as when Prove was called.
func Verify(p Params, levelRoots []hash.Digest, levelDs []int, prf Proof, ts *fiatshamir.Transcript) error {
	if len(levelDs) == 0 {
		return fmt.Errorf("fri: Verify: at least one level required")
	}
	if len(levelRoots) != len(levelDs) {
		return fmt.Errorf("fri: Verify: levelRoots has %d entries, levelDs has %d", len(levelRoots), len(levelDs))
	}
	if levelDs[0] != p.D {
		return fmt.Errorf("fri: Verify: levelDs[0]=%d must equal p.D=%d", levelDs[0], p.D)
	}

	numLevels := len(levelDs)
	numExtraLevels := numLevels - 1

	wantFRIRoots := p.numRounds - 1
	if p.numRounds <= 1 {
		wantFRIRoots = 0
	}
	if len(prf.FRIRoots) != wantFRIRoots {
		return fmt.Errorf("fri: Verify: proof has %d FRI roots, want %d", len(prf.FRIRoots), wantFRIRoots)
	}
	if len(prf.FRIQueries) != p.NumQueries {
		return fmt.Errorf("fri: Verify: proof has %d FRI queries, want %d", len(prf.FRIQueries), p.NumQueries)
	}
	if len(prf.LevelQueries) != numExtraLevels {
		return fmt.Errorf("fri: Verify: proof has %d level query sets, want %d", len(prf.LevelQueries), numExtraLevels)
	}
	for l, qs := range prf.LevelQueries {
		if len(qs) != p.NumQueries {
			return fmt.Errorf("fri: Verify: proof has %d queries for extra level %d, want %d", len(qs), l+1, p.NumQueries)
		}
	}
	if prf.FinalField != field.Base && prf.FinalField != field.Ext {
		return fmt.Errorf("fri: Verify: invalid final field %s", prf.FinalField)
	}
	if prf.FinalField == field.Base && len(prf.FinalPolyBase) == 0 {
		return fmt.Errorf("fri: Verify: base final field with empty FinalPolyBase")
	}
	if prf.FinalField == field.Ext && len(prf.FinalPolyExt) == 0 {
		return fmt.Errorf("fri: Verify: ext final field with empty FinalPolyExt")
	}

	// levelAtRound: folding round j → level indices l ≥ 1, in order.
	levelAtRound := make(map[int][]int, numExtraLevels)
	for l := 1; l < numLevels; l++ {
		if levelDs[l] <= 0 || levelDs[l]&(levelDs[l]-1) != 0 {
			return fmt.Errorf("fri: Verify: levelDs[%d]=%d is not a positive power of two", l, levelDs[l])
		}
		if levelDs[l] > levelDs[l-1] {
			return fmt.Errorf("fri: Verify: levelDs must not increase (levelDs[%d]=%d > levelDs[%d]=%d)", l, levelDs[l], l-1, levelDs[l-1])
		}
		ratio := p.D / levelDs[l]
		if ratio <= 0 || ratio*levelDs[l] != p.D || ratio&(ratio-1) != 0 {
			return fmt.Errorf("fri: Verify: levelDs[%d]=%d does not divide p.D=%d by a power-of-two ratio", l, levelDs[l], p.D)
		}
		jl := log2(ratio)
		if jl >= p.numRounds {
			return fmt.Errorf("fri: Verify: levelDs[%d]=%d gives intro round %d, must be in 0..%d", l, levelDs[l], jl, p.numRounds-1)
		}
		levelAtRound[jl] = append(levelAtRound[jl], l)
	}

	registerChallenges(p, levelAtRound, ts)

	// Assemble FRI running-polynomial roots: roots[0] is the level-0 root;
	// roots[1..r-1] come from prf.FRIRoots.
	roots := make([]hash.Digest, p.numRounds)
	roots[0] = levelRoots[0]
	for j := 1; j < p.numRounds; j++ {
		roots[j] = prf.FRIRoots[j-1]
	}

	var levelRootsExtra []hash.Digest
	if numExtraLevels > 0 {
		levelRootsExtra = levelRoots[1:]
	}

	if prf.FinalField == field.Ext {
		return verifyExt(p, levelRoots, levelRootsExtra, levelAtRound, roots, prf, ts)
	}
	return verifyBase(p, levelRoots, levelRootsExtra, levelAtRound, roots, prf, ts)
}

func verifyBase(p Params, levelRoots, levelRootsExtra []hash.Digest, levelAtRound map[int][]int, roots []hash.Digest, prf Proof, ts *fiatshamir.Transcript) error {
	numLevels := len(levelRoots)
	numExtraLevels := numLevels - 1

	// ── Replay commit phase (interleaved, same order as Prove) ───────────────
	gammas := make([]koalabear.Element, numLevels) // gammas[l] for levels[l], l = 1..numLevels-1
	alphas := make([]koalabear.Element, p.numRounds)

	for j := 0; j < p.numRounds; j++ {
		for i, l := range levelAtRound[j] {
			challenge, err := deriveLevelGamma(ts, l, levelRoots[l], j == 0 && i == 0, levelRoots[0])
			if err != nil {
				return fmt.Errorf("fri: Verify: %w", err)
			}
			gammas[l].Set(&challenge[0])
		}

		name := foldName(j)
		root := roots[j]
		if err := ts.Bind(name, root[:]); err != nil {
			return fmt.Errorf("fri: Verify: bind fold %d: %w", j, err)
		}
		challenge, err := computeVerifierFoldChallenge(ts, name, p.grinding, prf.PoW)
		if err != nil {
			return fmt.Errorf("fri: Verify: compute fold challenge %d: %w", j, err)
		}
		alphas[j].Set(&challenge[0])
	}

	if err := ts.Bind(queryName(0), transcriptBasePoly(prf.FinalPolyBase)); err != nil {
		return fmt.Errorf("fri: Verify: bind final poly: %w", err)
	}

	// ── Query phase ───────────────────────────────────────────────────────────
	for k := 0; k < p.NumQueries; k++ {
		challenge, err := ts.ComputeChallenge(queryName(k))
		if err != nil {
			return fmt.Errorf("fri: Verify: compute query challenge %d: %w", k, err)
		}
		s := queryIndex(challenge, p.N)

		if k < p.NumQueries-1 {
			if err := ts.Bind(queryName(k+1), challenge[:]); err != nil {
				return fmt.Errorf("fri: Verify: bind query chain %d: %w", k+1, err)
			}
		}

		var levelQueriesForQuery []QueryLayer
		if numExtraLevels > 0 {
			levelQueriesForQuery = make([]QueryLayer, numExtraLevels)
			for l := 0; l < numExtraLevels; l++ {
				levelQueriesForQuery[l] = prf.LevelQueries[l][k]
			}
		}

		if err := checkQuery(s, prf.FRIQueries[k], levelQueriesForQuery, levelRootsExtra,
			levelAtRound, gammas, roots, prf.FinalPolyBase, alphas, p); err != nil {
			return fmt.Errorf("fri: Verify: query %d failed: %w", k, err)
		}
	}

	return nil
}

func verifyExt(p Params, levelRoots, levelRootsExtra []hash.Digest, levelAtRound map[int][]int, roots []hash.Digest, prf Proof, ts *fiatshamir.Transcript) error {
	numLevels := len(levelRoots)
	numExtraLevels := numLevels - 1

	gammas := make([]ext.E6, numLevels)
	alphas := make([]ext.E6, p.numRounds)

	for j := 0; j < p.numRounds; j++ {
		for i, l := range levelAtRound[j] {
			challenge, err := deriveLevelGamma(ts, l, levelRoots[l], j == 0 && i == 0, levelRoots[0])
			if err != nil {
				return fmt.Errorf("fri: Verify: %w", err)
			}
			gammas[l] = hash.OutputToExt(challenge)
		}

		name := foldName(j)
		root := roots[j]
		if err := ts.Bind(name, root[:]); err != nil {
			return fmt.Errorf("fri: Verify: bind fold %d: %w", j, err)
		}
		challenge, err := computeVerifierFoldChallenge(ts, name, p.grinding, prf.PoW)
		if err != nil {
			return fmt.Errorf("fri: Verify: compute fold challenge %d: %w", j, err)
		}
		alphas[j] = hash.OutputToExt(challenge)
	}

	if err := ts.Bind(queryName(0), transcriptExtPoly(prf.FinalPolyExt)); err != nil {
		return fmt.Errorf("fri: Verify: bind final poly: %w", err)
	}

	for k := 0; k < p.NumQueries; k++ {
		challenge, err := ts.ComputeChallenge(queryName(k))
		if err != nil {
			return fmt.Errorf("fri: Verify: compute query challenge %d: %w", k, err)
		}
		s := queryIndex(challenge, p.N)

		if k < p.NumQueries-1 {
			if err := ts.Bind(queryName(k+1), challenge[:]); err != nil {
				return fmt.Errorf("fri: Verify: bind query chain %d: %w", k+1, err)
			}
		}

		var levelQueriesForQuery []QueryLayer
		if numExtraLevels > 0 {
			levelQueriesForQuery = make([]QueryLayer, numExtraLevels)
			for l := 0; l < numExtraLevels; l++ {
				levelQueriesForQuery[l] = prf.LevelQueries[l][k]
			}
		}

		if err := checkQueryExt(s, prf.FRIQueries[k], levelQueriesForQuery, levelRootsExtra,
			levelAtRound, gammas, roots, prf.FinalPolyExt, alphas, p); err != nil {
			return fmt.Errorf("fri: Verify: query %d failed: %w", k, err)
		}
	}

	return nil
}

// ── helpers ──────────────────────────────────────────────────────────────────

func levelGammaName(l int) string { return fmt.Sprintf("fri_level_%d_gamma", l) }
func foldName(j int) string       { return fmt.Sprintf("fri_fold_%d", j) }
func queryName(k int) string      { return fmt.Sprintf("fri_query_%d", k) }

func computeProverFoldChallenge(ts *fiatshamir.Transcript, name string, grinding int) ([8]koalabear.Element, error) {
	if grinding == 0 {
		return ts.ComputeChallenge(name)
	}
	return ts.ComputeChallenge(name, fiatshamir.WithGrinding(grinding))
}

func computeVerifierFoldChallenge(ts *fiatshamir.Transcript, name string, grinding int, proofsOfWork map[string]fiatshamir.ProofOfWork) ([8]koalabear.Element, error) {
	if grinding == 0 {
		return ts.ComputeChallenge(name)
	}

	pow, ok := proofsOfWork[name]
	if !ok {
		return [8]koalabear.Element{}, fmt.Errorf("missing proof of work for %s", name)
	}
	if err := ts.SetProofOfWork(name, pow); err != nil {
		return [8]koalabear.Element{}, err
	}
	return ts.ComputeChallenge(name, fiatshamir.WithGrinding(grinding))
}

func recordFoldProofsOfWork(p Params, prf *Proof, ts *fiatshamir.Transcript) error {
	if p.grinding == 0 || p.numRounds == 0 {
		return nil
	}
	prf.PoW = make(map[string]fiatshamir.ProofOfWork, p.numRounds)
	for j := 0; j < p.numRounds; j++ {
		name := foldName(j)
		pow, ok := ts.ProofOfWork(name)
		if !ok {
			return fmt.Errorf("missing proof of work for %s", name)
		}
		prf.PoW[name] = pow
	}
	return nil
}

func log2(n int) int {
	k := 0
	for n > 1 {
		n >>= 1
		k++
	}
	return k
}

func siblingRows(row int) (int, int) {
	lo := row &^ 1
	return lo, lo + 1
}

func bitReverseIndex(i, n int) int {
	if n <= 1 {
		return 0
	}
	width := bits.TrailingZeros(uint(n))
	return int(bits.Reverse(uint(i)) >> (bits.UintSize - width))
}

func bitReversedFoldXInv(generatorInv koalabear.Element, parentRow, half int) koalabear.Element {
	exponent := bitReverseIndex(parentRow, half)
	var xInv koalabear.Element
	xInv.ExpInt64(generatorInv, int64(exponent))
	return xInv
}

// buildTreeBase builds a Merkle tree of adjacent row-pair leaves where
// leaf k = LeafHasher(layer[2*k], layer[2*k+1]).
func buildTreeBase(layer []koalabear.Element, lh LeafHasher, nh NodeHasher) (*merkle.Tree, error) {
	pairLeaves, err := pairLeafCount(len(layer))
	if err != nil {
		return nil, err
	}
	tree, err := merkle.New(pairLeaves, nh)
	if err != nil {
		return nil, err
	}
	leaves := make([]hash.Digest, pairLeaves)
	HashLeafPairsParallel(lh, leaves, LeafSource{Base: []poly.Polynomial{layer}})
	return tree, tree.Build(leaves)
}

// buildTreeExt is the extension-field counterpart of buildTreeBase.
func buildTreeExt(layer []ext.E6, lh LeafHasher, nh NodeHasher) (*merkle.Tree, error) {
	pairLeaves, err := pairLeafCount(len(layer))
	if err != nil {
		return nil, err
	}
	tree, err := merkle.New(pairLeaves, nh)
	if err != nil {
		return nil, err
	}
	leaves := make([]hash.Digest, pairLeaves)
	HashLeafPairsParallel(lh, leaves, LeafSource{Ext: []poly.ExtPolynomial{layer}})
	return tree, tree.Build(leaves)
}

// foldLayerBase folds a base-field layer of size Nⱼ into a layer of size Nⱼ/2.
func foldLayerBase(layer []koalabear.Element, alpha koalabear.Element, domain *fft.Domain, invTwo koalabear.Element) []koalabear.Element {
	half := len(layer) / 2
	next := make([]koalabear.Element, half)
	parallel.ExecuteWithThreshold(half, foldParallelThreshold, func(start, end int) {
		var sum, diff koalabear.Element
		for i := start; i < end; i++ {
			p, q := layer[2*i], layer[2*i+1]
			xInv := bitReversedFoldXInv(domain.GeneratorInv, i, half)

			sum.Add(&p, &q)
			sum.Mul(&sum, &invTwo)

			diff.Sub(&p, &q)
			diff.Mul(&diff, &invTwo)
			diff.Mul(&diff, &xInv)
			diff.Mul(&diff, &alpha)

			next[i].Add(&sum, &diff)
		}
	})
	return next
}

// foldLayerExt is the extension-field counterpart of foldLayerBase; domain
// factors stay in the base field and are multiplied via MulByElement.
func foldLayerExt(layer []ext.E6, alpha ext.E6, domain *fft.Domain, invTwo koalabear.Element) []ext.E6 {
	half := len(layer) / 2
	next := make([]ext.E6, half)
	parallel.ExecuteWithThreshold(half, foldParallelThreshold, func(start, end int) {
		for i := start; i < end; i++ {
			p, q := layer[2*i], layer[2*i+1]
			xInv := bitReversedFoldXInv(domain.GeneratorInv, i, half)

			var sum, diff ext.E6
			sum.Add(&p, &q)
			sum.MulByElement(&sum, &invTwo)

			diff.Sub(&p, &q)
			diff.MulByElement(&diff, &invTwo)
			diff.MulByElement(&diff, &xInv)
			diff.Mul(&diff, &alpha)

			next[i].Add(&sum, &diff)
		}
	})
	return next
}

func transcriptBasePoly(poly []koalabear.Element) []koalabear.Element {
	res := make([]koalabear.Element, 0, 2+len(poly))
	res = append(res, hash.NewElement(0x42415345), hash.NewElement(uint64(len(poly)))) // "BASE"
	res = append(res, poly...)
	return res
}

func transcriptExtPoly(poly []ext.E6) []koalabear.Element {
	res := make([]koalabear.Element, 0, 2+hash.ExtDegree*len(poly))
	res = append(res, hash.NewElement(0x45585450), hash.NewElement(uint64(len(poly)))) // "EXTP"
	for _, v := range poly {
		res = hash.AppendExtElements(res, v)
	}
	return res
}

func queryIndex(challenge hash.Digest, modulus int) int {
	if modulus <= 0 {
		return 0
	}
	v := (challenge[0].Uint64() << 31) ^ challenge[1].Uint64()
	return int(v % uint64(modulus))
}

// openQueryBase builds the Merkle opening data for query index s across all r
// base folding levels.
func openQueryBase(s int, layers [][]koalabear.Element, trees []*merkle.Tree, numRounds int) (Query, error) {
	q := Query{Layers: make([]QueryLayer, numRounds)}
	for j := 0; j < numRounds; j++ {
		row := s >> j
		lo, hi := siblingRows(row)
		pairIdx := lo / 2

		path, err := trees[j].OpenProof(pairIdx)
		if err != nil {
			return Query{}, fmt.Errorf("layer %d OpenProof pair=%d: %w", j, pairIdx, err)
		}

		q.Layers[j] = QueryLayer{
			Field:     field.Base,
			Row:       row,
			LeafPBase: layers[j][lo],
			LeafQBase: layers[j][hi],
			Path:      path,
		}
	}
	return q, nil
}

// openQueryExt builds the Merkle opening data for query index s across all r
// extension folding levels.
func openQueryExt(s int, layers [][]ext.E6, trees []*merkle.Tree, numRounds int) (Query, error) {
	q := Query{Layers: make([]QueryLayer, numRounds)}
	for j := 0; j < numRounds; j++ {
		row := s >> j
		lo, hi := siblingRows(row)
		pairIdx := lo / 2

		path, err := trees[j].OpenProof(pairIdx)
		if err != nil {
			return Query{}, fmt.Errorf("layer %d OpenProof pair=%d: %w", j, pairIdx, err)
		}

		q.Layers[j] = QueryLayer{
			Field:    field.Ext,
			Row:      row,
			LeafPExt: layers[j][lo],
			LeafQExt: layers[j][hi],
			Path:     path,
		}
	}
	return q, nil
}

func verifyAdjacentBaseOpening(root hash.Digest, layer QueryLayer, context string, p Params) error {
	if layer.Field != field.Base {
		return fmt.Errorf("%s: expected base query layer, got %s", context, layer.Field)
	}
	lo, hi := siblingRows(layer.Row)
	pairIdx := lo / 2
	if layer.Path.LeafIdx != pairIdx {
		return fmt.Errorf("%s: proof pair = %d, want %d", context, layer.Path.LeafIdx, pairIdx)
	}

	pairLeaf := p.LeafHasher.HashLeafPair(
		RawRow{RawRowBase: []koalabear.Element{layer.LeafPBase}},
		RawRow{RawRowBase: []koalabear.Element{layer.LeafQBase}},
	)
	if !merkle.Verify(root, layer.Path, pairLeaf, p.NodeHasher) {
		return fmt.Errorf("%s: Merkle proof invalid for row pair (%d,%d)", context, lo, hi)
	}
	return nil
}

func verifyAdjacentExtOpening(root hash.Digest, layer QueryLayer, context string, p Params) error {
	if layer.Field != field.Ext {
		return fmt.Errorf("%s: expected ext query layer, got %s", context, layer.Field)
	}
	lo, hi := siblingRows(layer.Row)
	pairIdx := lo / 2
	if layer.Path.LeafIdx != pairIdx {
		return fmt.Errorf("%s: proof pair = %d, want %d", context, layer.Path.LeafIdx, pairIdx)
	}

	pairLeaf := p.LeafHasher.HashLeafPair(
		RawRow{RawRowExt: []ext.E6{layer.LeafPExt}},
		RawRow{RawRowExt: []ext.E6{layer.LeafQExt}},
	)
	if !merkle.Verify(root, layer.Path, pairLeaf, p.NodeHasher) {
		return fmt.Errorf("%s: Merkle proof invalid for row pair (%d,%d)", context, lo, hi)
	}
	return nil
}

// checkQuery verifies one base-field multi-degree FRI query:
//   - Merkle proofs for all level polynomial openings
//   - Merkle proofs and fold consistency for the running-polynomial path
//   - Batching consistency at each level introduction round
//
// levelQueriesForQuery[l-1] holds the opening for levels[l] (l 0-based index offset by 1).
// levelRoots[l-1] is the Merkle root of levels[l].Evals (l 0-based offset by 1).
// gammas[l] is the batching challenge for levels[l] (1-based; gammas[0] unused).
func checkQuery(s int, fq Query,
	levelQueriesForQuery []QueryLayer,
	levelRoots []hash.Digest,
	levelAtRound map[int][]int,
	gammas []koalabear.Element,
	roots []hash.Digest,
	finalPoly []koalabear.Element,
	alphas []koalabear.Element,
	p Params) error {

	// Verify Merkle proofs for all level polynomial openings.
	for lIdx, ld := range levelQueriesForQuery {
		if err := verifyAdjacentBaseOpening(levelRoots[lIdx], ld, fmt.Sprintf("level %d", lIdx+1), p); err != nil {
			return err
		}
	}

	// Verify running-polynomial fold path with batching consistency checks.
	for j := 0; j < p.numRounds; j++ {
		Nj := int(p.domainsLight[j].cardinality)
		row := s >> j
		lo, _ := siblingRows(row)
		layer := fq.Layers[j]
		if layer.Field != field.Base {
			return fmt.Errorf("round %d: expected base query layer, got %s", j, layer.Field)
		}
		if layer.Row != row {
			return fmt.Errorf("round %d: query row = %d, want %d", j, layer.Row, row)
		}
		if err := verifyAdjacentBaseOpening(roots[j], layer, fmt.Sprintf("round %d", j), p); err != nil {
			return err
		}

		// The folded pair: the layer's opening, plus at round 0 γ_l times
		// the opening of every other level entering at round 0.
		leafP, leafQ := layer.LeafPBase, layer.LeafQBase
		if j == 0 {
			for _, li := range levelAtRound[0] {
				ld := levelQueriesForQuery[li-1]
				if ld.Row != row {
					return fmt.Errorf("round 0: level %d query row = %d, want %d", li, ld.Row, row)
				}
				var term koalabear.Element
				term.Mul(&ld.LeafPBase, &gammas[li])
				leafP.Add(&leafP, &term)
				term.Mul(&ld.LeafQBase, &gammas[li])
				leafQ.Add(&leafQ, &term)
			}
		}

		// Fold: expected = (LeafP+LeafQ)/2 + α*(LeafP-LeafQ)/(2·X),
		// with X = ωⱼ^bitrev(row/2) for adjacent bit-reversed rows.
		var xInv, sum, diff, expected koalabear.Element
		generatorInv := p.domainsLight[j].generator
		generatorInv.Inverse(&generatorInv)
		xInv = bitReversedFoldXInv(generatorInv, lo>>1, Nj>>1)
		sum.Add(&leafP, &leafQ)
		sum.Mul(&sum, &p.invTwo)
		diff.Sub(&leafP, &leafQ)
		diff.Mul(&diff, &p.invTwo)
		diff.Mul(&diff, &xInv)
		diff.Mul(&diff, &alphas[j])
		expected.Add(&sum, &diff)

		if j < p.numRounds-1 {
			nextRow := row >> 1
			nextLayer := fq.Layers[j+1]
			isLeafP := nextRow&1 == 0

			// expectedNext = fold output + level contributions at round j+1 (if any).
			var expectedNext koalabear.Element
			expectedNext.Set(&expected)

			for _, li := range levelAtRound[j+1] {
				gamma := gammas[li]
				ld := levelQueriesForQuery[li-1]
				if ld.Row != nextRow {
					return fmt.Errorf("round %d: level %d query row = %d, want %d", j, li, ld.Row, nextRow)
				}
				var leafVal koalabear.Element
				if isLeafP {
					leafVal.Set(&ld.LeafPBase)
				} else {
					leafVal.Set(&ld.LeafQBase)
				}
				var term koalabear.Element
				term.Mul(&leafVal, &gamma)
				expectedNext.Add(&expectedNext, &term)
			}

			if isLeafP {
				if !expectedNext.Equal(&nextLayer.LeafPBase) {
					return fmt.Errorf("round %d: folded value mismatch at round %d LeafP", j, j+1)
				}
			} else {
				if !expectedNext.Equal(&nextLayer.LeafQBase) {
					return fmt.Errorf("round %d: folded value mismatch at round %d LeafQ", j, j+1)
				}
			}
		} else {
			finalVal := finalPoly[s>>p.numRounds]
			if !expected.Equal(&finalVal) {
				return fmt.Errorf("round %d (final): folded value does not match FinalPoly", j)
			}
		}
	}

	return nil
}

func checkQueryExt(s int, fq Query,
	levelQueriesForQuery []QueryLayer,
	levelRoots []hash.Digest,
	levelAtRound map[int][]int,
	gammas []ext.E6,
	roots []hash.Digest,
	finalPoly []ext.E6,
	alphas []ext.E6,
	p Params) error {

	for lIdx, ld := range levelQueriesForQuery {
		if err := verifyAdjacentExtOpening(levelRoots[lIdx], ld, fmt.Sprintf("level %d", lIdx+1), p); err != nil {
			return err
		}
	}

	for j := 0; j < p.numRounds; j++ {
		Nj := int(p.domainsLight[j].cardinality)
		row := s >> j
		lo, _ := siblingRows(row)
		layer := fq.Layers[j]
		if layer.Field != field.Ext {
			return fmt.Errorf("round %d: expected ext query layer, got %s", j, layer.Field)
		}
		if layer.Row != row {
			return fmt.Errorf("round %d: query row = %d, want %d", j, layer.Row, row)
		}
		if err := verifyAdjacentExtOpening(roots[j], layer, fmt.Sprintf("round %d", j), p); err != nil {
			return err
		}

		// The folded pair: the layer's opening, plus at round 0 γ_l times
		// the opening of every other level entering at round 0.
		leafP, leafQ := layer.LeafPExt, layer.LeafQExt
		if j == 0 {
			for _, li := range levelAtRound[0] {
				ld := levelQueriesForQuery[li-1]
				if ld.Row != row {
					return fmt.Errorf("round 0: level %d query row = %d, want %d", li, ld.Row, row)
				}
				var term ext.E6
				term.Mul(&ld.LeafPExt, &gammas[li])
				leafP.Add(&leafP, &term)
				term.Mul(&ld.LeafQExt, &gammas[li])
				leafQ.Add(&leafQ, &term)
			}
		}

		generatorInv := p.domainsLight[j].generator
		generatorInv.Inverse(&generatorInv)
		xInv := bitReversedFoldXInv(generatorInv, lo>>1, Nj>>1)

		var sum, diff, expected ext.E6
		sum.Add(&leafP, &leafQ)
		sum.MulByElement(&sum, &p.invTwo)
		diff.Sub(&leafP, &leafQ)
		diff.MulByElement(&diff, &p.invTwo)
		diff.MulByElement(&diff, &xInv)
		diff.Mul(&diff, &alphas[j])
		expected.Add(&sum, &diff)

		if j < p.numRounds-1 {
			nextRow := row >> 1
			nextLayer := fq.Layers[j+1]
			isLeafP := nextRow&1 == 0

			var expectedNext ext.E6
			expectedNext.Set(&expected)

			for _, li := range levelAtRound[j+1] {
				gamma := gammas[li]
				ld := levelQueriesForQuery[li-1]
				if ld.Row != nextRow {
					return fmt.Errorf("round %d: level %d query row = %d, want %d", j, li, ld.Row, nextRow)
				}
				var leafVal ext.E6
				if isLeafP {
					leafVal.Set(&ld.LeafPExt)
				} else {
					leafVal.Set(&ld.LeafQExt)
				}
				var term ext.E6
				term.Mul(&leafVal, &gamma)
				expectedNext.Add(&expectedNext, &term)
			}

			if isLeafP {
				if !expectedNext.Equal(&nextLayer.LeafPExt) {
					return fmt.Errorf("round %d: folded value mismatch at round %d LeafP", j, j+1)
				}
			} else {
				if !expectedNext.Equal(&nextLayer.LeafQExt) {
					return fmt.Errorf("round %d: folded value mismatch at round %d LeafQ", j, j+1)
				}
			}
		} else {
			finalVal := finalPoly[s>>p.numRounds]
			if !expected.Equal(&finalVal) {
				return fmt.Errorf("round %d (final): folded value does not match FinalPoly", j)
			}
		}
	}

	return nil
}
