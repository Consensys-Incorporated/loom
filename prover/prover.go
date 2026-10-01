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

package prover

import (
	"fmt"
	"sort"
	"sync"
	"time"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/gnark-crypto/utils"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/dag"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/parallel"
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/internal/protocol"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/trace"
)

type Config struct {
	SkipFRI             bool
	HashBackend         fri.HashBackend
	NewTranscriptHasher fiatshamir.NewTranscriptHasher
	PhaseCallback       func(name string, d time.Duration)
	NumFriQueries       int
	FriOptions          []fri.Option
	Fs                  *fiatshamir.Transcript
}

type Option func(c *Config) error

// WithTranscript provides a running transcript to the prover
func WithTranscript(fs *fiatshamir.Transcript) Option {
	return func(c *Config) error {
		c.Fs = fs
		return nil
	}
}

// WithFriOption adds options for FRI
func WithFriOption(opt fri.Option) Option {
	return func(c *Config) error {
		c.FriOptions = append(c.FriOptions, opt)
		return nil
	}
}

// WithNumFriQueries sets FRI NumQueries to numQueries
func WithNumFriQueries(numQueries int) Option {
	return func(c *Config) error {
		c.NumFriQueries = numQueries
		return nil
	}
}

func SkipFRI() Option {
	return func(c *Config) error {
		c.SkipFRI = true
		return nil
	}
}

func WithHashBackend(backend fri.HashBackend) Option {
	return func(c *Config) error {
		c.HashBackend = backend
		return nil
	}
}

func WithNewTranscriptHasher(h fiatshamir.NewTranscriptHasher) Option {
	return func(c *Config) error {
		c.NewTranscriptHasher = h
		return nil
	}
}

// WithPhaseCallback installs a callback that fires after each major prover
// phase with the phase name and wall-clock duration. Phases reported (in
// order): "execute-steps", "compute-air-quotients", "evaluations-at-zeta",
// "deep-quotient+fri-commit", "fri-query-open".
func WithPhaseCallback(cb func(name string, d time.Duration)) Option {
	return func(c *Config) error {
		c.PhaseCallback = cb
		return nil
	}
}

type proverRuntime struct {
	friParams fri.Params
	Proof     proof.Proof
	config    Config

	// layout is the canonical commitment layout (built from program + setup
	// at the start of every Prove call so program.SetSize changes are
	// reflected). It defines the order of trees in `committed` and the
	// column-name → Slot mapping used to assemble pcs.Open's inputs.
	layout protocol.Layout
	// schedule is the per-tree (shifts, names, canonical-keys) bundle the
	// prover hands to pcs.Open. Built deterministically from program/layout
	// so prover and verifier produce identical schedules.
	schedule protocol.CanonicalSchedule
	// committed[i] is the per-batch fri.Committed for tree i in canonical
	// order (setup → trace rounds → AIR). Setup committeds are copied from
	// provingKey.Setup at construction; trace and AIR slots get populated by
	// commitTraceRound and ComputeAIRQuotients.
	committed []fri.Committed

	t            trace.Trace
	airTrace     trace.Trace
	publicInputs public.Inputs
	program      board.Program
	zeta         ext.E6 // point of evaluation to check the AIR relation with SZ
	mu           *sync.Mutex
	setup        setup.ProvingKey
	fs           *fiatshamir.Transcript
	domainCache  poly.DomainCache
	hashBackend  fri.HashBackend
}

func newProverRuntime(t trace.Trace, provingKey setup.ProvingKey, publicInputs public.Inputs, program board.Program, config Config) (proverRuntime, error) {
	var err error
	hashBackend, err := fri.ResolveHashBackend(config.HashBackend, provingKey.HashBackendID)
	if err != nil {
		return proverRuntime{}, err
	}
	config.HashBackend = hashBackend

	if len(provingKey.Trace.Base) > 0 || len(provingKey.Trace.Ext) > 0 {
		t, err = trace.MergeMatching(t, provingKey.Trace)
		if err != nil {
			return proverRuntime{}, fmt.Errorf("newProverRuntime: merge setup trace: %w", err)
		}
	}

	res := proverRuntime{
		Proof:        proof.NewProof(),
		config:       config,
		t:            t,
		publicInputs: publicInputs,
		program:      program,
		setup:        provingKey,
		airTrace:     trace.New(),
		mu:           new(sync.Mutex), // mutex to protect the trace when reading/writing (in case of parallelisation)
		hashBackend:  hashBackend,
	}
	res.Proof.HashBackendID = hashBackend.ID

	// Build the canonical commitment layout + parallel shift schedule.
	// Both prover and verifier construct identical schedules from the same
	// program; the alpha_DEEP transcript binding depends on it.
	res.layout = protocol.BuildLayout(program, len(provingKey.Setup))
	res.schedule = protocol.BuildCanonicalSchedule(program, res.layout)

	// committed[i] is the i-th batch's full Committed in canonical order
	// (setup → trace rounds → AIR). Setup slots are filled now; the
	// trace and AIR slots are populated by commitTraceRound and
	// ComputeAIRQuotients. proof.Commitments stores ONLY the trace+AIR
	// roots; setup roots come from the verifier's VerificationKey.
	res.committed = make([]fri.Committed, res.layout.NumTrees)
	for i, c := range provingKey.Setup {
		res.committed[res.layout.SetupBegin+i] = c
	}
	res.Proof.Commitments = make([]hash.Digest, res.layout.NumTrees-res.layout.SetupEnd)

	// find the largest module size N in program (used to size FRI's outer domain)
	maxN := 0
	for _, m := range program.Modules {
		if m.N > maxN {
			maxN = m.N
		}
	}

	res.friParams, err = fri.NewParams(int(constants.RATE)*maxN, maxN, config.NumFriQueries, hashBackend.LeafHasher, hashBackend.NodeHasher, config.FriOptions...)
	if err != nil {
		return res, err
	}

	// Initialize the FS transcript and pre-register the caller-side
	// challenge names: per-round trace challenges and zeta. alpha_DEEP and
	// the FRI-internal challenge names are registered by fri.PCS.Open at
	// invocation time.
	if config.Fs != nil {
		res.fs = config.Fs
	} else {
		// default is poseidon2
		newTranscriptHasher, err := fiatshamir.ResolveNewTranscriptHasher(config.NewTranscriptHasher)
		if err != nil {
			return res, err
		}
		res.fs = fiatshamir.NewTranscript(newTranscriptHasher())
	}
	numRounds := len(program.Rounds)
	for i := 0; i < numRounds; i++ {
		res.fs.NewChallenge(constants.CanonicalChallengeName(i))
	}
	res.fs.NewChallenge(constants.FINAL_EVALUATION_POINT)

	initialChallenge := constants.InitialChallengeName(numRounds)
	if err := res.fs.Bind(initialChallenge, hash.StringToElements(constants.HASH_BACKEND_DOMAIN_TAG, hashBackend.ID)); err != nil {
		return res, err
	}
	if err := res.fs.Bind(initialChallenge, protocol.ModuleSizesTranscript(program)); err != nil {
		return res, err
	}

	// Bind every setup tree's root to the first challenge (decreasing-N order,
	// set by Setup) + public inputs.
	for _, c := range provingKey.Setup {
		root := c.Tree.Root()
		if err := res.fs.Bind(initialChallenge, root[:]); err != nil {
			return res, err
		}
	}
	if len(publicInputs) > 0 {
		if err := res.fs.Bind(initialChallenge, publicInputs.TranscriptElements()); err != nil {
			return res, err
		}
	}

	// materialise the public columns to the trace from the public inputs
	for colName, pi := range publicInputs {
		m, ok := program.Modules[pi.Module]
		if !ok {
			return res, fmt.Errorf("public input %q references unknown module %q", colName, pi.Module)
		}
		kind := field.Base
		for _, e := range pi.Entries {
			if e.Idx < 0 || e.Idx >= m.N {
				return res, fmt.Errorf("public input %q entry index %d out of bounds for module %q of size %d", colName, e.Idx, pi.Module, m.N)
			}
			kind = field.Join(e.Field, kind)
		}
		if kind == field.Base {
			col := make([]koalabear.Element, m.N)
			for _, e := range pi.Entries {
				col[e.Idx].Set(&e.Value)
			}
			err := t.PutBase(colName, col)
			if err != nil {
				return res, err
			}
		} else {
			col := make([]ext.E6, m.N)
			for _, e := range pi.Entries {
				if e.Field == field.Base {
					col[e.Idx] = hash.LiftBaseToExt(e.Value)
				} else {
					col[e.Idx].Set(&e.ValueExt)
				}
			}
			err := t.PutExt(colName, col)
			if err != nil {
				return res, err
			}
		}
	}

	return res, nil
}

// commitIdxOf converts a canonical tree index into the offset in
// pr.Proof.Commitments (which excludes the setup section).
func (pr *proverRuntime) commitIdxOf(treeIdx int) int {
	return treeIdx - pr.layout.SetupEnd
}

func liftPolynomialToExt(p poly.Polynomial) poly.ExtPolynomial {
	res := make(poly.ExtPolynomial, len(p))
	for i := range p {
		res[i] = hash.LiftBaseToExt(p[i])
	}
	return res
}

func buildBatchFromNames(batchNames protocol.BatchNames, base map[string]poly.Polynomial, ext map[string]poly.ExtPolynomial, errPrefix string, liftExtFromBase bool) (fri.Batch, error) {
	batch := make(fri.Batch, len(batchNames))
	for groupIdx, names := range batchNames {
		basePolys := make([]poly.Polynomial, len(names.Base))
		for i, name := range names.Base {
			p, ok := base[name]
			if !ok {
				return nil, fmt.Errorf("%s: group %d base poly %q not found", errPrefix, groupIdx, name)
			}
			basePolys[i] = p
		}
		extPolys := make([]poly.ExtPolynomial, len(names.Ext))
		for i, name := range names.Ext {
			p, ok := ext[name]
			if !ok && liftExtFromBase {
				if basePoly, ok := base[name]; ok {
					p = liftPolynomialToExt(basePoly)
					ok = true
				}
			}
			if !ok {
				return nil, fmt.Errorf("%s: group %d ext poly %q not found", errPrefix, groupIdx, name)
			}
			extPolys[i] = p
		}
		batch[groupIdx] = fri.Group{Base: basePolys, Ext: extPolys}
	}
	return batch, nil
}

func (pr *proverRuntime) commitTraceRound(roundIdx int, challengeName string) error {
	begin := pr.layout.TraceBegin[roundIdx]
	end := pr.layout.TraceEnd[roundIdx]
	if begin == end {
		return nil
	}
	if end != begin+1 {
		return fmt.Errorf("commitTraceRound: round %d: expected one trace tree, got %d", roundIdx, end-begin)
	}

	treeIdx := begin
	pr.mu.Lock()
	batch, err := buildBatchFromNames(
		pr.schedule.ColNamesByTree[treeIdx],
		pr.t.Base,
		pr.t.Ext,
		fmt.Sprintf("commitTraceRound: round %d tree %d", roundIdx, treeIdx),
		true,
	)
	pr.mu.Unlock()
	if err != nil {
		return err
	}

	pcs := fri.NewPCS(uint64(constants.RATE), pr.hashBackend.LeafHasher, pr.hashBackend.NodeHasher)
	committed, err := pcs.Commit(batch, fri.WithDomainCache(&pr.domainCache))
	if err != nil {
		return err
	}
	pr.committed[treeIdx] = committed
	root := committed.Tree.Root()
	pr.Proof.Commitments[pr.commitIdxOf(treeIdx)] = root
	if err := pr.fs.Bind(challengeName, root[:]); err != nil {
		return err
	}

	return nil
}

func (pr *proverRuntime) ExecuteSteps() error {

	// 1 - for each module in program, execute the list of Gen() functions in GenCol
	for _, m := range pr.program.Modules {
		mCopy := m
		for _, gen := range mCopy.GenCol {
			gen.Gen(pr.t, &mCopy)
		}
	}

	// 2 - execute the program round by round: run the round's steps, commit its
	// staged columns, then derive its challenge.
	for roundIdx, round := range pr.program.Rounds {
		for _, s := range round.Steps {
			if err := s.Execute(pr.t, &pr.program, &pr.Proof, pr.mu); err != nil {
				return err
			}
		}

		challengeName := constants.CanonicalChallengeName(roundIdx)
		if err := pr.commitTraceRound(roundIdx, challengeName); err != nil {
			return err
		}
		switch round.FSHook {
		case board.NoFSHook:
		case board.BindExposedValues:
			for _, name := range round.ExposedValueNames() {
				v, ok := pr.Proof.ExposedValues[name]
				if !ok {
					return fmt.Errorf("ExecuteSteps: round %d: exposed value %s missing", roundIdx, name)
				}
				if err := pr.fs.Bind(challengeName, board.ExposedValueElements(v)); err != nil {
					return err
				}
			}
		default:
			return fmt.Errorf("ExecuteSteps: round %d: FS hook %d is not supported", roundIdx, round.FSHook)
		}

		challenge, err := pr.fs.ComputeChallenge(challengeName)
		if err != nil {
			return err
		}
		challengeVal := hash.OutputToExt(challenge)

		pr.mu.Lock()
		pr.t.SetExt(challengeName, []ext.E6{challengeVal})
		pr.mu.Unlock()
	}

	return nil
}

// computeExtAIRQuotientChunks computes the AIR quotient for a single ext-rooted module
// and returns its N-sized chunks in Lagrange form, ready to commit. Chunks
// alias non-overlapping windows of the quotient backing array (no per-chunk
// copy); after this returns the caller owns the chunks and the original
// quotient is unreachable.
// fftNbTasks caps the inner parallelism of the per-chunk FFTs so that, when
// this function is itself invoked inside a parallel.Execute over modules,
// outer × inner goroutines stays bounded.
func computeExtAIRQuotientChunks(piBase map[string]poly.Polynomial, piExt map[string]poly.ExtPolynomial, vrel *dag.DAG, N int, D *fft.Domain, cache *poly.DomainCache, fftNbTasks int) ([]poly.ExtPolynomial, error) {
	quotient, err := poly.ComputeQuotientMixed(piBase, piExt, *vrel, N, poly.WithDomainCache(cache))
	if err != nil {
		return nil, err
	}
	// quotient is in coset-Lagrange Normal; convert directly to canonical
	// Normal so chunking can sub-slice the backing array.
	poly.CosetExtLagrangeNormalToCanonicalWithCache(quotient, cache)

	fftOpt := fft.WithNbTasks(fftNbTasks)
	chunks := make([]poly.ExtPolynomial, len(quotient)/N)
	for i := range chunks {
		chunk := quotient[i*N : (i+1)*N : (i+1)*N]
		D.FFTExt6(chunk, fft.DIF, fftOpt)
		utils.BitReverse(chunk)
		chunks[i] = chunk
	}
	return chunks, nil
}

// computeBaseAIRQuotientChunks is the base-field counterpart of computeExtAIRQuotientChunks.
func computeBaseAIRQuotientChunks(piBase map[string]poly.Polynomial, vrel *dag.DAG, N int, D *fft.Domain, cache *poly.DomainCache, fftNbTasks int) ([]poly.Polynomial, error) {
	quotient, err := poly.ComputeQuotient(piBase, *vrel, N, poly.WithDomainCache(cache))
	if err != nil {
		return nil, err
	}
	poly.CosetLagrangeNormalToCanonicalWithCache(quotient, cache)

	fftOpt := fft.WithNbTasks(fftNbTasks)
	chunks := make([]poly.Polynomial, len(quotient)/N)
	for i := range chunks {
		chunk := quotient[i*N : (i+1)*N : (i+1)*N]
		D.FFT(chunk, fft.DIF, fftOpt)
		utils.BitReverse(chunk)
		chunks[i] = chunk
	}
	return chunks, nil
}

func (pr *proverRuntime) ComputeAIRQuotients() error {

	moduleNames := make([]string, 0, len(pr.program.Modules))
	for name := range pr.program.Modules {
		moduleNames = append(moduleNames, name)
	}
	sort.Strings(moduleNames)

	// Per-module quotient computation is independent: each writes disjoint chunk
	// names into airTrace, reads only from the shared pr.t. pr.domainCache is
	// internally locked; trace map writes need an explicit lock. The DAG is
	// cloned per goroutine because ComputeQuotient* mutates Leaf.Idx and modules
	// can share *expr.Leaf pointers via cross-module arguments (Lookup, etc.).
	var (
		writeMu  sync.Mutex
		errMu    sync.Mutex
		firstErr error
	)
	// Per-chunk FFTs inside each module run with their internal parallelism
	// capped so the outer module fan-out doesn't multiply with the FFT's own.
	fftNbTasks := parallel.NbTasksPerJob(len(moduleNames))
	parallel.Execute(len(moduleNames), func(start, end int) {
		for idx := start; idx < end; idx++ {
			moduleName := moduleNames[idx]
			module := pr.program.Modules[moduleName]
			if module.VanishingRelation.Degree() <= 0 {
				continue
			}

			N := module.N
			vrel := module.VanishingRelation.Clone()

			var (
				baseChunks []poly.Polynomial
				extChunks  []poly.ExtPolynomial
				err        error
			)
			if module.VanishingRelation.Root.Field == field.Ext {
				extChunks, err = computeExtAIRQuotientChunks(pr.t.Base, pr.t.Ext, vrel, N, module.D, &pr.domainCache, fftNbTasks)
			} else {
				baseChunks, err = computeBaseAIRQuotientChunks(pr.t.Base, vrel, N, module.D, &pr.domainCache, fftNbTasks)
			}
			if err != nil {
				errMu.Lock()
				if firstErr == nil {
					firstErr = err
				}
				errMu.Unlock()
				return
			}

			writeMu.Lock()
			for i, c := range baseChunks {
				name := constants.QuotientChunkName(moduleName, i)
				pr.airTrace.SetBase(name, c)
			}
			for i, c := range extChunks {
				name := constants.QuotientChunkName(moduleName, i)
				pr.airTrace.SetExt(name, c)
			}
			writeMu.Unlock()
		}
	})
	if firstErr != nil {
		return firstErr
	}

	// Commit the AIR section: one tree (one group per module), as laid out
	// by protocol.BuildLayout.
	for treeIdx := pr.layout.AIRBegin; treeIdx < pr.layout.AIREnd; treeIdx++ {
		batch, err := buildBatchFromNames(
			pr.schedule.ColNamesByTree[treeIdx],
			pr.airTrace.Base,
			pr.airTrace.Ext,
			fmt.Sprintf("ComputeAIRQuotients: tree %d", treeIdx),
			false,
		)
		if err != nil {
			return err
		}
		pcs := fri.NewPCS(uint64(constants.RATE), pr.hashBackend.LeafHasher, pr.hashBackend.NodeHasher)
		committed, err := pcs.Commit(batch, fri.WithDomainCache(&pr.domainCache))
		if err != nil {
			return err
		}
		pr.committed[treeIdx] = committed
		root := committed.Tree.Root()
		pr.Proof.Commitments[pr.commitIdxOf(treeIdx)] = root
		if err := pr.fs.Bind(constants.FINAL_EVALUATION_POINT, root[:]); err != nil {
			return err
		}
	}

	zeta, err := pr.fs.ComputeChallenge(constants.FINAL_EVALUATION_POINT)
	if err != nil {
		return err
	}
	pr.zeta = hash.OutputToExt(zeta)

	return nil
}

// buildBatches assembles the per-tree fri.Batch slices in canonical
// order, looking up Lagrange-form polynomials by canonical column name
// (trace/setup polys live in pr.t, AIR chunks in pr.airTrace). Setup
// batches come first, then trace-round batches, then AIR batches. The
// canonical layout's tree index is the batch index; each batch may carry
// one or more declaration-order groups.
func (pr *proverRuntime) buildBatches() ([]fri.Batch, error) {
	n := pr.layout.NumTrees
	batches := make([]fri.Batch, n)
	for treeIdx := 0; treeIdx < n; treeIdx++ {
		isAIR := treeIdx >= pr.layout.AIRBegin && treeIdx < pr.layout.AIREnd

		traceBase := pr.t.Base
		traceExt := pr.t.Ext
		if isAIR {
			traceBase = pr.airTrace.Base
			traceExt = pr.airTrace.Ext
		}

		batch, err := buildBatchFromNames(
			pr.schedule.ColNamesByTree[treeIdx],
			traceBase,
			traceExt,
			fmt.Sprintf("buildBatches: tree %d", treeIdx),
			!isAIR,
		)
		if err != nil {
			return nil, err
		}
		batches[treeIdx] = batch
	}
	return batches, nil
}

// runPCSOpen invokes fri.PCS.Open with the canonical-order
// (batches, committed, shifts), storing the OpeningProof on the
// in-progress proof.
func (pr *proverRuntime) runPCSOpen() error {
	if pr.layout.NumTrees == 0 {
		return nil
	}
	batches, err := pr.buildBatches()
	if err != nil {
		return err
	}

	pcs := fri.NewPCSWithParams(pr.friParams)
	openProof, err := pcs.Open(
		batches,
		pr.committed,
		pr.schedule.Shifts,
		pr.zeta,
		pr.fs,
		fri.WithOpenDomainCache(&pr.domainCache),
		fri.WithDeepClasses(pr.layout.DeepClasses()),
	)
	if err != nil {
		return fmt.Errorf("runPCSOpen: %w", err)
	}
	pr.Proof.Opening = openProof
	return nil
}

// runPCSClaimedValuesOnly is the SkipFRI counterpart of runPCSOpen: it
// evaluates every committed polynomial at zeta * omega^shift and stores
// the result in Proof.Opening.ClaimedValues, skipping the DEEP-quotient
// construction, FRI prover, and PointSamplings. The verifier still
// needs ClaimedValues to populate ValuesAtZeta for the AIR check, so
// SkipFRI on the prover MUST still emit them.
func (pr *proverRuntime) runPCSClaimedValuesOnly() error {
	if pr.layout.NumTrees == 0 {
		return nil
	}
	batches, err := pr.buildBatches()
	if err != nil {
		return err
	}

	pcs := fri.NewPCSWithParams(pr.friParams)
	values, err := pcs.ClaimedValuesOnly(
		batches,
		pr.schedule.Shifts,
		pr.zeta,
		fri.WithOpenDomainCache(&pr.domainCache),
	)
	if err != nil {
		return fmt.Errorf("runPCSClaimedValuesOnly: %w", err)
	}
	pr.Proof.Opening.ClaimedValues = values
	return nil
}

func Prove(t trace.Trace, provingKey setup.ProvingKey, publicInputs public.Inputs, program board.Program, opts ...Option) (proof.Proof, error) {

	var config Config
	config.NumFriQueries = constants.NUM_QUERIES
	for _, opt := range opts {
		err := opt(&config)
		if err != nil {
			return proof.Proof{}, err
		}
	}

	pr, err := newProverRuntime(t, provingKey, publicInputs, program, config)
	if err != nil {
		return proof.Proof{}, err
	}

	report := func(name string, d time.Duration) {
		if config.PhaseCallback != nil {
			config.PhaseCallback(name, d)
		}
	}

	// run ExecuteSteps: commits trace per FS round, samples round challenges.
	t0 := time.Now()
	if err := pr.ExecuteSteps(); err != nil {
		return proof.Proof{}, err
	}
	report("execute-steps", time.Since(t0))

	// run ComputeAIRQuotients: commits AIR chunks, samples zeta.
	t0 = time.Now()
	if err := pr.ComputeAIRQuotients(); err != nil {
		return proof.Proof{}, err
	}
	report("compute-air-quotients", time.Since(t0))

	if config.SkipFRI {
		// SkipFRI still needs claimed values so the (SkipFRI-side)
		// verifier can populate its ValuesAtZeta map and run the AIR
		// check; the rest of the OpeningProof stays zero.
		t0 = time.Now()
		if err := pr.runPCSClaimedValuesOnly(); err != nil {
			return proof.Proof{}, err
		}
		report("pcs-claimed-values-only", time.Since(t0))
		return pr.Proof, nil
	}

	// One PCS.Open call replaces the legacy ComputeEvaluationsAtZeta +
	// ComputeDeepQuotient + SampleEvaluations triple. fri.PCS.Open
	// internally:
	//   - evaluates every committed polynomial at zeta * omega^shift,
	//   - registers alpha_DEEP on pr.fs, binds the claimed values in
	//     canonical-layout order, samples alpha_DEEP,
	//   - builds one DEEP-quotient codeword per distinct native size,
	//     commits each as a fri.Level, runs fri.Prove on the levels,
	//   - opens every committed batch at every FRI query position.
	t0 = time.Now()
	if err := pr.runPCSOpen(); err != nil {
		return proof.Proof{}, err
	}
	report("pcs-open", time.Since(t0))

	return pr.Proof, nil
}
