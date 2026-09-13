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

package verifier

import (
	"fmt"
	"math/big"

	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/protocol"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
)

type Config struct {
	SkipFRI             bool
	HashBackend         fri.HashBackend
	NewTranscriptHasher fiatshamir.NewTranscriptHasher
	NumFriQueries       int
	FriOptions          []fri.Option
	Fs                  *fiatshamir.Transcript
}

type Option func(c *Config) error

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

// WithTranscript provides a running transcript to the verifier.
func WithTranscript(fs *fiatshamir.Transcript) Option {
	return func(c *Config) error {
		c.Fs = fs
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

// WithFriOption adds options for FRI
func WithFriOption(opt fri.Option) Option {
	return func(c *Config) error {
		c.FriOptions = append(c.FriOptions, opt)
		return nil
	}
}

type verifierRunTime struct {
	config       Config
	proof        proof.Proof
	friParams    fri.Params
	publicInputs public.Inputs
	program      board.Program
	zeta         ext.E6
	setup        setup.VerificationKey
	fs           *fiatshamir.Transcript

	// layout is the canonical commitment layout, shared with the prover side
	// (built from program + len(setup) at the start of every Verify call).
	layout protocol.Layout
	// schedule is the per-batch shift schedule and reverse name table used
	// to translate Opening.ClaimedValues back into a canonical-key
	// ValuesAtZeta map for AIR-equation evaluation.
	schedule protocol.CanonicalSchedule
	// roots is the flat sequence of Merkle roots in canonical order:
	//   setup roots (from VerificationKey) ++ proof.Commitments
	// roots[i] aligns with proof.Opening.PointSamplings[q][i] for any q.
	roots []hash.Digest
	// valuesAtZeta is the local name-keyed map of every committed
	// polynomial's claimed value plus the verifier-reconstructed entries
	// (Lagrange, public inputs, exposed values, round challenges).
	// Replaces the old proof.ValuesAtZeta field, which is now transient.
	valuesAtZeta map[string]ext.E6

	hashBackend fri.HashBackend
}

func newVerifierRuntime(program board.Program, verificationKey setup.VerificationKey, publicInputs public.Inputs, prf proof.Proof, config Config) (verifierRunTime, error) {
	hashBackend, err := fri.ResolveHashBackend(config.HashBackend, verificationKey.HashBackendID)
	if err != nil {
		return verifierRunTime{}, err
	}
	if prf.HashBackendID != "" && prf.HashBackendID != hashBackend.ID {
		return verifierRunTime{}, fmt.Errorf("verifier: proof hash backend %q does not match verifier backend %q", prf.HashBackendID, hashBackend.ID)
	}
	config.HashBackend = hashBackend

	res := verifierRunTime{
		config:       config,
		proof:        prf,
		publicInputs: publicInputs,
		program:      program,
		setup:        verificationKey,
		hashBackend:  hashBackend,
		valuesAtZeta: make(map[string]ext.E6),
	}

	// Build the canonical layout + per-batch shift schedule. Both sides
	// must agree on these to share the alpha_DEEP transcript binding
	// order; they're deterministic in program + |verificationKey|.
	res.layout = protocol.BuildLayout(program, len(verificationKey.Roots))
	res.schedule = protocol.BuildCanonicalSchedule(program, res.layout)

	// Validate proof.Commitments matches layout (trace + AIR section).
	wantCommitments := res.layout.NumTrees - res.layout.SetupEnd
	if len(prf.Commitments) != wantCommitments {
		return res, fmt.Errorf("verifier: proof has %d commitments, layout expects %d", len(prf.Commitments), wantCommitments)
	}

	// Flatten setup roots ++ proof.Commitments into res.roots, the per-
	// batch root sequence pcs.Verify consumes.
	res.roots = make([]hash.Digest, res.layout.NumTrees)
	if len(verificationKey.Roots) != res.layout.SetupEnd-res.layout.SetupBegin {
		return res, fmt.Errorf("verifier: setup has %d trees, layout expects %d", len(verificationKey.Roots), res.layout.SetupEnd-res.layout.SetupBegin)
	}
	for i, pkr := range verificationKey.Roots {
		res.roots[res.layout.SetupBegin+i] = pkr
	}
	for i, root := range prf.Commitments {
		res.roots[res.layout.SetupEnd+i] = root
	}

	// Initialize the FS transcript. Pre-register only the caller-side
	// challenges (per-round + zeta); alpha_DEEP and FRI-internal names
	// are registered by fri.PCS.Verify at invocation time.
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
	numRounds := len(program.FScolumnsDependencies)
	for i := 0; i < numRounds; i++ {
		res.fs.NewChallenge(constants.CanonicalChallengeName(i))
	}
	res.fs.NewChallenge(constants.FINAL_EVALUATION_POINT)

	initialChallenge := constants.InitialChallengeName(numRounds)
	if err := res.fs.Bind(initialChallenge, hash.StringToElements(constants.HASH_BACKEND_DOMAIN_TAG, hashBackend.ID)); err != nil {
		return res, err
	}

	// Bind every setup tree's root to the first challenge (decreasing-N order,
	// set by Setup) + public inputs.
	for _, pkr := range verificationKey.Roots {
		if err := res.fs.Bind(initialChallenge, pkr[:]); err != nil {
			return res, err
		}
	}
	if len(publicInputs) > 0 {
		if err := res.fs.Bind(initialChallenge, publicInputs.TranscriptElements()); err != nil {
			return res, err
		}
	}

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

	return res, nil
}

// setValueAtZetaExt records an ext-valued claimed evaluation under name.
// Replaces the old proof.Proof.SetValueAtZetaExt accessor.
func (vr *verifierRunTime) setValueAtZetaExt(name string, v ext.E6) {
	vr.valuesAtZeta[name] = v
}

// valueAtZetaExt looks up the claimed evaluation registered under name.
// Replaces the old proof.Proof.ValueAtZetaExt accessor.
func (vr *verifierRunTime) valueAtZetaExt(name string) (ext.E6, bool) {
	v, ok := vr.valuesAtZeta[name]
	return v, ok
}

// TODO catch error when calling Bind
func (vr *verifierRunTime) deriveChallenges() error {

	// For each FS round, bind every trace root for that round before computing
	// the round challenge. A non-empty round normally has one mixed-size root.
	// Setup roots were already bound to challenge_0 in newVerifierRuntime.
	numRounds := len(vr.program.FScolumnsDependencies)
	for r := 0; r < numRounds; r++ {
		challengeName := constants.CanonicalChallengeName(r)
		for i := vr.layout.TraceBegin[r]; i < vr.layout.TraceEnd[r]; i++ {
			root := vr.roots[i]
			err := vr.fs.Bind(challengeName, root[:])
			if err != nil {
				return err
			}
		}
		challenge, err := vr.fs.ComputeChallenge(challengeName)
		if err != nil {
			return err
		}
		c := hash.OutputToExt(challenge)
		vr.setValueAtZetaExt(challengeName, c)
	}
	// Bind every per-size AIR-quotient root before computing zeta.
	for i := vr.layout.AIRBegin; i < vr.layout.AIREnd; i++ {
		root := vr.roots[i]
		err := vr.fs.Bind(constants.FINAL_EVALUATION_POINT, root[:])
		if err != nil {
			return err
		}
	}
	zeta, err := vr.fs.ComputeChallenge(constants.FINAL_EVALUATION_POINT)
	if err != nil {
		return err
	}
	vr.zeta = hash.OutputToExt(zeta)

	return nil
}

// loadClaimedValues translates Opening.ClaimedValues into the local
// vr.valuesAtZeta map keyed by canonical leaf names (= leaf.String()).
// Walks the canonical schedule in parallel with Opening.ClaimedValues:
// every (batch, group, base|ext, polyIdx, kth_shift) tuple has a value
// in ClaimedValues and a (possibly multi-entry) list of canonical keys
// in schedule.Keys. All keys sharing one (poly, normalized shift) share
// one value.
func (vr *verifierRunTime) loadClaimedValues() error {
	cv := vr.proof.Opening.ClaimedValues
	if len(cv) != len(vr.schedule.Keys) {
		return fmt.Errorf("loadClaimedValues: Opening.ClaimedValues has %d batches, schedule has %d", len(cv), len(vr.schedule.Keys))
	}
	for b, batchKeys := range vr.schedule.Keys {
		if len(cv[b]) != len(batchKeys) {
			return fmt.Errorf("loadClaimedValues: batch %d has %d groups, schedule has %d", b, len(cv[b]), len(batchKeys))
		}
		for g, groupKeys := range batchKeys {
			gcv := cv[b][g]
			if len(gcv.Base) != len(groupKeys.Base) {
				return fmt.Errorf("loadClaimedValues: batch %d group %d Base width mismatch (%d vs %d)", b, g, len(gcv.Base), len(groupKeys.Base))
			}
			if len(gcv.Ext) != len(groupKeys.Ext) {
				return fmt.Errorf("loadClaimedValues: batch %d group %d Ext width mismatch (%d vs %d)", b, g, len(gcv.Ext), len(groupKeys.Ext))
			}
			for i, perPolyKeys := range groupKeys.Base {
				if len(gcv.Base[i]) != len(perPolyKeys) {
					return fmt.Errorf("loadClaimedValues: batch %d group %d Base[%d] shift count mismatch (%d vs %d)", b, g, i, len(gcv.Base[i]), len(perPolyKeys))
				}
				for k, keys := range perPolyKeys {
					v := gcv.Base[i][k]
					for _, name := range keys {
						vr.setValueAtZetaExt(name, v)
					}
				}
			}
			for i, perPolyKeys := range groupKeys.Ext {
				if len(gcv.Ext[i]) != len(perPolyKeys) {
					return fmt.Errorf("loadClaimedValues: batch %d group %d Ext[%d] shift count mismatch (%d vs %d)", b, g, i, len(gcv.Ext[i]), len(perPolyKeys))
				}
				for k, keys := range perPolyKeys {
					v := gcv.Ext[i][k]
					for _, name := range keys {
						vr.setValueAtZetaExt(name, v)
					}
				}
			}
		}
	}
	return nil
}

// computeVerifierColumns fills in every leaf the verifier evaluates at zeta
// itself — Lagrange selectors, public inputs and prover-exposed values —
// rather than reading it from a prover opening. Each such leaf carries an
// expr.HookID naming the formula to use; the hook is resolved through HookMap.
//
// The hooks are mutually independent (none consumes another's output), so a
// single pass in leaf order is equivalent to the three ordered passes this
// replaces.
func (vr *verifierRunTime) computeVerifierColumns() error {
	config := expr.NewConfig(expr.OnlyVerifierColumns...)
	for _, m := range vr.program.Modules {
		for _, leaf := range m.VanishingRelation.LeavesFull(config) {
			// LeavesFull yields one entry per distinct leaf node, so the same
			// column can come up more than once across shared subtrees; and
			// loadClaimedValues may already have supplied a value.
			name := leaf.String()
			if _, ok := vr.valueAtZetaExt(name); ok {
				continue
			}
			hook, ok := HookMap[leaf.Hook]
			if !ok {
				return fmt.Errorf("computeVerifierColumns: %s carries unregistered hook %s", name, leaf.Hook)
			}
			v, err := hook(vr, m, leaf)
			if err != nil {
				return err
			}
			vr.setValueAtZetaExt(name, v)
		}
	}
	return nil
}

func (vr *verifierRunTime) checkLogupBus() error {
	for _, bus := range vr.program.LogupBus {
		var cumNegative, cumPositive ext.E6
		for _, pos := range bus.Positive {
			if len(vr.proof.ExposedValues[pos].Entries) > 1 {
				return fmt.Errorf("an extracted value from a logup column should have exactly one entry")
			}
			// TODO add a check that the exposed value's index is N-1
			pe := vr.proof.ExposedValues[pos].Entries[0]
			value := pe.ExtValue()
			cumPositive.Add(&cumPositive, &value)
		}
		for _, neg := range bus.Negative {
			if len(vr.proof.ExposedValues[neg].Entries) > 1 {
				return fmt.Errorf("an extracted value from a logup column should have exactly one entry")
			}
			// TODO add a check that the exposed value's index is N-1
			pe := vr.proof.ExposedValues[neg].Entries[0]
			value := pe.ExtValue()
			cumNegative.Add(&cumNegative, &value)
		}
		cumPositive.Sub(&cumPositive, &cumNegative)
		if !cumPositive.IsZero() {
			return fmt.Errorf("the cumulative sums of the bus are not equal")
		}
	}
	return nil
}

// checkAIRRelations checks the air relations per module.
func (vr *verifierRunTime) checkAIRRelations() error {
	// EvalExt expects the full claimed-values map.
	valuesAtZeta := make(map[string]ext.E6, len(vr.valuesAtZeta))
	for k, v := range vr.valuesAtZeta {
		valuesAtZeta[k] = v
	}

	for moduleName, m := range vr.program.Modules {
		var qZeta ext.E6
		var zetaPowIN ext.E6
		zetaPowIN.SetOne()
		var zetaN ext.E6
		zetaN.Exp(vr.zeta, big.NewInt(int64(m.N)))
		for i := 0; ; i++ {
			chunkName := constants.QuotientChunkName(moduleName, i)
			chunkVal, ok := vr.valueAtZetaExt(chunkName)
			if !ok {
				break
			}
			var term ext.E6
			term.Mul(&zetaPowIN, &chunkVal)
			qZeta.Add(&qZeta, &term)
			zetaPowIN.Mul(&zetaPowIN, &zetaN)
		}

		vZeta := m.VanishingRelation.EvalExt(valuesAtZeta)

		var one, zetaNMinusOne, rhs ext.E6
		one.SetOne()
		zetaNMinusOne.Sub(&zetaN, &one)
		rhs.Mul(&zetaNMinusOne, &qZeta)

		if !vZeta.Equal(&rhs) {
			return fmt.Errorf("AIR relation check failed for module %q: V(zeta)=%s != (zeta^N-1)*Q(zeta)=%s", moduleName, vZeta.String(), rhs.String())
		}
	}

	return nil
}

// runPCSVerify reconstructs the per-batch shapes from layout + setup
// metadata and invokes fri.PCS.Verify on proof.Opening with the same
// shift schedule the prover used. PCS.Verify internally registers
// alpha_DEEP + FRI challenge names, replays the claimed-value binding
// in canonical-layout order, runs the multi-degree FRI check, and
// authenticates every (query, batch) Merkle path.
func (vr *verifierRunTime) runPCSVerify() error {
	shapes := make([]fri.BatchShapes, vr.layout.NumTrees)
	for treeIdx := 0; treeIdx < vr.layout.NumTrees; treeIdx++ {
		if treeIdx >= len(vr.layout.TreeGroups) {
			return fmt.Errorf("runPCSVerify: tree %d has no layout group metadata", treeIdx)
		}
		groups := vr.layout.TreeGroups[treeIdx]
		namesByGroup := vr.schedule.ColNamesByTree[treeIdx]
		if len(namesByGroup) != len(groups) {
			return fmt.Errorf("runPCSVerify: tree %d has %d scheduled groups, layout has %d", treeIdx, len(namesByGroup), len(groups))
		}
		shapes[treeIdx] = make(fri.BatchShapes, len(groups))
		for groupIdx, group := range groups {
			names := namesByGroup[groupIdx]
			shapes[treeIdx][groupIdx] = fri.GroupShape{
				Rows:      int(constants.RATE) * group.N,
				BaseWidth: len(names.Base),
				ExtWidth:  len(names.Ext),
			}
		}
	}

	pcs := fri.NewPCSWithParams(vr.friParams)
	return pcs.Verify(vr.roots, shapes, vr.schedule.Shifts, vr.zeta, vr.proof.Opening, vr.fs)
}

func Verify(publicInputs public.Inputs, verificationKey setup.VerificationKey, program board.Program, proof proof.Proof, opts ...Option) error {

	var config Config
	config.NumFriQueries = constants.NUM_QUERIES
	// The verifier never folds polynomials, so it doesn't need the full FFT
	// twiddle tables — only the domain generator is used for path checks.
	config.FriOptions = []fri.Option{fri.WoFullDomainAllocation()}
	for _, opt := range opts {
		err := opt(&config)
		if err != nil {
			return err
		}
	}

	vr, err := newVerifierRuntime(program, verificationKey, publicInputs, proof, config)
	if err != nil {
		return err
	}

	// 1 - derive the per-round challenges and zeta from the transcript.
	if err := vr.deriveChallenges(); err != nil {
		return err
	}

	// 2 - translate Opening.ClaimedValues into vr.valuesAtZeta keyed by
	//     canonical leaf names, then add verifier-reconstructed entries
	//     (Lagrange, public inputs, exposed values).
	if err := vr.loadClaimedValues(); err != nil {
		return err
	}
	if err := vr.computeVerifierColumns(); err != nil {
		return err
	}

	// 3 - check logup buses (multi-set equality from cumulative sums).
	if err := vr.checkLogupBus(); err != nil {
		return err
	}

	// 4 - check the AIR relations at zeta.
	if err := vr.checkAIRRelations(); err != nil {
		return err
	}

	// 5 - PCS verification: alpha_DEEP replay + FRI proof + Merkle paths
	//     + bridge check (DQ_N(±X) recomputed from raw leaves & claimed
	//     values, compared against the FRI level leaves).
	if config.SkipFRI {
		return nil
	}
	return vr.runPCSVerify()
}
