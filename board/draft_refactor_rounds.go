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

package board

// DRAFT — not wired into Compile yet. Everything here compiles and is covered
// by draft_refactor_rounds_test.go, but nothing in the prover, verifier or
// arguments packages uses it.
//
// # What this replaces
//
// Compile currently infers the protocol's round structure from data
// dependencies, in nine phases with two fixed-point loops:
//
//   - phases 1 and 4 derive a level per step from input/output names;
//   - phase 2 derives which FS steps may share a round, by checking whether one
//     challenge transitively feeds another's inputs;
//   - phases 3, 3.5 and 7 repair the interaction between the two, syncing FS
//     steps to a common level, forcing strictly increasing levels so distinct
//     rounds cannot merge, and collapsing same-level FS steps into one
//     canonical challenge;
//   - phases 7e and 8 derive the column-to-round map with a "first round that
//     mentions the column wins" rule plus a final sweep of the leftovers.
//
// Here the caller states the round instead, and Compile's job shrinks to
// resolving column metadata and *validating* what was stated. The inference was
// also an implicit correctness guarantee, so the validation is not optional:
// see ValidateRounds for the four properties the phases used to establish by
// construction.
//
// # Round model
//
// A round is one Fiat-Shamir boundary. In round order the prover:
//
//  1. runs that round's prover steps;
//  2. commits that round's staged columns;
//  3. applies the round's FS hook, if any;
//  4. derives the round's challenge.
//
// This is already what prover.ExecuteSteps does; the difference is that the
// round boundary becomes explicit data rather than "a level that happens to
// contain an FS step".
//
// In practice arguments need at most two rounds, and Compile appends one more:
//
//	round 0            fold tables down to single columns
//	round 1            log-derivative / lookup challenge
//	round NumRounds-1  fold the per-module AIR relations (appended by Compile)
//
// The trailing folding round is not something a caller stages into. It is
// appended by CompileRounds, and every committed column not staged by an
// earlier round is swept into it — which is what phase 8 did. Staging is
// therefore opt-in: a caller names only the columns that must be committed
// early, and everything else lands in the folding round by default.

import (
	"fmt"
	"sort"

	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
)

// Conventional round numbers. They are ordinary ints: a caller composing
// arguments owns the numbering, and nothing here requires these particular
// values.
const (
	// RoundFold samples the challenge that folds tables into single columns.
	RoundFold = 0
	// RoundLogDerivative samples the challenge of the log-derivative argument.
	// It must follow RoundFold because its staged columns are computed from
	// folded expressions.
	RoundLogDerivative = 1
)

// Coin returns the challenge sampled at the end of round r, as an expression
// usable in relations and step inputs.
//
// Referencing Coin(r) is only legal from round r+1 onwards; ValidateRounds
// rejects earlier uses, which the old phase 3.5 prevented by construction.
func Coin(r int) expr.Expr {
	return expr.Challenge(constants.CanonicalChallengeName(r))
}

// StagedColumns is the set of columns committed at the end of one round, by
// bare name.
//
// Names alone are enough: CompileRounds resolves the owning module and field
// from the module relations, the same way Compile builds its columnModule map
// today. Callers should not have to repeat what the relations already say.
type StagedColumns []string

// AddCol stages one or more columns. The receiver is a pointer because AddCol
// appends.
func (sc *StagedColumns) AddCol(names ...string) {
	*sc = append(*sc, names...)
}

// FSHookID selects extra data to bind into the transcript after a round's
// commitment, for instance a preflight digest.
//
// It is an ID rather than a func value for the same reason expr.HookID is: the
// verifier must perform the identical binding, and a func in Program would be
// neither reachable from the verifier nor serializable. Prover and verifier
// each keep their own registry keyed by this ID.
type FSHookID int

// NoFSHook is the zero value: a round that binds nothing beyond its
// commitment. Making it the zero value means a round left unset cannot silently
// acquire a real hook.
const NoFSHook FSHookID = 0

// ProverRound is one round of the compiled protocol.
type ProverRound struct {
	// Steps run before this round's commitment, in slice order. A step may
	// depend on an earlier step in the same round or on any earlier round.
	Steps []ProverStep
	// Staged are the columns committed at the end of this round, with their
	// module and field resolved by CompileRounds.
	Staged []ColumnRef
	// FSHook is extra data bound after the commitment, or NoFSHook.
	FSHook FSHookID
}

// builderRound is the caller-facing accumulator, before module and field
// resolution.
type builderRound struct {
	Steps  []ProverStep
	Staged StagedColumns
	FSHook FSHookID
}

// RoundBuilder is a Builder that records which round each column and step
// belongs to.
//
// It embeds Builder so that AddModule, AssertZero and the argument helpers keep
// working unchanged during migration. Only the step- and column-registering
// calls need to move over.
// TODO embedd directly 'rounds []builderRound' in Builder, and attach the RoundBuilder's methods on Builder directly once the refactor is done
type RoundBuilder struct {
	Builder
	rounds []builderRound
}

// NewRoundBuilder returns a RoundBuilder with no rounds declared.
func NewRoundBuilder() RoundBuilder {
	return RoundBuilder{Builder: NewBuilder()}
}

// growTo makes round r addressable, creating any intermediate rounds. Empty
// intermediate rounds are legal: they still sample a challenge.
func (b *RoundBuilder) growTo(r int) {
	for len(b.rounds) <= r {
		b.rounds = append(b.rounds, builderRound{})
	}
}

// StageColumns commits names at the end of round r.
func (b *RoundBuilder) StageColumns(r int, names ...string) {
	b.growTo(r)
	b.rounds[r].Staged.AddCol(names...)
}

// AddStepAt schedules step in round r, after any step already added to it.
func (b *RoundBuilder) AddStepAt(r int, step ProverStep) {
	b.growTo(r)
	b.rounds[r].Steps = append(b.rounds[r].Steps, step)
}

// SetFSHook attaches an FS hook to round r, replacing any previous one.
func (b *RoundBuilder) SetFSHook(r int, id FSHookID) {
	b.growTo(r)
	b.rounds[r].FSHook = id
}

// NumDeclaredRounds is the number of rounds the caller declared, excluding the
// folding round CompileRounds appends.
func (b *RoundBuilder) NumDeclaredRounds() int {
	return len(b.rounds)
}

// RoundProgram is the compiled form: Program with Rounds in place of the
// level-scheduled Steps and the derived FScolumnsDependencies.
//
// Rounds[r].Staged is exactly what FScolumnsDependencies[r] holds today, so the
// layout and schedule builders in internal/protocol need only a field rename.
type RoundProgram struct {
	Program
	Rounds []ProverRound
	// Late lists columns the sweep committed later than the round that produces
	// them. It is diagnostic, not an error: the protocol is well-formed either
	// way, and CompileRounds keeps sweeping.
	//
	// It is worth looking at, because a late-committed column is one the prover
	// could in principle choose after seeing the challenges sampled in between.
	// That is harmless when the column is pinned down by the AIR relations, and
	// is not something today's Compile can produce at all, so a non-empty Late
	// means a caller staged something in a way the old inference never would.
	// Use StrictNoLateStaging to turn it into an error.
	Late []LateColumn
}

// LateColumn is one column committed after the round that produces it.
type LateColumn struct {
	Name     string
	Produced int
	Staged   int
}

// StrictNoLateStaging reports an error if any column was committed later than
// the round that produces it. Callers that want the old inference's implicit
// guarantee back can run it after CompileRounds.
func (p *RoundProgram) StrictNoLateStaging() error {
	for _, late := range p.Late {
		return fmt.Errorf(
			"StrictNoLateStaging: column %q is produced at round %d but committed at round %d; "+
				"stage it in round %d, or move the step that produces it",
			late.Name, late.Produced, late.Staged, late.Produced)
	}
	return nil
}

// committedConfig selects the leaves that correspond to committed trace
// columns: no challenges, no setup columns (those are precommitted), and no
// verifier columns. It matches the config Compile uses in phases 7e and 8.
func committedConfig() expr.Config {
	return expr.NewConfig(
		expr.WithoutChallenges(),
		expr.WithoutSetupColumns(),
		expr.WithoutVerifierColumns(),
	)
}

// columnModules maps every committed column name to its owning module, by
// scanning the module relations.
//
// This is the one piece of inference worth keeping: it is a linear scan, it
// cannot disagree with the relations, and it spares every caller from repeating
// a module name the relations already carry. The result feeds ColumnRef.Module,
// which internal/protocol/layout.go needs to group commitments by polynomial
// size for multi-degree FRI.
func columnModules(modules map[string]*Module) map[string]string {
	config := committedConfig()
	owner := make(map[string]string)
	for moduleName, m := range modules {
		for _, rel := range m.Relations {
			for _, leaf := range rel.LeavesFull(config) {
				owner[leaf.Name] = moduleName
			}
		}
	}
	return owner
}

// CompileRounds turns a RoundBuilder into a RoundProgram.
//
// It resolves each staged column to a ColumnRef, appends the folding round that
// commits whatever was not staged earlier, and validates the result. It does no
// scheduling: round order is the caller's, and step order within a round is
// slice order.
//
// The returned program's embedded Program is left partly unset; wiring the
// remaining fields (ColumnFields, Modules, LogupBus) is the same work Compile
// phases 8 and 9 already do and is deliberately out of scope for this draft.
func CompileRounds(b *RoundBuilder) (RoundProgram, error) {
	var res RoundProgram

	owner := columnModules(b.Modules)

	producer, err := stepProducers(b.rounds)
	if err != nil {
		return res, err
	}

	// Declared rounds, in order.
	res.Rounds = make([]ProverRound, 0, len(b.rounds)+1)
	staged := make(map[string]int) // column name -> round that stages it
	for r, br := range b.rounds {
		round := ProverRound{Steps: br.Steps, FSHook: br.FSHook}
		for _, name := range br.Staged {
			if prev, ok := staged[name]; ok {
				return res, fmt.Errorf(
					"CompileRounds: column %q staged twice, at rounds %d and %d", name, prev, r)
			}
			module, ok := owner[name]
			if !ok {
				return res, fmt.Errorf(
					"CompileRounds: column %q staged at round %d is not referenced by any module relation",
					name, r)
			}
			staged[name] = r
			round.Staged = append(round.Staged, ColumnRef{Name: name, Module: module})
		}
		res.Rounds = append(res.Rounds, round)
	}

	// The folding round. Its challenge folds the per-module AIR relations, and
	// it commits every committed column no earlier round staged — the raw trace
	// columns nobody staged, and the running sums produced after the last
	// argument challenge.
	//
	// Sweeping is unconditional, matching Compile's phase 8: staging is a
	// convenience for pinning a column to an early round, not an obligation to
	// name every column. A caller who stages nothing at all still gets a valid
	// single-round protocol.
	foldRound := len(res.Rounds)
	leftovers := make([]ColumnRef, 0)
	for _, name := range sortedKeys(owner) {
		if _, ok := staged[name]; ok {
			continue
		}
		staged[name] = foldRound
		leftovers = append(leftovers, ColumnRef{Name: name, Module: owner[name]})
		// A swept column produced by an earlier round's step is committed later
		// than it had to be. Today's Compile cannot express this — phase 4 bumps
		// every non-FS step past the FS level it lands on, so a produced column
		// is always swept into its own round — but explicit staging can, so
		// record it rather than let it pass unnoticed. See RoundProgram.Late.
		if p, ok := producer[name]; ok && p != foldRound {
			res.Late = append(res.Late, LateColumn{Name: name, Produced: p, Staged: foldRound})
		}
	}
	res.Rounds = append(res.Rounds, ProverRound{Staged: leftovers})

	if err := ValidateRounds(b, res.Rounds, producer, staged); err != nil {
		return res, err
	}
	return res, nil
}

// stepProducers maps each step output to the round of the step that writes it,
// rejecting any column two steps both claim to produce.
func stepProducers(rounds []builderRound) (map[string]int, error) {
	producer := make(map[string]int)
	for r, round := range rounds {
		for _, step := range round.Steps {
			for _, out := range step.Outs {
				if prev, ok := producer[out]; ok {
					return nil, fmt.Errorf(
						"CompileRounds: column %q produced twice, at rounds %d and %d", out, prev, r)
				}
				producer[out] = r
			}
		}
	}
	return producer, nil
}

// ValidateRounds re-establishes, as checks, the four properties the old phase
// pipeline guaranteed by construction. Each is a linear scan; none needs a
// fixed point.
//
//  1. Every committed column is staged exactly once. The "staged twice" half is
//     checked in CompileRounds as the map is built; the "never staged" half is
//     absorbed by the folding round, which stages whatever is left.
//  2. No column is staged *before* the round that produces it — that column
//     would be committed while still empty. Staging after production is the
//     sweep and is allowed; RoundProgram.Late records it.
//  3. A step's inputs are available: produced earlier in the same round, or
//     staged in a strictly earlier round.
//  4. Coin(r) is referenced only from round r+1 onwards. This is what phase 3.5
//     defended against, and the one a caller is most likely to get wrong,
//     because the symptom is a silently wrong proof rather than a panic.
func ValidateRounds(b *RoundBuilder, rounds []ProverRound, producer, staged map[string]int) error {
	config := committedConfig()
	onlyChallenges := expr.NewConfig(expr.OnlyChallenges...)

	// Property 2. Only staging strictly before production is an error; staging
	// after it is the folding round's sweep.
	for name, r := range staged {
		if p, ok := producer[name]; ok && r < p {
			return fmt.Errorf(
				"ValidateRounds: column %q is staged at round %d but produced at round %d; "+
					"it would be committed before it is filled", name, r, p)
		}
	}

	// Properties 3 and 4.
	for r, round := range rounds {
		// Columns produced earlier within this same round are available to
		// later steps in it.
		availableHere := make(map[string]bool)
		for _, step := range round.Steps {
			for _, in := range step.Ins {
				for _, leaf := range in.LeavesFull(config) {
					name := leaf.Name
					if availableHere[name] {
						continue
					}
					if p, ok := producer[name]; ok && p > r {
						return fmt.Errorf(
							"ValidateRounds: round %d step %v reads column %q, produced later at round %d",
							r, step.Outs, name, p)
					}
					if s, ok := staged[name]; ok && s > r {
						return fmt.Errorf(
							"ValidateRounds: round %d step %v reads column %q, staged later at round %d",
							r, step.Outs, name, s)
					}
				}
				// Property 4, on step inputs.
				for _, name := range in.Leaves(onlyChallenges) {
					src, ok := constants.ParseCanonicalChallengeName(name)
					if !ok {
						continue
					}
					if src >= r {
						return fmt.Errorf(
							"ValidateRounds: round %d step %v reads %s, which is only sampled at the end of round %d",
							r, step.Outs, name, src)
					}
				}
			}
			for _, out := range step.Outs {
				availableHere[out] = true
			}
		}
	}

	// Property 4, on module relations. A relation may reference any challenge
	// sampled by any round, including the folding round, so the only bad case
	// is a challenge from a round that does not exist.
	numRounds := len(rounds)
	for moduleName, m := range b.Modules {
		for _, rel := range m.Relations {
			for _, name := range rel.Leaves(onlyChallenges) {
				src, ok := constants.ParseCanonicalChallengeName(name)
				if !ok {
					continue
				}
				if src >= numRounds {
					return fmt.Errorf(
						"ValidateRounds: module %q references %s, but the protocol has only %d rounds",
						moduleName, name, numRounds)
				}
			}
		}
	}

	return nil
}

func sortedKeys(m map[string]string) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}
