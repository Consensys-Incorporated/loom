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

// # Round model
//
// A round is one Fiat-Shamir boundary. The caller declares, for each round, the
// prover steps it runs and the columns it commits (stages). In round order the
// prover:
//
//  1. runs that round's prover steps, in slice order;
//  2. commits that round's staged columns;
//  3. applies the round's FS hook, if any;
//  4. derives the round's challenge, Coin(r).
//
// The last declared round is the folding round: every committed column that no
// round staged is swept into it, and its challenge folds the per-module AIR
// relations. Staging is therefore opt-in: a caller names only the columns that
// must be committed early. A builder that declares no round gets a single one.
//
// The arguments package uses three rounds:
//
//	RoundFold           stages the raw tables and their multiplicities;
//	                    Coin(RoundFold) folds tables into single columns
//	RoundLogDerivative  stages nothing; Coin(RoundLogDerivative) is the
//	                    log-derivative / grand-product challenge
//	RoundRunningSums    computes the running sums and products, which are
//	                    swept into it; Coin(RoundRunningSums) folds the AIR
//
// Compile does no scheduling: it resolves column metadata and validates the
// declared rounds (see validateRounds).

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
	// RoundFold commits the raw tables of the arguments and samples the
	// challenge that folds tables into single columns.
	RoundFold = 0
	// RoundLogDerivative commits nothing and samples the log-derivative
	// challenge, independent of the folding one.
	RoundLogDerivative = 1
	// RoundRunningSums computes the running sums and products of the
	// arguments, which depend on both previous challenges.
	RoundRunningSums = 2
)

// Coin returns the challenge sampled at the end of round r, as an expression
// usable in relations and step inputs.
//
// Referencing Coin(r) is only legal from round r+1 onwards; validateRounds
// rejects earlier uses.
func Coin(r int) expr.Expr {
	return expr.Challenge(constants.CanonicalChallengeName(r))
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
	// module and field resolved by Compile.
	Staged []ColumnRef
	// FSHook is extra data bound after the commitment, or NoFSHook.
	FSHook FSHookID
}

// builderRound is the caller-facing accumulator, before module and field
// resolution.
type builderRound struct {
	Steps  []ProverStep
	Staged []string
	FSHook FSHookID
}

// growTo makes round r addressable, creating any intermediate rounds. Empty
// intermediate rounds are legal: they still sample a challenge.
func (b *Builder) growTo(r int) {
	if r < 0 {
		panic(fmt.Sprintf("board: negative round %d", r))
	}
	for len(b.rounds) <= r {
		b.rounds = append(b.rounds, builderRound{})
	}
}

// StageColumns commits the named columns at the end of round r. Staging a
// column twice in the same round is a no-op; staging it in two different
// rounds is rejected by Compile.
func (b *Builder) StageColumns(r int, names ...string) {
	b.growTo(r)
	for _, name := range names {
		if !containsString(b.rounds[r].Staged, name) {
			b.rounds[r].Staged = append(b.rounds[r].Staged, name)
		}
	}
}

// StageLeaves commits, at the end of round r, every committed column that the
// expressions reference. Challenges, setup and verifier columns are skipped.
func (b *Builder) StageLeaves(r int, exprs ...expr.Expr) {
	config := committedConfig()
	for _, e := range exprs {
		for _, leaf := range e.LeavesFull(config) {
			b.StageColumns(r, leaf.Name)
		}
	}
}

// AddStepAt schedules step in round r, after any step already added to it.
func (b *Builder) AddStepAt(r int, step ProverStep) {
	b.growTo(r)
	b.rounds[r].Steps = append(b.rounds[r].Steps, step)
}

// SetFSHook attaches an FS hook to round r, replacing any previous one.
func (b *Builder) SetFSHook(r int, id FSHookID) {
	b.growTo(r)
	b.rounds[r].FSHook = id
}

// NumDeclaredRounds is the number of rounds the caller declared.
func (b *Builder) NumDeclaredRounds() int {
	return len(b.rounds)
}

// LateColumn is one column committed after the round that produces it.
type LateColumn struct {
	Name     string
	Produced int
	Staged   int
}

// StrictNoLateStaging reports an error if any column was committed later than
// the round that produces it.
func (p *Program) StrictNoLateStaging() error {
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
// verifier columns.
func committedConfig() expr.Config {
	return expr.NewConfig(
		expr.WithoutChallenges(),
		expr.WithoutSetupColumns(),
		expr.WithoutVerifierColumns(),
	)
}

// columnModules maps every committed column name to its owning module, by
// scanning the module relations. The result feeds ColumnRef.Module, which
// internal/protocol/layout.go needs to group commitments by polynomial size.
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

// compileRounds resolves each staged column to a ColumnRef, sweeps every
// committed column not staged by any round into the last round, and validates
// the result. It returns the rounds and the columns committed later than the
// round that produces them.
func compileRounds(b *Builder) ([]ProverRound, []LateColumn, error) {
	owner := columnModules(b.Modules)

	declared := b.rounds
	if len(declared) == 0 {
		declared = []builderRound{{}}
	}

	producer, err := stepProducers(declared)
	if err != nil {
		return nil, nil, err
	}

	rounds := make([]ProverRound, len(declared))
	staged := make(map[string]int) // column name -> round that stages it
	for r, br := range declared {
		round := ProverRound{Steps: br.Steps, FSHook: br.FSHook}
		for _, name := range br.Staged {
			if prev, ok := staged[name]; ok {
				return nil, nil, fmt.Errorf(
					"board.Compile: column %q staged twice, at rounds %d and %d", name, prev, r)
			}
			module, ok := owner[name]
			if !ok {
				return nil, nil, fmt.Errorf(
					"board.Compile: column %q staged at round %d is not referenced by any module relation",
					name, r)
			}
			staged[name] = r
			round.Staged = append(round.Staged, ColumnRef{Name: name, Module: module})
		}
		rounds[r] = round
	}

	// Sweep into the folding round every committed column no round staged: the
	// raw trace columns nobody staged, and the columns produced by the last
	// round's steps.
	var late []LateColumn
	last := len(rounds) - 1
	for _, name := range sortedKeys(owner) {
		if _, ok := staged[name]; ok {
			continue
		}
		staged[name] = last
		rounds[last].Staged = append(rounds[last].Staged, ColumnRef{Name: name, Module: owner[name]})
		// A swept column produced by an earlier round's step is committed later
		// than it had to be: the prover could in principle choose it after
		// seeing the challenges sampled in between. That is harmless when the
		// relations pin it down, but worth reporting.
		if p, ok := producer[name]; ok && p != last {
			late = append(late, LateColumn{Name: name, Produced: p, Staged: last})
		}
	}

	if err := validateRounds(b.Modules, rounds, producer, staged); err != nil {
		return nil, nil, err
	}
	return rounds, late, nil
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
						"board.Compile: column %q produced twice, at rounds %d and %d", out, prev, r)
				}
				producer[out] = r
			}
		}
	}
	return producer, nil
}

// validateRounds checks the properties a well-formed protocol needs. Each is a
// linear scan.
//
//  1. Every committed column is staged exactly once. The "staged twice" half is
//     checked in compileRounds as the map is built; the "never staged" half is
//     absorbed by the folding round, which stages whatever is left.
//  2. No column is staged before the round that produces it: it would be
//     committed while still empty.
//  3. A step's inputs are available: produced earlier in the same round or in
//     an earlier round, and committed no later than the step's round. The
//     latter keeps a challenge-dependent step from reading a column the prover
//     may still choose.
//  4. Coin(r) is referenced by steps only from round r+1 onwards, and by
//     relations only for rounds that exist.
func validateRounds(modules map[string]*Module, rounds []ProverRound, producer, staged map[string]int) error {
	config := committedConfig()
	onlyChallenges := expr.NewConfig(expr.OnlyChallenges...)

	// Property 2.
	for name, r := range staged {
		if p, ok := producer[name]; ok && r < p {
			return fmt.Errorf(
				"board.Compile: column %q is staged at round %d but produced at round %d; "+
					"it would be committed before it is filled", name, r, p)
		}
	}

	// Properties 3 and 4, on step inputs.
	for r, round := range rounds {
		availableHere := make(map[string]bool)
		for _, step := range round.Steps {
			for _, in := range step.Ins {
				for _, leaf := range in.LeavesFull(config) {
					name := leaf.Name
					if availableHere[name] {
						continue
					}
					if p, ok := producer[name]; ok && p >= r {
						return fmt.Errorf(
							"board.Compile: round %d step %v reads column %q before it is produced (round %d)",
							r, step.Outs, name, p)
					}
					if s, ok := staged[name]; ok && s > r {
						return fmt.Errorf(
							"board.Compile: round %d step %v reads column %q, staged later at round %d",
							r, step.Outs, name, s)
					}
				}
				for _, name := range in.Leaves(onlyChallenges) {
					src, ok := constants.ParseCanonicalChallengeName(name)
					if !ok {
						return fmt.Errorf(
							"board.Compile: round %d step %v reads challenge %q, which is not a round coin",
							r, step.Outs, name)
					}
					if src >= r {
						return fmt.Errorf(
							"board.Compile: round %d step %v reads %s, which is only sampled at the end of round %d",
							r, step.Outs, name, src)
					}
				}
			}
			for _, out := range step.Outs {
				availableHere[out] = true
			}
		}
	}

	// Property 4, on module relations.
	for moduleName, m := range modules {
		for _, rel := range m.Relations {
			for _, name := range rel.Leaves(onlyChallenges) {
				src, ok := constants.ParseCanonicalChallengeName(name)
				if !ok {
					return fmt.Errorf(
						"board.Compile: module %q references challenge %q, which is not a round coin",
						moduleName, name)
				}
				if src >= len(rounds) {
					return fmt.Errorf(
						"board.Compile: module %q references %s, but the protocol has only %d rounds",
						moduleName, name, len(rounds))
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

func containsString(s []string, x string) bool {
	for _, y := range s {
		if y == x {
			return true
		}
	}
	return false
}
