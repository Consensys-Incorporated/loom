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

package arguments

import (
	"fmt"
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
)

// Lookups collects lookups and builds them grouped by target: the lookups
// into the same target (the same table, selector and module) share one
// multiplicity column, counted over all their sources. Building each lookup on
// its own (CLookupTuple) would instead add a multiplicity column and a
// target-side fraction per lookup.
//
// All the lookups share one logup bus. Each target k has a constant tag, k,
// folded in front of its tuples: fold(α, [k, c_1, …, c_w]) = k + α·c_1 + … +
// α^w·c_w, whose constant coefficient is k whatever the width, so tuples of
// different targets are distinct polynomials in α, and their fractions
// cannot cancel each other. The fractions of a module, whatever their
// targets, are then batched into the same logup columns.
//
// Register the lookups with Add, then call Build once.
type Lookups struct {
	groups []*lookupGroup
	index  map[string]int // target key → group
}

// lookupGroup is the lookups into one target.
type lookupGroup struct {
	target  board.CTable
	sources []board.CTable
}

// NewLookups returns an empty collector.
func NewLookups() *Lookups {
	return &Lookups{index: map[string]int{}}
}

// Add registers the lookup {row(source) | source.Sel ≠ 0} ⊂ {row(target) | target.Sel ≠ 0}.
func (l *Lookups) Add(source, target board.CTable) error {
	if len(source.In) == 0 || len(source.In) != len(target.In) {
		return fmt.Errorf("Lookups.Add: source of width %d, target of width %d", len(source.In), len(target.In))
	}
	key := targetKey(target)
	g, ok := l.index[key]
	if !ok {
		g = len(l.groups)
		l.index[key] = g
		l.groups = append(l.groups, &lookupGroup{target: target})
	}
	l.groups[g].sources = append(l.groups[g].sources, source)
	return nil
}

// NumTargets returns the number of distinct targets registered.
func (l *Lookups) NumTargets() int { return len(l.groups) }

// Build adds the lookups to the builder: per target, in the order the
// targets were first registered, its multiplicity column; then the logup
// columns of all the fractions, per module, and their bus.
func (l *Lookups) Build(builder *board.Builder) error {
	return l.build(builder, true)
}

// build is Build, with the targets' tags when tagged (false only to test
// that the tags are what keeps the targets apart).
func (l *Lookups) build(builder *board.Builder, tagged bool) error {
	if len(l.groups) == 0 {
		return nil
	}
	alpha := board.Coin(board.RoundFold)
	gamma := board.Coin(board.RoundLogDerivative)
	minusOne := expr.Const(*new(koalabear.Element).Neg(new(koalabear.Element).SetOne()))
	var terms []board.LogupTerm
	for k, g := range l.groups {
		selS, S := make([]expr.Expr, len(g.sources)), make([]board.Table, len(g.sources))
		for i, s := range g.sources {
			selS[i], S[i] = s.Selector(), s.Table
		}
		selT, T := []expr.Expr{g.target.Selector()}, []board.Table{g.target.Table}
		mult, err := stageLookup(builder, selS, selT, S, T)
		if err != nil {
			return err
		}

		fold := func(t board.Table) expr.Expr {
			cols := t.In
			if tagged {
				cols = append([]expr.Expr{expr.Const(koalabear.NewElement(uint64(k)))}, cols...)
			}
			return expr.Fold(alpha, cols).Sub(gamma)
		}
		for i, s := range S {
			terms = append(terms, board.LogupTerm{Module: s.Module, E: fold(s), M: selS[i]})
		}
		m := expr.Col(constants.MultiplicityChunkName(mult, 0)).Mul(selT[0])
		terms = append(terms, board.LogupTerm{Module: g.target.Module, E: fold(T[0]), M: minusOne.Mul(m)})
	}
	totals, err := AddLogupColumns(builder, fmt.Sprintf("%s_", constants.LOGUP), terms)
	if err != nil {
		return err
	}
	builder.AddLogupBus(board.NewLogupBus(totals))
	return nil
}

// targetKey identifies a target: its module, selector and expressions.
func targetKey(t board.CTable) string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "%s|%s", t.Module, t.Selector().String())
	for _, e := range t.In {
		fmt.Fprintf(&sb, "|%s", e.String())
	}
	return sb.String()
}
