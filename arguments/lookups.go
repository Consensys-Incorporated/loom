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

	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

// Lookups collects lookups and builds them grouped by target: the lookups
// into the same target (the same table, selector and module) share one
// multiplicity column, counted over all their sources, and one logup bus, on
// which the sources of a module are batched together. Building each lookup on
// its own (CLookupTuple) would instead add a multiplicity column and a
// target-side fraction per lookup.
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

// Build adds the lookups to the builder, one argument per target, in the
// order the targets were first registered.
func (l *Lookups) Build(builder *board.Builder) error {
	for _, g := range l.groups {
		selS, S := make([]expr.Expr, len(g.sources)), make([]board.Table, len(g.sources))
		for i, s := range g.sources {
			selS[i], S[i] = s.Selector(), s.Table
		}
		selT, T := []expr.Expr{g.target.Selector()}, []board.Table{g.target.Table}
		if err := CLookupUnionTuple(builder, selS, selT, S, T); err != nil {
			return err
		}
	}
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
