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
	"sort"
	"strings"

	"github.com/consensys/loom/board"
	loomfield "github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/protocol"
)

// LeafCost is the per-query leaf hashing work of verifying a loom proof: every
// committed polynomial (setup, trace, logup, AIR-quotient chunk) is opened at
// every query, as one row pair per (tree, group).
type LeafCost struct {
	// Elements is the number of field elements opened per query: 2 per base
	// polynomial and 12 per extension polynomial.
	Elements int
	// Perms is the number of Poseidon2 permutations hashing them: one sponge
	// of 3 + Elements(group) elements per (tree, group).
	Perms int
}

// LeafBreakdown is the per-query leaf elements of one module, by column kind.
type LeafBreakdown struct {
	Module                       string
	Trace, Logup, Mult, Quotient int
}

// Total returns the module's leaf elements per query.
func (l LeafBreakdown) Total() int { return l.Trace + l.Logup + l.Mult + l.Quotient }

// LeafBreakdownOf returns the leaf elements per query of each module, sorted
// by decreasing total.
func LeafBreakdownOf(program board.Program) []LeafBreakdown {
	per := map[string]*LeafBreakdown{}
	get := func(m string) *LeafBreakdown {
		if per[m] == nil {
			per[m] = &LeafBreakdown{Module: m}
		}
		return per[m]
	}
	for _, r := range program.Rounds {
		for _, c := range r.Staged {
			w := 2
			if c.Field == loomfield.Ext {
				w = 12
			}
			l := get(c.Module)
			switch {
			case strings.Contains(c.Name, "logup"):
				l.Logup += w
			case strings.HasPrefix(c.Name, "Mult_"):
				l.Mult += w
			default:
				l.Trace += w
			}
		}
	}
	layout := protocol.BuildLayout(program, 0)
	for name := range layout.AIRChunkSlot {
		get(moduleOf(name)).Quotient += 12
	}
	res := make([]LeafBreakdown, 0, len(per))
	for _, l := range per {
		res = append(res, *l)
	}
	sort.Slice(res, func(i, j int) bool {
		if res[i].Total() != res[j].Total() {
			return res[i].Total() > res[j].Total()
		}
		return res[i].Module < res[j].Module
	})
	return res
}

// LeafCostOf computes the leaf cost of a program whose module sizes are set.
func LeafCostOf(program board.Program) LeafCost {
	layout := protocol.BuildLayout(program, 0)
	type key struct{ tree, group int }
	width := map[key]int{}
	add := func(s protocol.Slot) {
		w := 2
		if s.Field == loomfield.Ext {
			w = 12
		}
		width[key{s.TreeIdx, s.GroupIdx}] += w
	}
	for _, s := range layout.ColSlot {
		add(s)
	}
	for _, s := range layout.AIRChunkSlot {
		add(s)
	}
	var res LeafCost
	for _, w := range width {
		res.Elements += w
		res.Perms += (3 + w + 15) / 16
	}
	return res
}

// moduleOf returns the module of a "module.column" name.
func moduleOf(colName string) string {
	if i := strings.IndexByte(colName, '.'); i >= 0 {
		return colName[:i]
	}
	return ""
}
