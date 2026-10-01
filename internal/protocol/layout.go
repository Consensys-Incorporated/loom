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

package protocol

import (
	"sort"

	"github.com/consensys/loom/board"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/poly"
)

// Slot identifies the position of a single committed polynomial inside the
// flat (canonical) tree array used by the multi-degree commitment scheme.
//
//	TreeIdx = index into the canonical tree order
//	          (setup → trace-round-0 → … → trace-round-{r-1} → AIR)
//	GroupIdx = declaration-order group index inside that tree's fri.Batch
//	PolyIdx  = rail-relative index of this polynomial inside the group's raw leaf entries
//	Field   = rail to read/write inside the tree
type Slot struct {
	TreeIdx  int
	GroupIdx int
	PolyIdx  int
	Field    field.Kind
}

// TreeGroup records the module and native polynomial size of one group
// inside a canonical commitment tree.
type TreeGroup struct {
	Module string
	N      int
}

// Layout describes the canonical order of WMerkleTrees produced by the
// prover and consumed by the verifier. Both sides build it from the current
// `program` (so module sizes can be changed via program.SetSize between
// Compile and Prove and the layout adapts).
//
// Tree order (flat):
//
//	[setup (0 or 1 tree)] [trace-round-0] … [trace-round-{r-1}] [AIR (0 or 1 tree)]
//
// Every tree holds one group per module, in ModuleOrder (sorted module
// names), skipping modules with nothing to commit in it. The structure does
// not depend on which modules share a size: groups of equal size are
// distinct injections of the mixed-height tree (see fri.Commit).
type Layout struct {
	NumTrees int // total number of trees in the canonical order

	// Section boundaries, expressed as tree indices. SectionEnd is one past
	// the last tree of the section.
	SetupBegin int // = 0
	SetupEnd   int
	TraceBegin []int // [round] start of trace round r (== SetupEnd for round 0)
	TraceEnd   []int // [round] end of trace round r
	AIRBegin   int
	AIREnd     int // = NumTrees

	// Per-tree group metadata, one group per module in ModuleOrder.
	TreeGroups [][]TreeGroup

	// Column-name → Slot for trace columns and setup public columns.
	ColSlot map[string]Slot

	// "module.chunkIdx" name → Slot for AIR-quotient chunks.
	AIRChunkSlot map[string]Slot

	// Modules is ModuleOrder(program).
	Modules []string
}

// DeepClasses returns, for every tree and group, the index of the group's
// module in Modules: the DEEP class of the group (fri.WithDeepClasses), so
// that the PCS builds one DEEP quotient per module, in module order.
func (l Layout) DeepClasses() [][]int {
	index := make(map[string]int, len(l.Modules))
	for i, m := range l.Modules {
		index[m] = i
	}
	res := make([][]int, len(l.TreeGroups))
	for t, groups := range l.TreeGroups {
		res[t] = make([]int, len(groups))
		for g, group := range groups {
			res[t][g] = index[group.Module]
		}
	}
	return res
}

// ModuleOrder returns the canonical module order of the commitment layout:
// the sorted module names.
func ModuleOrder(program board.Program) []string {
	names := make([]string, 0, len(program.Modules))
	for name := range program.Modules {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

// SetupGroups returns the setup columns grouped by module, in ModuleOrder,
// sorted by name within a module: the groups of the setup tree. Modules
// without setup columns are skipped.
func SetupGroups(program board.Program) [][]board.ColumnRef {
	byModule := map[string][]board.ColumnRef{}
	for _, c := range program.SetupColumns {
		if _, ok := program.Modules[c.Module]; ok {
			byModule[c.Module] = append(byModule[c.Module], c)
		}
	}
	var res [][]board.ColumnRef
	for _, m := range ModuleOrder(program) {
		cols := byModule[m]
		if len(cols) == 0 {
			continue
		}
		sort.Slice(cols, func(i, j int) bool { return cols[i].Name < cols[j].Name })
		res = append(res, cols)
	}
	return res
}

// AIRChunkCount returns the number of AIR-quotient chunks of a module, 0 if
// its vanishing relation is trivial.
func AIRChunkCount(m board.CompiledModule) int {
	if m.VanishingRelation == nil || m.VanishingRelation.Degree() <= 0 {
		return 0
	}
	return poly.NextPowerOfTwo(m.VanishingRelation.Degree()*m.N) / m.N
}

// BuildLayout builds the canonical commitment layout for a Prove/Verify run.
//
// The function is deterministic in `program`; it does not look at the trace.
func BuildLayout(program board.Program, _ int) Layout {
	var layout Layout
	layout.ColSlot = make(map[string]Slot)
	layout.AIRChunkSlot = make(map[string]Slot)
	order := ModuleOrder(program)
	layout.Modules = order

	treeIdx := 0
	// addTree appends a tree whose groups are the non-empty column lists of
	// byModule, in module order, and assigns their slots via assign.
	addTree := func(byModule map[string][]board.ColumnRef, assign func(name string, s Slot)) {
		var groups []TreeGroup
		for _, m := range order {
			cols := byModule[m]
			if len(cols) == 0 {
				continue
			}
			groupIdx := len(groups)
			groups = append(groups, TreeGroup{Module: m, N: program.Modules[m].N})
			railIdx := map[field.Kind]int{}
			for _, c := range cols {
				polyIdx := nextRailPolyIdx(railIdx, c.Field)
				assign(c.Name, Slot{TreeIdx: treeIdx, GroupIdx: groupIdx, PolyIdx: polyIdx, Field: c.Field})
			}
		}
		if len(groups) == 0 {
			return
		}
		layout.TreeGroups = append(layout.TreeGroups, groups)
		treeIdx++
	}
	colSlot := func(name string, s Slot) { layout.ColSlot[name] = s }

	// ---- Setup section: one tree, one group per module ----
	layout.SetupBegin = treeIdx
	setupByModule := map[string][]board.ColumnRef{}
	for _, cols := range SetupGroups(program) {
		setupByModule[cols[0].Module] = cols
	}
	addTree(setupByModule, colSlot)
	layout.SetupEnd = treeIdx

	// ---- Trace section: one tree per FS round, one group per module ----
	// Within a module, columns keep the order of Rounds[r].Staged.
	numRounds := len(program.Rounds)
	layout.TraceBegin = make([]int, numRounds)
	layout.TraceEnd = make([]int, numRounds)
	for r, round := range program.Rounds {
		layout.TraceBegin[r] = treeIdx
		byModule := map[string][]board.ColumnRef{}
		for _, dep := range round.Staged {
			if _, ok := program.Modules[dep.Module]; ok {
				byModule[dep.Module] = append(byModule[dep.Module], dep)
			}
		}
		addTree(byModule, colSlot)
		layout.TraceEnd[r] = treeIdx
	}

	// ---- AIR section: one tree, one group per module, chunks in order ----
	// Must match the chunks computed by ComputeAIRQuotients in the prover.
	layout.AIRBegin = treeIdx
	airByModule := map[string][]board.ColumnRef{}
	for _, name := range order {
		m := program.Modules[name]
		for i := range AIRChunkCount(m) {
			airByModule[name] = append(airByModule[name], board.ColumnRef{
				Name: constants.QuotientChunkName(name, i), Module: name, Field: m.VanishingRelation.Root.Field,
			})
		}
	}
	addTree(airByModule, func(name string, s Slot) { layout.AIRChunkSlot[name] = s })
	layout.AIREnd = treeIdx

	layout.NumTrees = treeIdx
	return layout
}

func nextRailPolyIdx(counters map[field.Kind]int, f field.Kind) int {
	idx := counters[f]
	counters[f] = idx + 1
	return idx
}
