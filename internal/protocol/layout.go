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
	"github.com/consensys/loom/expr"
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

// TreeGroup records the native polynomial size of one declaration-order group
// inside a canonical commitment tree.
type TreeGroup struct {
	N int
}

// Layout describes the canonical order of WMerkleTrees produced by the
// prover and consumed by the verifier. Both sides build it from the current
// `program` (so module sizes can be changed via program.SetSize between
// Compile and Prove and the layout adapts).
//
// Tree order (flat):
//
//	[setup (0 or 1 tree)] [trace-round-0] … [trace-round-{r-1}] [AIR, decreasing N]
//
// Each non-empty trace round occupies one tree whose groups are ordered by
// decreasing native size. The setup section occupies at most one tree that
// also uses multiple groups in decreasing-N order. AIR uses one tree per size.
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

	// Per-tree group metadata. Trace and setup trees can contain several
	// groups in decreasing N; AIR trees are single-group.
	TreeGroups [][]TreeGroup

	// Column-name → Slot for trace columns and setup public columns.
	ColSlot map[string]Slot

	// "module.chunkIdx" name → Slot for AIR-quotient chunks.
	AIRChunkSlot map[string]Slot
}

// BuildLayout builds the canonical commitment layout for a Prove/Verify run.
//
// The function is deterministic in `program`; it does not look at the trace.
func BuildLayout(program board.Program, _ int) Layout {
	var layout Layout
	layout.ColSlot = make(map[string]Slot)
	layout.AIRChunkSlot = make(map[string]Slot)

	treeIdx := 0

	// ---- Setup section ----
	// All setup columns across all sizes share a single tree, with one group
	// per distinct native size in decreasing order — mirroring the trace-round
	// multi-group layout.
	layout.SetupBegin = treeIdx
	{
		colsByN := map[int][]board.ColumnRef{}
		for _, c := range program.SetupColumns {
			m, ok := program.Modules[c.Module]
			if !ok {
				continue
			}
			colsByN[m.N] = append(colsByN[m.N], c)
		}
		sizes := sortedSizesDesc(colsByN)
		if len(sizes) > 0 {
			setupTreeIdx := treeIdx
			groups := make([]TreeGroup, len(sizes))
			for groupIdx, N := range sizes {
				groups[groupIdx] = TreeGroup{N: N}
			}
			layout.TreeGroups = append(layout.TreeGroups, groups)
			for groupIdx, N := range sizes {
				cols := colsByN[N]
				sort.Slice(cols, func(i, j int) bool { return cols[i].Name < cols[j].Name })
				railIdx := map[field.Kind]int{}
				for _, col := range cols {
					polyIdx := nextRailPolyIdx(railIdx, col.Field)
					layout.ColSlot[col.Name] = Slot{TreeIdx: setupTreeIdx, GroupIdx: groupIdx, PolyIdx: polyIdx, Field: col.Field}
				}
			}
			treeIdx++
		}
	}
	layout.SetupEnd = treeIdx

	// ---- Trace section, per FS round ----
	numRounds := len(program.Rounds)
	layout.TraceBegin = make([]int, numRounds)
	layout.TraceEnd = make([]int, numRounds)
	for r, round := range program.Rounds {
		deps := round.Staged
		layout.TraceBegin[r] = treeIdx

		// Group dependencies by size, decreasing N. Every non-empty round is
		// committed as a single mixed-size tree, with one group per size.
		// Stable order within a size group matches the dependency order.
		depsByN := map[int][]board.ColumnRef{}
		for _, dep := range deps {
			m, ok := program.Modules[dep.Module]
			if !ok {
				continue
			}
			depsByN[m.N] = append(depsByN[m.N], dep)
		}
		sizes := sortedSizesDesc(depsByN)
		if len(sizes) > 0 {
			roundTreeIdx := treeIdx
			groups := make([]TreeGroup, len(sizes))
			for groupIdx, N := range sizes {
				groups[groupIdx] = TreeGroup{N: N}
			}
			layout.TreeGroups = append(layout.TreeGroups, groups)
			for groupIdx, N := range sizes {
				group := depsByN[N]
				// Preserve iteration order of Rounds[r].Staged within
				// a size by NOT re-sorting here.
				railIdx := map[field.Kind]int{}
				for _, dep := range group {
					polyIdx := nextRailPolyIdx(railIdx, dep.Field)
					layout.ColSlot[dep.Name] = Slot{TreeIdx: roundTreeIdx, GroupIdx: groupIdx, PolyIdx: polyIdx, Field: dep.Field}
				}
			}
			treeIdx++
		}

		layout.TraceEnd[r] = treeIdx
	}

	// ---- AIR section ----
	layout.AIRBegin = treeIdx
	{
		// Modules contributing AIR-quotient chunks: those with non-trivial
		// vanishing relation. Iterate in deterministic name order.
		moduleNames := make([]string, 0, len(program.Modules))
		for name := range program.Modules {
			moduleNames = append(moduleNames, name)
		}
		sort.Strings(moduleNames)

		// chunksByN[N] is the ordered list of (moduleName, chunkIdx) pairs
		// of size N, in (sortedModule × chunkIdx) order — must match
		// ComputeAIRQuotients in the prover.
		type airEntry struct {
			module string
			idx    int
			field  field.Kind
		}
		chunksByN := map[int][]airEntry{}
		for _, moduleName := range moduleNames {
			m := program.Modules[moduleName]
			if m.VanishingRelation == nil || m.VanishingRelation.Degree() <= 0 {
				continue
			}
			N := m.N
			eDeg := m.VanishingRelation.Degree()
			bigSize := poly.NextPowerOfTwo(eDeg * N)
			numChunks := bigSize / N
			f := m.VanishingRelation.Root.Field
			for i := 0; i < numChunks; i++ {
				chunksByN[N] = append(chunksByN[N], airEntry{module: moduleName, idx: i, field: f})
			}
		}
		sizes := sortedSizesDesc(chunksByN)
		for _, N := range sizes {
			railIdx := map[field.Kind]int{}
			for _, e := range chunksByN[N] {
				chunkName := constants.QuotientChunkName(e.module, e.idx)
				polyIdx := nextRailPolyIdx(railIdx, e.field)
				layout.AIRChunkSlot[chunkName] = Slot{TreeIdx: treeIdx, GroupIdx: 0, PolyIdx: polyIdx, Field: e.field}
			}
			layout.TreeGroups = append(layout.TreeGroups, []TreeGroup{{N: N}})
			treeIdx++
		}
	}
	layout.AIREnd = treeIdx

	layout.NumTrees = treeIdx
	return layout
}

func nextRailPolyIdx(counters map[field.Kind]int, f field.Kind) int {
	idx := counters[f]
	counters[f] = idx + 1
	return idx
}

// sortedSizesDesc returns the keys of m sorted in decreasing order.
func sortedSizesDesc[V any](m map[int]V) []int {
	out := make([]int, 0, len(m))
	for n := range m {
		out = append(out, n)
	}
	sort.Sort(sort.Reverse(sort.IntSlice(out)))
	return out
}

// DEEPquotientLayout describes the iteration order used by ComputeDeepQuotient
// (prover) and checkFRIBridge (verifier) when assembling the per-size DEEP
// quotient. The layout is purely metadata — no field values, no tree handles —
// so the same struct can drive both sides.
//
// Phase 1 (vanishing-relation columns): for each size i (decreasing N), and
// each shift j (increasing) at that size, Names[i][j] / Keys[i][j] hold the
// bare column names and their leaf.String() forms (parallel arrays sorted by
// Keys[i][j]). A column referenced by several modules of the same size is
// pooled and dedup'd by leaf.String().
//
// Phase 2 (AIR-quotient chunks): AIRChunks[i] is the ordered list of chunk
// names of size Sizes[i], in canonical (sortedModule × chunkIdx) order.
// Modules from different names of the same size are merged into a single
// accumulate-and-divide step (mathematically equivalent to per-module).
type DEEPquotientLayout struct {
	Sizes  []int        // decreasing N
	Shifts [][]int      // Shifts[i] = shifts at Sizes[i] (increasing)
	Names  [][][]string // Names[i][j] = bare column names at (Sizes[i], Shifts[i][j])
	Keys   [][][]string // Keys[i][j]  = parallel leaf.String() keys (for ValuesAtZeta lookup)

	AIRChunks [][]string // AIRChunks[i] = chunk names of size Sizes[i] in canonical order
}

// BuildDeepQuotientLayout constructs the iteration layout used by both the
// prover's ComputeDeepQuotient and the verifier's checkFRIBridge.
//
// The function is deterministic in `program`. Module sizes can be changed
// between Compile and Prove (via program.SetSize); the layout reflects the
// current sizes.
func BuildDeepQuotientLayout(program board.Program) DEEPquotientLayout {
	leafConfig := expr.NewConfig(
		expr.WithoutChallenges(),
		expr.WithoutVerifierColumns(),
	)

	// Group module names by size, deterministic within a size.
	modulesByN := map[int][]string{}
	for name, m := range program.Modules {
		modulesByN[m.N] = append(modulesByN[m.N], name)
	}
	for _, names := range modulesByN {
		sort.Strings(names)
	}
	sizes := sortedSizesDesc(modulesByN)

	out := DEEPquotientLayout{
		Sizes:     sizes,
		Shifts:    make([][]int, len(sizes)),
		Names:     make([][][]string, len(sizes)),
		Keys:      make([][][]string, len(sizes)),
		AIRChunks: make([][]string, len(sizes)),
	}

	sizeIdx := make(map[int]int, len(sizes))
	for i, N := range sizes {
		sizeIdx[N] = i
	}

	// ---- Phase 1: pool vanishing-relation leaves per size ----
	type colEntry struct{ name, key string }
	for i, N := range sizes {
		byShift := map[int][]colEntry{}
		seenKey := map[string]bool{}
		for _, moduleName := range modulesByN[N] {
			module := program.Modules[moduleName]
			if module.VanishingRelation == nil {
				continue
			}
			for _, leaf := range module.VanishingRelation.LeavesFull(leafConfig) {
				k := leaf.String()
				if seenKey[k] {
					continue
				}
				seenKey[k] = true
				normalizedShift := 0
				if leaf.Shift != 0 {
					normalizedShift = ((leaf.Shift % N) + N) % N
				}
				byShift[normalizedShift] = append(byShift[normalizedShift], colEntry{name: leaf.Name, key: k})
			}
		}

		shifts := make([]int, 0, len(byShift))
		for sh := range byShift {
			shifts = append(shifts, sh)
		}
		sort.Ints(shifts)

		out.Shifts[i] = shifts
		out.Names[i] = make([][]string, len(shifts))
		out.Keys[i] = make([][]string, len(shifts))
		for j, sh := range shifts {
			entries := byShift[sh]
			sort.Slice(entries, func(a, b int) bool { return entries[a].key < entries[b].key })
			names := make([]string, len(entries))
			keys := make([]string, len(entries))
			for k, e := range entries {
				names[k] = e.name
				keys[k] = e.key
			}
			out.Names[i][j] = names
			out.Keys[i][j] = keys
		}
	}

	// ---- Phase 2: AIR chunk names per size, in (sortedModule × chunkIdx) order ----
	moduleNames := make([]string, 0, len(program.Modules))
	for name := range program.Modules {
		moduleNames = append(moduleNames, name)
	}
	sort.Strings(moduleNames)
	for _, moduleName := range moduleNames {
		m := program.Modules[moduleName]
		if m.VanishingRelation == nil || m.VanishingRelation.Degree() <= 0 {
			continue
		}
		N := m.N
		eDeg := m.VanishingRelation.Degree()
		bigSize := poly.NextPowerOfTwo(eDeg * N)
		numChunks := bigSize / N
		i := sizeIdx[N]
		for c := 0; c < numChunks; c++ {
			out.AIRChunks[i] = append(out.AIRChunks[i], constants.QuotientChunkName(moduleName, c))
		}
	}

	return out
}
