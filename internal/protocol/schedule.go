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
	"github.com/consensys/loom/internal/fri"
)

// CanonicalSchedule bundles the per-batch shift schedule and the parallel
// reverse-name table both prover and verifier need to drive fri.PCS.Open /
// fri.PCS.Verify.
//
// Built deterministically from board.Program and the existing Layout, the
// two sides MUST produce identical CanonicalSchedules: the canonical
// alpha_DEEP binding order depends on it.
type CanonicalSchedule struct {
	// Shifts[b] is the fri.BatchShifts for the b-th batch in the canonical
	// commitment-tree order: setup batches (decreasing N) → trace-round
	// batches → AIR batches (decreasing N). Each trace batch may contain
	// several declaration-order groups in decreasing native size.
	Shifts []fri.BatchShifts

	// Keys is parallel to Shifts. Keys[b][g].Base[i][k] is the list of
	// canonical ValuesAtZeta keys (= leaf.String() forms) that map to
	// the (batch, group, base rail, polyIdx, kth shift) entry.
	//
	// A single normalized shift may correspond to several raw leaf shifts
	// (e.g. raw -1 and raw N-1 both normalize to N-1); each raw shift
	// contributes one canonical key. All keys share the same evaluation
	// value, so when translating fri.OpeningProof.ClaimedValues into a
	// name-keyed ValuesAtZeta map we write the same value under each.
	//
	// For AIR-quotient batches, every chunk is opened only at shift 0
	// and its canonical key is the chunk name itself (no shift suffix);
	// Keys[b][g].Base[i][0] therefore has a single entry equal to the
	// chunk name.
	Keys []BatchKeys

	// ColNamesByTree[b][g].Base[i] is the raw column name (no shift
	// suffix) of the i-th base polynomial in batch b, group g. The
	// prover uses these to look up Lagrange-form polynomials in its
	// trace maps when assembling fri.Batch slices for pcs.Open. For
	// AIR-quotient batches the names ARE the chunk names (since chunks
	// live keyed by chunkName in pr.airTrace).
	ColNamesByTree []BatchNames
}

// BatchNames mirrors fri.BatchShifts: one entry per Group inside the batch.
type BatchNames []GroupNames

// GroupNames carries the per-rail polynomial names for one Group.
type GroupNames struct {
	Base []string
	Ext  []string
}

// BatchKeys mirrors fri.BatchShifts: one entry per Group inside the batch.
type BatchKeys []GroupKeys

// GroupKeys mirrors fri.GroupShifts: per-rail, per-poly, per-shift list of
// canonical ValuesAtZeta keys.
type GroupKeys struct {
	Base [][][]string
	Ext  [][][]string
}

// BuildCanonicalSchedule walks every vanishing relation to learn which
// canonical (leaf.String()) keys live at which shift for each committed
// column, then assembles the per-batch schedule in canonical order using
// the Layout's slot table to invert the column-to-tree mapping.
//
// The function is deterministic in program. AIR-quotient chunks are
// handled separately from trace/setup columns: chunks have no shift
// dimension, so the schedule entry for each chunk is fixed to ([0],
// [chunkName]).
func BuildCanonicalSchedule(program board.Program, layout Layout) CanonicalSchedule {
	leafConfig := expr.NewConfig(
		expr.WithoutChallenges(),
		expr.WithoutVerifierColumns(),
	)

	// 1- For every committed column referenced by some vanishing relation,
	//    collect {normalizedShift -> [canonical keys]}. Two raw shift
	//    values that normalize to the same shift produce two distinct
	//    canonical keys (leaf.String() encodes the raw shift).
	colKeysByShift := make(map[string]map[int][]string)
	moduleNames := make([]string, 0, len(program.Modules))
	for name := range program.Modules {
		moduleNames = append(moduleNames, name)
	}
	sort.Strings(moduleNames)
	for _, mn := range moduleNames {
		m := program.Modules[mn]
		if m.VanishingRelation == nil {
			continue
		}
		N := m.N
		for _, leaf := range m.VanishingRelation.LeavesFull(leafConfig) {
			normalizedShift := 0
			if leaf.Shift != 0 {
				normalizedShift = ((leaf.Shift % N) + N) % N
			}
			key := leaf.String()
			if colKeysByShift[leaf.Name] == nil {
				colKeysByShift[leaf.Name] = make(map[int][]string)
			}
			existing := colKeysByShift[leaf.Name][normalizedShift]
			dup := false
			for _, k := range existing {
				if k == key {
					dup = true
					break
				}
			}
			if !dup {
				colKeysByShift[leaf.Name][normalizedShift] = append(existing, key)
			}
		}
	}

	// 2- Invert layout.ColSlot / layout.AIRChunkSlot into per-tree/per-group rail
	//    lists ordered by Slot.PolyIdx -- the same order the prover commits
	//    polynomials in and that PCS.Open / PCS.Verify use for per-polynomial
	//    DEEP quotient traversal.
	type railList struct {
		base []string
		ext  []string
	}
	railsByTree := make([][]railList, layout.NumTrees)
	for treeIdx := 0; treeIdx < layout.NumTrees; treeIdx++ {
		if treeIdx < len(layout.TreeGroups) {
			railsByTree[treeIdx] = make([]railList, len(layout.TreeGroups[treeIdx]))
		}
	}
	put := func(treeIdx, groupIdx, polyIdx int, f field.Kind, name string) {
		for len(railsByTree[treeIdx]) <= groupIdx {
			railsByTree[treeIdx] = append(railsByTree[treeIdx], railList{})
		}
		rl := &railsByTree[treeIdx][groupIdx]
		switch f {
		case field.Base:
			for len(rl.base) <= polyIdx {
				rl.base = append(rl.base, "")
			}
			rl.base[polyIdx] = name
		case field.Ext:
			for len(rl.ext) <= polyIdx {
				rl.ext = append(rl.ext, "")
			}
			rl.ext[polyIdx] = name
		}
	}
	for colName, slot := range layout.ColSlot {
		put(slot.TreeIdx, slot.GroupIdx, slot.PolyIdx, slot.Field, colName)
	}
	for chunkName, slot := range layout.AIRChunkSlot {
		put(slot.TreeIdx, slot.GroupIdx, slot.PolyIdx, slot.Field, chunkName)
	}

	isAIRTree := func(t int) bool { return t >= layout.AIRBegin && t < layout.AIREnd }

	// 3- For each tree, build the per-group BatchShifts + BatchKeys.
	schedule := CanonicalSchedule{
		Shifts:         make([]fri.BatchShifts, layout.NumTrees),
		Keys:           make([]BatchKeys, layout.NumTrees),
		ColNamesByTree: make([]BatchNames, layout.NumTrees),
	}

	for t := 0; t < layout.NumTrees; t++ {
		treeRails := railsByTree[t]
		schedule.Shifts[t] = make(fri.BatchShifts, len(treeRails))
		schedule.Keys[t] = make(BatchKeys, len(treeRails))
		schedule.ColNamesByTree[t] = make(BatchNames, len(treeRails))

		air := isAIRTree(t)
		fill := func(rail string, names []string, shifts *[][]int, keys *[][][]string) {
			_ = rail
			for i, name := range names {
				if air {
					(*shifts)[i] = []int{0}
					(*keys)[i] = [][]string{{name}}
					continue
				}
				perShift := colKeysByShift[name]
				orderedShifts := make([]int, 0, len(perShift))
				for sh := range perShift {
					orderedShifts = append(orderedShifts, sh)
				}
				sort.Ints(orderedShifts)
				(*shifts)[i] = orderedShifts
				(*keys)[i] = make([][]string, len(orderedShifts))
				for k, sh := range orderedShifts {
					(*keys)[i][k] = perShift[sh]
				}
			}
		}
		for g, rl := range treeRails {
			gs := fri.GroupShifts{
				Base: make([][]int, len(rl.base)),
				Ext:  make([][]int, len(rl.ext)),
			}
			gk := GroupKeys{
				Base: make([][][]string, len(rl.base)),
				Ext:  make([][][]string, len(rl.ext)),
			}
			fill("Base", rl.base, &gs.Base, &gk.Base)
			fill("Ext", rl.ext, &gs.Ext, &gk.Ext)

			schedule.Shifts[t][g] = gs
			schedule.Keys[t][g] = gk
			schedule.ColNamesByTree[t][g] = GroupNames{
				Base: append([]string{}, rl.base...),
				Ext:  append([]string{}, rl.ext...),
			}
		}
	}

	return schedule
}
