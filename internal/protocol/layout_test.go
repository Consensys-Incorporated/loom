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
	"reflect"
	"testing"

	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/dag"
)

// TestBuildLayoutBaseOnlySlotStability locks in the concrete (TreeIdx,
// PolyIdx, Field) assignments for a base-only program. PR8 adds Slot.Field and
// rail-relative PolyIdx values, but it must not shift existing base-only
// TreeIdx/PolyIdx assignments.
func TestBuildLayoutBaseOnlySlotStability(t *testing.T) {
	builder := board.NewBuilder()

	m := board.NewModule("m")
	m.N = 8
	mulChunk := constants.MultiplicityChunkName("mul", 0)
	// (((z + mul_0) + s) + t).LeavesFull = [z, mul_0, s, t].
	rel := expr.Col("z").Add(expr.Col(mulChunk)).
		Add(expr.Col("s")).
		Add(expr.Col("t")).
		Add(expr.Setup("pz")).
		Add(expr.Setup("pa")).
		Add(expr.Setup("pm"))
	m.AssertZero(rel)
	builder.AddModule(m)

	// The multiplicity step stays in the base field; it does not depend on a
	// Fiat-Shamir challenge.
	builder.AddLookupMultiplicityStep(board.RoundFold, nil, nil,
		[][]expr.Expr{{expr.Col("s")}},
		[][]expr.Expr{{expr.Col("t")}},
		"mul",
	)

	program, err := board.Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}

	layout := BuildLayout(program, 1)

	wantColSlot := map[string]Slot{
		// Setup section (TreeIdx=0): setup columns sorted by name.
		"pa": {TreeIdx: 0, GroupIdx: 0, PolyIdx: 0, Field: field.Base},
		"pm": {TreeIdx: 0, GroupIdx: 0, PolyIdx: 1, Field: field.Base},
		"pz": {TreeIdx: 0, GroupIdx: 0, PolyIdx: 2, Field: field.Base},
		// Trace round 0 (TreeIdx=1): unstaged columns are swept in name order.
		mulChunk: {TreeIdx: 1, GroupIdx: 0, PolyIdx: 0, Field: field.Base},
		"s":      {TreeIdx: 1, GroupIdx: 0, PolyIdx: 1, Field: field.Base},
		"t":      {TreeIdx: 1, GroupIdx: 0, PolyIdx: 2, Field: field.Base},
		"z":      {TreeIdx: 1, GroupIdx: 0, PolyIdx: 3, Field: field.Base},
	}
	for name, want := range wantColSlot {
		got, ok := layout.ColSlot[name]
		if !ok {
			t.Fatalf("ColSlot[%q] missing", name)
		}
		if got != want {
			t.Errorf("ColSlot[%q] = %+v, want %+v", name, got, want)
		}
	}
	if len(layout.ColSlot) != len(wantColSlot) {
		t.Errorf("ColSlot has %d entries, want %d (extras: %v)",
			len(layout.ColSlot), len(wantColSlot), extraSlotKeys(layout.ColSlot, wantColSlot))
	}

	wantAIRSlot := map[string]Slot{
		constants.QuotientChunkName("m", 0): {TreeIdx: 2, GroupIdx: 0, PolyIdx: 0, Field: field.Base},
	}
	for name, want := range wantAIRSlot {
		got, ok := layout.AIRChunkSlot[name]
		if !ok {
			t.Fatalf("AIRChunkSlot[%q] missing", name)
		}
		if got != want {
			t.Errorf("AIRChunkSlot[%q] = %+v, want %+v", name, got, want)
		}
	}
	if len(layout.AIRChunkSlot) != len(wantAIRSlot) {
		t.Errorf("AIRChunkSlot has %d entries, want %d",
			len(layout.AIRChunkSlot), len(wantAIRSlot))
	}

	if got := layout.NumTrees; got != 3 {
		t.Errorf("NumTrees = %d, want 3", got)
	}
	if wantTreeGroups := [][]TreeGroup{{{Module: "m", N: 8}}, {{Module: "m", N: 8}}, {{Module: "m", N: 8}}}; !reflect.DeepEqual(layout.TreeGroups, wantTreeGroups) {
		t.Errorf("TreeGroups = %v, want %v", layout.TreeGroups, wantTreeGroups)
	}
	if got := layout.SetupEnd - layout.SetupBegin; got != 1 {
		t.Errorf("setup section has %d trees, want 1", got)
	}
	if len(layout.TraceBegin) != 1 || len(layout.TraceEnd) != 1 {
		t.Fatalf("trace section has %d round(s), want 1", len(layout.TraceBegin))
	}
	if got := layout.TraceEnd[0] - layout.TraceBegin[0]; got != 1 {
		t.Errorf("trace round 0 has %d trees, want 1", got)
	}
	if got := layout.AIREnd - layout.AIRBegin; got != 1 {
		t.Errorf("AIR section has %d trees, want 1", got)
	}
}

func TestBuildLayoutMixedSizeSetupUsesSingleTree(t *testing.T) {
	program := board.Program{
		Modules: map[string]board.CompiledModule{
			"big":   {Name: "big", N: 8},
			"small": {Name: "small", N: 4},
		},
		SetupColumns: []board.ColumnRef{
			{Name: "pb", Module: "big", Field: field.Base},
			{Name: "ps", Module: "small", Field: field.Base},
		},
	}

	layout := BuildLayout(program, 0)

	if got := layout.SetupEnd - layout.SetupBegin; got != 1 {
		t.Fatalf("setup section has %d trees, want 1", got)
	}
	if got := layout.NumTrees; got != 1 {
		t.Fatalf("NumTrees = %d, want 1", got)
	}
	if want := [][]TreeGroup{{{Module: "big", N: 8}, {Module: "small", N: 4}}}; !reflect.DeepEqual(layout.TreeGroups, want) {
		t.Errorf("TreeGroups = %v, want %v", layout.TreeGroups, want)
	}

	wantColSlot := map[string]Slot{
		"pb": {TreeIdx: 0, GroupIdx: 0, PolyIdx: 0, Field: field.Base},
		"ps": {TreeIdx: 0, GroupIdx: 1, PolyIdx: 0, Field: field.Base},
	}
	for name, want := range wantColSlot {
		got, ok := layout.ColSlot[name]
		if !ok {
			t.Fatalf("ColSlot[%q] missing", name)
		}
		if got != want {
			t.Errorf("ColSlot[%q] = %+v, want %+v", name, got, want)
		}
	}
}

// Two modules of the same size get one group each, and PolyIdx is relative to
// the rail within a group.
func TestBuildLayoutRailRelativePolyIdx(t *testing.T) {
	baseRelation := dag.ExprToDAG(expr.Col("base_air"))
	extRelation := dag.ExprToDAG(expr.ExtCol("ext_air"))
	program := board.Program{
		Modules: map[string]board.CompiledModule{
			"base": {Name: "base", N: 8, VanishingRelation: baseRelation},
			"ext":  {Name: "ext", N: 8, VanishingRelation: extRelation},
		},
		Rounds: roundsOf([][]board.ColumnRef{
			{
				{Name: "base_0", Module: "base", Field: field.Base},
				{Name: "ext_0", Module: "ext", Field: field.Ext},
				{Name: "base_1", Module: "base", Field: field.Base},
				{Name: "ext_1", Module: "ext", Field: field.Ext},
			},
		}),
	}

	layout := BuildLayout(program, 0)

	wantColSlot := map[string]Slot{
		"base_0": {TreeIdx: 0, GroupIdx: 0, PolyIdx: 0, Field: field.Base},
		"base_1": {TreeIdx: 0, GroupIdx: 0, PolyIdx: 1, Field: field.Base},
		"ext_0":  {TreeIdx: 0, GroupIdx: 1, PolyIdx: 0, Field: field.Ext},
		"ext_1":  {TreeIdx: 0, GroupIdx: 1, PolyIdx: 1, Field: field.Ext},
	}
	for name, want := range wantColSlot {
		if got := layout.ColSlot[name]; got != want {
			t.Errorf("ColSlot[%q] = %+v, want %+v", name, got, want)
		}
	}

	wantAIRSlot := map[string]Slot{
		constants.QuotientChunkName("base", 0): {TreeIdx: 1, GroupIdx: 0, PolyIdx: 0, Field: field.Base},
		constants.QuotientChunkName("ext", 0):  {TreeIdx: 1, GroupIdx: 1, PolyIdx: 0, Field: field.Ext},
	}
	for name, want := range wantAIRSlot {
		if got := layout.AIRChunkSlot[name]; got != want {
			t.Errorf("AIRChunkSlot[%q] = %+v, want %+v", name, got, want)
		}
	}

	if wantTreeGroups := [][]TreeGroup{{{Module: "base", N: 8}, {Module: "ext", N: 8}}, {{Module: "base", N: 8}, {Module: "ext", N: 8}}}; !reflect.DeepEqual(layout.TreeGroups, wantTreeGroups) {
		t.Errorf("TreeGroups = %v, want %v", layout.TreeGroups, wantTreeGroups)
	}
}

func TestBuildLayoutMixedSizeTraceRoundUsesSingleTree(t *testing.T) {
	program := board.Program{
		Modules: map[string]board.CompiledModule{
			"big":   {Name: "big", N: 8},
			"small": {Name: "small", N: 4},
		},
		Rounds: roundsOf([][]board.ColumnRef{
			{
				{Name: "small_0", Module: "small", Field: field.Base},
				{Name: "big_0", Module: "big", Field: field.Base},
				{Name: "small_ext", Module: "small", Field: field.Ext},
				{Name: "big_1", Module: "big", Field: field.Base},
			},
		}),
	}

	layout := BuildLayout(program, 0)

	if got := layout.NumTrees; got != 1 {
		t.Fatalf("NumTrees = %d, want 1", got)
	}
	if got := layout.TraceEnd[0] - layout.TraceBegin[0]; got != 1 {
		t.Fatalf("trace round 0 has %d trees, want 1", got)
	}
	if wantTreeGroups := [][]TreeGroup{{{Module: "big", N: 8}, {Module: "small", N: 4}}}; !reflect.DeepEqual(layout.TreeGroups, wantTreeGroups) {
		t.Errorf("TreeGroups = %v, want %v", layout.TreeGroups, wantTreeGroups)
	}

	wantColSlot := map[string]Slot{
		"big_0":     {TreeIdx: 0, GroupIdx: 0, PolyIdx: 0, Field: field.Base},
		"big_1":     {TreeIdx: 0, GroupIdx: 0, PolyIdx: 1, Field: field.Base},
		"small_0":   {TreeIdx: 0, GroupIdx: 1, PolyIdx: 0, Field: field.Base},
		"small_ext": {TreeIdx: 0, GroupIdx: 1, PolyIdx: 0, Field: field.Ext},
	}
	for name, want := range wantColSlot {
		if got := layout.ColSlot[name]; got != want {
			t.Errorf("ColSlot[%q] = %+v, want %+v", name, got, want)
		}
	}
}

func TestBuildCanonicalScheduleMixedTraceGroupsMatchLayout(t *testing.T) {
	program := board.Program{
		Modules: map[string]board.CompiledModule{
			"big": {
				Name: "big",
				N:    8,
				VanishingRelation: dag.ExprToDAG(
					expr.Col("big_0").Add(expr.Col("big_1", expr.WithShift(1))),
				),
			},
			"small": {
				Name: "small",
				N:    4,
				VanishingRelation: dag.ExprToDAG(
					expr.Col("small_0", expr.WithShift(-1)).Add(expr.ExtCol("small_ext")),
				),
			},
		},
		Rounds: roundsOf([][]board.ColumnRef{
			{
				{Name: "small_0", Module: "small", Field: field.Base},
				{Name: "big_0", Module: "big", Field: field.Base},
				{Name: "small_ext", Module: "small", Field: field.Ext},
				{Name: "big_1", Module: "big", Field: field.Base},
			},
		}),
	}

	layout := BuildLayout(program, 0)
	treeIdx := layout.TraceBegin[0]
	schedule := BuildCanonicalSchedule(program, layout)

	if got := layout.TraceEnd[0] - layout.TraceBegin[0]; got != 1 {
		t.Fatalf("trace round 0 has %d trees, want 1", got)
	}
	if want := []TreeGroup{{Module: "big", N: 8}, {Module: "small", N: 4}}; !reflect.DeepEqual(layout.TreeGroups[treeIdx], want) {
		t.Fatalf("trace TreeGroups = %v, want %v", layout.TreeGroups[treeIdx], want)
	}
	if got, want := len(schedule.Shifts[treeIdx]), len(layout.TreeGroups[treeIdx]); got != want {
		t.Fatalf("schedule.Shifts[%d] has %d groups, want %d", treeIdx, got, want)
	}
	if got, want := len(schedule.ColNamesByTree[treeIdx]), len(layout.TreeGroups[treeIdx]); got != want {
		t.Fatalf("schedule.ColNamesByTree[%d] has %d groups, want %d", treeIdx, got, want)
	}

	if got := schedule.ColNamesByTree[treeIdx][0].Base; !reflect.DeepEqual(got, []string{"big_0", "big_1"}) {
		t.Fatalf("group 0 base names = %v, want [big_0 big_1]", got)
	}
	if got := schedule.ColNamesByTree[treeIdx][1].Base; !reflect.DeepEqual(got, []string{"small_0"}) {
		t.Fatalf("group 1 base names = %v, want [small_0]", got)
	}
	if got := schedule.ColNamesByTree[treeIdx][1].Ext; !reflect.DeepEqual(got, []string{"small_ext"}) {
		t.Fatalf("group 1 ext names = %v, want [small_ext]", got)
	}
	if got := schedule.Shifts[treeIdx][0].Base; !reflect.DeepEqual(got, [][]int{{0}, {1}}) {
		t.Fatalf("group 0 base shifts = %v, want [[0] [1]]", got)
	}
	if got := schedule.Shifts[treeIdx][1].Base; !reflect.DeepEqual(got, [][]int{{3}}) {
		t.Fatalf("group 1 base shifts = %v, want [[3]]", got)
	}
	if got := schedule.Shifts[treeIdx][1].Ext; !reflect.DeepEqual(got, [][]int{{0}}) {
		t.Fatalf("group 1 ext shifts = %v, want [[0]]", got)
	}
}

func TestBuildCanonicalScheduleSupportsMultipleGroupsPerTree(t *testing.T) {
	layout := Layout{
		NumTrees:   1,
		AIRBegin:   0,
		AIREnd:     1,
		TreeGroups: [][]TreeGroup{{{N: 8}, {N: 4}}},
		ColSlot:    map[string]Slot{},
		AIRChunkSlot: map[string]Slot{
			"g0_base": {TreeIdx: 0, GroupIdx: 0, PolyIdx: 0, Field: field.Base},
			"g1_base": {TreeIdx: 0, GroupIdx: 1, PolyIdx: 0, Field: field.Base},
			"g1_ext":  {TreeIdx: 0, GroupIdx: 1, PolyIdx: 0, Field: field.Ext},
		},
	}

	schedule := BuildCanonicalSchedule(board.Program{
		Modules: map[string]board.CompiledModule{},
	}, layout)

	if got := len(schedule.Shifts); got != 1 {
		t.Fatalf("Shifts has %d trees, want 1", got)
	}
	if got := len(schedule.Shifts[0]); got != 2 {
		t.Fatalf("Shifts[0] has %d groups, want 2", got)
	}
	if got := schedule.ColNamesByTree[0][0].Base; !reflect.DeepEqual(got, []string{"g0_base"}) {
		t.Fatalf("group 0 base names = %v, want [g0_base]", got)
	}
	if got := schedule.ColNamesByTree[0][1].Base; !reflect.DeepEqual(got, []string{"g1_base"}) {
		t.Fatalf("group 1 base names = %v, want [g1_base]", got)
	}
	if got := schedule.ColNamesByTree[0][1].Ext; !reflect.DeepEqual(got, []string{"g1_ext"}) {
		t.Fatalf("group 1 ext names = %v, want [g1_ext]", got)
	}
	if got := schedule.Shifts[0][0].Base; !reflect.DeepEqual(got, [][]int{{0}}) {
		t.Fatalf("group 0 base shifts = %v, want [[0]]", got)
	}
	if got := schedule.Shifts[0][1].Base; !reflect.DeepEqual(got, [][]int{{0}}) {
		t.Fatalf("group 1 base shifts = %v, want [[0]]", got)
	}
	if got := schedule.Shifts[0][1].Ext; !reflect.DeepEqual(got, [][]int{{0}}) {
		t.Fatalf("group 1 ext shifts = %v, want [[0]]", got)
	}
	if got := schedule.Keys[0][1].Ext; !reflect.DeepEqual(got, [][][]string{{{"g1_ext"}}}) {
		t.Fatalf("group 1 ext keys = %v, want [[[g1_ext]]]", got)
	}
}

func extraSlotKeys(got, want map[string]Slot) []string {
	var out []string
	for k := range got {
		if _, ok := want[k]; !ok {
			out = append(out, k)
		}
	}
	return out
}

// roundsOf builds rounds staging the given columns, one round per entry.
func roundsOf(staged [][]board.ColumnRef) []board.ProverRound {
	res := make([]board.ProverRound, len(staged))
	for r, cols := range staged {
		res[r].Staged = cols
	}
	return res
}

// The groups of a tree follow the module names, not their sizes: the layout
// does not change when module sizes change.
func TestBuildLayoutGroupsFollowModuleOrder(t *testing.T) {
	cols := [][]board.ColumnRef{{
		{Name: "z_0", Module: "z", Field: field.Base},
		{Name: "a_0", Module: "a", Field: field.Base},
		{Name: "m_0", Module: "m", Field: field.Base},
	}}
	for _, sizes := range [][3]int{{4, 8, 16}, {16, 8, 4}, {8, 8, 8}} {
		program := board.Program{
			Modules: map[string]board.CompiledModule{
				"a": {Name: "a", N: sizes[0]},
				"m": {Name: "m", N: sizes[1]},
				"z": {Name: "z", N: sizes[2]},
			},
			Rounds: roundsOf(cols),
		}
		layout := BuildLayout(program, 0)
		want := [][]TreeGroup{{{Module: "a", N: sizes[0]}, {Module: "m", N: sizes[1]}, {Module: "z", N: sizes[2]}}}
		if !reflect.DeepEqual(layout.TreeGroups, want) {
			t.Errorf("sizes %v: TreeGroups = %v, want %v", sizes, layout.TreeGroups, want)
		}
		for g, name := range []string{"a_0", "m_0", "z_0"} {
			if got := layout.ColSlot[name].GroupIdx; got != g {
				t.Errorf("sizes %v: ColSlot[%q].GroupIdx = %d, want %d", sizes, name, got, g)
			}
		}
	}
}

// The module sizes bound to the transcript follow the module order and
// change with any module's size.
func TestModuleSizesTranscript(t *testing.T) {
	program := func(a, b int) board.Program {
		return board.Program{Modules: map[string]board.CompiledModule{
			"b": {Name: "b", N: b},
			"a": {Name: "a", N: a},
		}}
	}
	got := ModuleSizesTranscript(program(8, 16))
	want := []uint64{constants.MODULE_SIZES_DOMAIN_TAG, 2, 8, 16}
	if len(got) != len(want) {
		t.Fatalf("got %d elements, want %d", len(got), len(want))
	}
	for i := range want {
		if got[i].Uint64() != want[i] {
			t.Fatalf("element %d = %d, want %d", i, got[i].Uint64(), want[i])
		}
	}
	if reflect.DeepEqual(ModuleSizesTranscript(program(8, 16)), ModuleSizesTranscript(program(16, 8))) {
		t.Fatal("swapping the module sizes does not change the transcript")
	}
}
