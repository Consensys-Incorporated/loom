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

package arguments_test

import (
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"
)

// column returns the single-column table module.c, selected by sel (nil:
// every row).
func column(module, c string, sel expr.Expr) board.CTable {
	return board.CTable{Table: board.Table{Module: module, In: []expr.Expr{expr.Col(module + "." + c)}}, Sel: sel}
}

// countStaged returns the number of staged columns whose name contains sub.
func countStaged(pg board.Program, sub string) int {
	res := 0
	for _, r := range pg.Rounds {
		for _, c := range r.Staged {
			if strings.Contains(c.Name, sub) {
				res++
			}
		}
	}
	return res
}

// sharedTargetProgram looks up a.s0, a.s1 and b.s, three lookups, into the
// table tab.t, registered with the collector when grouped, built one by one
// otherwise.
func sharedTargetProgram(t *testing.T, grouped bool) board.Program {
	t.Helper()
	b := board.NewBuilder()
	for _, name := range []string{"a", "b", "tab"} {
		m := board.NewModule(name)
		m.N = n
		b.AddModule(m)
	}
	tab := column("tab", "t", nil)
	sources := []board.CTable{column("a", "s0", nil), column("a", "s1", nil), column("b", "s", nil)}
	if grouped {
		l := arguments.NewLookups()
		for _, s := range sources {
			if err := l.Add(s, tab); err != nil {
				t.Fatal(err)
			}
		}
		if l.NumTargets() != 1 {
			t.Fatalf("%d targets, want 1", l.NumTargets())
		}
		if err := l.Build(&b); err != nil {
			t.Fatal(err)
		}
	} else {
		for _, s := range sources {
			if err := arguments.LookupTuple(&b, s.Table, tab.Table); err != nil {
				t.Fatal(err)
			}
		}
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}
	return pg
}

func sharedTargetTrace(bad bool) trace.Trace {
	col := func(f func(i int) uint64) []koalabear.Element {
		res := make([]koalabear.Element, n)
		for i := range res {
			res[i].SetUint64(f(i))
		}
		return res
	}
	tr := trace.New()
	tr.SetBase("tab.t", col(func(i int) uint64 { return uint64(i) }))
	tr.SetBase("a.s0", col(func(i int) uint64 { return uint64(i / 2) }))
	tr.SetBase("a.s1", col(func(i int) uint64 { return uint64(n - 1 - i) }))
	tr.SetBase("b.s", col(func(i int) uint64 {
		if bad && i == 3 {
			return 100 // not in the table
		}
		return 5
	}))
	return tr
}

// TestLookupsShareTarget: three lookups into one table share one multiplicity
// column and one bus, whose logup columns batch the two sources of module a.
func TestLookupsShareTarget(t *testing.T) {
	pg := sharedTargetProgram(t, true)
	if got := countStaged(pg, "Mult_"); got != 1 {
		t.Fatalf("%d multiplicity columns, want 1", got)
	}
	if len(pg.LogupBus) != 1 || len(pg.LogupBus[0].Totals) != 3 {
		t.Fatalf("got buses %v, want one bus with 3 totals (a, b, tab)", pg.LogupBus)
	}
	// built one by one: a multiplicity column and a bus per lookup
	if got := countStaged(sharedTargetProgram(t, false), "Mult_"); got != 3 {
		t.Fatalf("ungrouped: %d multiplicity columns, want 3", got)
	}

	st, prf, err := prove(t, pg, sharedTargetTrace(false))
	if err != nil {
		t.Fatal(err)
	}
	if err := loom.Verify(st, prf); err != nil {
		t.Fatalf("valid proof rejected: %v", err)
	}
	st, prf, err = prove(t, pg, sharedTargetTrace(true))
	if err == nil && loom.Verify(st, prf) == nil {
		t.Fatal("lookup of a value outside the table accepted")
	}
}

// TestLookupsTargetKey: lookups are grouped by the whole target, its table,
// module and selector: another selector or another table is another target.
// A source and a target of different widths are refused.
func TestLookupsTargetKey(t *testing.T) {
	s := column("a", "s", nil)
	t1, t2 := column("tab", "t1", nil), column("tab", "t2", nil)
	t1sel := column("tab", "t1", expr.Col("tab.sel"))
	l := arguments.NewLookups()
	for _, target := range []board.CTable{t1, t1, t1sel, t2, t1sel} {
		if err := l.Add(s, target); err != nil {
			t.Fatal(err)
		}
	}
	if got := l.NumTargets(); got != 3 {
		t.Fatalf("%d targets, want 3", got)
	}
	wide := board.CTable{Table: board.Table{Module: "tab", In: []expr.Expr{expr.Col("tab.t1"), expr.Col("tab.t2")}}}
	if err := l.Add(s, wide); err == nil {
		t.Fatal("a source of width 1 into a target of width 2 accepted")
	}
}

// TestLookupsSelectors: selected sources into a selected target, with a
// second lookup into the same target, prove; a selected source outside the
// selected target rows is rejected.
func TestLookupsSelectors(t *testing.T) {
	b := board.NewBuilder()
	for _, name := range []string{"a", "tab"} {
		m := board.NewModule(name)
		m.N = n
		b.AddModule(m)
	}
	l := arguments.NewLookups()
	tab := column("tab", "t", expr.Col("tab.sel"))
	for _, c := range []string{"s0", "s1"} {
		if err := l.Add(column("a", c, expr.Col("a.sel"+c)), tab); err != nil {
			t.Fatal(err)
		}
	}
	if err := l.Build(&b); err != nil {
		t.Fatal(err)
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}
	if got := countStaged(pg, "Mult_"); got != 1 {
		t.Fatalf("%d multiplicity columns, want 1", got)
	}
	col := func(v ...uint64) []koalabear.Element {
		res := make([]koalabear.Element, n)
		for i, x := range v {
			res[i].SetUint64(x)
		}
		return res
	}
	for _, bad := range []bool{false, true} {
		tr := trace.New()
		// the table selects 10, 11, 12 (row 3, 13, is not selected)
		tr.SetBase("tab.t", col(10, 11, 12, 13))
		tr.SetBase("tab.sel", col(1, 1, 1, 0))
		// unselected source rows may hold anything
		tr.SetBase("a.s0", col(10, 99, 12, 12))
		tr.SetBase("a.sels0", col(1, 0, 1, 1))
		last := uint64(11)
		if bad {
			last = 13 // in the table, but not selected
		}
		tr.SetBase("a.s1", col(11, 77, last))
		tr.SetBase("a.sels1", col(1, 0, 1))
		st, prf, err := prove(t, pg, tr)
		if bad {
			if err == nil && loom.Verify(st, prf) == nil {
				t.Fatal("lookup of an unselected target row accepted")
			}
			continue
		}
		if err != nil {
			t.Fatal(err)
		}
		if err := loom.Verify(st, prf); err != nil {
			t.Fatalf("valid proof rejected: %v", err)
		}
	}
}
