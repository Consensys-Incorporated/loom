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
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/trace"
)

// TestBus: module "a" sends (x, y) on its selected rows, module "b" receives
// them on its selected rows, in another order. Unbalancing the bus by one
// message is rejected.
func TestBus(t *testing.T) {
	b := board.NewBuilder()
	for _, name := range []string{"a", "b"} {
		m := board.NewModule(name)
		m.N = n
		b.AddModule(m)
	}
	table := func(module string) board.Table {
		t := board.NewTable(module, 2)
		t.In[0], t.In[1] = expr.Col(module+".x"), expr.Col(module+".y")
		return t
	}
	if err := arguments.Bus(&b,
		[]expr.Expr{expr.Col("a.sel")}, []expr.Expr{expr.Col("b.sel")},
		[]board.Table{table("a")}, []board.Table{table("b")}); err != nil {
		t.Fatal(err)
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}

	col := func(v ...uint64) []koalabear.Element {
		res := make([]koalabear.Element, n)
		for i, x := range v {
			res[i].SetUint64(x)
		}
		return res
	}
	build := func(bad bool) trace.Trace {
		tr := trace.New()
		// a sends (1,10), (2,20), (2,20) and (3,30); its row 4 is not selected
		tr.SetBase("a.x", col(1, 2, 2, 3, 9))
		tr.SetBase("a.y", col(10, 20, 20, 30, 90))
		tr.SetBase("a.sel", col(1, 1, 1, 1, 0))
		// b receives (3,30), (2,20) twice, and (1,10); its row 2 is not selected
		last := uint64(10)
		if bad {
			last = 11
		}
		tr.SetBase("b.x", col(3, 2, 7, 2, 1))
		tr.SetBase("b.y", col(30, 20, 70, 20, last))
		tr.SetBase("b.sel", col(1, 1, 0, 1, 1))
		return tr
	}
	for _, bad := range []bool{false, true} {
		st, prf, err := prove(t, pg, build(bad))
		if bad {
			if err == nil && loom.Verify(st, prf) == nil {
				t.Fatal("unbalanced bus accepted")
			}
			continue
		}
		if err != nil {
			t.Fatal(err)
		}
		if err := loom.Verify(st, prf); err != nil {
			t.Fatalf("balanced bus rejected: %v", err)
		}
		// each running-ratio end is bound: changing one is rejected
		for _, name := range pg.ProductBus[0].Ends {
			bad := prf
			bad.ExposedValues = make(proof.ExposedValues, len(prf.ExposedValues))
			for k, v := range prf.ExposedValues {
				bad.ExposedValues[k] = v
			}
			e := prf.ExposedValues[name].Entries[0]
			v := e.ExtValue()
			v.B0.A0.Add(&v.B0.A0, new(koalabear.Element).SetOne())
			e.SetExt(v)
			bad.ExposedValues[name] = proof.ExposedValue{Entries: []proof.ExposedEntry{e}}
			if err := loom.Verify(st, bad); err == nil {
				t.Fatalf("tampered running-ratio end %s accepted", name)
			}
		}
	}
}

// TestBusSameModule: one module sends x on its selected rows and receives y on
// others, in one running-ratio column (a numerator and a denominator).
func TestBusSameModule(t *testing.T) {
	b := board.NewBuilder()
	m := board.NewModule("m")
	m.N = n
	b.AddModule(m)
	table := func(c string) board.Table {
		t := board.NewTable("m", 1)
		t.In[0] = expr.Col(c)
		return t
	}
	if err := arguments.Bus(&b,
		[]expr.Expr{expr.Col("m.s")}, []expr.Expr{expr.Col("m.r")},
		[]board.Table{table("m.x")}, []board.Table{table("m.y")}); err != nil {
		t.Fatal(err)
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}
	if len(pg.ProductBus) != 1 || len(pg.ProductBus[0].Ends) != 1 {
		t.Fatalf("got product buses %v, want one bus with one column", pg.ProductBus)
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
		tr.SetBase("m.x", col(5, 6, 7, 0, 9))
		tr.SetBase("m.s", col(1, 1, 1, 0, 0))
		last := uint64(5)
		if bad {
			last = 9 // on a row of m.x that is not sent
		}
		tr.SetBase("m.y", col(0, 7, 6, last))
		tr.SetBase("m.r", col(0, 1, 1, 1))
		st, prf, err := prove(t, pg, tr)
		if bad {
			if err == nil && loom.Verify(st, prf) == nil {
				t.Fatal("unbalanced bus accepted")
			}
			continue
		}
		if err != nil {
			t.Fatal(err)
		}
		if err := loom.Verify(st, prf); err != nil {
			t.Fatalf("balanced bus rejected: %v", err)
		}
	}
}
