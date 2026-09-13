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

package expr

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/field"
)

func TestString(t *testing.T) {

	var five koalabear.Element
	five.SetUint64(5)

	a := Col("x")
	b := Const(five)
	c := &Add{Left: a, Right: b}
	d := &Mul{Left: a, Right: c}

	if a.String() != "x" {
		t.Errorf("Expected 'x', got '%s'", a.String())
	}

	if b.String() != "5" {
		t.Errorf("Expected '5', got '%s'", b.String())
	}

	if c.String() != "(x + 5)" {
		t.Errorf("Expected '(x + 5)', got '%s'", c.String())
	}

	if d.String() != "(x * (x + 5))" {
		t.Errorf("Expected '(x * (x + 5))', got '%s'", d.String())
	}

}

func TestFieldMetadata(t *testing.T) {
	var one koalabear.Element
	one.SetOne()

	tests := []struct {
		name string
		expr Expr
		want field.Kind
	}{
		{"Col", Col("x"), field.Base},
		{"ExtCol", ExtCol("x"), field.Ext},
		{"ShiftedCol", Col("x", WithShift(1)), field.Base},
		{"ShiftedExtCol", ExtCol("x", WithShift(1)), field.Ext},
		{"Setup", Setup("q_l"), field.Base},
		{"ExtSetup", ExtSetup("q_l"), field.Ext},
		// VerifierColumns evaluate at zeta in E6, so FieldKind pins them to Ext
		// regardless of the Field they were declared with.
		{"Exposed", Exposed("x"), field.Ext},
		{"Lagrange", Lagrange("L0"), field.Ext},
		{"Const", Const(one), field.Base},
		{"Challenge", Challenge("gamma"), field.Ext},
		{"RawChallengeLeaf", &Leaf{Type: ChallengeColumn, Name: "gamma"}, field.Ext},
		{"BaseExpression", Col("x").Add(Const(one)), field.Base},
		{"ChallengeExpression", Col("x").Mul(Challenge("gamma")), field.Ext},
		{"ExtColumnExpression", ExtCol("x").Sub(Col("y")).Pow(2), field.Ext},
		{"ColumnRegistryExpression", Col("logup").Add(Col("x")), field.Ext},
		{"SetupRegistryExpression", Setup("logup").Add(Col("x")), field.Ext},
		{"PublicInput", PublicInput("x"), field.Ext},
		{"PublicInputExt", PublicInputExt("x"), field.Ext},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			columnFields := map[string]field.Kind{"logup": field.Ext}
			if got := FieldOfWithColumnFields(tc.expr, columnFields); got != tc.want {
				t.Fatalf("FieldOf(%s) = %s, want %s", tc.expr.String(), got, tc.want)
			}
		})
	}
}

func TestPrune(t *testing.T) {

	x0 := Col("x_0")
	x1 := Col("x_1")
	e := x0.Add(x1).Pow(8)

	degreeBefore := e.Degree()
	beforePruning := e.String()

	degreeToPrune := 2
	_ = e.Prune(degreeToPrune)
	degreeAfter := e.Degree()
	afterPruning := e.String()
	if beforePruning != afterPruning {
		t.Fatal("pruning should not affect the string")
	}

	if degreeAfter+1 != degreeBefore {
		t.Errorf("pruning by a degree %d should decrease the degree by %d", degreeToPrune, degreeToPrune-1)
	}

}

func TestLeaves(t *testing.T) {
	var five koalabear.Element
	five.SetUint64(5)

	all := NewConfig()
	woCC := NewConfig(WithoutVerifierColumns())
	woChal := NewConfig(WithoutChallenges())
	woSetup := NewConfig(WithoutSetupColumns())
	woAll := NewConfig(WithoutVerifierColumns(), WithoutChallenges())

	// --- Leaf nodes ---

	// VerifierColumn (Lagrange hook): present by default, absent when excluded
	AssertSameSet(t, Lagrange("L0").Leaves(all), []string{"L0"})
	AssertSameSet(t, Lagrange("L0").Leaves(woCC), []string{})

	// CommittedColumn: always present regardless of config
	AssertSameSet(t, Col("x").Leaves(all), []string{"x"})
	AssertSameSet(t, Col("x").Leaves(woCC), []string{"x"})
	AssertSameSet(t, Col("x").Leaves(woChal), []string{"x"})

	// Const: never present
	AssertSameSet(t, Const(five).Leaves(all), []string{})

	// Challenge: present by default, absent when excluded
	AssertSameSet(t, Challenge("beta").Leaves(all), []string{"beta"})
	AssertSameSet(t, Challenge("beta").Leaves(woChal), []string{})

	// SetupColumn: present by default, absent when excluded
	AssertSameSet(t, Setup("q_l").Leaves(all), []string{"q_l"})
	AssertSameSet(t, Setup("q_l").Leaves(woSetup), []string{})

	// All three verifier hooks share the one VerifierColumn flag.
	AssertSameSet(t, PublicInput("pub").Leaves(all), []string{"pub"})
	AssertSameSet(t, PublicInput("pub").Leaves(woCC), []string{})
	AssertSameSet(t, Exposed("exp").Leaves(all), []string{"exp"})
	AssertSameSet(t, Exposed("exp").Leaves(woCC), []string{})

	// --- Composite expressions ---

	// VerifierColumn + CommittedColumn
	e := Lagrange("L0").Add(Col("x"))
	AssertSameSet(t, e.Leaves(all), []string{"L0", "x"})
	AssertSameSet(t, e.Leaves(woCC), []string{"x"})

	// VerifierColumn * Challenge
	e = Lagrange("L0").Mul(Challenge("gamma"))
	AssertSameSet(t, e.Leaves(all), []string{"L0", "gamma"})
	AssertSameSet(t, e.Leaves(woCC), []string{"gamma"})
	AssertSameSet(t, e.Leaves(woChal), []string{"L0"})
	AssertSameSet(t, e.Leaves(woAll), []string{})

	// Multiple VerifierColumns
	e = Lagrange("L0").Add(Lagrange("L1"))
	AssertSameSet(t, e.Leaves(all), []string{"L0", "L1"})
	AssertSameSet(t, e.Leaves(woCC), []string{})

	// Sub: VerifierColumn on the right
	e = Col("x").Sub(Lagrange("L0"))
	AssertSameSet(t, e.Leaves(all), []string{"x", "L0"})
	AssertSameSet(t, e.Leaves(woCC), []string{"x"})

	// Pow: VerifierColumn inside
	AssertSameSet(t, Lagrange("L0").Pow(2).Leaves(all), []string{"L0"})
	AssertSameSet(t, Lagrange("L0").Pow(2).Leaves(woCC), []string{})

	// Pow: CommittedColumn inside — no VerifierColumn
	AssertSameSet(t, Col("x").Pow(3).Leaves(all), []string{"x"})
	AssertSameSet(t, Col("x").Pow(3).Leaves(woCC), []string{"x"})

	// Nested: (x + L0) * (y - alpha) — all four leaf types interact
	e = Col("x").Add(Lagrange("L0")).Mul(Col("y").Sub(Challenge("alpha")))
	AssertSameSet(t, e.Leaves(all), []string{"x", "L0", "y", "alpha"})
	AssertSameSet(t, e.Leaves(woCC), []string{"x", "y", "alpha"})
	AssertSameSet(t, e.Leaves(woChal), []string{"x", "L0", "y"})
	AssertSameSet(t, e.Leaves(woAll), []string{"x", "y"})

	// Verifier columns are filtered independently from committed columns, and
	// OnlyVerifierColumns selects every hook kind at once.
	e = PublicInput("pub").Add(Col("x")).Add(Lagrange("L0")).Add(Exposed("exp"))
	AssertSameSet(t, e.Leaves(all), []string{"pub", "x", "L0", "exp"})
	AssertSameSet(t, e.Leaves(woCC), []string{"x"})
	AssertSameSet(t, e.Leaves(NewConfig(OnlyVerifierColumns...)), []string{"pub", "L0", "exp"})

	// Setup columns are filtered independently from committed columns.
	e = Setup("q_l").Add(Col("x"))
	AssertSameSet(t, e.Leaves(all), []string{"q_l", "x"})
	AssertSameSet(t, e.Leaves(woSetup), []string{"x"})
	AssertSameSet(t, e.Leaves(NewConfig(OnlySetupColumns...)), []string{"q_l"})

	// Same VerifierColumn appearing multiple times — deduplicated
	e = Lagrange("L0").Add(Lagrange("L0"))
	AssertSameSet(t, e.Leaves(all), []string{"L0"})
}

func TestReplaceLeafByExpression(t *testing.T) {

	var five koalabear.Element
	five.SetUint64(5)

	// Var: matching name → replaced
	if got := Col("x").ReplaceLeafByExpression("x", Col("y")); got.String() != "y" {
		t.Errorf("expected 'y', got '%s'", got.String())
	}

	// Var: non-matching name → unchanged
	if got := Col("x").ReplaceLeafByExpression("z", Col("y")); got.String() != "x" {
		t.Errorf("expected 'x', got '%s'", got.String())
	}

	// Challenge: matching name → replaced
	if got := Challenge("alpha").ReplaceLeafByExpression("alpha", Col("y")); got.String() != "y" {
		t.Errorf("expected 'y', got '%s'", got.String())
	}

	// Challenge: non-matching name → unchanged
	if got := Challenge("alpha").ReplaceLeafByExpression("beta", Col("y")); got.String() != "alpha" {
		t.Errorf("expected 'alpha', got '%s'", got.String())
	}

	// Const: never replaced regardless of the leaf name
	if got := Const(five).ReplaceLeafByExpression("5", Col("y")); got.String() != "5" {
		t.Errorf("expected '5', got '%s'", got.String())
	}

	// Add: only the matching child is replaced
	e := Col("x").Add(Const(five))
	if got := e.ReplaceLeafByExpression("x", Col("y")); got.String() != "(y + 5)" {
		t.Errorf("expected '(y + 5)', got '%s'", got.String())
	}

	// All occurrences replaced: x + x with x→y gives y + y
	e = Col("x").Add(Col("x"))
	if got := e.ReplaceLeafByExpression("x", Col("y")); got.String() != "(y + y)" {
		t.Errorf("expected '(y + y)', got '%s'", got.String())
	}

	// Sub: alpha replaced by composite expression
	e = Col("x").Sub(Challenge("alpha"))
	if got := e.ReplaceLeafByExpression("alpha", Col("x").Mul(Col("y"))); got.String() != "(x - (x * y))" {
		t.Errorf("expected '(x - (x * y))', got '%s'", got.String())
	}

	// Mul: nested replacement — x in x*(x+y) with x→a gives a*(a+y)
	e = Col("x").Mul(Col("x").Add(Col("y")))
	if got := e.ReplaceLeafByExpression("x", Col("a")); got.String() != "(a * (a + y))" {
		t.Errorf("expected '(a * (a + y))', got '%s'", got.String())
	}

	// Pow: base replaced by composite
	e = &Pow{Base: Col("x"), Exp: 2}
	if got := e.ReplaceLeafByExpression("x", Col("y").Add(Col("z"))); got.String() != "((y + z) ^ 2)" {
		t.Errorf("expected '((y + z) ^ 2)', got '%s'", got.String())
	}

	// Original expression is not modified by replacement
	original := Col("x").Add(Col("y"))
	originalStr := original.String()
	_ = original.ReplaceLeafByExpression("x", Col("z"))
	if original.String() != originalStr {
		t.Errorf("original modified: expected '%s', got '%s'", originalStr, original.String())
	}
}

func TestEval(t *testing.T) {

	x0 := Col("x_0")
	x1 := Col("x_1")
	x2 := Col("x_2")
	x3 := Col("x_3")

	input := make(map[string]koalabear.Element)

	var one, two, three, four koalabear.Element
	one.SetUint64(1)
	two.SetUint64(2)
	three.SetUint64(3)
	four.SetUint64(4)
	input[x0.Name] = one
	input[x1.Name] = two
	input[x2.Name] = three
	input[x3.Name] = four

	e := x0.Mul(x1).Add(x2).Mul(x3).Add(Const(one)).Mul(Const(two)).Add(Const(three)).Mul(Const(four))

	var expected, result koalabear.Element
	expected.SetUint64(180) // (((((((x_0 * x_1) + x_2) * x_3) + 1) * 2) + 3) * 4)
	result = e.Evaluate(input)

	if !result.Equal(&expected) {
		t.Errorf("Expected %s, got %s", expected.String(), result.String())
	}

}
