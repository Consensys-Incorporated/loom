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

package dag

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
)

// u64Vals builds a vals map from alternating (name, uint64) pairs.
func u64Vals(pairs ...any) map[string]koalabear.Element {
	vals := make(map[string]koalabear.Element, len(pairs)/2)
	for i := 0; i < len(pairs); i += 2 {
		name := pairs[i].(string)
		var e koalabear.Element
		e.SetUint64(pairs[i+1].(uint64))
		vals[name] = e
	}
	return vals
}

// checkDAGEval asserts that ExprToDAG(expr).Eval(vals) == expr.Evaluate(vals).
func checkDAGEval(t *testing.T, expr expr.Expr, vals map[string]koalabear.Element) {
	t.Helper()
	want := expr.Evaluate(vals)
	got := ExprToDAG(expr).Eval(vals)
	if !got.Equal(&want) {
		t.Errorf("DAG Eval mismatch for %s: got %s, want %s", expr.String(), got.String(), want.String())
	}
}

// checkFlatDAGEval asserts that ExprToDAG(expr).Flatten().Eval(vals) == expr.Evaluate(vals).
func checkFlatDAGEval(t *testing.T, expr expr.Expr, vals map[string]koalabear.Element) {
	t.Helper()
	want := expr.Evaluate(vals)
	got := ExprToDAG(expr).Flatten().Eval(vals)
	if !got.Equal(&want) {
		t.Errorf("Flattened DAG Eval mismatch for %s: got %s, want %s", expr.String(), got.String(), want.String())
	}
}

func e6FromU64(a0, a1, b0, b1 uint64, b2 ...uint64) ext.E6 {
	var z ext.E6
	z.B0.A0.SetUint64(a0)
	z.B0.A1.SetUint64(a1)
	z.B1.A0.SetUint64(b0)
	z.B1.A1.SetUint64(b1)
	if len(b2) > 0 {
		z.B2.A0.SetUint64(b2[0])
	}
	if len(b2) > 1 {
		z.B2.A1.SetUint64(b2[1])
	}
	return z
}

func liftE6(v koalabear.Element) ext.E6 {
	var z ext.E6
	z.B0.A0.Set(&v)
	return z
}

func u64Poly(vals ...uint64) []koalabear.Element {
	p := make([]koalabear.Element, len(vals))
	for i, v := range vals {
		p[i].SetUint64(v)
	}
	return p
}

// TestDAGEvalLeaves checks that every leaf kind evaluates correctly via the DAG.
func TestDAGEvalLeaves(t *testing.T) {
	lagName := "L0"
	vals := u64Vals("x", uint64(7), "alpha", uint64(3), lagName, uint64(11))
	var c koalabear.Element
	c.SetUint64(42)

	checkDAGEval(t, expr.Col("x"), vals)
	checkDAGEval(t, expr.Challenge("alpha"), vals)
	checkDAGEval(t, expr.Lagrange("L0"), vals)
	checkDAGEval(t, expr.Const(c), vals)
}

// TestDAGEvalOperators checks each binary operator and Pow individually.
func TestDAGEvalOperators(t *testing.T) {
	vals := u64Vals("a", uint64(3), "b", uint64(5))
	a := expr.Col("a")
	b := expr.Col("b")

	tests := []struct {
		name string
		expr expr.Expr
	}{
		{"Add", a.Add(b)},
		{"Sub", a.Sub(b)},
		{"Mul", a.Mul(b)},
		{"Pow0", &expr.Pow{Base: expr.Col("a"), Exp: 0}},
		{"Pow1", &expr.Pow{Base: expr.Col("a"), Exp: 1}},
		{"Pow2", &expr.Pow{Base: expr.Col("a"), Exp: 2}},
		{"Pow7", expr.Col("a").Pow(7)}, // uses squareAndMultiply
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			checkDAGEval(t, tc.expr, vals)
		})
	}
}

// TestDAGEvalSharedSubExpression verifies that two structurally-identical subtrees
// collapse into a single DAG node and that the result still matches the AST.
//
// Expression: (a+b) * (a+b) — two separate Add trees in the AST, one node in the DAG.
func TestDAGEvalSharedSubExpression(t *testing.T) {
	vals := u64Vals("a", uint64(3), "b", uint64(5))

	// Build two independent AST trees for (a+b), then multiply them.
	sum1 := expr.Col("a").Add(expr.Col("b"))
	sum2 := expr.Col("a").Add(expr.Col("b"))
	expr := sum1.Mul(sum2)

	dag := ExprToDAG(expr)

	// The DAG should have exactly 4 nodes: col:a, col:b, add(a,b), mul.
	// expr.Without deduplication we would have 7 (two copies of col:a, col:b, add).
	if len(dag.Nodes) != 4 {
		t.Errorf("expected 4 DAG nodes, got %d", len(dag.Nodes))
	}

	// The Mul root's two children must be the same pointer (the shared Add node).
	root := dag.Root
	if root.Kind != KindMul {
		t.Fatalf("expected Mul root, got kind %d", root.Kind)
	}
	if root.Children[0] != root.Children[1] {
		t.Error("expected both children of Mul to be the same shared Add node")
	}

	checkDAGEval(t, expr, vals)
}

// TestDAGEvalCommutativity verifies that (a+b) and (b+a) map to the same DAG node,
// so (a+b) - (b+a) has a Sub root whose two children are the same pointer.
func TestDAGEvalCommutativity(t *testing.T) {
	vals := u64Vals("a", uint64(3), "b", uint64(5))

	// (a+b) - (b+a): in the field this is 0; in the DAG both Add nodes must be shared.
	expr := expr.Col("a").Add(expr.Col("b")).
		Sub(expr.Col("b").Add(expr.Col("a")))

	dag := ExprToDAG(expr)

	root := dag.Root
	if root.Kind != KindSub {
		t.Fatalf("expected Sub root, got kind %d", root.Kind)
	}
	if root.Children[0] != root.Children[1] {
		t.Error("expected (a+b) and (b+a) to be the same DAG node")
	}

	checkDAGEval(t, expr, vals)
}

// TestDAGFlattenEvalChains verifies that flattening deep Add/Mul chains into n-ary
// nodes does not change the evaluated result.
func TestDAGFlattenEvalChains(t *testing.T) {
	vals := u64Vals("a", uint64(2), "b", uint64(3), "c", uint64(5), "d", uint64(7))
	a := expr.Col("a")
	b := expr.Col("b")
	c := expr.Col("c")
	d := expr.Col("d")

	tests := []struct {
		name string
		expr expr.Expr
	}{
		{"AddChain", a.Add(b).Add(c).Add(d)},         // ((a+b)+c)+d
		{"MulChain", a.Mul(b).Mul(c).Mul(d)},         // ((a*b)*c)*d
		{"Mixed", a.Add(b).Mul(c.Add(d))},            // (a+b)*(c+d)
		{"SubAndPow", a.Sub(b).Pow(2).Add(c.Mul(d))}, // (a-b)^2 + c*d
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			checkFlatDAGEval(t, tc.expr, vals)
		})
	}
}

// TestDAGLeaves verifies that DAG.Leaves(config) returns the String() of every
// unique leaf that passes the filter, with deduplication from the DAG.
func TestDAGLeaves(t *testing.T) {
	var c koalabear.Element
	c.SetUint64(7)

	all := expr.NewConfig()
	woCC := expr.NewConfig(expr.WithoutCommittedColumns())
	woChal := expr.NewConfig(expr.WithoutChallenges())
	woComp := expr.NewConfig(expr.WithoutVerifierColumns())
	woSetup := expr.NewConfig(expr.WithoutSetupColumns())

	mixed := expr.Col("x").
		Mul(expr.Challenge("gamma")).
		Add(expr.Setup("q_l")).
		Add(expr.Lagrange("L0")).
		Sub(expr.Const(c))

	lagrangeName := "L0"
	tests := []struct {
		name   string
		expr   expr.Expr
		config expr.Config
		want   []string // expected, order-independent
	}{
		// Individual leaf kinds with default config
		{"CommittedColumn/all", expr.Col("x"), all, []string{"x"}},
		{"Challenge/all", expr.Challenge("alpha"), all, []string{"alpha"}},
		{"VerifierColumn.Lagrange/all", expr.Lagrange("L0"), all, []string{lagrangeName}},
		{"SetupColumn/all", expr.Setup("q_l"), all, []string{"q_l"}},
		{"VerifierColumn.PublicInput/all", expr.PublicInput("pub"), all, []string{"pub"}},
		{"VerifierColumn.Exposed/all", expr.Exposed("exp"), all, []string{"exp"}},
		{"Const/all", expr.Const(c), all, []string{}}, // Const never included

		// Filtering individual leaf kinds
		{"CommittedColumn/woCC", expr.Col("x"), woCC, []string{}},
		{"Challenge/woChal", expr.Challenge("alpha"), woChal, []string{}},
		{"VerifierColumn.Lagrange/woComp", expr.Lagrange("L0"), woComp, []string{}},
		{"SetupColumn/woSetup", expr.Setup("q_l"), woSetup, []string{}},
		{"VerifierColumn.PublicInput/woComp", expr.PublicInput("pub"), woComp, []string{}},
		{"VerifierColumn.Exposed/woComp", expr.Exposed("exp"), woComp, []string{}},

		// DAG deduplication
		{"SharedLeaf", // a+a → col:a once
			expr.Col("a").Add(expr.Col("a")),
			all, []string{"a"}},
		{"SharedSubExpr", // (a+b)*(a+b) → a and b once each
			expr.Col("a").Add(expr.Col("b")).
				Mul(expr.Col("a").Add(expr.Col("b"))),
			all, []string{"a", "b"}},

		// Mixed leaf kinds with filtering
		{"Mixed/all", mixed, all, []string{"x", "gamma", "q_l", lagrangeName}}, // Const excluded always
		{"Mixed/woCC", mixed, woCC, []string{"gamma", "q_l", lagrangeName}},
		{"Mixed/woChal", mixed, woChal, []string{"x", "q_l", lagrangeName}},
		{"Mixed/woComp", mixed, woComp, []string{"x", "gamma", "q_l"}},
		{"Mixed/woSetup", mixed, woSetup, []string{"x", "gamma", lagrangeName}},
		{"Mixed/woCC+woChal", mixed, expr.NewConfig(expr.WithoutCommittedColumns(), expr.WithoutChallenges()), []string{"q_l", lagrangeName}},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got := ExprToDAG(tc.expr).Leaves(tc.config)
			expr.AssertSameSet(t, got, tc.want)
		})
	}
}

// TestDAGDegree verifies that DAG.Degree() matches Expr.Degree() for a range
// of expressions, including every leaf kind and every operator.
func TestDAGDegree(t *testing.T) {
	var zero, one koalabear.Element
	one.SetUint64(1)

	tests := []struct {
		name string
		expr expr.Expr
		want int
	}{
		// Leaves
		{"CommittedColumn", expr.Col("x"), 1},
		{"VerifierColumn.Lagrange", expr.Lagrange("L0"), 1},
		{"SetupColumn", expr.Setup("q_l"), 1},
		{"VerifierColumn.PublicInput", expr.PublicInput("pub"), 1},
		{"Challenge", expr.Challenge("alpha"), 0},    // Challenge is degree 0
		{"ConstNonZero", expr.Const(one), 0},         // non-zero constant
		{"ConstZero", expr.Const(zero), expr.NegInf}, // zero polynomial

		// Binary operators
		{"Add(1,1)", expr.Col("a").Add(expr.Col("b")), 1},
		{"Sub(1,0)", expr.Col("a").Sub(expr.Challenge("g")), 1},
		{"Mul(1,1)", expr.Col("a").Mul(expr.Col("b")), 2},
		{"Mul(1,0)", expr.Col("a").Mul(expr.Challenge("g")), 1},
		{"Pow2", &expr.Pow{Base: expr.Col("a"), Exp: 2}, 2},
		{"Pow5", expr.Col("a").Pow(5), 5},
		{"Pow0", &expr.Pow{Base: expr.Col("a"), Exp: 0}, 0},

		// Challenge treated as degree-0 in a larger expression
		{"AddChallenge", expr.Col("a").Add(expr.Challenge("g")), 1},
		{"MulChallenge", expr.Col("a").Mul(expr.Challenge("g")).Mul(expr.Col("b")), 2},

		// Flattened n-ary chains should have the same degree as the AST
		{"AddChain", expr.Col("a").Add(expr.Col("b")).Add(expr.Col("c")), 1},
		{"MulChain", expr.Col("a").Mul(expr.Col("b")).Mul(expr.Col("c")), 3},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			// Plain DAG
			got := ExprToDAG(tc.expr).Degree()
			if got != tc.want {
				t.Errorf("DAG.Degree() = %d, want %d", got, tc.want)
			}
			// Flattened DAG must give the same answer
			gotFlat := ExprToDAG(tc.expr).Flatten().Degree()
			if gotFlat != tc.want {
				t.Errorf("Flattened DAG.Degree() = %d, want %d", gotFlat, tc.want)
			}
			// Must also match Expr.Degree()
			if exprDeg := tc.expr.Degree(); exprDeg != tc.want {
				t.Errorf("Expr.Degree() = %d, want %d (test case has wrong want?)", exprDeg, tc.want)
			}
		})
	}
}

func TestDAGFieldInference(t *testing.T) {
	tests := []struct {
		name string
		expr expr.Expr
		want field.Kind
	}{
		{"BaseColumn", expr.Col("x"), field.Base},
		{"ExtColumn", expr.ExtCol("x"), field.Ext},
		{"Challenge", expr.Challenge("gamma"), field.Ext},
		// Every VerifierColumn is Ext: the verifier evaluates it at zeta in E6.
		{"PublicInput", expr.PublicInput("pub"), field.Ext},
		{"PublicInputExt", expr.PublicInputExt("pub"), field.Ext},
		{"Lagrange", expr.Lagrange("L0"), field.Ext},
		{"Exposed", expr.Exposed("exp"), field.Ext},
		{"BaseExpression", expr.Col("x").Add(expr.Col("y")), field.Base},
		{"ChallengeExpression", expr.Col("x").Mul(expr.Challenge("gamma")), field.Ext},
		{"ExtColumnExpression", expr.ExtCol("x").Sub(expr.Col("y")).Pow(3), field.Ext},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			d := ExprToDAG(tc.expr)
			if got := d.Root.Field; got != tc.want {
				t.Fatalf("root field = %s, want %s", got, tc.want)
			}

			flat := d.Flatten()
			if got := flat.Root.Field; got != tc.want {
				t.Fatalf("flattened root field = %s, want %s", got, tc.want)
			}

			factored := flat.Factorize()
			if got := factored.Root.Field; got != tc.want {
				t.Fatalf("factored root field = %s, want %s", got, tc.want)
			}
		})
	}
}

func TestDAGEvalMixedBaseOnly(t *testing.T) {
	vals := u64Vals("x", uint64(3), "y", uint64(5))
	ex := expr.Col("x").Mul(expr.Col("y")).Add(expr.Col("x").Pow(2))

	got := ExprToDAG(ex).EvalMixed(vals, nil)
	want := liftE6(ex.Evaluate(vals))
	if !got.Equal(&want) {
		t.Fatalf("EvalMixed = %s, want %s", got.String(), want.String())
	}
}

func TestDAGEvalMixedWithExtensionChallenge(t *testing.T) {
	var x, two koalabear.Element
	x.SetUint64(7)
	two.SetUint64(2)
	gamma := e6FromU64(3, 4, 5, 6)

	ex := expr.Col("x").Mul(expr.Challenge("gamma")).Add(expr.Const(two))
	got := ExprToDAG(ex).EvalMixed(
		map[string]koalabear.Element{"x": x},
		map[string]ext.E6{"gamma": gamma},
	)

	xExt := liftE6(x)
	twoExt := liftE6(two)
	var want ext.E6
	want.Mul(&xExt, &gamma)
	want.Add(&want, &twoExt)

	if !got.Equal(&want) {
		t.Fatalf("EvalMixed = %s, want %s", got.String(), want.String())
	}
}

func TestDAGEvalMixedWithColumnFieldRegistry(t *testing.T) {
	logup := e6FromU64(9, 1, 2, 3)
	var x koalabear.Element
	x.SetUint64(4)

	ex := expr.Col("logup").Add(expr.Col("x"))
	d := ExprToDAGWithColumnFields(ex, map[string]field.Kind{"logup": field.Ext})
	got := d.EvalMixed(
		map[string]koalabear.Element{"x": x},
		map[string]ext.E6{"logup": logup},
	)

	xExt := liftE6(x)
	var want ext.E6
	want.Add(&logup, &xExt)
	if !got.Equal(&want) {
		t.Fatalf("EvalMixed = %s, want %s", got.String(), want.String())
	}
}

func TestDAGEvalMixedExtLeafBaseFallback(t *testing.T) {
	var gamma koalabear.Element
	gamma.SetUint64(11)

	got := ExprToDAG(expr.Challenge("gamma")).EvalMixed(
		map[string]koalabear.Element{"gamma": gamma},
		nil,
	)
	want := liftE6(gamma)
	if !got.Equal(&want) {
		t.Fatalf("EvalMixed = %s, want %s", got.String(), want.String())
	}
}

func TestDAGEvalMixedMissingVariablePanics(t *testing.T) {
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("expected missing variable panic")
		}
	}()

	_ = ExprToDAG(expr.Challenge("gamma")).EvalMixed(nil, nil)
}

func TestDAGEvalWithCacheVarsMixed(t *testing.T) {
	var x, two koalabear.Element
	x.SetUint64(7)
	two.SetUint64(2)
	gamma := e6FromU64(3, 4, 5, 6)
	logup := e6FromU64(9, 1, 2, 3)

	ex := expr.Col("x").
		Mul(expr.Challenge("gamma")).
		Add(expr.ExtCol("logup")).
		Sub(expr.Const(two))
	d := ExprToDAG(ex)

	baseVars := make([]koalabear.Element, len(d.VarIndex))
	extVars := make([]ext.E6, len(d.VarIndex))
	baseVars[d.VarIndex["x"]] = x
	extVars[d.VarIndex["gamma"]] = gamma
	extVars[d.VarIndex["logup"]] = logup

	got := d.EvalWithCacheVarsMixed(
		baseVars,
		extVars,
		make([]koalabear.Element, len(d.Nodes)),
		make([]ext.E6, len(d.Nodes)),
	)

	xExt := liftE6(x)
	twoExt := liftE6(two)
	var want ext.E6
	want.Mul(&xExt, &gamma)
	want.Add(&want, &logup)
	want.Sub(&want, &twoExt)

	if !got.Equal(&want) {
		t.Fatalf("EvalWithCacheVarsMixed = %s, want %s", got.String(), want.String())
	}
}

func TestDAGEvalOnAllEntriesMixed(t *testing.T) {
	const N = 4

	x := u64Poly(1, 2, 3, 4)
	gamma := e6FromU64(3, 4, 5, 6)
	logup := []ext.E6{
		e6FromU64(10, 1, 0, 0),
		e6FromU64(11, 2, 1, 0),
		e6FromU64(12, 3, 0, 1),
		e6FromU64(13, 4, 2, 1),
	}
	var two koalabear.Element
	two.SetUint64(2)

	ex := expr.Col("x", expr.WithShift(1)).
		Mul(expr.Challenge("gamma")).
		Add(expr.ExtCol("logup").Pow(2)).
		Sub(expr.Const(two))
	d := ExprToDAG(ex)
	if d.Root.Field != field.Ext {
		t.Fatalf("root field = %s, want %s", d.Root.Field, field.Ext)
	}

	for _, n := range d.Nodes {
		if n.Kind != KindLeaf || n.IsConst {
			continue
		}
		switch n.Leaf.Name {
		case "x":
			n.Leaf.Idx = 0
		case "gamma":
			n.Leaf.Idx = 0
		case "logup":
			n.Leaf.Idx = 1
		default:
			t.Fatalf("unexpected leaf %q", n.Leaf.Name)
		}
	}

	got := d.EvalOnAllEntriesMixed(
		[][]koalabear.Element{x},
		[][]ext.E6{{gamma}, logup},
		N,
	)
	var ws EvalWorkspace
	gotInto := make([]ext.E6, N)
	d.EvalOnAllEntriesMixedInto(
		gotInto,
		[][]koalabear.Element{x},
		[][]ext.E6{{gamma}, logup},
		N,
		&ws,
	)

	twoExt := liftE6(two)
	for j := range N {
		xRot := liftE6(x[(j+1)%N])
		var want, term, square ext.E6
		term.Mul(&xRot, &gamma)
		square.Mul(&logup[j], &logup[j])
		want.Add(&term, &square)
		want.Sub(&want, &twoExt)

		if !got[j].Equal(&want) {
			t.Fatalf("row %d: EvalOnAllEntriesMixed = %s, want %s", j, got[j].String(), want.String())
		}
		if !gotInto[j].Equal(&want) {
			t.Fatalf("row %d: EvalOnAllEntriesMixedInto = %s, want %s", j, gotInto[j].String(), want.String())
		}
	}

	logup[0] = e6FromU64(21, 1, 2, 3)
	d.EvalOnAllEntriesMixedInto(
		gotInto,
		[][]koalabear.Element{x},
		[][]ext.E6{{gamma}, logup},
		N,
		&ws,
	)
	xRot := liftE6(x[1])
	var want, term, square ext.E6
	term.Mul(&xRot, &gamma)
	square.Mul(&logup[0], &logup[0])
	want.Add(&term, &square)
	want.Sub(&want, &twoExt)
	if !gotInto[0].Equal(&want) {
		t.Fatalf("workspace reuse: row 0 = %s, want %s", gotInto[0].String(), want.String())
	}
}

// TestDAGFactorize verifies that Factorize correctly applies
// add(mul(x,y),mul(x,z)) → mul(x,add(y,z)) and preserves evaluation results.
func TestDAGFactorize(t *testing.T) {
	x := expr.Col("x")
	y := expr.Col("y")
	z := expr.Col("z")
	w := expr.Col("w")
	vals := u64Vals("x", uint64(2), "y", uint64(3), "z", uint64(5), "w", uint64(7))

	cases := []struct {
		name        string
		expr        expr.Expr
		wantMulSave int // expected reduction in Mul field operations at eval time
	}{
		{
			// x*y + x*z  →  x*(y+z): Mul(x,y)+Mul(x,z)=4 muls → Mul(x,Add(y,z))=2 muls
			name:        "binary",
			expr:        x.Mul(y).Add(x.Mul(z)),
			wantMulSave: 2,
		},
		{
			// x*y + x*z + x*w  →  x*(y+z+w): 6 muls → 2 muls
			name:        "three_terms",
			expr:        x.Mul(y).Add(x.Mul(z)).Add(x.Mul(w)),
			wantMulSave: 4,
		},
		{
			// x*y + x*z + w  →  x*(y+z) + w: 4 muls → 2 muls
			name:        "partial",
			expr:        x.Mul(y).Add(x.Mul(z)).Add(w),
			wantMulSave: 2,
		},
		{
			// x*y + z*w: no common factor, no savings
			name:        "no_common_factor",
			expr:        x.Mul(y).Add(z.Mul(w)),
			wantMulSave: 0,
		},
		{
			// x*y*z + x*y*w  →  x*(y*(z+w)): saves 2 multiplications
			name:        "multi_factor_mul",
			expr:        x.Mul(y).Mul(z).Add(x.Mul(y).Mul(w)),
			wantMulSave: 2,
		},
	}

	// countMuls counts field Mul operations performed when evaluating the DAG.
	countMuls := func(d *DAG) int {
		n := 0
		for _, node := range d.Nodes {
			if node.Kind == KindMul {
				n += len(node.Children) // n-ary Mul does len(Children) multiplications
			}
		}
		return n
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			d := ExprToDAG(tc.expr).Flatten().Factorize()

			// Correctness: evaluation must match the original expression.
			want := tc.expr.Evaluate(vals)
			got := d.Eval(vals)
			if !got.Equal(&want) {
				t.Errorf("eval mismatch: got %s, want %s\n", got.String(), want.String())
			}

			// EvalWithCacheVars must also produce the correct result.
			vars := make([]koalabear.Element, len(d.VarIndex))
			for name, idx := range d.VarIndex {
				if v, ok := vals[name]; ok {
					vars[idx] = v
				}
			}
			cache := make([]koalabear.Element, len(d.Nodes))
			gotVars := d.EvalWithCacheVars(vars, cache)
			if !gotVars.Equal(&want) {
				t.Errorf("EvalWithCacheVars mismatch: got %s, want %s", gotVars.String(), want.String())
			}

			// Mul savings: factorize reduces field multiplications, not node count.
			unfactored := ExprToDAG(tc.expr).Flatten()
			mulsBefore := countMuls(unfactored)
			mulsAfter := countMuls(d)
			if mulsBefore-mulsAfter != tc.wantMulSave {
				t.Errorf("Mul savings: got %d (before=%d after=%d), want %d\n",
					mulsBefore-mulsAfter, mulsBefore, mulsAfter, tc.wantMulSave)
			}
		})
	}
}

// setupPiSlice assigns Idx to every leaf in expr (deduplicating by name) and
// returns _Pi where _Pi[leaf.Idx] is the polynomial for that leaf.
// This mirrors the setup done inside evalPointWiseInto.
func setupPiSlice(ex expr.Expr, pi map[string][]koalabear.Element) [][]koalabear.Element {
	nameToIdx := make(map[string]int)
	for _, l := range ex.LeavesFull(expr.NewConfig()) {
		if _, ok := nameToIdx[l.Name]; !ok {
			nameToIdx[l.Name] = len(nameToIdx)
		}
		l.Idx = nameToIdx[l.Name]
	}
	_Pi := make([][]koalabear.Element, len(nameToIdx))
	for name, idx := range nameToIdx {
		_Pi[idx] = pi[name]
	}
	return _Pi
}

func TestDAGEvalOnIthEntry(t *testing.T) {
	const N = 8

	makePoly := func(vals ...uint64) []koalabear.Element {
		p := make([]koalabear.Element, len(vals))
		for i, v := range vals {
			p[i].SetUint64(v)
		}
		return p
	}

	t.Run("Regular_x0sq_plus_x1", func(t *testing.T) {
		P0 := makePoly(1, 2, 3, 4, 5, 6, 7, 8)
		P1 := makePoly(10, 20, 30, 40, 50, 60, 70, 80)
		pi := map[string][]koalabear.Element{"x0": P0, "x1": P1}
		expr := expr.Col("x0").Pow(2).Add(expr.Col("x1"))
		d := ExprToDAG(expr)
		_Pi := setupPiSlice(expr, pi)

		for i := 0; i < N; i++ {
			want := expr.EvaluateOnIthEntry(_Pi, i)
			got := d.EvalOnIthEntry(_Pi, i)
			if !got.Equal(&want) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), want.String())
			}
		}
	})

	t.Run("ConstantPolynomial", func(t *testing.T) {
		// gamma is a length-1 (constant) polynomial; should always return gamma[0]
		P0 := makePoly(3, 5, 7, 9, 11, 13, 15, 17)
		var gVal koalabear.Element
		gVal.SetUint64(42)
		pi := map[string][]koalabear.Element{"x0": P0, "gamma": {gVal}}
		expr := expr.Col("x0").Sub(expr.Col("gamma"))
		d := ExprToDAG(expr)
		_Pi := setupPiSlice(expr, pi)

		for i := 0; i < N; i++ {
			want := expr.EvaluateOnIthEntry(_Pi, i)
			got := d.EvalOnIthEntry(_Pi, i)
			if !got.Equal(&want) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), want.String())
			}
		}
	})

	t.Run("ConstLeaf", func(t *testing.T) {
		var three koalabear.Element
		three.SetUint64(3)
		P0 := makePoly(4, 5, 6, 7, 8, 9, 10, 11)
		pi := map[string][]koalabear.Element{"x0": P0}
		expr := expr.Col("x0").Sub(expr.Const(three))
		d := ExprToDAG(expr)
		_Pi := setupPiSlice(expr, pi)

		for i := 0; i < N; i++ {
			want := expr.EvaluateOnIthEntry(_Pi, i)
			got := d.EvalOnIthEntry(_Pi, i)
			if !got.Equal(&want) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), want.String())
			}
		}
	})

	t.Run("ShiftedColumn", func(t *testing.T) {
		// E = x0(shift=1) - x0 → P0[(i+1)%N] - P0[i]
		P0 := makePoly(1, 3, 2, 7, 5, 4, 6, 8)
		pi := map[string][]koalabear.Element{"x0": P0}
		expr := expr.Col("x0", expr.WithShift(1)).Sub(expr.Col("x0"))
		d := ExprToDAG(expr)
		_Pi := setupPiSlice(expr, pi)

		for i := 0; i < N; i++ {
			want := expr.EvaluateOnIthEntry(_Pi, i)
			got := d.EvalOnIthEntry(_Pi, i)
			if !got.Equal(&want) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), want.String())
			}
		}
	})

	t.Run("SharedSubExpression", func(t *testing.T) {
		// (a*b + c) * (a*b - d): a*b is shared in the DAG
		Pa := makePoly(2, 3, 5, 7, 11, 13, 17, 19)
		Pb := makePoly(1, 2, 3, 4, 5, 6, 7, 8)
		Pc := makePoly(10, 10, 10, 10, 10, 10, 10, 10)
		Pd := makePoly(1, 1, 1, 1, 1, 1, 1, 1)
		pi := map[string][]koalabear.Element{"a": Pa, "b": Pb, "c": Pc, "d": Pd}

		ab1 := expr.Col("a").Mul(expr.Col("b"))
		ab2 := expr.Col("a").Mul(expr.Col("b"))
		expr := ab1.Add(expr.Col("c")).Mul(ab2.Sub(expr.Col("d")))
		d := ExprToDAG(expr)
		_Pi := setupPiSlice(expr, pi)

		for i := 0; i < N; i++ {
			want := expr.EvaluateOnIthEntry(_Pi, i)
			got := d.EvalOnIthEntry(_Pi, i)
			if !got.Equal(&want) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), want.String())
			}
		}
	})
}

// TestDAGEvalComplex uses a rich expression with shared sub-expressions, all
// operator kinds, and both DAG and flattened-DAG evaluation.
//
// Expression: (a*b + c) * (a*b - d)
// a*b is a shared sub-expression; it should appear once in the DAG.
func TestDAGEvalComplex(t *testing.T) {
	vals := u64Vals("a", uint64(2), "b", uint64(3), "c", uint64(5), "d", uint64(7))

	// Build (a*b + c) * (a*b - d) using two independent trees for a*b.
	ab1 := expr.Col("a").Mul(expr.Col("b"))
	ab2 := expr.Col("a").Mul(expr.Col("b"))
	expr := ab1.Add(expr.Col("c")).Mul(ab2.Sub(expr.Col("d")))

	dag := ExprToDAG(expr)

	// With sharing: col:a, col:b, mul(a,b), col:c, add, col:d, sub, mul(root) = 8 nodes.
	// expr.Without sharing we would have 10 (two col:a, two col:b, two mul(a,b)).
	if len(dag.Nodes) != 8 {
		t.Errorf("expected 8 DAG nodes, got %d", len(dag.Nodes))
	}

	checkDAGEval(t, expr, vals)
	checkFlatDAGEval(t, expr, vals)
}
