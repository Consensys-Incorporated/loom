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

package poly

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/dag"
)

// makeLagrangePoly builds a Polynomial from uint64 evaluations.
func makeLagrangePoly(vals ...uint64) Polynomial {
	coeffs := make(Polynomial, len(vals))
	for i, v := range vals {
		coeffs[i].SetUint64(v)
	}
	return coeffs
}

// checkPointwise asserts R[i] == expected[i] for each domain point.
func checkPointwise(t *testing.T, R Polynomial, expected []koalabear.Element) {
	t.Helper()
	for i := 0; i < len(expected); i++ {
		if !R[i].Equal(&expected[i]) {
			t.Errorf("point %d: got %s, want %s", i, R[i].String(), expected[i].String())
		}
	}
}

// canonicalEval evaluates a canonical-form polynomial at z using Horner's method.
func canonicalEval(coeffs []koalabear.Element, z koalabear.Element) koalabear.Element {
	if len(coeffs) == 0 {
		return koalabear.Element{}
	}
	y := coeffs[len(coeffs)-1]
	for i := len(coeffs) - 2; i >= 0; i-- {
		y.Mul(&y, &z)
		y.Add(&y, &coeffs[i])
	}
	return y
}

// lagrangeNormalToCanonical converts a Lagrange Normal polynomial to canonical form in-place.
func lagrangeNormalToCanonical(p []koalabear.Element) {
	d := fft.NewDomain(uint64(len(p)))
	d.FFTInverse(p, fft.DIF)
	fft.BitReverse(p)
}

// evalLagrangeNormalAt evaluates a Lagrange Normal polynomial at z by converting to canonical first.
func evalLagrangeNormalAt(p Polynomial, z koalabear.Element) koalabear.Element {
	if len(p) == 1 {
		return p[0]
	}
	coeffs := make([]koalabear.Element, len(p))
	copy(coeffs, p)
	lagrangeNormalToCanonical(coeffs)
	return canonicalEval(coeffs, z)
}

func TestLagrangeAtZeta(t *testing.T) {

	n := 16
	p := make([]koalabear.Element, n)
	d := fft.NewDomain(uint64(n))
	var zeta koalabear.Element
	zeta.SetRandom()
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			p[j].SetZero()
			if i == j {
				p[j].SetOne()
			}
		}
		d.FFTInverse(p, fft.DIF)
		fft.BitReverse(p)
		expected := canonicalEval(p, zeta)
		computed := LagrangeAtZeta(zeta, n, i)
		if !expected.Equal(&computed) {
			t.Errorf("expected %s, got %s", expected.String(), computed.String())
		}
	}

}

func TestLagrangesAtZetaExt(t *testing.T) {
	n := 16
	zeta := e6FromU64(3, 5, 7, 11)

	computed := LagrangesAtZeta(zeta, n)
	if len(computed) != n {
		t.Fatalf("expected %d lagrange evaluations, got %d", n, len(computed))
	}

	for i := 0; i < n; i++ {
		expected := LagrangeAtZetaExt(zeta, n, i)
		if !expected.Equal(&computed[i]) {
			t.Errorf("L_%d(zeta): expected %s, got %s", i, expected.String(), computed[i].String())
		}
	}
}

func TestEvalPointWise(t *testing.T) {

	t.Run("NonHomogeneous_x0sq_plus_x1", func(t *testing.T) {
		// Q = x0^2 + x1
		size := 8
		coeffs0 := make([]koalabear.Element, size)
		coeffs1 := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			coeffs0[i].SetUint64(uint64(i + 1))
			coeffs1[i].SetUint64(uint64(2 * (i + 1)))
		}

		C := expr.Col("x0").Pow(2).Add(expr.Col("x1"))
		Pi := map[string]Polynomial{"x0": coeffs0, "x1": coeffs1}

		R, err := BuildPointwiseEvaluation(Pi, C, nil)
		if err != nil {
			t.Fatalf("EvalPointWise failed: %v", err)
		}
		if len(R) != size {
			t.Fatalf("R is of size %d, expected %d", len(R), size)
		}

		expected := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			expected[i].Square(&coeffs0[i]).Add(&expected[i], &coeffs1[i])
		}
		checkPointwise(t, R, expected)
	})

	t.Run("Sub_x0_minus_x1", func(t *testing.T) {
		size := 8
		P0 := makeLagrangePoly(10, 20, 30, 40, 50, 60, 70, 80)
		P1 := makeLagrangePoly(1, 2, 3, 4, 5, 6, 7, 8)

		C := expr.Col("x0").Sub(expr.Col("x1"))
		Pi := map[string]Polynomial{"x0": P0, "x1": P1}

		R, err := BuildPointwiseEvaluation(Pi, C, nil)
		if err != nil {
			t.Fatalf("EvalPointWise failed: %v", err)
		}

		expected := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			expected[i].Sub(&P0[i], &P1[i])
		}
		checkPointwise(t, R, expected)
	})

	t.Run("Mul_x0_times_x1", func(t *testing.T) {
		size := 8
		P0 := makeLagrangePoly(2, 4, 6, 8, 10, 12, 14, 16)
		P1 := makeLagrangePoly(3, 3, 3, 3, 3, 3, 3, 3)

		C := expr.Col("x0").Mul(expr.Col("x1"))
		Pi := map[string]Polynomial{"x0": P0, "x1": P1}

		R, err := BuildPointwiseEvaluation(Pi, C, nil)
		if err != nil {
			t.Fatalf("EvalPointWise failed: %v", err)
		}

		expected := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			expected[i].Mul(&P0[i], &P1[i])
		}
		checkPointwise(t, R, expected)
	})

	t.Run("Combined_x0_mul_x1_add_x2_sub_x3", func(t *testing.T) {
		size := 8
		P0 := makeLagrangePoly(1, 2, 3, 4, 5, 6, 7, 8)
		P1 := makeLagrangePoly(2, 2, 2, 2, 2, 2, 2, 2)
		P2 := makeLagrangePoly(10, 10, 10, 10, 10, 10, 10, 10)
		P3 := makeLagrangePoly(1, 1, 1, 1, 1, 1, 1, 1)

		C := expr.Col("x0").Mul(expr.Col("x1")).
			Add(expr.Col("x2")).
			Sub(expr.Col("x3"))
		Pi := map[string]Polynomial{"x0": P0, "x1": P1, "x2": P2, "x3": P3}

		R, err := BuildPointwiseEvaluation(Pi, C, nil)
		if err != nil {
			t.Fatalf("EvalPointWise failed: %v", err)
		}

		expected := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			expected[i].Mul(&P0[i], &P1[i])
			expected[i].Add(&expected[i], &P2[i])
			expected[i].Sub(&expected[i], &P3[i])
		}
		checkPointwise(t, R, expected)
	})

	t.Run("Mul_then_sub_same_poly", func(t *testing.T) {
		size := 8
		P0 := makeLagrangePoly(0, 1, 2, 3, 5, 7, 11, 13)

		C := expr.Col("x0").Mul(expr.Col("x0")).Sub(expr.Col("x0"))
		Pi := map[string]Polynomial{"x0": P0}

		R, err := BuildPointwiseEvaluation(Pi, C, nil)
		if err != nil {
			t.Fatalf("EvalPointWise failed: %v", err)
		}

		expected := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			expected[i].Square(&P0[i])
			expected[i].Sub(&expected[i], &P0[i])
		}
		checkPointwise(t, R, expected)
	})

	t.Run("Sub_and_mul_three_terms", func(t *testing.T) {
		size := 8
		P0 := makeLagrangePoly(10, 9, 8, 7, 6, 5, 4, 3)
		P1 := makeLagrangePoly(1, 2, 3, 4, 5, 6, 7, 8)
		P2 := makeLagrangePoly(2, 2, 2, 2, 2, 2, 2, 2)

		C := expr.Col("x0").Sub(expr.Col("x1")).Mul(expr.Col("x2"))
		Pi := map[string]Polynomial{"x0": P0, "x1": P1, "x2": P2}

		R, err := BuildPointwiseEvaluation(Pi, C, nil)
		if err != nil {
			t.Fatalf("EvalPointWise failed: %v", err)
		}

		expected := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			expected[i].Sub(&P0[i], &P1[i])
			expected[i].Mul(&expected[i], &P2[i])
		}
		checkPointwise(t, R, expected)
	})
}

// setupPiSlice assigns Idx values to every leaf in E and returns _Pi []Polynomial,
// where _Pi[l.Idx] is the polynomial for leaf l drawn from Pi.
// This mirrors the setup done inside evalPointWiseInto.
func setupPiSlice(Pi map[string]Polynomial, E expr.Expr) []Polynomial {
	type varKey struct {
		name  string
		shift int
	}
	varToIdx := make(map[varKey]int)
	allLeaves := E.LeavesFull(expr.NewConfig())
	var unique []*expr.Leaf
	for _, l := range allLeaves {
		key := varKey{l.Name, l.Shift}
		if idx, ok := varToIdx[key]; ok {
			l.Idx = idx
		} else {
			l.Idx = len(unique)
			varToIdx[key] = l.Idx
			unique = append(unique, l)
		}
	}
	_Pi := make([]Polynomial, len(unique))
	for _, l := range unique {
		_Pi[l.Idx] = Pi[l.Name]
	}
	return _Pi
}

func TestEvaluateOnIthEntry(t *testing.T) {

	t.Run("Regular_x0sq_plus_x1", func(t *testing.T) {
		// E = x0^2 + x1; verify row-by-row against BuildPointwiseEvaluation
		size := 8
		P0 := makeLagrangePoly(1, 2, 3, 4, 5, 6, 7, 8)
		P1 := makeLagrangePoly(10, 20, 30, 40, 50, 60, 70, 80)
		Pi := map[string]Polynomial{"x0": P0, "x1": P1}
		E := expr.Col("x0").Pow(2).Add(expr.Col("x1"))

		_Pi := setupPiSlice(Pi, E)
		R, err := BuildPointwiseEvaluation(Pi, E, nil)
		if err != nil {
			t.Fatal(err)
		}
		for i := 0; i < size; i++ {
			got := E.EvaluateOnIthEntry(_Pi, i)
			if !got.Equal(&R[i]) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), R[i].String())
			}
		}
	})

	t.Run("ConstantPolynomial", func(t *testing.T) {
		// gamma is a constant polynomial (len==1); should always return gamma[0]
		size := 8
		P0 := makeLagrangePoly(3, 5, 7, 9, 11, 13, 15, 17)
		var gVal koalabear.Element
		gVal.SetUint64(42)
		Pi := map[string]Polynomial{"x0": P0, "gamma": {gVal}}
		E := expr.Col("x0").Sub(expr.Col("gamma"))

		_Pi := setupPiSlice(Pi, E)
		R, err := BuildPointwiseEvaluation(Pi, E, nil)
		if err != nil {
			t.Fatal(err)
		}
		for i := 0; i < size; i++ {
			got := E.EvaluateOnIthEntry(_Pi, i)
			if !got.Equal(&R[i]) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), R[i].String())
			}
		}
	})

	t.Run("ConstLeaf", func(t *testing.T) {
		// E = x0 - 3 where 3 is a Const leaf (not in Pi)
		size := 8
		var three koalabear.Element
		three.SetUint64(3)
		P0 := makeLagrangePoly(4, 5, 6, 7, 8, 9, 10, 11)
		Pi := map[string]Polynomial{"x0": P0}
		E := expr.Col("x0").Sub(expr.Const(three))

		_Pi := setupPiSlice(Pi, E)
		R, err := BuildPointwiseEvaluation(Pi, E, nil)
		if err != nil {
			t.Fatal(err)
		}
		for i := 0; i < size; i++ {
			got := E.EvaluateOnIthEntry(_Pi, i)
			if !got.Equal(&R[i]) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), R[i].String())
			}
		}
	})

	t.Run("ShiftedColumn", func(t *testing.T) {
		// E = x0(shift=1) - x0; should equal P0[(i+1)%N] - P0[i]
		size := 8
		P0 := makeLagrangePoly(1, 3, 2, 7, 5, 4, 6, 8)
		Pi := map[string]Polynomial{"x0": P0}
		E := expr.Col("x0", expr.WithShift(1)).Sub(expr.Col("x0"))

		_Pi := setupPiSlice(Pi, E)
		for i := 0; i < size; i++ {
			got := E.EvaluateOnIthEntry(_Pi, i)
			var want koalabear.Element
			want.Sub(&P0[(i+1)%size], &P0[i])
			if !got.Equal(&want) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), want.String())
			}
		}
	})

	t.Run("NegativeShift", func(t *testing.T) {
		// E = x0(shift=-1); should equal P0[(i-1+N)%N]
		size := 8
		P0 := makeLagrangePoly(2, 4, 6, 8, 10, 12, 14, 16)
		Pi := map[string]Polynomial{"x0": P0}
		E := expr.Col("x0", expr.WithShift(-1))

		_Pi := setupPiSlice(Pi, E)
		for i := 0; i < size; i++ {
			got := E.EvaluateOnIthEntry(_Pi, i)
			want := P0[(i-1+size)%size]
			if !got.Equal(&want) {
				t.Errorf("row %d: got %s, want %s", i, got.String(), want.String())
			}
		}
	})
}

func TestDivPointWise(t *testing.T) {

	t.Run("Simple", func(t *testing.T) {
		size := 8
		P1 := makeLagrangePoly(2, 4, 6, 8, 10, 12, 14, 16)
		P2 := makeLagrangePoly(2, 2, 2, 2, 2, 2, 2, 2)

		R, err := divPointwise(P1, P2, size)
		if err != nil {
			t.Fatal(err)
		}

		expected := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			expected[i].Div(&P1[i], &P2[i])
		}
		checkPointwise(t, R, expected)
	})

	t.Run("IdentityDenominator", func(t *testing.T) {
		size := 8
		P1 := makeLagrangePoly(3, 7, 11, 5, 2, 9, 6, 4)
		P2 := makeLagrangePoly(1, 1, 1, 1, 1, 1, 1, 1)

		R, err := divPointwise(P1, P2, size)
		if err != nil {
			t.Fatal(err)
		}
		checkPointwise(t, R, P1)
	})

	t.Run("EqualOperands", func(t *testing.T) {
		size := 8
		P1 := makeLagrangePoly(5, 3, 9, 2, 7, 11, 4, 6)
		P2 := makeLagrangePoly(5, 3, 9, 2, 7, 11, 4, 6)

		R, err := divPointwise(P1, P2, size)
		if err != nil {
			t.Fatal(err)
		}

		var one koalabear.Element
		one.SetOne()
		expected := make([]koalabear.Element, size)
		for i := range expected {
			expected[i] = one
		}
		checkPointwise(t, R, expected)
	})

	t.Run("DivisionByZero", func(t *testing.T) {
		size := 8
		P1 := makeLagrangePoly(1, 2, 3, 4, 5, 6, 7, 8)
		P2 := makeLagrangePoly(1, 0, 1, 1, 1, 1, 1, 1)

		_, err := divPointwise(P1, P2, size)
		if err == nil {
			t.Fatal("expected error for division by zero, got nil")
		}
	})
}

// func TestBuildGrandProduct(t *testing.T) {

// 	t.Run("IdentityRatio", func(t *testing.T) {
// 		size := 8
// 		P := makeLagrangePoly(2, 3, 4, 5, 6, 7, 8, 9)
// 		Pi := map[string]Polynomial{"x": P}
// 		E0 := expr.Col("x")
// 		E1 := expr.Col("x")

// 		R, err := BuildGrandProduct(Pi, E0, E1, size, nil)
// 		if err != nil {
// 			t.Fatal(err)
// 		}

// 		var one koalabear.Element
// 		one.SetOne()
// 		expected := make([]koalabear.Element, size)
// 		for i := range expected {
// 			expected[i] = one
// 		}
// 		checkPointwise(t, R, expected)
// 	})

// 	t.Run("SimpleRecurrence", func(t *testing.T) {
// 		size := 8
// 		P := makeLagrangePoly(2, 3, 4, 5, 6, 7, 8, 9)
// 		var one koalabear.Element
// 		one.SetOne()
// 		Pi := map[string]Polynomial{
// 			"x":   P,
// 			"one": []koalabear.Element{one},
// 		}
// 		E0 := expr.Col("x")
// 		E1 := expr.Col("one")

// 		R, err := BuildGrandProduct(Pi, E0, E1, size, nil)
// 		if err != nil {
// 			t.Fatal(err)
// 		}

// 		expected := make([]koalabear.Element, size)
// 		expected[0].SetOne()
// 		for i := 1; i < size; i++ {
// 			expected[i].Mul(&expected[i-1], &P[i-1])
// 		}
// 		checkPointwise(t, R, expected)
// 	})

// 	t.Run("FirstEntryAlwaysOne", func(t *testing.T) {
// 		size := 8
// 		P0 := makeLagrangePoly(7, 3, 11, 5, 2, 9, 4, 6)
// 		P1 := makeLagrangePoly(1, 2, 3, 4, 5, 6, 7, 8)
// 		Pi := map[string]Polynomial{"x": P0, "y": P1}
// 		E0 := expr.Col("x")
// 		E1 := expr.Col("y")

// 		R, err := BuildGrandProduct(Pi, E0, E1, size, nil)
// 		if err != nil {
// 			t.Fatal(err)
// 		}

// 		var one koalabear.Element
// 		one.SetOne()
// 		if !R[0].Equal(&one) {
// 			t.Errorf("R[0]: got %s, want 1", R[0].String())
// 		}
// 	})

// 	t.Run("Recurrence_check", func(t *testing.T) {
// 		size := 8
// 		P0 := makeLagrangePoly(6, 10, 3, 15, 2, 8, 5, 9)
// 		P1 := makeLagrangePoly(2, 5, 1, 3, 2, 4, 1, 3)
// 		Pi := map[string]Polynomial{"x": P0, "y": P1}
// 		E0 := expr.Col("x")
// 		E1 := expr.Col("y")

// 		R, err := BuildGrandProduct(Pi, E0, E1, size, nil)
// 		if err != nil {
// 			t.Fatal(err)
// 		}

// 		var one koalabear.Element
// 		one.SetOne()
// 		if !R[0].Equal(&one) {
// 			t.Errorf("R[0]: got %s, want 1", R[0].String())
// 		}

// 		for i := 0; i < size-1; i++ {
// 			var expected koalabear.Element
// 			expected.Mul(&R[i], &P0[i])
// 			expected.Div(&expected, &P1[i])
// 			if !R[i+1].Equal(&expected) {
// 				t.Errorf("R[%d]: got %s, want %s", i+1, R[i+1].String(), expected.String())
// 			}
// 		}
// 	})

// 	t.Run("DenominatorZero_error", func(t *testing.T) {
// 		size := 8
// 		P0 := makeLagrangePoly(1, 2, 3, 4, 5, 6, 7, 8)
// 		P1 := makeLagrangePoly(1, 0, 1, 1, 1, 1, 1, 1)
// 		Pi := map[string]Polynomial{"x": P0, "y": P1}
// 		E0 := expr.Col("x")
// 		E1 := expr.Col("y")

// 		_, err := BuildGrandProduct(Pi, E0, E1, size, nil)
// 		if err == nil {
// 			t.Fatal("expected error for zero denominator, got nil")
// 		}
// 	})
// }

func TestAccumulateProducts(t *testing.T) {

	t.Run("Simple", func(t *testing.T) {
		size := 8
		P := makeLagrangePoly(2, 3, 4, 5, 1, 1, 1, 1)

		R, err := accumulateProducts(P, size)
		if err != nil {
			t.Fatal(err)
		}

		expected := make([]koalabear.Element, size)
		expected[0].SetOne()
		for i := 1; i < size; i++ {
			expected[i].Mul(&expected[i-1], &P[i-1])
		}
		checkPointwise(t, R, expected)
	})

	t.Run("AllOnes", func(t *testing.T) {
		size := 8
		P := makeLagrangePoly(1, 1, 1, 1, 1, 1, 1, 1)

		R, err := accumulateProducts(P, size)
		if err != nil {
			t.Fatal(err)
		}

		var one koalabear.Element
		one.SetOne()
		expected := make([]koalabear.Element, size)
		for i := range expected {
			expected[i] = one
		}
		checkPointwise(t, R, expected)
	})

	t.Run("FirstEntryAlwaysOne", func(t *testing.T) {
		size := 8
		P := makeLagrangePoly(7, 3, 11, 5, 2, 9, 4, 6)

		R, err := accumulateProducts(P, size)
		if err != nil {
			t.Fatal(err)
		}

		var one koalabear.Element
		one.SetOne()
		if !R[0].Equal(&one) {
			t.Errorf("R[0]: got %s, want 1", R[0].String())
		}
	})

	t.Run("GrandProductInLastEntry", func(t *testing.T) {
		size := 8
		P := makeLagrangePoly(2, 3, 4, 5, 6, 7, 8, 9)

		R, err := accumulateProducts(P, size)
		if err != nil {
			t.Fatal(err)
		}

		var expected koalabear.Element
		expected.SetOne()
		for i := 0; i < size-1; i++ {
			expected.Mul(&expected, &P[i])
		}
		if !R[size-1].Equal(&expected) {
			t.Errorf("R[%d]: got %s, want %s", size-1, R[size-1].String(), expected.String())
		}
	})
}

func verifyQuotientIdentity(t *testing.T, Pi map[string]Polynomial, E expr.Expr, Q Polynomial, N int) {
	t.Helper()

	var x koalabear.Element
	x.SetRandom()

	// Evaluate each Pi[name] at x
	leaves := expr.RemoveDuplicates(E.Leaves(expr.NewConfig()))
	piAtX := make(map[string]koalabear.Element, len(leaves))
	for _, name := range leaves {
		piAtX[name] = evalLagrangeNormalAt(Pi[name], x)
	}

	// E(Pi(x))
	numeratorAtX := E.Evaluate(piAtX)

	// Convert Q from coset-Lagrange to Lagrange Normal, then to canonical, then evaluate
	qCopy := make([]koalabear.Element, len(Q))
	copy(qCopy, Q)
	CosetLagrangeToLagrangeNormal(qCopy)
	lagrangeNormalToCanonical(qCopy)
	qAtX := canonicalEval(qCopy, x)

	// x^N - 1
	var xN, one koalabear.Element
	one.SetOne()
	xN.Exp(x, big.NewInt(int64(N)))
	xN.Sub(&xN, &one)

	var rhs koalabear.Element
	rhs.Mul(&qAtX, &xN)
	if !numeratorAtX.Equal(&rhs) {
		t.Errorf("quotient identity failed: E(Pi(x)) = %s, Q(x)*(x^N-1) = %s",
			numeratorAtX.String(), rhs.String())
	}
}

// func TestBuildFilteredAccPolynomial(t *testing.T) {

// 	t.Run("AllOnesFilter_LastEntryIsHornerEval", func(t *testing.T) {
// 		// When F = [1, 1, ..., 1], the recurrence simplifies to
// 		//   R[0]   = E[0]
// 		//   R[i]   = alpha * R[i-1] + E[i]
// 		// so R[N-1] = E[0]*alpha^{N-1} + E[1]*alpha^{N-2} + ... + E[N-1],
// 		// i.e. the evaluation of E interpreted as a canonical polynomial
// 		// (E[0] = leading coefficient) at alpha.
// 		N := 8
// 		E := makeLagrangePoly(3, 7, 2, 11, 5, 9, 1, 4)
// 		F := makeLagrangePoly(1, 1, 1, 1, 1, 1, 1, 1)
// 		var alphaVal koalabear.Element
// 		alphaVal.SetUint64(5)

// 		Pi := map[string]Polynomial{
// 			"e":     E,
// 			"f":     F,
// 			"alpha": {alphaVal},
// 		}
// 		Eexpr := expr.Col("e")
// 		Fexpr := expr.Col("f")

// 		R, err := BuildFilteredAccPolynomial(Pi, Eexpr, Fexpr, expr.Challenge("alpha"), N, nil)
// 		if err != nil {
// 			t.Fatal(err)
// 		}

// 		// Compute expected = E[0]*alpha^{N-1} + ... + E[N-1] via forward Horner.
// 		expected := E[0]
// 		for i := 1; i < N; i++ {
// 			expected.Mul(&expected, &alphaVal)
// 			expected.Add(&expected, &E[i])
// 		}

// 		if !R[N-1].Equal(&expected) {
// 			t.Errorf("R[N-1] = %s, want %s", R[N-1].String(), expected.String())
// 		}
// 	})
// }

func TestComputeQuotient(t *testing.T) {

	t.Run("TrivialZero", func(t *testing.T) {
		size := 8
		P := makeLagrangePoly(1, 2, 3, 4, 5, 6, 7, 8)
		Pi := map[string]Polynomial{"f": P, "g": P}
		E := expr.Col("f").Sub(expr.Col("g"))
		EDag := dag.ExprToDAG(E)

		Q, err := ComputeQuotient(Pi, *EDag, size)
		if err != nil {
			t.Fatal(err)
		}

		// Convert to canonical to check all coefficients are zero
		qCopy := make([]koalabear.Element, len(Q))
		copy(qCopy, Q)
		CosetLagrangeToLagrangeNormal(qCopy)
		lagrangeNormalToCanonical(qCopy)
		for i, c := range qCopy {
			if !c.IsZero() {
				t.Errorf("quotient[%d] = %s, want 0", i, c.String())
			}
		}
	})

	t.Run("QuadraticRangeCheck", func(t *testing.T) {
		// E = f*(f-1): zero when f ∈ {0,1}
		size := 4
		var one koalabear.Element
		one.SetOne()
		P := makeLagrangePoly(0, 1, 0, 1)
		Pi := map[string]Polynomial{"f": P}

		var minusOne koalabear.Element
		minusOne.Neg(&one)
		E := expr.Col("f").Mul(expr.Col("f").Add(expr.Const(minusOne)))
		EDag := dag.ExprToDAG(E)

		Q, err := ComputeQuotient(Pi, *EDag, size)
		if err != nil {
			t.Fatal(err)
		}

		verifyQuotientIdentity(t, Pi, E, Q, size)
	})

	t.Run("ThreeVariable", func(t *testing.T) {
		// E = x0^3 + x1*x2 + x3, with x3 = -(x0^3 + x1*x2)
		size := 16

		c0 := make([]koalabear.Element, size)
		c1 := make([]koalabear.Element, size)
		c2 := make([]koalabear.Element, size)
		c3 := make([]koalabear.Element, size)
		for i := 0; i < size; i++ {
			c0[i].SetRandom()
			c1[i].SetRandom()
			c2[i].SetRandom()
		}

		trunc := expr.Col("x0").Pow(3).Add(expr.Col("x1").Mul(expr.Col("x2")))
		truncVals := make(map[string]koalabear.Element, 3)
		for i := 0; i < size; i++ {
			truncVals["x0"], truncVals["x1"], truncVals["x2"] = c0[i], c1[i], c2[i]
			c3[i] = trunc.Evaluate(truncVals)
			c3[i].Neg(&c3[i])
		}

		Pi := map[string]Polynomial{"x0": c0, "x1": c1, "x2": c2, "x3": c3}
		E := expr.Col("x0").Pow(3).
			Add(expr.Col("x1").Mul(expr.Col("x2"))).
			Add(expr.Col("x3"))
		EDag := dag.ExprToDAG(E)

		Q, err := ComputeQuotient(Pi, *EDag, size)
		if err != nil {
			t.Fatal(err)
		}

		verifyQuotientIdentity(t, Pi, E, Q, size)
	})

	t.Run("ConstantPiInRelation", func(t *testing.T) {
		// E = f - gamma with f = [3,3,...] and gamma = 3 → quotient = 0
		size := 8
		var three koalabear.Element
		three.SetUint64(3)

		P := makeLagrangePoly(3, 3, 3, 3, 3, 3, 3, 3)
		Pi := map[string]Polynomial{"f": P, "gamma": []koalabear.Element{three}}
		E := expr.Col("f").Sub(expr.Col("gamma"))
		EDag := dag.ExprToDAG(E)

		Q, err := ComputeQuotient(Pi, *EDag, size)
		if err != nil {
			t.Fatal(err)
		}

		qCopy := make([]koalabear.Element, len(Q))
		copy(qCopy, Q)
		CosetLagrangeToLagrangeNormal(qCopy)
		lagrangeNormalToCanonical(qCopy)
		for i, c := range qCopy {
			if !c.IsZero() {
				t.Errorf("quotient[%d] = %s, want 0", i, c.String())
			}
		}
	})
}
