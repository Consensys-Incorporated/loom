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

package arguments

import (
	"fmt"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
)

// PermutationCrossModules we use the lookup in this case, so that each module has its own logup
func PermutationCrossModules(builder *board.Builder, A, B board.Column) error {

	// 1. commit A and B, and use the log-derivative challenge
	builder.StageLeaves(board.RoundFold, A.In, B.In)
	gamma := board.Coin(board.RoundLogDerivative)

	// 2. register lookup for both parties
	prefixLogup := "logup"
	_logupA, err := constants.RandomString(10)
	if err != nil {
		return err
	}
	_logupB, err := constants.RandomString(10)
	if err != nil {
		return err
	}
	_logupA = fmt.Sprintf("%s.%s_%s", A.Module, prefixLogup, _logupA)
	_logupB = fmt.Sprintf("%s.%s_%s", B.Module, prefixLogup, _logupB)
	{
		aMinusGamma := A.In.Sub(gamma)
		builder.AddLogupStep(board.RoundRunningSums, A.Module, aMinusGamma, expr.Const(koalabear.One()), _logupA)
	}
	{
		bMinusGamma := B.In.Sub(gamma)
		builder.AddLogupStep(board.RoundRunningSums, B.Module, bMinusGamma, expr.Const(koalabear.One()), _logupB)
	}

	// 3. Check logup relation
	logupA := board.Column{Module: A.Module, In: expr.Col(_logupA)}
	logupB := board.Column{Module: B.Module, In: expr.Col(_logupB)}
	AddLogupEqualityCheck(builder, []board.Column{logupA}, []board.Column{logupB})

	return nil
}

// PermutationWithinModule we use the grand product argument in that case, it saves a column (1 grand product instead of 2 logups+bus)
// Generates an argument to prove that (A[0] || A[1] || ..) and (B[0] || B[1] || ..) are equal up to permutation
func PermutationWithinModule(builder *board.Builder, module string, A, B []expr.Expr) error {

	// 1. commit A and B, and use the log-derivative challenge
	builder.StageLeaves(board.RoundFold, A...)
	builder.StageLeaves(board.RoundFold, B...)
	gamma := board.Coin(board.RoundLogDerivative)

	// 2. register permutation
	AminusGamma := make([]expr.Expr, len(A))
	BminusGamma := make([]expr.Expr, len(B))
	for i, a := range A {
		AminusGamma[i] = a.Sub(gamma)
	}
	for i, b := range B {
		BminusGamma[i] = b.Sub(gamma)
	}
	_gp, err := constants.RandomString(10)
	if err != nil {
		return err
	}
	Amul := AminusGamma[0]
	Bmul := BminusGamma[0]
	for i := 1; i < len(AminusGamma); i++ {
		Amul = Amul.Mul(AminusGamma[i])
	}
	for i := 1; i < len(BminusGamma); i++ {
		Bmul = Bmul.Mul(BminusGamma[i])
	}
	builder.AddGrandProductStep(board.RoundRunningSums, module, Amul, Bmul, _gp)
	m := builder.Modules[module]
	m.AssertEqualAt(expr.Const(koalabear.One()), expr.Col(_gp), 0)
	builder.Modules[module] = m

	return nil
}

// PermutationTupleWithinModule
// Generates an argument to prove that
// (A[0][0] || A[1][0] || A[2][0] || ..) |
// (A[0][1] || A[1][1] || A[2][1] || ..) | <- the rows are folded
// (A[0][2] || A[1][2] || A[2][2] || ..) |
// ..
// and
// (B[0][0] || B[1][0] || B[2][0] || ..) |
// (B[0][1] || B[1][1] || B[2][1] || ..) | <- the rows are folded
// (B[0][2] || B[1][2] || B[2][2] || ..) |
// are equal up to permutation
// The rows of each matrix are folded, and we call PermutationWithinModule afterwards
func PermutationTupleWithinModule(builder *board.Builder, module string, A, B [][]expr.Expr) error {

	// 1. fold the rows with α = Coin(RoundFold); PermutationWithinModule
	// commits the raw columns at RoundFold.
	alpha := board.Coin(board.RoundFold)
	foldedA := make([]expr.Expr, len(A))
	foldedB := make([]expr.Expr, len(B))
	for i := 0; i < len(A); i++ { // A and B must be of the same size
		foldedA[i] = expr.Fold(alpha, A[i])
		foldedB[i] = expr.Fold(alpha, B[i])
	}

	// 2. call 1 dimensional permutation
	return PermutationWithinModule(builder, module, foldedA, foldedB)
}

// CopyConstraint copy constraint argument from plonk, ensuring that (A[0] || A[1] || .. ) is invariant when
// permuted by S.
// Syntactic sugar for FixedPermutationWithinModule
func CopyConstraint(builder *board.Builder, module string, A []expr.Expr, S board.PermutationGen) error {

	// 1 - register the permutation in the module
	m := builder.Modules[module]
	if m.N*len(A) != len(S.S) {
		return fmt.Errorf("m.N*len(A) must be equal to len(S.S), got %d, %d, %d", m.N, len(A), len(S.S))
	}
	m.GenCol = append(m.GenCol, S)

	// 2 - add the support of the permutation + the interpolation of the permutation to A and B
	AID := make([][]expr.Expr, len(A))
	APermuted := make([][]expr.Expr, len(A))
	for i := 0; i < len(A); i++ {

		AID[i] = make([]expr.Expr, 2)
		AID[i][0] = A[i]
		AID[i][1] = expr.Col(m.NameIthIDSupport(i))

		APermuted[i] = make([]expr.Expr, 2)
		APermuted[i][0] = A[i]
		APermuted[i][1] = expr.Col(S.NameIthPermutationChunk(i))

	}

	// 3 - the case is now reduced to PermutationTupleWithinModule
	return PermutationTupleWithinModule(builder, module, AID, APermuted)
}

// FixedPermutationWithinModule
func FixedPermutationWithinModule(builder *board.Builder, module string, A, B [][]expr.Expr, S board.PermutationGen) error {

	// 1 - register the permutation in the module
	m := builder.Modules[module]
	if m.N*len(A) != len(S.S) {
		return fmt.Errorf("m.N*len(A) must be equal to len(S.S), got %d, %d, %d", m.N, len(A), len(S.S))
	}
	m.GenCol = append(m.GenCol, S)

	// 2 - add the support of the permutation + the interpolation of the permutation to A and B
	APrime := make([][]expr.Expr, len(A))
	BPrime := make([][]expr.Expr, len(B))
	if len(A) != len(B) {
		return fmt.Errorf("len(A) must equal len(B), got respectively %d and %d", len(A), len(B))
	}
	for i := 0; i < len(A); i++ {
		APrime[i] = make([]expr.Expr, len(A[i])+1)
		BPrime[i] = make([]expr.Expr, len(B[i])+1)
		copy(APrime[i], A[i])
		copy(BPrime[i], B[i])
		APrime[i][len(A[i])] = expr.Col(m.NameIthIDSupport(i))
		BPrime[i][len(B[i])] = expr.Col(S.NameIthPermutationChunk(i))
	}

	// 3 - the case is now reduced to PermutationTupleWithinModule
	return PermutationTupleWithinModule(builder, module, APrime, BPrime)
}
