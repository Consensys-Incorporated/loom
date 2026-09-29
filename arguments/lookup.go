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

// Every lookup uses the same three rounds (see board/rounds.go):
//
//	board.RoundFold           stage the raw tables, and their multiplicities,
//	                          counted on the raw tuples
//	board.RoundLogDerivative  nothing staged; γ = Coin(RoundLogDerivative)
//	board.RoundRunningSums    the logup running sums, with tuples folded by
//	                          α = Coin(RoundFold)

import (
	"fmt"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
)

func Range(builder *board.Builder, S board.Column, bound uint64) error {

	// 1 - check if the range module for bound exists, if not, create it
	bound = ecc.NextPowerOfTwo(bound)
	rangeModuleName := constants.RangeModuleName(bound)
	_, ok := builder.Modules[rangeModuleName]
	if !ok {
		rangeModule := board.NewModule(constants.RangeModuleName(bound))
		rangeModule.N = int(bound)
		rangeModule.GenCol = append(rangeModule.GenCol, board.RangeColumnGen{Bound: bound})
		builder.AddModule(rangeModule)
	}
	T := board.Column{Module: rangeModuleName, In: expr.Col(constants.RangeColName(bound))}

	// 2 - add the lookup
	return Lookup(builder, S, T)
}

// LookupUnion argument that {S[0], S[1], ..} ⊂ {T[0], T[1], ..}
// len(S) and len(T) need not be equal.
func LookupUnion(builder *board.Builder, S, T []board.Column) error {
	return LookupUnionTuple(builder, columnsToTables(S), columnsToTables(T))
}

// LookupUnionTuple
// argument that {S[0], S[1], ..} ⊂ {T[0], T[1], ..}, where S[i], T[i] are tuples of columns
//
// for each i, len(S[i]) must be equal to len(T[i])
func LookupUnionTuple(builder *board.Builder, S, T []board.Table) error {
	if err := checkWidths(S, T); err != nil {
		return err
	}
	mult, err := stageLookup(builder, nil, nil, S, T)
	if err != nil {
		return err
	}
	one := expr.Const(koalabear.One())
	multT := make([]expr.Expr, len(T))
	selS := make([]expr.Expr, len(S))
	for i := range T {
		multT[i] = expr.Col(constants.MultiplicityChunkName(mult, i))
	}
	for i := range S {
		selS[i] = one
	}
	return addLogups(builder, foldTables(S), foldTables(T), selS, multT)
}

// CLookupUnion argues that {S[i] | selS[i] != 0} ⊂ {T[i] | selT[i] != 0}.
func CLookupUnion(builder *board.Builder, selS, selT []expr.Expr, S, T []board.Column) error {
	return CLookupUnionTuple(builder, selS, selT, columnsToTables(S), columnsToTables(T))
}

// CLookupUnionTuple argues that {row(S[i]) | selS[i] != 0} ⊂ {row(T[i]) | selT[i] != 0},
// where row(.) is the tuple of all columns of a table in a row.
func CLookupUnionTuple(builder *board.Builder, selS, selT []expr.Expr, S, T []board.Table) error {
	if len(selS) != len(S) {
		return fmt.Errorf("selS has %d chunks, but S has %d chunks", len(selS), len(S))
	}
	if len(selT) != len(T) {
		return fmt.Errorf("selT has %d chunks, but T has %d chunks", len(selT), len(T))
	}
	if err := checkWidths(S, T); err != nil {
		return err
	}
	wmult, err := stageLookup(builder, selS, selT, S, T)
	if err != nil {
		return err
	}
	multT := make([]expr.Expr, len(T))
	for i := range T {
		multT[i] = expr.Col(constants.MultiplicityChunkName(wmult, i)).Mul(selT[i])
	}
	return addLogups(builder, foldTables(S), foldTables(T), selS, multT)
}

// Lookup arguments that S ⊂ T
func Lookup(builder *board.Builder, S, T board.Column) error {
	return LookupUnion(builder, []board.Column{S}, []board.Column{T})
}

// LookupTuple lookup on table of width len(S)=len(T)
func LookupTuple(builder *board.Builder, S, T board.Table) error {
	if len(S.In) != len(T.In) {
		return fmt.Errorf("[LookupTuple] S and T must have equal size, got %d and %d", len(S.In), len(T.In))
	}
	return LookupUnionTuple(builder, []board.Table{S}, []board.Table{T})
}

func CLookup(builder *board.Builder, S, T board.Column, SelS, SelT expr.Expr) error {
	return CLookupUnion(builder, []expr.Expr{SelS}, []expr.Expr{SelT}, []board.Column{S}, []board.Column{T})
}

// CLookupTuple argues that { row(S) | SelS != 0 } is a subset of { row(T) | SelT != 0 }
// where row(.) denotes the tuple of all columns in a row.
func CLookupTuple(builder *board.Builder, S, T board.Table, selS, selT expr.Expr) error {
	return CLookupUnionTuple(builder, []expr.Expr{selS}, []expr.Expr{selT}, []board.Table{S}, []board.Table{T})
}

// stageLookup stages, at RoundFold, the raw tables and selectors of a lookup
// together with its multiplicity columns, counted on the raw tuples. It returns
// the multiplicity base name. selS and selT may be nil (all selectors 1).
func stageLookup(builder *board.Builder, selS, selT []expr.Expr, S, T []board.Table) (string, error) {
	mult, err := constants.RandomString(10)
	if err != nil {
		return "", err
	}
	mult = fmt.Sprintf("Mult_%s", mult)

	for _, tables := range [][]board.Table{S, T} {
		for _, t := range tables {
			builder.StageLeaves(board.RoundFold, t.In...)
		}
	}
	builder.StageLeaves(board.RoundFold, selS...)
	builder.StageLeaves(board.RoundFold, selT...)

	builder.AddLookupMultiplicityStep(board.RoundFold, selS, selT, tablesToTuples(S), tablesToTuples(T), mult)
	for i := range T {
		builder.StageColumns(board.RoundFold, constants.MultiplicityChunkName(mult, i))
	}
	return mult, nil
}

// MaxLogupBatch is the largest number of fractions summed by one logup
// column: three linear denominators give a degree-4 constraint (see
// board.LogupConstraintDegree).
const MaxLogupBatch = 3

// addLogups adds, at RoundRunningSums, the cyclic logup columns of the folded
// sources (fractions numS/(s − γ)) and targets (numT/(t − γ)), and balances
// their totals on a bus. Sources of the same module are batched by up to
// MaxLogupBatch per column, within board.MaxLogupDegree; each target gets its
// own column.
func addLogups(builder *board.Builder, S, T []board.Column, numS, numT []expr.Expr) error {
	gamma := board.Coin(board.RoundLogDerivative)
	positives, err := addLogupColumns(builder, S, numS, gamma, MaxLogupBatch)
	if err != nil {
		return err
	}
	negatives, err := addLogupColumns(builder, T, numT, gamma, 1)
	if err != nil {
		return err
	}
	builder.AddLogupBus(board.NewLogupBus(positives, negatives))
	return nil
}

// addLogupColumns groups the fractions num[i]/(cols[i] − γ) by module, in
// order, into logup columns of at most maxBatch fractions each, and returns
// the names of their exposed totals.
func addLogupColumns(builder *board.Builder, cols []board.Column, num []expr.Expr, gamma expr.Expr, maxBatch int) ([]string, error) {
	var order []string
	byModule := map[string][]board.LogupTerm{}
	for i, c := range cols {
		if _, ok := byModule[c.Module]; !ok {
			order = append(order, c.Module)
		}
		byModule[c.Module] = append(byModule[c.Module], board.LogupTerm{E: c.In.Sub(gamma), M: num[i]})
	}
	var totals []string
	for _, module := range order {
		terms := byModule[module]
		for len(terms) > 0 {
			n := 1
			for n < min(maxBatch, len(terms)) && board.LogupConstraintDegree(terms[:n+1]) <= board.MaxLogupDegree {
				n++
			}
			base, err := constants.RandomString(10)
			if err != nil {
				return nil, err
			}
			name := constants.LogupChunkName(fmt.Sprintf("%s.%s_%s", module, constants.LOGUP, base), 0)
			total, err := builder.AddCyclicLogupStep(board.RoundRunningSums, module, terms[:n], name)
			if err != nil {
				return nil, err
			}
			totals = append(totals, total)
			terms = terms[n:]
		}
	}
	return totals, nil
}

// foldTables folds each table into a single column with α = Coin(RoundFold).
// Width-1 tables are left as they are.
func foldTables(tables []board.Table) []board.Column {
	alpha := board.Coin(board.RoundFold)
	res := make([]board.Column, len(tables))
	for i, t := range tables {
		res[i].Module = t.Module
		if len(t.In) == 1 {
			res[i].In = t.In[0]
		} else {
			res[i].In = expr.Fold(alpha, t.In)
		}
	}
	return res
}

func checkWidths(S, T []board.Table) error {
	refWidth := len(S[0].In)
	for _, t := range append(append([]board.Table(nil), S...), T...) {
		if len(t.In) != refWidth {
			return fmt.Errorf("inconsistent width, expected %d, got %d", refWidth, len(t.In))
		}
	}
	return nil
}

func columnsToTables(cols []board.Column) []board.Table {
	res := make([]board.Table, len(cols))
	for i, c := range cols {
		res[i] = board.Table{Module: c.Module, In: []expr.Expr{c.In}}
	}
	return res
}

func tablesToTuples(tables []board.Table) [][]expr.Expr {
	res := make([][]expr.Expr, len(tables))
	for i, t := range tables {
		res[i] = t.In
	}
	return res
}
