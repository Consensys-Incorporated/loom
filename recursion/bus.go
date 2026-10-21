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

// Package recursion is a prototype of a loom-native recursion machine: a few
// fixed-width chips wired through a write-once memory, with the program (every
// address, multiplicity and flag) in setup columns. Its width does not depend
// on the proof being verified; only its row counts do.
package recursion

import (
	"fmt"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
)

// CellWidth is the number of base elements of a memory cell: a digest, or an
// E6 value in lanes 0..5, or a scalar in lane 0.
const CellWidth = 8

// access is one access of a chip row to a bus: a tuple with multiplicity
// mult, positive for a write (the number of times it is read) and −1 for a
// read, 0 on rows that do not access.
type access struct {
	module string
	tuple  []expr.Expr
	mult   expr.Expr
}

// Bus is the write-once memory: every address is written by exactly one chip
// row, with its read count as multiplicity, and each read is a −1 term. The
// accesses of all chips balance on one logup bus:
//
//	Σ_writes mult/(fold(addr, v) − γ) − Σ_reads 1/(fold(addr, v) − γ) = 0.
//
// The compiler assigns each address to a single write and counts its reads,
// and both are setup columns, so a read can only be balanced by the write of
// its address, with the same value.
//
// The tables (see Table) are read at indices computed during execution, on a
// second bus: each entry is written once, as the tuple (tag, i, v0..v7) for
// entry i of the table tag, with a witness multiplicity, its number of reads.
// Every entry of a table has an index below its length, so a read at another
// index, or with another table's tag, balances against no entry. The two
// buses are kept apart by being checked against zero separately: a fraction
// of one cannot balance a fraction of the other.
type Bus struct {
	accesses []access // the memory
	entries  []access // the tables
}

// Write adds a write of vals at addr with multiplicity mult.
func (b *Bus) Write(module string, addr expr.Expr, vals [CellWidth]expr.Expr, mult expr.Expr) {
	b.accesses = append(b.accesses, access{module, append([]expr.Expr{addr}, vals[:]...), mult})
}

// Read adds a read of vals at addr, active when sel is 1.
func (b *Bus) Read(module string, addr expr.Expr, vals [CellWidth]expr.Expr, sel expr.Expr) {
	b.accesses = append(b.accesses, access{module, append([]expr.Expr{addr}, vals[:]...), negate(sel)})
}

// WriteEntry adds the write of vals as entry idx of the table tag, with
// multiplicity mult.
func (b *Bus) WriteEntry(module string, tag, idx expr.Expr, vals [CellWidth]expr.Expr, mult expr.Expr) {
	b.entries = append(b.entries, access{module, append([]expr.Expr{tag, idx}, vals[:]...), mult})
}

// ReadEntry adds a read of vals as entry idx of the table tag, active when sel
// is 1.
func (b *Bus) ReadEntry(module string, tag, idx expr.Expr, vals [CellWidth]expr.Expr, sel expr.Expr) {
	b.entries = append(b.entries, access{module, append([]expr.Expr{tag, idx}, vals[:]...), negate(sel)})
}

func negate(e expr.Expr) expr.Expr {
	var neg koalabear.Element
	neg.SetOne()
	neg.Neg(&neg)
	return expr.Const(neg).Mul(e)
}

// Build adds the bus arguments, the memory's and (if any) the tables': the
// accessed values are committed at RoundFold, tuples are folded with
// Coin(RoundFold), and the accesses of each module are batched into cyclic
// logup columns at RoundRunningSums, whose totals must sum to zero, for each
// bus on its own.
func (b *Bus) Build(builder *board.Builder) error {
	if err := buildBus(builder, "bus", b.accesses); err != nil {
		return fmt.Errorf("memory bus: %w", err)
	}
	if len(b.entries) == 0 {
		return nil
	}
	if err := buildBus(builder, "tables", b.entries); err != nil {
		return fmt.Errorf("tables bus: %w", err)
	}
	return nil
}

func buildBus(builder *board.Builder, name string, accesses []access) error {
	alpha := board.Coin(board.RoundFold)
	gamma := board.Coin(board.RoundLogDerivative)
	var terms []board.LogupTerm
	for _, a := range accesses {
		builder.StageLeaves(board.RoundFold, a.tuple...)
		builder.StageLeaves(board.RoundFold, a.mult)
		terms = append(terms, board.LogupTerm{Module: a.module, E: expr.Fold(alpha, a.tuple).Sub(gamma), M: a.mult})
	}
	totals, err := arguments.AddLogupColumns(builder, fmt.Sprintf("%s_%s_", constants.LOGUP, name), terms)
	if err != nil {
		return err
	}
	builder.AddLogupBus(board.NewLogupBus(totals))
	return nil
}
