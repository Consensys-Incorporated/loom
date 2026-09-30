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

// access is one memory access of a chip row: the tuple (addr, v0..v7) with
// multiplicity mult, positive for a write (the number of times the cell is
// read) and −1 for a read, 0 on rows that do not access.
type access struct {
	module string
	addr   expr.Expr
	vals   [CellWidth]expr.Expr
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
type Bus struct {
	accesses []access
}

// Write adds a write of vals at addr with multiplicity mult.
func (b *Bus) Write(module string, addr expr.Expr, vals [CellWidth]expr.Expr, mult expr.Expr) {
	b.accesses = append(b.accesses, access{module, addr, vals, mult})
}

// Read adds a read of vals at addr, active when sel is 1.
func (b *Bus) Read(module string, addr expr.Expr, vals [CellWidth]expr.Expr, sel expr.Expr) {
	var neg koalabear.Element
	neg.SetOne()
	neg.Neg(&neg)
	b.accesses = append(b.accesses, access{module, addr, vals, expr.Const(neg).Mul(sel)})
}

// Build adds the bus argument: the accessed values are committed at
// RoundFold, tuples are folded with Coin(RoundFold), and the accesses of each
// module are batched into cyclic logup columns at RoundRunningSums, whose
// totals must sum to zero.
func (b *Bus) Build(builder *board.Builder) error {
	alpha := board.Coin(board.RoundFold)
	gamma := board.Coin(board.RoundLogDerivative)
	var modules []string
	var terms []board.LogupTerm
	for _, a := range b.accesses {
		tuple := append([]expr.Expr{a.addr}, a.vals[:]...)
		builder.StageLeaves(board.RoundFold, tuple...)
		builder.StageLeaves(board.RoundFold, a.mult)
		modules = append(modules, a.module)
		terms = append(terms, board.LogupTerm{E: expr.Fold(alpha, tuple).Sub(gamma), M: a.mult})
	}
	totals, err := arguments.AddLogupColumns(builder, fmt.Sprintf("%s_bus_", constants.LOGUP), modules, terms)
	if err != nil {
		return fmt.Errorf("memory bus: %w", err)
	}
	builder.AddLogupBus(board.NewLogupBus(totals))
	return nil
}
