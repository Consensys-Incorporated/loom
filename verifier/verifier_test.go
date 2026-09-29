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

package verifier

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/protocol"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/trace"
)

func TestVerifyMixedTraceRoundTrip(t *testing.T) {
	program, tr := mixedTraceRoundFixture(t)
	layout := protocol.BuildLayout(program, 0)
	traceTreeIdx := mixedTraceTreeIndex(t, layout)

	oldTraceTrees, nonEmptyTraceRounds := legacyTraceTreeCount(program)
	newTraceTrees := 0
	for r := range layout.TraceBegin {
		newTraceTrees += layout.TraceEnd[r] - layout.TraceBegin[r]
	}
	if oldTraceTrees <= newTraceTrees {
		t.Fatalf("fixture has %d old trace trees and %d new trace trees; want a real compaction", oldTraceTrees, newTraceTrees)
	}
	if newTraceTrees != nonEmptyTraceRounds {
		t.Fatalf("new trace tree count = %d, want one per non-empty round (%d)", newTraceTrees, nonEmptyTraceRounds)
	}

	prf, err := prover.Prove(tr, setup.ProvingKey{}, nil, program)
	if err != nil {
		t.Fatal(err)
	}

	airTrees := layout.AIREnd - layout.AIRBegin
	if got, want := len(prf.Commitments), newTraceTrees+airTrees; got != want {
		t.Fatalf("proof commitments = %d, want %d", got, want)
	}
	if err := Verify(nil, setup.VerificationKey{}, program, prf); err != nil {
		t.Fatal(err)
	}

	requireMixedTraceInjection(t, prf, traceTreeIdx)
	tamperMixedTraceInjection(t, &prf, traceTreeIdx)
	if err := Verify(nil, setup.VerificationKey{}, program, prf); err == nil {
		t.Fatal("expected verifier to reject a tampered mixed-trace injection row")
	}
}

func mixedTraceRoundFixture(t *testing.T) (board.Program, trace.Trace) {
	t.Helper()

	builder := board.NewBuilder()

	n := 4
	fibonacciModule := board.NewModule("fibonacci")
	fibonacciModule.N = n
	fibonacciModule.AssertZeroExceptAt(expr.Col("A", expr.WithShift(1)).Sub(expr.Col("B")), n-1)
	fibonacciModule.AssertZeroExceptAt(expr.Col("B", expr.WithShift(1)).Sub(expr.Col("C")), n-1)
	fibonacciModule.AssertZero(expr.Col("C").Sub(expr.Col("A")).Sub(expr.Col("B")))

	rangeModule := board.NewModule("range")
	rangeModule.N = 2 * n

	builder.AddModule(fibonacciModule)
	builder.AddModule(rangeModule)

	target := board.Column{
		Module: "range",
		In:     expr.Col("Lookup"),
	}
	for _, name := range []string{"A", "B", "C"} {
		source := board.Column{
			Module: "fibonacci",
			In:     expr.Col(name),
		}
		if err := arguments.Lookup(&builder, source, target); err != nil {
			t.Fatal(err)
		}
	}

	program, err := board.Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}

	var a, b koalabear.Element
	b.SetOne()
	return program, prover.MergeTrace(prover.TraceFibonacci(n, a, b), prover.TraceRange(n))
}

func mixedTraceTreeIndex(t *testing.T, layout protocol.Layout) int {
	t.Helper()

	for r := range layout.TraceBegin {
		if layout.TraceEnd[r]-layout.TraceBegin[r] != 1 {
			continue
		}
		treeIdx := layout.TraceBegin[r]
		if len(layout.TreeGroups[treeIdx]) > 1 {
			return treeIdx
		}
	}
	t.Fatal("fixture did not produce a mixed-size trace tree")
	return -1
}

func legacyTraceTreeCount(program board.Program) (oldTraceTrees, nonEmptyRounds int) {
	for _, round := range program.Rounds {
		sizes := make(map[int]bool)
		for _, dep := range round.Staged {
			module, ok := program.Modules[dep.Module]
			if ok {
				sizes[module.N] = true
			}
		}
		oldTraceTrees += len(sizes)
		if len(sizes) > 0 {
			nonEmptyRounds++
		}
	}
	return oldTraceTrees, nonEmptyRounds
}

func requireMixedTraceInjection(t *testing.T, prf proof.Proof, treeIdx int) {
	t.Helper()

	if len(prf.Opening.PointSamplings) == 0 {
		t.Fatal("proof has no point samplings")
	}
	if treeIdx >= len(prf.Opening.PointSamplings[0]) {
		t.Fatalf("trace tree index %d out of point-sampling range %d", treeIdx, len(prf.Opening.PointSamplings[0]))
	}
	if len(prf.Opening.PointSamplings[0][treeIdx].Injections) == 0 {
		t.Fatalf("trace tree %d has no injected rows", treeIdx)
	}
}

func tamperMixedTraceInjection(t *testing.T, prf *proof.Proof, treeIdx int) {
	t.Helper()

	injection := &prf.Opening.PointSamplings[0][treeIdx].Injections[0]
	if len(injection.Rows.Hi.RawRowBase) > 0 {
		injection.Rows.Hi.RawRowBase[0].SetUint64(0xdeadbeef)
		return
	}
	if len(injection.Rows.Lo.RawRowBase) > 0 {
		injection.Rows.Lo.RawRowBase[0].SetUint64(0xdeadbeef)
		return
	}
	t.Fatalf("trace tree %d injection has no base row to tamper", treeIdx)
}
