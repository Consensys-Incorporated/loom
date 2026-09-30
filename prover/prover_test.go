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

package prover

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/setup"
)

func TestVanishingRelationsAndLogupBus(t *testing.T) {

	builder := board.NewBuilder()

	fibonacciModule := board.NewModule("fibonacci")
	rangeModule := board.NewModule("range")

	N := 4
	fibonacciModule.N = N
	rangeModule.N = 2 * N

	C := expr.Col("A", expr.WithShift(1)).Sub(expr.Col("B"))
	fibonacciModule.AssertZeroExceptAt(C, N-1)
	C = expr.Col("B", expr.WithShift(1)).Sub(expr.Col("C"))
	fibonacciModule.AssertZeroExceptAt(C, N-1)
	C = expr.Col("C").Sub(expr.Col("A")).Sub(expr.Col("B"))
	fibonacciModule.AssertZero(C)

	builder.AddModule(fibonacciModule)
	builder.AddModule(rangeModule)

	T := board.Column{
		Module: "range",
		In:     expr.Col("Lookup"),
	}
	columnsFibonacci := []string{"A", "B", "C"}
	for _, c := range columnsFibonacci {
		S := board.Column{
			Module: "fibonacci",
			In:     expr.Col(c),
		}
		err := arguments.Lookup(&builder, S, T)
		if err != nil {
			t.Fatal(err)
		}
	}

	program, err := board.Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}

	// load the traces
	var a, b koalabear.Element
	b.SetOne()
	traceFrob := TraceFibonacci(N, a, b)
	traceRange := TraceRange(N)
	tr := MergeTrace(traceFrob, traceRange)

	proof, err := Prove(tr, setup.ProvingKey{}, nil, program)
	if err != nil {
		t.Fatal(err)
	}

	for _, m := range program.Modules {
		if err := CheckVanishingRelation(tr, m); err != nil {
			t.Fatal(err)
		}
	}

	// check the values of the bus
	for _, bus := range program.LogupBus {
		var sum koalabear.Element
		for _, name := range bus.Totals {
			if len(proof.ExposedValues[name].Entries) > 1 {
				t.Fatal("an extracted value from a logup column should have exactly one entry")
			}
			pe := proof.ExposedValues[name].Entries[0]
			sum.Add(&sum, &pe.Value)
		}
		if !sum.IsZero() {
			t.Fatal("the logup totals of the bus do not sum to zero")
		}
	}

}
