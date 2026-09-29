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

package board

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
)

func TestCompileColumnFields(t *testing.T) {
	builder := NewBuilder()
	module := NewModule("m")
	module.N = 4
	module.AssertZero(expr.Col("x").Sub(expr.Col("y")))
	builder.AddModule(module)

	program, err := Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}

	if got := program.ColumnFields["x"]; got != field.Base {
		t.Fatalf("x field = %s, want %s", got, field.Base)
	}
	if got := program.ColumnFields["y"]; got != field.Base {
		t.Fatalf("y field = %s, want %s", got, field.Base)
	}
	if got := program.ColumnFields[constants.CanonicalChallengeName(0)]; got != field.Ext {
		t.Fatalf("folding challenge field = %s, want %s", got, field.Ext)
	}
}

func TestCompileColumnFieldsForChallengeDerivedOutputs(t *testing.T) {
	var one koalabear.Element
	one.SetOne()

	builder := NewBuilder()
	module := NewModule("m")
	module.N = 4
	builder.AddModule(module)

	builder.StageColumns(RoundFold, "x", "y")
	denominator := expr.Col("x").Sub(Coin(RoundLogDerivative))
	builder.AddLogupStep(RoundRunningSums, "m", denominator, expr.Const(one), "logup")
	builder.AddGrandProductStep(RoundRunningSums, "m", expr.Col("x").Add(Coin(RoundFold)), expr.Col("y"), "gp")
	builder.AddExposeLastEntryStep(RoundRunningSums, "m", expr.Col("logup"), "public_logup")

	program, err := Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}

	for _, name := range []string{"logup", "gp", "public_logup"} {
		if got := program.ColumnFields[name]; got != field.Ext {
			t.Fatalf("%s field = %s, want %s", name, got, field.Ext)
		}
	}

	for _, round := range program.Rounds {
		for _, dep := range round.Staged {
			if dep.Name == "logup" && dep.Field != field.Ext {
				t.Fatalf("FS dependency logup field = %s, want %s", dep.Field, field.Ext)
			}
		}
	}
}
