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

package proof

import (
	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/field"
	fieldhash "github.com/consensys/loom/internal/hash"
)

type ExposedEntry struct {
	Idx      int
	Field    field.Kind
	Value    koalabear.Element
	ValueExt extensions.E6
}

func (e *ExposedEntry) SetBase(v koalabear.Element) {
	e.Field = field.Base
	e.Value.Set(&v)
	e.ValueExt = fieldhash.LiftBaseToExt(v)
}

func (e *ExposedEntry) SetExt(v extensions.E6) {
	e.Field = field.Ext
	e.ValueExt.Set(&v)
}

func (e ExposedEntry) ExtValue() extensions.E6 {
	if e.Field == field.Ext {
		return e.ValueExt
	}
	return fieldhash.LiftBaseToExt(e.Value)
}

type ExposedValue struct {
	Entries []ExposedEntry
}

// ExposedValues values made public by the prover
type ExposedValues map[string]ExposedValue

// LogupBus balances the logup columns of a log-derivative interaction (a
// lookup, a permutation, a memory bus). Each column sums fractions M/(E − γ)
// with signed numerators (a lookup target, for instance, has numerator
// −multiplicity), so the bus holds if the totals sum to zero:
// Σ_i Totals_i = 0.
type LogupBus struct {
	Totals []string // Totals[i] = name of the exposed total of the i-th logup column (proof.ExposedValues[name], one entry)
}
