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

package recursion

import (
	"fmt"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
)

// Cell layouts: an E6 value in lanes 0..5 (B0.A0, B0.A1, B1.A0, B1.A1, B2.A0,
// B2.A1), a scalar in lane 0. A scalar cell is also the E6 cell of its
// base-field embedding.
//
// Every cell has a kind (scalar, E6 or digest), and its lanes from its kind on
// are zero, enforced by its writer, whatever reads it: a reader may use more
// lanes than the kind it reads (an E6 operation reads lanes 0..5 of a scalar),
// and the bus only balances a read against the write's exact 8 lanes. The
// witness chip constrains the lanes of the cells the prover writes (inputs,
// hints); the window chip writes Lanes outputs zero beyond their kind; the
// other chips write their kind's tuple (zero constants beyond it).

// E6Cell returns the cell of x.
func E6Cell(x ext.E6) Cell {
	return Cell{x.B0.A0, x.B0.A1, x.B1.A0, x.B1.A1, x.B2.A0, x.B2.A1}
}

// CellE6 returns the E6 value of a cell (lanes 0..5).
func CellE6(c Cell) ext.E6 {
	var x ext.E6
	x.B0.A0, x.B0.A1, x.B1.A0, x.B1.A1, x.B2.A0, x.B2.A1 = c[0], c[1], c[2], c[3], c[4], c[5]
	return x
}

// ScalarCell returns the cell of v.
func ScalarCell(v koalabear.Element) Cell { return Cell{v} }

const (
	roleNone = iota
	roleRead
	roleWrite
)

// slot is one memory access of a chip row.
type slot struct {
	addr, role int
}

func (m *Machine) rd(addr int) slot { m.read(addr); return slot{addr, roleRead} }

func (m *Machine) wr() slot { return slot{m.alloc(), roleWrite} }

// mult is the signed bus multiplicity of s: −1 for a read, the read count for
// a write.
func (m *Machine) mult(s slot) int64 {
	switch s.role {
	case roleRead:
		return -1
	case roleWrite:
		return int64(m.reads[s.addr])
	}
	return 0
}

// Kinds: the number of lanes of a cell or of an item. Cells are of the three
// kinds below; an item (a window of a stream) may have any kind from 1 to
// CellWidth.
const (
	KindScalar = 1
	KindE6     = 6
	KindDigest = 8
)

// checkCellKind panics unless k is the kind of a cell.
func checkCellKind(k int) {
	if k != KindScalar && k != KindE6 && k != KindDigest {
		panic(fmt.Sprintf("cell kind %d", k))
	}
}

// typedCell is a cell the witness chip writes, with its kind.
type typedCell struct {
	addr, kind int
}

// cellKindOf returns the narrowest cell kind holding c: the kind of an input
// given by its value (tests).
func cellKindOf(c Cell) int {
	kind := KindScalar
	for i := CellWidth - 1; i > 0; i-- {
		if !c[i].IsZero() {
			if i >= KindE6 {
				return KindDigest
			}
			kind = KindE6
		}
	}
	return kind
}
