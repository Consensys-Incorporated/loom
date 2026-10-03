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
	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
)

// Cell layouts: an E6 value in lanes 0..5 (B0.A0, B0.A1, B1.A0, B1.A1, B2.A0,
// B2.A1), a scalar in lane 0. The other lanes are zero, which every reader
// enforces through the constants of its tuple. A scalar cell is also the E6
// cell of its base-field embedding.

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

// Item lengths of the window chip.
const (
	KindScalar = 1
	KindE6     = 6
	KindDigest = 8
)
