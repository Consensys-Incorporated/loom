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

import "github.com/consensys/loom/board"

// Const returns the address of a constant cell of value v, written by the
// const chip (its values are setup columns). Constants are shared.
func (m *Machine) Const(v Cell) int {
	if a, ok := m.consts[v]; ok {
		return a
	}
	if m.consts == nil {
		m.consts, m.constVal = map[Cell]int{}, map[int]Cell{}
	}
	a := m.alloc()
	m.consts[v] = a
	m.constVal[a] = v
	m.constList = append(m.constList, a)
	return a
}

// constChip: one row per constant cell, all setup: addr, mult, v0..v7.
type constChip struct{ m *Machine }

func (c constChip) name() string { return constMod }

func (c constChip) rows() int { return len(c.m.constList) }

func (c constChip) define(b *board.Builder, bus *Bus) error {
	bus.Write(constMod, setupCol(constMod, "addr"), setupCellCols(constMod, "v"), setupCol(constMod, "mult"))
	return nil
}

func (c constChip) setup(cs *cols) {
	cs.declare("addr", "mult")
	cs.declareLanes("v", CellWidth)
	for row, a := range c.m.constList {
		cs.set("addr", row, uint64(a))
		cs.set("mult", row, uint64(c.m.reads[a]))
		cs.setCell("v", row, c.m.constVal[a])
	}
}

func (c constChip) trace(*cols, *Run) error { return nil }
