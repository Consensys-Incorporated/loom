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

	"github.com/consensys/loom/board"
)

// Setup columns of the table chip.
const (
	tableActive  = "active"
	tableSrcAddr = "src_addr"
	tableAddr    = "addr"
)

// Witness columns of the table chip.
const (
	tableCnt = "cnt"
	tableV   = "v" // lanes
)

// Setup columns of the lookup chip.
const (
	lookupActive  = "active"
	lookupIdxAddr = "idx_addr"
	lookupBase    = "base"
	lookupOutAddr = "out_addr"
	lookupOutMult = "out_mult"
)

// Witness columns of the lookup chip.
const (
	lookupIdx = "idx"
	lookupV   = "v" // lanes
)

// Dynamic reads. A table copies cells to n consecutive fresh addresses, base
// to base + n − 1; a lookup reads the entry at base + idx, an address computed
// in the circuit from the index cell idx. How often each entry is read
// depends on the execution, so the entries' write multiplicities are witness
// columns: the bus is then a lookup argument over the entries, and a dynamic
// read balances only against the entry of its address, with its value.
//
// The index must be below the table's length: out of range, the address
// would be that of an unrelated cell. Such a read cannot balance against a
// cell whose multiplicity is setup, but could against an entry of another
// table. Callers take indices from a producer that bounds them, such as Bits
// (Shr[i] < 2^(n−i)); execution rejects an index out of range.

// Table is a table of cells readable at a computed index.
type Table struct {
	base    int
	entries []int // base, base + 1, ...
}

// Len returns the number of entries.
func (t Table) Len() int { return len(t.entries) }

type tableInst struct {
	src     []int // the copied cells
	entries []int
}

type lookupInst struct {
	table    int // index in Machine.tables
	idx, out int
}

// Table returns a table whose entry i holds the value of cells[i].
func (m *Machine) Table(cells []int) Table {
	if len(cells) == 0 {
		panic("Table: no cell")
	}
	for _, c := range cells {
		m.read(c)
	}
	entries := make([]int, len(cells))
	for i := range entries {
		entries[i] = m.alloc() // consecutive: nothing else allocates meanwhile
	}
	m.tables = append(m.tables, tableInst{src: cells, entries: entries})
	m.record(instrTable, len(m.tables)-1)
	return Table{base: entries[0], entries: entries}
}

// Lookup returns a cell holding table[idx], for a scalar cell idx whose value
// is below the table's length (see the bound above).
func (m *Machine) Lookup(t Table, idx int) int {
	k := -1
	for i, ti := range m.tables {
		if ti.entries[0] == t.base {
			k = i
		}
	}
	if k < 0 {
		panic("Lookup: unknown table")
	}
	m.read(idx)
	out := m.alloc()
	m.lookups = append(m.lookups, lookupInst{table: k, idx: idx, out: out})
	m.record(instrLookup, len(m.lookups)-1)
	return out
}

func (m *Machine) execTable(t tableInst, r *Run) {
	for i, c := range t.src {
		r.values[t.entries[i]] = r.values[c]
	}
}

func (m *Machine) execLookup(l lookupInst, r *Run) error {
	t := m.tables[l.table]
	i := r.values[l.idx][0].Uint64()
	if i >= uint64(len(t.entries)) {
		return fmt.Errorf("Lookup: index %d out of a table of %d entries", i, len(t.entries))
	}
	r.values[l.out] = r.values[t.entries[i]]
	return nil
}

// tableChip: one row per table entry.
//
// Columns: v0..7 (the value), cnt (how many lookups read the entry). Setup:
// active, src_addr (the copied cell, read), addr (the entry's address,
// written with multiplicity cnt).
type tableChip struct{ m *Machine }

func (c tableChip) name() string { return tableMod }

func (c tableChip) rows() int {
	n := 0
	for _, t := range c.m.tables {
		n += len(t.entries)
	}
	return n
}

func (c tableChip) define(b *board.Builder, bus *Bus) error {
	v := cellCols(tableMod, tableV, 0)
	bus.Read(tableMod, setupCol(tableMod, tableSrcAddr), v, setupCol(tableMod, tableActive))
	bus.Write(tableMod, setupCol(tableMod, tableAddr), v, col(tableMod, tableCnt))
	return nil
}

func (c tableChip) setup(cs *cols) {
	cs.declare(tableActive, tableSrcAddr, tableAddr)
	row := 0
	for _, t := range c.m.tables {
		for i, e := range t.entries {
			cs.set(tableActive, row, 1)
			cs.set(tableSrcAddr, row, uint64(t.src[i]))
			cs.set(tableAddr, row, uint64(e))
			row++
		}
	}
}

// trace fills the values and counts the lookups of every entry.
func (c tableChip) trace(cs *cols, r *Run) error {
	cs.declare(tableCnt)
	cs.declareLanes(tableV, CellWidth)
	counts := make([][]uint64, len(c.m.tables))
	for k, t := range c.m.tables {
		counts[k] = make([]uint64, len(t.entries))
	}
	for _, l := range c.m.lookups {
		counts[l.table][r.values[l.idx][0].Uint64()]++
	}
	row := 0
	for k, t := range c.m.tables {
		for i, e := range t.entries {
			cs.setCell(tableV, row, r.values[e])
			cs.set(tableCnt, row, counts[k][i])
			row++
		}
	}
	return nil
}

// lookupChip: one row per lookup.
//
// Columns: idx (the index), v0..7 (the entry read). Setup: active, idx_addr
// (the index cell, read), base (the table's first address), out_addr and
// out_mult (the result cell, written). The entry is read at the address
// base + idx.
type lookupChip struct{ m *Machine }

func (c lookupChip) name() string { return lookupMod }
func (c lookupChip) rows() int    { return len(c.m.lookups) }

func (c lookupChip) define(b *board.Builder, bus *Bus) error {
	active, idx := setupCol(lookupMod, lookupActive), col(lookupMod, lookupIdx)
	v := cellCols(lookupMod, lookupV, 0)
	bus.Read(lookupMod, setupCol(lookupMod, lookupIdxAddr), cellOf(idx), active)
	bus.Read(lookupMod, setupCol(lookupMod, lookupBase).Add(idx), v, active)
	bus.Write(lookupMod, setupCol(lookupMod, lookupOutAddr), v, setupCol(lookupMod, lookupOutMult))
	return nil
}

func (c lookupChip) setup(cs *cols) {
	cs.declare(lookupActive, lookupIdxAddr, lookupBase, lookupOutAddr, lookupOutMult)
	for row, l := range c.m.lookups {
		cs.set(lookupActive, row, 1)
		cs.set(lookupIdxAddr, row, uint64(l.idx))
		cs.set(lookupBase, row, uint64(c.m.tables[l.table].entries[0]))
		cs.set(lookupOutAddr, row, uint64(l.out))
		cs.set(lookupOutMult, row, uint64(c.m.reads[l.out]))
	}
}

func (c lookupChip) trace(cs *cols, r *Run) error {
	cs.declare(lookupIdx)
	cs.declareLanes(lookupV, CellWidth)
	for row, l := range c.m.lookups {
		cs.setElem(lookupIdx, row, r.values[l.idx][0])
		cs.setCell(lookupV, row, r.values[l.out])
	}
	return nil
}
