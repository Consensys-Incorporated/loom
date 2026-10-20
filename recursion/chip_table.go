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
	tableTag     = "tag"
	tableIdx     = "idx"
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
	lookupTag     = "tag"
	lookupOutAddr = "out_addr"
	lookupOutMult = "out_mult"
)

// Witness columns of the lookup chip.
const (
	lookupIdx = "idx"
	lookupV   = "v" // lanes
)

// Dynamic reads. A table holds copies of cells, its entries; a lookup (or a
// dynamic path) reads the entry at an index computed in the circuit. The
// entries are not memory cells: they live on the bus's tables bus, as the
// tuples (tag, i, v) of the table tag, written once with a witness
// multiplicity, their number of reads (it depends on the execution). A read
// of (tag, idx, v) balances only against the entry idx of its own table, with
// its value: an index out of the table, or another table's entry, matches no
// entry, whatever its value, so callers need not bound the indices.
// Execution still rejects an index out of range.

// Table is a table of cells readable at a computed index.
type Table struct {
	tag int // its index in Machine.tables
	n   int
}

// Len returns the number of entries.
func (t Table) Len() int { return t.n }

type tableInst struct {
	src []int // the copied cells
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
	m.tables = append(m.tables, tableInst{src: append([]int(nil), cells...)})
	return Table{tag: len(m.tables) - 1, n: len(cells)}
}

// Lookup returns a cell holding the entry idx of the table t, for a scalar
// cell idx. Executing it fails if idx is not below the table's length (and a
// proof of such a read does not verify, see above).
func (m *Machine) Lookup(t Table, idx int) int {
	k := m.tableIndex(t)
	m.read(idx)
	out := m.alloc()
	m.lookups = append(m.lookups, lookupInst{table: k, idx: idx, out: out})
	m.record(instrLookup, len(m.lookups)-1)
	return out
}

// tableIndex returns t's index in Machine.tables (its tag), checking that t
// is one of this machine's tables.
func (m *Machine) tableIndex(t Table) int {
	if t.tag < 0 || t.tag >= len(m.tables) || len(m.tables[t.tag].src) != t.n {
		panic("unknown table")
	}
	return t.tag
}

// entryValue returns the value of entry i of the table tag: its source cell's.
func (m *Machine) entryValue(r *Run, tag, i int) Cell { return r.values[m.tables[tag].src[i]] }

func (m *Machine) execLookup(l lookupInst, r *Run) error {
	t := m.tables[l.table]
	i := r.values[l.idx][0].Uint64()
	if i >= uint64(len(t.src)) {
		return fmt.Errorf("Lookup: index %d out of a table of %d entries", i, len(t.src))
	}
	r.values[l.out] = m.entryValue(r, l.table, int(i))
	return nil
}

// tableChip: one row per table entry.
//
// Columns: v0..7 (the value), cnt (how many lookups and dynamic paths read
// the entry). Setup: active, src_addr (the copied cell, read), tag and idx
// (the entry's table and index). Bus: reads v at src_addr on the memory bus;
// writes the entry (tag, idx, v) with multiplicity active·cnt on the tables
// bus. The gating matters: on the module's padding rows the setup is zero, so
// the source read is off and v is free, while cnt is a witness; ungated, a
// padding row would write any value as the entry (tag 0, idx 0), with any
// multiplicity.
type tableChip struct{ m *Machine }

func (c tableChip) name() string { return tableMod }

func (c tableChip) rows() int {
	n := 0
	for _, t := range c.m.tables {
		n += len(t.src)
	}
	return n
}

func (c tableChip) define(b *board.Builder, bus *Bus) error {
	v, active := cellCols(tableMod, tableV, 0), setupCol(tableMod, tableActive)
	bus.Read(tableMod, setupCol(tableMod, tableSrcAddr), v, active)
	bus.WriteEntry(tableMod, setupCol(tableMod, tableTag), setupCol(tableMod, tableIdx), v,
		active.Mul(col(tableMod, tableCnt)))
	return nil
}

func (c tableChip) setup(cs *cols) {
	cs.declare(tableActive, tableSrcAddr, tableTag, tableIdx)
	row := 0
	for k, t := range c.m.tables {
		for i, src := range t.src {
			cs.set(tableActive, row, 1)
			cs.set(tableSrcAddr, row, uint64(src))
			cs.set(tableTag, row, uint64(k))
			cs.set(tableIdx, row, uint64(i))
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
		counts[k] = make([]uint64, len(t.src))
	}
	for _, l := range c.m.lookups {
		counts[l.table][r.values[l.idx][0].Uint64()]++
	}
	for k, reads := range r.tableReads {
		for i, n := range reads {
			counts[k][i] += n
		}
	}
	row := 0
	for k, t := range c.m.tables {
		for i, src := range t.src {
			cs.setCell(tableV, row, r.values[src])
			cs.set(tableCnt, row, counts[k][i])
			row++
		}
	}
	return nil
}

// lookupChip: one row per lookup.
//
// Columns: idx (the index), v0..7 (the entry read). Setup: active, idx_addr
// (the index cell, read), tag (the table), out_addr and out_mult (the result
// cell, written). The entry (tag, idx, v) is read on the tables bus.
type lookupChip struct{ m *Machine }

func (c lookupChip) name() string { return lookupMod }
func (c lookupChip) rows() int    { return len(c.m.lookups) }

func (c lookupChip) define(b *board.Builder, bus *Bus) error {
	active, idx := setupCol(lookupMod, lookupActive), col(lookupMod, lookupIdx)
	v := cellCols(lookupMod, lookupV, 0)
	bus.Read(lookupMod, setupCol(lookupMod, lookupIdxAddr), cellOf(idx), active)
	bus.ReadEntry(lookupMod, setupCol(lookupMod, lookupTag), idx, v, active)
	bus.Write(lookupMod, setupCol(lookupMod, lookupOutAddr), v, setupCol(lookupMod, lookupOutMult))
	return nil
}

func (c lookupChip) setup(cs *cols) {
	cs.declare(lookupActive, lookupIdxAddr, lookupTag, lookupOutAddr, lookupOutMult)
	for row, l := range c.m.lookups {
		cs.set(lookupActive, row, 1)
		cs.set(lookupIdxAddr, row, uint64(l.idx))
		cs.set(lookupTag, row, uint64(l.table))
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
