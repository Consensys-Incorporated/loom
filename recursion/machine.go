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
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/trace"
)

// Poseidon2 parameters (width 24, rate 16, digest 8) and the Merkle node
// domain tag, as in internal/hash and internal/fri.
const (
	width   = P2Width
	rate    = P2Rate
	digest  = P2Digest
	nodeTag = NodeDomainTag
)

// Module names of the chips.
const (
	witnessMod = "witness"
	constMod   = "const"
	p2Mod      = "p2" // the P2 core, carrying the sponge and the Merkle paths
	dpathMod   = "dpath"
	selectMod  = "select"
	windowMod  = "window"
	bitsMod    = "bits"
	e6Mod      = "e6"
	deepMod    = "deep"
	foldMod    = "fold"
	tableMod   = "table"
	lookupMod  = "lookup"
	sumMod     = "sum"
)

// Cell is the value of a memory cell.
type Cell [CellWidth]koalabear.Element

// Machine builds a program for the chips: it allocates addresses, counts the
// reads of every cell and records the instructions, without values. A cell
// holds an input (supplied per execution), a constant (known when building),
// or the output of an instruction. Compile turns the program into a loom AIR
// and its setup; Program.Execute runs it on inputs and traces the witness.
type Machine struct {
	nCells int
	reads  []int // read count of every address

	inputs    []typedCell // input cells, in input order
	hints     []typedCell // cells the witness chip writes with a computed value (Pack streams)
	consts    map[Cell]int
	constList []int        // addresses written by the const chip
	constVal  map[int]Cell // value of every constant

	// SumLanes is the number of terms one Sum row adds; 0 means
	// DefaultSumLanes. Set it before recording any instruction.
	SumLanes int

	instrs  []instr // every instruction, in execution order
	packs   []packInst
	lanes   []lanesInst
	sponges []spongeInst
	paths   []pathInst
	dpaths  []dpathInst
	selects []selectInst
	windows []windowInst
	bits    []bitsInst
	e6Insts []e6Inst
	sums    []sumInst
	deeps   []deepInst
	folds   [][]foldRow
	tables  []tableInst
	lookups []lookupInst
}

// instr is one instruction in execution order: its kind and its index in the
// kind's list.
type instr struct {
	kind, idx int
}

const (
	instrPack = iota
	instrLanes
	instrSponge
	instrPath
	instrDPath
	instrSelect
	instrBits
	instrE6
	instrDeep
	instrSum
	instrLookup
)

func (m *Machine) alloc() int {
	m.reads = append(m.reads, 0)
	m.nCells++
	return m.nCells - 1
}

func (m *Machine) read(addr int) { m.reads[addr]++ }

func (m *Machine) record(kind, idx int) { m.instrs = append(m.instrs, instr{kind, idx}) }

// InputScalar, InputE6 and InputDigest allocate a cell of their kind whose
// value is the next input of every execution (proof values, indices) and
// return its address. The witness chip constrains its lanes beyond the kind to
// zero, and Execute rejects an input with a nonzero lane beyond its kind.
func (m *Machine) InputScalar() int { return m.Input(KindScalar) }
func (m *Machine) InputE6() int     { return m.Input(KindE6) }
func (m *Machine) InputDigest() int { return m.Input(KindDigest) }

// Input allocates an input cell of the given kind (see InputScalar).
func (m *Machine) Input(kind int) int {
	checkCellKind(kind)
	a := m.alloc()
	m.inputs = append(m.inputs, typedCell{a, kind})
	return a
}

// hint allocates a cell of the given kind that the witness chip writes with a
// value computed during execution, which its readers check.
func (m *Machine) hint(kind int) int {
	checkCellKind(kind)
	a := m.alloc()
	m.hints = append(m.hints, typedCell{a, kind})
	return a
}

// InputStream allocates the input cells of a stream of length elements,
// packed CellWidth per cell and zero padded to a whole number of sponge
// blocks (see PackElements for their values), and returns their addresses.
func (m *Machine) InputStream(length int) []int {
	res := make([]int, streamCells(length))
	for i := range res {
		res[i] = m.InputDigest()
	}
	return res
}

// streamCells is the number of cells of a stream of length elements: two per
// sponge block.
func streamCells(length int) int { return 2 * ((length + rate - 1) / rate) }

// PackElements returns the cells of a stream (InputStream's layout).
func PackElements(xs []koalabear.Element) []Cell {
	res := make([]Cell, streamCells(len(xs)))
	for c := range res {
		for j := range CellWidth {
			if p := c*CellWidth + j; p < len(xs) {
				res[c][j] = xs[p]
			}
		}
	}
	return res
}

// Compile builds the chips, their constraints and the memory bus, and the
// setup columns: everything that depends on the program and not on its
// inputs. The machine must not be modified afterwards.
func (m *Machine) Compile() (*Program, error) {
	b := board.NewBuilder()
	bus := &Bus{}
	setup := trace.New()
	p := &Program{m: m}

	// Every module exists before any chip is defined: a chip may look up into
	// another one (the dynamic-path chip into the P2 core).
	var used []chip
	for _, c := range m.chips() {
		if c.rows() == 0 {
			continue
		}
		used = append(used, c)
		p.heights = append(p.heights, chipHeight{c.name(), newChipModule(&b, c.name(), c.rows())})
	}
	for i, c := range used {
		if err := c.define(&b, bus); err != nil {
			return nil, fmt.Errorf("chip %s: %w", c.name(), err)
		}
		cols := newCols(p.heights[i].n)
		c.setup(cols)
		cols.store(setup, c.name())
	}
	if err := bus.Build(&b); err != nil {
		return nil, err
	}
	pg, err := board.Compile(&b)
	if err != nil {
		return nil, err
	}
	p.Loom, p.Setup = pg, setup
	return p, nil
}

// chip is one module of the machine: define adds its AIR and bus accesses,
// setup fills its setup columns (from the program), trace its witness columns
// (from an execution). Chips are traced in the order of Machine.chips, so a
// chip may use what the execution recorded in the Run (the dynamic paths'
// compressions, for the P2 core).
type chip interface {
	name() string
	rows() int
	define(b *board.Builder, bus *Bus) error
	setup(c *cols)
	trace(c *cols, r *Run) error
}

func (m *Machine) chips() []chip {
	return []chip{witnessChip{m}, constChip{m}, p2Chip{m}, dpathChip{m}, selectChip{m},
		windowChip{m}, bitsChip{m}, e6Chip{m}, sumChip{m}, deepChip{m}, foldChip{m}, tableChip{m}, lookupChip{m}}
}

type chipHeight struct {
	module string
	n      int
}

// Program is a compiled machine: its loom program and setup columns, built
// once, and executed on any number of inputs.
type Program struct {
	Loom    board.Program
	Setup   trace.Trace // the setup columns, for loom.Setup
	m       *Machine
	heights []chipHeight // the chips with rows, in Machine.chips order
}

// NumInputs returns the number of input cells of an execution.
func (p *Program) NumInputs() int { return len(p.m.inputs) }

// Run is one execution of a program: every cell's value and the witness
// columns.
type Run struct {
	Trace  trace.Trace // the witness columns (loom merges the setup ones)
	values []Cell
	// p2 holds the dynamic paths' compression inputs, in the order of the
	// rows the P2 core traces for them, after the sponges' and the Merkle
	// paths' own.
	p2 [][width]koalabear.Element

	// tableReads[t][i] counts the reads of entry i of table t by dynamic
	// paths (Lookup's are counted from the lookups); dpathRows[i] are the
	// rows of dynamic path i.
	tableReads map[int][]uint64
	dpathRows  map[int][]dpathRow
}

// Value returns the value of the cell at addr.
func (r *Run) Value(addr int) Cell { return r.values[addr] }

// Execute runs the program on inputs (one cell per Input, in order) and
// traces the witness.
func (p *Program) Execute(inputs []Cell) (*Run, error) {
	m := p.m
	if len(inputs) != len(m.inputs) {
		return nil, fmt.Errorf("Execute: %d inputs, want %d", len(inputs), len(m.inputs))
	}
	r := &Run{Trace: trace.New(), values: make([]Cell, m.nCells)}
	for i, in := range m.inputs {
		for k := in.kind; k < CellWidth; k++ {
			if !inputs[i][k].IsZero() {
				return nil, fmt.Errorf("Execute: input %d has kind %d but a nonzero lane %d", i, in.kind, k)
			}
		}
		r.values[in.addr] = inputs[i]
	}
	for a, v := range m.constVal {
		r.values[a] = v
	}
	for _, in := range m.instrs {
		if err := m.exec(in, r); err != nil {
			return nil, err
		}
	}

	if err := p.trace(r); err != nil {
		return nil, err
	}
	return r, nil
}

// trace computes the chips' witness columns from the cells' values (and what
// the execution recorded: permutation inputs, dynamic reads).
func (p *Program) trace(r *Run) error {
	r.Trace = trace.New()
	byName := map[string]chip{}
	for _, c := range p.m.chips() {
		byName[c.name()] = c
	}
	for _, h := range p.heights {
		cols := newCols(h.n)
		if err := byName[h.module].trace(cols, r); err != nil {
			return fmt.Errorf("chip %s: %w", h.module, err)
		}
		cols.store(r.Trace, h.module)
	}
	return nil
}

// exec computes the cells an instruction writes.
func (m *Machine) exec(in instr, r *Run) error {
	switch in.kind {
	case instrPack:
		m.execPack(m.packs[in.idx], r)
	case instrLanes:
		l := m.lanes[in.idx]
		var c Cell
		copy(c[:l.kind], r.values[l.src][l.off:l.off+l.kind])
		r.values[l.out] = c
	case instrSponge:
		s := m.sponges[in.idx]
		d, err := spongeDigest(r, s)
		if err != nil {
			return err
		}
		r.values[s.out] = d
	case instrPath:
		m.execPath(m.paths[in.idx], r)
	case instrDPath:
		return m.execDPath(in.idx, r)
	case instrSelect:
		return m.execSelect(m.selects[in.idx], r)
	case instrBits:
		m.execBits(m.bits[in.idx], r)
	case instrE6:
		return m.execE6(m.e6Insts[in.idx], r)
	case instrSum:
		m.execSum(m.sums[in.idx], r)
	case instrDeep:
		m.execDeep(m.deeps[in.idx], r)
	case instrLookup:
		return m.execLookup(m.lookups[in.idx], r)
	}
	return nil
}

func height(n int) int {
	h := 4
	for h < n {
		h *= 2
	}
	return h
}

func newChipModule(b *board.Builder, name string, rows int) int {
	n := height(rows)
	mod := board.NewModule(name)
	mod.N = n
	b.AddModule(mod)
	return n
}
