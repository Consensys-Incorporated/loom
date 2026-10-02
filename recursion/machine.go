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
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
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
	spongeMod  = "sponge"
	merkleMod  = "merkle"
	windowMod  = "window"
	bitsMod    = "bits"
	e6Mod      = "e6"
	foldMod    = "fold"
	p2Mod      = "p2"
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

	inputs    []int // input cells, in input order
	consts    map[Cell]int
	constList []int        // addresses written by the const chip
	constVal  map[int]Cell // value of every constant

	instrs  []instr // every instruction, in execution order
	packs   []packInst
	sponges []spongeInst
	paths   []pathInst
	windows []windowInst
	bits    []bitsInst
	e6Ops   []e6Op
	e6Rows  []e6Row
	folds   [][]foldRow
}

// instr is one instruction in execution order: its kind and its index in the
// kind's list.
type instr struct {
	kind, idx int
}

const (
	instrPack = iota
	instrSponge
	instrPath
	instrBits
	instrE6
)

type packInst struct {
	items, kinds []int
	stream       []int // the stream cells, written by the witness chip
}

type spongeInst struct {
	data   []int // data cells, 2 per block
	length int   // number of input elements
	out    int   // digest address
}

type pathInst struct {
	leaf, index, root int
	siblings          []int
	gens              []koalabear.Element // x⁻¹ accumulator constants, nil if unused
	xb                int                 // address of [x⁻¹, b0], if gens != nil
}

func (m *Machine) alloc() int {
	m.reads = append(m.reads, 0)
	m.nCells++
	return m.nCells - 1
}

func (m *Machine) read(addr int) { m.reads[addr]++ }

func (m *Machine) record(kind, idx int) { m.instrs = append(m.instrs, instr{kind, idx}) }

// Input allocates a cell whose value is the next input of every execution
// (proof values, indices) and returns its address.
func (m *Machine) Input() int {
	a := m.alloc()
	m.inputs = append(m.inputs, a)
	return a
}

// InputStream allocates the input cells of a stream of length elements,
// packed CellWidth per cell and zero padded to a whole number of sponge
// blocks (see PackElements for their values), and returns their addresses.
func (m *Machine) InputStream(length int) []int {
	res := make([]int, streamCells(length))
	for i := range res {
		res[i] = m.Input()
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

// Sponge hashes the first length elements of the data cells (2 per block,
// as laid out by InputStream or Pack) with loom's Poseidon2 sponge, and
// returns the address of the digest.
func (m *Machine) Sponge(data []int, length int) int {
	if len(data) != streamCells(length) || length == 0 {
		panic(fmt.Sprintf("Sponge: %d cells for %d elements", len(data), length))
	}
	for _, d := range data {
		m.read(d)
	}
	out := m.alloc()
	m.sponges = append(m.sponges, spongeInst{data: data, length: length, out: out})
	m.record(instrSponge, len(m.sponges)-1)
	return out
}

// MerklePath checks that the digest at leaf is the leaf of index (lane 0 of
// the index cell) under the root, with siblings leaf-level first.
func (m *Machine) MerklePath(leaf int, siblings []int, index int, root int) {
	m.read(leaf)
	m.read(index)
	m.read(root)
	for _, s := range siblings {
		m.read(s)
	}
	m.paths = append(m.paths, pathInst{leaf: leaf, index: index, root: root, siblings: siblings, xb: -1})
	m.record(instrPath, len(m.paths)-1)
}

// MerklePathX is MerklePath for the Merkle tree of a FRI layer over a domain
// of generator g⁻¹ = gInv: it also returns the cell [x⁻¹, b0], where x⁻¹ =
// gInv^bitrev(index) (bit-reversed over the path depth) is the inverse of the
// fold point of the queried pair, and b0 is the index's low bit.
func (m *Machine) MerklePathX(leaf int, siblings []int, index int, root int, gInv koalabear.Element) int {
	m.MerklePath(leaf, siblings, index, root)
	p := &m.paths[len(m.paths)-1]
	d := len(siblings)
	for lvl := range d {
		g := gInv
		for range d - 1 - lvl {
			g.Square(&g)
		}
		p.gens = append(p.gens, g)
	}
	p.xb = m.alloc()
	return p.xb
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
	// another one (the sponge and Merkle chips into the P2 core).
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
// chip may use what an earlier one recorded in the Run (the P2 core, the
// permutations of the sponge and Merkle chips).
type chip interface {
	name() string
	rows() int
	define(b *board.Builder, bus *Bus) error
	setup(c *cols)
	trace(c *cols, r *Run) error
}

func (m *Machine) chips() []chip {
	return []chip{witnessChip{m}, constChip{m}, spongeChip{m}, merkleChip{m},
		windowChip{m}, bitsChip{m}, e6Chip{m}, foldChip{m}, p2Chip{m}}
}

// numPerms is the number of Poseidon2 permutations: one per sponge block and
// one per Merkle level.
func (m *Machine) numPerms() int {
	n := 0
	for _, s := range m.sponges {
		n += len(s.data) / 2
	}
	for _, p := range m.paths {
		n += len(p.siblings)
	}
	return n
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
	p2     [][width]koalabear.Element // the permutation inputs, in P2 row order
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
	for i, a := range m.inputs {
		r.values[a] = inputs[i]
	}
	for a, v := range m.constVal {
		r.values[a] = v
	}
	for _, in := range m.instrs {
		if err := m.exec(in, r); err != nil {
			return nil, err
		}
	}

	byName := map[string]chip{}
	for _, c := range m.chips() {
		byName[c.name()] = c
	}
	for _, h := range p.heights {
		cols := newCols(h.n)
		if err := byName[h.module].trace(cols, r); err != nil {
			return nil, fmt.Errorf("chip %s: %w", h.module, err)
		}
		cols.store(r.Trace, h.module)
	}
	return r, nil
}

// exec computes the cells an instruction writes.
func (m *Machine) exec(in instr, r *Run) error {
	switch in.kind {
	case instrPack:
		m.execPack(m.packs[in.idx], r)
	case instrSponge:
		s := m.sponges[in.idx]
		d, err := spongeDigest(r, s)
		if err != nil {
			return err
		}
		r.values[s.out] = d
	case instrPath:
		m.execPath(m.paths[in.idx], r)
	case instrBits:
		m.execBits(m.bits[in.idx], r)
	case instrE6:
		return m.execE6(m.e6Ops[in.idx], r)
	}
	return nil
}

func setupCol(module, name string) expr.Expr { return expr.Setup(module + "." + name) }
func col(module, name string) expr.Expr      { return expr.Col(module + "." + name) }
func colShift(module, name string, s int) expr.Expr {
	return expr.Col(module+"."+name, expr.WithShift(s))
}
func constE(v uint64) expr.Expr { return expr.Const(koalabear.NewElement(v)) }
func one() expr.Expr            { return constE(1) }

func cellCols(module, prefix string, from int) [CellWidth]expr.Expr {
	var res [CellWidth]expr.Expr
	for i := range res {
		res[i] = col(module, fmt.Sprintf("%s%d", prefix, from+i))
	}
	return res
}

func height(n int) int {
	h := 4
	for h < n {
		h *= 2
	}
	return h
}

// ── P2 core ──────────────────────────────────────────────────────────────────

func p2Ins() []string {
	res := make([]string, width)
	for i := range res {
		res[i] = fmt.Sprintf("%s.s%d", p2Mod, i)
	}
	return res
}

func p2Outs() []string {
	res := make([]string, width)
	for i := range res {
		res[i] = fmt.Sprintf("%s.r%d", p2Mod, i)
	}
	return res
}

// p2Chip: the P2 core, one row per Poseidon2 permutation of the sponge and
// Merkle chips (their lookup target), constrained by poseidon2AIR. Columns:
// s0..23 (input), r0..23 (output), and the AIR's round columns. No setup, no
// memory access.
type p2Chip struct{ m *Machine }

func (c p2Chip) name() string { return p2Mod }
func (c p2Chip) rows() int    { return c.m.numPerms() }

func (c p2Chip) define(b *board.Builder, bus *Bus) error {
	return (poseidon2AIR{}).Define(b, p2Mod, p2Ins(), p2Outs())
}

func (c p2Chip) setup(*cols) {}

// trace fills the permutations recorded by the sponge and Merkle traces, then
// the AIR's round columns.
func (c p2Chip) trace(cs *cols, r *Run) error {
	if len(r.p2) != c.rows() {
		return fmt.Errorf("%d permutations recorded, want %d", len(r.p2), c.rows())
	}
	cs.declareLanes("s", width)
	cs.declareLanes("r", width)
	perm := newPerm()
	for row, in := range r.p2 {
		out := in
		if err := perm.Permutation(out[:]); err != nil {
			return err
		}
		for i := range width {
			cs.setElem(fmt.Sprintf("s%d", i), row, in[i])
			cs.setElem(fmt.Sprintf("r%d", i), row, out[i])
		}
	}
	// The AIR fills its columns from a trace: run it on these columns and
	// take its own back.
	tmp := trace.New()
	cs.store(tmp, p2Mod)
	if err := (poseidon2AIR{}).Fill(tmp, p2Mod, p2Ins(), p2Outs()); err != nil {
		return err
	}
	for name, v := range tmp.Base {
		cs.vals[strings.TrimPrefix(name, p2Mod+".")] = v
	}
	return nil
}

// p2Table returns the P2 core's lookup target (inputs, then the first nOut
// outputs).
func p2Table(nOut int) board.Table {
	t := board.NewTable(p2Mod, width+nOut)
	for i := range width {
		t.In[i] = col(p2Mod, fmt.Sprintf("s%d", i))
	}
	for i := range nOut {
		t.In[width+i] = col(p2Mod, fmt.Sprintf("r%d", i))
	}
	return t
}
