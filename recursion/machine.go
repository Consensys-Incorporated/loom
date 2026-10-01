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
	"math/big"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"
	"github.com/consensys/loom/zkc"
)

// Poseidon2 parameters (width 24, rate 16, digest 8) and the Merkle node
// domain tag, as in internal/hash and internal/fri.
const (
	width   = zkc.P2Width
	rate    = zkc.P2Rate
	digest  = zkc.P2Digest
	nodeTag = zkc.NodeDomainTag
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

// Machine is a program for the prototype chips, together with its witness:
// the compiler assigns addresses, counts reads, and runs the computation to
// fill the trace.
type Machine struct {
	cells     []Cell // value of every address
	reads     []int  // read count of every address
	witness   []int  // addresses written by the witness chip
	consts    map[Cell]int
	constList []int // addresses written by the const chip
	sponges   []spongeInst
	paths     []pathInst
	windows   []windowInst
	bits      []bitsInst
	e6Rows    []e6Row
	folds     [][]foldRow
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

func (m *Machine) alloc(v Cell) int {
	m.cells = append(m.cells, v)
	m.reads = append(m.reads, 0)
	return len(m.cells) - 1
}

func (m *Machine) read(addr int) Cell {
	m.reads[addr]++
	return m.cells[addr]
}

// Witness writes a cell of prover data (proof values, indices) and returns
// its address.
func (m *Machine) Witness(v Cell) int {
	a := m.alloc(v)
	m.witness = append(m.witness, a)
	return a
}

// WitnessStream writes xs, packed CellWidth per cell and zero padded to a
// whole number of sponge blocks, and returns the cell addresses.
func (m *Machine) WitnessStream(xs []koalabear.Element) []int {
	blocks := (len(xs) + rate - 1) / rate
	var res []int
	for c := 0; c < 2*blocks; c++ {
		var v Cell
		for j := range v {
			if p := c*CellWidth + j; p < len(xs) {
				v[j] = xs[p]
			}
		}
		res = append(res, m.Witness(v))
	}
	return res
}

// Sponge hashes the first length elements of the data cells (2 per block,
// as written by WitnessStream) with loom's Poseidon2 sponge, and returns the
// address of the digest.
func (m *Machine) Sponge(data []int, length int) int {
	if len(data) != 2*((length+rate-1)/rate) || length == 0 {
		panic(fmt.Sprintf("Sponge: %d cells for %d elements", len(data), length))
	}
	var state [width]koalabear.Element
	perm := poseidon2.NewPermutation(width, zkc.P2FullRounds, zkc.P2PartialRounds)
	for b := 0; b < len(data)/2; b++ {
		lo, hi := m.read(data[2*b]), m.read(data[2*b+1])
		for j := 0; j < rate; j++ {
			if p := b*rate + j; p < length {
				if j < CellWidth {
					state[j] = lo[j]
				} else {
					state[j] = hi[j-CellWidth]
				}
			}
		}
		if err := perm.Permutation(state[:]); err != nil {
			panic(err)
		}
	}
	var d Cell
	copy(d[:], state[:digest])
	out := m.alloc(d)
	m.sponges = append(m.sponges, spongeInst{data: data, length: length, out: out})
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
	m.paths = append(m.paths, pathInst{leaf: leaf, index: index, root: root, siblings: siblings})
}

// MerklePathX is MerklePath for the Merkle tree of a FRI layer over a domain
// of generator g⁻¹ = gInv: it also returns the cell [x⁻¹, b0], where x⁻¹ =
// gInv^bitrev(index) (bit-reversed over the path depth) is the inverse of the
// fold point of the queried pair, and b0 is the index's low bit.
func (m *Machine) MerklePathX(leaf int, siblings []int, index int, root int, gInv koalabear.Element) int {
	m.MerklePath(leaf, siblings, index, root)
	d := len(siblings)
	p := &m.paths[len(m.paths)-1]
	idx := m.cells[index][0].Uint64()
	var x koalabear.Element
	x.SetOne()
	for lvl := range d {
		var g koalabear.Element
		g.Exp(gInv, new(big.Int).Lsh(big.NewInt(1), uint(d-1-lvl)))
		p.gens = append(p.gens, g)
		if idx>>lvl&1 == 1 {
			x.Mul(&x, &g)
		}
	}
	var xb Cell
	xb[0] = x
	xb[1].SetUint64(idx & 1)
	p.xb = m.alloc(xb)
	return p.xb
}

// Program is a compiled machine: the loom program and its trace.
type Program struct {
	Loom  board.Program
	Trace trace.Trace
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

// Compile builds the chips, their constraints and the memory bus, and fills
// the trace.
func (m *Machine) Compile() (*Program, error) {
	b := board.NewBuilder()
	bus := &Bus{}
	t := trace.New()
	var p2Inputs [][width]koalabear.Element
	// The P2 core exists first: the other chips look up into it. Its height
	// is set once every permutation is known.
	b.AddModule(board.NewModule(p2Mod))

	// Witness chip: one row per written cell.
	nw := height(len(m.witness))
	wm := board.NewModule(witnessMod)
	wm.N = nw
	b.AddModule(wm)
	bus.Write(witnessMod, setupCol(witnessMod, "addr"), cellCols(witnessMod, "v", 0), setupCol(witnessMod, "mult"))
	wc := newCols(nw)
	for row, a := range m.witness {
		wc.set("addr", row, uint64(a))
		wc.set("mult", row, uint64(m.reads[a]))
		for j := range CellWidth {
			wc.setElem(fmt.Sprintf("v%d", j), row, m.cells[a][j])
		}
	}
	wc.declare("addr", "mult")
	for j := range CellWidth {
		wc.declare(fmt.Sprintf("v%d", j))
	}
	wc.store(t, witnessMod)

	// Sponge and Merkle chips.
	if err := m.spongeChip(&b, bus, t, &p2Inputs); err != nil {
		return nil, err
	}
	if err := m.merkleChip(&b, bus, t, &p2Inputs); err != nil {
		return nil, err
	}
	for _, chip := range []func(*board.Builder, *Bus, trace.Trace) error{
		m.constChip, m.windowChip, m.bitsChip, m.e6Chip, m.foldChip,
	} {
		if err := chip(&b, bus, t); err != nil {
			return nil, err
		}
	}

	// P2 core: one row per permutation, the Poseidon2 gadget's constraints.
	np := height(len(p2Inputs))
	b.Modules[p2Mod].N = np
	ins, outs := make([]string, width), make([]string, width)
	for i := range ins {
		ins[i], outs[i] = fmt.Sprintf("%s.s%d", p2Mod, i), fmt.Sprintf("%s.r%d", p2Mod, i)
	}
	if err := (zkc.Poseidon2Gadget{}).Define(&b, p2Mod, ins, outs); err != nil {
		return nil, err
	}
	pc := newCols(np)
	perm := poseidon2.NewPermutation(width, zkc.P2FullRounds, zkc.P2PartialRounds)
	for row, in := range p2Inputs {
		out := in
		if err := perm.Permutation(out[:]); err != nil {
			return nil, err
		}
		for i := range width {
			pc.setElem(fmt.Sprintf("s%d", i), row, in[i])
			pc.setElem(fmt.Sprintf("r%d", i), row, out[i])
		}
	}
	for i := range width {
		pc.declare(fmt.Sprintf("s%d", i), fmt.Sprintf("r%d", i))
	}
	pc.store(t, p2Mod)
	if err := (zkc.Poseidon2Gadget{}).Fill(t, p2Mod, ins, outs); err != nil {
		return nil, err
	}

	if err := bus.Build(&b); err != nil {
		return nil, err
	}
	pg, err := board.Compile(&b)
	if err != nil {
		return nil, err
	}
	return &Program{Loom: pg, Trace: t}, nil
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
