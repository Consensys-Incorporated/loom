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
	"github.com/consensys/loom/expr"
)

// Setup columns of the dpath chip.
const (
	dpathFirst      = "first"
	dpathLast       = "last"
	dpathActive     = "active"
	dpathHMax       = "hmax"     // H, on a path's first row
	dpathGroups     = "groups"   // G, on a path's last row
	dpathLeafTag    = "leaf_tag" // the tables' tags
	dpathOrderTag   = "order_tag"
	dpathHeightsTag = "heights_tag"
	dpathSibTag     = "sib_tag"
	dpathBitsTag    = "bits_tag"
	dpathL          = "l" // L, the number of bits of the row
	dpathRootAddr   = "root_addr"
)

// Witness columns of the dpath chip.
const (
	dpathKind    = "kind"    // 1 on a fold row, 0 on a compress row
	dpathHc      = "hc"      // the height before the row
	dpathStarted = "started" // a leaf has been taken before the row
	dpathFc      = "fc"      // the number of fold rows before the row
	dpathPi      = "pi"      // the group folded (fold rows)
	dpathHg      = "hg"      // its height (fold rows)
	dpathB       = "b"       // the direction bit (compress rows)
	dpathCur     = "cur"     // lanes: the running hash entering the row
	dpathOp      = "op"      // lanes: the sibling or the group's leaf
	dpathOut     = "out"     // lanes
)

// DynamicPath is a Merkle path in a mixed-height tree whose shape is data:
// the groups' heights are cells, not constants. Counted from the root, a
// group of height h_g holds 2^h_g leaves, and the path, from the maximum
// height H down, folds at every height h the leaves of the groups of height
// h (the first one starting the path, the others compressed on its right,
// as merkle.LevelInjection), then compresses the level with its sibling,
// ordered by the bit L − h of the query's row (h → h − 1). The root follows
// height 1.
type DynamicPath struct {
	// Leaves[g] is group g's leaf digest at the queried position; Heights[g]
	// its height, a scalar in [1, H].
	Leaves, Heights Table
	// Order[k] is the k-th group folded: the groups by decreasing height,
	// equal heights by increasing index. The chip relies on it: the caller
	// checks that it is that permutation (an index past G reads no entry of
	// Leaves and Heights, so it cannot verify, but a repeated group could).
	Order Table
	// Siblings[h−1] is the sibling at height h (h = 1..H), zero above the
	// path's top height; H = Siblings.Len().
	Siblings Table
	// Bits[j] is bit j of the query's row, j < L; the direction bit at height
	// h is Bits[L − h].
	Bits Table
	L    int
	Root int
}

type dpathInst struct {
	p                                     DynamicPath
	leaves, heights, order, siblings, bit int // indices in Machine.tables
}

// dpathRow is one executed row of a dynamic path.
type dpathRow struct {
	fold     bool
	hc, fc   int
	started  bool
	pi, hg   int
	b        uint64
	cur, op  Cell
	out      Cell
	hashed   bool
	p2Inputs [width]koalabear.Element
}

// MerklePathDynamic checks a DynamicPath: that the path from the groups'
// leaves, at their heights, through the siblings, is the root. One row per
// height (H) and per group (G), whatever the heights.
func (m *Machine) MerklePathDynamic(p DynamicPath) {
	H, G := p.Siblings.Len(), p.Order.Len()
	if p.Leaves.Len() != G || p.Heights.Len() != G {
		panic(fmt.Sprintf("MerklePathDynamic: %d leaves, %d heights, %d groups ordered", p.Leaves.Len(), p.Heights.Len(), G))
	}
	if p.L < H || p.Bits.Len() < p.L {
		panic(fmt.Sprintf("MerklePathDynamic: %d bits for a row of %d bits and %d heights", p.Bits.Len(), p.L, H))
	}
	m.read(p.Root)
	m.dpaths = append(m.dpaths, dpathInst{
		p:      p,
		leaves: m.tableIndex(p.Leaves), heights: m.tableIndex(p.Heights), order: m.tableIndex(p.Order),
		siblings: m.tableIndex(p.Siblings), bit: m.tableIndex(p.Bits),
	})
	m.record(instrDPath, len(m.dpaths)-1)
}

// execDPath builds the path's rows from the tables' values (the heights and
// the order decide which rows fold), counts its reads of the tables' entries,
// and records its compressions for the P2 core.
func (m *Machine) execDPath(idx int, r *Run) error {
	d := m.dpaths[idx]
	p := d.p
	H, G := p.Siblings.Len(), p.Order.Len()
	entry := func(t Table, i int) Cell { return m.entryValue(r, t.tag, i) }
	scalar := func(t Table, i int) int {
		c := entry(t, i)
		return int(c[0].Uint64())
	}
	count := func(table, i int) {
		if r.tableReads == nil {
			r.tableReads = map[int][]uint64{}
		}
		if r.tableReads[table] == nil {
			r.tableReads[table] = make([]uint64, len(m.tables[table].src))
		}
		r.tableReads[table][i]++
	}
	perm := newPerm()
	var rows []dpathRow
	var cur Cell
	started, fc := false, 0
	for hc := H; hc >= 1; hc-- {
		// The groups of height hc, in order.
		for fc < G {
			pi := scalar(p.Order, fc)
			if pi >= G {
				return fmt.Errorf("MerklePathDynamic: order entry %d is group %d, of %d", fc, pi, G)
			}
			hg := scalar(p.Heights, pi)
			if hg > hc {
				return fmt.Errorf("MerklePathDynamic: group %d of height %d after height %d", pi, hg, hc)
			}
			if hg < hc {
				break
			}
			count(d.order, fc)
			count(d.heights, pi)
			count(d.leaves, pi)
			row := dpathRow{fold: true, hc: hc, fc: fc, started: started, pi: pi, hg: hg, cur: cur, op: entry(p.Leaves, pi)}
			if started {
				row.out = compressCell(perm, &row, cur, row.op)
			} else {
				row.out = row.op
			}
			rows = append(rows, row)
			cur, started = row.out, true
			fc++
		}
		// The level hc → hc − 1.
		count(d.siblings, hc-1)
		count(d.bit, p.L-hc)
		bc := entry(p.Bits, p.L-hc)
		b := bc[0].Uint64()
		row := dpathRow{hc: hc, fc: fc, started: started, b: b, cur: cur, op: entry(p.Siblings, hc-1)}
		if started {
			left, right := cur, row.op
			if b == 1 {
				left, right = right, left
			}
			row.out = compressCell(perm, &row, left, right)
		} else {
			row.out = cur
		}
		rows = append(rows, row)
		cur = row.out
	}
	if fc != G {
		return fmt.Errorf("MerklePathDynamic: %d of %d groups folded (heights in [1, %d], in order)", fc, G, H)
	}
	for _, row := range rows {
		if row.hashed {
			r.p2m = append(r.p2m, row.p2Inputs)
		}
	}
	if r.dpathRows == nil {
		r.dpathRows = map[int][]dpathRow{}
	}
	r.dpathRows[idx] = rows
	return nil
}

// compressCell returns the node compression of left and right (the first
// digest lanes of each), recording the permutation input in the row.
func compressCell(perm interface {
	Permutation([]koalabear.Element) error
}, row *dpathRow, left, right Cell) Cell {
	var in [width]koalabear.Element
	in[0].SetUint64(nodeTag)
	copy(in[digest:], left[:digest])
	copy(in[2*digest:], right[:digest])
	row.hashed, row.p2Inputs = true, in
	out := in
	if err := perm.Permutation(out[:]); err != nil {
		panic(err)
	}
	var res Cell
	copy(res[:], out[:digest])
	return res
}

// dpathChip: one row per row of a dynamic path (H + G per path).
//
// Constraints (transitions on every path row but the last):
//
//	kind, b, started ∈ {0, 1},  kind·b = 0
//	first: hc = H, started = 0, fc = 0
//	hc[+1] = hc − (1 − kind),  fc[+1] = fc + kind
//	started[+1] = started + kind − started·kind,  cur[+1] = out
//	kind·(hg − hc) = 0                      a group folds at its height
//	last: kind = 0, hc = 1, fc = G          every level, every group
//	(1 − started)·(out − cur − kind·(op − cur)) = 0
//	                                        before a leaf: copy; the first leaf
//
// and, when started, out = compress(b ? (op, cur) : (cur, op)), looked up in
// the P2 core (a fold row has b = 0: its leaf on the right). Reads, on the
// tables bus (see Table): the leaf, entry pi of Leaves, pi, entry fc of
// Order, and hg, entry pi of Heights (fold rows); the sibling, entry hc − 1 of
// Siblings, and b, entry L − hc of Bits (compress rows). On the memory bus:
// the root, with out, on the last row. Each table read is tagged by its
// table, so an index out of a table matches no entry: these reads cannot reach
// another table's entries whatever the indices. That the order is the
// permutation folding each group once remains the caller's check.
type dpathChip struct{ m *Machine }

func (c dpathChip) name() string { return dpathMod }

func (c dpathChip) rows() int {
	n := 0
	for _, d := range c.m.dpaths {
		n += d.p.Siblings.Len() + d.p.Order.Len()
	}
	return n
}

func (c dpathChip) define(b *board.Builder, bus *Bus) error {
	mm := b.Modules[dpathMod]
	s := func(name string) expr.Expr { return setupCol(dpathMod, name) }
	w := func(name string) expr.Expr { return col(dpathMod, name) }
	next := func(name string) expr.Expr { return colShift(dpathMod, name, 1) }
	first, last, active := s(dpathFirst), s(dpathLast), s(dpathActive)
	kind, hc, started, fc, pi, hg, bit := w(dpathKind), w(dpathHc), w(dpathStarted), w(dpathFc), w(dpathPi), w(dpathHg), w(dpathB)
	notKind := one().Sub(kind)
	trans := active.Sub(last)

	for _, x := range []expr.Expr{kind, bit, started} {
		mm.AssertZero(x.Mul(x.Sub(one())))
	}
	mm.AssertZero(kind.Mul(bit))
	mm.AssertZero(first.Mul(hc.Sub(s(dpathHMax))))
	mm.AssertZero(first.Mul(started))
	mm.AssertZero(first.Mul(fc))
	mm.AssertZero(trans.Mul(next(dpathHc).Sub(hc).Add(notKind)))
	mm.AssertZero(trans.Mul(next(dpathFc).Sub(fc).Sub(kind)))
	mm.AssertZero(trans.Mul(next(dpathStarted).Sub(started).Sub(kind).Add(started.Mul(kind))))
	mm.AssertZero(kind.Mul(hg.Sub(hc)))
	mm.AssertZero(last.Mul(kind))
	mm.AssertZero(last.Mul(hc.Sub(one())))
	mm.AssertZero(last.Mul(fc.Sub(s(dpathGroups))))
	for i := range digest {
		cur, op, out := w(laneName(dpathCur, i)), w(laneName(dpathOp, i)), w(laneName(dpathOut, i))
		mm.AssertZero(trans.Mul(colShift(dpathMod, laneName(dpathCur, i), 1).Sub(out)))
		mm.AssertZero(one().Sub(started).Mul(out.Sub(cur).Sub(kind.Mul(op.Sub(cur)))))
	}

	cur, op, out := cellCols(dpathMod, dpathCur, 0), cellCols(dpathMod, dpathOp, 0), cellCols(dpathMod, dpathOut, 0)
	bus.ReadEntry(dpathMod, s(dpathLeafTag), pi, op, kind)
	bus.ReadEntry(dpathMod, s(dpathSibTag), hc.Sub(one()), op, active.Sub(kind))
	bus.ReadEntry(dpathMod, s(dpathOrderTag), fc, cellOf(pi), kind)
	bus.ReadEntry(dpathMod, s(dpathHeightsTag), pi, cellOf(hg), kind)
	bus.ReadEntry(dpathMod, s(dpathBitsTag), s(dpathL).Sub(hc), cellOf(bit), active.Sub(kind))
	bus.Read(dpathMod, s(dpathRootAddr), out, last)

	src := board.NewTable(dpathMod, width+digest)
	src.In[0] = constE(nodeTag)
	for i := 1; i < digest; i++ {
		src.In[i] = expr.Const(koalabear.Element{})
	}
	for i := range digest {
		src.In[digest+i] = cur[i].Add(bit.Mul(op[i].Sub(cur[i])))
		src.In[2*digest+i] = op[i].Add(bit.Mul(cur[i].Sub(op[i])))
		src.In[width+i] = out[i]
	}
	return bus.Lookup(board.CTable{Table: src, Sel: started}, board.CTable{Table: p2Table(p2mMod, digest)})
}

func (c dpathChip) setup(cs *cols) {
	cs.declare(dpathFirst, dpathLast, dpathActive, dpathHMax, dpathGroups, dpathLeafTag, dpathOrderTag,
		dpathHeightsTag, dpathSibTag, dpathBitsTag, dpathL, dpathRootAddr)
	row := 0
	for _, d := range c.m.dpaths {
		p := d.p
		n := p.Siblings.Len() + p.Order.Len()
		for k := range n {
			cs.set(dpathActive, row, 1)
			cs.set(dpathLeafTag, row, uint64(d.leaves))
			cs.set(dpathOrderTag, row, uint64(d.order))
			cs.set(dpathHeightsTag, row, uint64(d.heights))
			cs.set(dpathSibTag, row, uint64(d.siblings))
			cs.set(dpathBitsTag, row, uint64(d.bit))
			cs.set(dpathL, row, uint64(p.L))
			if k == 0 {
				cs.set(dpathFirst, row, 1)
				cs.set(dpathHMax, row, uint64(p.Siblings.Len()))
			}
			if k == n-1 {
				cs.set(dpathLast, row, 1)
				cs.set(dpathGroups, row, uint64(p.Order.Len()))
				cs.set(dpathRootAddr, row, uint64(p.Root))
			}
			row++
		}
	}
}

func (c dpathChip) trace(cs *cols, r *Run) error {
	cs.declare(dpathKind, dpathHc, dpathStarted, dpathFc, dpathPi, dpathHg, dpathB)
	for _, x := range []string{dpathCur, dpathOp, dpathOut} {
		cs.declareLanes(x, CellWidth)
	}
	row := 0
	for i := range c.m.dpaths {
		for _, dr := range r.dpathRows[i] {
			if dr.fold {
				cs.set(dpathKind, row, 1)
			}
			if dr.started {
				cs.set(dpathStarted, row, 1)
			}
			cs.set(dpathHc, row, uint64(dr.hc))
			cs.set(dpathFc, row, uint64(dr.fc))
			cs.set(dpathPi, row, uint64(dr.pi))
			cs.set(dpathHg, row, uint64(dr.hg))
			cs.set(dpathB, row, dr.b)
			cs.setCell(dpathCur, row, dr.cur)
			cs.setCell(dpathOp, row, dr.op)
			cs.setCell(dpathOut, row, dr.out)
			row++
		}
	}
	return nil
}
