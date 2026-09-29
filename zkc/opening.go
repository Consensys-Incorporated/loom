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

package zkc

// The opening gadget: one native zkc function per (batch, group), open_<b>_<g>,
// returning for one query the leaf digest of the group's opened row pair and
// the DEEP sums of its polynomials,
//
//	G_set(±X) = Σ_{i ∈ set} α^i·f_i(±X),
//
// one per shift set of the group, for the row X (lo) and −X (hi). The caller
// (pcs_query) no longer holds any per-polynomial column: it combines these
// sums with a few E6 operations (see emitDeepBridge).
//
// Soundness does not rely on zkc memory: the opened values are witness columns
// of the gadget, bound to the batch root by the leaf digest, which the caller
// authenticates along the Merkle path. The gadget has three modules:
//
//   - the native I/O module (zkc's), one row per call;
//   - <module>_items: one row per (query, side, polynomial), in alpha_DEEP
//     order within each side, holding f and accumulating α^i·f per shift set;
//   - <module>_sponge: one row per 16-element block of the leaf sponge, in
//     the leaf's stream order [LEAF, 2nB, 2nE, lo.base, hi.base, lo.ext,
//     hi.ext], each block's permutation being looked up in p2_perm.
//
// Stream elements of the sponge are looked up in the item rows by (query,
// position), and the I/O rows look up the digest and the sums in the last
// block and last item rows of their query. Every selector depends only on the
// proof's shape, so it is a setup column, of degree 1.

import (
	"fmt"
	"slices"
	"sort"
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/trace"
)

// groupRef is one group of one batch, as opened by an opening gadget.
type groupRef struct {
	b, g     int
	logN     int
	nB, nE   int
	sets     [][]int // distinct shift sets of the group's polynomials
	polySet  []int   // set index of each polynomial, base then ext
	alphaOff int     // index of the group's first polynomial in its size's alpha_DEEP order
	fn       string  // native function name
}

func setKey(set []int) string { return fmt.Sprint(set) }

// newGroups lists the groups of the fixture, in batch then declaration order.
func newGroups(f *Fixture, shape pcsShape) []*groupRef {
	var res []*groupRef
	for b, bc := range f.Config.Batches {
		for g, gc := range bc {
			gr := &groupRef{b: b, g: g, logN: gc.LogN, nB: gc.NumBase, nE: gc.NumExt, fn: fmt.Sprintf("open_%d_%d", b, g)}
			for _, sr := range shape.sizes {
				if sr.logN != gc.LogN {
					continue
				}
				gr.alphaOff = -1
				for pi, p := range sr.polys {
					if p.batch != b || p.group != g {
						continue
					}
					if gr.alphaOff < 0 {
						gr.alphaOff = pi
					}
					idx := slices.IndexFunc(gr.sets, func(s []int) bool { return slices.Equal(s, p.shifts) })
					if idx < 0 {
						idx = len(gr.sets)
						gr.sets = append(gr.sets, p.shifts)
					}
					gr.polySet = append(gr.polySet, idx)
				}
			}
			res = append(res, gr)
		}
	}
	return res
}

// streamLen is the length of the group's leaf sponge input.
func (gr *groupRef) streamLen() int { return 3 + 2*gr.nB + 12*gr.nE }

func (gr *groupRef) numBlocks() int { return (gr.streamLen() + P2Rate - 1) / P2Rate }

func (gr *groupRef) numPolys() int { return gr.nB + gr.nE }

// rowsAt returns the group's opened row pair at query k.
func (gr *groupRef) rowsAt(f *Fixture, k int) fri.RawRowPair {
	shapes := f.Shapes[gr.b]
	order := make([]int, len(shapes))
	for i := range order {
		order[i] = i
	}
	sort.SliceStable(order, func(i, j int) bool { return shapes[order[i]].Rows > shapes[order[j]].Rows })
	wp := f.Proof.PointSamplings[k][gr.b]
	pos := slices.Index(order, gr.g)
	if pos == 0 {
		return wp.TopRows
	}
	return wp.Injections[pos-1].Rows
}

// polyValues returns f_i(X) and f_i(−X) of the group's polynomials at query k,
// base then ext, base values lifted.
func (gr *groupRef) polyValues(f *Fixture, k int) (lo, hi []ext.E6) {
	rows := gr.rowsAt(f, k)
	for i := range gr.nB {
		var l, h ext.E6
		l.B0.A0, h.B0.A0 = rows.Lo.RawRowBase[i], rows.Hi.RawRowBase[i]
		lo, hi = append(lo, l), append(hi, h)
	}
	lo = append(lo, rows.Lo.RawRowExt...)
	hi = append(hi, rows.Hi.RawRowExt...)
	return lo, hi
}

// stream returns the group's leaf sponge input at query k.
func (gr *groupRef) stream(f *Fixture, k int) []koalabear.Element {
	rows := gr.rowsAt(f, k)
	res := []koalabear.Element{hash.NewElement(LeafDomainTag), hash.NewElement(uint64(2 * gr.nB)), hash.NewElement(uint64(2 * gr.nE))}
	res = append(res, rows.Lo.RawRowBase...)
	res = append(res, rows.Hi.RawRowBase...)
	for _, v := range rows.Lo.RawRowExt {
		res = append(res, hash.ExtToElements(v)...)
	}
	for _, v := range rows.Hi.RawRowExt {
		res = append(res, hash.ExtToElements(v)...)
	}
	return res
}

// readGroup reads the group's row pair (as the batch opening serializes it):
// lo base values, hi base values (packed), then each ext value on its own row.
func readGroup(r *reader, rows fri.RawRowPair) (loB, hiB []string, loE, hiE [][]string) {
	loB, hiB = r.elems(rows.Lo.RawRowBase), r.elems(rows.Hi.RawRowBase)
	for _, v := range rows.Lo.RawRowExt {
		loE = append(loE, r.e6(v))
	}
	for _, v := range rows.Hi.RawRowExt {
		hiE = append(hiE, r.e6(v))
	}
	return loB, hiB, loE, hiE
}

// storeGroup serializes the group's row pair into r without emitting reads,
// and returns the word offset where it starts.
func storeGroup(r *reader, rows fri.RawRowPair) int {
	off := r.align()
	tmp := &reader{e: &Emitter{}, base: r.base, words: r.words, pos: r.pos}
	readGroup(tmp, rows)
	r.words, r.pos = tmp.words, tmp.pos
	return off
}

// openOutputs returns the output names of the group's native function: the
// digest, then the lo sums and the hi sums, one E6 per set.
func (gr *groupRef) openOutputs() (d []string, lo, hi [][]string) {
	d = paramList("d", P2Digest)
	for s := range gr.sets {
		lo = append(lo, paramList(fmt.Sprintf("lo%d_", s), 6))
		hi = append(hi, paramList(fmt.Sprintf("hi%d_", s), 6))
	}
	return d, lo, hi
}

// openSource defines the group's native function. Its body is the reference
// computation, run by the zkc VM only: it reads the group's rows at word
// offset off (relative to the query's base row), hashes the leaf and
// accumulates the sums.
func (gr *groupRef) openSource(f *Fixture, off int, sponges map[string]func() string) string {
	e := Emitter{Sponges: sponges}
	r := newReader(&e, "base")
	r.words = make([]uint32, off)
	loB, hiB, loE, hiE := readGroup(r, gr.rowsAt(f, 0))
	leaf := slices.Concat([]string{fmt.Sprint(LeafDomainTag), fmt.Sprint(2 * gr.nB), fmt.Sprint(2 * gr.nE)},
		loB, hiB, slices.Concat(loE...), slices.Concat(hiE...))
	digest := e.Sponge(leaf)

	d, loOut, hiOut := gr.openOutputs()
	accumulate := func(vals [][]string) [][]string {
		acc := make([][]string, len(gr.sets))
		for s := range acc {
			acc[s] = zeroE6()
		}
		pw := paramList("p", 6)
		for i, v := range vals {
			s := gr.polySet[i]
			// explicit additions: zkc does not inline into native functions
			term := e.Call("e6_mul", 6, slices.Concat(pw, v)...)
			for c := range acc[s] {
				acc[s][c] = e.Let(fmt.Sprintf("%s + %s", acc[s][c], term[c]))
			}
			if i < len(vals)-1 {
				pw = e.Call("e6_mul", 6, slices.Concat(pw, paramList("a", 6))...)
			}
		}
		return acc
	}
	lift := func(xs []string) [][]string {
		res := make([][]string, len(xs))
		for i, x := range xs {
			res[i] = liftBase(x)
		}
		return res
	}
	loAcc := accumulate(append(lift(loB), loE...))
	hiAcc := accumulate(append(lift(hiB), hiE...))

	var typedOuts []string
	for _, o := range d {
		typedOuts = append(typedOuts, o+":𝔽")
	}
	for s := range gr.sets {
		typedOuts = append(typedOuts, typed(loOut[s]), typed(hiOut[s]))
	}
	var sb strings.Builder
	fmt.Fprintf(&sb, "\n#[native]\nfn %s(base:u16, qid:𝔽, %s, %s) -> (%s) {\n%s", gr.fn,
		strings.Join(typedList("a", 6), ", "), strings.Join(typedList("p", 6), ", "),
		strings.Join(typedOuts, ", "), e.String())
	sb.WriteString(assignAll(d, digest))
	for s := range gr.sets {
		sb.WriteString(assignAll(loOut[s], loAcc[s]))
		sb.WriteString(assignAll(hiOut[s], hiAcc[s]))
	}
	sb.WriteString("}\n")
	return sb.String()
}

// OpeningGadget proves the native function of one group, see the package
// comment of opening.go.
type OpeningGadget struct {
	f  *Fixture
	gr *groupRef
}

var _ zkcv.Gadget = (*OpeningGadget)(nil)

func (og *OpeningGadget) items(module string) string  { return module + "_items" }
func (og *OpeningGadget) sponge(module string) string { return module + "_sponge" }

func col(module, name string, shift ...int) expr.Expr {
	if len(shift) > 0 && shift[0] != 0 {
		return expr.Col(module+"."+name, expr.WithShift(shift[0]))
	}
	return expr.Col(module + "." + name)
}

func setup(module, name string) expr.Expr { return expr.Setup(module + "." + name) }

func e6Cols(module, prefix string, shift int) []expr.Expr {
	res := make([]expr.Expr, 6)
	for c := range res {
		res[c] = col(module, fmt.Sprintf("%s%d", prefix, c), shift)
	}
	return res
}

func one() expr.Expr { return expr.Const(koalabear.One()) }

// Define adds the item and sponge modules, their constraints, and the lookups
// tying them to each other, to p2_perm and to the I/O rows.
func (og *OpeningGadget) Define(b *board.Builder, module string, inputs, outputs []string) error {
	gr := og.gr
	S := len(gr.sets)
	if len(inputs) != 14 || len(outputs) != P2Digest+12*S {
		return fmt.Errorf("opening gadget %s: want 14 inputs and %d outputs, got %d and %d", module, P2Digest+12*S, len(inputs), len(outputs))
	}
	items, sponge := og.items(module), og.sponge(module)
	b.AddModule(board.NewModule(items))
	b.AddModule(board.NewModule(sponge))
	mi, ms := b.Modules[items], b.Modules[sponge]

	// Item rows.
	first, instFirst, isBase := setup(items, "first"), setup(items, "inst_first"), setup(items, "is_base")
	f, pw, a, pb := e6Cols(items, "f", 0), e6Cols(items, "pw", 0), e6Cols(items, "a", 0), e6Cols(items, "pb", 0)
	pwPrev, aPrev, pbPrev := e6Cols(items, "pw", -1), e6Cols(items, "a", -1), e6Cols(items, "pb", -1)
	pwA := e6MulExprs(pwPrev, a)
	pwF := e6MulExprs(pw, f)
	for c := range 6 {
		if c > 0 {
			mi.AssertZero(isBase.Mul(f[c]))
		}
		mi.AssertZero(pw[c].Sub(first.Mul(pb[c])).Sub(one().Sub(first).Mul(pwA[c])))
		mi.AssertZero(one().Sub(instFirst).Mul(a[c].Sub(aPrev[c])))
		mi.AssertZero(one().Sub(instFirst).Mul(pb[c].Sub(pbPrev[c])))
		for s := range S {
			acc := col(items, fmt.Sprintf("acc%d_%d", s, c))
			accPrev := col(items, fmt.Sprintf("acc%d_%d", s, c), -1)
			mi.AssertZero(acc.Sub(one().Sub(first).Mul(accPrev)).Sub(setup(items, fmt.Sprintf("m%d", s)).Mul(pwF[c])))
		}
	}

	// Sponge rows: header lanes of the first block are the constants.
	sFirst := setup(sponge, "first")
	for j := range 3 {
		ms.AssertZero(sFirst.Mul(col(sponge, fmt.Sprintf("x%d", j)).Sub(setup(sponge, fmt.Sprintf("hv%d", j)))))
	}

	// Lanes of the sponge are item values: (query, position, value).
	var laneS []board.Table
	var laneSel []expr.Expr
	for j := range P2Rate {
		t := board.NewTable(sponge, 3)
		t.In[0] = setup(sponge, "inst")
		t.In[1] = setup(sponge, "bpos").Add(expr.Const(koalabear.NewElement(uint64(j))))
		t.In[2] = col(sponge, fmt.Sprintf("x%d", j))
		laneS = append(laneS, t)
		laneSel = append(laneSel, setup(sponge, fmt.Sprintf("lane%d", j)))
	}
	var itemT []board.Table
	var itemSel []expr.Expr
	for c := range 6 {
		t := board.NewTable(items, 3)
		t.In[0] = setup(items, "inst")
		t.In[1] = setup(items, "pos").Add(expr.Const(koalabear.NewElement(uint64(c))))
		t.In[2] = f[c]
		itemT = append(itemT, t)
		if c == 0 {
			itemSel = append(itemSel, setup(items, "active"))
		} else {
			itemSel = append(itemSel, setup(items, "active_ext"))
		}
	}
	if err := arguments.CLookupUnionTuple(b, laneSel, itemSel, laneS, itemT); err != nil {
		return err
	}

	// Each block is a Poseidon2 permutation: lanes 0..15 are overwritten by
	// the data lanes, the others keep the previous block's output (zero at
	// the first block).
	perm := board.NewTable(sponge, 2*P2Width)
	for l := range P2Width {
		prev := col(sponge, fmt.Sprintf("out%d", l), -1)
		if l < P2Rate {
			perm.In[l] = setup(sponge, fmt.Sprintf("data%d", l)).Mul(col(sponge, fmt.Sprintf("x%d", l))).
				Add(setup(sponge, fmt.Sprintf("keep%d", l)).Mul(prev))
		} else {
			perm.In[l] = setup(sponge, "keep_cap").Mul(prev)
		}
		perm.In[P2Width+l] = col(sponge, fmt.Sprintf("out%d", l))
	}
	p2 := board.NewTable("p2_perm", 2*P2Width)
	for l := range P2Width {
		p2.In[l] = expr.Col(fmt.Sprintf("p2_perm.s%d", l))
		p2.In[P2Width+l] = expr.Col(fmt.Sprintf("p2_perm.r%d", l))
	}
	if err := arguments.CLookupTuple(b, perm, p2, setup(sponge, "active"), one()); err != nil {
		return err
	}

	// The I/O rows look up their digest and sums.
	io := func(names []string) []expr.Expr {
		res := make([]expr.Expr, len(names))
		for i, n := range names {
			res[i] = expr.Col(n)
		}
		return res
	}
	qid, alpha, pbase := expr.Col(inputs[1]), io(inputs[2:8]), io(inputs[8:14])
	digestS := board.Table{Module: module, In: append([]expr.Expr{qid}, io(outputs[:P2Digest])...)}
	digestT := board.NewTable(sponge, 1+P2Digest)
	digestT.In[0] = setup(sponge, "inst")
	for l := range P2Digest {
		digestT.In[1+l] = col(sponge, fmt.Sprintf("out%d", l))
	}
	if err := arguments.CLookupTuple(b, digestS, digestT, one(), setup(sponge, "last")); err != nil {
		return err
	}
	sums := outputs[P2Digest:]
	var sumS []board.Table
	for side := range 2 {
		t := board.Table{Module: module, In: []expr.Expr{qid, expr.Const(koalabear.NewElement(uint64(side)))}}
		t.In = append(t.In, alpha...)
		t.In = append(t.In, pbase...)
		for s := range S {
			// outputs: lo0 (6), hi0 (6), lo1, hi1, ...
			t.In = append(t.In, io(sums[12*s+6*side:12*s+6*side+6])...)
		}
		sumS = append(sumS, t)
	}
	sumT := board.NewTable(items, 2+12+6*S)
	sumT.In[0], sumT.In[1] = setup(items, "inst"), setup(items, "side")
	copy(sumT.In[2:], a)
	copy(sumT.In[8:], pb)
	for s := range S {
		for c := range 6 {
			sumT.In[14+6*s+c] = col(items, fmt.Sprintf("acc%d_%d", s, c))
		}
	}
	return arguments.CLookupUnionTuple(b, []expr.Expr{one(), one()}, []expr.Expr{setup(items, "last")},
		sumS, []board.Table{sumT})
}

// Fill computes the item and sponge modules from the fixture, and turns zkc's
// zero padding rows of the I/O module into copies of a real call.
func (og *OpeningGadget) Fill(t trace.Trace, module string, inputs, outputs []string) error {
	gr, f := og.gr, og.f
	Q := f.Config.NumQueries
	n := len(t.Base[inputs[0]])

	// I/O rows: find the call of each query, pad with copies.
	callRow := make([]int, Q)
	for k := range callRow {
		callRow[k] = -1
	}
	realRow := -1
	for row := 0; row < n; row++ {
		padding := true
		for _, in := range inputs[2:8] {
			padding = padding && t.Base[in][row].IsZero()
		}
		if padding {
			continue
		}
		k := int(t.Base[inputs[1]][row].Uint64())
		if k >= Q || callRow[k] >= 0 {
			return fmt.Errorf("opening gadget %s: unexpected query id %d at row %d", module, k, row)
		}
		callRow[k], realRow = row, row
	}
	if realRow < 0 {
		return fmt.Errorf("opening gadget %s: no call", module)
	}
	for k, row := range callRow {
		if row < 0 {
			return fmt.Errorf("opening gadget %s: query %d is never opened", module, k)
		}
	}
	all := slices.Concat(inputs, outputs)
	for row := 0; row < n; row++ {
		if slices.Contains(callRow, row) {
			continue
		}
		for _, name := range all {
			t.Base[name][row] = t.Base[name][realRow]
		}
	}
	e6At := func(names []string, row int) ext.E6 {
		var x ext.E6
		for i, c := range []*koalabear.Element{&x.B0.A0, &x.B0.A1, &x.B1.A0, &x.B1.A1, &x.B2.A0, &x.B2.A1} {
			*c = t.Base[names[i]][row]
		}
		return x
	}

	S := len(gr.sets)
	np := gr.numPolys()
	items, sponge := og.items(module), og.sponge(module)

	// Item module.
	ni := padHeight(Q * 2 * np)
	ic := newCols(ni)
	for _, name := range og.itemColumns() {
		ic.get(name)
	}
	var pw, alpha, pbase ext.E6
	acc := make([]ext.E6, S)
	for row := 0; row < ni; row++ {
		k, rest := row/(2*np), row%(2*np)
		side, i := rest/np, rest%np
		active := k < Q
		var fv ext.E6
		isFirst := active && i == 0
		if active {
			call := callRow[k]
			alpha, pbase = e6At(inputs[2:8], call), e6At(inputs[8:14], call)
			lo, hi := gr.polyValues(f, k)
			fv = lo[i]
			if side == 1 {
				fv = hi[i]
			}
			ic.set("inst", row, uint64(k))
			ic.set("side", row, uint64(side))
			pos := 3 + 2*gr.nB + 6*(i-gr.nB) + 6*gr.nE*side
			if i < gr.nB {
				pos = 3 + i + gr.nB*side
				ic.set("is_base", row, 1)
			} else {
				ic.set("active_ext", row, 1)
			}
			ic.set("pos", row, uint64(pos))
			ic.set("active", row, 1)
			ic.set(fmt.Sprintf("m%d", gr.polySet[i]), row, 1)
			if i == np-1 {
				ic.set("last", row, 1)
			}
		}
		if isFirst {
			ic.set("first", row, 1)
			if side == 0 {
				ic.set("inst_first", row, 1)
			}
			pw = pbase
			for s := range acc {
				acc[s] = ext.E6{}
			}
		} else {
			pw.Mul(&pw, &alpha)
		}
		if row == 0 {
			ic.set("first", row, 1)
			ic.set("inst_first", row, 1)
		}
		if active {
			var term ext.E6
			term.Mul(&pw, &fv)
			s := gr.polySet[i]
			acc[s].Add(&acc[s], &term)
		}
		ic.setE6("f", row, fv)
		ic.setE6("pw", row, pw)
		ic.setE6("a", row, alpha)
		ic.setE6("pb", row, pbase)
		for s := range acc {
			ic.setE6(fmt.Sprintf("acc%d_", s), row, acc[s])
		}
		if active && i == np-1 {
			// check the reference body's outputs
			for s := range S {
				want := e6At(outputs[P2Digest+12*s+6*side:P2Digest+12*s+6*side+6], callRow[k])
				if !want.Equal(&acc[s]) {
					return fmt.Errorf("opening gadget %s: query %d side %d set %d: traced sum differs from gadget", module, k, side, s)
				}
			}
		}
	}
	ic.store(t, items)

	// Sponge module.
	nb := gr.numBlocks()
	ns := padHeight(Q * nb)
	sc := newCols(ns)
	for _, name := range og.spongeColumns() {
		sc.get(name)
	}
	perm := hash.NewPoseidon2SpongeHasher().Perm
	L := gr.streamLen()
	var state [P2Width]koalabear.Element
	for row := 0; row < ns; row++ {
		k, blk := row/nb, row%nb
		if k >= Q {
			continue
		}
		stream := gr.stream(f, k)
		if blk == 0 {
			state = [P2Width]koalabear.Element{}
			sc.set("first", row, 1)
			for j := range 3 {
				sc.set(fmt.Sprintf("hv%d", j), row, stream[j].Uint64())
			}
		} else {
			sc.set("keep_cap", row, 1)
		}
		sc.set("inst", row, uint64(k))
		sc.set("bpos", row, uint64(blk*P2Rate))
		sc.set("active", row, 1)
		if blk == nb-1 {
			sc.set("last", row, 1)
		}
		for j := range P2Rate {
			p := blk*P2Rate + j
			if p < L {
				sc.set(fmt.Sprintf("data%d", j), row, 1)
				sc.setElem(fmt.Sprintf("x%d", j), row, stream[p])
				state[j] = stream[p]
				if p >= 3 {
					sc.set(fmt.Sprintf("lane%d", j), row, 1)
				}
			} else if blk > 0 {
				sc.set(fmt.Sprintf("keep%d", j), row, 1)
			}
		}
		out := state
		if err := perm.Permutation(out[:]); err != nil {
			return err
		}
		for l := range P2Width {
			sc.setElem(fmt.Sprintf("out%d", l), row, out[l])
		}
		state = out
		if blk == nb-1 {
			for l := range P2Digest {
				if want := t.Base[outputs[l]][callRow[k]]; !want.Equal(&out[l]) {
					return fmt.Errorf("opening gadget %s: query %d: traced digest differs from gadget", module, k)
				}
			}
		}
	}
	sc.store(t, sponge)
	return nil
}

// itemColumns lists every column of the item module.
func (og *OpeningGadget) itemColumns() []string {
	res := []string{"inst", "pos", "side", "first", "inst_first", "last", "is_base", "active", "active_ext"}
	for s := range og.gr.sets {
		res = append(res, fmt.Sprintf("m%d", s))
		for c := range 6 {
			res = append(res, fmt.Sprintf("acc%d_%d", s, c))
		}
	}
	for _, p := range []string{"f", "pw", "a", "pb"} {
		for c := range 6 {
			res = append(res, fmt.Sprintf("%s%d", p, c))
		}
	}
	return res
}

// spongeColumns lists every column of the sponge module.
func (og *OpeningGadget) spongeColumns() []string {
	res := []string{"inst", "bpos", "first", "last", "active", "keep_cap", "hv0", "hv1", "hv2"}
	for j := range P2Rate {
		res = append(res, fmt.Sprintf("x%d", j), fmt.Sprintf("data%d", j), fmt.Sprintf("keep%d", j), fmt.Sprintf("lane%d", j))
	}
	for l := range P2Width {
		res = append(res, fmt.Sprintf("out%d", l))
	}
	return res
}

func padHeight(n int) int {
	h := zkcv.MinModuleHeight
	for h < n {
		h *= 2
	}
	return h
}

// cols accumulates the columns of a gadget module.
type cols struct {
	n    int
	vals map[string][]koalabear.Element
}

func newCols(n int) *cols { return &cols{n: n, vals: map[string][]koalabear.Element{}} }

func (c *cols) get(name string) []koalabear.Element {
	v, ok := c.vals[name]
	if !ok {
		v = make([]koalabear.Element, c.n)
		c.vals[name] = v
	}
	return v
}

func (c *cols) set(name string, row int, v uint64) { c.get(name)[row].SetUint64(v) }

func (c *cols) setElem(name string, row int, v koalabear.Element) { c.get(name)[row] = v }

func (c *cols) setE6(prefix string, row int, v ext.E6) {
	for i, x := range hash.ExtToElements(v) {
		c.get(fmt.Sprintf("%s%d", prefix, i))[row] = x
	}
}

// store puts the columns in the trace, with every column the constraints
// reference present (missing ones are zero).
func (c *cols) store(t trace.Trace, module string) {
	for name, v := range c.vals {
		t.SetBase(module+"."+name, v)
	}
}
