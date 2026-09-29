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

import (
	"fmt"
	"math/bits"
	"slices"
	"sort"
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/internal/constants"
)

// polyRef is one committed polynomial, in alpha_DEEP order within its size.
type polyRef struct {
	batch, group int
	ext          bool
	idx          int   // index within the group's base or ext polynomials
	shifts       []int // normalized shifts, in declared order
}

// sizeRef lists the polynomials of one native size, in alpha_DEEP order
// (batch, group, base then ext), with their distinct shifts.
type sizeRef struct {
	logN   int
	polys  []polyRef
	shifts []int // distinct normalized shifts, in first-seen order
}

// pcsShape is the shape of the committed batches.
type pcsShape struct {
	sizes []sizeRef // decreasing size
}

func normalizeShift(s, n int) int {
	return ((s % n) + n) % n
}

func newPCSShape(f *Fixture) pcsShape {
	logs := map[int]bool{}
	for _, b := range f.Config.Batches {
		for _, g := range b {
			logs[g.LogN] = true
		}
	}
	desc := make([]int, 0, len(logs))
	for l := range logs {
		desc = append(desc, l)
	}
	sort.Sort(sort.Reverse(sort.IntSlice(desc)))

	var res pcsShape
	for _, logN := range desc {
		sr := sizeRef{logN: logN}
		seen := map[int]bool{}
		add := func(p polyRef) {
			sr.polys = append(sr.polys, p)
			for _, s := range p.shifts {
				if !seen[s] {
					seen[s] = true
					sr.shifts = append(sr.shifts, s)
				}
			}
		}
		for b, bc := range f.Config.Batches {
			for g, gc := range bc {
				if gc.LogN != logN {
					continue
				}
				gs := f.Shifts[b][g]
				for i, ss := range gs.Base {
					add(polyRef{batch: b, group: g, idx: i, shifts: normalizeAll(ss, 1<<logN)})
				}
				for i, ss := range gs.Ext {
					add(polyRef{batch: b, group: g, ext: true, idx: i, shifts: normalizeAll(ss, 1<<logN)})
				}
			}
		}
		res.sizes = append(res.sizes, sr)
	}
	return res
}

func normalizeAll(ss []int, n int) []int {
	res := make([]int, len(ss))
	for i, s := range ss {
		res[i] = normalizeShift(s, n)
	}
	return res
}

// claimedValues reads the claimed values in alpha_DEEP binding order and
// returns them as values[size][poly][k], k indexing the poly's shifts.
func (r *reader) claimedValues(f *Fixture, shape pcsShape) [][][][]string {
	res := make([][][][]string, len(shape.sizes))
	for si, sr := range shape.sizes {
		res[si] = make([][][]string, len(sr.polys))
		for pi, p := range sr.polys {
			cv := f.Proof.ClaimedValues[p.batch][p.group]
			var vs []ext.E6
			if p.ext {
				vs = cv.Ext[p.idx]
			} else {
				vs = cv.Base[p.idx]
			}
			for _, v := range vs {
				res[si][pi] = append(res[si][pi], r.e6(v))
			}
		}
	}
	return res
}

// emitDeepSums emits, in main, V[size][shift] = Σ_{i ∋ shift} α^i·v_{i,shift}
// by Horner's rule; they do not depend on the query.
func emitDeepSums(e *Emitter, shape pcsShape, values [][][][]string, alpha []string) [][][]string {
	res := make([][][]string, len(shape.sizes))
	for si, sr := range shape.sizes {
		res[si] = make([][]string, len(sr.shifts))
		for ki, s := range sr.shifts {
			terms := make([][]string, len(sr.polys))
			for pi, p := range sr.polys {
				if k := slices.Index(p.shifts, s); k >= 0 {
					terms[pi] = values[si][pi][k]
				}
			}
			res[si][ki] = horner(e, terms, alpha)
		}
	}
	return res
}

// horner emits Σ_i α^i·terms[i], where a nil term is 0.
func horner(e *Emitter, terms [][]string, alpha []string) []string {
	acc := zeroE6()
	for i := len(terms) - 1; i >= 0; i-- {
		if i < len(terms)-1 {
			acc = e.Call("e6_mul", 6, slices.Concat(acc, alpha)...)
		}
		if terms[i] != nil {
			acc = e.Call("e6_add", 6, slices.Concat(acc, terms[i])...)
		}
	}
	return acc
}

func zeroE6() []string { return []string{"0", "0", "0", "0", "0", "0"} }

// liftBase returns a base-field value as an E6 element.
func liftBase(x string) []string { return []string{x, "0", "0", "0", "0", "0"} }

// groupSums are the DEEP sums a group's opening returns, per shift set of
// the group: lo at X, hi at −X.
type groupSums struct {
	lo, hi [][]string
}

// emitBatchOpening checks the opening of batch b at query k along its
// mixed-size Merkle path (fri.verifyOneWMerkleProof) against the root. Each
// group's leaf digest and DEEP sums come from its opening gadget (open_b_g),
// whose rows are serialized here, and whose word offset is recorded in offs
// (the same for every query).
func emitBatchOpening(r *reader, s []string, L int, f *Fixture, b, k int, root []string,
	groups []*groupRef, pbase map[*groupRef][]string, offs map[*groupRef]int, sums map[*groupRef]groupSums) {
	e := r.e
	shapes := f.Shapes[b]
	wp := f.Proof.PointSamplings[k][b]
	order := make([]int, len(shapes)) // decreasing rows, stable
	for i := range order {
		order[i] = i
	}
	sort.SliceStable(order, func(i, j int) bool { return shapes[order[i]].Rows > shapes[order[j]].Rows })

	open := func(g int) []string {
		i := slices.IndexFunc(groups, func(gr *groupRef) bool { return gr.b == b && gr.g == g })
		gr := groups[i]
		off := storeGroup(r, gr.rowsAt(f, k))
		if prev, ok := offs[gr]; ok && prev != off {
			panic(fmt.Sprintf("group %s: offset %d at query %d, %d before", gr.fn, off, k, prev))
		}
		offs[gr] = off
		n := P2Digest + 12*len(gr.sets)
		outs := e.Call(gr.fn, n, slices.Concat([]string{r.base, "qid"}, paramList("d", 6), pbase[gr])...)
		var gs groupSums
		for set := range gr.sets {
			gs.lo = append(gs.lo, outs[P2Digest+12*set:P2Digest+12*set+6])
			gs.hi = append(gs.hi, outs[P2Digest+12*set+6:P2Digest+12*set+12])
		}
		sums[gr] = gs
		return outs[:P2Digest]
	}

	top := order[0]
	topRows := shapes[top].Rows
	h := open(top)
	depth := log2(topRows) - 1
	reduction := L - log2(topRows)
	injAtWidth := map[int]int{} // pair width -> injection index
	for i := 1; i < len(order); i++ {
		injAtWidth[shapes[order[i]].Rows/2] = i - 1
	}
	for i, sib := range wp.Path.Siblings {
		h = e.MerkleStep(h, r.digest(sib), s[reduction+1+i])
		width := 1 << (depth - i - 1)
		if inj, ok := injAtWidth[width]; ok {
			h = e.Node(h, open(order[inj+1]))
		}
	}
	e.AssertEqAll(h, root)
}

// emitDeepBridge checks, for one query and one size, that the DEEP quotient
// equals the opened FRI values at ±X (fri.checkFRIBridgeByPolynomial). With
// inv_s(±X) = 1/(ζ·ω^s ∓ X), V_s the claimed-value sums and G_set the sums
// returned by the opening gadgets,
//
//	DQ(±X) = Σ_s inv_s·V_s − Σ_set W_set·G_set,   W_set = Σ_{s ∈ set} inv_s.
//
// The inverses are prover hints, checked with e6_assert_inv.
func emitDeepBridge(r *reader, s []string, L int, f *Fixture, k int, sr sizeRef, groups []*groupRef,
	sums map[*groupRef]groupSums, V [][]string, zeta, dqP, dqQ []string) {
	e := r.e
	ratLog := sr.logN + log2(constants.RATE)
	reduction := L - ratLog

	// X = ω_{RATE·N}^{bitrev(lo)}, lo = (s >> reduction) with bit 0 cleared.
	g, err := koalabear.Generator(uint64(1) << ratLog)
	if err != nil {
		panic(err)
	}
	x := "1"
	for i := 1; i < ratLog; i++ {
		var c koalabear.Element
		c.Exp(g, bigPow2(ratLog-1-i))
		one := koalabear.One()
		c.Sub(&c, &one)
		x = e.Let(fmt.Sprintf("%s * (1 + (%s * %s))", x, s[reduction+i], felt(c)))
	}

	// Go-side X, for the inverse hints.
	sFull := f.Proof.FRIProof.FRIQueries[k].Layers[0].Row
	lo := (sFull >> reduction) &^ 1
	var X koalabear.Element
	X.ExpInt64(g, int64(bits.Reverse(uint(lo))>>(bits.UintSize-ratLog)))
	zetaV := f.Zeta
	traceGen, err := koalabear.Generator(uint64(1) << sr.logN)
	if err != nil {
		panic(err)
	}

	accP, accQ := zeroE6(), zeroE6()
	invP := make([][]string, len(sr.shifts))
	invQ := make([][]string, len(sr.shifts))
	for ki, sh := range sr.shifts {
		// ζ·ω^s, then the denominators ζ·ω^s ∓ X and their inverses.
		var om koalabear.Element
		om.ExpInt64(traceGen, int64(sh))
		zs := e.Call("e6_mul_base", 6, append(slices.Clone(zeta), felt(om))...)
		dP := slices.Clone(zs)
		dP[0] = e.Let(fmt.Sprintf("%s - %s", zs[0], x))
		dQ := slices.Clone(zs)
		dQ[0] = e.Let(fmt.Sprintf("%s + %s", zs[0], x))

		var zsV, dPV, dQV, iPV, iQV ext.E6
		zsV.MulByElement(&zetaV, &om)
		dPV, dQV = zsV, zsV
		dPV.B0.A0.Sub(&dPV.B0.A0, &X)
		dQV.B0.A0.Add(&dQV.B0.A0, &X)
		iPV.Inverse(&dPV)
		iQV.Inverse(&dQV)
		invP[ki], invQ[ki] = r.e6(iPV), r.e6(iQV)
		e.Line("e6_assert_inv(%s)", strings.Join(slices.Concat(dP, invP[ki]), ", "))
		e.Line("e6_assert_inv(%s)", strings.Join(slices.Concat(dQ, invQ[ki]), ", "))

		accP = e.Call("e6_add", 6, slices.Concat(accP, e.Call("e6_mul", 6, slices.Concat(V[ki], invP[ki])...))...)
		accQ = e.Call("e6_add", 6, slices.Concat(accQ, e.Call("e6_mul", 6, slices.Concat(V[ki], invQ[ki])...))...)
	}

	for _, gr := range groups {
		for set, shifts := range gr.sets {
			wP, wQ := zeroE6(), zeroE6()
			for _, sh := range shifts {
				ki := slices.Index(sr.shifts, sh)
				wP = e.Call("e6_add", 6, slices.Concat(wP, invP[ki])...)
				wQ = e.Call("e6_add", 6, slices.Concat(wQ, invQ[ki])...)
			}
			gs := sums[gr]
			accP = e.Call("e6_sub", 6, slices.Concat(accP, e.Call("e6_mul", 6, slices.Concat(wP, gs.lo[set])...))...)
			accQ = e.Call("e6_sub", 6, slices.Concat(accQ, e.Call("e6_mul", 6, slices.Concat(wQ, gs.hi[set])...))...)
		}
	}
	e.AssertEqAll(accP, dqP)
	e.AssertEqAll(accQ, dqQ)
}

// e6Pow emits x^n by square-and-multiply.
func e6Pow(e *Emitter, x []string, n int) []string {
	res := []string{"1", "0", "0", "0", "0", "0"}
	if n == 0 {
		return res
	}
	first := true
	for bit := bits.Len(uint(n)) - 1; bit >= 0; bit-- {
		if !first {
			res = e.Call("e6_mul", 6, slices.Concat(res, res)...)
		}
		if n>>bit&1 == 1 {
			if first {
				res = slices.Clone(x)
			} else {
				res = e.Call("e6_mul", 6, slices.Concat(res, x)...)
			}
		}
		first = false
	}
	return res
}
