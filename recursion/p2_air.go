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
	"maps"
	"slices"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"
)

// poseidon2AIR is the AIR of a P2 core: one permutation per row, laid out as
// Plonky3's poseidon2-air with S-box degree 3 and no S-box registers. Its
// columns are
//
//	inputs                 w
//	post of full rounds    w × (full rounds − 1)   (the last one is the outputs)
//	partial S-box outputs  1 × partial rounds
//	outputs                w
//
// i.e. w·(R_F + 1) + R_P columns — 189 at loom's width 24, 6 full and 21
// partial rounds — and every constraint has degree 3. Between committed
// columns the state is tracked as linear forms, so the linear layers cost no
// columns.
//
// A full round costs w columns and a partial round one, so the width and R_F
// are what the column count is made of; see TestP2WidthCost, which prices a
// narrower core.
type poseidon2AIR struct {
	w, rf, rp int
	me, mi    [][]koalabear.Element // the external and internal matrices
}

// newP2AIR returns the AIR of the width-w permutation with rf full and rp
// partial rounds.
func newP2AIR(w, rf, rp int) poseidon2AIR {
	return poseidon2AIR{w: w, rf: rf, rp: rp, me: p2Matrix(w, matExternal), mi: p2Matrix(w, matInternal)}
}

// loomP2AIR is the AIR of loom's own permutation, the one the sponge and the
// Merkle node hasher use.
func loomP2AIR() poseidon2AIR { return newP2AIR(P2Width, P2FullRounds, P2PartialRounds) }

// p2Matrix returns a linear layer as a dense w×w matrix, obtained by applying
// gnark-crypto's addition chains to unit vectors.
func p2Matrix(w int, apply func([]koalabear.Element)) [][]koalabear.Element {
	m := make([][]koalabear.Element, w)
	for r := range m {
		m[r] = make([]koalabear.Element, w)
	}
	for j := 0; j < w; j++ {
		unit := make([]koalabear.Element, w)
		unit[j].SetOne()
		apply(unit)
		for r := 0; r < w; r++ {
			m[r][j] = unit[r]
		}
	}
	return m
}

// matExternal applies circ(2·M4, M4, …, M4) in place (gnark-crypto's
// matMulExternalInPlace).
func matExternal(s []koalabear.Element) {
	for c := 0; c < len(s)/4; c++ {
		x := s[4*c : 4*c+4]
		var t01, t23, t0123, t01123, t01233 koalabear.Element
		t01.Add(&x[0], &x[1])
		t23.Add(&x[2], &x[3])
		t0123.Add(&t01, &t23)
		t01123.Add(&t0123, &x[1])
		t01233.Add(&t0123, &x[3])
		x[3].Double(&x[0]).Add(&x[3], &t01233)
		x[1].Double(&x[2]).Add(&x[1], &t01123)
		x[0].Add(&t01, &t01123)
		x[2].Add(&t23, &t01233)
	}
	var sums [4]koalabear.Element
	for c := 0; c < len(s)/4; c++ {
		for j := range sums {
			sums[j].Add(&sums[j], &s[4*c+j])
		}
	}
	for i := range s {
		s[i].Add(&s[i], &sums[i%4])
	}
}

// matInternal applies 1·1ᵀ + diag in place (gnark-crypto's
// matMulInternalInPlace).
func matInternal(s []koalabear.Element) {
	var sum koalabear.Element
	for i := range s {
		sum.Add(&sum, &s[i])
	}
	for i, d := range p2Diag(len(s)) {
		var t koalabear.Element
		t.Mul(&s[i], &d)
		s[i].Add(&sum, &t)
	}
}

func mulMat(m [][]koalabear.Element, x []koalabear.Element) []koalabear.Element {
	res := make([]koalabear.Element, len(m))
	for r := range res {
		for j := range x {
			var t koalabear.Element
			t.Mul(&m[r][j], &x[j])
			res[r].Add(&res[r], &t)
		}
	}
	return res
}

func (a poseidon2AIR) halfFull() int { return a.rf / 2 }

func (a poseidon2AIR) isFullRound(r int) bool {
	return r < a.halfFull() || r >= a.halfFull()+a.rp
}

// p2Columns names the AIR's internal columns: post[r][i] for every full
// round but the last, and sbox[r] for partial rounds.
func (a poseidon2AIR) p2Columns(module string) (post map[int][]string, sbox map[int]string) {
	post, sbox = map[int][]string{}, map[int]string{}
	last := a.rf + a.rp - 1
	for r := 0; r <= last; r++ {
		switch {
		case r == last:
		case a.isFullRound(r):
			post[r] = make([]string, a.w)
			for i := range post[r] {
				post[r][i] = fmt.Sprintf("%s.p2_post%d_%d", module, r, i)
			}
		default:
			sbox[r] = fmt.Sprintf("%s.p2_sbox%d", module, r)
		}
	}
	return post, sbox
}

// linForm is a linear form over loom columns.
type linForm struct {
	terms map[string]koalabear.Element
	c     koalabear.Element
}

func linCol(name string) linForm {
	return linForm{terms: map[string]koalabear.Element{name: koalabear.One()}}
}

// combine returns Σ_j m[j]·xs[j].
func combine(m []koalabear.Element, xs []linForm) linForm {
	res := linForm{terms: map[string]koalabear.Element{}}
	for j, x := range xs {
		for v, c := range x.terms {
			c.Mul(&c, &m[j])
			t := res.terms[v]
			t.Add(&t, &c)
			res.terms[v] = t
		}
		var c koalabear.Element
		c.Mul(&x.c, &m[j])
		res.c.Add(&res.c, &c)
	}
	return res
}

// expr renders the form as a fresh expression tree, its terms in column-name
// order: the tree, and so the compiled program, must not depend on the map's
// iteration order.
func (l linForm) expr() expr.Expr {
	res := expr.Expr(expr.Const(l.c))
	for _, v := range slices.Sorted(maps.Keys(l.terms)) {
		c := l.terms[v]
		if c.IsZero() {
			continue
		}
		res = res.Add(expr.Const(c).Mul(expr.Col(v)))
	}
	return res
}

// cube returns (l + k)³ as a fresh expression tree.
func cube(l linForm, k koalabear.Element) expr.Expr {
	f := func() expr.Expr { return l.expr().Add(expr.Const(k)) }
	return f().Mul(f()).Mul(f())
}

// Define adds the constraints of Poseidon2 on every row of the module.
func (a poseidon2AIR) Define(b *board.Builder, module string, inputs, outputs []string) error {
	if len(inputs) != a.w || len(outputs) != a.w {
		return fmt.Errorf("poseidon2 AIR: want %d inputs and outputs, got %d and %d", a.w, len(inputs), len(outputs))
	}
	m, ok := b.Modules[module]
	if !ok {
		return fmt.Errorf("poseidon2 AIR: module %q not found", module)
	}
	params := poseidon2.NewParameters(a.w, a.rf, a.rp)
	post, sbox := a.p2Columns(module)

	// state = M_E · inputs, as linear forms
	state := make([]linForm, a.w)
	in := make([]linForm, a.w)
	for i := range in {
		in[i] = linCol(inputs[i])
	}
	for i := range state {
		state[i] = combine(a.me[i], in)
	}

	last := a.rf + a.rp - 1
	for r := 0; r <= last; r++ {
		rk := params.RoundKeys[r]
		if a.isFullRound(r) {
			// target_i = Σ_j M_E[i][j]·(state_j + rk_j)³
			next := post[r]
			if r == last {
				next = outputs
			}
			for i := 0; i < a.w; i++ {
				rhs := expr.Expr(expr.Const(koalabear.Element{}))
				for j := 0; j < a.w; j++ {
					if a.me[i][j].IsZero() {
						continue
					}
					rhs = rhs.Add(expr.Const(a.me[i][j]).Mul(cube(state[j], rk[j])))
				}
				m.AssertZero(expr.Col(next[i]).Sub(rhs))
			}
			for i := range state {
				state[i] = linCol(next[i])
			}
			continue
		}
		// sbox_r = (state_0 + rk_0)³, then state = M_I · state
		m.AssertZero(expr.Col(sbox[r]).Sub(cube(state[0], rk[0])))
		state[0] = linCol(sbox[r])
		nextState := make([]linForm, a.w)
		for i := range nextState {
			nextState[i] = combine(a.mi[i], state)
		}
		state = nextState
	}
	return nil
}

// Fill computes the internal columns and the outputs from the inputs, on every
// row. Rows whose inputs and outputs are all zero are padding rows: they
// become the genuine instance P(0). On other rows, the traced outputs must
// match.
func (a poseidon2AIR) Fill(t trace.Trace, module string, inputs, outputs []string) error {
	params := poseidon2.NewParameters(a.w, a.rf, a.rp)
	post, sbox := a.p2Columns(module)
	n := len(t.Base[inputs[0]])
	cols := map[string][]koalabear.Element{}
	col := func(name string) []koalabear.Element {
		c, ok := cols[name]
		if !ok {
			c = make([]koalabear.Element, n)
			cols[name] = c
		}
		return c
	}

	last := a.rf + a.rp - 1
	for row := 0; row < n; row++ {
		x := make([]koalabear.Element, a.w)
		padding := true
		for i := range x {
			x[i] = t.Base[inputs[i]][row]
			padding = padding && x[i].IsZero() && t.Base[outputs[i]][row].IsZero()
		}
		state := mulMat(a.me, x)
		for r := 0; r <= last; r++ {
			rk := params.RoundKeys[r]
			if a.isFullRound(r) {
				for j := range state {
					state[j].Add(&state[j], &rk[j])
					var c koalabear.Element
					c.Square(&state[j]).Mul(&c, &state[j])
					state[j] = c
				}
				state = mulMat(a.me, state)
				if r < last {
					for i := range state {
						col(post[r][i])[row] = state[i]
					}
				}
				continue
			}
			state[0].Add(&state[0], &rk[0])
			var c koalabear.Element
			c.Square(&state[0]).Mul(&c, &state[0])
			state[0] = c
			col(sbox[r])[row] = c
			state = mulMat(a.mi, state)
		}
		for i := range state {
			traced := t.Base[outputs[i]][row]
			if !padding && !traced.Equal(&state[i]) {
				return fmt.Errorf("poseidon2 AIR: row %d output %d: traced %s, AIR %s", row, i, traced.String(), state[i].String())
			}
			t.Base[outputs[i]][row] = state[i]
		}
	}
	for name, c := range cols {
		t.SetBase(name, c)
	}
	return nil
}
