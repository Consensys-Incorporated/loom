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
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"
)

// Poseidon2Gadget is the AIR of the P2 core: one
// permutation per row, laid out as Plonky3's poseidon2-air with S-box degree 3
// and no S-box registers. Its columns are
//
//	inputs                 24
//	post of full rounds    24 × (full rounds − 1)   (the last one is the outputs)
//	partial S-box outputs  1 × partial rounds
//	outputs                24
//
// i.e. 189 columns, and every constraint has degree 3. Between committed
// columns the state is tracked as linear forms, so the linear layers cost no
// columns.
type Poseidon2Gadget struct{}

// p2Matrices returns the external and internal matrices as dense 24×24
// matrices, obtained by applying gnark-crypto's addition chains to unit vectors.
var p2Matrices = func() (me, mi [P2Width][P2Width]koalabear.Element) {
	for j := 0; j < P2Width; j++ {
		var unit [P2Width]koalabear.Element
		unit[j].SetOne()
		e, i := unit, unit
		matExternal(e[:])
		matInternal(i[:])
		for r := 0; r < P2Width; r++ {
			me[r][j], mi[r][j] = e[r], i[r]
		}
	}
	return me, mi
}

var p2ME, p2MI = p2Matrices()

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
	for i, d := range p2Diag24() {
		var t koalabear.Element
		t.Mul(&s[i], &d)
		s[i].Add(&sum, &t)
	}
}

func mulMat(m *[P2Width][P2Width]koalabear.Element, x []koalabear.Element) []koalabear.Element {
	res := make([]koalabear.Element, P2Width)
	for r := range res {
		for j := range x {
			var t koalabear.Element
			t.Mul(&m[r][j], &x[j])
			res[r].Add(&res[r], &t)
		}
	}
	return res
}

func isFullRound(r int) bool {
	return r < p2HalfFullRounds || r >= p2HalfFullRounds+P2PartialRounds
}

// p2Columns names the gadget's internal columns: post[r][i] for every full
// round but the last, and sbox[r] for partial rounds.
func p2Columns(module string) (post map[int][]string, sbox map[int]string) {
	post, sbox = map[int][]string{}, map[int]string{}
	last := P2FullRounds + P2PartialRounds - 1
	for r := 0; r <= last; r++ {
		switch {
		case r == last:
		case isFullRound(r):
			post[r] = make([]string, P2Width)
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
func combine(m [P2Width]koalabear.Element, xs []linForm) linForm {
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

// expr renders the form as a fresh expression tree.
func (l linForm) expr() expr.Expr {
	res := expr.Expr(expr.Const(l.c))
	for v, c := range l.terms {
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
func (Poseidon2Gadget) Define(b *board.Builder, module string, inputs, outputs []string) error {
	if len(inputs) != P2Width || len(outputs) != P2Width {
		return fmt.Errorf("p2_perm gadget: want %d inputs and outputs, got %d and %d", P2Width, len(inputs), len(outputs))
	}
	m, ok := b.Modules[module]
	if !ok {
		return fmt.Errorf("p2_perm gadget: module %q not found", module)
	}
	params := poseidon2.NewParameters(P2Width, P2FullRounds, P2PartialRounds)
	post, sbox := p2Columns(module)

	// state = M_E · inputs, as linear forms
	state := make([]linForm, P2Width)
	in := make([]linForm, P2Width)
	for i := range in {
		in[i] = linCol(inputs[i])
	}
	for i := range state {
		state[i] = combine(p2ME[i], in)
	}

	last := P2FullRounds + P2PartialRounds - 1
	for r := 0; r <= last; r++ {
		rk := params.RoundKeys[r]
		if isFullRound(r) {
			// target_i = Σ_j M_E[i][j]·(state_j + rk_j)³
			next := post[r]
			if r == last {
				next = outputs
			}
			for i := 0; i < P2Width; i++ {
				rhs := expr.Expr(expr.Const(koalabear.Element{}))
				for j := 0; j < P2Width; j++ {
					if p2ME[i][j].IsZero() {
						continue
					}
					rhs = rhs.Add(expr.Const(p2ME[i][j]).Mul(cube(state[j], rk[j])))
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
		nextState := make([]linForm, P2Width)
		for i := range nextState {
			nextState[i] = combine(p2MI[i], state)
		}
		state = nextState
	}
	return nil
}

// Fill computes the internal columns and the outputs from the inputs, on every
// row. Rows whose inputs and outputs are all zero are padding rows: they
// become the genuine instance P(0). On other rows, the traced outputs must
// match.
func (Poseidon2Gadget) Fill(t trace.Trace, module string, inputs, outputs []string) error {
	params := poseidon2.NewParameters(P2Width, P2FullRounds, P2PartialRounds)
	post, sbox := p2Columns(module)
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

	last := P2FullRounds + P2PartialRounds - 1
	for row := 0; row < n; row++ {
		x := make([]koalabear.Element, P2Width)
		padding := true
		for i := range x {
			x[i] = t.Base[inputs[i]][row]
			padding = padding && x[i].IsZero() && t.Base[outputs[i]][row].IsZero()
		}
		state := mulMat(&p2ME, x)
		for r := 0; r <= last; r++ {
			rk := params.RoundKeys[r]
			if isFullRound(r) {
				for j := range state {
					state[j].Add(&state[j], &rk[j])
					var c koalabear.Element
					c.Square(&state[j]).Mul(&c, &state[j])
					state[j] = c
				}
				state = mulMat(&p2ME, state)
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
			state = mulMat(&p2MI, state)
		}
		for i := range state {
			traced := t.Base[outputs[i]][row]
			if !padding && !traced.Equal(&state[i]) {
				return fmt.Errorf("p2_perm gadget: row %d output %d: traced %s, gadget %s", row, i, traced.String(), state[i].String())
			}
			t.Base[outputs[i]][row] = state[i]
		}
	}
	for name, c := range cols {
		t.SetBase(name, c)
	}
	return nil
}
