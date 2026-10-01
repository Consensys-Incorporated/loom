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

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
	"github.com/consensys/loom/trace"
)

// E6MulGadget is the AIR of e6_mul when declared #[native]: one
// multiplication z = x·y per row, over the 18 columns x, y, z, with 6
// degree-2 constraints. In zkc, the same multiplication costs its caller about
// 80 registers, one per base product.
type E6MulGadget struct{}

var _ zkcv.Gadget = E6MulGadget{}

// e6MulExprs returns z = x·y as expressions (schoolbook over E2, with
// u² = 3 and v³ = u + 1), in the layout (B0.A0, B0.A1, B1.A0, B1.A1, B2.A0,
// B2.A1).
func e6MulExprs(x, y []expr.Expr) []expr.Expr {
	three := expr.Const(koalabear.NewElement(3))
	// E2 product (a0 + a1·u)(b0 + b1·u) = (a0·b0 + 3·a1·b1) + (a0·b1 + a1·b0)·u
	mul2 := func(a0, a1, b0, b1 expr.Expr) (expr.Expr, expr.Expr) {
		return a0.Mul(b0).Add(three.Mul(a1.Mul(b1))), a0.Mul(b1).Add(a1.Mul(b0))
	}
	// ξ·(p + q·u) = (p + 3·q) + (p + q)·u
	xi := func(p, q expr.Expr) (expr.Expr, expr.Expr) {
		return p.Add(three.Mul(q)), p.Add(q)
	}
	p := func(i, j int) (expr.Expr, expr.Expr) {
		return mul2(x[2*i], x[2*i+1], y[2*j], y[2*j+1])
	}
	p00r, p00u := p(0, 0)
	p01r, p01u := p(0, 1)
	p02r, p02u := p(0, 2)
	p10r, p10u := p(1, 0)
	p11r, p11u := p(1, 1)
	p12r, p12u := p(1, 2)
	p20r, p20u := p(2, 0)
	p21r, p21u := p(2, 1)
	p22r, p22u := p(2, 2)
	t0r, t0u := xi(p12r.Add(p21r), p12u.Add(p21u))
	t1r, t1u := xi(p22r, p22u)
	return []expr.Expr{
		p00r.Add(t0r), p00u.Add(t0u),
		p01r.Add(p10r).Add(t1r), p01u.Add(p10u).Add(t1u),
		p02r.Add(p11r).Add(p20r), p02u.Add(p11u).Add(p20u),
	}
}

// E6MulExprs returns z = x·y as expressions over the six base coordinates of
// x and y, in the layout of e6MulExprs.
func E6MulExprs(x, y []expr.Expr) []expr.Expr { return e6MulExprs(x, y) }

// Define adds z = x·y on every row.
func (E6MulGadget) Define(b *board.Builder, module string, inputs, outputs []string) error {
	if len(inputs) != 12 || len(outputs) != 6 {
		return fmt.Errorf("e6_mul gadget: want 12 inputs and 6 outputs, got %d and %d", len(inputs), len(outputs))
	}
	m, ok := b.Modules[module]
	if !ok {
		return fmt.Errorf("e6_mul gadget: module %q not found", module)
	}
	cols := func(names []string) []expr.Expr {
		res := make([]expr.Expr, len(names))
		for i, n := range names {
			res[i] = expr.Col(n)
		}
		return res
	}
	z := e6MulExprs(cols(inputs[:6]), cols(inputs[6:]))
	for i := range z {
		m.AssertZero(expr.Col(outputs[i]).Sub(z[i]))
	}
	return nil
}

func e6At(t trace.Trace, names []string, row int) ext.E6 {
	var x ext.E6
	for i, c := range []*koalabear.Element{&x.B0.A0, &x.B0.A1, &x.B1.A0, &x.B1.A1, &x.B2.A0, &x.B2.A1} {
		*c = t.Base[names[i]][row]
	}
	return x
}

// Fill recomputes z on every row and checks it against the trace. Padding rows
// (all zero) are valid as they are.
func (E6MulGadget) Fill(t trace.Trace, module string, inputs, outputs []string) error {
	n := len(t.Base[inputs[0]])
	for row := 0; row < n; row++ {
		x, y := e6At(t, inputs[:6], row), e6At(t, inputs[6:], row)
		var z ext.E6
		z.Mul(&x, &y)
		want := e6At(t, outputs, row)
		if !z.Equal(&want) {
			return fmt.Errorf("e6_mul gadget: row %d: traced %s, gadget %s", row, want.String(), z.String())
		}
	}
	return nil
}
