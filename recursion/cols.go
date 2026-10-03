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
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/trace"
)

func setupCol(module, name string) expr.Expr { return expr.Setup(module + "." + name) }

func col(module, name string) expr.Expr { return expr.Col(module + "." + name) }

func colShift(module, name string, s int) expr.Expr {
	return expr.Col(module+"."+name, expr.WithShift(s))
}

func constE(v uint64) expr.Expr { return expr.Const(koalabear.NewElement(v)) }

func one() expr.Expr { return constE(1) }

func cellCols(module, prefix string, from int) [CellWidth]expr.Expr {
	var res [CellWidth]expr.Expr
	for i := range res {
		res[i] = col(module, fmt.Sprintf("%s%d", prefix, from+i))
	}
	return res
}

// TODO maybe put the cols code in trace/
// cols accumulates the columns of a module.
type cols struct {
	n    int
	vals map[string][]koalabear.Element
}

func newCols(n int) *cols { return &cols{n: n, vals: map[string][]koalabear.Element{}} }

func (c *cols) declare(names ...string) {
	for _, n := range names {
		c.get(n)
	}
}

func (c *cols) get(name string) []koalabear.Element {
	v, ok := c.vals[name]
	if !ok {
		v = make([]koalabear.Element, c.n)
		c.vals[name] = v
	}
	return v
}

func (c *cols) set(name string, row int, v uint64) { c.get(name)[row].SetUint64(v) }

func (c *cols) setInt(name string, row int, v int64) { c.get(name)[row].SetInt64(v) }

func (c *cols) setElem(name string, row int, v koalabear.Element) { c.get(name)[row] = v }

func (c *cols) store(t trace.Trace, module string) {
	for name, v := range c.vals {
		t.SetBase(module+"."+name, v)
	}
}

func zero() expr.Expr { return expr.Const(koalabear.Element{}) }

func constElem(v koalabear.Element) expr.Expr { return expr.Const(v) }

func setupCellCols(module, prefix string) [CellWidth]expr.Expr {
	var res [CellWidth]expr.Expr
	for i := range res {
		res[i] = setupCol(module, fmt.Sprintf("%s%d", prefix, i))
	}
	return res
}

// e6Cols returns the 6 columns prefix0..5, shifted by s.
func e6Cols(module, prefix string, s int) []expr.Expr {
	res := make([]expr.Expr, 6)
	for i := range res {
		res[i] = colShift(module, fmt.Sprintf("%s%d", prefix, i), s)
	}
	return res
}

// cellOf pads lanes to a cell tuple with zero lanes.
func cellOf(lanes ...expr.Expr) [CellWidth]expr.Expr {
	var res [CellWidth]expr.Expr
	for i := range res {
		if i < len(lanes) {
			res[i] = lanes[i]
		} else {
			res[i] = zero()
		}
	}
	return res
}

func (c *cols) setE6(prefix string, row int, x ext.E6) {
	cell := E6Cell(x)
	for i := range 6 {
		c.setElem(fmt.Sprintf("%s%d", prefix, i), row, cell[i])
	}
}

func (c *cols) setCell(prefix string, row int, v Cell) {
	for i := range CellWidth {
		c.setElem(fmt.Sprintf("%s%d", prefix, i), row, v[i])
	}
}

func (c *cols) declareLanes(prefix string, n int) {
	for i := range n {
		c.declare(fmt.Sprintf("%s%d", prefix, i))
	}
}
