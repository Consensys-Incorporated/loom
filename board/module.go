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

package board

import (
	"fmt"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/dag"
	"github.com/consensys/loom/trace"
)

type Relation = expr.Expr

type Module struct {
	Name      string
	Relations []Relation
	GenCol    []Gen // public columns generator (lagrange, permutation columns, selectors, etc)
	N         int
}

func NewModule(name string) Module {
	var res Module
	res.Name = name
	res.Relations = make([]Relation, 0)
	res.GenCol = make([]Gen, 0)
	return res
}

type CompiledModule struct {
	Name              string
	GenCol            []Gen // public columns generator (lagrange, permutation columns, etc)
	N                 int
	VanishingRelation *dag.DAG
	D                 *fft.Domain
}

type Gen interface {
	Gen(t trace.Trace, m *CompiledModule) error
}

type RangeColumnGen struct {
	Bound uint64
}

func (rc RangeColumnGen) Gen(t trace.Trace, m *CompiledModule) error {
	res := make([]koalabear.Element, m.N)
	for i := 0; i < int(rc.Bound); i++ {
		res[i].SetUint64(uint64(i))
	}
	name := constants.RangeColName(rc.Bound)
	if _, ok := t.GetField(name); ok {
		return nil
	}
	t.SetBase(name, res)
	return nil
}

type LagrangeRelativeGen struct {
	i int // <- real position: module.N-i-1
}

func (p LagrangeRelativeGen) Gen(t trace.Trace, m *CompiledModule) error {
	res := make([]koalabear.Element, m.N)
	res[m.N-1-p.i].SetOne()
	name := constants.LagrangeNameRelative(m.Name, p.i)
	if _, ok := t.GetField(name); ok {
		return nil
	}
	t.SetBase(name, res)
	return nil
}

type LagrangeGen struct {
	i int
}

func (p LagrangeGen) Gen(t trace.Trace, m *CompiledModule) error {
	res := make([]koalabear.Element, m.N)
	res[p.i].SetOne()
	name := constants.LagrangeName(m.Name, p.i)
	if _, ok := t.GetField(name); ok {
		return nil
	}
	t.SetBase(name, res)
	return nil
}

// NameIthIDSupport returns the name of the i-th chunk of the support of a permutation
// (common to every permutation within a module)
func (m *Module) NameIthIDSupport(i int) string {
	return fmt.Sprintf("%s.ID_%d_%d", m.Name, i, m.N)
}

// NameIthIDSupport returns the name of the i-th chunk of the support of a permutation
// (common to every permutation within a CompiledModule)
func (m *CompiledModule) NameIthIDSupport(i int) string {
	return fmt.Sprintf("%s.ID_%d_%d", m.Name, i, m.N)
}

func (m *Module) LagrangeColRelative(i int) expr.Expr {
	m.GenCol = append(m.GenCol, LagrangeRelativeGen{i: i})
	name := constants.LagrangeNameRelative(m.Name, i)
	return expr.Lagrange(name)
}

// asserts that A[m.N-1-i]=B[m.N-1-i]
func (m *Module) AssertEqualRelativeAt(A, B expr.Expr, i int) {
	relation := A.Sub(B)
	relation = relation.Mul(m.LagrangeColRelative(i))
	m.AssertZero(relation)
}

func (m *Module) AssertEqualAt(A, B expr.Expr, i int) {
	relation := A.Sub(B)
	relation = relation.Mul(m.LagrangeCol(i))
	m.AssertZero(relation)
}

func (m *Module) AssertEqualFirstEntry(A, B expr.Expr) {
	m.AssertEqualAt(A, B, 0)
}

func (m *Module) AssertEqualLastEntry(A, B expr.Expr) {
	m.AssertEqualRelativeAt(A, B, 0)
}

func (m *Module) LagrangeCol(i int) expr.Expr {
	m.GenCol = append(m.GenCol, LagrangeGen{i: i})
	name := constants.LagrangeName(m.Name, i)
	return expr.Lagrange(name)
}

func (m *Module) AssertZero(relation expr.Expr) {
	m.Relations = append(m.Relations, relation)
}

func (m *Module) AssertZeroFirstEntry(relation expr.Expr) {
	m.AssertZeroAt(relation, 0)
}

func (m *Module) AssertZeroLastEntry(relation expr.Expr) {
	m.AssertZeroRelativeAt(relation, 0)
}

func (m *Module) AssertZeroExceptLastEntry(relation expr.Expr) {
	one := koalabear.One()
	conj := expr.Const(one).Sub(m.LagrangeColRelative(0))
	_relation := conj.Mul(relation)
	m.AssertZero(_relation)
}

func (m *Module) AssertZeroExceptAt(relation expr.Expr, i ...int) {
	one := koalabear.One()
	conj := expr.Const(one).Sub(m.LagrangeCol(i[0]))
	for k := 1; k < len(i); k++ {
		_conj := expr.Const(one).Sub(m.LagrangeCol(i[k]))
		conj = conj.Mul(_conj)
	}
	_relation := relation.Mul(conj)
	m.AssertZero(_relation)
}

func (m *Module) AssertZeroRelativeAt(relation expr.Expr, i ...int) {
	disj := expr.Expr(m.LagrangeColRelative(i[0]))
	for k := 1; k < len(i); k++ {
		disj = disj.Add(m.LagrangeColRelative(i[k]))
	}
	_relation := relation.Mul(disj)
	m.AssertZero(_relation)
}

func (m *Module) AssertZeroAt(relation expr.Expr, i ...int) {
	disj := expr.Expr(m.LagrangeCol(i[0]))
	for k := 1; k < len(i); k++ {
		disj = disj.Add(m.LagrangeCol(i[k]))
	}
	_relation := relation.Mul(disj)
	m.AssertZero(_relation)
}

type SelectorGen struct {
	Idx  []int
	Name string
}

func (s SelectorGen) Gen(t trace.Trace, m *CompiledModule) error {
	res := make([]koalabear.Element, m.N)
	for _, idx := range s.Idx {
		res[idx].SetOne()
	}
	err := t.PutBase(s.Name, res)
	if err != nil {
		return err
	}
	return nil
}

type PermutationGen struct {
	S               []int64
	PermutationName string
}

func (p PermutationGen) NameIthPermutationChunk(i int) string {
	return fmt.Sprintf("%s_%d", p.PermutationName, i)
}

func NewPermutationGen(S []int64, permutationName string) PermutationGen {
	return PermutationGen{
		S:               S,
		PermutationName: permutationName,
	}
}

func (p PermutationGen) Gen(t trace.Trace, m *CompiledModule) error {

	// 1 - gen permutation support
	if len(p.S)%m.N != 0 {
		return fmt.Errorf("size of permutation %d is not a multiplie of the module size %d", len(p.S), m.N)
	}
	nbChunks := len(p.S) / m.N
	support, err := generateSupport(nbChunks, m.N)
	if err != nil {
		return err
	}
	for i := 0; i < nbChunks; i++ {
		err := t.PutBase(m.NameIthIDSupport(i), support[i])
		if err != nil {
			return err
		}
	}

	// 2 - register permutation columns
	perm := generatePermutation(support, p.S)
	for i := 0; i < nbChunks; i++ {
		err := t.PutBase(p.NameIthPermutationChunk(i), perm[i])
		if err != nil {
			return err
		}
	}

	return nil
}

func generateSupport(nbChunks, N int) ([][]koalabear.Element, error) {
	var acc koalabear.Element
	frGen := fft.GeneratorFullMultiplicativeGroup()
	acc.Set(&frGen)
	res := make([][]koalabear.Element, nbChunks)
	res[0] = make([]koalabear.Element, N)
	res[0][0].SetOne()
	g, err := koalabear.Generator(uint64(N))
	if err != nil {
		return res, err
	}
	for i := 1; i < N; i++ {
		res[0][i].Mul(&res[0][i-1], &g)
	}
	for i := 1; i < nbChunks; i++ {
		res[i] = make([]koalabear.Element, N)
		for j := 0; j < N; j++ {
			res[i][j].Mul(&res[i-1][j], &frGen)
		}
	}
	return res, nil
}

func generatePermutation(support [][]koalabear.Element, S []int64) [][]koalabear.Element {
	res := make([][]koalabear.Element, len(support))
	N := len(support[0])
	for i := 0; i < len(support); i++ {
		res[i] = make([]koalabear.Element, N)
	}
	for i := 0; i < len(S); i++ {
		s := S[i]
		res[i/N][i%N].Set(&support[int(s)/N][int(s)%N])
	}
	return res
}
