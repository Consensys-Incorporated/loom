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

package expr

import (
	"fmt"
	"math"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/field"
)

const NegInf = math.MinInt

type LeafType int

const (
	CommittedColumn LeafType = iota
	ChallengeColumn
	ConstantColumn
	SetupColumn // structural columns like ql, qr, etc in plonk, committed beforehand

	// VerifierColumn is a column whose evaluation at zeta is recomputed by the
	// verifier itself rather than read from a prover opening. Which formula to
	// use is carried by Leaf.Hook; see HookID.
	VerifierColumn
)

// HookID selects the verifier-side routine that evaluates a VerifierColumn at
// zeta. The mapping HookID -> implementation lives in verifier.HookMap; it is
// kept out of this package so the AST stays free of verifier internals.
type HookID int

const (
	// NoHook is the zero value: an unset hook. A VerifierColumn carrying it is
	// a construction bug, and the verifier rejects it rather than silently
	// picking a formula.
	NoHook HookID = iota
	LagrangeHook
	PublicInputHook  // verifier-supplied statement values
	ExposedValueHook // prover-exposed local values, carried by the proof
)

func (h HookID) String() string {
	switch h {
	case NoHook:
		return "none"
	case LagrangeHook:
		return "lagrange"
	case PublicInputHook:
		return "public-input"
	case ExposedValueHook:
		return "exposed-value"
	default:
		return fmt.Sprintf("unknown(%d)", int(h))
	}
}

type Leaf struct {
	Type  LeafType
	Idx   int // used for EvalPointWise, as a lookup to avoid maps
	Shift int
	Name  string
	Field field.Kind
	Hook  HookID            // only set for VerifierColumn
	Value koalabear.Element // only set for Const type
}

type LeafOption func(leaf *Leaf)

func WithShift(shift int) LeafOption {
	return func(leaf *Leaf) {
		leaf.Shift = shift
	}
}

func applyLeafOptions(leaf *Leaf, opts ...LeafOption) *Leaf {
	for _, opt := range opts {
		if opt != nil {
			opt(leaf)
		}
	}
	return leaf
}

// Config useful for querying the leaves
type Config struct {
	WoCommittedColumns bool
	WoSetupColumns     bool
	WoRotatedColumns   bool
	WoChallenges       bool
	WoVerifierColumns  bool
}

type Option func(*Config)

// Leaves() doesnt return shifted leafs
func WithoutRotatedColumns() Option {
	return func(c *Config) {
		c.WoRotatedColumns = true
	}
}

// Leaves() doesnt return the CommittedColumns
func WithoutCommittedColumns() Option {
	return func(c *Config) {
		c.WoCommittedColumns = true
	}
}

// Leaves() doesnt return the SetupColumn
func WithoutSetupColumns() Option {
	return func(c *Config) {
		c.WoSetupColumns = true
	}
}

// Leaves() doesnt return the Challenge
func WithoutChallenges() Option {
	return func(c *Config) {
		c.WoChallenges = true
	}
}

// Leaves() doesnt return the VerifierColumns (Lagrange, public inputs and
// exposed values), i.e. every column the verifier evaluates at zeta itself.
func WithoutVerifierColumns() Option {
	return func(c *Config) {
		c.WoVerifierColumns = true
	}
}

func NewConfig(opts ...Option) Config {
	var res Config
	for _, opt := range opts {
		opt(&res)
	}
	return res
}

var OnlyChallenges = []Option{WithoutSetupColumns(), WithoutCommittedColumns(), WithoutRotatedColumns(), WithoutVerifierColumns()}
var OnlySetupColumns = []Option{WithoutChallenges(), WithoutCommittedColumns(), WithoutVerifierColumns()}
var OnlyVerifierColumns = []Option{WithoutSetupColumns(), WithoutChallenges(), WithoutCommittedColumns(), WithoutRotatedColumns()}

type Expr interface {
	Degree() int
	String() string
	Add(Expr) Expr
	Sub(Expr) Expr
	Mul(Expr) Expr
	Pow(uint32) Expr

	// Leaves returns every non-Const Leaf in the expression tree, only by their names.
	// the shifted columns have their own ID: baseName + "shifted_<shift>"
	Leaves(config Config) []string

	// LeavesFull returns every non-Const Leaf in the expression tree (the full structure).
	LeavesFull(config Config) []*Leaf

	// ReplaceLeafByExpression finds all occurence of leaf in the tree and replace it with e
	ReplaceLeafByExpression(leaf string, e Expr) Expr

	// recurse through expr, until an Expr (call it E) of degree <= deg is found.
	// When E is found, remove E from expr and replace this subexpression with Col(E.String())
	// Return E.
	Prune(deg int) Expr

	// EvaluateOnIthEntry evaluates the expression at row i of the polynomial slice _Pi.
	// Each leaf's Idx field selects which polynomial in _Pi to read from.
	// Row selection rules:
	//   - Const leaf          : returns the constant value (ignores _Pi and i)
	//   - len(_Pi[l.Idx]) == 1: constant polynomial, always returns _Pi[l.Idx][0]
	//   - shifted leaf        : returns _Pi[l.Idx][(i + N + l.Shift) % N] where N = len(_Pi[l.Idx])
	//   - unshifted leaf      : returns _Pi[l.Idx][i]
	// Leaf Idx values must be set by the caller before invoking this method (e.g. via LeavesFull).
	EvaluateOnIthEntry(_Pi [][]koalabear.Element, i int) koalabear.Element

	// Evaluate substitutes each leaf name with the corresponding field element
	// from vals and returns the result. Panics if a required name is absent.
	// This function exists for testing purpose, in the protocols in std/ for instance
	// we use EvaluateWithIdx (through EvalPointWise).
	Evaluate(vals map[string]koalabear.Element) koalabear.Element
}

func Col(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: CommittedColumn, Name: name}, opts...)
}

func ExtCol(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: CommittedColumn, Name: name, Field: field.Ext}, opts...)
}

func Setup(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: SetupColumn, Name: name}, opts...)
}

func ExtSetup(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: SetupColumn, Name: name, Field: field.Ext}, opts...)
}

func Exposed(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: VerifierColumn, Hook: ExposedValueHook, Name: name}, opts...)
}

func PublicInput(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: VerifierColumn, Hook: PublicInputHook, Name: name}, opts...)
}

// PublicInputExt is kept as a distinct constructor for callers that want to
// declare the extension field explicitly; VerifierColumn evaluates in E6
// regardless, so it is now equivalent to PublicInput.
func PublicInputExt(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: VerifierColumn, Hook: PublicInputHook, Name: name, Field: field.Ext}, opts...)
}

func Lagrange(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: VerifierColumn, Hook: LagrangeHook, Name: name}, opts...)
}

func Challenge(name string, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: ChallengeColumn, Name: name, Field: field.Ext}, opts...)
}

func Const(value koalabear.Element, opts ...LeafOption) *Leaf {
	return applyLeafOptions(&Leaf{Type: ConstantColumn, Value: value}, opts...)
}

// FieldKind reports the field a leaf's values live in. Challenges are drawn
// from E6, and VerifierColumns are evaluated at zeta by the verifier, which
// works in E6 throughout — so both are Ext regardless of the declared Field.
func (l *Leaf) FieldKind() field.Kind {
	if l.Type == ChallengeColumn || l.Type == VerifierColumn {
		return field.Ext
	}
	return l.Field
}

func FieldOf(e Expr) field.Kind {
	return FieldOfWithColumnFields(e, nil)
}

func FieldOfWithColumnFields(e Expr, columnFields map[string]field.Kind) field.Kind {
	switch v := e.(type) {
	case *Leaf:
		f := v.FieldKind()
		switch v.Type {
		// VerifierColumn is deliberately absent: FieldKind already pins it to
		// Ext, so joining the inferred map entry could not change the result.
		case CommittedColumn, SetupColumn:
			if columnFields != nil {
				f = field.Join(f, columnFields[v.Name])
			}
		}
		return f
	case *Add:
		return field.Join(FieldOfWithColumnFields(v.Left, columnFields), FieldOfWithColumnFields(v.Right, columnFields))
	case *Sub:
		return field.Join(FieldOfWithColumnFields(v.Left, columnFields), FieldOfWithColumnFields(v.Right, columnFields))
	case *Mul:
		return field.Join(FieldOfWithColumnFields(v.Left, columnFields), FieldOfWithColumnFields(v.Right, columnFields))
	case *Pow:
		return FieldOfWithColumnFields(v.Base, columnFields)
	default:
		panic(fmt.Sprintf("FieldOfWithColumnFields: unknown Expr type %T", e))
	}
}

func (l *Leaf) String() string {
	if l.Type == ConstantColumn {
		return l.Value.String()
	}
	if l.Shift != 0 {
		return fmt.Sprintf("%s_shift_%d", l.Name, l.Shift)
	}
	return l.Name
}

func (l *Leaf) Degree() int {
	switch l.Type {
	case ConstantColumn:
		if l.Value.IsZero() {
			return NegInf
		}
		return 0
	case ChallengeColumn:
		return 0
	default: // CommittedColumn, SetupColumn, VerifierColumn
		return 1
	}
}

func (l *Leaf) Add(e Expr) Expr { return &Add{l, e} }
func (l *Leaf) Sub(e Expr) Expr { return &Sub{l, e} }
func (l *Leaf) Mul(e Expr) Expr { return &Mul{l, e} }
func (l *Leaf) Pow(n uint32) Expr {
	if n > 2 {
		return squareAndMultiply(l, n)
	}
	return &Pow{l, n}
}

func (l *Leaf) Leaves(config Config) []string {
	if l.Type == ConstantColumn {
		return []string{}
	}
	if config.WoRotatedColumns && l.Shift != 0 {
		return []string{}
	}

	switch l.Type {
	case CommittedColumn:
		if config.WoCommittedColumns {
			return []string{}
		}
		return []string{l.String()}
	case SetupColumn:
		if config.WoSetupColumns {
			return []string{}
		}
		return []string{l.String()}
	case ChallengeColumn:
		if config.WoChallenges {
			return []string{}
		}
		return []string{l.String()}
	case VerifierColumn:
		if config.WoVerifierColumns {
			return []string{}
		}
		return []string{l.String()}
	}
	return []string{}
}

func (l *Leaf) ReplaceLeafByExpression(leaf string, e Expr) Expr {
	if l.Type == ConstantColumn {
		return l
	}
	if l.String() == leaf {
		return e
	}

	return l
}

func (l *Leaf) Prune(deg int) Expr { return pruneSearch(l, deg) }

func (l *Leaf) Evaluate(vals map[string]koalabear.Element) koalabear.Element {
	if l.Type == ConstantColumn {
		return l.Value
	}
	key := l.String()
	v, ok := vals[key]
	if !ok {
		panic("Evaluate: missing value for " + key)
	}
	return v
}

func (l *Leaf) EvaluateOnIthEntry(_Pi [][]koalabear.Element, i int) koalabear.Element {
	if l.Type == ConstantColumn {
		return l.Value
	}
	p := _Pi[l.Idx]
	if len(p) == 1 {
		return p[0]
	}
	N := len(p)
	if l.Shift != 0 {
		return p[(i+N+l.Shift)%N]
	}
	return p[i]
}

type Add struct {
	Left, Right Expr
}

func (a Add) Degree() int {
	leftDegree := a.Left.Degree()
	rightDegree := a.Right.Degree()
	return max(leftDegree, rightDegree)
}

func (a Add) String() string {
	return "(" + a.Left.String() + " + " + a.Right.String() + ")"
}

type Sub struct {
	Left, Right Expr
}

func (s Sub) Degree() int {
	leftDegree := s.Left.Degree()
	rightDegree := s.Right.Degree()
	return max(leftDegree, rightDegree)
}

func (s Sub) String() string {
	return "(" + s.Left.String() + " - " + s.Right.String() + ")"
}

type Mul struct {
	Left, Right Expr
}

func (m Mul) Degree() int {
	leftDegree := m.Left.Degree()
	rightDegree := m.Right.Degree()
	return leftDegree + rightDegree
}

func (m Mul) String() string {
	return "(" + m.Left.String() + " * " + m.Right.String() + ")"
}

type Pow struct {
	Base Expr
	Exp  uint32
}

func (p Pow) Degree() int {
	return p.Base.Degree() * int(p.Exp)
}

func (p Pow) String() string {
	return "(" + p.Base.String() + " ^ " + fmt.Sprintf("%d", p.Exp) + ")"
}

func (a *Add) Add(e Expr) Expr { return &Add{a, e} }
func (a *Add) Sub(e Expr) Expr { return &Sub{a, e} }
func (a *Add) Mul(e Expr) Expr { return &Mul{a, e} }
func (a *Add) Pow(n uint32) Expr {
	if n > 2 {
		return squareAndMultiply(a, n)
	}
	return &Pow{a, n}
}

func (s *Sub) Add(e Expr) Expr { return &Add{s, e} }
func (s *Sub) Sub(e Expr) Expr { return &Sub{s, e} }
func (s *Sub) Mul(e Expr) Expr { return &Mul{s, e} }
func (s *Sub) Pow(n uint32) Expr {
	if n > 2 {
		return squareAndMultiply(s, n)
	}
	return &Pow{s, n}
}

func (m *Mul) Add(e Expr) Expr { return &Add{m, e} }
func (m *Mul) Sub(e Expr) Expr { return &Sub{m, e} }
func (m *Mul) Mul(e Expr) Expr { return &Mul{m, e} }
func (m *Mul) Pow(n uint32) Expr {
	if n > 2 {
		return squareAndMultiply(m, n)
	}
	return &Pow{m, n}
}

func (p *Pow) Add(e Expr) Expr { return &Add{p, e} }
func (p *Pow) Sub(e Expr) Expr { return &Sub{p, e} }
func (p *Pow) Mul(e Expr) Expr { return &Mul{p, e} }
func (p *Pow) Pow(n uint32) Expr {
	if n > 2 {
		return squareAndMultiply(p, n)
	}
	return &Pow{p, n}
}

func Sum(exprs ...Expr) Expr {
	if len(exprs) == 0 {
		panic("empty sum")
	}
	result := exprs[0]
	for i := 1; i < len(exprs); i++ {
		result = &Add{result, exprs[i]}
	}
	return result
}

func Prod(exprs ...Expr) Expr {
	if len(exprs) == 0 {
		panic("empty product")
	}
	result := exprs[0]
	for i := 1; i < len(exprs); i++ {
		result = &Mul{result, exprs[i]}
	}
	return result
}

// isPrunable returns true if e is a composite sub-expression (not a bare leaf)
// that is eligible to be extracted into a new intermediate polynomial.
func isPrunable(e Expr) bool {
	switch e.(type) {
	case *Leaf:
		return false
	}
	return true
}

// pruneSearch recurses through expr looking for a composite child node E with degree <= deg.
// When found, E is replaced in-place with Col(E.String()) and E is returned.
// Leaf children are skipped (they are already leaves; replacing them is a no-op).
// Returns nil if no such sub-expression is found.
func pruneSearch(expr Expr, deg int) Expr {
	switch e := expr.(type) {
	case *Leaf:
		return nil
	case *Add:
		if isPrunable(e.Left) && e.Left.Degree() <= deg {
			found := e.Left
			e.Left = Col(found.String())
			return found
		}
		if isPrunable(e.Right) && e.Right.Degree() <= deg {
			found := e.Right
			e.Right = Col(found.String())
			return found
		}
		if r := pruneSearch(e.Left, deg); r != nil {
			return r
		}
		return pruneSearch(e.Right, deg)
	case *Sub:
		if isPrunable(e.Left) && e.Left.Degree() <= deg {
			found := e.Left
			e.Left = Col(found.String())
			return found
		}
		if isPrunable(e.Right) && e.Right.Degree() <= deg {
			found := e.Right
			e.Right = Col(found.String())
			return found
		}
		if r := pruneSearch(e.Left, deg); r != nil {
			return r
		}
		return pruneSearch(e.Right, deg)
	case *Mul:
		if isPrunable(e.Left) && e.Left.Degree() <= deg {
			found := e.Left
			e.Left = Col(found.String())
			return found
		}
		if isPrunable(e.Right) && e.Right.Degree() <= deg {
			found := e.Right
			e.Right = Col(found.String())
			return found
		}
		if r := pruneSearch(e.Left, deg); r != nil {
			return r
		}
		return pruneSearch(e.Right, deg)
	case *Pow:
		if isPrunable(e.Base) && e.Base.Degree() <= deg {
			found := e.Base
			e.Base = Col(found.String())
			return found
		}
		return pruneSearch(e.Base, deg)
	}
	return nil
}

func (a *Add) Leaves(config Config) []string {
	return append(a.Left.Leaves(config), a.Right.Leaves(config)...)
}
func (s *Sub) Leaves(config Config) []string {
	return append(s.Left.Leaves(config), s.Right.Leaves(config)...)
}
func (m *Mul) Leaves(config Config) []string {
	return append(m.Left.Leaves(config), m.Right.Leaves(config)...)
}
func (p *Pow) Leaves(config Config) []string { return p.Base.Leaves(config) }

func (l *Leaf) LeavesFull(config Config) []*Leaf {
	if l.Type == ConstantColumn {
		return nil
	}
	if config.WoRotatedColumns && l.Shift != 0 {
		return nil
	}

	switch l.Type {
	case CommittedColumn:
		if config.WoCommittedColumns {
			return nil
		}
	case SetupColumn:
		if config.WoSetupColumns {
			return nil
		}
	case ChallengeColumn:
		if config.WoChallenges {
			return nil
		}
	case VerifierColumn:
		if config.WoVerifierColumns {
			return nil
		}
	}
	return []*Leaf{l}
}
func (a *Add) LeavesFull(config Config) []*Leaf {
	return append(a.Left.LeavesFull(config), a.Right.LeavesFull(config)...)
}
func (s *Sub) LeavesFull(config Config) []*Leaf {
	return append(s.Left.LeavesFull(config), s.Right.LeavesFull(config)...)
}
func (m *Mul) LeavesFull(config Config) []*Leaf {
	return append(m.Left.LeavesFull(config), m.Right.LeavesFull(config)...)
}
func (p *Pow) LeavesFull(config Config) []*Leaf { return p.Base.LeavesFull(config) }

func (a *Add) Prune(deg int) Expr { return pruneSearch(a, deg) }
func (s *Sub) Prune(deg int) Expr { return pruneSearch(s, deg) }
func (m *Mul) Prune(deg int) Expr { return pruneSearch(m, deg) }
func (p *Pow) Prune(deg int) Expr { return pruneSearch(p, deg) }

func (a *Add) ReplaceLeafByExpression(leaf string, e Expr) Expr {
	l := a.Left.ReplaceLeafByExpression(leaf, e)
	r := a.Right.ReplaceLeafByExpression(leaf, e)
	if l == a.Left && r == a.Right {
		return a
	}
	return &Add{l, r}
}
func (s *Sub) ReplaceLeafByExpression(leaf string, e Expr) Expr {
	l := s.Left.ReplaceLeafByExpression(leaf, e)
	r := s.Right.ReplaceLeafByExpression(leaf, e)
	if l == s.Left && r == s.Right {
		return s
	}
	return &Sub{l, r}
}
func (m *Mul) ReplaceLeafByExpression(leaf string, e Expr) Expr {
	l := m.Left.ReplaceLeafByExpression(leaf, e)
	r := m.Right.ReplaceLeafByExpression(leaf, e)
	if l == m.Left && r == m.Right {
		return m
	}
	return &Mul{l, r}
}
func (p *Pow) ReplaceLeafByExpression(leaf string, e Expr) Expr {
	b := p.Base.ReplaceLeafByExpression(leaf, e)
	if b == p.Base {
		return p
	}
	return &Pow{b, p.Exp}
}

// ReplaceLeavesByMap replaces all leaves whose String() key is present in rename
// in a single tree traversal. Interior nodes are reused (not allocated) when
// neither child changes, which avoids the O(n_renames × tree_size) allocation
// cost of calling ReplaceLeafByExpression once per rename entry.
func ReplaceLeavesByMap(e Expr, rename map[string]Expr) Expr {
	switch v := e.(type) {
	case *Leaf:
		if v.Type == ConstantColumn {
			return v
		}
		if repl, ok := rename[v.String()]; ok {
			return repl
		}
		return v
	case *Add:
		l := ReplaceLeavesByMap(v.Left, rename)
		r := ReplaceLeavesByMap(v.Right, rename)
		if l == v.Left && r == v.Right {
			return v
		}
		return &Add{l, r}
	case *Sub:
		l := ReplaceLeavesByMap(v.Left, rename)
		r := ReplaceLeavesByMap(v.Right, rename)
		if l == v.Left && r == v.Right {
			return v
		}
		return &Sub{l, r}
	case *Mul:
		l := ReplaceLeavesByMap(v.Left, rename)
		r := ReplaceLeavesByMap(v.Right, rename)
		if l == v.Left && r == v.Right {
			return v
		}
		return &Mul{l, r}
	case *Pow:
		b := ReplaceLeavesByMap(v.Base, rename)
		if b == v.Base {
			return v
		}
		return &Pow{b, v.Exp}
	}
	return e
}

func (a *Add) Evaluate(vals map[string]koalabear.Element) koalabear.Element {
	l := a.Left.Evaluate(vals)
	r := a.Right.Evaluate(vals)
	l.Add(&l, &r)
	return l
}

func (s *Sub) Evaluate(vals map[string]koalabear.Element) koalabear.Element {
	l := s.Left.Evaluate(vals)
	r := s.Right.Evaluate(vals)
	l.Sub(&l, &r)
	return l
}

func (m *Mul) Evaluate(vals map[string]koalabear.Element) koalabear.Element {
	l := m.Left.Evaluate(vals)
	r := m.Right.Evaluate(vals)
	l.Mul(&l, &r)
	return l
}

// Evaluate uses binary exponentiation so that large exponents (as produced by
// squareAndMultiply trees) are still handled in O(log exp) multiplications.
func (p *Pow) Evaluate(vals map[string]koalabear.Element) koalabear.Element {
	base := p.Base.Evaluate(vals)
	var res koalabear.Element
	res.SetOne()
	exp := p.Exp
	for exp > 0 {
		if exp&1 == 1 {
			res.Mul(&res, &base)
		}
		base.Mul(&base, &base)
		exp >>= 1
	}
	return res
}

func (a *Add) EvaluateOnIthEntry(_Pi [][]koalabear.Element, i int) koalabear.Element {
	l := a.Left.EvaluateOnIthEntry(_Pi, i)
	r := a.Right.EvaluateOnIthEntry(_Pi, i)
	l.Add(&l, &r)
	return l
}

func (s *Sub) EvaluateOnIthEntry(_Pi [][]koalabear.Element, i int) koalabear.Element {
	l := s.Left.EvaluateOnIthEntry(_Pi, i)
	r := s.Right.EvaluateOnIthEntry(_Pi, i)
	l.Sub(&l, &r)
	return l
}

func (m *Mul) EvaluateOnIthEntry(_Pi [][]koalabear.Element, i int) koalabear.Element {
	l := m.Left.EvaluateOnIthEntry(_Pi, i)
	r := m.Right.EvaluateOnIthEntry(_Pi, i)
	l.Mul(&l, &r)
	return l
}

func (p *Pow) EvaluateOnIthEntry(_Pi [][]koalabear.Element, i int) koalabear.Element {
	base := p.Base.EvaluateOnIthEntry(_Pi, i)
	var res koalabear.Element
	res.SetOne()
	exp := p.Exp
	for exp > 0 {
		if exp&1 == 1 {
			res.Mul(&res, &base)
		}
		base.Mul(&base, &base)
		exp >>= 1
	}
	return res
}

// Clone returns a deep copy of the expression tree with no shared nodes.
func Clone(e Expr) Expr {
	switch v := e.(type) {
	case *Leaf:
		c := *v
		return &c
	case *Add:
		return &Add{Left: Clone(v.Left), Right: Clone(v.Right)}
	case *Sub:
		return &Sub{Left: Clone(v.Left), Right: Clone(v.Right)}
	case *Mul:
		return &Mul{Left: Clone(v.Left), Right: Clone(v.Right)}
	case *Pow:
		return &Pow{Base: Clone(v.Base), Exp: v.Exp}
	}
	panic("Clone: unknown Expr type")
}

// squareAndMultiply builds an Expr tree for base^exp using binary exponentiation.
// exp must be >= 3.
// Each node in the tree is a distinct object (no shared pointers) so that
// in-place transformations such as Prune work correctly on the tree.
func squareAndMultiply(base Expr, exp uint32) Expr {
	// Collect the bits of exp from LSB to MSB, then reverse to get MSB-first.
	var binaryBits []bool
	for n := exp; n > 0; n >>= 1 {
		binaryBits = append(binaryBits, n&1 == 1)
	}
	for i, j := 0, len(binaryBits)-1; i < j; i, j = i+1, j-1 {
		binaryBits[i], binaryBits[j] = binaryBits[j], binaryBits[i]
	}

	// The MSB is always 1; start with result = base and process the remaining bits.
	// Clone the right child on every squaring step so that Left and Right are always
	// distinct objects — otherwise Prune (which rewrites nodes in-place) would
	// simultaneously modify both sides of a Mul when it modifies a shared subtree.
	result := base
	for i := 1; i < len(binaryBits); i++ {
		result = &Mul{result, Clone(result)} // square
		if binaryBits[i] {
			result = &Mul{result, Clone(base)} // multiply
		}
	}
	return result
}

func RemoveDuplicates[T comparable](s []T) []T {
	seen := make(map[T]struct{}, len(s))
	result := make([]T, 0, len(s))

	for _, v := range s {
		if _, ok := seen[v]; !ok {
			seen[v] = struct{}{}
			result = append(result, v)
		}
	}

	return result
}
