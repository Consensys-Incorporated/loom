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

package dag

import (
	"fmt"
	"strconv"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	fieldhash "github.com/consensys/loom/internal/hash"
)

// NodeKind identifies the type of an expression DAG node.
type NodeKind int

const (
	KindLeaf NodeKind = iota // leaf: any expr.LeafType
	KindAdd
	KindSub
	KindMul
	KindPow
)

// DAGNode is a node in the directed acyclic graph (DAG) representation of an
// Expr. A single *DAGNode may be referenced by multiple parents, representing
// shared sub-expressions.
//
// For commutative operators (Add, Mul), the expression (a op b) and (b op a)
// are represented by the same node: Children are stored in canonical structural
// ID order so that the node is unique regardless of operand order in the source
// tree.
type DAGNode struct {
	Kind     NodeKind
	Leaf     *expr.Leaf        // non-nil iff Kind == KindLeaf; stored as concrete type to avoid interface dispatch in hot eval path
	Children []*DAGNode        // len 2 for Add/Sub/Mul; len 1 for Pow; len 0 for Leaf
	Exp      uint32            // exponent, only meaningful when Kind == KindPow
	Index    int               // position in DAG.Nodes; used by EvalWithCache / EvalWithCacheVars
	VarIdx   int               // for KindLeaf: index into vars slice for EvalWithCacheVars
	Field    field.Kind        // output field inferred from the node and its children
	IsConst  bool              // true iff Kind == KindLeaf and the leaf is a Const
	ConstVal koalabear.Element // valid iff IsConst; avoids the l.Type==Const branch in the hot eval path

	structID int    // non-zero iff the node was interned during ExprToDAG construction
	key      string // lazily materialized debug key derived from structID
}

// DAG is the directed acyclic graph form of an Expr. Sub-expressions that are
// structurally identical (including commutativity for Add and Mul) share a
// single *DAGNode.
type DAG struct {
	Root     *DAGNode
	Nodes    []*DAGNode     // every unique node, in topological order (children before parents)
	VarIndex map[string]int // leaf name → index in vars slice for EvalWithCacheVars
}

// Clone returns a deep copy of the DAG: fresh DAGNodes and fresh *expr.Leaf for
// every leaf, with Children rewired to the new nodes. Use this to make per-call
// mutations (e.g. ComputeQuotient*'s assignment of Leaf.Idx) safe across
// goroutines that would otherwise share leaf pointers via shared sub-expressions
// upstream of ExprToDAG.
//
// VarIndex is shared (read-only after build).
func (d *DAG) Clone() *DAG {
	if d == nil {
		return nil
	}
	cloneOf := make(map[*DAGNode]*DAGNode, len(d.Nodes))
	nodes := make([]*DAGNode, len(d.Nodes))
	for i, n := range d.Nodes {
		nn := *n
		if n.Leaf != nil {
			leafCp := *n.Leaf
			nn.Leaf = &leafCp
		}
		if len(n.Children) > 0 {
			nn.Children = make([]*DAGNode, len(n.Children))
			for j, c := range n.Children {
				// children come before parents in topological order, so cloneOf[c] is populated
				nn.Children[j] = cloneOf[c]
			}
		}
		nodes[i] = &nn
		cloneOf[n] = &nn
	}
	return &DAG{
		Root:     cloneOf[d.Root],
		Nodes:    nodes,
		VarIndex: d.VarIndex,
	}
}

// ExprToDAG converts an Expr tree into a DAG by merging identical
// sub-expressions into shared nodes. Commutativity is respected: (a+b) and
// (b+a) produce the same node, as do (a*b) and (b*a). Sub is not commutative.
func ExprToDAG(e expr.Expr) *DAG {
	return ExprToDAGWithColumnFields(e, nil)
}

func ExprToDAGWithColumnFields(e expr.Expr, columnFields map[string]field.Kind) *DAG {
	b := &dagBuilder{
		cache:        make(map[nodeKey]*DAGNode),
		leafIDs:      make(map[leafKey]int),
		varIndex:     make(map[string]int),
		columnFields: columnFields,
	}
	root := b.build(e)
	return &DAG{Root: root, Nodes: b.ordered, VarIndex: b.varIndex}
}

type leafKey struct {
	typ   expr.LeafType
	shift int
	name  string
	field field.Kind
	hook  expr.HookID
	value koalabear.Element
}

type nodeKey struct {
	kind  NodeKind
	left  int
	right int
	exp   uint32
	leaf  int
	field field.Kind
}

type dagBuilder struct {
	cache        map[nodeKey]*DAGNode
	leafIDs      map[leafKey]int
	ordered      []*DAGNode
	varIndex     map[string]int
	columnFields map[string]field.Kind
	nextLeafID   int
	nextNodeID   int
}

func (b *dagBuilder) assignVarIdx(name string) int {
	if idx, ok := b.varIndex[name]; ok {
		return idx
	}
	idx := len(b.varIndex)
	b.varIndex[name] = idx
	return idx
}

func (b *dagBuilder) assignLeafID(l *expr.Leaf) int {
	key := leafKey{
		typ:   l.Type,
		shift: l.Shift,
		name:  l.Name,
		field: l.FieldKind(),
		hook:  l.Hook,
		value: l.Value,
	}
	if id, ok := b.leafIDs[key]; ok {
		return id
	}
	b.nextLeafID++
	b.leafIDs[key] = b.nextLeafID
	return b.nextLeafID
}

// intern returns the cached node for key, or creates it via make(), records
// it, and appends it to the topological slice. Children must already be in
// b.ordered when intern is called, which is guaranteed by the post-order
// traversal in build().
func (b *dagBuilder) intern(key nodeKey, make func() *DAGNode) *DAGNode {
	if n, ok := b.cache[key]; ok {
		return n
	}
	n := make()
	b.nextNodeID++
	n.structID = b.nextNodeID
	n.Index = len(b.ordered)
	b.cache[key] = n
	b.ordered = append(b.ordered, n)
	return n
}

func inferField(children ...*DAGNode) field.Kind {
	res := field.Base
	for _, child := range children {
		res = field.Join(res, child.Field)
	}
	return res
}

func (b *dagBuilder) leafWithInferredField(l *expr.Leaf) *expr.Leaf {
	f := expr.FieldOfWithColumnFields(l, b.columnFields)
	if f == l.FieldKind() {
		return l
	}
	cp := *l
	cp.Field = f
	return &cp
}

func (b *dagBuilder) build(root expr.Expr) *DAGNode {
	// Iterative post-order traversal to avoid stack overflow on deep expression trees
	// (e.g. a sum of thousands of constraints folded left-associatively).
	type frame struct {
		expr      expr.Expr
		processed bool // true = children already pushed; time to intern this node
	}

	result := make(map[expr.Expr]*DAGNode) // expr pointer → built DAGNode
	stack := make([]frame, 0, 64)
	stack = append(stack, frame{root, false})

	for len(stack) > 0 {
		f := stack[len(stack)-1]
		stack = stack[:len(stack)-1]

		e := f.expr

		if _, done := result[e]; done {
			continue // shared subtree already built
		}

		switch v := e.(type) {
		case *expr.Leaf:
			lv := b.leafWithInferredField(v)
			key := nodeKey{kind: KindLeaf, leaf: b.assignLeafID(lv), field: lv.FieldKind()}
			result[e] = b.intern(key, func() *DAGNode {
				n := &DAGNode{Kind: KindLeaf, Leaf: lv, VarIdx: b.assignVarIdx(lv.String()), Field: lv.FieldKind()}
				if lv.Type == expr.ConstantColumn {
					n.IsConst = true
					n.ConstVal = lv.Value
				}
				return n
			})

		case *expr.Add:
			if !f.processed {
				stack = append(stack, frame{e, true}, frame{v.Left, false}, frame{v.Right, false})
			} else {
				left, right := result[v.Left], result[v.Right]
				leftID, rightID := left.structID, right.structID
				if leftID > rightID { // Add is commutative: canonical order by structural ID.
					left, right = right, left
					leftID, rightID = rightID, leftID
				}
				key := nodeKey{kind: KindAdd, left: leftID, right: rightID, field: inferField(left, right)}
				l, r := left, right
				result[e] = b.intern(key, func() *DAGNode {
					return &DAGNode{Kind: KindAdd, Children: []*DAGNode{l, r}, Field: inferField(l, r)}
				})
			}

		case *expr.Sub:
			if !f.processed {
				stack = append(stack, frame{e, true}, frame{v.Left, false}, frame{v.Right, false})
			} else {
				left, right := result[v.Left], result[v.Right]
				key := nodeKey{kind: KindSub, left: left.structID, right: right.structID, field: inferField(left, right)}
				l, r := left, right
				result[e] = b.intern(key, func() *DAGNode {
					return &DAGNode{Kind: KindSub, Children: []*DAGNode{l, r}, Field: inferField(l, r)}
				})
			}

		case *expr.Mul:
			if !f.processed {
				stack = append(stack, frame{e, true}, frame{v.Left, false}, frame{v.Right, false})
			} else {
				left, right := result[v.Left], result[v.Right]
				leftID, rightID := left.structID, right.structID
				if leftID > rightID { // Mul is commutative: canonical order by structural ID.
					left, right = right, left
					leftID, rightID = rightID, leftID
				}
				key := nodeKey{kind: KindMul, left: leftID, right: rightID, field: inferField(left, right)}
				l, r := left, right
				result[e] = b.intern(key, func() *DAGNode {
					return &DAGNode{Kind: KindMul, Children: []*DAGNode{l, r}, Field: inferField(l, r)}
				})
			}

		case *expr.Pow:
			if !f.processed {
				stack = append(stack, frame{e, true}, frame{v.Base, false})
			} else {
				base := result[v.Base]
				key := nodeKey{kind: KindPow, left: base.structID, exp: v.Exp, field: base.Field}
				bs, exp := base, v.Exp
				result[e] = b.intern(key, func() *DAGNode {
					return &DAGNode{Kind: KindPow, Children: []*DAGNode{bs}, Exp: exp, Field: bs.Field}
				})
			}

		default:
			panic(fmt.Sprintf("ExprToDAG: unknown Expr type %T", e))
		}
	}

	return result[root]
}

// Key returns a compact debug ID for nodes interned during ExprToDAG
// construction. It is only stable within a single DAG build: two independent
// DAGs containing the same expression may assign different keys to equivalent
// nodes. Use it for local debugging only, not as a persistent or cross-DAG
// content identifier. Nodes produced by later rewrites such as Flatten or
// Factorize are intentionally keyless and return the empty string.
func (d *DAGNode) Key() string {
	if d.structID == 0 {
		return ""
	}
	if d.key == "" {
		d.key = "node:" + strconv.Itoa(d.structID)
	}
	return d.key
}

// Flatten returns a new DAG where every chain of binary Add nodes is collapsed
// into a single n-ary Add node, and every chain of binary Mul nodes into a
// single n-ary Mul node. For example:
//
//	Add(Add(a, b), c)  →  Add node with children [a, b, c]
//	Mul(a, Mul(b, c))  →  Mul node with children [a, b, c]
//
// Sub and Pow are left as binary/unary nodes (they are not associative).
// Leaf nodes are shared with the receiver; operator nodes are freshly allocated.
//
// The single pass over the topological order is sufficient: by the time a
// parent is processed, its children are already fully flattened, so absorbing
// same-kind children one level deep catches arbitrarily deep chains.
func (d *DAG) Flatten() *DAG {
	// flat maps each original *DAGNode to its flattened counterpart.
	// d.Nodes is in topological order (children before parents), so every
	// child is already in flat when its parent is processed.
	flat := make(map[*DAGNode]*DAGNode, len(d.Nodes))
	for _, n := range d.Nodes {
		flat[n] = flattenNode(n, flat)
	}

	root := flat[d.Root]

	// Rebuild the topological order for the new DAG via post-order DFS.
	// Intermediate binary nodes that were absorbed are no longer reachable
	// from the new root and are therefore excluded.
	seen := make(map[*DAGNode]bool, len(d.Nodes))
	ordered := make([]*DAGNode, 0, len(d.Nodes))
	var postOrder func(*DAGNode)
	postOrder = func(n *DAGNode) {
		if seen[n] {
			return
		}
		seen[n] = true
		for _, child := range n.Children {
			postOrder(child)
		}
		ordered = append(ordered, n)
	}
	postOrder(root)

	// Reassign Index for every node in the new ordering.
	// Non-leaf nodes are newly allocated (safe to mutate). Leaf nodes are
	// shared with the original DAG, but Flatten is typically called once and
	// the original DAG is discarded, so mutation is acceptable.
	for i, n := range ordered {
		n.Index = i
	}

	return &DAG{Root: root, Nodes: ordered, VarIndex: d.VarIndex}
}

// Factorize applies the distributive law
//
//	add(mul(x,y), mul(x,z)) → mul(x, add(y,z))
//
// to every Add node, bottom-up, until no further reductions are possible
// within a single pass. Best called on a Flatten()ed DAG. Returns a new DAG
// that shares leaf nodes with the receiver.
//
// The rule is applied greedily: at each Add node the factor that appears in
// the largest number of Mul children is extracted first, then the rule is
// re-applied to the residual terms. Only factors that are nodes with a
// structural ID (i.e. nodes from the original ExprToDAG construction) are
// considered, so newly-created intermediate nodes are never spuriously
// identified as a common factor.
func (d *DAG) Factorize() *DAG {
	// Process nodes bottom-up (d.Nodes is in topological order: children
	// before parents), mapping each original node to its rewritten form.
	rewritten := make(map[*DAGNode]*DAGNode, len(d.Nodes))
	for _, n := range d.Nodes {
		rewritten[n] = factorizeRewrite(n, rewritten)
	}

	root := rewritten[d.Root]

	// Rebuild topological order for the new DAG via post-order DFS.
	seen := make(map[*DAGNode]bool, len(d.Nodes))
	ordered := make([]*DAGNode, 0, len(d.Nodes))
	var postOrder func(*DAGNode)
	postOrder = func(n *DAGNode) {
		if seen[n] {
			return
		}
		seen[n] = true
		for _, c := range n.Children {
			postOrder(c)
		}
		ordered = append(ordered, n)
	}
	postOrder(root)

	for i, n := range ordered {
		n.Index = i
	}

	return &DAG{Root: root, Nodes: ordered, VarIndex: d.VarIndex}
}

// factorizeRewrite rewrites n after all its children have already been
// rewritten (bottom-up order). For Add nodes it calls factorizeAddChildren
// to apply the distributive law; other node kinds just thread through
// rewritten children unchanged.
func factorizeRewrite(n *DAGNode, rewritten map[*DAGNode]*DAGNode) *DAGNode {
	switch n.Kind {
	case KindLeaf:
		return n // leaves are shared unchanged

	case KindAdd:
		children := make([]*DAGNode, len(n.Children))
		for i, c := range n.Children {
			children[i] = rewritten[c]
		}
		return factorizeAddChildren(children)

	case KindMul:
		changed := false
		children := make([]*DAGNode, len(n.Children))
		for i, c := range n.Children {
			children[i] = rewritten[c]
			if children[i] != c {
				changed = true
			}
		}
		if !changed {
			return n // unchanged: preserve structID for factor lookup
		}
		return &DAGNode{Kind: KindMul, Children: children, Field: inferField(children...)} // structID intentionally empty

	case KindSub:
		l, r := rewritten[n.Children[0]], rewritten[n.Children[1]]
		if l == n.Children[0] && r == n.Children[1] {
			return n
		}
		return &DAGNode{Kind: KindSub, Children: []*DAGNode{l, r}, Field: inferField(l, r)}

	case KindPow:
		base := rewritten[n.Children[0]]
		if base == n.Children[0] {
			return n
		}
		return &DAGNode{Kind: KindPow, Children: []*DAGNode{base}, Exp: n.Exp, Field: base.Field}
	}
	panic(fmt.Sprintf("Factorize: unknown NodeKind %d", n.Kind))
}

// factorizeAddChildren applies the distributive law to the children of an Add
// node and returns a (possibly factored) replacement node. It recurses until
// no further reductions are possible at this level.
//
// Only KindMul children participate in factorization. Non-Mul children (leaves,
// Pow, Sub) are carried through unchanged, which avoids the need to introduce
// a Const(1) node for the case where a term reduces to the identity.
//
// Factor candidates are restricted to nodes whose structID is non-zero: this
// ensures that only nodes from the original DAG construction are used as
// factors, preventing newly-created intermediate nodes from being spuriously
// matched.
func factorizeAddChildren(children []*DAGNode) *DAGNode {
	// Count how many KindMul children contain each factor (by structural ID).
	factorCount := make(map[int]int)
	factorByID := make(map[int]*DAGNode)
	for _, c := range children {
		if c.Kind != KindMul {
			continue
		}
		seen := make(map[int]bool)
		for _, f := range c.Children {
			if f.structID == 0 {
				continue // skip rewritten intermediate nodes
			}
			if !seen[f.structID] {
				seen[f.structID] = true
				factorCount[f.structID]++
				factorByID[f.structID] = f
			}
		}
	}

	// Pick the factor with the highest count (≥ 2 to be worth extracting).
	bestID, bestCount := 0, 1
	for id, cnt := range factorCount {
		if cnt > bestCount {
			bestCount, bestID = cnt, id
		}
	}
	if bestID == 0 {
		return &DAGNode{Kind: KindAdd, Children: children, Field: inferField(children...)}
	}

	factor := factorByID[bestID]

	// Partition children: Mul children that contain the factor go into
	// withFactor (with the factor removed); all others go into withoutFactor.
	var withFactor, withoutFactor []*DAGNode
	for _, c := range children {
		if c.Kind == KindMul {
			// Find the first occurrence of the factor in this Mul's children.
			idx := -1
			for i, f := range c.Children {
				if f.structID == bestID {
					idx = i
					break
				}
			}
			if idx >= 0 {
				// Rebuild Mul without this one occurrence of the factor.
				rem := make([]*DAGNode, 0, len(c.Children)-1)
				rem = append(rem, c.Children[:idx]...)
				rem = append(rem, c.Children[idx+1:]...)
				switch len(rem) {
				case 0:
					// Mul had exactly one child = the factor itself.
					// Avoid creating a Const(1); treat as non-participating.
					withoutFactor = append(withoutFactor, c)
				case 1:
					withFactor = append(withFactor, rem[0])
				default:
					withFactor = append(withFactor, &DAGNode{Kind: KindMul, Children: rem, Field: inferField(rem...)})
				}
				continue
			}
		}
		withoutFactor = append(withoutFactor, c)
	}

	// Build mul(factor, add(withFactor...)), recursing into the inner Add to
	// factor out any additional common factors among withFactor terms.
	var inner *DAGNode
	switch len(withFactor) {
	case 0:
		// Nothing was factored (all candidates hit the len=0 edge case).
		return &DAGNode{Kind: KindAdd, Children: children, Field: inferField(children...)}
	case 1:
		inner = withFactor[0]
	default:
		inner = factorizeAddChildren(withFactor) // recurse: more factors possible
	}
	factored := &DAGNode{Kind: KindMul, Children: []*DAGNode{factor, inner}, Field: inferField(factor, inner)}

	if len(withoutFactor) == 0 {
		return factored
	}

	// Combine the factored group with the remaining children and recurse to
	// extract any further common factors among the residual terms.
	residual := append(withoutFactor, factored)
	return factorizeAddChildren(residual)
}

// flattenNode returns the flattened version of n, looking up already-flattened
// children in flat.
func flattenNode(n *DAGNode, flat map[*DAGNode]*DAGNode) *DAGNode {
	switch n.Kind {
	case KindLeaf:
		return n // leaves have no children; share the original pointer

	case KindAdd:
		children := absorbChildren(n, KindAdd, flat)
		return &DAGNode{Kind: KindAdd, Children: children, Field: inferField(children...)}

	case KindMul:
		children := absorbChildren(n, KindMul, flat)
		return &DAGNode{Kind: KindMul, Children: children, Field: inferField(children...)}

	case KindSub:
		l, r := flat[n.Children[0]], flat[n.Children[1]]
		return &DAGNode{Kind: KindSub, Children: []*DAGNode{l, r}, Field: inferField(l, r)}

	case KindPow:
		base := flat[n.Children[0]]
		return &DAGNode{Kind: KindPow, Children: []*DAGNode{base}, Exp: n.Exp, Field: base.Field}
	}
	panic(fmt.Sprintf("Flatten: unknown NodeKind %d", n.Kind))
}

// absorbChildren builds the child list for a flattened n-ary node of the given
// kind. For each child of n, if its flattened version has the same kind, its
// own children are inlined (absorbed) rather than kept as a nested node.
func absorbChildren(n *DAGNode, kind NodeKind, flat map[*DAGNode]*DAGNode) []*DAGNode {
	children := make([]*DAGNode, 0, len(n.Children))
	for _, child := range n.Children {
		fc := flat[child]
		if fc.Kind == kind {
			children = append(children, fc.Children...)
		} else {
			children = append(children, fc)
		}
	}
	return children
}

// Eval evaluates the DAG at the given variable assignment. It processes nodes
// in topological order (d.Nodes is children-before-parents), caching each
// result so shared nodes are computed only once.
//
// Add and Mul are n-ary: all children are summed / multiplied together.
// Sub is binary: Children[0] − Children[1].
// Pow uses the exponent stored in the node.
// Leaves are looked up in vals, keyed by String() (not the bare name); missing keys cause a panic.
func (d *DAG) Eval(vals map[string]koalabear.Element) koalabear.Element {
	cache := make(map[*DAGNode]koalabear.Element, len(d.Nodes))
	for _, n := range d.Nodes {
		cache[n] = evalDAGNode(n, cache, vals)
	}
	return cache[d.Root]
}

func evalDAGNode(n *DAGNode, cache map[*DAGNode]koalabear.Element, vals map[string]koalabear.Element) koalabear.Element {
	switch n.Kind {
	case KindLeaf:
		return n.Leaf.Evaluate(vals)

	case KindAdd:
		var acc koalabear.Element
		for _, child := range n.Children {
			v := cache[child]
			acc.Add(&acc, &v)
		}
		return acc

	case KindSub:
		l, r := cache[n.Children[0]], cache[n.Children[1]]
		var res koalabear.Element
		res.Sub(&l, &r)
		return res

	case KindMul:
		var acc koalabear.Element
		acc.SetOne()
		for _, child := range n.Children {
			v := cache[child]
			acc.Mul(&acc, &v)
		}
		return acc

	case KindPow:
		base := cache[n.Children[0]]
		var res koalabear.Element
		res.SetOne()
		exp := n.Exp
		for exp > 0 {
			if exp&1 == 1 {
				res.Mul(&res, &base)
			}
			base.Mul(&base, &base)
			exp >>= 1
		}
		return res
	}
	panic(fmt.Sprintf("Eval: unknown NodeKind %d", n.Kind))
}

// EvalMixed evaluates the DAG in the Koalabear E6 extension field. Base-field
// variables are lifted from baseVars; extension-field variables are read from
// extVars. If an extension-marked leaf is absent from extVars but present in
// baseVars, it is lifted as a compatibility fallback for transition code.
func (d *DAG) EvalMixed(baseVars map[string]koalabear.Element, extVars map[string]ext.E6) ext.E6 {
	cache := make(map[*DAGNode]ext.E6, len(d.Nodes))
	for _, n := range d.Nodes {
		cache[n] = evalMixedDAGNode(n, cache, baseVars, extVars)
	}
	return cache[d.Root]
}

// EvalExt evaluates the DAG entirely in the E6 extension field. It is used on
// verifier-side zeta checks where every column evaluation, even for base
// polynomials, already lives in E6 because zeta is an extension point.
func (d *DAG) EvalExt(vals map[string]ext.E6) ext.E6 {
	return d.EvalMixed(nil, vals)
}

// evalMixedDAGNode evaluates one node for EvalMixed after all children have
// already been evaluated into cache. Every operation is performed in E6; base
// inputs must have been lifted before reaching non-leaf arithmetic.
func evalMixedDAGNode(n *DAGNode, cache map[*DAGNode]ext.E6, baseVars map[string]koalabear.Element, extVars map[string]ext.E6) ext.E6 {
	switch n.Kind {
	case KindLeaf:
		return evalMixedLeaf(n, baseVars, extVars)

	case KindAdd:
		var acc ext.E6
		for _, child := range n.Children {
			v := cache[child]
			acc.Add(&acc, &v)
		}
		return acc

	case KindSub:
		l, r := cache[n.Children[0]], cache[n.Children[1]]
		var res ext.E6
		res.Sub(&l, &r)
		return res

	case KindMul:
		var acc ext.E6
		acc.SetOne()
		for _, child := range n.Children {
			v := cache[child]
			acc.Mul(&acc, &v)
		}
		return acc

	case KindPow:
		base := cache[n.Children[0]]
		var res ext.E6
		res.SetOne()
		exp := n.Exp
		for exp > 0 {
			if exp&1 == 1 {
				res.Mul(&res, &base)
			}
			base.Mul(&base, &base)
			exp >>= 1
		}
		return res
	}
	panic(fmt.Sprintf("EvalMixed: unknown NodeKind %d", n.Kind))
}

// evalMixedLeaf resolves a leaf from the appropriate scalar variable map and
// returns it as an E6 element. Extension leaves prefer extVars but may fall back
// to baseVars during the staged migration while some callers still provide only
// base values for extension-tagged leaves.
func evalMixedLeaf(n *DAGNode, baseVars map[string]koalabear.Element, extVars map[string]ext.E6) ext.E6 {
	if n.IsConst {
		return liftBaseToE6(n.ConstVal)
	}

	key := n.Leaf.String()
	if n.Field == field.Ext {
		if v, ok := extVars[key]; ok {
			return v
		}
		if v, ok := baseVars[key]; ok {
			return liftBaseToE6(v)
		}
		panic("EvalMixed: missing extension value for " + key)
	}

	if v, ok := baseVars[key]; ok {
		return liftBaseToE6(v)
	}
	if v, ok := extVars[key]; ok {
		return v
	}
	panic("EvalMixed: missing base value for " + key)
}

// liftBaseToE6 embeds a Koalabear base-field element into the E6 extension.
func liftBaseToE6(v koalabear.Element) ext.E6 {
	return fieldhash.LiftBaseToExt(v)
}

// EvalWithCacheVars evaluates the DAG using pre-filled vars and cache slices,
// avoiding all map operations. vars must be indexed by DAGNode.VarIdx (leaf
// variables must be set by the caller before each call). cache must have
// length >= len(d.Nodes). Both slices can be reused across repeated calls.
// Only works on DAGs produced by ExprToDAG (not Flatten).
func (d *DAG) EvalWithCacheVars(vars []koalabear.Element, cache []koalabear.Element) koalabear.Element {
	for _, n := range d.Nodes {
		cache[n.Index] = evalDAGNodeSliceVars(n, cache, vars)
	}
	return cache[d.Root.Index]
}

func evalDAGNodeSliceVars(n *DAGNode, cache []koalabear.Element, vars []koalabear.Element) koalabear.Element {
	switch n.Kind {
	case KindLeaf:
		if n.IsConst {
			return n.ConstVal
		}
		return vars[n.VarIdx]

	case KindAdd:
		var acc koalabear.Element
		for _, child := range n.Children {
			v := cache[child.Index]
			acc.Add(&acc, &v)
		}
		return acc

	case KindSub:
		l, r := cache[n.Children[0].Index], cache[n.Children[1].Index]
		var res koalabear.Element
		res.Sub(&l, &r)
		return res

	case KindMul:
		var acc koalabear.Element
		acc.SetOne()
		for _, child := range n.Children {
			v := cache[child.Index]
			acc.Mul(&acc, &v)
		}
		return acc

	case KindPow:
		base := cache[n.Children[0].Index]
		var res koalabear.Element
		res.SetOne()
		exp := n.Exp
		for exp > 0 {
			if exp&1 == 1 {
				res.Mul(&res, &base)
			}
			base.Mul(&base, &base)
			exp >>= 1
		}
		return res
	}
	panic(fmt.Sprintf("EvalWithCacheVars: unknown NodeKind %d", n.Kind))
}

// EvalWithCacheVarsMixed evaluates the DAG with base and extension variable
// rails, using pre-filled vars and cache slices indexed by DAGNode.VarIdx and
// DAGNode.Index respectively. Base-valued nodes stay in koalabear arithmetic;
// extension-valued nodes use E6 arithmetic and lift base children on demand.
// Only works on DAGs produced by ExprToDAG (not Flatten).
func (d *DAG) EvalWithCacheVarsMixed(baseVars []koalabear.Element, extVars []ext.E6, baseCache []koalabear.Element, extCache []ext.E6) ext.E6 {
	for _, n := range d.Nodes {
		if n.Field == field.Base {
			baseCache[n.Index] = evalDAGNodeSliceVars(n, baseCache, baseVars)
			continue
		}
		extCache[n.Index] = evalExtDAGNodeSliceVars(n, baseCache, extCache, baseVars, extVars)
	}
	if d.Root.Field == field.Base {
		return liftBaseToE6(baseCache[d.Root.Index])
	}
	return extCache[d.Root.Index]
}

// evalExtDAGNodeSliceVars evaluates one extension-valued node in the cached
// variable-slice evaluator. Base-valued children are read from baseCache and
// lifted just before they participate in E6 arithmetic.
func evalExtDAGNodeSliceVars(n *DAGNode, baseCache []koalabear.Element, extCache []ext.E6, baseVars []koalabear.Element, extVars []ext.E6) ext.E6 {
	switch n.Kind {
	case KindLeaf:
		if n.IsConst {
			return liftBaseToE6(n.ConstVal)
		}
		if n.Field == field.Ext {
			return extVars[n.VarIdx]
		}
		return liftBaseToE6(baseVars[n.VarIdx])

	case KindAdd:
		var acc ext.E6
		for _, child := range n.Children {
			v := childCacheAsExt(child, baseCache, extCache)
			acc.Add(&acc, &v)
		}
		return acc

	case KindSub:
		l := childCacheAsExt(n.Children[0], baseCache, extCache)
		r := childCacheAsExt(n.Children[1], baseCache, extCache)
		var res ext.E6
		res.Sub(&l, &r)
		return res

	case KindMul:
		var acc ext.E6
		acc.SetOne()
		for _, child := range n.Children {
			v := childCacheAsExt(child, baseCache, extCache)
			acc.Mul(&acc, &v)
		}
		return acc

	case KindPow:
		base := childCacheAsExt(n.Children[0], baseCache, extCache)
		var res ext.E6
		res.SetOne()
		exp := n.Exp
		for exp > 0 {
			if exp&1 == 1 {
				res.Mul(&res, &base)
			}
			base.Mul(&base, &base)
			exp >>= 1
		}
		return res
	}
	panic(fmt.Sprintf("EvalWithCacheVarsMixed: unknown NodeKind %d", n.Kind))
}

// childCacheAsExt returns a child node's cached value as E6, lifting from the
// base cache when the child itself is base-valued.
func childCacheAsExt(child *DAGNode, baseCache []koalabear.Element, extCache []ext.E6) ext.E6 {
	if child.Field == field.Ext {
		return extCache[child.Index]
	}
	return liftBaseToE6(baseCache[child.Index])
}

// EvalOnIthEntry evaluates the DAG at row i of the polynomial slice _Pi.
// Each leaf node's Leaf.Idx field selects which polynomial in _Pi to read from
// (must be set by the caller, e.g. via evalPointWiseInto setup).
// Row selection follows the same rules as expr.Expr.EvaluateOnIthEntry:
//   - Const leaf              : returns the constant value
//   - len(_Pi[leaf.Idx]) == 1 : constant polynomial, returns _Pi[leaf.Idx][0]
//   - shifted leaf            : returns _Pi[leaf.Idx][(i+N+leaf.Shift)%N]
//   - unshifted leaf          : returns _Pi[leaf.Idx][i]
//
// Composite nodes are evaluated in topological order using an internal cache
// so that shared sub-expressions are computed only once.
func (d *DAG) EvalOnIthEntry(_Pi [][]koalabear.Element, i int) koalabear.Element {
	cache := make([]koalabear.Element, len(d.Nodes))
	for _, n := range d.Nodes {
		cache[n.Index] = evalDAGNodeOnIthEntry(n, cache, _Pi, i)
	}
	return cache[d.Root.Index]
}

func evalDAGNodeOnIthEntry(n *DAGNode, cache []koalabear.Element, _Pi [][]koalabear.Element, i int) koalabear.Element {
	switch n.Kind {
	case KindLeaf:
		return n.Leaf.EvaluateOnIthEntry(_Pi, i)

	case KindAdd:
		var acc koalabear.Element
		for _, child := range n.Children {
			v := cache[child.Index]
			acc.Add(&acc, &v)
		}
		return acc

	case KindSub:
		l, r := cache[n.Children[0].Index], cache[n.Children[1].Index]
		var res koalabear.Element
		res.Sub(&l, &r)
		return res

	case KindMul:
		var acc koalabear.Element
		acc.SetOne()
		for _, child := range n.Children {
			v := cache[child.Index]
			acc.Mul(&acc, &v)
		}
		return acc

	case KindPow:
		base := cache[n.Children[0].Index]
		var res koalabear.Element
		res.SetOne()
		exp := n.Exp
		for exp > 0 {
			if exp&1 == 1 {
				res.Mul(&res, &base)
			}
			base.Mul(&base, &base)
			exp >>= 1
		}
		return res
	}
	panic(fmt.Sprintf("EvalOnIthEntry: unknown NodeKind %d", n.Kind))
}

// EvalOnAllEntries evaluates the DAG pointwise for all N rows simultaneously
// and returns a slice of length N. Equivalent to calling EvalOnIthEntry(Pi, j)
// for j=0..N-1, but uses a single topological traversal with tight inner loops
// instead of N separate traversals. Each non-leaf node is visited exactly once.
//
// Peak memory is bounded to O(max_live_nodes × N) by reference counting: a
// node's buffer is returned to an internal pool as soon as all its parents have
// consumed it.
func (d *DAG) EvalOnAllEntries(Pi [][]koalabear.Element, N int) []koalabear.Element {
	// Pre-compute how many parent nodes reference each child.
	refCount := make([]int, len(d.Nodes))
	for _, n := range d.Nodes {
		for _, child := range n.Children {
			refCount[child.Index]++
		}
	}

	// Buffer pool: recycle N-length slices to limit peak allocation.
	// (don't use sync.Pool -> no cross-call, cross-goroutine sharing in this function case)
	var pool [][]koalabear.Element
	alloc := func() []koalabear.Element {
		if last := len(pool) - 1; last >= 0 {
			b := pool[last]
			pool = pool[:last]
			return b
		}
		return make([]koalabear.Element, N)
	}
	release := func(b []koalabear.Element) { pool = append(pool, b) }

	vectors := make([][]koalabear.Element, len(d.Nodes))

	for _, n := range d.Nodes {
		dst := alloc()

		switch n.Kind {
		case KindLeaf:
			if n.IsConst {
				for j := range N {
					dst[j] = n.ConstVal
				}
			} else {
				l := n.Leaf
				p := Pi[l.Idx]
				if len(p) == 1 {
					for j := range N {
						dst[j] = p[0]
					}
				} else if l.Shift != 0 {
					for j := range N {
						dst[j] = p[(j+N+l.Shift)%N]
					}
				} else {
					copy(dst, p[:N])
				}
			}

		case KindAdd:
			copy(dst, vectors[n.Children[0].Index])
			for _, child := range n.Children[1:] {
				src := vectors[child.Index]
				for j := range N {
					dst[j].Add(&dst[j], &src[j])
				}
			}

		case KindSub:
			l, r := vectors[n.Children[0].Index], vectors[n.Children[1].Index]
			for j := range N {
				dst[j].Sub(&l[j], &r[j])
			}

		case KindMul:
			copy(dst, vectors[n.Children[0].Index])
			for _, child := range n.Children[1:] {
				src := vectors[child.Index]
				for j := range N {
					dst[j].Mul(&dst[j], &src[j])
				}
			}

		case KindPow:
			base := vectors[n.Children[0].Index]
			tmp := alloc()
			copy(tmp, base)
			for j := range N {
				dst[j].SetOne()
			}
			exp := n.Exp
			for exp > 0 {
				if exp&1 == 1 {
					for j := range N {
						dst[j].Mul(&dst[j], &tmp[j])
					}
				}
				for j := range N {
					tmp[j].Mul(&tmp[j], &tmp[j])
				}
				exp >>= 1
			}
			release(tmp)
		}

		vectors[n.Index] = dst

		// Release child buffers no longer needed by any future parent.
		for _, child := range n.Children {
			refCount[child.Index]--
			if refCount[child.Index] == 0 && child != d.Root {
				release(vectors[child.Index])
				vectors[child.Index] = nil
			}
		}
	}

	return vectors[d.Root.Index]
}

// EvalOnAllEntriesMixed evaluates the DAG pointwise for all N rows using
// separate base and extension polynomial rails. Base-valued nodes stay in
// koalabear arithmetic and extension-valued nodes use E6 arithmetic, lifting
// base children on demand. The root must be extension-valued.
func (d *DAG) EvalOnAllEntriesMixed(PiBase [][]koalabear.Element, PiExt [][]ext.E6, N int) []ext.E6 {
	dst := make([]ext.E6, N)
	var ws EvalWorkspace
	d.EvalOnAllEntriesMixedInto(dst, PiBase, PiExt, N, &ws)
	return dst
}

// EvalWorkspace stores scratch buffers for repeated DAG vector evaluations.
// It is not safe for concurrent use.
type EvalWorkspace struct {
	refCount []int
	baseVec  [][]koalabear.Element
	extVec   [][]ext.E6
	basePool [][]koalabear.Element
	extPool  [][]ext.E6
}

// EvalOnAllEntriesMixedInto evaluates the DAG pointwise into dst for all N
// rows, reusing ws scratch buffers across calls. dst must have length at least
// N. The root must be extension-valued.
func (d *DAG) EvalOnAllEntriesMixedInto(dst []ext.E6, PiBase [][]koalabear.Element, PiExt [][]ext.E6, N int, ws *EvalWorkspace) {
	if d.Root.Field != field.Ext {
		panic("EvalOnAllEntriesMixed: root is not extension-valued")
	}
	if len(dst) < N {
		panic("EvalOnAllEntriesMixedInto: dst length is smaller than N")
	}
	dst = dst[:N]

	if ws == nil {
		ws = &EvalWorkspace{}
	}
	ws.prepare(len(d.Nodes))

	refCount := ws.refCount
	for _, n := range d.Nodes {
		for _, child := range n.Children {
			refCount[child.Index]++
		}
	}

	allocBase := func() []koalabear.Element {
		for last := len(ws.basePool) - 1; last >= 0; last = len(ws.basePool) - 1 {
			b := ws.basePool[last]
			ws.basePool = ws.basePool[:last]
			if cap(b) >= N {
				return b[:N]
			}
		}
		return make([]koalabear.Element, N)
	}
	releaseBase := func(b []koalabear.Element) { ws.basePool = append(ws.basePool, b) }

	allocExt := func() []ext.E6 {
		for last := len(ws.extPool) - 1; last >= 0; last = len(ws.extPool) - 1 {
			b := ws.extPool[last]
			ws.extPool = ws.extPool[:last]
			if cap(b) >= N {
				return b[:N]
			}
		}
		return make([]ext.E6, N)
	}
	releaseExt := func(b []ext.E6) { ws.extPool = append(ws.extPool, b) }

	baseVec := ws.baseVec
	extVec := ws.extVec

	for _, n := range d.Nodes {
		if n.Field == field.Base {
			dst := allocBase()
			evalBaseNodeOnAllEntries(dst, n, baseVec, PiBase, N, allocBase, releaseBase)
			baseVec[n.Index] = dst
		} else {
			nodeDst := dst
			if n != d.Root {
				nodeDst = allocExt()
			}
			evalExtNodeOnAllEntries(nodeDst, n, baseVec, extVec, PiExt, N, allocExt, releaseExt)
			extVec[n.Index] = nodeDst
		}

		for _, child := range n.Children {
			refCount[child.Index]--
			if refCount[child.Index] != 0 || child == d.Root {
				continue
			}
			if child.Field == field.Base {
				releaseBase(baseVec[child.Index])
				baseVec[child.Index] = nil
			} else {
				releaseExt(extVec[child.Index])
				extVec[child.Index] = nil
			}
		}
	}
}

func (ws *EvalWorkspace) prepare(numNodes int) {
	ws.refCount = resizeAndClear(ws.refCount, numNodes)
	ws.baseVec = resizeAndClear(ws.baseVec, numNodes)
	ws.extVec = resizeAndClear(ws.extVec, numNodes)
}

func resizeAndClear[S ~[]E, E any](s S, n int) S {
	if cap(s) < n {
		return make(S, n)
	}
	s = s[:n]
	clear(s)
	return s
}

// evalBaseNodeOnAllEntries evaluates one base-valued node for
// EvalOnAllEntriesMixed into dst. It mirrors the base-only EvalOnAllEntries
// tight loops so base subgraphs remain on koalabear arithmetic even when the
// overall expression root is extension-valued.
func evalBaseNodeOnAllEntries(dst []koalabear.Element, n *DAGNode, baseVec [][]koalabear.Element, PiBase [][]koalabear.Element, N int, alloc func() []koalabear.Element, release func([]koalabear.Element)) {
	switch n.Kind {
	case KindLeaf:
		fillBaseLeafVector(dst, n, PiBase, N)

	case KindAdd:
		copy(dst, baseVec[n.Children[0].Index])
		for _, child := range n.Children[1:] {
			src := baseVec[child.Index]
			for j := range N {
				dst[j].Add(&dst[j], &src[j])
			}
		}

	case KindSub:
		l, r := baseVec[n.Children[0].Index], baseVec[n.Children[1].Index]
		for j := range N {
			dst[j].Sub(&l[j], &r[j])
		}

	case KindMul:
		copy(dst, baseVec[n.Children[0].Index])
		for _, child := range n.Children[1:] {
			src := baseVec[child.Index]
			for j := range N {
				dst[j].Mul(&dst[j], &src[j])
			}
		}

	case KindPow:
		base := baseVec[n.Children[0].Index]
		tmp := alloc()
		copy(tmp, base)
		for j := range N {
			dst[j].SetOne()
		}
		exp := n.Exp
		for exp > 0 {
			if exp&1 == 1 {
				for j := range N {
					dst[j].Mul(&dst[j], &tmp[j])
				}
			}
			for j := range N {
				tmp[j].Mul(&tmp[j], &tmp[j])
			}
			exp >>= 1
		}
		release(tmp)

	default:
		panic(fmt.Sprintf("EvalOnAllEntriesMixed: unknown NodeKind %d", n.Kind))
	}
}

// fillBaseLeafVector writes the N row values of a base leaf into dst. It
// handles constant leaves, length-1 constant polynomials, rotated columns, and
// regular columns using the same row-selection convention as EvalOnAllEntries.
func fillBaseLeafVector(dst []koalabear.Element, n *DAGNode, PiBase [][]koalabear.Element, N int) {
	if n.IsConst {
		for j := range N {
			dst[j] = n.ConstVal
		}
		return
	}

	l := n.Leaf
	p := PiBase[l.Idx]
	if len(p) == 1 {
		for j := range N {
			dst[j] = p[0]
		}
	} else if l.Shift != 0 {
		for j := range N {
			dst[j] = p[(j+N+l.Shift)%N]
		}
	} else {
		copy(dst, p[:N])
	}
}

// evalExtNodeOnAllEntries evaluates one extension-valued node for
// EvalOnAllEntriesMixed into dst. Extension children are consumed directly
// from extVec; base children are lifted row by row from baseVec.
func evalExtNodeOnAllEntries(dst []ext.E6, n *DAGNode, baseVec [][]koalabear.Element, extVec [][]ext.E6, PiExt [][]ext.E6, N int, alloc func() []ext.E6, release func([]ext.E6)) {
	switch n.Kind {
	case KindLeaf:
		fillExtLeafVector(dst, n, PiExt, N)

	case KindAdd:
		copyChildVectorToExt(dst, n.Children[0], baseVec, extVec, N)
		for _, child := range n.Children[1:] {
			addChildVectorToExt(dst, child, baseVec, extVec, N)
		}

	case KindSub:
		copyChildVectorToExt(dst, n.Children[0], baseVec, extVec, N)
		subChildVectorFromExt(dst, n.Children[1], baseVec, extVec, N)

	case KindMul:
		copyChildVectorToExt(dst, n.Children[0], baseVec, extVec, N)
		for _, child := range n.Children[1:] {
			mulChildVectorIntoExt(dst, child, baseVec, extVec, N)
		}

	case KindPow:
		tmp := alloc()
		copyChildVectorToExt(tmp, n.Children[0], baseVec, extVec, N)
		for j := range N {
			dst[j].SetOne()
		}
		exp := n.Exp
		for exp > 0 {
			if exp&1 == 1 {
				for j := range N {
					dst[j].Mul(&dst[j], &tmp[j])
				}
			}
			for j := range N {
				tmp[j].Mul(&tmp[j], &tmp[j])
			}
			exp >>= 1
		}
		release(tmp)

	default:
		panic(fmt.Sprintf("EvalOnAllEntriesMixed: unknown NodeKind %d", n.Kind))
	}
}

// fillExtLeafVector writes the N row values of an extension leaf into dst. It
// mirrors fillBaseLeafVector for the extension rail, while constants are base
// values embedded into E6.
func fillExtLeafVector(dst []ext.E6, n *DAGNode, PiExt [][]ext.E6, N int) {
	if n.IsConst {
		v := liftBaseToE6(n.ConstVal)
		for j := range N {
			dst[j] = v
		}
		return
	}

	l := n.Leaf
	p := PiExt[l.Idx]
	if len(p) == 1 {
		for j := range N {
			dst[j] = p[0]
		}
	} else if l.Shift != 0 {
		for j := range N {
			dst[j] = p[(j+N+l.Shift)%N]
		}
	} else {
		copy(dst, p[:N])
	}
}

// copyChildVectorToExt copies an already-computed child vector into an
// extension destination, lifting each row when the child vector lives on the
// base rail.
func copyChildVectorToExt(dst []ext.E6, child *DAGNode, baseVec [][]koalabear.Element, extVec [][]ext.E6, N int) {
	if child.Field == field.Ext {
		copy(dst, extVec[child.Index])
		return
	}
	src := baseVec[child.Index]
	for j := range N {
		dst[j] = fieldhash.LiftBaseToExt(src[j])
	}
}

// addChildVectorToExt accumulates a child vector into an extension destination.
// Base children are lifted per row; extension children are added directly.
func addChildVectorToExt(dst []ext.E6, child *DAGNode, baseVec [][]koalabear.Element, extVec [][]ext.E6, N int) {
	if child.Field == field.Ext {
		src := extVec[child.Index]
		for j := range N {
			dst[j].Add(&dst[j], &src[j])
		}
		return
	}
	src := baseVec[child.Index]
	for j := range N {
		dst[j].B0.A0.Add(&dst[j].B0.A0, &src[j])
	}
}

// subChildVectorFromExt subtracts a child vector from an extension destination.
// Base children are lifted per row; extension children are subtracted directly.
func subChildVectorFromExt(dst []ext.E6, child *DAGNode, baseVec [][]koalabear.Element, extVec [][]ext.E6, N int) {
	if child.Field == field.Ext {
		src := extVec[child.Index]
		for j := range N {
			dst[j].Sub(&dst[j], &src[j])
		}
		return
	}
	src := baseVec[child.Index]
	for j := range N {
		dst[j].B0.A0.Sub(&dst[j].B0.A0, &src[j])
	}
}

// mulChildVectorIntoExt multiplies an extension destination by a child vector.
// Base children are lifted per row; extension children are multiplied directly.
func mulChildVectorIntoExt(dst []ext.E6, child *DAGNode, baseVec [][]koalabear.Element, extVec [][]ext.E6, N int) {
	if child.Field == field.Ext {
		src := extVec[child.Index]
		for j := range N {
			dst[j].Mul(&dst[j], &src[j])
		}
		return
	}
	src := baseVec[child.Index]
	ext.VectorE6(dst).MulByElement(ext.VectorE6(dst), koalabear.Vector(src))
}

// EvalWithCache evaluates the DAG using the caller-supplied cache slice instead
// of allocating a new map on each call. cache must have length >= len(d.Nodes).
// Reuse the same slice across repeated calls to avoid allocation overhead.
func (d *DAG) EvalWithCache(vals map[string]koalabear.Element, cache []koalabear.Element) koalabear.Element {
	for _, n := range d.Nodes {
		cache[n.Index] = evalDAGNodeSlice(n, cache, vals)
	}
	return cache[d.Root.Index]
}

func evalDAGNodeSlice(n *DAGNode, cache []koalabear.Element, vals map[string]koalabear.Element) koalabear.Element {
	switch n.Kind {
	case KindLeaf:
		return n.Leaf.Evaluate(vals)

	case KindAdd:
		var acc koalabear.Element
		for _, child := range n.Children {
			v := cache[child.Index]
			acc.Add(&acc, &v)
		}
		return acc

	case KindSub:
		l, r := cache[n.Children[0].Index], cache[n.Children[1].Index]
		var res koalabear.Element
		res.Sub(&l, &r)
		return res

	case KindMul:
		var acc koalabear.Element
		acc.SetOne()
		for _, child := range n.Children {
			v := cache[child.Index]
			acc.Mul(&acc, &v)
		}
		return acc

	case KindPow:
		base := cache[n.Children[0].Index]
		var res koalabear.Element
		res.SetOne()
		exp := n.Exp
		for exp > 0 {
			if exp&1 == 1 {
				res.Mul(&res, &base)
			}
			base.Mul(&base, &base)
			exp >>= 1
		}
		return res
	}
	panic(fmt.Sprintf("EvalWithCache: unknown NodeKind %d", n.Kind))
}

// Leaves returns the String() representation of every unique leaf in the DAG
// that is not excluded by config. The filtering rules are identical to those
// of Expr.Leaves: WithoutCommittedColumns, WithoutChallenges,
// WithoutSetupColumns and WithoutVerifierColumns suppress the corresponding
// leaf kinds; Const leaves are never included.
// Because the DAG deduplicates nodes, each structurally-identical leaf appears
// at most once.
func (d *DAG) Leaves(config expr.Config) []string {
	var leaves []string
	for _, n := range d.Nodes {
		if n.Kind == KindLeaf {
			leaves = append(leaves, n.Leaf.Leaves(config)...)
		}
	}
	return leaves
}

// LeavesFull returns every unique non-Const leaf in the DAG that is not
// excluded by config, as full *expr.Leaf structs. The filtering rules are
// identical to those of Expr.LeavesFull. Because the DAG deduplicates nodes,
// each structurally-identical leaf appears at most once.
func (d *DAG) LeavesFull(config expr.Config) []*expr.Leaf {
	var leaves []*expr.Leaf
	for _, n := range d.Nodes {
		if n.Kind == KindLeaf {
			leaves = append(leaves, n.Leaf.LeavesFull(config)...)
		}
	}
	return leaves
}

// Degree returns the total degree of the DAG expression, following the same
// conventions as Expr.Degree:
//   - CommittedColumn, SetupColumn and VerifierColumn leaves have degree 1.
//   - Challenge and non-zero Const leaves have degree 0.
//   - The zero Const leaf has degree NegInf (math.MinInt).
//   - Add/Sub: max of children's degrees (n-ary after Flatten).
//   - Mul: sum of children's degrees (n-ary after Flatten).
//   - Pow: base degree × exponent.
//
// Shared nodes are evaluated once; the cached result is reused for every
// parent that references them.
func (d *DAG) Degree() int {
	degrees := make(map[*DAGNode]int, len(d.Nodes))
	for _, n := range d.Nodes {
		degrees[n] = dagNodeDegree(n, degrees)
	}
	return degrees[d.Root]
}

func dagNodeDegree(n *DAGNode, degrees map[*DAGNode]int) int {
	switch n.Kind {
	case KindLeaf:
		return n.Leaf.Degree()

	case KindAdd, KindSub:
		deg := expr.NegInf
		for _, child := range n.Children {
			deg = max(deg, degrees[child])
		}
		return deg

	case KindMul:
		deg := 0
		for _, child := range n.Children {
			deg += degrees[child]
		}
		return deg

	case KindPow:
		return degrees[n.Children[0]] * int(n.Exp)
	}
	panic(fmt.Sprintf("Degree: unknown NodeKind %d", n.Kind))
}
