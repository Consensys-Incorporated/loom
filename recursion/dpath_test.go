package recursion

import (
	"math/rand/v2"
	"sort"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/merkle"
	"github.com/consensys/loom/trace"
)

// The dynamic path circuit of these tests: G groups, heights up to H, rows of
// L bits.
const (
	dpG = 4
	dpH = 8
	dpL = 10
)

// dpathValues are the input values of a dynamic path: the groups' leaves and
// heights, the order, the siblings by height, the row's bits and the root.
type dpathValues struct {
	leaves  []hash.Digest
	heights []int
	order   []int
	sibs    []hash.Digest
	bits    []uint64
	root    hash.Digest
}

// canonicalOrder returns the groups by decreasing height, equal heights by
// increasing index.
func canonicalOrder(heights []int) []int {
	order := make([]int, len(heights))
	for g := range order {
		order[g] = g
	}
	sort.SliceStable(order, func(a, b int) bool { return heights[order[a]] > heights[order[b]] })
	return order
}

// dpathTree builds an internal/merkle mixed-height tree with the groups at
// the given heights (the canonical order's first group gives the leaves, the
// others are injections of width 2^h, in that order), opens it at a random
// leaf, and returns the dynamic path's values for that opening.
func dpathTree(t *testing.T, heights []int, seed uint64) dpathValues {
	t.Helper()
	r := rand.New(rand.NewPCG(seed, 31))
	order := canonicalOrder(heights)
	top := heights[order[0]]
	leaves := randDigests(r, 1<<top)
	var injections []merkle.LevelInjection
	for _, g := range order[1:] {
		injections = append(injections, merkle.LevelInjection{LevelWidth: 1 << heights[g], LeafHashes: randDigests(r, 1<<heights[g])})
	}
	tree, err := merkle.NewWithInjections(1<<top, fri.DefaultNodeHasher, injections)
	if err != nil {
		t.Fatal(err)
	}
	if err := tree.Build(leaves); err != nil {
		t.Fatal(err)
	}
	i := r.IntN(1 << top)
	prf, err := tree.OpenProof(i)
	if err != nil {
		t.Fatal(err)
	}
	widths := make([]int, len(injections))
	for k, inj := range injections {
		widths[k] = inj.LevelWidth
	}
	if !merkle.VerifyWithInjections(tree.Root(), prf, leaves[i], widths, fri.DefaultNodeHasher) {
		t.Fatal("the reference opening does not verify")
	}

	v := dpathValues{leaves: make([]hash.Digest, len(heights)), heights: heights, order: order, sibs: make([]hash.Digest, dpH), root: tree.Root()}
	v.leaves[order[0]] = leaves[i]
	for k, g := range order[1:] {
		v.leaves[g] = prf.InjectionLeaves[k]
	}
	for h := 1; h <= top; h++ {
		v.sibs[h-1] = prf.Siblings[top-h]
	}
	// The row: the leaf index at height top, then random low bits.
	s := uint64(i)<<(dpL-top) | r.Uint64N(1<<(dpL-top))
	for j := range dpL {
		v.bits = append(v.bits, s>>j&1)
	}
	return v
}

// cells returns the input cells of v, in the circuit's input order.
func (v dpathValues) cells() []Cell {
	var res []Cell
	for _, d := range v.leaves {
		res = append(res, digestCell(d))
	}
	for _, h := range v.heights {
		res = append(res, ScalarCell(koalabear.NewElement(uint64(h))))
	}
	for _, g := range v.order {
		res = append(res, ScalarCell(koalabear.NewElement(uint64(g))))
	}
	for _, d := range v.sibs {
		res = append(res, digestCell(d))
	}
	for _, b := range v.bits {
		res = append(res, ScalarCell(koalabear.NewElement(b)))
	}
	return append(res, digestCell(v.root))
}

// dpathCircuit is one dynamic path over input tables, its inputs being those
// of v (cells' order).
func dpathCircuit(v dpathValues) *builder {
	b := &builder{}
	in := v.cells()
	next := 0
	// explicit kinds: the circuit is executed on other trees, whose unused
	// siblings (zero here) may be digests there
	inputs := func(n, kind int) []int {
		res := make([]int, n)
		for i := range res {
			res[i] = b.inputKind(in[next], kind)
			next++
		}
		return res
	}
	leaves := b.Table(inputs(dpG, KindDigest))
	heights, order := b.Table(inputs(dpG, KindScalar)), b.Table(inputs(dpG, KindScalar))
	sibs, bits := b.Table(inputs(dpH, KindDigest)), b.Table(inputs(dpL, KindScalar))
	root := inputs(1, KindDigest)[0]
	b.MerklePathDynamic(DynamicPath{Leaves: leaves, Heights: heights, Order: order, Siblings: sibs, Bits: bits, L: dpL, Root: root})
	return b
}

// TestDynamicPath: one circuit checks the openings of mixed-height trees of
// every shape — distinct heights, all groups at the top, a top below H, the
// top group changing, all at height 1, a group at H — against internal/merkle.
func TestDynamicPath(t *testing.T) {
	patterns := [][]int{{5, 3, 3, 2}, {8, 8, 8, 8}, {4, 4, 4, 4}, {2, 6, 6, 1}, {1, 1, 1, 1}, {8, 1, 4, 4}, {3, 7, 3, 7}}
	p, err := dpathCircuit(dpathTree(t, patterns[0], 0)).Compile()
	if err != nil {
		t.Fatal(err)
	}
	for i, hs := range patterns {
		v := dpathTree(t, hs, uint64(i))
		r, err := p.Execute(v.cells())
		if err != nil {
			t.Fatalf("heights %v: %v", hs, err)
		}
		if err := prove(t, p, r); err != nil {
			t.Fatalf("heights %v: valid opening rejected: %v", hs, err)
		}
	}
}

// TestDynamicPathRejects: openings the circuit must reject, on the tree of
// heights 5, 3, 3, 2 — statements whose execution goes through (the circuit,
// not the executor, rejects them), then traces tampered past the executor.
func TestDynamicPathRejects(t *testing.T) {
	hs := []int{5, 3, 3, 2}
	p, err := dpathCircuit(dpathTree(t, hs, 7)).Compile()
	if err != nil {
		t.Fatal(err)
	}
	statements := map[string]func(v *dpathValues){
		// groups 1 and 2 share height 3: folded in the other order
		"order of equal heights": func(v *dpathValues) { v.order = []int{0, 2, 1, 3} },
		// group 1 folded twice, group 2 never
		"group twice": func(v *dpathValues) { v.order = []int{0, 1, 1, 3} },
		// group 2 claimed at height 2: folded at the wrong level
		"wrong height": func(v *dpathValues) {
			v.heights = []int{5, 3, 2, 2}
			v.order = []int{0, 1, 2, 3}
		},
		"sibling": func(v *dpathValues) { v.sibs[2][0].SetUint64(9) },
		// the direction bit of height 3: bit L − 3 of the row
		"direction bit": func(v *dpathValues) { v.bits[dpL-3] ^= 1 },
		"root":          func(v *dpathValues) { v.root[1].SetUint64(9) },
		"leaf":          func(v *dpathValues) { v.leaves[3][2].SetUint64(9) },
	}
	for name, edit := range statements {
		t.Run(name, func(t *testing.T) {
			v := dpathTree(t, hs, 7)
			v.heights = append([]int(nil), v.heights...)
			v.sibs = append([]hash.Digest(nil), v.sibs...)
			v.leaves = append([]hash.Digest(nil), v.leaves...)
			v.bits = append([]uint64(nil), v.bits...)
			edit(&v)
			r, err := p.Execute(v.cells())
			if err != nil {
				t.Fatalf("not executed: %v", err)
			}
			if err := prove(t, p, r); err == nil {
				t.Fatal("tampered opening accepted")
			}
		})
	}

	// Execution rejects orders that do not decrease, and heights out of
	// [1, H].
	for name, edit := range map[string]func(v *dpathValues){
		"increasing order": func(v *dpathValues) { v.order = []int{3, 0, 1, 2} },
		"height 0":         func(v *dpathValues) { v.heights = []int{5, 3, 3, 0} },
		"height above H":   func(v *dpathValues) { v.heights = []int{dpH + 1, 3, 3, 2} },
	} {
		v := dpathTree(t, hs, 7)
		v.heights = append([]int(nil), v.heights...)
		edit(&v)
		if _, err := p.Execute(v.cells()); err == nil {
			t.Fatalf("%s: executed", name)
		}
	}

	// Traces tampered past the executor. The rows: H − 5 = 3 copies, then
	// group 0 (the leaf) at row 3.
	var one koalabear.Element
	one.SetOne()
	for name, tamper := range map[string]func(tr trace.Trace){
		// a fold with its leaf on the left
		"fold direction": func(tr trace.Trace) { tr.Base["dpath.b"][3].SetOne() },
		// a copy row (before the leaf) that changes the running value
		"copy": func(tr trace.Trace) { tr.Base["dpath.out0"][1].Add(&tr.Base["dpath.out0"][1], &one) },
		// a level skipped: one compress row turned into a fold
		"kind": func(tr trace.Trace) { tr.Base["dpath.kind"][2].SetOne() },
	} {
		t.Run(name, func(t *testing.T) {
			if err := compileAndProve(t, dpathCircuit(dpathTree(t, hs, 7)), witnessOnly(tamper)); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}

// TestDynamicPathFoldsAtItsHeight: a group must fold at the height its
// Heights entry gives. The tree of heights 5, 3, 3, 2 holds group 2 at height
// 3; claiming height 2 for it, a forged trace still folds it at height 3 (row
// 7: 3 copies, group 0, two levels, group 1, group 2), where the tree needs
// it, and reads the claimed 2 consistently (the input cell, the table's
// entry, the row's hg): only the fold-height constraint rejects it.
func TestDynamicPathFoldsAtItsHeight(t *testing.T) {
	two := koalabear.NewElement(2)
	tamper := func(_, w trace.Trace) {
		w.Base["witness.v0"][dpG+2] = two // the input cell of heights[2]
		w.Base["table.v0"][dpG+2] = two   // the heights table's entry 2
		w.Base["dpath.hg"][7] = two
	}
	if err := compileAndProve(t, dpathCircuit(dpathTree(t, []int{5, 3, 3, 2}, 7)), tamper); err == nil {
		t.Fatal("group folded at another height than its claimed one")
	}
}
