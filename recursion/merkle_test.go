package recursion

import (
	"fmt"
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/merkle"
	"github.com/consensys/loom/trace"
)

const injDepth = 4 // 16 leaves

// injectionSchedules covers no injection, one, the leaf level, repeated
// widths and the root level (width 1).
var injectionSchedules = [][]int{{}, {8}, {16}, {16, 16, 4, 4, 4, 1}, {8, 2, 1, 1}}

func randDigests(r *rand.Rand, n int) []hash.Digest {
	res := make([]hash.Digest, n)
	for i := range res {
		for j := range res[i] {
			res[i][j].SetUint64(r.Uint64())
		}
	}
	return res
}

// injectionTree builds an internal/merkle tree with loom's node hasher and
// the given injection widths.
func injectionTree(t *testing.T, widths []int, seed uint64) (*merkle.Tree, []hash.Digest) {
	t.Helper()
	r := rand.New(rand.NewPCG(seed, 2))
	var injections []merkle.LevelInjection
	for _, w := range widths {
		injections = append(injections, merkle.LevelInjection{LevelWidth: w, LeafHashes: randDigests(r, w)})
	}
	tree, err := merkle.NewWithInjections(1<<injDepth, fri.DefaultNodeHasher, injections)
	if err != nil {
		t.Fatal(err)
	}
	leaves := randDigests(r, 1<<injDepth)
	if err := tree.Build(leaves); err != nil {
		t.Fatal(err)
	}
	return tree, leaves
}

// injectionMachine opens every leaf of the tree with MerklePathX (x⁻¹ and b0
// checked against Go, which exercises paths whose first row is an
// injection); edit may alter a path's injections before it is built.
func injectionMachine(t *testing.T, widths []int, edit func(leaf int, inj []Injection)) *builder {
	t.Helper()
	tree, leaves := injectionTree(t, widths, 1)
	b := &builder{}
	root := b.Const(digestCell(tree.Root()))
	var gInv koalabear.Element
	gInv.SetUint64(987654321)
	for i, leaf := range leaves {
		prf, err := tree.OpenProof(i)
		if err != nil {
			t.Fatal(err)
		}
		var sibs []int
		for _, s := range prf.Siblings {
			sibs = append(sibs, b.input(digestCell(s)))
		}
		var inj []Injection
		for k, w := range widths {
			inj = append(inj, Injection{Width: w, Leaf: b.input(digestCell(prf.InjectionLeaves[k]))})
		}
		if edit != nil {
			edit(i, inj)
		}
		xb := b.MerklePathX(b.input(digestCell(leaf)), sibs, b.input(ScalarCell(koalabear.NewElement(uint64(i)))), root, gInv, inj...)
		var want Cell
		want[0].ExpInt64(gInv, int64(bitrev(i, injDepth)))
		want[1].SetUint64(uint64(i & 1))
		b.AssertEq(xb, b.Const(want))
	}
	return b
}

func TestMerkleInjections(t *testing.T) {
	for _, widths := range injectionSchedules {
		t.Run(fmt.Sprint(widths), func(t *testing.T) {
			if err := compileAndProve(t, injectionMachine(t, widths, nil), nil); err != nil {
				t.Fatalf("valid paths rejected: %v", err)
			}
		})
	}

	widths := []int{16, 16, 4, 4, 4, 1}
	stepsPerPath := injDepth + len(widths)
	// Rows of the first path: inj(16) inj(16) lvl0 lvl1 inj(4)×3 lvl2 lvl3
	// inj(1).
	rejects := map[string]struct {
		edit   func(leaf int, inj []Injection)
		tamper func(trace.Trace)
	}{
		// the two leaf-level injections, swapped: their order is committed
		"same-width order": {edit: func(leaf int, inj []Injection) {
			if leaf == 3 {
				inj[0].Leaf, inj[1].Leaf = inj[1].Leaf, inj[0].Leaf
			}
		}},
		// a root-level injection leaf of another path
		"injection leaf": {edit: func(leaf int, inj []Injection) {
			if leaf == 5 {
				inj[5].Leaf = inj[4].Leaf
			}
		}},
		// a direction bit set on an injection row
		"injection bit": {tamper: func(tr trace.Trace) { tr.Base["merkle.b"][stepsPerPath+4].SetOne() }},
		// an injection row of leaf 13's path (0b1101) that consumes an index
		// bit: after two levels the index left is 3, it becomes 6
		"injection index": {tamper: func(tr trace.Trace) {
			idx := &tr.Base["merkle.idx"][13*stepsPerPath+4]
			if idx.Uint64() != 3 {
				panic(fmt.Sprintf("index left = %d, want 3", idx.Uint64()))
			}
			idx.Double(idx)
		}},
	}
	for name, c := range rejects {
		t.Run(name, func(t *testing.T) {
			var tamper func(_, w trace.Trace)
			if c.tamper != nil {
				tamper = witnessOnly(c.tamper)
			}
			if err := compileAndProve(t, injectionMachine(t, widths, c.edit), tamper); err == nil {
				t.Fatal("invalid path accepted")
			}
		})
	}
}

func TestPathSteps(t *testing.T) {
	sibs := []int{10, 11, 12}
	steps, err := pathSteps(sibs, []Injection{{8, 20}, {4, 21}, {4, 22}, {1, 23}})
	if err != nil {
		t.Fatal(err)
	}
	want := []pathStep{{sib: 20, inj: true}, {sib: 10, lvl: 0}, {sib: 21, inj: true}, {sib: 22, inj: true},
		{sib: 11, lvl: 1}, {sib: 12, lvl: 2}, {sib: 23, inj: true}}
	if fmt.Sprint(steps) != fmt.Sprint(want) {
		t.Fatalf("steps %v, want %v", steps, want)
	}
	for _, bad := range [][]Injection{{{4, 0}, {8, 0}}, {{16, 0}}, {{3, 0}}, {{0, 0}}} {
		if _, err := pathSteps(sibs, bad); err == nil {
			t.Fatalf("schedule %v accepted", bad)
		}
	}
}
