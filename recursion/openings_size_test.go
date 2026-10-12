package recursion

import (
	"slices"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/proof"
)

// openingsCircuit builds the verifier without FRI (P3.5): the sizes, the
// transcript, the PCS transcript, the commitment openings (their Merkle
// paths), DEEP and the AIR check.
func openingsCircuit(t *testing.T, ip innerProof, opts ...VerifierOption) *Verifier {
	t.Helper()
	v, err := newVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi), opts...)
	if err != nil {
		t.Fatal(err)
	}
	if err := v.buildTranscript(); err != nil {
		t.Fatal(err)
	}
	if err := v.buildPCSTranscript(); err != nil {
		t.Fatal(err)
	}
	v.buildOpenings()
	v.buildDEEP()
	if err := v.buildAIR(); err != nil {
		t.Fatal(err)
	}
	return v
}

// TestOpeningsDynamicPaths: one circuit, built for acc of size 8, checks the
// commitment openings of proofs with acc of sizes 8, 16, 32 and 64 — trees
// whose shape changes with acc's size (acc below, equal to and above range,
// big the largest) — through dynamic paths in the canonical order at the
// statement's sizes; and rejects tampered openings, a wrong order and a lying
// size.
func TestOpeningsDynamicPaths(t *testing.T) {
	program := accProgram(t, 16, 128)
	v := openingsCircuit(t, accProof(t, program, 8, 3), WithDynamicModules("acc"))
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	if len(v.orderInputs) == 0 {
		t.Fatal("no tree takes the dynamic path")
	}
	statement := func(ip innerProof, n int) ([]Cell, error) {
		return v.Inputs(ip.prf, ip.pi, ModuleSizes{"acc": n})
	}
	for _, n := range []int{8, 16, 32, 64} {
		ip := accProof(t, program, n, 5)
		in, err := statement(ip, n)
		if err != nil {
			t.Fatalf("size %d: %v", n, err)
		}
		r, err := p.Execute(in)
		if err != nil {
			t.Fatalf("size %d: %v", n, err)
		}
		if err := prove(t, p, r); err != nil {
			t.Fatalf("size %d: valid openings rejected: %v", n, err)
		}
	}

	// Rejected statements, at size 32 (acc above range, below big).
	ip := accProof(t, program, 32, 5)
	const tree = 1 // trace round 1: acc, big and range
	rejected := func(name string, in []Cell, err error) {
		t.Helper()
		if err != nil {
			return // rejected by Inputs
		}
		r, err := p.Execute(in)
		if err != nil {
			return
		}
		if err := prove(t, p, r); err == nil {
			t.Fatalf("%s: accepted", name)
		}
	}
	tampered := func(f func(prf *proof.Proof)) innerProof {
		c := ip
		ps := slices.Clone(ip.prf.Opening.PointSamplings)
		ps[2] = slices.Clone(ps[2])
		c.prf.Opening.PointSamplings = ps
		f(&c.prf)
		return c
	}
	for name, c := range map[string]innerProof{
		"opened value": tampered(func(prf *proof.Proof) {
			wp := &prf.Opening.PointSamplings[2][tree]
			wp.Injections = slices.Clone(wp.Injections)
			lo := slices.Clone(wp.Injections[0].Rows.Lo.RawRowBase)
			lo[0].SetUint64(lo[0].Uint64() + 1)
			wp.Injections[0].Rows.Lo.RawRowBase = lo
		}),
		"sibling": tampered(func(prf *proof.Proof) {
			wp := &prf.Opening.PointSamplings[2][tree]
			sibs := slices.Clone(wp.Path.Siblings)
			sibs[1][0].SetUint64(9)
			wp.Path.Siblings = sibs
		}),
	} {
		in, err := statement(c, 32)
		rejected(name, in, err)
	}
	// π with two groups swapped.
	in, err := statement(ip, 32)
	if err != nil {
		t.Fatal(err)
	}
	pos := v.orderInputs[treeOrderKey(tree)]
	in[pos[0]], in[pos[1]] = in[pos[1]], in[pos[0]]
	rejected("order", in, nil)
	// The proof of size 32 claimed of size 16.
	in, err = statement(ip, 16)
	rejected("lying size", in, err)
}

// TestDynamicTreeOrderCheck: a tree's order π must be its canonical
// permutation at the statement's sizes. With acc of size 16, tree 1's groups
// are big (height 8), then acc and range (both 5: acc first, by index). A
// circuit holding only the sizes and the order check of tree 1 rejects the
// tied groups swapped, a group twice, and an index out of the groups.
func TestDynamicTreeOrderCheck(t *testing.T) {
	program := accProgram(t, 16, 128)
	ip := accProof(t, program, 16, 5)
	v, err := newVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi), WithDynamicModules("acc"))
	if err != nil {
		t.Fatal(err)
	}
	const tree = 1
	v.dynamicTreeOrder(tree)
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	in, err := v.Inputs(ip.prf, ip.pi, ModuleSizes{"acc": 16})
	if err != nil {
		t.Fatal(err)
	}
	pos := v.orderInputs[treeOrderKey(tree)]
	groups := v.layout.TreeGroups[tree]
	index := map[string]int{}
	for g, grp := range groups {
		index[grp.Module] = g
	}
	order := func(in []Cell) []string {
		var res []string
		for _, i := range pos {
			res = append(res, groups[in[i][0].Uint64()].Module)
		}
		return res
	}
	if got := order(in); !slices.Equal(got, []string{"big", "acc", "range"}) {
		t.Fatalf("canonical order %v, want big, acc, range", got)
	}
	r, err := p.Execute(in)
	if err != nil {
		t.Fatal(err)
	}
	if err := prove(t, p, r); err != nil {
		t.Fatalf("canonical order rejected: %v", err)
	}

	for name, pi := range map[string][]uint64{
		"tied groups swapped": {uint64(index["big"]), uint64(index["range"]), uint64(index["acc"])},
		"group twice":         {uint64(index["big"]), uint64(index["acc"]), uint64(index["acc"])},
		"index out of range":  {uint64(index["big"]), uint64(index["acc"]), 3},
	} {
		bad := slices.Clone(in)
		for k, g := range pi {
			bad[pos[k]] = ScalarCell(koalabear.NewElement(g))
		}
		r, err := p.Execute(bad)
		if err != nil {
			continue // rejected at execution (a lookup out of its table)
		}
		if err := prove(t, p, r); err == nil {
			t.Fatalf("%s: accepted", name)
		}
	}
}
