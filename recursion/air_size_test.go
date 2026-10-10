package recursion

import (
	"maps"
	"slices"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/trace"
)

// accProgram is a program whose module acc can take any size (range, a fixed
// table of size rangeN, holds 0..rangeN−1; big, if bigN > 0, is a fixed
// module of size bigN with a constant column): its relations
// name rows from the start (row 0) or from the end (the last row), never by
// an absolute index past 0. acc.A accumulates acc.B (A[i+1] = A[i] + B[i]
// except on the last row) from the public input acc.a0; acc.B = i mod 8 is
// looked up in the fixed table range (a cyclic logup: an exposed total and its
// average over acc's size); acc.A's last entry and three entries of acc.B are
// exposed.
func accProgram(t *testing.T, rangeN, bigN int) board.Program {
	t.Helper()
	b := board.NewBuilder()
	acc := board.NewModule("acc")
	acc.N = 8
	A, B := expr.Col("acc.A"), expr.Col("acc.B")
	acc.AssertZeroExceptLastEntry(expr.Col("acc.A", expr.WithShift(1)).Sub(A).Sub(B))
	acc.AssertEqualAt(A, expr.PublicInput("acc.a0"), 0)
	b.AddModule(acc)
	rng := board.NewModule("range")
	rng.N = rangeN
	b.AddModule(rng)
	if bigN > 0 {
		big := board.NewModule("big")
		big.N = bigN
		big.AssertZeroExceptLastEntry(expr.Col("big.C", expr.WithShift(1)).Sub(expr.Col("big.C")))
		b.AddModule(big)
	}
	if err := arguments.Lookup(&b, board.Column{Module: "acc", In: B}, board.Column{Module: "range", In: expr.Col("range.T")}); err != nil {
		t.Fatal(err)
	}
	b.AddExposeLastEntryStep(board.RoundRunningSums, "acc", A, "acc.last")
	b.AddExposeIthValueStep(board.RoundRunningSums, "acc", B, "acc.b2", 2)
	b.AddExposeValuesStep(board.RoundRunningSums, "acc", B, "acc.sel", "acc.bs", []int{1, 5})
	program, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}
	return program
}

// withSizes returns a copy of program with the given module sizes.
func withSizes(program board.Program, sizes ModuleSizes) board.Program {
	res := program
	res.Modules = maps.Clone(program.Modules)
	for name, n := range sizes {
		res.SetSize(name, n)
	}
	return res
}

// accProof proves accProgram with acc of size n, from a0.
func accProof(t *testing.T, program board.Program, n int, a0 uint64) innerProof {
	t.Helper()
	program = withSizes(program, ModuleSizes{"acc": n})
	col := func(n int, f func(i int) uint64) []koalabear.Element {
		res := make([]koalabear.Element, n)
		for i := range res {
			res[i].SetUint64(f(i))
		}
		return res
	}
	bs := col(n, func(i int) uint64 { return uint64(i % 8) })
	as := make([]koalabear.Element, n)
	as[0].SetUint64(a0)
	for i := 1; i < n; i++ {
		as[i].Add(&as[i-1], &bs[i-1])
	}
	tr := trace.New()
	tr.SetBase("acc.A", as)
	tr.SetBase("acc.B", bs)
	tr.SetBase("range.T", col(program.Modules["range"].N, func(i int) uint64 { return uint64(i) }))
	if big, ok := program.Modules["big"]; ok {
		tr.SetBase("big.C", col(big.N, func(int) uint64 { return 7 }))
	}
	var e public.Entry
	e.SetBase(koalabear.NewElement(a0))
	pi := public.Inputs{"acc.a0": {Module: "acc", Entries: []public.Entry{e}}}
	prf, err := prover.Prove(tr, setup.ProvingKey{}, pi, program)
	if err != nil {
		t.Fatalf("size %d: %v", n, err)
	}
	ip := innerProof{program: program, pi: pi, prf: prf}
	ip.goTranscript(t) // loom's verifier accepts it
	return ip
}

// airCircuit builds the part of the verifier up to the AIR check: the sizes,
// the transcript up to zeta, the claimed values and the AIR check (no PCS).
func airCircuit(t *testing.T, ip innerProof, opts ...VerifierOption) *Verifier {
	t.Helper()
	v, err := newVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi), opts...)
	if err != nil {
		t.Fatal(err)
	}
	if err := v.buildTranscript(); err != nil {
		t.Fatal(err)
	}
	v.allocClaimed()
	if err := v.buildAIR(); err != nil {
		t.Fatal(err)
	}
	return v
}

// TestAIRDynamicSizes: one AIR-check circuit, built for acc of size 8 with acc
// dynamic, checks proofs with acc of sizes 8, 16 and 64: their challenges up to
// zeta are loom's, and their AIR checks hold (ζ^N, the Lagrange selectors of
// the first and last rows, the public input's and exposed values' indices,
// the logup average's 1/N, all at the statement's size).
func TestAIRDynamicSizes(t *testing.T) {
	program := accProgram(t, 8, 0)
	ref := accProof(t, program, 8, 3)
	v := airCircuit(t, ref, WithDynamicModules("acc"))
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	type statement struct {
		ip    innerProof
		sizes ModuleSizes
	}
	execute := func(st statement) (*Run, error) {
		in, err := v.Inputs(st.ip.prf, st.ip.pi, st.sizes)
		if err != nil {
			t.Fatal(err)
		}
		return p.Execute(in)
	}
	for _, n := range []int{8, 16, 64} {
		ip := accProof(t, program, n, 5)
		r, err := execute(statement{ip, ModuleSizes{"acc": n}})
		if err != nil {
			t.Fatalf("size %d: %v", n, err)
		}
		fs := ip.goTranscript(t)
		for name, cell := range v.Challenges {
			want, err := fs.ComputeChallenge(name)
			if err != nil {
				t.Fatal(err)
			}
			if got := r.Value(cell); [8]koalabear.Element(got) != [8]koalabear.Element(want) {
				t.Fatalf("size %d: challenge %s differs from loom's", n, name)
			}
		}
		if err := prove(t, p, r); err != nil {
			t.Fatalf("size %d: valid AIR check rejected: %v", n, err)
		}
	}

	// Statements loom rejects, at size 16.
	ip := accProof(t, program, 16, 5)
	tampered := func(f func(ip *innerProof)) innerProof {
		c := ip
		c.prf.ExposedValues = maps.Clone(ip.prf.ExposedValues)
		c.pi = maps.Clone(ip.pi)
		f(&c)
		return c
	}
	var one koalabear.Element
	one.SetOne()
	for name, st := range map[string]statement{
		// acc's first base column at zeta (tree 0: trace round 0, no setup;
		// group 0: acc), copied along the tampered path only.
		"claimed value": {tampered(func(c *innerProof) {
			cv := slices.Clone(c.prf.Opening.ClaimedValues)
			cv[0] = slices.Clone(cv[0])
			cv[0][0].Base = slices.Clone(cv[0][0].Base)
			cv[0][0].Base[0] = slices.Clone(cv[0][0].Base[0])
			cv[0][0].Base[0][0].B0.A0.Add(&cv[0][0].Base[0][0].B0.A0, &one)
			c.prf.Opening.ClaimedValues = cv
		}), ModuleSizes{"acc": 16}},
		"lying size": {ip, ModuleSizes{"acc": 32}},
		"exposed value": {tampered(func(c *innerProof) {
			ev := c.prf.ExposedValues["acc.last"]
			ev.Entries = slices.Clone(ev.Entries)
			x := ev.Entries[0].ExtValue()
			x.B0.A0.Add(&x.B0.A0, &one)
			ev.Entries[0].SetExt(x)
			c.prf.ExposedValues["acc.last"] = ev
		}), ModuleSizes{"acc": 16}},
		"public input": {tampered(func(c *innerProof) {
			var e public.Entry
			e.SetBase(koalabear.NewElement(6))
			c.pi["acc.a0"] = public.Input{Module: "acc", Entries: []public.Entry{e}}
		}), ModuleSizes{"acc": 16}},
	} {
		r, err := execute(st)
		if err != nil {
			continue // rejected at execution
		}
		if err := prove(t, p, r); err == nil {
			t.Fatalf("%s: AIR check accepted", name)
		}
	}
}
