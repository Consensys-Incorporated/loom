package recursion

import (
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/verifier"
)

// innerProof is a loom proof to verify in circuit, with what verifying it
// needs.
type innerProof struct {
	program board.Program
	vk      setup.VerificationKey
	pi      public.Inputs
	prf     proof.Proof
}

// goTranscript verifies the proof with loom's verifier on an exposed
// transcript, and returns it: its computed challenges are the reference.
func (ip innerProof) goTranscript(t *testing.T) *fiatshamir.Transcript {
	t.Helper()
	h := hash.NewPoseidon2SpongeHasher()
	fs := fiatshamir.NewTranscript(&h)
	if err := verifier.Verify(ip.pi, ip.vk, ip.program, ip.prf, verifier.WithTranscript(fs)); err != nil {
		t.Fatalf("loom's verifier rejects the inner proof: %v", err)
	}
	return fs
}

// fiboProofs proves gnark_plonk's Fibonacci program (two public inputs, three
// lookups into a range module of another size, so several rounds with
// exposed logup totals, no setup) for each pair of initial values.
func fiboProofs(t *testing.T, inits ...[2]uint64) []innerProof {
	t.Helper()
	const n = 4
	builder := board.NewBuilder()
	fib := board.NewModule("fibonacci")
	fib.N = n
	fib.AssertZeroExceptAt(expr.Col("A", expr.WithShift(1)).Sub(expr.Col("B")), n-1)
	fib.AssertZeroExceptAt(expr.Col("B", expr.WithShift(1)).Sub(expr.Col("C")), n-1)
	fib.AssertZero(expr.Col("C").Sub(expr.Col("A")).Sub(expr.Col("B")))
	fib.AssertEqualAt(expr.Col("A"), expr.PublicInput("fibonacci.a0"), 0)
	fib.AssertEqualAt(expr.Col("B"), expr.PublicInput("fibonacci.b0"), 0)
	builder.AddModule(fib)
	rng := board.NewModule("range")
	rng.N = 2 * n
	builder.AddModule(rng)
	for _, c := range []string{"A", "B", "C"} {
		if err := arguments.Lookup(&builder, board.Column{Module: "fibonacci", In: expr.Col(c)}, board.Column{Module: "range", In: expr.Col("Lookup")}); err != nil {
			t.Fatal(err)
		}
	}
	program, err := board.Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}
	var res []innerProof
	for _, init := range inits {
		a0, b0 := koalabear.NewElement(init[0]), koalabear.NewElement(init[1])
		tr := prover.MergeTrace(prover.TraceFibonacci(n, a0, b0), prover.TraceRange(n))
		entry := func(v koalabear.Element) public.Input {
			var e public.Entry
			e.SetBase(v)
			return public.Input{Module: "fibonacci", Entries: []public.Entry{e}}
		}
		pi := public.Inputs{"fibonacci.a0": entry(a0), "fibonacci.b0": entry(b0)}
		prf, err := prover.Prove(tr, setup.ProvingKey{}, pi, program)
		if err != nil {
			t.Fatal(err)
		}
		res = append(res, innerProof{program: program, pi: pi, prf: prf})
	}
	return res
}

// vmProofs proves executions of one VM program (setup columns, several
// modules of different sizes, lookups and the memory bus) on PCS fixtures of
// one shape and the given seeds.
func vmProofs(t *testing.T, seeds ...uint64) []innerProof {
	t.Helper()
	p, err := openingsMachine(t, smallCfg).Compile()
	if err != nil {
		t.Fatal(err)
	}
	pk, vk := keys(t, p)
	st := loom.Statement{Program: p.Loom, VerificationKey: vk, PublicInputs: public.Inputs{}}
	var res []innerProof
	for _, seed := range seeds {
		cfg := smallCfg
		cfg.Seed = seed
		r, err := p.Execute(openingsMachine(t, cfg).in)
		if err != nil {
			t.Fatal(err)
		}
		prf, err := loom.Prove(st, loom.Witness{Trace: r.Trace, ProvingKey: pk})
		if err != nil {
			t.Fatal(err)
		}
		res = append(res, innerProof{program: p.Loom, vk: vk, pi: public.Inputs{}, prf: prf})
	}
	return res
}

// checkChallenges executes the verifier circuit on ip and compares every
// challenge it computed with loom's verifier's.
func checkChallenges(t *testing.T, v *Verifier, p *Program, ip innerProof) *Run {
	t.Helper()
	in, err := v.Inputs(ip.prf, ip.pi)
	if err != nil {
		t.Fatal(err)
	}
	r, err := p.Execute(in)
	if err != nil {
		t.Fatal(err)
	}
	fs := ip.goTranscript(t)
	for name, c := range v.Challenges {
		want, err := fs.ComputeChallenge(name)
		if err != nil {
			t.Fatalf("challenge %s: %v", name, err)
		}
		got := r.Value(c)
		for j := range digest {
			if !got[j].Equal(&want[j]) {
				t.Fatalf("challenge %s: lane %d = %s, want %s", name, j, got[j].String(), want[j].String())
			}
		}
	}
	return r
}

func TestVerifierTranscript(t *testing.T) {
	cases := map[string]func(t *testing.T) (innerProof, innerProof){
		"fibonacci": func(t *testing.T) (innerProof, innerProof) {
			ips := fiboProofs(t, [2]uint64{0, 1}, [2]uint64{1, 0})
			return ips[0], ips[1]
		},
		"vm": func(t *testing.T) (innerProof, innerProof) {
			ips := vmProofs(t, 3, 11)
			return ips[0], ips[1]
		},
	}
	for name, mk := range cases {
		t.Run(name, func(t *testing.T) {
			ip, ip2 := mk(t)
			v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi))
			if err != nil {
				t.Fatal(err)
			}
			// The E6 value of zeta, as a cell readers of E6 accept.
			zeta := v.ChallengeE6("__zeta")
			p, err := v.M.Compile()
			if err != nil {
				t.Fatal(err)
			}
			if got := len(v.Challenges); got != len(ip.program.Rounds)+1 {
				t.Fatalf("%d challenges, want %d", got, len(ip.program.Rounds)+1)
			}
			r := checkChallenges(t, v, p, ip)
			want := hash.OutputToExt([8]koalabear.Element(r.Value(v.Challenges["__zeta"])))
			if got := CellE6(r.Value(zeta)); !got.Equal(&want) {
				t.Fatalf("zeta as E6 = %s, want %s", got.String(), want.String())
			}
			if err := prove(t, p, r); err != nil {
				t.Fatalf("valid verifier execution rejected: %v", err)
			}
			// The same circuit on another proof of the same program.
			checkChallenges(t, v, p, ip2)
			t.Log(fmt.Sprintf("%d rounds, %d inputs", len(ip.program.Rounds), p.NumInputs()))
		})
	}
}
