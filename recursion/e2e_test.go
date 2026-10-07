package recursion

import (
	"fmt"
	"sort"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/trace"
)

// exposeProofs proves a program using the three expose steps: an
// accumulator A[i+1] = A[i] + B[i], whose last entry, B at row 2 and B at
// rows 1 and 5 are exposed. Its relations use relative Lagrange columns and
// exposed columns with indexed entries.
func exposeProofs(t *testing.T, seeds ...uint64) []innerProof {
	t.Helper()
	const n = 8
	b := board.NewBuilder()
	mod := board.NewModule("acc")
	mod.N = n
	mod.AssertZeroExceptAt(expr.Col("acc.A", expr.WithShift(1)).Sub(expr.Col("acc.A")).Sub(expr.Col("acc.B")), n-1)
	b.AddModule(mod)
	b.AddExposeLastEntryStep(0, "acc", expr.Col("acc.A"), "acc.last")
	b.AddExposeIthValueStep(0, "acc", expr.Col("acc.B"), "acc.b2", 2)
	b.AddExposeValuesStep(0, "acc", expr.Col("acc.B"), "acc.sel", "acc.bs", []int{1, 5})
	program, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}
	var res []innerProof
	for _, seed := range seeds {
		a, bv := make([]koalabear.Element, n), make([]koalabear.Element, n)
		for i := range n {
			bv[i].SetUint64(seed*31 + uint64(i)*7 + 1)
			if i > 0 {
				a[i].Add(&a[i-1], &bv[i-1])
			}
		}
		tr := trace.New()
		tr.SetBase("acc.A", a)
		tr.SetBase("acc.B", bv)
		prf, err := prover.Prove(tr, setup.ProvingKey{}, public.Inputs{}, program)
		if err != nil {
			t.Fatal(err)
		}
		res = append(res, innerProof{program: program, pi: public.Inputs{}, prf: prf})
	}
	return res
}

// verifierRun builds the verifier of ip's program and executes it on ip.
func verifierRun(t *testing.T, ip innerProof) (*Verifier, *Program, *Run) {
	t.Helper()
	v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi))
	if err != nil {
		t.Fatal(err)
	}
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	in, err := v.Inputs(ip.prf, ip.pi)
	if err != nil {
		t.Fatal(err)
	}
	r, err := p.Execute(in)
	if err != nil {
		t.Fatal(err)
	}
	return v, p, r
}

// TestVerifierExposedColumns verifies, in circuit, proofs of a program with
// exposed columns, and checks the challenges and DEEP values against Go.
func TestVerifierExposedColumns(t *testing.T) {
	ips := exposeProofs(t, 1, 2)
	v, p, r := verifierRun(t, ips[0])
	if err := prove(t, p, r); err != nil {
		t.Fatalf("valid verifier execution rejected: %v", err)
	}
	checkChallenges(t, v, p, ips[1])
}

// TestVerifierRejects: statements the Go verifier rejects are rejected by the
// circuit too, end to end.
func TestVerifierRejects(t *testing.T) {
	cases := map[string]func(t *testing.T) innerProof{
		// a proof of Fibonacci(0, 1), against the public inputs of (1, 0)
		"wrong public input": func(t *testing.T) innerProof {
			ips := fiboProofs(t, [2]uint64{0, 1}, [2]uint64{1, 0})
			ip := ips[0]
			ip.pi = ips[1].pi
			return ip
		},
		"commitment": func(t *testing.T) innerProof {
			ip := fiboProofs(t, [2]uint64{0, 1})[0]
			ip.prf.Commitments[1][2].SetUint64(9)
			return ip
		},
		"logup total": func(t *testing.T) innerProof {
			ip := fiboProofs(t, [2]uint64{0, 1})[0]
			for name, ev := range ip.prf.ExposedValues {
				e := ev.Entries[0]
				val := e.ExtValue()
				val.B0.A0.SetUint64(val.B0.A0.Uint64() + 1)
				e.SetExt(val)
				ip.prf.ExposedValues[name] = proof.ExposedValue{Entries: []proof.ExposedEntry{e}}
				break
			}
			return ip
		},
		"exposed column entry": func(t *testing.T) innerProof {
			ip := exposeProofs(t, 1)[0]
			ev := ip.prf.ExposedValues["acc.bs"]
			e := ev.Entries[1]
			e.Value.SetUint64(e.Value.Uint64() + 1)
			e.ValueExt.B0.A0 = e.Value
			ev.Entries = append([]proof.ExposedEntry{ev.Entries[0]}, e)
			ip.prf.ExposedValues["acc.bs"] = ev
			return ip
		},
	}
	for name, mk := range cases {
		t.Run(name, func(t *testing.T) {
			ip := mk(t)
			// the circuit is built from the honest shape: the same as ip's
			v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi))
			if err != nil {
				t.Fatal(err)
			}
			p, err := v.M.Compile()
			if err != nil {
				t.Fatal(err)
			}
			in, err := v.Inputs(ip.prf, ip.pi)
			if err != nil {
				t.Fatal(err)
			}
			r, err := p.Execute(in)
			if err != nil {
				return // caught at execution (e.g. a zero divisor)
			}
			if err := prove(t, p, r); err == nil {
				t.Fatal("invalid statement accepted")
			}
		})
	}
}

// TestVerifierSize logs, for each inner program, the verifier circuit's rows
// per chip, its leaf cost per query, and the times to build, execute and
// prove it.
func TestVerifierSize(t *testing.T) {
	cases := []struct {
		name string
		ip   func(t *testing.T) innerProof
	}{
		{"fibonacci", func(t *testing.T) innerProof { return fiboProofs(t, [2]uint64{0, 1})[0] }},
		{"expose", func(t *testing.T) innerProof { return exposeProofs(t, 1)[0] }},
		{"vm", func(t *testing.T) innerProof { return vmProofs(t, 3)[0] }},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			ip := c.ip(t)
			t0 := time.Now()
			v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi))
			if err != nil {
				t.Fatal(err)
			}
			p, err := v.M.Compile()
			if err != nil {
				t.Fatal(err)
			}
			build := time.Since(t0)
			in, err := v.Inputs(ip.prf, ip.pi)
			if err != nil {
				t.Fatal(err)
			}
			t0 = time.Now()
			r, err := p.Execute(in)
			if err != nil {
				t.Fatal(err)
			}
			exec := time.Since(t0)
			t0 = time.Now()
			if err := prove(t, p, r); err != nil {
				t.Fatal(err)
			}
			prv := time.Since(t0)
			var mods []string
			for name := range p.Loom.Modules {
				mods = append(mods, name)
			}
			sort.Strings(mods)
			var sb []byte
			for _, name := range mods {
				sb = fmt.Appendf(sb, " %s=%d", name, p.Loom.Modules[name].N)
			}
			leaf := LeafCostOf(p.Loom)
			t.Logf("inner: %d modules; verifier: %d inputs, rows:%s; leaf %d elements/query; build %v, execute %v, setup+prove+verify %v",
				len(ip.program.Modules), p.NumInputs(), sb, leaf.Elements, build.Round(time.Millisecond), exec.Round(time.Millisecond), prv.Round(time.Millisecond))
		})
	}
}

// TestTwoLevels is recursion: a proof of a Fibonacci program is verified by
// a verifier circuit, whose execution is proved; that proof is verified by a
// second verifier circuit, whose execution is proved in turn.
func TestTwoLevels(t *testing.T) {
	inner := fiboProofs(t, [2]uint64{0, 1})[0]

	// Level 1: the Fibonacci verifier's execution, proved.
	_, p1, r1 := verifierRun(t, inner)
	pk1, vk1 := keys(t, p1)
	st1 := loom.Statement{Program: p1.Loom, VerificationKey: vk1, PublicInputs: public.Inputs{}}
	t0 := time.Now()
	prf1, err := loom.Prove(st1, loom.Witness{Trace: r1.Trace, ProvingKey: pk1})
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("level 1: proved in %v", time.Since(t0).Round(time.Millisecond))
	level1 := innerProof{program: p1.Loom, vk: vk1, pi: public.Inputs{}, prf: prf1}

	// Level 2: the verifier of the level-1 program, on that proof.
	t0 = time.Now()
	v2, p2, r2 := verifierRun(t, level1)
	t.Logf("level 2: %d inputs, built and executed in %v", p2.NumInputs(), time.Since(t0).Round(time.Millisecond))
	t0 = time.Now()
	if err := prove(t, p2, r2); err != nil {
		t.Fatalf("level-2 verifier execution rejected: %v", err)
	}
	t.Logf("level 2: setup, proved and verified in %v", time.Since(t0).Round(time.Millisecond))
	var rows []byte
	for _, name := range []string{e6Mod, windowMod, spongeMod, merkleMod, p2Mod} {
		rows = fmt.Appendf(rows, " %s=%d", name, p2.Loom.Modules[name].N)
	}
	t.Logf("level 2 rows:%s; leaf %d elements/query", rows, LeafCostOf(p2.Loom).Elements)
	_ = v2
}
