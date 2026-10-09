package recursion

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
)

// deepCircuit builds the part of the verifier up to the DEEP quotients: the
// sizes, the transcript, the PCS transcript (FRI challenges and queries), the
// opened values (without their Merkle paths) and DEEP.
func deepCircuit(t *testing.T, ip innerProof, opts ...VerifierOption) *Verifier {
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
	v.allocOpenings()
	v.buildDEEP()
	return v
}

// TestDEEPDynamicSizes: one DEEP circuit, built for acc of size 8 with acc
// dynamic, computes the DEEP quotients of proofs with acc of sizes 8, 16 and
// 32 — at the point X of acc's class, read at the query's depth for acc's
// size, and at acc's shift points ζ·ω_N^s — equal to the FRI level openings
// loom's prover committed. range (size 64, fixed) stays the largest module,
// so FRI's shape and the trees' group order do not change (P3.4, P3.5).
func TestDEEPDynamicSizes(t *testing.T) {
	program := accProgram(t, 64)
	v := deepCircuit(t, accProof(t, program, 8, 3), WithDynamicModules("acc"))
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	for _, n := range []int{8, 16, 32} {
		ip := accProof(t, program, n, 5)
		in, err := v.Inputs(ip.prf, ip.pi, ModuleSizes{"acc": n})
		if err != nil {
			t.Fatal(err)
		}
		r, err := p.Execute(in)
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
		fp := ip.prf.Opening.FRIProof
		for k := range v.DEEP {
			for c, dq := range v.DEEP[k] {
				lvl := v.fri.levelOf[c]
				layer := fp.FRIQueries[k].Layers[0]
				if lvl > 0 {
					layer = fp.LevelQueries[lvl-1][k]
				}
				for side, want := range []ext.E6{layer.LeafPExt, layer.LeafQExt} {
					if got := CellE6(r.Value(dq[side])); !got.Equal(&want) {
						t.Fatalf("size %d, query %d, class %s, side %d: DQ = %s, want %s", n, k, v.fri.classMod[c], side, got.String(), want.String())
					}
				}
			}
		}
		if n == 16 {
			if err := prove(t, p, r); err != nil {
				t.Fatalf("size %d: valid DEEP circuit rejected: %v", n, err)
			}
		}
	}
}

// TestDynamicModuleMinimumSize: a dynamic module's size must exceed twice its
// largest shift — acc's shifts are −1, 0 and 1, so its sizes start at 4 —
// below which shifts merge mod N and the proof's shape changes.
func TestDynamicModuleMinimumSize(t *testing.T) {
	program := accProgram(t, 64)
	if got := minLogSize(program.Modules["acc"]); got != 2 {
		t.Fatalf("acc's minimum log size is %d, want 2", got)
	}
	ip := accProof(t, program, 8, 3)
	v := deepCircuit(t, ip, WithDynamicModules("acc"))
	for _, n := range []int{1, 2} {
		if _, err := v.Inputs(ip.prf, ip.pi, ModuleSizes{"acc": n}); err == nil {
			t.Fatalf("acc of size %d accepted", n)
		}
	}
	if _, err := v.Inputs(ip.prf, ip.pi, ModuleSizes{"acc": 4}); err != nil {
		t.Fatalf("acc of size 4: %v", err)
	}
	small := withSizes(program, ModuleSizes{"acc": 2})
	if _, err := newVerifier(small, ip.vk, ShapeOf(ip.prf, ip.pi), WithDynamicModules("acc")); err == nil {
		t.Fatal("verifier built for a program below the dynamic module's minimum size")
	}
}
