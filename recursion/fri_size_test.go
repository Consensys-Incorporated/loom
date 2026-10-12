package recursion

import (
	"slices"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
)

// friTranscriptCircuit builds the verifier up to FRI's queries: the sizes,
// the transcript and the PCS transcript.
func friTranscriptCircuit(t *testing.T, ip innerProof, opts ...VerifierOption) *Verifier {
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
	return v
}

// TestFRITranscriptDynamicSizes: one circuit, built for acc of size 8, derives
// loom's FRI challenges — the levels' γs, every fold challenge, every query —
// for proofs with acc of sizes 8, 128, 256 and 1024: big (128) is the largest
// module, then acc, so FRI's first round moves (15, 15, 14, 12) and with it
// the root each fold challenge binds (the zero digest, the levels root or a
// layer root).
func TestFRITranscriptDynamicSizes(t *testing.T) {
	program := accProgram(t, 16, 128)
	v := friTranscriptCircuit(t, accProof(t, program, 8, 3), WithDynamicModules("acc"))
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	for _, n := range []int{8, 128, 256, 1024} {
		ip := accProof(t, program, n, 5)
		in, err := v.Inputs(ip.prf, ip.pi, ModuleSizes{"acc": n})
		if err != nil {
			t.Fatalf("size %d: %v", n, err)
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
		if n == 256 {
			if err := prove(t, p, r); err != nil {
				t.Fatalf("size %d: valid FRI transcript rejected: %v", n, err)
			}
			// A lying hint: no level entered by the first round (b = 0, one
			// fewer): the round indicators would move the levels root later.
			first := MaxLogModuleSize - 8
			bad := slices.Clone(in)
			bad[v.hintInput(first)] = Cell{}
			r, err := p.Execute(bad)
			if err != nil {
				t.Fatalf("lying hint not executed: %v", err)
			}
			if err := prove(t, p, r); err == nil {
				t.Fatal("lying number of entered levels accepted")
			}

			// A nonzero root given for an empty round (round 3 < first): the
			// circuit binds the zero digest whatever the input, so the
			// challenges stay loom's — a prover cannot steer them with it.
			steer := slices.Clone(in)
			steer[v.friDyn.rootInputs[3]][2].SetUint64(77)
			r, err = p.Execute(steer)
			if err != nil {
				t.Fatal(err)
			}
			for name, cell := range v.Challenges {
				want, _ := fs.ComputeChallenge(name)
				if got := r.Value(cell); [8]koalabear.Element(got) != [8]koalabear.Element(want) {
					t.Fatalf("an empty round's root input changed challenge %s", name)
				}
			}
		}
	}
}
