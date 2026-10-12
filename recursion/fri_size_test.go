package recursion

import (
	"slices"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/internal/fri"
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

// TestVerifierDynamicSizes: one complete verifier, built for acc of size 8
// with acc dynamic, verifies proofs with acc of sizes 8 to 1024 — the trees'
// order changes (acc crosses range, ties big at 128), and from 256 acc is the
// largest module: FRI's first round and its levels' order move. At size 256,
// tampered FRI openings, paths, final polynomial and a lying size are
// rejected.
func TestVerifierDynamicSizes(t *testing.T) {
	program := accProgram(t, 16, 128)
	ref := accProof(t, program, 8, 3)
	v, err := NewVerifier(ref.program, ref.vk, ShapeOf(ref.prf, ref.pi), WithDynamicModules("acc"))
	if err != nil {
		t.Fatal(err)
	}
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	run := func(ip innerProof, n int) error {
		in, err := v.Inputs(ip.prf, ip.pi, ModuleSizes{"acc": n})
		if err != nil {
			return err
		}
		r, err := p.Execute(in)
		if err != nil {
			return err
		}
		return prove(t, p, r)
	}
	for _, n := range []int{8, 16, 64, 128, 256, 1024} {
		if err := run(accProof(t, program, n, 5), n); err != nil {
			t.Fatalf("size %d: valid proof rejected: %v", n, err)
		}
	}

	ip := accProof(t, program, 256, 5)
	tampered := func(f func(fp *fri.Proof)) innerProof {
		c := ip
		fp := ip.prf.Opening.FRIProof
		fp.FRIQueries = slices.Clone(fp.FRIQueries)
		fp.FRIQueries[1].Layers = slices.Clone(fp.FRIQueries[1].Layers)
		fp.FinalPolyExt = slices.Clone(fp.FinalPolyExt)
		f(&fp)
		c.prf.Opening.FRIProof = fp
		return c
	}
	var one ext.E6
	one.SetOne()
	for name, c := range map[string]innerProof{
		"layer value": tampered(func(fp *fri.Proof) {
			l := &fp.FRIQueries[1].Layers[3]
			l.LeafQExt.Add(&l.LeafQExt, &one)
		}),
		"layer path": tampered(func(fp *fri.Proof) {
			l := &fp.FRIQueries[1].Layers[2]
			l.Path.Siblings = slices.Clone(l.Path.Siblings)
			l.Path.Siblings[0][0].SetUint64(9)
		}),
		"levels tree path": tampered(func(fp *fri.Proof) {
			l := &fp.FRIQueries[1].Layers[0]
			l.Path.Siblings = slices.Clone(l.Path.Siblings)
			l.Path.Siblings[1][3].SetUint64(9)
		}),
		"final polynomial": tampered(func(fp *fri.Proof) {
			fp.FinalPolyExt[0].Add(&fp.FinalPolyExt[0], &one)
		}),
	} {
		if err := run(c, 256); err == nil {
			t.Fatalf("%s: tampered proof accepted", name)
		}
	}
	if err := run(ip, 1024); err == nil {
		t.Fatal("proof accepted under a lying size")
	}
}
