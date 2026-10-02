package recursion

import (
	"fmt"
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/trace"
)

// proveP2AIR builds a program made of the Poseidon2 AIR alone, fills it
// from random inputs (row 0 is left as zkc padding), applies tamper, and
// proves and verifies it.
func proveP2AIR(t *testing.T, tamper func(tr trace.Trace)) error {
	t.Helper()
	const n = 8
	const module = "p2_perm"
	inputs, outputs := make([]string, P2Width), make([]string, P2Width)
	for i := range inputs {
		inputs[i] = fmt.Sprintf("%s.s%d", module, i)
		outputs[i] = fmt.Sprintf("%s.r%d", module, i)
	}
	b := board.NewBuilder()
	m := board.NewModule(module)
	m.N = n
	b.AddModule(m)
	if err := (poseidon2AIR{}).Define(&b, module, inputs, outputs); err != nil {
		t.Fatal(err)
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}

	rng := rand.New(rand.NewPCG(9, 10))
	perm := hash.NewPoseidon2SpongeHasher().Perm
	tr := trace.New()
	in := make([][]koalabear.Element, P2Width)
	out := make([][]koalabear.Element, P2Width)
	for i := range in {
		in[i], out[i] = make([]koalabear.Element, n), make([]koalabear.Element, n)
	}
	for row := 1; row < n; row++ {
		state := make([]koalabear.Element, P2Width)
		for i := range state {
			state[i].SetUint64(rng.Uint64())
			in[i][row] = state[i]
		}
		if err := perm.Permutation(state); err != nil {
			t.Fatal(err)
		}
		for i := range state {
			out[i][row] = state[i]
		}
	}
	for i := range in {
		tr.SetBase(inputs[i], in[i])
		tr.SetBase(outputs[i], out[i])
	}
	if err := (poseidon2AIR{}).Fill(tr, module, inputs, outputs); err != nil {
		t.Fatal(err)
	}
	if tamper != nil {
		tamper(tr)
	}

	pk, vk, err := loom.Setup(tr, pg)
	if err != nil {
		return err
	}
	st := loom.Statement{Program: pg, VerificationKey: vk, PublicInputs: public.Inputs{}}
	prf, err := loom.Prove(st, loom.Witness{Trace: tr, ProvingKey: pk})
	if err != nil {
		return err
	}
	return loom.Verify(st, prf)
}

func TestPoseidon2AIR(t *testing.T) {
	if err := proveP2AIR(t, nil); err != nil {
		t.Fatalf("valid trace rejected: %v", err)
	}
	cases := map[string]func(tr trace.Trace){
		"output":        func(tr trace.Trace) { tr.Base["p2_perm.r7"][3].SetUint64(1) },
		"full round":    func(tr trace.Trace) { tr.Base["p2_perm.p2_post1_12"][5].SetUint64(2) },
		"partial sbox":  func(tr trace.Trace) { tr.Base["p2_perm.p2_sbox10"][2].SetUint64(3) },
		"padding row 0": func(tr trace.Trace) { tr.Base["p2_perm.r0"][0].SetZero() },
	}
	for name, tamper := range cases {
		t.Run(name, func(t *testing.T) {
			if err := proveP2AIR(t, tamper); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}
