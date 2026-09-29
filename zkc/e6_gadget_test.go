package zkc

import (
	"fmt"
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/trace"
)

func proveE6Gadget(t *testing.T, tamper func(tr trace.Trace)) error {
	t.Helper()
	const n = 8
	const module = "e6_mul"
	inputs, outputs := make([]string, 12), make([]string, 6)
	for i := range inputs {
		inputs[i] = fmt.Sprintf("%s.x%d", module, i)
	}
	for i := range outputs {
		outputs[i] = fmt.Sprintf("%s.z%d", module, i)
	}
	b := board.NewBuilder()
	m := board.NewModule(module)
	m.N = n
	b.AddModule(m)
	if err := (E6MulGadget{}).Define(&b, module, inputs, outputs); err != nil {
		t.Fatal(err)
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}
	rng := rand.New(rand.NewPCG(11, 12))
	tr := trace.New()
	cols := make([][]koalabear.Element, 18)
	for i := range cols {
		cols[i] = make([]koalabear.Element, n)
	}
	for row := 1; row < n; row++ { // row 0 is all-zero padding
		x, y := randE6(rng), randE6(rng)
		var z ext.E6
		z.Mul(&x, &y)
		for i, v := range [][]koalabear.Element{elems6(x), elems6(y), elems6(z)} {
			for j := range v {
				cols[6*i+j][row] = v[j]
			}
		}
	}
	for i, name := range append(append([]string(nil), inputs...), outputs...) {
		tr.SetBase(name, cols[i])
	}
	if err := (E6MulGadget{}).Fill(tr, module, inputs, outputs); err != nil {
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

func elems6(x ext.E6) []koalabear.Element {
	return []koalabear.Element{x.B0.A0, x.B0.A1, x.B1.A0, x.B1.A1, x.B2.A0, x.B2.A1}
}

func TestE6MulGadget(t *testing.T) {
	if err := proveE6Gadget(t, nil); err != nil {
		t.Fatalf("valid trace rejected: %v", err)
	}
	for name, tamper := range map[string]func(tr trace.Trace){
		"output": func(tr trace.Trace) { tr.Base["e6_mul.z4"][3].SetUint64(1) },
		"input":  func(tr trace.Trace) { tr.Base["e6_mul.x9"][5].SetUint64(2) },
	} {
		t.Run(name, func(t *testing.T) {
			if err := proveE6Gadget(t, tamper); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}
