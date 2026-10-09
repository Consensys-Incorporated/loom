package recursion

import (
	"maps"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/protocol"
	"github.com/consensys/loom/proof"
)

// sizesProgram is a program of four modules, sized only: the size binding and
// the size helpers read nothing else.
func sizesProgram() board.Program {
	return board.Program{Modules: map[string]board.CompiledModule{
		"a": {Name: "a", N: 8},
		"b": {Name: "b", N: 16},
		"c": {Name: "c", N: 4},
		"d": {Name: "d", N: 2},
	}}
}

// sizesCircuit builds, for sizesProgram with dynamic modules b and d, the size
// binding of an initial challenge and the cells of N, 1/N, ω_N and ω_N^−1
// of every module.
type sizesCircuit struct {
	v                        *Verifier
	challenge                int
	n, invN, omega, omegaInv map[string]int
}

func newSizesCircuit(t *testing.T) sizesCircuit {
	t.Helper()
	v := &Verifier{M: &Machine{}, program: sizesProgram()}
	if err := v.buildSizes(map[string]bool{"b": true, "d": true}); err != nil {
		t.Fatal(err)
	}
	v.tr = NewTranscript(v.M, "init")
	v.bindModuleSizes("init")
	c := sizesCircuit{v: v, challenge: v.tr.Compute("init"),
		n: map[string]int{}, invN: map[string]int{}, omega: map[string]int{}, omegaInv: map[string]int{}}
	for name := range v.program.Modules {
		c.n[name] = v.SizeN(name)
		c.invN[name] = v.SizeInvN(name)
		c.omega[name] = v.SizeOmega(name, 1)
		c.omegaInv[name] = v.SizeOmega(name, -1)
	}
	return c
}

// TestModuleSizesBinding: one circuit binds the sizes of its dynamic modules
// as loom's transcript does, at every size combination, and its size helpers
// hold the right constants.
func TestModuleSizesBinding(t *testing.T) {
	c := newSizesCircuit(t)
	p, err := c.v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	for i, sizes := range []ModuleSizes{
		{"b": 16, "d": 2}, // the program's
		{"b": 1, "d": 1 << MaxLogModuleSize},
		{"b": 1 << 5, "d": 4, "a": 8},
		{"b": 1 << MaxLogModuleSize, "d": 1 << 7},
	} {
		in, err := c.v.Inputs(proof.Proof{}, nil, sizes)
		if err != nil {
			t.Fatal(err)
		}
		r, err := p.Execute(in)
		if err != nil {
			t.Fatalf("sizes %v: %v", sizes, err)
		}

		// loom's transcript, for the program at these sizes.
		resized := board.Program{Modules: maps.Clone(c.v.program.Modules)}
		for name, n := range sizes {
			mod := resized.Modules[name]
			mod.N = n
			resized.Modules[name] = mod
		}
		h := hash.NewPoseidon2SpongeHasher()
		fs := fiatshamir.NewTranscript(&h, "init")
		if err := fs.Bind("init", protocol.ModuleSizesTranscript(resized)); err != nil {
			t.Fatal(err)
		}
		want, err := fs.ComputeChallenge("init")
		if err != nil {
			t.Fatal(err)
		}
		if got := r.Value(c.challenge); [8]koalabear.Element(want) != [8]koalabear.Element(got) {
			t.Fatalf("sizes %v: initial challenge differs from loom's", sizes)
		}

		for name, mod := range resized.Modules {
			g, err := koalabear.Generator(uint64(mod.N))
			if err != nil {
				t.Fatal(err)
			}
			var n, inv, gInv koalabear.Element
			n.SetUint64(uint64(mod.N))
			inv.Inverse(&n)
			gInv.Inverse(&g)
			for what, cw := range map[string]struct {
				cell int
				want koalabear.Element
			}{"N": {c.n[name], n}, "1/N": {c.invN[name], inv}, "ω": {c.omega[name], g}, "ω^-1": {c.omegaInv[name], gInv}} {
				if got := r.Value(cw.cell)[0]; !got.Equal(&cw.want) {
					t.Fatalf("sizes %v, module %s: %s = %s, want %s", sizes, name, what, got.String(), cw.want.String())
				}
			}
		}
		if i == 1 {
			if err := prove(t, p, r); err != nil {
				t.Fatalf("sizes %v: valid size circuit rejected: %v", sizes, err)
			}
		}
	}
}

// TestModuleSizesInputs: Inputs only accepts power-of-two sizes up to the
// maximum for the dynamic modules, and the program's sizes for the fixed ones.
func TestModuleSizesInputs(t *testing.T) {
	c := newSizesCircuit(t)
	for name, sizes := range map[string]ModuleSizes{
		"missing dynamic size": {"b": 16},
		"not a power of two":   {"b": 16, "d": 6},
		"zero":                 {"b": 0, "d": 2},
		"above the maximum":    {"b": 1 << (MaxLogModuleSize + 1), "d": 2},
		"fixed module resized": {"b": 16, "d": 2, "a": 16},
		"unknown module":       {"b": 16, "d": 2, "e": 4},
	} {
		if _, err := c.v.Inputs(proof.Proof{}, nil, sizes); err == nil {
			t.Fatalf("%s: sizes %v accepted", name, sizes)
		}
	}

	// A log size above the maximum, bypassing Inputs, reads past the
	// size tables: it does not execute.
	p, err := c.v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	in, err := c.v.Inputs(proof.Proof{}, nil, ModuleSizes{"b": 16, "d": 2})
	if err != nil {
		t.Fatal(err)
	}
	for i, mod := range c.v.sizeInputs {
		if mod == "d" {
			in[i] = ScalarCell(koalabear.NewElement(MaxLogModuleSize + 1))
		}
	}
	if _, err := p.Execute(in); err == nil {
		t.Fatal("log size 23 executed")
	}
}

// TestVerifierDynamicModule verifies, with one circuit whose fibonacci module
// is dynamic, a real proof at the program's size; the same proof under
// another claimed size is rejected (its transcript differs). Only the size
// binding is oblivious so far: the circuit's other parts still use the
// program's sizes.
func TestVerifierDynamicModule(t *testing.T) {
	ip := fiboProofs(t, [2]uint64{0, 1})[0]
	v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi), WithDynamicModules("fibonacci"))
	if err != nil {
		t.Fatal(err)
	}
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	run := func(n int) error {
		sizes := SizesOf(ip.program)
		sizes["fibonacci"] = n
		in, err := v.Inputs(ip.prf, ip.pi, sizes)
		if err != nil {
			t.Fatal(err)
		}
		r, err := p.Execute(in)
		if err != nil {
			return err
		}
		return prove(t, p, r)
	}
	n := ip.program.Modules["fibonacci"].N
	if err := run(n); err != nil {
		t.Fatalf("valid proof rejected: %v", err)
	}
	if err := run(2 * n); err == nil {
		t.Fatal("proof accepted under a lying size")
	}

	if _, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi), WithDynamicModules("nope")); err == nil {
		t.Fatal("unknown dynamic module accepted")
	}
}

// TestDynamicModuleWithSetupColumns: a module with setup columns cannot be
// dynamic, since the verification key commits to its setup columns at one
// size.
func TestDynamicModuleWithSetupColumns(t *testing.T) {
	pg := sizesProgram()
	pg.SetupColumns = []board.ColumnRef{{Name: "a.sel", Module: "a"}}
	v := &Verifier{M: &Machine{}, program: pg}
	if err := v.buildSizes(map[string]bool{"a": true}); err == nil {
		t.Fatal("module with setup columns made dynamic")
	}
	v = &Verifier{M: &Machine{}, program: pg}
	if err := v.buildSizes(map[string]bool{"b": true}); err != nil {
		t.Fatalf("module without setup columns: %v", err)
	}
}
