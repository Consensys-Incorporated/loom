package recursion

import (
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/trace"
)

// builder is a Machine together with the inputs of one execution, so that a
// test can build a program and its inputs side by side.
type builder struct {
	Machine
	in []Cell
}

// input allocates an input cell of value v.
func (b *builder) input(v Cell) int {
	b.in = append(b.in, v)
	return b.Input()
}

// inputStream allocates the input stream of xs.
func (b *builder) inputStream(xs []koalabear.Element) []int {
	b.in = append(b.in, PackElements(xs)...)
	return b.InputStream(len(xs))
}

// run compiles the program and executes it on the builder's inputs.
func (b *builder) run(t *testing.T) (*Program, *Run) {
	t.Helper()
	p, err := b.Compile()
	if err != nil {
		t.Fatal(err)
	}
	r, err := p.Execute(b.in)
	if err != nil {
		t.Fatal(err)
	}
	return p, r
}

// keys runs loom's setup on the program's setup columns.
func keys(t *testing.T, p *Program) (setup.ProvingKey, setup.VerificationKey) {
	t.Helper()
	pk, vk, err := loom.Setup(p.Setup, p.Loom)
	if err != nil {
		t.Fatal(err)
	}
	return pk, vk
}

// proveWith proves and verifies an execution under given keys.
func proveWith(p *Program, pk setup.ProvingKey, vk setup.VerificationKey, r *Run) error {
	st := loom.Statement{Program: p.Loom, VerificationKey: vk, PublicInputs: public.Inputs{}}
	prf, err := loom.Prove(st, loom.Witness{Trace: r.Trace, ProvingKey: pk})
	if err != nil {
		return err
	}
	return loom.Verify(st, prf)
}

// prove runs setup, then proves and verifies an execution.
func prove(t *testing.T, p *Program, r *Run) error {
	t.Helper()
	pk, vk := keys(t, p)
	return proveWith(p, pk, vk, r)
}

// compileAndProve compiles and executes b, applies tamper to the setup and
// witness columns (if any), and proves.
func compileAndProve(t *testing.T, b *builder, tamper func(setup, witness trace.Trace)) error {
	t.Helper()
	p, r := b.run(t)
	if tamper != nil {
		tamper(p.Setup, r.Trace)
	}
	return prove(t, p, r)
}

// inputValue returns the value given to the input cell at addr.
func (b *builder) inputValue(addr int) Cell {
	for i, a := range b.inputs {
		if a == addr {
			return b.in[i]
		}
	}
	panic(fmt.Sprintf("cell %d is not an input", addr))
}
