package fibonacci

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/verifier"
)

func fiboPublicInputs(a0, b0 koalabear.Element) public.Inputs {
	baseInput := func(module string, idx int, value koalabear.Element) public.Input {
		var entry public.Entry
		entry.Idx = idx
		entry.SetBase(value)
		return public.Input{Module: module, Entries: []public.Entry{entry}}
	}

	return public.Inputs{
		"fibonacci.a0": baseInput("fibonacci", 0, a0),
		"fibonacci.b0": baseInput("fibonacci", 0, b0),
	}
}

func TestVerifierFibo(t *testing.T) {

	// build the modules
	builder := board.NewBuilder()

	rangeModule := board.NewModule("range")

	N := 4
	rangeModule.N = 2 * N

	fibonacciModule := PrepareFibonacciModule(N)
	fibonacciModule.AssertEqualAt(expr.Col("A"), expr.PublicInput("fibonacci.a0"), 0)
	fibonacciModule.AssertEqualAt(expr.Col("B"), expr.PublicInput("fibonacci.b0"), 0)
	builder.AddModule(fibonacciModule)
	builder.AddModule(rangeModule)

	T := board.Column{
		Module: "range",
		In:     expr.Col("Lookup"),
	}
	columnsFibonacci := []string{"A", "B", "C"}
	for _, c := range columnsFibonacci {
		S := board.Column{
			Module: "fibonacci",
			In:     expr.Col(c),
		}
		err := arguments.Lookup(&builder, S, T)
		if err != nil {
			t.Fatal(err)
		}
	}

	program, err := board.Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}

	// load the traces
	var a, b koalabear.Element
	b.SetOne()
	traceFrob := prover.TraceFibonacci(N, a, b)
	traceRange := prover.TraceRange(N)
	tr := prover.MergeTrace(traceFrob, traceRange)

	publicInputs := fiboPublicInputs(a, b)

	proof, err := prover.Prove(tr, setup.ProvingKey{}, publicInputs, program)
	if err != nil {
		t.Fatal(err)
	}

	err = verifier.Verify(publicInputs, setup.VerificationKey{}, program, proof)
	if err != nil {
		t.Fatal(err)
	}

	if err := verifier.Verify(nil, setup.VerificationKey{}, program, proof); err == nil {
		t.Fatal("expected verifier to reject missing public inputs")
	}

	var wrongB koalabear.Element
	wrongB.SetUint64(2)
	if err := verifier.Verify(fiboPublicInputs(a, wrongB), setup.VerificationKey{}, program, proof); err == nil {
		t.Fatal("expected verifier to reject incorrect public input")
	}
}
