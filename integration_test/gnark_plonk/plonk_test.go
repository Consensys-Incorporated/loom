// Copyright Consensys Software Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
// the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0

package gnarkplonk

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/integration_test/fibonacci"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/trace"
	"github.com/consensys/loom/verifier"
	"github.com/consensys/loom/viz"
)

func TestVerifierPlonk(t *testing.T) {

	builder := board.NewBuilder()

	// without setup
	{
		// fetch the plonk trace
		N := 16
		tr, sigma, size, err := GetIthPlonkTrace(N, 0)
		if err != nil {
			t.Fatal(err)
		}

		// build the plonk module
		plonkModule := PrepareIthPlonk(size, 0)
		builder.AddModule(plonkModule)

		lro := []expr.Expr{expr.Col(Ith(ID_L, 0)), expr.Col(Ith(ID_R, 0)), expr.Col(Ith(ID_O, 0))}
		sigmaGen := board.NewPermutationGen(sigma, Ith("plonk.S", 0))
		err = arguments.CopyConstraint(&builder, Ith("plonk", 0), lro, sigmaGen)
		if err != nil {
			t.Fatal(err)
		}
		program, err := board.Compile(&builder)
		if err != nil {
			t.Fatal(err)
		}

		stmt := loom.Statement{Program: program}
		witness := loom.Witness{Trace: tr}

		proof, err := loom.Prove(stmt, witness)
		if err != nil {
			t.Fatal(err)
		}

		err = loom.Verify(stmt, proof)
		if err != nil {
			t.Fatal(err)
		}
	}

	// with setup
	{
		// fetch the plonk trace
		N := 16
		tr, sigma, size, err := GetIthPlonkTrace(N, 0)
		if err != nil {
			t.Fatal(err)
		}

		// build the plonk module
		plonkModule := PrepareIthPlonkWithSetup(size, 0)
		builder.AddModule(plonkModule)

		lro := []expr.Expr{expr.Col(Ith(ID_L, 0)), expr.Col(Ith(ID_R, 0)), expr.Col(Ith(ID_O, 0))}
		sigmaGen := board.NewPermutationGen(sigma, Ith("plonk.S", 0))
		err = arguments.CopyConstraint(&builder, Ith("plonk", 0), lro, sigmaGen)
		if err != nil {
			t.Fatal(err)
		}

		program, err := board.Compile(&builder)
		if err != nil {
			t.Fatal(err)
		}

		pk, vk, err := loom.Setup(tr, program)
		if err != nil {
			t.Fatal(err)
		}
		stmt := loom.Statement{Program: program, VerificationKey: vk}
		witness := loom.Witness{Trace: tr, ProvingKey: pk}
		proof, err := loom.Prove(stmt, witness)
		if err != nil {
			t.Fatal(err)
		}

		err = loom.Verify(stmt, proof)
		if err != nil {
			t.Fatal(err)
		}
	}
}

func TestFiboPlonk(t *testing.T) {

	// fetch the plonk trace
	NPlonk := 16
	tr, sigma, size, err := GetIthPlonkTrace(NPlonk, 0)
	if err != nil {
		t.Fatal(err)
	}

	// build the modules
	plonkModule := PrepareIthPlonk(size, 0)
	NFibo := 4
	fibonacciModule := fibonacci.PrepareFibonacciModule(NFibo)
	rangeModule := board.NewModule("range")
	rangeModule.N = 2 * NFibo

	// build the arguments
	builder := board.NewBuilder()
	builder.AddModule(plonkModule)
	builder.AddModule(fibonacciModule)
	builder.AddModule(rangeModule)

	// 1 - lookup of fibo's columns
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

	// 2 - plonk copy constraint
	lro := []expr.Expr{expr.Col(Ith(ID_L, 0)), expr.Col(Ith(ID_R, 0)), expr.Col(Ith(ID_O, 0))}
	sigmaGen := board.NewPermutationGen(sigma, Ith("plonk.S", 0))
	err = arguments.CopyConstraint(&builder, Ith("plonk", 0), lro, sigmaGen)
	if err != nil {
		t.Fatal(err)
	}

	// compile
	program, err := board.Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}

	// load traces for range and TestFibo
	var a, b koalabear.Element
	b.SetOne()
	traceFrob := prover.TraceFibonacci(NFibo, a, b)
	traceRange := prover.TraceRange(NFibo)
	fullTrace := prover.MergeTrace(traceFrob, traceRange, tr)

	// prover, verify
	proof, err := prover.Prove(fullTrace, setup.ProvingKey{}, nil, program)
	if err != nil {
		t.Fatal(err)
	}

	viz.WriteRawTraceToCSV("trace.csv", fullTrace)

	err = verifier.Verify(nil, setup.VerificationKey{}, program, proof)
	if err != nil {
		t.Fatal(err)
	}

}

func TestBigGraph(t *testing.T) {

	ns := []int{8, 8, 8, 8, 8}
	builder := board.NewBuilder()
	traces := make([]trace.Trace, len(ns))
	for i, n := range ns {
		tr, sigma, size, err := GetIthPlonkTrace(n, i)
		if err != nil {
			t.Fatal(err)
		}
		traces[i] = tr
		builder.AddModule(PrepareIthPlonk(size, i))

		lro := []expr.Expr{expr.Col(Ith(ID_L, i)), expr.Col(Ith(ID_R, i)), expr.Col(Ith(ID_O, i))}
		sigmaGen := board.NewPermutationGen(sigma, Ith("plonk.S", i))
		if err := arguments.CopyConstraint(&builder, Ith("plonk", i), lro, sigmaGen); err != nil {
			t.Fatal(err)
		}
	}

	// fullTrace := prover.MergeTrace(traces[0], traces[1:]...)
	_, err := board.Compile(&builder)
	if err != nil {
		t.Fatal(err)
	}
}

//======================== Benchmarks ========================

func BenchmarkProver(b *testing.B) {

	sameSize := make([]int, 50)
	for i := range sameSize {
		sameSize[i] = 1 << 10
	}

	varying := make([]int, 0, 50)
	for s := 8; s <= 12; s++ {
		for k := 0; k < 10; k++ {
			varying = append(varying, 1<<s)
		}
	}

	b.Run("SameSize/N=1024/SkipFRI", func(b *testing.B) { benchProver(b, sameSize, true) })
	b.Run("SameSize/N=1024", func(b *testing.B) { benchProver(b, sameSize, false) })
	b.Run("VaryingSizes/SkipFRI", func(b *testing.B) { benchProver(b, varying, true) })
	b.Run("VaryingSizes", func(b *testing.B) { benchProver(b, varying, false) })
}

func benchProver(b *testing.B, ns []int, skipFRI bool) {

	builder := board.NewBuilder()
	traces := make([]trace.Trace, len(ns))
	for i, n := range ns {
		tr, sigma, size, err := GetIthPlonkTrace(n, i)
		if err != nil {
			b.Fatal(err)
		}
		traces[i] = tr
		builder.AddModule(PrepareIthPlonk(size, i))

		lro := []expr.Expr{expr.Col(Ith(ID_L, i)), expr.Col(Ith(ID_R, i)), expr.Col(Ith(ID_O, i))}
		sigmaGen := board.NewPermutationGen(sigma, Ith("plonk.S", i))
		if err := arguments.CopyConstraint(&builder, Ith("plonk", i), lro, sigmaGen); err != nil {
			b.Fatal(err)
		}
	}

	fullTrace := prover.MergeTrace(traces[0], traces[1:]...)
	program, err := board.Compile(&builder)
	if err != nil {
		b.Fatal(err)
	}

	var opts []prover.Option
	if skipFRI {
		opts = append(opts, prover.SkipFRI())
	}

	b.ResetTimer()
	for b.Loop() {
		// prover.Prove mutates the input trace (adds challenge / GP /
		// multiplicity columns), so each iteration needs a fresh trace. The
		// column slices themselves are not mutated and can be shared.
		b.StopTimer()
		fresh := trace.New(len(fullTrace.Base))
		for k, v := range fullTrace.Base {
			fresh.SetBase(k, v)
		}
		for k, v := range fullTrace.Ext {
			fresh.SetExt(k, v)
		}
		b.StartTimer()
		if _, err := prover.Prove(fresh, setup.ProvingKey{}, nil, program, opts...); err != nil {
			b.Fatal(err)
		}
	}
}

func BenchmarkVerifier(b *testing.B) {

	sameSize := make([]int, 50)
	for i := range sameSize {
		sameSize[i] = 1 << 10
	}

	varying := make([]int, 0, 50)
	for s := 8; s <= 12; s++ {
		for k := 0; k < 10; k++ {
			varying = append(varying, 1<<s)
		}
	}

	b.Run("SameSize/N=1024/SkipFRI", func(b *testing.B) { benchVerifier(b, sameSize, true) })
	b.Run("SameSize/N=1024", func(b *testing.B) { benchVerifier(b, sameSize, false) })
	b.Run("VaryingSizes/SkipFRI", func(b *testing.B) { benchVerifier(b, varying, true) })
	b.Run("VaryingSizes", func(b *testing.B) { benchVerifier(b, varying, false) })
}

func benchVerifier(b *testing.B, ns []int, skipFRI bool) {

	builder := board.NewBuilder()
	traces := make([]trace.Trace, len(ns))
	for i, n := range ns {
		tr, sigma, size, err := GetIthPlonkTrace(n, i)
		if err != nil {
			b.Fatal(err)
		}
		traces[i] = tr
		builder.AddModule(PrepareIthPlonk(size, i))

		lro := []expr.Expr{expr.Col(Ith(ID_L, i)), expr.Col(Ith(ID_R, i)), expr.Col(Ith(ID_O, i))}
		sigmaGen := board.NewPermutationGen(sigma, Ith("plonk.S", i))
		if err := arguments.CopyConstraint(&builder, Ith("plonk", i), lro, sigmaGen); err != nil {
			b.Fatal(err)
		}
	}

	fullTrace := prover.MergeTrace(traces[0], traces[1:]...)
	program, err := board.Compile(&builder)
	if err != nil {
		b.Fatal(err)
	}

	var optsProver []prover.Option
	if skipFRI {
		optsProver = append(optsProver, prover.SkipFRI())
	}
	proof, err := prover.Prove(fullTrace, setup.ProvingKey{}, nil, program, optsProver...)
	if err != nil {
		b.Fatal(err)
	}

	var optsVerifier []verifier.Option
	if skipFRI {
		optsVerifier = append(optsVerifier, verifier.SkipFRI())
	}

	b.ResetTimer()
	for b.Loop() {
		b.StartTimer()
		err := verifier.Verify(nil, setup.VerificationKey{}, program, proof, optsVerifier...)
		if err != nil {
			b.Fatal(err)
		}
	}
}
