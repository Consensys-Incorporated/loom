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

package recursion

import (
	"errors"
	"maps"
	"reflect"
	"slices"
	"sort"
	"testing"
	"time"

	"github.com/LFDT-Lineth/zkc/pkg/ir/air"
	zkc_kb "github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/vm"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	gocorset "github.com/consensys/loom/integration_test/go_corset"
	"github.com/consensys/loom/integration_test/zkc/riscv"
	"github.com/consensys/loom/integration_test/zkc/riscv/minimalelf"
	"github.com/consensys/loom/integration_test/zkc/riscv/predecoding"
	"github.com/consensys/loom/public"
)

// riscvSystem is the zkc RISC-V interpreter's loom program, compiled once:
// every proof is of a copy of it, with its trace's module sizes, so that all
// are proofs of the same program (whose compilation names some columns at
// random).
type riscvSystem struct {
	binf      *gocorset.BinaryFile
	airSchema air.Schema[zkc_kb.Element]
	manifest  *gocorset.FrontendManifest // nil: no public inputs
	pg        board.Program
	cfg       vm.TraceConfig
}

// newRiscvSystem compiles the interpreter, binding its input memories to row
// public inputs when publicInputs.
func newRiscvSystem(t *testing.T, publicInputs bool) *riscvSystem {
	t.Helper()
	binf, err := riscv.CompiledBinaryFile()
	if err != nil {
		t.Fatal(err)
	}
	s := &riscvSystem{binf: binf, airSchema: binf.AirConstraints(), cfg: vm.DEFAULT_TRACE_CONFIG}
	builder := board.NewBuilder()
	bridge := gocorset.NewCorsetBridge(&builder, &s.airSchema)
	bridge.SetupModules()
	if publicInputs {
		if s.manifest, err = gocorset.NewZkcManifest(binf); err != nil {
			t.Fatal(err)
		}
		if err := s.manifest.ApplyToBridge(bridge); err != nil {
			t.Fatal(err)
		}
	}
	gocorset.ScanConstraints(bridge)
	if s.pg, err = board.Compile(bridge.Builder); err != nil {
		t.Fatal(err)
	}
	return s
}

// dynamicModules returns the modules whose size depends on the guest: all
// but the static tables (setup columns, of fixed size).
func (s *riscvSystem) dynamicModules() []string {
	var res []string
	for it := s.airSchema.Modules(); it.HasNext(); {
		m := it.Next()
		if _, ok := s.pg.Modules[m.Name()]; ok && !m.IsStatic() {
			res = append(res, m.Name())
		}
	}
	return res
}

// padForDynamic makes zkc pad every module to at least the smallest size a
// dynamic module of the program may have (minLogSize), the largest over the
// modules.
func (s *riscvSystem) padForDynamic() {
	minLog := 0
	for _, m := range s.pg.Modules {
		minLog = max(minLog, minLogSize(m))
	}
	s.cfg = vm.DEFAULT_TRACE_CONFIG.WithPadding(gocorset.PaddingAtLeast(1 << minLog))
}

// prove proves, with loom, the interpreter running guest elf (one shard), with
// the given prover options (e.g. prover.WithNumFriQueries).
func (s *riscvSystem) prove(t *testing.T, elf []byte, opts ...loom.ProverOption) innerProof {
	t.Helper()
	inputs, err := predecoding.PrepareInputs(elf, nil)
	if err != nil {
		t.Fatal(err)
	}
	_, lazy, errs := s.binf.Trace(inputs, s.cfg)
	if len(errs) > 0 {
		t.Fatal(errors.Join(errs...))
	}
	if failures, errs := s.binf.Check(s.cfg, lazy.Unwrap()); len(failures) > 0 || len(errs) > 0 {
		t.Fatalf("zkc check: %v %v", failures, errs)
	}
	if n := lazy.Unwrap().Len(); n != 1 {
		t.Fatalf("%d shards, want 1", n)
	}
	shard, errs := lazy.Unwrap().Get(0)
	if len(errs) > 0 {
		t.Fatal(errors.Join(errs...))
	}
	tr, err := gocorset.ShardToLoom(shard.Unwrap(), &s.airSchema)
	if err != nil {
		t.Fatal(err)
	}
	pg := s.pg
	pg.Modules = maps.Clone(s.pg.Modules)
	gocorset.SetSize(&pg, tr)
	pi := public.Inputs{}
	if s.manifest != nil {
		if pi, err = s.manifest.PublicInputsOf(inputs, pg); err != nil {
			t.Fatal(err)
		}
	}
	pk, vk, err := loom.Setup(tr, pg)
	if err != nil {
		t.Fatal(err)
	}
	st := loom.Statement{Program: pg, VerificationKey: vk, PublicInputs: pi}
	prf, err := loom.Prove(st, loom.Witness{Trace: tr, ProvingKey: pk}, opts...)
	if err != nil {
		t.Fatal(err)
	}
	return innerProof{program: pg, vk: vk, pi: pi, prf: prf}
}

// TestRiscvVerifierSize builds the recursive verifier of a RISC-V proof (the
// instruction-coverage guest, minimalelf.AllInOneElfProgram), executes and
// proves it, and logs its rows per chip. Every module must fit in one shard:
// N ≤ 2^MaxLogModuleSize.
func TestRiscvVerifierSize(t *testing.T) {
	if testing.Short() {
		t.Skip("proves a RISC-V guest, then its recursive verifier")
	}
	elf, _ := minimalelf.AllInOneElfProgram()
	t0 := time.Now()
	ip := newRiscvSystem(t, true).prove(t, elf)
	t.Logf("inner proof: %d modules, in %v", len(ip.program.Modules), time.Since(t0).Round(time.Millisecond))

	t0 = time.Now()
	v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi))
	if err != nil {
		t.Fatal(err)
	}
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("verifier built in %v, leaf %d elements/query", time.Since(t0).Round(time.Millisecond), LeafCostOf(ip.program).Elements)
	in, err := v.Inputs(ip.prf, ip.pi, SizesOf(ip.program))
	if err != nil {
		t.Fatal(err)
	}
	runVerifierCircuit(t, p, in)
}

// TestRiscvTwoProofsVerifier builds, in one circuit, the size-oblivious
// verifiers of two RISC-V proofs of the same program, for two guests whose
// module sizes differ (the instruction-coverage guest and a Fibonacci loop):
// every module of the interpreter but its static tables is dynamic. The
// proofs are verified independently (each with its own bus check), without
// public inputs (the guests' input memories are not bound to the statement).
// It executes and proves the circuit, and logs its rows per chip.
func TestRiscvTwoProofsVerifier(t *testing.T) {
	if testing.Short() {
		t.Skip("proves two RISC-V guests, then their recursive verifiers")
	}
	sys := newRiscvSystem(t, false)
	sys.padForDynamic()
	t0 := time.Now()
	ips := sys.proveTwoGuests(t)
	t.Logf("inner proofs in %v", time.Since(t0).Round(time.Millisecond))
	p, in := buildTwoProofsVerifier(t, sys, ips)
	runVerifierCircuit(t, p, in)
}

// proveTwoGuests proves the instruction-coverage guest and a Fibonacci(200)
// loop, whose module sizes differ, with the given prover options.
func (s *riscvSystem) proveTwoGuests(t *testing.T, opts ...loom.ProverOption) []innerProof {
	t.Helper()
	allInOne, _ := minimalelf.AllInOneElfProgram()
	fib, _ := minimalelf.FibonacciELF(200)
	return []innerProof{s.prove(t, allInOne, opts...), s.prove(t, fib, opts...)}
}

// buildTwoProofsVerifier builds, in one circuit, the size-oblivious verifiers
// of two proofs of sys's program (see TestRiscvTwoProofsVerifier), and returns
// the compiled circuit with its inputs.
func buildTwoProofsVerifier(t *testing.T, sys *riscvSystem, ips []innerProof) (*Program, []Cell) {
	t.Helper()
	if !slices.Equal(ips[0].vk.Roots, ips[1].vk.Roots) {
		t.Fatal("the two proofs have different verification keys")
	}
	differ := 0
	for name, m := range ips[0].program.Modules {
		if ips[1].program.Modules[name].N != m.N {
			differ++
		}
	}
	dynamic := sys.dynamicModules()
	t.Logf("%d modules, %d dynamic, %d of different sizes in the two proofs", len(ips[0].program.Modules), len(dynamic), differ)

	t0 := time.Now()
	m := &Machine{}
	var vs []*Verifier
	for _, ip := range ips {
		// the circuit is of the program and shape, the same for both proofs
		v, err := NewVerifier(ips[0].program, ips[0].vk, ShapeOf(ips[0].prf, ips[0].pi), WithMachine(m), WithDynamicModules(dynamic...))
		if err != nil {
			t.Fatal(err)
		}
		if got := ShapeOf(ip.prf, ip.pi); !reflect.DeepEqual(got, ShapeOf(ips[0].prf, ips[0].pi)) {
			t.Fatal("the two proofs have different shapes")
		}
		vs = append(vs, v)
	}
	p, err := m.Compile()
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("verifiers built in %v", time.Since(t0).Round(time.Millisecond))
	var in []Cell
	for i, v := range vs {
		vin, err := v.Inputs(ips[i].prf, ips[i].pi, SizesOf(ips[i].program))
		if err != nil {
			t.Fatal(err)
		}
		in = append(in, vin...)
	}
	return p, in
}

// runVerifierCircuit executes a verifier circuit on its inputs, logs its rows
// per chip, checks that every module fits in one shard (N ≤
// 2^MaxLogModuleSize), and proves the execution.
func runVerifierCircuit(t *testing.T, p *Program, in []Cell) {
	t.Helper()
	r, chips := executeVerifierCircuit(t, p, in)
	total := 0
	for _, c := range chips {
		total += c.n
		t.Logf("  %-8s %9d rows, N = 2^%d", c.module, c.rows, log2Int(c.n))
		if c.n > 1<<MaxLogModuleSize {
			t.Errorf("module %s: N = %d exceeds 2^%d", c.module, c.n, MaxLogModuleSize)
		}
	}
	t.Logf("verifier: %d modules, %d padded rows", len(chips), total)

	t0 := time.Now()
	if err := prove(t, p, r); err != nil {
		t.Fatalf("verifier execution rejected: %v", err)
	}
	t.Logf("verifier execution: setup+prove+verify in %v", time.Since(t0).Round(time.Millisecond))
}

// chipRows is the size of one chip of an executed verifier circuit: its rows,
// and N, the size of its loom module (the rows padded to a power of two).
type chipRows struct {
	module  string
	rows, n int
}

// executeVerifierCircuit executes a verifier circuit on its inputs, and returns
// the run with the rows of every chip that has some, by decreasing rows.
func executeVerifierCircuit(t *testing.T, p *Program, in []Cell) (*Run, []chipRows) {
	t.Helper()
	t0 := time.Now()
	r, err := p.Execute(in)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("verifier: %d inputs, executed in %v", p.NumInputs(), time.Since(t0).Round(time.Millisecond))

	rows := map[string]int{}
	for _, c := range p.m.chips() {
		rows[c.name()] = c.rows()
	}
	chips := make([]chipRows, len(p.heights))
	for i, h := range p.heights {
		chips[i] = chipRows{module: h.module, rows: rows[h.module], n: p.Loom.Modules[h.module].N}
	}
	sort.SliceStable(chips, func(i, j int) bool { return chips[i].rows > chips[j].rows })
	return r, chips
}

func log2Int(n int) int {
	l := 0
	for 1<<l < n {
		l++
	}
	return l
}
