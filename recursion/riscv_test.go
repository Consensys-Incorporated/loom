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
	"sort"
	"testing"
	"time"

	"github.com/LFDT-Lineth/zkc/pkg/zkc/vm"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	gocorset "github.com/consensys/loom/integration_test/go_corset"
	"github.com/consensys/loom/integration_test/zkc/riscv"
	"github.com/consensys/loom/integration_test/zkc/riscv/minimalelf"
	"github.com/consensys/loom/integration_test/zkc/riscv/predecoding"
)

// riscvProof proves, with loom, the zkc RISC-V interpreter running guest elf
// (one shard).
func riscvProof(t *testing.T, elf []byte) innerProof {
	t.Helper()
	binf, err := riscv.CompiledBinaryFile()
	if err != nil {
		t.Fatal(err)
	}
	inputs, err := predecoding.PrepareInputs(elf, nil)
	if err != nil {
		t.Fatal(err)
	}
	_, lazy, errs := binf.Trace(inputs, vm.DEFAULT_TRACE_CONFIG)
	if len(errs) > 0 {
		t.Fatal(errors.Join(errs...))
	}
	if n := lazy.Unwrap().Len(); n != 1 {
		t.Fatalf("%d shards, want 1", n)
	}
	shard, errs := lazy.Unwrap().Get(0)
	if len(errs) > 0 {
		t.Fatal(errors.Join(errs...))
	}

	airSchema := binf.AirConstraints()
	manifest, err := gocorset.NewZkcManifest(binf)
	if err != nil {
		t.Fatal(err)
	}
	builder := board.NewBuilder()
	bridge := gocorset.NewCorsetBridge(&builder, &airSchema)
	bridge.SetupModules()
	if err := manifest.ApplyToBridge(bridge); err != nil {
		t.Fatal(err)
	}
	gocorset.ScanConstraints(bridge)
	pg, err := board.Compile(bridge.Builder)
	if err != nil {
		t.Fatal(err)
	}
	tr, err := gocorset.ShardToLoom(shard.Unwrap(), &airSchema)
	if err != nil {
		t.Fatal(err)
	}
	gocorset.SetSize(&pg, tr)
	pi, err := manifest.PublicInputsOf(inputs, pg)
	if err != nil {
		t.Fatal(err)
	}
	pk, vk, err := loom.Setup(tr, pg)
	if err != nil {
		t.Fatal(err)
	}
	st := loom.Statement{Program: pg, VerificationKey: vk, PublicInputs: pi}
	prf, err := loom.Prove(st, loom.Witness{Trace: tr, ProvingKey: pk})
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
	ip := riscvProof(t, elf)
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
	build := time.Since(t0)
	in, err := v.Inputs(ip.prf, ip.pi, SizesOf(ip.program))
	if err != nil {
		t.Fatal(err)
	}
	t0 = time.Now()
	r, err := p.Execute(in)
	if err != nil {
		t.Fatal(err)
	}
	exec := time.Since(t0)
	t.Logf("verifier: %d inputs, leaf %d elements/query; build %v, execute %v",
		p.NumInputs(), LeafCostOf(ip.program).Elements, build.Round(time.Millisecond), exec.Round(time.Millisecond))

	rows := map[string]int{}
	for _, c := range p.m.chips() {
		rows[c.name()] = c.rows()
	}
	sort.Slice(p.heights, func(i, j int) bool { return rows[p.heights[i].module] > rows[p.heights[j].module] })
	total := 0
	for _, h := range p.heights {
		n := p.Loom.Modules[h.module].N
		total += n
		t.Logf("  %-8s %9d rows, N = 2^%d", h.module, rows[h.module], log2Int(n))
		if n > 1<<MaxLogModuleSize {
			t.Errorf("module %s: N = %d exceeds 2^%d", h.module, n, MaxLogModuleSize)
		}
	}
	t.Logf("verifier: %d modules, %d padded rows", len(p.heights), total)

	t0 = time.Now()
	if err := prove(t, p, r); err != nil {
		t.Fatalf("verifier execution rejected: %v", err)
	}
	t.Logf("verifier execution: setup+prove+verify in %v", time.Since(t0).Round(time.Millisecond))
}

func log2Int(n int) int {
	l := 0
	for 1<<l < n {
		l++
	}
	return l
}
