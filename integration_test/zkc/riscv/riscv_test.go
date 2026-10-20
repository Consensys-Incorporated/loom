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

package riscv_test

import (
	"bytes"
	"errors"
	"testing"
	"time"

	"github.com/LFDT-Lineth/zkc/pkg/zkc/vm"
	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	gocorset "github.com/consensys/loom/integration_test/go_corset"
	"github.com/consensys/loom/integration_test/zkc/riscv"
	"github.com/consensys/loom/integration_test/zkc/riscv/minimalelf"
	"github.com/consensys/loom/integration_test/zkc/riscv/predecoding"
	"github.com/consensys/loom/public"
)

// TestRiscvAllInOne proves and verifies, with loom, the RISC-V interpreter
// running prover-ray's instruction-coverage guest (minimalelf.AllInOneElfProgram).
func TestRiscvAllInOne(t *testing.T) {
	if testing.Short() {
		t.Skip("proves the RISC-V interpreter")
	}
	elf, wantOutput := minimalelf.AllInOneElfProgram()
	proveGuest(t, elf, wantOutput)
}

func proveGuest(t *testing.T, elf, wantOutput []byte) {
	t.Helper()
	binf, err := riscv.CompiledBinaryFile()
	if err != nil {
		t.Fatal(err)
	}
	inputs, err := predecoding.PrepareInputs(elf, nil)
	if err != nil {
		t.Fatal(err)
	}

	// zkc: trace, in one shard, and check
	cfg := vm.DEFAULT_TRACE_CONFIG
	start := time.Now()
	outputs, lazy, errs := binf.Trace(inputs, cfg)
	if len(errs) > 0 {
		t.Fatalf("trace: %v", errors.Join(errs...))
	}
	if got := outputs["guest_output"]; !bytes.Equal(got, wantOutput) {
		t.Fatalf("guest_output = %x, want %x", got, wantOutput)
	}
	if failures, errs := binf.Check(cfg, lazy.Unwrap()); len(failures) > 0 || len(errs) > 0 {
		t.Fatalf("zkc check: %v %v", failures, errs)
	}
	if n := lazy.Unwrap().Len(); n != 1 {
		t.Fatalf("%d shards, want 1", n)
	}
	shard, errs := lazy.Unwrap().Get(0)
	if len(errs) > 0 {
		t.Fatal(errors.Join(errs...))
	}
	t.Logf("traced in %v", time.Since(start))

	// loom: translate, prove, verify
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
	publicInputs, err := manifest.PublicInputsOf(inputs, pg)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("%d modules, %d public inputs", len(pg.Modules), len(publicInputs))

	start = time.Now()
	pk, vk, err := loom.Setup(tr, pg)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("setup in %v", time.Since(start))
	st := loom.Statement{Program: pg, VerificationKey: vk, PublicInputs: publicInputs}
	start = time.Now()
	prf, err := loom.Prove(st, loom.Witness{Trace: tr, ProvingKey: pk})
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("proved in %v", time.Since(start))
	start = time.Now()
	if err := loom.Verify(st, prf); err != nil {
		t.Fatal(err)
	}
	t.Logf("verified in %v", time.Since(start))

	// another program: one immediate of the predecoded instructions changed
	bad := st
	bad.PublicInputs = make(public.Inputs, len(publicInputs))
	for name, in := range publicInputs {
		bad.PublicInputs[name] = in
	}
	name := "__public__.decoded.imm'0"
	in, ok := publicInputs[name]
	if !ok {
		t.Fatalf("no public input %s", name)
	}
	entries := append([]public.Entry(nil), in.Entries...)
	last := &entries[len(entries)-1]
	v := last.Value
	v.Add(&v, new(koalabear.Element).SetOne())
	last.SetBase(v)
	bad.PublicInputs[name] = public.Input{Module: in.Module, Entries: entries}
	if err := loom.Verify(bad, prf); err == nil {
		t.Fatal("proof accepted for another program")
	}
}
