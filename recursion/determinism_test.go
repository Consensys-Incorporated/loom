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
	"slices"
	"strings"
	"testing"

	"github.com/consensys/loom/board"
	"github.com/consensys/loom/integration_test/zkc/riscv/minimalelf"
	"github.com/consensys/loom/internal/hash"
)

// compiled is what a recursion layer pins about the program below it: the
// program, as board.Describe writes it, and its verification key.
type compiled struct {
	desc string
	vk   []hash.Digest
}

// requireSame fails if two builds of the same program differ, naming the first
// line of their descriptions that differs.
func requireSame(t *testing.T, what string, a, b compiled) {
	t.Helper()
	if a.desc != b.desc {
		la, lb := strings.Split(a.desc, "\n"), strings.Split(b.desc, "\n")
		for i := range min(len(la), len(lb)) {
			if la[i] != lb[i] {
				t.Fatalf("%s: two builds compile differently, first at line %d:\n  %.200s\n  %.200s", what, i, la[i], lb[i])
			}
		}
		t.Fatalf("%s: two builds compile to %d and %d lines", what, len(la), len(lb))
	}
	if !slices.Equal(a.vk, b.vk) {
		t.Fatalf("%s: two builds compile alike but have different verification keys", what)
	}
}

// TestDeterministicRiscvVerifier builds, twice and independently, the RISC-V
// interpreter's program, a proof of it, and the size-oblivious verifier
// circuit of that proof. Both builds must give the same programs and the same
// verification keys: a recursion layer pins the program and the key of the
// layer below, so a build that depended on the run (random column names, Go's
// map order) would give every prover its own circuit.
func TestDeterministicRiscvVerifier(t *testing.T) {
	if testing.Short() {
		t.Skip("proves a RISC-V guest twice")
	}
	elf, _ := minimalelf.AllInOneElfProgram()
	var riscv, verifier []compiled
	for range 2 {
		sys := newRiscvSystem(t, false)
		sys.padForDynamic()
		ip := sys.prove(t, elf)
		riscv = append(riscv, compiled{board.Describe(ip.program), ip.vk.Roots})
		v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi), WithDynamicModules(sys.dynamicModules()...))
		if err != nil {
			t.Fatal(err)
		}
		p, err := v.M.Compile()
		if err != nil {
			t.Fatal(err)
		}
		_, vk := keys(t, p)
		verifier = append(verifier, compiled{board.Describe(p.Loom), vk.Roots})
	}
	requireSame(t, "RISC-V program", riscv[0], riscv[1])
	requireSame(t, "verifier circuit", verifier[0], verifier[1])
}

// TestDeterministicStaticVerifier is TestDeterministicRiscvVerifier for a
// verifier of fixed module sizes with two instances on one machine, as a layer
// verifying proofs of a verifier circuit is: the openings machine is compiled
// and proven twice, and each build gets its verifier.
func TestDeterministicStaticVerifier(t *testing.T) {
	var inner, verifier []compiled
	for range 2 {
		ip := vmProofs(t, 3)[0]
		inner = append(inner, compiled{board.Describe(ip.program), ip.vk.Roots})
		m := &Machine{}
		for range 2 {
			if _, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi), WithMachine(m)); err != nil {
				t.Fatal(err)
			}
		}
		p, err := m.Compile()
		if err != nil {
			t.Fatal(err)
		}
		_, vk := keys(t, p)
		verifier = append(verifier, compiled{board.Describe(p.Loom), vk.Roots})
	}
	requireSame(t, "openings machine", inner[0], inner[1])
	requireSame(t, "verifier circuit", verifier[0], verifier[1])
}
