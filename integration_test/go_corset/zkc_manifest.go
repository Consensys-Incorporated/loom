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

package gocorset

import (
	"fmt"
	"math/big"
	"sort"

	gocorset_kb "github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
	zkc_constraints "github.com/LFDT-Lineth/zkc/pkg/zkc/constraints"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/vm"
	gnark_kb "github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/public"
)

// BinaryFile is a zkc binary over koalabear, traced with 32-bit words.
type BinaryFile = zkc_constraints.BinaryFile[gocorset_kb.Element, vm.Uint32]

type memory = vm.Memory[vm.Uint32]

const zkcPublicInputPrefix = "__public__."

// FrontendManifest carries frontend-level information that is not explicit in
// air.Schema: the public input memories, which become loom public inputs.
type FrontendManifest struct {
	PublicInputs map[string]PublicValueSpec

	publicInputMemories map[string]publicInputMemorySpec
}

// PublicValueSpec describes one column of a public input memory. Column is
// the loom public-input column; TraceColumn is the committed zkc trace column
// it equals.
type PublicValueSpec struct {
	Module      string
	Column      string
	TraceColumn string
	Register    int // index of the register in the memory
}

type publicInputMemorySpec struct {
	mem   memory
	specs []PublicValueSpec
}

// NewZkcManifest builds a manifest from a zkc binary. The memories are read
// from the tracing program, whose registers are already split into the limbs
// of the AIR (e.g. a u64 register x into x'3 … x'0 of 16 bits): each register
// is one trace column.
func NewZkcManifest(binf *BinaryFile) (*FrontendManifest, error) {
	if binf == nil {
		return nil, fmt.Errorf("NewZkcManifest: nil binary file")
	}
	manifest := &FrontendManifest{
		PublicInputs:        make(map[string]PublicValueSpec),
		publicInputMemories: make(map[string]publicInputMemorySpec),
	}
	program := binf.TracingProgram()
	for it := program.Inputs(); it.HasNext(); {
		mem := it.Next()
		if !mem.IsPublic() || !mem.IsReadOnly() || mem.IsStatic() {
			continue
		}
		var specs []PublicValueSpec
		for i, reg := range mem.Registers() {
			if !reg.Bitwidth().HasValue() {
				return nil, fmt.Errorf("NewZkcManifest: memory %q register %q is native", mem.Name(), reg.Name())
			}
			traceColumn := qualifyColumnName(mem.Name(), reg.Name())
			spec := PublicValueSpec{
				Module:      mem.Name(),
				Column:      zkcPublicInputPrefix + traceColumn,
				TraceColumn: traceColumn,
				Register:    i,
			}
			specs = append(specs, spec)
			manifest.PublicInputs[spec.Column] = spec
		}
		manifest.publicInputMemories[mem.Name()] = publicInputMemorySpec{mem, specs}
	}
	return manifest, nil
}

// ApplyToBridge ties every public input memory's columns to their public
// inputs, on all rows: zkc's padding rows included, whose public values are
// the registers' padding.
func (m *FrontendManifest) ApplyToBridge(bridge *CorsetBridge) error {
	if m == nil {
		return nil
	}
	if bridge == nil || bridge.Builder == nil {
		return fmt.Errorf("FrontendManifest.ApplyToBridge: nil bridge")
	}
	for _, name := range sortedKeys(m.PublicInputs) {
		spec := m.PublicInputs[name]
		if _, ok := bridge.Builder.Modules[spec.Module]; !ok {
			return fmt.Errorf("FrontendManifest.ApplyToBridge: public input module %q not found in builder", spec.Module)
		}
		relation := expr.Col(spec.TraceColumn).Sub(expr.PublicInput(spec.Column))
		if err := bridge.Builder.AssertZero(spec.Module, relation); err != nil {
			return err
		}
	}
	return nil
}

// PublicInputsOf returns the loom public inputs of a zkc input. A public input
// memory of h words is traced as N − h padding rows followed by its words in
// address order (address = row − (N − h)), N being its module's size in pg.
func (m *FrontendManifest) PublicInputsOf(input map[string][]byte, pg board.Program) (public.Inputs, error) {
	res := make(public.Inputs)
	if m == nil {
		return res, nil
	}
	for _, name := range sortedKeys(m.publicInputMemories) {
		spec := m.publicInputMemories[name]
		mem := spec.mem
		raw, ok := input[name]
		if !ok {
			return nil, fmt.Errorf("PublicInputs: missing public input memory %q", name)
		}
		module, ok := pg.Modules[name]
		if !ok {
			return nil, fmt.Errorf("PublicInputs: module %q not found in program", name)
		}
		nData := len(mem.DataRegisters())
		words := vm.DecodeBytes[vm.Uint32](raw, mem)
		if nData == 0 || len(words)%nData != 0 {
			return nil, fmt.Errorf("PublicInputs: memory %q decodes to %d words, for %d data registers", name, len(words), nData)
		}
		h, n := len(words)/nData, module.N
		if h > n {
			return nil, fmt.Errorf("PublicInputs: memory %q has %d rows, its module %d", name, h, n)
		}
		regs := mem.Registers()
		nAddr := len(mem.AddressRegisters())
		for _, s := range spec.specs {
			entries := make([]public.Entry, n)
			for row := range n {
				var value *big.Int
				switch a := row - (n - h); {
				case a < 0:
					value = regs[s.Register].Padding().BigInt()
				case s.Register < nAddr:
					v, err := addressLineValue(a, mem.AddressRegisters(), s.Register)
					if err != nil {
						return nil, fmt.Errorf("PublicInputs: memory %q: %w", name, err)
					}
					value = v
				default:
					value = words[a*nData+s.Register-nAddr].BigInt()
				}
				var elem gnark_kb.Element
				elem.SetBigInt(value)
				entries[row].Idx = row
				entries[row].SetBase(elem)
			}
			res[s.Column] = public.Input{Module: s.Module, Entries: entries}
		}
	}
	return res, nil
}

// addressLineValue returns line `line` of the address lines encoding address
// a, the last line being the least significant.
func addressLineValue(a int, lines []vm.Register[vm.Uint32], line int) (*big.Int, error) {
	var total, shift uint
	for i, r := range lines {
		w := r.Bitwidth().Unwrap()
		total += w
		if i > line {
			shift += w
		}
	}
	addr := big.NewInt(int64(a))
	if addr.BitLen() > int(total) {
		return nil, fmt.Errorf("address %d does not fit in %d bits", a, total)
	}
	return limbValue(addr, shift, lines[line].Bitwidth().Unwrap()), nil
}

func limbValue(value *big.Int, shift, width uint) *big.Int {
	limb := new(big.Int).Rsh(value, shift)
	mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), width), big.NewInt(1))
	return limb.And(limb, mask)
}

func qualifyColumnName(moduleName, registerName string) string {
	if moduleName == "" {
		return registerName
	}
	return moduleName + "." + registerName
}

func sortedKeys[V any](m map[string]V) []string {
	keys := make([]string, 0, len(m))
	for key := range m {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	return keys
}
