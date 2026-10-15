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
	"fmt"
	"sort"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/protocol"
)

// MaxLogModuleSize is the log of the maximum size of a module: a dynamic
// module's size is 2^ℓ with 0 ≤ ℓ ≤ MaxLogModuleSize.
const MaxLogModuleSize = constants.MAX_LOG_MODULE_SIZE

// ModuleSizes are the sizes of a statement's modules, by name.
type ModuleSizes map[string]int

// SizesOf returns the module sizes of a program.
func SizesOf(program board.Program) ModuleSizes {
	res := ModuleSizes{}
	for name, m := range program.Modules {
		res[name] = m.N
	}
	return res
}

// VerifierOption configures NewVerifier.
type VerifierOption func(*verifierConfig) error

type verifierConfig struct {
	dynamic map[string]bool
}

// WithDynamicModules makes the sizes of the given modules inputs of the
// circuit, given with each statement (Inputs), instead of constants: one
// circuit then verifies proofs of any sizes of these modules, up to
// 2^MaxLogModuleSize. A dynamic module must not have setup columns, whose
// commitment (in the verification key) depends on its size.
func WithDynamicModules(names ...string) VerifierOption {
	return func(c *verifierConfig) error {
		if c.dynamic == nil {
			c.dynamic = map[string]bool{}
		}
		for _, n := range names {
			c.dynamic[n] = true
		}
		return nil
	}
}

// moduleSize is the size N = 2^ℓ of a module in circuit: constants for a
// fixed module, the input cell of ℓ (range-checked) and the cell of N, read
// from a table, for a dynamic one.
type moduleSize struct {
	dynamic bool
	logN    int // ℓ: the size's log, a constant for a fixed module (the program's for a dynamic one)
	minLog  int // a dynamic module's minimum ℓ (see minLogSize)
	cell    int // the scalar cell of ℓ (dynamic modules only)
	n       int // the scalar cell of N
}

// minLogSize returns the smallest ℓ such that N = 2^ℓ > 2·max|s| over the
// shifts s of a module's relation. The proof's schedule keeps every shift mod
// N, sorted (protocol.BuildCanonicalSchedule); above that size, no two shifts
// of a column are equal mod N and their order is the same whatever N
// (non-negative shifts ascending, then negative ones), so the proof's shape
// does not depend on N, and a shift's raw value is recovered from its value
// mod N (rawShift).
func minLogSize(mod board.CompiledModule) int {
	maxAbs := 0
	if mod.VanishingRelation != nil {
		for _, leaf := range mod.VanishingRelation.LeavesFull(expr.NewConfig(expr.WithoutChallenges(), expr.WithoutVerifierColumns())) {
			maxAbs = max(maxAbs, leaf.Shift, -leaf.Shift)
		}
	}
	l := 0
	for 1<<l <= 2*maxAbs {
		l++
	}
	return l
}

// rawShift returns the shift of a module's column whose value mod the
// program's size N0 is norm (as the schedule holds it): norm if below N0/2,
// norm − N0 otherwise (minLogSize).
func (v *Verifier) rawShift(module string, norm int) int {
	n0 := v.program.Modules[module].N
	if norm < n0/2 || norm == 0 {
		return norm
	}
	return norm - n0
}

// buildSizes checks the dynamic modules and allocates their size inputs: the
// log ℓ of each, range-checked to [0, MaxLogModuleSize] (ℓ and
// MaxLogModuleSize − ℓ both below 2^5), and N = 2^ℓ read from a table.
func (v *Verifier) buildSizes(dynamic map[string]bool) error {
	m := v.M
	withSetup := map[string]bool{}
	for _, c := range v.program.SetupColumns {
		withSetup[c.Module] = true
	}
	names := make([]string, 0, len(dynamic))
	for name := range dynamic {
		if _, ok := v.program.Modules[name]; !ok {
			return fmt.Errorf("NewVerifier: dynamic module %q is not in the program", name)
		}
		if withSetup[name] {
			return fmt.Errorf("NewVerifier: dynamic module %q has setup columns, whose commitment depends on its size", name)
		}
		names = append(names, name)
	}
	sort.Strings(names)

	v.sizes = map[string]moduleSize{}
	for name, mod := range v.program.Modules {
		if mod.N > 1<<MaxLogModuleSize {
			return fmt.Errorf("NewVerifier: module %q has size %d, above 2^%d", name, mod.N, MaxLogModuleSize)
		}
		if !dynamic[name] {
			v.sizes[name] = moduleSize{logN: log2(mod.N), n: m.Const(ScalarCell(koalabear.NewElement(uint64(mod.N))))}
		}
	}
	maxLog := m.Const(ScalarCell(koalabear.NewElement(MaxLogModuleSize)))
	for _, name := range names {
		mod := v.program.Modules[name]
		minLog := minLogSize(mod)
		if log2(mod.N) < minLog {
			return fmt.Errorf("NewVerifier: dynamic module %q: the program's size %d is below its minimum 2^%d (its shifts)", name, mod.N, minLog)
		}
		l := v.sizeInput(name, minLog)
		// ℓ − minLog and MaxLog − ℓ are both in [0, 2^5).
		for _, x := range []int{m.Sub(l, m.Const(ScalarCell(koalabear.NewElement(uint64(minLog))))), m.Sub(maxLog, l)} {
			m.AssertEq(x, m.Bits(x, 5).Shr[0])
		}
		v.sizes[name] = moduleSize{dynamic: true, logN: log2(mod.N), minLog: minLog, cell: l, n: v.sizeTable("pow2", l, func(l int) koalabear.Element {
			return koalabear.NewElement(uint64(1) << l)
		})}
	}
	return nil
}

// sizeInput allocates the input cell of a dynamic module's log size, read
// from the statement's ModuleSizes (its minimum is minLog).
func (v *Verifier) sizeInput(module string, minLog int) int {
	if v.sizeInputs == nil {
		v.sizeInputs = map[int]string{}
	}
	v.sizeInputs[len(v.extract)] = module
	return v.input(func(st *statement) (Cell, error) {
		return statementSize(st.sizes, module, minLog)
	})
}

// sizeTable returns the cell f(ℓ) for the scalar cell ℓ of a dynamic size,
// read from a table of the constants f(0), ..., f(MaxLogModuleSize) built
// once per key. ℓ must be range-checked (buildSizes).
func (v *Verifier) sizeTable(key string, l int, f func(l int) koalabear.Element) int {
	if v.sizeTables == nil {
		v.sizeTables = map[string]Table{}
	}
	tab, ok := v.sizeTables[key]
	if !ok {
		entries := make([]int, MaxLogModuleSize+1)
		for i := range entries {
			entries[i] = v.M.Const(ScalarCell(f(i)))
		}
		tab = v.M.Table(entries)
		v.sizeTables[key] = tab
	}
	return v.M.Lookup(tab, l)
}

// SizeN returns the scalar cell of a module's size N.
func (v *Verifier) SizeN(module string) int { return v.sizes[module].n }

// SizeInvN returns the scalar cell of 1/N for a module.
func (v *Verifier) SizeInvN(module string) int {
	s := v.sizes[module]
	inv := func(l int) koalabear.Element {
		var x koalabear.Element
		x.SetUint64(uint64(1) << l)
		x.Inverse(&x)
		return x
	}
	if !s.dynamic {
		return v.M.Const(ScalarCell(inv(s.logN)))
	}
	return v.sizeTable("invN", s.cell, inv)
}

// SizeOmega returns the scalar cell of ω_N^e for a module, ω_N the generator
// of its domain and e a constant exponent (possibly negative).
func (v *Verifier) SizeOmega(module string, e int) int {
	s := v.sizes[module]
	pow := func(l int) koalabear.Element {
		g, err := koalabear.Generator(uint64(1) << l)
		if err != nil {
			panic(err)
		}
		var x koalabear.Element
		x.ExpInt64(g, int64(e))
		return x
	}
	if !s.dynamic {
		return v.M.Const(ScalarCell(pow(s.logN)))
	}
	return v.sizeTable(fmt.Sprintf("omega^%d", e), s.cell, pow)
}

// bindModuleSizes binds the module sizes as protocol.ModuleSizesTranscript
// encodes them: the tag, the module count, then every module's size in
// ModuleOrder — constants for the fixed modules, the size cells of the
// dynamic ones.
func (v *Verifier) bindModuleSizes(name string) {
	order := protocol.ModuleOrder(v.program)
	run := []koalabear.Element{koalabear.NewElement(constants.MODULE_SIZES_DOMAIN_TAG), koalabear.NewElement(uint64(len(order)))}
	for _, mod := range order {
		s := v.sizes[mod]
		if !s.dynamic {
			run = append(run, koalabear.NewElement(uint64(v.program.Modules[mod].N)))
			continue
		}
		v.tr.BindElements(name, run)
		run = nil
		v.tr.Bind(name, Scalar(s.n))
	}
	v.tr.BindElements(name, run)
}

// statementSize returns the input value of a dynamic module's log size for a
// statement: its size must be a power of two between the module's minimum
// (minLogSize) and 2^MaxLogModuleSize.
func statementSize(sizes ModuleSizes, module string, minLog int) (Cell, error) {
	n, ok := sizes[module]
	if !ok {
		return Cell{}, fmt.Errorf("no size for the dynamic module %q", module)
	}
	if n < 1<<minLog || n&(n-1) != 0 || n > 1<<MaxLogModuleSize {
		return Cell{}, fmt.Errorf("module %q: size %d is not a power of two between 2^%d and 2^%d", module, n, minLog, MaxLogModuleSize)
	}
	return ScalarCell(hash.NewElement(uint64(log2(n)))), nil
}
