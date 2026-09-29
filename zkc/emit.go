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

package zkc

import (
	"fmt"
	"slices"
	"strings"
)

// Emitter writes the body of a straight-line zkc function. Values are passed
// around as zkc expressions (variable names or literals) of type 𝔽.
type Emitter struct {
	sb   strings.Builder
	next int

	// Perms counts the Poseidon2 permutations emitted, including those of
	// node compressions.
	Perms int

	// Sponges, when set, makes Sponge emit calls to generated sponge
	// functions (sponge_L for L inputs) and record their definitions, instead
	// of inlining the permutations. The caller then pays the 8 digest
	// registers and one lookup per hash; see SpongeSources.
	Sponges map[string]func() string
}

// Line emits one statement.
func (e *Emitter) Line(format string, args ...any) {
	e.sb.WriteString("    ")
	fmt.Fprintf(&e.sb, format, args...)
	e.sb.WriteString("\n")
}

// String returns the emitted body.
func (e *Emitter) String() string {
	return e.sb.String()
}

// Fresh declares n fresh 𝔽 variables and returns their names.
func (e *Emitter) Fresh(n int) []string {
	names := make([]string, n)
	for i := range names {
		names[i] = fmt.Sprintf("v%d", e.next)
		e.next++
	}
	e.Line("var %s", typed(names))
	return names
}

// Let binds x to a fresh variable and returns its name.
func (e *Emitter) Let(x string) string {
	v := fmt.Sprintf("v%d", e.next)
	e.next++
	e.Line("var %s:𝔽 = %s", v, x)
	return v
}

// Call emits outs = fn(args) with n fresh outputs.
func (e *Emitter) Call(fn string, n int, args ...string) []string {
	outs := e.Fresh(n)
	e.Line("%s = %s(%s)", strings.Join(outs, ", "), fn, strings.Join(args, ", "))
	return outs
}

// Perm emits one Poseidon2 permutation of a 24-lane state.
func (e *Emitter) Perm(state []string) []string {
	if len(state) != P2Width {
		panic(fmt.Sprintf("Perm: state has %d lanes", len(state)))
	}
	e.Perms++
	return e.Call("p2_perm", P2Width, state...)
}

// Node emits the Merkle node compression of two digests.
func (e *Emitter) Node(left, right []string) []string {
	if len(left) != P2Digest || len(right) != P2Digest {
		panic("Node: digests must have 8 elements")
	}
	e.Perms++
	return e.Call("p2_node", P2Digest, append(append([]string(nil), left...), right...)...)
}

// MerkleStep emits one Merkle path level: the node compression of (h, sib)
// if the index bit b is 0, of (sib, h) otherwise.
func (e *Emitter) MerkleStep(h, sib []string, b string) []string {
	e.Perms++
	return e.Call(merkleStepFn, P2Digest, slices.Concat(h, sib, []string{b})...)
}

// Sponge emits loom's Poseidon2 sponge (hash.Poseidon2SpongeHasher) over
// inputs and returns the digest. The sponge overwrites the rate lanes with
// each block: a full block replaces lanes 0..15; a trailing partial block of
// k elements only replaces lanes 0..k-1. The empty input hashes to zero.
func (e *Emitter) Sponge(inputs []string) []string {
	if len(inputs) == 0 {
		return []string{"0", "0", "0", "0", "0", "0", "0", "0"}
	}
	if e.Sponges == nil {
		return e.spongeFrom(zeroState(), inputs)
	}
	e.Perms += (len(inputs) + P2Rate - 1) / P2Rate
	if len(inputs) <= maxCallArgs {
		e.Sponges[spongeFn(len(inputs))] = func() string { return spongeSource(len(inputs)) }
		return e.Call(spongeFn(len(inputs)), P2Digest, inputs...)
	}
	// zkc calls take at most 255 arguments: absorb full chunks while the rest
	// does not fit, carrying the state.
	state := zeroState()
	for len(inputs) > maxCallArgs-P2Width {
		e.Sponges[absorbFn] = absorbSource
		state = e.Call(absorbFn, P2Width, slices.Concat(state, inputs[:absorbChunk])...)
		inputs = inputs[absorbChunk:]
	}
	e.Sponges[squeezeFn(len(inputs))] = func() string { return squeezeSource(len(inputs)) }
	return e.Call(squeezeFn(len(inputs)), P2Digest, slices.Concat(state, inputs)...)
}

const (
	// maxCallArgs is the number of arguments of the largest sponge call.
	maxCallArgs = 248
	// absorbChunk is the number of elements absorbed by absorbFn: 13 full
	// blocks, so that the state plus the chunk fit in one call.
	absorbChunk = 13 * P2Rate
	absorbFn    = "sponge_absorb"
)

func zeroState() []string {
	res := make([]string, P2Width)
	for i := range res {
		res[i] = "0"
	}
	return res
}

// spongeFrom continues the sponge from state over inputs (at least one
// element) and returns the digest.
func (e *Emitter) spongeFrom(state, inputs []string) []string {
	state = slices.Clone(state)
	for start := 0; start < len(inputs); start += P2Rate {
		end := min(start+P2Rate, len(inputs))
		copy(state, inputs[start:end])
		if end == len(inputs) {
			// last block: only the digest lanes are needed
			e.Perms++
			outs := e.Fresh(P2Digest)
			e.Line("%s, %s = p2_perm(%s)", strings.Join(outs, ", "),
				strings.TrimSuffix(strings.Repeat("_, ", P2Width-P2Digest), ", "), strings.Join(state, ", "))
			return outs
		}
		state = e.Perm(state)
	}
	panic("spongeFrom: empty input")
}

func spongeFn(n int) string  { return fmt.Sprintf("sponge_%d", n) }
func squeezeFn(n int) string { return fmt.Sprintf("sponge_squeeze_%d", n) }

// spongeSource defines sponge_n, hashing n elements from the zero state.
func spongeSource(n int) string {
	var body Emitter
	d := body.spongeFrom(zeroState(), paramList("x", n))
	return fmt.Sprintf("\nfn %s(%s) -> (%s) {\n%s%s}\n", spongeFn(n), strings.Join(typedList("x", n), ", "),
		typed(paramList("d", P2Digest)), body.String(), assignAll(paramList("d", P2Digest), d))
}

// squeezeSource defines sponge_squeeze_n, finishing a sponge from a state
// with n more elements.
func squeezeSource(n int) string {
	var body Emitter
	d := body.spongeFrom(paramList("s", P2Width), paramList("x", n))
	return fmt.Sprintf("\nfn %s(%s, %s) -> (%s) {\n%s%s}\n", squeezeFn(n),
		strings.Join(typedList("s", P2Width), ", "), strings.Join(typedList("x", n), ", "),
		typed(paramList("d", P2Digest)), body.String(), assignAll(paramList("d", P2Digest), d))
}

// absorbSource defines sponge_absorb, absorbing absorbChunk elements (full
// blocks) into a state.
func absorbSource() string {
	var body Emitter
	state := paramList("s", P2Width)
	xs := paramList("x", absorbChunk)
	for start := 0; start < absorbChunk; start += P2Rate {
		state = slices.Clone(state)
		copy(state, xs[start:start+P2Rate])
		state = body.Perm(state)
	}
	return fmt.Sprintf("\nfn %s(%s, %s) -> (%s) {\n%s%s}\n", absorbFn,
		strings.Join(typedList("s", P2Width), ", "), strings.Join(typedList("x", absorbChunk), ", "),
		typed(paramList("t", P2Width)), body.String(), assignAll(paramList("t", P2Width), state))
}

func assignAll(dst, src []string) string {
	var sb strings.Builder
	for i := range dst {
		fmt.Fprintf(&sb, "    %s = %s\n", dst[i], src[i])
	}
	return sb.String()
}

// SpongeSources defines every sponge function recorded in an emitter's
// Sponges registry.
func SpongeSources(fns map[string]func() string) string {
	names := make([]string, 0, len(fns))
	for n := range fns {
		names = append(names, n)
	}
	slices.Sort(names)
	var sb strings.Builder
	for _, n := range names {
		sb.WriteString(fns[n]())
	}
	return sb.String()
}

// Select returns b ? y : x for a bit b in {0, 1}, as x + b·(y − x).
func (e *Emitter) Select(b, x, y string) string {
	return e.Let(fmt.Sprintf("%s + (%s * (%s - %s))", x, b, y, x))
}

// AssertEq emits a check that x = y.
func (e *Emitter) AssertEq(x, y string) {
	e.Line("assert_eq(%s, %s)", x, y)
}

// AssertEqAll emits checks that xs[i] = ys[i] for all i: one assert_eq8 or
// assert_eq6 call per digest or extension element, since each call costs the
// caller one lookup.
func (e *Emitter) AssertEqAll(xs, ys []string) {
	if len(xs) != len(ys) {
		panic("AssertEqAll: length mismatch")
	}
	for len(xs) > 0 {
		switch {
		case len(xs) >= 8:
			e.Line("assert_eq8(%s)", strings.Join(slices.Concat(xs[:8], ys[:8]), ", "))
			xs, ys = xs[8:], ys[8:]
		case len(xs) >= 6:
			e.Line("assert_eq6(%s)", strings.Join(slices.Concat(xs[:6], ys[:6]), ", "))
			xs, ys = xs[6:], ys[6:]
		default:
			e.AssertEq(xs[0], ys[0])
			xs, ys = xs[1:], ys[1:]
		}
	}
}

// assertSource defines the assertions used by the generated code. Each check
// is its own if/fail (many branches in one multi-line function crashed zkc
// v1.2.32 in an earlier form of the code).
var assertSource = func() string {
	var sb strings.Builder
	sb.WriteString("\nfn assert_eq(a:𝔽, b:𝔽) {\n    if a != b { fail }\n}\n")
	for _, n := range []int{6, 8} {
		a, b := make([]string, n), make([]string, n)
		for i := range a {
			a[i], b[i] = fmt.Sprintf("a%d:𝔽", i), fmt.Sprintf("b%d:𝔽", i)
		}
		fmt.Fprintf(&sb, "\nfn assert_eq%d(%s, %s) {\n", n, strings.Join(a, ", "), strings.Join(b, ", "))
		for i := range n {
			fmt.Fprintf(&sb, "    if a%d != b%d { fail }\n", i, i)
		}
		sb.WriteString("}\n")
	}
	return sb.String()
}()

// ChallengeDomainTag is the domain tag of loom's transcript challenge names
// (internal/fiat-shamir/transcript.go).
const ChallengeDomainTag uint64 = 0x46534944 // "FSID"

// StringElements returns loom's encoding of a string as field elements
// (hash.StringToElements): [tag, len(s), 3-byte little-endian limbs...].
func StringElements(tag uint64, s string) []string {
	res := []string{fmt.Sprint(tag), fmt.Sprint(len(s))}
	for i := 0; i < len(s); i += 3 {
		var limb uint64
		for j := 0; j < 3 && i+j < len(s); j++ {
			limb |= uint64(s[i+j]) << (8 * j)
		}
		res = append(res, fmt.Sprint(limb))
	}
	return res
}

// Challenge emits the digest of the transcript challenge name
// (fiatshamir.Transcript.ComputeChallenge without grinding):
//
//	H(StringToElements(FSID, name) || prev || bindings)
//
// where prev is the previous challenge digest, empty for the first challenge.
func (e *Emitter) Challenge(name string, prev []string, bindings ...[]string) []string {
	inputs := StringElements(ChallengeDomainTag, name)
	inputs = append(inputs, prev...)
	for _, b := range bindings {
		inputs = append(inputs, b...)
	}
	return e.Sponge(inputs)
}
