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
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
)

// Poseidon2 parameters of loom's sponge and Merkle node hasher
// (internal/hash/hash.go): width 24, 6 full rounds, 21 partial rounds, x^3.
const (
	P2Width          = 24
	P2FullRounds     = 6
	P2PartialRounds  = 21
	p2HalfFullRounds = P2FullRounds / 2

	// P2Rate and P2Digest are the sponge rate and digest size of loom's
	// Poseidon2 sponge (internal/hash/poseidon2.go).
	P2Rate   = 16
	P2Digest = 8

	// Domain tags of loom's Merkle leaves and nodes (internal/fri/commitment.go).
	LeafDomainTag uint64 = 0x4c454146 // "LEAF"
	NodeDomainTag uint64 = 0x4e4f4445 // "NODE"
)

// p2Diag24 is the diagonal of the width-24 internal matrix, M = 1·1ᵀ + diag,
// as used by gnark-crypto's matMulInternalInPlace.
func p2Diag24() []koalabear.Element {
	var d [P2Width]koalabear.Element
	pow2Inv := func(n int) koalabear.Element {
		var r koalabear.Element
		r.SetUint64(1 << n)
		r.Inverse(&r)
		return r
	}
	set := func(i int, v int64) {
		d[i].SetInt64(v)
	}
	set(0, -2)
	set(1, 1)
	set(2, 2)
	d[3] = pow2Inv(1)
	set(4, 3)
	set(5, 4)
	d[6] = pow2Inv(1)
	d[6].Neg(&d[6])
	set(7, -3)
	set(8, -4)
	for i, n := range []int{8, 2, 3, 4, 5, 6, 24} {
		d[9+i] = pow2Inv(n)
	}
	for i, n := range []int{8, 3, 4, 5, 6, 7, 9, 24} {
		d[16+i] = pow2Inv(n)
		d[16+i].Neg(&d[16+i])
	}
	return d[:]
}

func felt(e koalabear.Element) string {
	return fmt.Sprintf("%d", e.Uint64())
}

func vars(prefix string, n int) []string {
	res := make([]string, n)
	for i := range res {
		res[i] = fmt.Sprintf("%s%d", prefix, i)
	}
	return res
}

func typed(names []string) string {
	res := make([]string, len(names))
	for i, n := range names {
		res[i] = n + ":𝔽"
	}
	return strings.Join(res, ", ")
}

// externalMatrix emits statements computing out = M_E · in, with M_E =
// circ(2·M4, M4, …, M4), following gnark-crypto's matMulExternalInPlace.
func externalMatrix(sb *strings.Builder, in, out []string, tmp string) {
	// M4 on each chunk of 4
	m4 := make([]string, P2Width)
	for c := 0; c < P2Width/4; c++ {
		x := in[4*c : 4*c+4]
		y := m4[4*c : 4*c+4]
		for j := range y {
			y[j] = fmt.Sprintf("%s_m%d", tmp, 4*c+j)
		}
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", tmp+fmt.Sprint("_t01_", c), x[0], x[1])
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", tmp+fmt.Sprint("_t23_", c), x[2], x[3])
		t01, t23 := tmp+fmt.Sprint("_t01_", c), tmp+fmt.Sprint("_t23_", c)
		t0123 := tmp + fmt.Sprint("_t0123_", c)
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", t0123, t01, t23)
		t01123 := tmp + fmt.Sprint("_t01123_", c)
		t01233 := tmp + fmt.Sprint("_t01233_", c)
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", t01123, t0123, x[1])
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", t01233, t0123, x[3])
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", y[3], x[0], x[0]+" + "+t01233)
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", y[1], x[2], x[2]+" + "+t01123)
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", y[0], t01, t01123)
		fmt.Fprintf(sb, "    var %s:𝔽 = %s + %s\n", y[2], t23, t01233)
	}
	// column sums of the chunks, then add them to every chunk
	for j := 0; j < 4; j++ {
		terms := make([]string, 0, P2Width/4)
		for c := 0; c < P2Width/4; c++ {
			terms = append(terms, m4[4*c+j])
		}
		fmt.Fprintf(sb, "    var %s_sum%d:𝔽 = %s\n", tmp, j, strings.Join(terms, " + "))
	}
	for i := 0; i < P2Width; i++ {
		fmt.Fprintf(sb, "    %s = %s + %s_sum%d\n", out[i], m4[i], tmp, i%4)
	}
}

// internalMatrix emits statements computing out = (1·1ᵀ + diag) · in.
func internalMatrix(sb *strings.Builder, in, out []string, tmp string) {
	fmt.Fprintf(sb, "    var %s_sum:𝔽 = %s\n", tmp, strings.Join(in, " + "))
	for i, d := range p2Diag24() {
		fmt.Fprintf(sb, "    %s = %s_sum + (%s * %s)\n", out[i], tmp, felt(d), in[i])
	}
}

// Poseidon2Source returns the zkc Poseidon2 library:
//
//	fn p2_perm(s0:𝔽, …, s23:𝔽) -> (r0:𝔽, …, r23:𝔽)
//	fn p2_node(l0:𝔽, …, l7:𝔽, r0:𝔽, …, r7:𝔽) -> (d0:𝔽, …, d7:𝔽)
//
// p2_perm is gnark-crypto's koalabear Poseidon2 permutation of width 24, as
// one straight-line function with the round constants inlined: each call is a
// single row. p2_node is loom's Merkle node compression
// (hash.Poseidon2NodeCompress).
func Poseidon2Source() string {
	params := poseidon2.NewParameters(P2Width, P2FullRounds, P2PartialRounds)
	var sb strings.Builder
	fmt.Fprintf(&sb, "// Code generated by Poseidon2Source; DO NOT EDIT.\n")
	fmt.Fprintf(&sb, "// Poseidon2 over KoalaBear: width %d, %d full rounds, %d partial rounds, x^3.\n\n",
		P2Width, P2FullRounds, P2PartialRounds)
	writeInlinePerm(&sb, params, vars("s", P2Width), vars("r", P2Width))

	l, r, d := vars("l", 8), vars("r", 8), vars("d", 8)
	t := vars("t", P2Width)
	fmt.Fprintf(&sb, "\n// p2_node compresses two digests: permute [NODE, 0 × 7, l, r], keep lanes 0..7.\n")
	fmt.Fprintf(&sb, "fn p2_node(%s, %s) -> (%s) {\n", typed(l), typed(r), typed(d))
	fmt.Fprintf(&sb, "    var %s\n", typed(t))
	fmt.Fprintf(&sb, "    %s = p2_perm(%d, 0, 0, 0, 0, 0, 0, 0, %s, %s)\n",
		strings.Join(t, ", "), NodeDomainTag, strings.Join(l, ", "), strings.Join(r, ", "))
	for i := range d {
		fmt.Fprintf(&sb, "    %s = %s\n", d[i], t[i])
	}
	sb.WriteString("}\n")
	return sb.String()
}

// P2Native declares p2_perm #[native]: its body then only serves to compute
// the witness, and Poseidon2Gadget supplies the constraints (see Gadgets).
var P2Native = true

// writeInlinePerm emits p2_perm as one straight-line function with the round
// constants inlined, so each call is a single row. zkc materializes nearly
// every operation as a register (a flat sum of variables is free, but each
// nested sub-expression or constant product costs one), so the linear layers
// use gnark-crypto's addition chains rather than dense linear forms.
func writeInlinePerm(sb *strings.Builder, params *poseidon2.Parameters, in, out []string) {
	if P2Native {
		sb.WriteString("#[native]\n")
	}
	fmt.Fprintf(sb, "fn p2_perm(%s) -> (%s) {\n", typed(in), typed(out))
	cur := vars("w0_", P2Width)
	fmt.Fprintf(sb, "    var %s\n", typed(cur))
	externalMatrix(sb, in, cur, "e0")
	nbRounds := P2FullRounds + P2PartialRounds
	for r := 0; r < nbRounds; r++ {
		next := vars(fmt.Sprintf("w%d_", r+1), P2Width)
		if r == nbRounds-1 {
			next = out
		} else {
			fmt.Fprintf(sb, "    var %s\n", typed(next))
		}
		full := r < p2HalfFullRounds || r >= p2HalfFullRounds+P2PartialRounds
		if full {
			x := vars(fmt.Sprintf("x%d_", r), P2Width)
			for i := range x {
				fmt.Fprintf(sb, "    var a%d_%d:𝔽 = %s + %s\n", r, i, cur[i], felt(params.RoundKeys[r][i]))
				fmt.Fprintf(sb, "    var %s:𝔽 = a%d_%d * a%d_%d * a%d_%d\n", x[i], r, i, r, i, r, i)
			}
			externalMatrix(sb, x, next, fmt.Sprintf("e%d", r+1))
		} else {
			fmt.Fprintf(sb, "    var a%d_0:𝔽 = %s + %s\n", r, cur[0], felt(params.RoundKeys[r][0]))
			fmt.Fprintf(sb, "    var x%d_0:𝔽 = a%d_0 * a%d_0 * a%d_0\n", r, r, r, r)
			partialIn := append([]string{fmt.Sprintf("x%d_0", r)}, cur[1:]...)
			internalMatrix(sb, partialIn, next, fmt.Sprintf("i%d", r+1))
		}
		cur = next
	}
	sb.WriteString("}\n")
}
