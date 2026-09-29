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

package zkcverifier

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
)

// P2Layout selects how the Poseidon2 permutation is laid out in zkc.
type P2Layout int

const (
	// P2Rounds implements each round kind as its own function (one module per
	// kind), reading round constants from a static table: ~29 rows per
	// permutation across narrow modules.
	P2Rounds P2Layout = iota
	// P2Inline inlines the whole permutation into one straight-line function:
	// one row per permutation in a single wide module.
	P2Inline
)

func (l P2Layout) String() string {
	if l == P2Inline {
		return "inline"
	}
	return "rounds"
}

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

// GeneratePoseidon2 returns zkc source defining
//
//	fn p2_perm(s0:𝔽, …, s23:𝔽) -> (r0:𝔽, …, r23:𝔽)
//
// equal to gnark-crypto's koalabear Poseidon2 permutation of width 24.
func GeneratePoseidon2(layout P2Layout) string {
	params := poseidon2.NewParameters(P2Width, P2FullRounds, P2PartialRounds)
	var sb strings.Builder
	fmt.Fprintf(&sb, "// Code generated by GeneratePoseidon2(%s); DO NOT EDIT.\n", layout)
	fmt.Fprintf(&sb, "// Poseidon2 over KoalaBear: width %d, %d full rounds, %d partial rounds, x^3.\n\n",
		P2Width, P2FullRounds, P2PartialRounds)

	in, out := vars("s", P2Width), vars("r", P2Width)
	if layout == P2Inline {
		writeInlinePerm(&sb, params, in, out)
		return sb.String()
	}

	// Static round-constant table: full rounds use all 24 lanes, partial
	// rounds only lane 0 (the other lanes of their rows are 0).
	nbRounds := P2FullRounds + P2PartialRounds
	fmt.Fprintf(&sb, "static p2_rc(round:u5) -> (%s) {\n", typed(vars("c", P2Width)))
	for r := 0; r < nbRounds; r++ {
		row := make([]string, P2Width)
		for i := range row {
			row[i] = "0"
			if i < len(params.RoundKeys[r]) {
				row[i] = felt(params.RoundKeys[r][i])
			}
		}
		sep := ","
		if r == nbRounds-1 {
			sep = ""
		}
		fmt.Fprintf(&sb, "    (%s)%s\n", strings.Join(row, ", "), sep)
	}
	sb.WriteString("}\n\n")

	// External matrix alone (applied once before the first round).
	fmt.Fprintf(&sb, "fn p2_ext(%s) -> (%s) {\n", typed(in), typed(out))
	externalMatrix(&sb, in, out, "e")
	sb.WriteString("}\n\n")

	// Full round: add round constants, S-box on every lane, external matrix.
	c := vars("c", P2Width)
	x := vars("x", P2Width)
	fmt.Fprintf(&sb, "fn p2_full(round:u5, %s) -> (%s) {\n", typed(in), typed(out))
	fmt.Fprintf(&sb, "    var %s\n", typed(c))
	fmt.Fprintf(&sb, "    %s = p2_rc[round]\n", strings.Join(c, ", "))
	for i := range x {
		fmt.Fprintf(&sb, "    var a%d:𝔽 = %s + %s\n", i, in[i], c[i])
		fmt.Fprintf(&sb, "    var %s:𝔽 = (a%d * a%d) * a%d\n", x[i], i, i, i)
	}
	externalMatrix(&sb, x, out, "e")
	sb.WriteString("}\n\n")

	// Partial round: add the lane-0 constant, S-box on lane 0, internal matrix.
	fmt.Fprintf(&sb, "fn p2_partial(round:u5, %s) -> (%s) {\n", typed(in), typed(out))
	fmt.Fprintf(&sb, "    var c0:𝔽\n")
	fmt.Fprintf(&sb, "    c0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ = p2_rc[round]\n")
	fmt.Fprintf(&sb, "    var a0:𝔽 = %s + c0\n", in[0])
	fmt.Fprintf(&sb, "    var x0:𝔽 = (a0 * a0) * a0\n")
	partialIn := append([]string{"x0"}, in[1:]...)
	internalMatrix(&sb, partialIn, out, "i")
	sb.WriteString("}\n\n")

	// Permutation: chain the rounds. It is multi-line (one call per round), and
	// zkc v1.2.32 cannot frame multi-line functions with 𝔽 inputs
	// (initMultiLineFraming calls Width() on native registers), so it is
	// inlined into its (integer-parameterised) caller.
	fmt.Fprintf(&sb, "#[inline]\nfn p2_perm(%s) -> (%s) {\n", typed(in), typed(out))
	st := vars("t", P2Width)
	fmt.Fprintf(&sb, "    var %s\n", typed(st))
	all := strings.Join(st, ", ")
	fmt.Fprintf(&sb, "    %s = p2_ext(%s)\n", all, strings.Join(in, ", "))
	for r := 0; r < nbRounds; r++ {
		fn := "p2_partial"
		if r < p2HalfFullRounds || r >= p2HalfFullRounds+P2PartialRounds {
			fn = "p2_full"
		}
		fmt.Fprintf(&sb, "    %s = %s(%d, %s)\n", all, fn, r, all)
	}
	for i := range out {
		fmt.Fprintf(&sb, "    %s = %s\n", out[i], st[i])
	}
	sb.WriteString("}\n")
	return sb.String()
}

// writeInlinePerm emits p2_perm as one straight-line function with the round
// constants inlined, so each call is a single row.
func writeInlinePerm(sb *strings.Builder, params *poseidon2.Parameters, in, out []string) {
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
				fmt.Fprintf(sb, "    var %s:𝔽 = (a%d_%d * a%d_%d) * a%d_%d\n", x[i], r, i, r, i, r, i)
			}
			externalMatrix(sb, x, next, fmt.Sprintf("e%d", r+1))
		} else {
			fmt.Fprintf(sb, "    var a%d_0:𝔽 = %s + %s\n", r, cur[0], felt(params.RoundKeys[r][0]))
			fmt.Fprintf(sb, "    var x%d_0:𝔽 = (a%d_0 * a%d_0) * a%d_0\n", r, r, r, r)
			partialIn := append([]string{fmt.Sprintf("x%d_0", r)}, cur[1:]...)
			internalMatrix(sb, partialIn, next, fmt.Sprintf("i%d", r+1))
		}
		cur = next
	}
	sb.WriteString("}\n")
}
