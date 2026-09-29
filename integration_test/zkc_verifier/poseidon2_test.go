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
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
)

// p2Driver applies n permutations: p2_in holds n input states, and the output
// states are written to p2_out, 24 words each.
const p2Driver = `
input p2_n(address:u1) -> (n:u16)
input p2_in(address:u16) -> (w:u32)
output p2_out(address:u16) -> (w:u32)

fn main() {
    var n:u16 = p2_n[0]
    for i:u16 = 0; i < n; i = i + 1 {
        check(i * 24)
    }
}

fn check(base:u16) {
%s
}
`

func p2DriverSource() string {
	var sb strings.Builder
	s, r := vars("s", P2Width), vars("r", P2Width)
	for i := range s {
		fmt.Fprintf(&sb, "    var %s:𝔽 = p2_in[base + %d] as 𝔽\n", s[i], i)
	}
	fmt.Fprintf(&sb, "    var %s\n", typed(r))
	fmt.Fprintf(&sb, "    %s = p2_perm(%s)\n", strings.Join(r, ", "), strings.Join(s, ", "))
	for i := range r {
		fmt.Fprintf(&sb, "    p2_out[base + %d] = %s as u32\n", i, r[i])
	}
	return fmt.Sprintf(p2Driver, sb.String())
}

// hexWords encodes 32-bit words as a zkc JSON hex byte string.
func hexWords(words []uint32) string {
	buf := make([]byte, 4*len(words))
	for i, w := range words {
		binary.BigEndian.PutUint32(buf[4*i:], w)
	}
	return "0x" + hex.EncodeToString(buf)
}

// p2Input returns the zkc input for n random permutations, and the expected
// output words.
func p2Input(t *testing.T, n int) (string, []uint32) {
	perm := poseidon2.NewPermutation(P2Width, P2FullRounds, P2PartialRounds)
	rng := rand.New(rand.NewPCG(1, 2))
	in := make([]uint32, 0, n*P2Width)
	exp := make([]uint32, 0, n*P2Width)
	for range n {
		state := make([]koalabear.Element, P2Width)
		for i := range state {
			state[i].SetUint64(rng.Uint64())
			in = append(in, uint32(state[i].Uint64()))
		}
		if err := perm.Permutation(state); err != nil {
			t.Fatal(err)
		}
		for i := range state {
			exp = append(exp, uint32(state[i].Uint64()))
		}
	}
	return fmt.Sprintf(`{"p2_n": "0x%04x", "p2_in": "%s"}`, n, hexWords(in)), exp
}

// decodeWords decodes a zkc output byte string of big-endian 32-bit words.
func decodeWords(b []byte) []uint32 {
	res := make([]uint32, len(b)/4)
	for i := range res {
		res[i] = binary.BigEndian.Uint32(b[4*i:])
	}
	return res
}

// writeSources writes the generated sources to a temporary directory and
// returns their paths.
func writeSources(t *testing.T, sources map[string]string) []string {
	t.Helper()
	dir := t.TempDir()
	var paths []string
	for name, src := range sources {
		p := filepath.Join(dir, name)
		if err := os.WriteFile(p, []byte(src), 0o600); err != nil {
			t.Fatal(err)
		}
		paths = append(paths, p)
	}
	return paths
}

func TestPoseidon2(t *testing.T) {
	for _, layout := range []P2Layout{P2Rounds, P2Inline} {
		t.Run(layout.String(), func(t *testing.T) {
			files := writeSources(t, map[string]string{
				"poseidon2.zkc": GeneratePoseidon2(layout),
				"main.zkc":      p2DriverSource(),
			})
			input, exp := p2Input(t, 4)
			got := decodeWords(runZkc(t, input, files...)["p2_out"])
			if !slices.Equal(got, exp) {
				t.Fatalf("p2_out mismatch:\ngot  %v\nwant %v", got, exp)
			}
		})
	}
}
