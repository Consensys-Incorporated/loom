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
	"os"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/prover"
)

// recursionQueriesEnv lists the FRI query counts TestRiscvTwoProofsRowsPerQueries
// measures, comma-separated (default defaultRecursionQueries).
const recursionQueriesEnv = "LOOM_RECURSION_QUERIES"

// recursionProveEnv, when set to a non-empty value, makes
// TestRiscvTwoProofsRowsPerQueries also prove and verify every verifier
// circuit it measures (minutes at high query counts).
const recursionProveEnv = "LOOM_RECURSION_PROVE"

var defaultRecursionQueries = []int{32, 64, 100}

// TestRiscvTwoProofsRowsPerQueries measures the recursion verifier circuit of
// TestRiscvTwoProofsVerifier (two RISC-V proofs of one program, the
// instruction-coverage guest and a Fibonacci(200) loop, verified in one
// size-oblivious circuit) as a function of the inner proofs' number of FRI
// queries, at Reed-Solomon rate 1/constants.RATE. For each query count, it
// proves the two guests with that many queries, builds and executes their
// verifier circuit, and logs its rows per chip, its padded size N per chip
// and in total, and whether it fits in one shard: every module at most
// 2^MaxLogModuleSize rows (the FFT domain of the field at that rate). It ends
// with a table of the rows per chip, one column per query count.
//
//	LOOM_RECURSION_QUERIES=32,64,100,128 go test ./recursion -run TestRiscvTwoProofsRowsPerQueries -v -timeout 2h
//
// The verifier circuits are only executed, not proven, unless
// LOOM_RECURSION_PROVE is set. The test fails if a query count is invalid or a
// circuit does not execute, not if it exceeds a shard: it is a measurement.
func TestRiscvTwoProofsRowsPerQueries(t *testing.T) {
	if testing.Short() {
		t.Skip("proves RISC-V guests and executes their recursive verifier, per query count")
	}
	queries := defaultRecursionQueries
	if v := os.Getenv(recursionQueriesEnv); v != "" {
		queries = nil
		for _, f := range strings.Split(v, ",") {
			q, err := strconv.Atoi(strings.TrimSpace(f))
			if err != nil || q <= 0 {
				t.Fatalf("%s=%q: %q is not a positive query count", recursionQueriesEnv, v, f)
			}
			queries = append(queries, q)
		}
	}
	proveCircuits := os.Getenv(recursionProveEnv) != ""
	t.Logf("Reed-Solomon rate 1/%d, shard limit 2^%d rows per module, FRI queries %v",
		constants.RATE, MaxLogModuleSize, queries)

	sys := newRiscvSystem(t, false)
	sys.padForDynamic()

	// rows[module][i] is the module's rows at queries[i]
	rows := map[string][]int{}
	var order []string
	totals := make([]int, len(queries))
	maxN := make([]int, len(queries))
	for i, q := range queries {
		t.Logf("=== %d FRI queries", q)
		t0 := time.Now()
		ips := sys.proveTwoGuests(t, prover.WithNumFriQueries(q))
		if got := len(ips[0].prf.Opening.FRIProof.FRIQueries); got != q {
			t.Fatalf("inner proof has %d FRI queries, want %d", got, q)
		}
		t.Logf("inner proofs in %v", time.Since(t0).Round(time.Millisecond))

		p, in := buildTwoProofsVerifier(t, sys, ips)
		r, chips := executeVerifierCircuit(t, p, in)
		for _, c := range chips {
			if _, ok := rows[c.module]; !ok {
				rows[c.module] = make([]int, len(queries))
				order = append(order, c.module)
			}
			rows[c.module][i] = c.rows
			totals[i] += c.n
			maxN[i] = max(maxN[i], c.n)
			t.Logf("  %-8s %9d rows, N = 2^%d", c.module, c.rows, log2Int(c.n))
		}
		t.Logf("%d queries: %d padded rows, largest module N = 2^%d, fits in one shard: %v",
			q, totals[i], log2Int(maxN[i]), maxN[i] <= 1<<MaxLogModuleSize)

		if proveCircuits {
			t0 = time.Now()
			if err := prove(t, p, r); err != nil {
				t.Fatalf("%d queries: verifier execution rejected: %v", q, err)
			}
			t.Logf("verifier execution: setup+prove+verify in %v", time.Since(t0).Round(time.Millisecond))
		}
	}

	var b strings.Builder
	fmt.Fprintf(&b, "\nrows per chip, by FRI queries (rate 1/%d):\n%-10s", constants.RATE, "chip")
	for _, q := range queries {
		fmt.Fprintf(&b, " %12d", q)
	}
	for _, module := range order {
		fmt.Fprintf(&b, "\n%-10s", module)
		for _, n := range rows[module] {
			fmt.Fprintf(&b, " %12d", n)
		}
	}
	fmt.Fprintf(&b, "\n%-10s", "padded")
	for _, n := range totals {
		fmt.Fprintf(&b, " %12d", n)
	}
	fmt.Fprintf(&b, "\n%-10s", "max log N")
	for _, n := range maxN {
		fmt.Fprintf(&b, " %12d", log2Int(n))
	}
	fmt.Fprintf(&b, "\n%-10s", "one shard")
	for _, n := range maxN {
		fmt.Fprintf(&b, " %12v", n <= 1<<MaxLogModuleSize)
	}
	t.Log(b.String())
}
