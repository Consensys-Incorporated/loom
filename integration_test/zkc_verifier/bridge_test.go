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
	"path/filepath"
	"testing"

	zkc_util "github.com/LFDT-Lineth/zkc/pkg/zkc/util"
)

// runZkc compiles files, traces them on a JSON input, and proves and verifies
// the result with full FRI. It returns the program outputs.
func runZkc(t *testing.T, input string, files ...string) map[string][]byte {
	t.Helper()
	binf, err := CompileFiles(files...)
	if err != nil {
		t.Fatal(err)
	}
	pg, err := NewProgram(binf, nil)
	if err != nil {
		t.Fatal(err)
	}
	in, err := zkc_util.ParseJsonInputFile([]byte(input))
	if err != nil {
		t.Fatal(err)
	}
	tr, outputs, err := pg.Trace(in)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("\n%s", FormatStats(Stats(tr)))
	if _, err := pg.ProveAndVerify(tr); err != nil {
		t.Fatal(err)
	}
	return outputs
}

func TestBridge(t *testing.T) {
	cases := []struct {
		name  string
		input string
	}{
		{"zkc_01", `{"data": "0x0000_0001"}`},
		{"zkc_01", `{"data": "0x0041_0042"}`},
		{"zkc_02", `{"data": "0x0003_0008"}`},
		{"zkc_02", `{"data": "0x000f_8000"}`},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			runZkc(t, tc.input, filepath.Join("testdata", tc.name+".zkc"))
		})
	}
}
