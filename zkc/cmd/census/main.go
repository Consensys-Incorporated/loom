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

// Command census renders the zkc verifier column report as an HTML page.
//
// Generate the data, then the page, from the repository root:
//
//	ZKC_REPORT=$PWD/zkc-report.json go test -count=1 -run TestReport ./zkc
//	go run ./zkc/cmd/census -data zkc-report.json -out zkc-census.html
//
// The page embeds the data and loads its fonts from Google Fonts; it needs no
// other file.
package main

import (
	"bytes"
	_ "embed"
	"encoding/json"
	"flag"
	"fmt"
	"os"
)

// generating -> from loom's root
//  ZKC_REPORT=$PWD/zkc-report.json go test -count=1 -run TestReport ./zkc
// && go run zkc/cmd/census/main.go -data zkc-report.json -out zkc-report.html

//go:embed census.html.tmpl
var page []byte

// placeholder is replaced by the report data in the template.
const placeholder = "__DATA__"

func main() {
	data := flag.String("data", "zkc-report.json", "report data written by TestReport (ZKC_REPORT)")
	out := flag.String("out", "zkc-census.html", "HTML page to write")
	flag.Parse()
	if err := run(*data, *out); err != nil {
		fmt.Fprintln(os.Stderr, "census:", err)
		os.Exit(1)
	}
}

func run(dataPath, outPath string) error {
	raw, err := os.ReadFile(dataPath)
	if err != nil {
		return err
	}
	// Check the data and compact it; the page expects an array of shapes.
	var shapes []json.RawMessage
	if err := json.Unmarshal(raw, &shapes); err != nil {
		return fmt.Errorf("%s: not a report written by TestReport: %w", dataPath, err)
	}
	if len(shapes) == 0 {
		return fmt.Errorf("%s: the report has no shapes", dataPath)
	}
	var compact bytes.Buffer
	if err := json.Compact(&compact, raw); err != nil {
		return err
	}
	if bytes.Count(page, []byte(placeholder)) != 1 {
		return fmt.Errorf("template: expected one %s placeholder", placeholder)
	}
	html := bytes.Replace(page, []byte(placeholder), compact.Bytes(), 1)
	if err := os.WriteFile(outPath, html, 0o644); err != nil {
		return err
	}
	fmt.Printf("wrote %s (%d shapes)\n", outPath, len(shapes))
	return nil
}
