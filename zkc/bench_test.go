package zkc

import (
	"fmt"
	"os"
	"strings"
	"testing"

	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
)

// benchCase is one PCS shape to measure.
type benchCase struct {
	name string
	cfg  FixtureConfig
}

func singleSize(logN, nBase int) BatchConfig {
	return BatchConfig{{LogN: logN, NumBase: nBase, Shifts: []int{0, 1}}}
}

func benchCases() []benchCase {
	if os.Getenv("ZKC_BENCH") == "small" {
		return []benchCase{
			{"1 size 2^10, 16 polys", FixtureConfig{Batches: []BatchConfig{singleSize(10, 16)}, NumQueries: 32, Seed: 1}},
			{"3 sizes [10 8 6], 16 polys each", FixtureConfig{Batches: []BatchConfig{{
				{LogN: 10, NumBase: 16, Shifts: []int{0, 1}},
				{LogN: 8, NumBase: 16, Shifts: []int{0, 1}},
				{LogN: 6, NumBase: 16, Shifts: []int{0, 1}},
			}}, NumQueries: 32, Seed: 1}},
		}
	}
	var res []benchCase
	for _, n := range []int{4, 16, 64} {
		res = append(res, benchCase{fmt.Sprintf("1 size 2^10, %d polys", n),
			FixtureConfig{Batches: []BatchConfig{singleSize(10, n)}, NumQueries: 32, Seed: 1}})
	}
	for _, sizes := range [][]int{{10, 8}, {10, 8, 6}} {
		var b BatchConfig
		for _, l := range sizes {
			b = append(b, GroupConfig{LogN: l, NumBase: 16, Shifts: []int{0, 1}})
		}
		res = append(res, benchCase{fmt.Sprintf("%d sizes %v, 16 polys each", len(sizes), sizes),
			FixtureConfig{Batches: []BatchConfig{b}, NumQueries: 32, Seed: 1}})
	}
	for _, logN := range []int{8, 14} {
		res = append(res, benchCase{fmt.Sprintf("1 size 2^%d, 16 polys", logN),
			FixtureConfig{Batches: []BatchConfig{singleSize(logN, 16)}, NumQueries: 32, Seed: 1}})
	}
	return res
}

// TestBenchPCSVerifier measures the zkc PCS verifier over several shapes. It
// only runs with ZKC_BENCH=1.
func TestBenchPCSVerifier(t *testing.T) {
	if os.Getenv("ZKC_BENCH") == "" {
		t.Skip("set ZKC_BENCH=1 to run")
	}
	var sb strings.Builder
	fmt.Fprintf(&sb, "\n%-32s %8s %8s %11s %8s %8s %12s %12s\n",
		"shape", "perms", "perms/q", "cells", "columns", "q cols", "leaf elts/q", "leaf perms/q")
	for _, bc := range benchCases() {
		f, err := NewFixture(bc.cfg)
		if err != nil {
			t.Fatal(err)
		}
		p, err := GeneratePCSVerifier(f)
		if err != nil {
			t.Fatal(err)
		}
		res, err := zkcv.MeasureWith(p.Input, Gadgets(), writeZkc(t, p.Sources)...)
		if err != nil {
			t.Fatalf("%s: %v", bc.name, err)
		}
		cells, cols, qcols := 0, 0, 0
		for _, m := range res.Stats {
			cells += m.Cells()
			cols += m.Columns
			if m.Name == friQueryFn {
				qcols = m.Columns
			}
		}
		perms := p.MainPerms + bc.cfg.NumQueries*p.QueryPerms
		fmt.Fprintf(&sb, "%-32s %8d %8d %11d %8d %8d %12d %12d\n",
			bc.name, perms, p.QueryPerms, cells, cols, qcols, res.Leaf.Elements, res.Leaf.Perms)
		if os.Getenv("ZKC_BENCH_BREAKDOWN") != "" {
			fmt.Fprintf(&sb, "    %-18s %8s %8s %8s %8s\n", "module", "trace", "logup", "mult", "quotient")
			for _, l := range res.LeafModules[:min(8, len(res.LeafModules))] {
				fmt.Fprintf(&sb, "    %-18s %8d %8d %8d %8d\n", l.Module, l.Trace, l.Logup, l.Mult, l.Quotient)
			}
		}
	}
	t.Log(sb.String())
}
