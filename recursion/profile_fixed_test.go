package recursion

import (
	"fmt"
	"sort"
	"testing"

	loomfield "github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/poly"
)

// costOf is TestProfileVerifierCost's table for an already compiled program.
func costOf(t *testing.T, p *Program, label string) {
	t.Helper()
	var rows []costRow
	for mod, m := range p.Loom.Modules {
		c := costRow{module: mod, n: m.N}
		if m.VanishingRelation != nil {
			c.deg = m.VanishingRelation.Degree()
			c.chunks = poly.QuotientDomainSize(c.deg, m.N) / m.N
		}
		for _, round := range p.Loom.Rounds {
			for _, ref := range round.Staged {
				if ref.Module != mod {
					continue
				}
				if ref.Field == loomfield.Ext {
					c.extW++
				} else {
					c.baseW++
				}
			}
		}
		rows = append(rows, c)
	}
	sort.Slice(rows, func(i, j int) bool { return rows[i].total() > rows[j].total() })
	total, cols := 0, 0
	for _, r := range rows {
		total += r.total()
		cols += r.baseW + r.extW
	}
	fmt.Printf("\n=== %s (%d chips, %d committed columns)\n", label, len(rows), cols)
	fmt.Printf("%-9s %7s %6s %5s %4s %7s %8s %11s %6s\n",
		"chip", "rows", "base", "ext", "deg", "chunks", "per-row", "cost", "share")
	for _, r := range rows {
		fmt.Printf("%-9s %7d %6d %5d %4d %7d %8d %11d %5.1f%%\n",
			r.module, r.n, r.baseW, r.extW, r.deg, r.chunks, r.perRow(), r.total(),
			100*float64(r.total())/float64(total))
	}
	fmt.Printf("%-9s %7s %6s %5s %4s %7s %8s %11d\n", "TOTAL", "", "", "", "", "", "", total)
	lc := LeafCostOf(p.Loom)
	fmt.Printf("leaf: %d elements/query, %d perms/query\n", lc.Elements, lc.Perms)
}

// TestProfileFixedCost prices a workload that does not depend on the shape of
// the chips: the openings machine of the test fixtures, which is also the
// inner statement TestProfileVerifierCost verifies. Comparing this across a
// change to the hashing chips isolates the change, where the verifier profile
// also moves because its inner proof moved.
func TestProfileFixedCost(t *testing.T) {
	// A config big enough that the core's padding does not dominate: deep
	// Merkle paths and many queries, so sponge blocks and path steps are of
	// the same order as in a real verifier.
	bigCfg := FixtureConfig{
		Batches:    []BatchConfig{{{LogN: 14, NumBase: 40, NumExt: 4, Shifts: []int{0, 1}}}},
		NumQueries: 24,
		Seed:       3,
	}
	for _, c := range []struct {
		label string
		cfg   FixtureConfig
	}{{"smallCfg", smallCfg}, {"bigCfg", bigCfg}} {
		p, err := openingsMachine(t, c.cfg).Compile()
		if err != nil {
			t.Fatal(err)
		}
		costOf(t, p, "openings machine ("+c.label+")")
	}
}
