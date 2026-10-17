package recursion

import (
	"fmt"
	"sort"
	"strings"
	"testing"

	loomfield "github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/poly"
)

type costRow struct {
	module                      string
	n, baseW, extW, deg, chunks int
}

func (c costRow) perRow() int { return c.baseW + 6*c.extW + 6*c.chunks }
func (c costRow) total() int  { return c.n * c.perRow() }

// TestProfileVerifierCost prints the prover-side cost of the real verifier
// circuit: committed base-equivalents per row (base + 6*ext + 6*chunks) times
// the module height.
func TestProfileVerifierCost(t *testing.T) {
	ip := vmProofs(t, 3)[0]
	v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi))
	if err != nil {
		t.Fatal(err)
	}
	p, err := v.M.Compile()
	if err != nil {
		t.Fatal(err)
	}
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
	fmt.Printf("\n=== verifier of vm (%d chips, %d committed columns)\n", len(rows), cols)
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

	e6rows, sumrows := 0, 0
	for _, in := range v.M.e6Insts {
		e6rows += len(in.rows)
	}
	sumrows = (sumChip{v.M}).rows()
	fmt.Printf("e6 instruction rows: %d; sum chip rows: %d (%d Sum calls)\n",
		e6rows, sumrows, len(v.M.sums))
	_ = strings.TrimSpace
}
