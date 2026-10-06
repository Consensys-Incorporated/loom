package recursion

import (
	"fmt"
	"math/rand/v2"
	"sort"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom"
	loomfield "github.com/consensys/loom/field"
	"github.com/consensys/loom/public"
)

// bridgeMachine models the E6 work of the DEEP bridge: for each query and
// each shift, one Horner accumulation of the opened base values with
// alpha_DEEP, a subtraction and a division; then the fold chain of the query.
//
// useBase picks the Horner chip (base coefficients) over the e6 chip's
// generic Horner. Both variants allocate the same number of input cells, so
// the witness chip is identical and only the accumulation differs.
func bridgeMachine(nQueries, nPolys, nShifts int, useBase bool) *builder {
	r := rand.New(rand.NewPCG(11, 12))
	b := &builder{}
	e6 := func() int { return b.input(E6Cell(randE6(r))) }

	alpha := e6()
	for range nQueries {
		var terms []int
		for range nShifts {
			coeffs := make([]int, nPolys)
			for i := range coeffs {
				if useBase {
					var c koalabear.Element
					c.SetUint64(r.Uint64())
					coeffs[i] = b.input(ScalarCell(c))
				} else {
					// the same opened base value, lifted into an E6 cell
					var e ext.E6
					e.B0.A0.SetUint64(r.Uint64())
					coeffs[i] = b.input(E6Cell(e))
				}
			}
			var num int
			if useBase {
				num = b.HornerBase(alpha, coeffs)
			} else {
				num = b.Horner(alpha, coeffs)
			}
			terms = append(terms, b.Div(b.Sub(num, e6()), e6()))
		}
		acc := terms[0]
		for _, x := range terms[1:] {
			acc = b.Add(acc, x)
		}
		// The fold chain is identical in both variants and needs a consistent
		// witness, so it is left out of the comparison; _ = acc keeps the
		// accumulated DEEP term read.
		b.AssertEq(acc, acc)
	}
	return b
}

// chipCost is the per-module cost model: committed base-equivalents per row
// (base width + 6·ext width + 6·NextPow2(degree) for the AIR quotient
// chunks), times the module height.
type chipCost struct {
	module         string
	n, baseW, extW int
	deg, setupW    int
}

func (c chipCost) perRow() int { return c.baseW + 6*c.extW + 6*nextPow2(c.deg) }

func (c chipCost) total() int { return c.n * c.perRow() }

func nextPow2(n int) int {
	p := 1
	for p < n {
		p *= 2
	}
	return p
}

func costsOf(p *Program, r *Run) []chipCost {
	var res []chipCost
	for mod, m := range p.Loom.Modules {
		c := chipCost{module: mod, n: m.N}
		if m.VanishingRelation != nil {
			c.deg = m.VanishingRelation.Degree()
		}
		for name := range p.Setup.Base {
			if moduleOf(name) == mod {
				c.setupW++
			}
		}
		for _, round := range p.Loom.Rounds {
			for _, col := range round.Staged {
				if col.Module != mod {
					continue
				}
				if col.Field == loomfield.Ext {
					c.extW++
				} else {
					c.baseW++
				}
			}
		}
		res = append(res, c)
	}
	sort.Slice(res, func(i, j int) bool { return res[i].total() > res[j].total() })
	return res
}

func reportCosts(label string, cs []chipCost) int {
	total := 0
	for _, c := range cs {
		total += c.total()
	}
	fmt.Printf("\n--- %s\n%-10s %7s %6s %5s %5s %8s %10s %6s\n",
		label, "chip", "rows", "base", "ext", "deg", "per-row", "cost", "share")
	for _, c := range cs {
		fmt.Printf("%-10s %7d %6d %5d %5d %8d %10d %5.1f%%\n",
			c.module, c.n, c.baseW, c.extW, c.deg, c.perRow(), c.total(),
			100*float64(c.total())/float64(total))
	}
	fmt.Printf("%-10s %7s %6s %5s %5s %8s %10d\n", "TOTAL", "", "", "", "", "", total)
	return total
}

// proveTime runs setup once, then times n Prove+Verify rounds and returns the
// best wall time.
func proveTime(t *testing.T, p *Program, r *Run, n int) time.Duration {
	t.Helper()
	pk, vk := keys(t, p)
	st := loom.Statement{Program: p.Loom, VerificationKey: vk, PublicInputs: public.Inputs{}}
	w := loom.Witness{Trace: r.Trace, ProvingKey: pk}
	best := time.Duration(1<<62 - 1)
	for range n {
		start := time.Now()
		prf, err := loom.Prove(st, w)
		if err != nil {
			t.Fatal(err)
		}
		d := time.Since(start)
		if err := loom.Verify(st, prf); err != nil {
			t.Fatal(err)
		}
		best = min(best, d)
	}
	return best
}

// TestHornerBaseSaving compares the two variants on the same workload.
func TestHornerBaseSaving(t *testing.T) {
	const (
		nQueries = 32
		nPolys   = 72
		nShifts  = 2
		reps     = 3
	)
	var cost [2]int
	var wall [2]time.Duration
	for i, useBase := range []bool{false, true} {
		b := bridgeMachine(nQueries, nPolys, nShifts, useBase)
		p, r := b.run(t)
		label := "e6 Horner (baseline)"
		if useBase {
			label = "HornerBase chip"
		}
		cost[i] = reportCosts(label, costsOf(p, r))
		wall[i] = proveTime(t, p, r, reps)
		fmt.Printf("prove+verify (best of %d): %v\n", reps, wall[i])
	}
	fmt.Printf("\n=== cost  %d -> %d  (%.1f%%)\n", cost[0], cost[1],
		100*float64(cost[1]-cost[0])/float64(cost[0]))
	fmt.Printf("=== wall  %v -> %v  (%.1f%%)\n", wall[0], wall[1],
		100*float64(wall[1]-wall[0])/float64(wall[0]))
}

// hornerOnlyMachine builds nChains Horner chains of length coeffs and nothing
// else, so the accumulation chip is the only difference between variants.
func hornerOnlyMachine(nChains, coeffs int, useBase bool) *builder {
	r := rand.New(rand.NewPCG(21, 22))
	b := &builder{}
	alpha := b.input(E6Cell(randE6(r)))
	for range nChains {
		addrs := make([]int, coeffs)
		for i := range addrs {
			var c koalabear.Element
			c.SetUint64(r.Uint64())
			if useBase {
				addrs[i] = b.input(ScalarCell(c))
			} else {
				var e ext.E6
				e.B0.A0 = c
				addrs[i] = b.input(E6Cell(e))
			}
		}
		if useBase {
			b.HornerBase(alpha, addrs)
		} else {
			b.Horner(alpha, addrs)
		}
	}
	return b
}

// TestHornerBaseIsolated reports the accumulation chip's own cost, with the
// chains sized to fill the module exactly (no padding on either side).
func TestHornerBaseIsolated(t *testing.T) {
	const (
		nChains = 64
		coeffs  = 128 // 64*128 = 8192 rows exactly
		reps    = 3
	)
	var acc [2]int
	var wall [2]time.Duration
	for i, useBase := range []bool{false, true} {
		p, r := hornerOnlyMachine(nChains, coeffs, useBase).run(t)
		label, mod := "e6 Horner (baseline)", e6Mod
		if useBase {
			label, mod = "HornerBase chip", hornerMod
		}
		cs := costsOf(p, r)
		reportCosts(label, cs)
		for _, c := range cs {
			if c.module == mod {
				acc[i] = c.total()
			}
		}
		wall[i] = proveTime(t, p, r, reps)
		fmt.Printf("prove+verify (best of %d): %v\n", reps, wall[i])
	}
	fmt.Printf("\n=== accumulation chip  %d -> %d  (%.1f%%)\n", acc[0], acc[1],
		100*float64(acc[1]-acc[0])/float64(acc[0]))
	fmt.Printf("=== wall (incl. unchanged witness chip)  %v -> %v  (%.1f%%)\n", wall[0], wall[1],
		100*float64(wall[1]-wall[0])/float64(wall[0]))
}
