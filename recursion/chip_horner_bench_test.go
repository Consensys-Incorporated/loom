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

// lanesE6 asks for the e6 chip's generic Horner instead of the Horner chip.
const lanesE6 = 0

// randCoeffs returns n random base coefficients.
func randCoeffs(r *rand.Rand, n int) []koalabear.Element {
	res := make([]koalabear.Element, n)
	for i := range res {
		res[i].SetUint64(r.Uint64())
	}
	return res
}

// hornerChain records one accumulation of n base coefficients with y, either
// on the e6 chip (lanes == lanesE6, one E6 input cell per coefficient, as
// Machine.Horner needs) or on the Horner chip at the given lane count (the
// coefficients packed lanes per cell, as they arrive from an opened leaf row).
func hornerChain(b *builder, r *rand.Rand, y, n, lanes int) int {
	coeffs := randCoeffs(r, n)
	if lanes == lanesE6 {
		addrs := make([]int, n)
		for i, c := range coeffs {
			var e ext.E6
			e.B0.A0 = c
			addrs[i] = b.input(E6Cell(e))
		}
		return b.Horner(y, addrs)
	}
	return b.HornerPacked(y, packCoeffs(b, coeffs, lanes))
}

func newBuilder(lanes int) *builder {
	b := &builder{}
	if lanes != lanesE6 {
		b.HornerLanes = lanes
	}
	return b
}

// bridgeMachine models the E6 work of the DEEP bridge: per query and shift,
// one accumulation of the opened base values with alpha_DEEP, a subtraction
// and a division.
func bridgeMachine(nQueries, nPolys, nShifts, lanes int) *builder {
	r := rand.New(rand.NewPCG(11, 12))
	b := newBuilder(lanes)
	e6 := func() int { return b.input(E6Cell(randE6(r))) }
	alpha := e6()
	for range nQueries {
		var terms []int
		for range nShifts {
			num := hornerChain(b, r, alpha, nPolys, lanes)
			terms = append(terms, b.Div(b.Sub(num, e6()), e6()))
		}
		acc := terms[0]
		for _, x := range terms[1:] {
			acc = b.Add(acc, x)
		}
		// The fold chain is identical in every variant and needs a consistent
		// witness, so it is left out; this keeps the DEEP term read.
		b.AssertEq(acc, acc)
	}
	return b
}

// hornerOnlyMachine builds nChains accumulations of coeffs coefficients and
// nothing else.
func hornerOnlyMachine(nChains, coeffs, lanes int) *builder {
	r := rand.New(rand.NewPCG(21, 22))
	b := newBuilder(lanes)
	alpha := b.input(E6Cell(randE6(r)))
	for range nChains {
		hornerChain(b, r, alpha, coeffs, lanes)
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

func costsOf(p *Program) []chipCost {
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
			for _, colRef := range round.Staged {
				if colRef.Module != mod {
					continue
				}
				if colRef.Field == loomfield.Ext {
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

func laneLabel(lanes int) string {
	if lanes == lanesE6 {
		return "e6 Horner (baseline)"
	}
	return fmt.Sprintf("horner chip, %d lane(s)/row", lanes)
}

var laneSweep = []int{lanesE6, 1, 2, 4, 8}

// TestHornerSweepIsolated reports the accumulation chip's own cost at every
// lane count, with 8192 coefficients spread over 64 chains.
func TestHornerSweepIsolated(t *testing.T) {
	const (
		nChains = 64
		coeffs  = 128
		reps    = 3
	)
	type row struct {
		lanes, acc, total int
		rows              int
		wall              time.Duration
	}
	var out []row
	for _, lanes := range laneSweep {
		p, r := hornerOnlyMachine(nChains, coeffs, lanes).run(t)
		cs := costsOf(p)
		total := reportCosts(laneLabel(lanes), cs)
		rec := row{lanes: lanes, total: total}
		mod := hornerMod
		if lanes == lanesE6 {
			mod = e6Mod
		}
		for _, c := range cs {
			if c.module == mod {
				rec.acc, rec.rows = c.total(), c.n
			}
		}
		rec.wall = proveTime(t, p, r, reps)
		fmt.Printf("prove+verify (best of %d): %v\n", reps, rec.wall)
		out = append(out, rec)
	}
	fmt.Printf("\n=== %d coefficients, accumulation chip + witness chip\n", nChains*coeffs)
	fmt.Printf("%-30s %7s %10s %10s %10s %9s\n", "variant", "rows", "chip cost", "per coeff", "total", "wall")
	for _, x := range out {
		fmt.Printf("%-30s %7d %10d %10.1f %10d %9v  (%+.1f%% total)\n",
			laneLabel(x.lanes), x.rows, x.acc, float64(x.acc)/float64(nChains*coeffs), x.total, x.wall.Round(time.Millisecond),
			100*float64(x.total-out[0].total)/float64(out[0].total))
	}
}

// TestHornerSweepBridge reports the same sweep on the DEEP-bridge workload.
func TestHornerSweepBridge(t *testing.T) {
	const (
		nQueries = 32
		nPolys   = 72
		nShifts  = 2
		reps     = 3
	)
	type row struct {
		lanes, total int
		wall         time.Duration
	}
	var out []row
	for _, lanes := range laneSweep {
		p, r := bridgeMachine(nQueries, nPolys, nShifts, lanes).run(t)
		total := reportCosts(laneLabel(lanes), costsOf(p))
		wall := proveTime(t, p, r, reps)
		fmt.Printf("prove+verify (best of %d): %v\n", reps, wall)
		out = append(out, row{lanes, total, wall})
	}
	fmt.Printf("\n=== DEEP bridge: %d queries x %d polys x %d shifts\n", nQueries, nPolys, nShifts)
	fmt.Printf("%-30s %10s %9s %9s %8s\n", "variant", "total", "vs base", "wall", "vs base")
	for _, x := range out {
		fmt.Printf("%-30s %10d %8.1f%% %9v %7.1f%%\n", laneLabel(x.lanes), x.total,
			100*float64(x.total-out[0].total)/float64(out[0].total),
			x.wall.Round(time.Millisecond),
			100*float64(x.wall-out[0].wall)/float64(out[0].wall))
	}
}
