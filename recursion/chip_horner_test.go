package recursion

import (
	"fmt"
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/trace"
)

// hornerBaseWant returns Σ_i coeffs[i]·y^(len−1−i) in E6, the coefficients
// being base elements.
func hornerBaseWant(y ext.E6, coeffs []koalabear.Element) ext.E6 {
	var z ext.E6
	for i, c := range coeffs {
		if i > 0 {
			z.Mul(&z, &y)
		}
		z.B0.A0.Add(&z.B0.A0, &c)
	}
	return z
}

// packCoeffs allocates the input cells of coeffs packed k per cell, front
// padded with zero coefficients to a whole number of cells.
func packCoeffs(b *builder, coeffs []koalabear.Element, k int) []int {
	pad := (k - len(coeffs)%k) % k
	all := make([]koalabear.Element, pad+len(coeffs))
	copy(all[pad:], coeffs)
	cells := make([]int, 0, len(all)/k)
	for i := 0; i < len(all); i += k {
		var c Cell
		copy(c[:k], all[i:i+k])
		cells = append(cells, b.input(c))
	}
	return cells
}

// hornerMachine runs a chain per length and checks each result against a
// constant computed in Go.
func hornerMachine(k int, lengths ...int) *builder {
	r := rand.New(rand.NewPCG(3, 5))
	b := &builder{}
	b.HornerLanes = k
	y := randE6(r)
	ya := b.input(E6Cell(y))
	for _, n := range lengths {
		coeffs := make([]koalabear.Element, n)
		for i := range coeffs {
			coeffs[i].SetUint64(r.Uint64())
		}
		cells := packCoeffs(b, coeffs, k)
		b.AssertEq(b.HornerPacked(ya, cells), b.Const(E6Cell(hornerBaseWant(y, coeffs))))
	}
	return b
}

func TestHornerPacked(t *testing.T) {
	for _, k := range []int{1, 2, 3, 4, 8} {
		t.Run(fmt.Sprintf("lanes=%d", k), func(t *testing.T) {
			// lengths that straddle cell boundaries in both directions
			if err := compileAndProve(t, hornerMachine(k, 1, 2, 3, 7, 8, 9, 16, 17), nil); err != nil {
				t.Fatalf("valid Horner chains rejected: %v", err)
			}
		})
	}
}

// TestHornerBaseUnbatched checks that HornerBase still drives the chip at one
// lane per row.
func TestHornerBaseUnbatched(t *testing.T) {
	r := rand.New(rand.NewPCG(31, 37))
	b := &builder{}
	b.HornerLanes = 1
	y := randE6(r)
	ya := b.input(E6Cell(y))
	coeffs := make([]koalabear.Element, 11)
	addrs := make([]int, len(coeffs))
	for i := range coeffs {
		coeffs[i].SetUint64(r.Uint64())
		addrs[i] = b.input(ScalarCell(coeffs[i]))
	}
	b.AssertEq(b.HornerBase(ya, addrs), b.Const(E6Cell(hornerBaseWant(y, coeffs))))
	if err := compileAndProve(t, b, nil); err != nil {
		t.Fatalf("valid HornerBase chain rejected: %v", err)
	}
}

// TestHornerPackedMatchesE6 checks the chip against the e6 chip's Horner on
// the same coefficients, lifted to E6 cells.
func TestHornerPackedMatchesE6(t *testing.T) {
	for _, k := range []int{1, 4, 8} {
		t.Run(fmt.Sprintf("lanes=%d", k), func(t *testing.T) {
			r := rand.New(rand.NewPCG(9, 11))
			b := &builder{}
			b.HornerLanes = k
			y := randE6(r)
			ya := b.input(E6Cell(y))
			const n = 12
			coeffs := make([]koalabear.Element, n)
			lifted := make([]int, n)
			for i := range coeffs {
				coeffs[i].SetUint64(r.Uint64())
				var e ext.E6
				e.B0.A0 = coeffs[i]
				lifted[i] = b.input(E6Cell(e))
			}
			b.AssertEq(b.HornerPacked(ya, packCoeffs(b, coeffs, k)), b.Horner(ya, lifted))
			if err := compileAndProve(t, b, nil); err != nil {
				t.Fatalf("HornerPacked disagrees with the e6 Horner: %v", err)
			}
		})
	}
}

// TestHornerPackedRejects checks that the chain, the coefficients and the
// derived powers are all constrained.
func TestHornerPackedRejects(t *testing.T) {
	const k = 4
	// chains of 8 and 12 coefficients: rows 0..1 are the first chain, 2..4
	// the second.
	rejects := map[string]func(trace.Trace){
		"accumulator":      func(tr trace.Trace) { tr.Base["horner.o0"][1].SetUint64(5) },
		"first row":        func(tr trace.Trace) { tr.Base["horner.o0"][2].SetUint64(5) },
		"coefficient":      func(tr trace.Trace) { tr.Base["horner.c0"][1].SetUint64(5) },
		"high coefficient": func(tr trace.Trace) { tr.Base["horner.c3"][0].SetUint64(5) },
		"multiplier":       func(tr trace.Trace) { tr.Base["horner.p1_0"][1].SetUint64(5) },
		// a derived power, which the in-row recurrence fixes
		"power 2": func(tr trace.Trace) { tr.Base["horner.p2_0"][1].SetUint64(5) },
		"power k": func(tr trace.Trace) { tr.Base[fmt.Sprintf("horner.p%d_1", k)][1].SetUint64(5) },
		// the result cell, which the last row writes to the bus
		"result": func(tr trace.Trace) { tr.Base["horner.o1"][4].SetUint64(5) },
	}
	for name, tamper := range rejects {
		t.Run(name, func(t *testing.T) {
			err := compileAndProve(t, hornerMachine(k, 8, 12), witnessOnly(tamper))
			if err == nil {
				t.Fatal("tampered chain accepted")
			}
			t.Logf("rejected: %v", err)
		})
	}
}

// TestHornerPackedPadding exercises chains whose cell count is not a power of
// two, so the chip has padding rows.
func TestHornerPackedPadding(t *testing.T) {
	for _, n := range []int{5, 9, 17, 33, 40} {
		t.Run(fmt.Sprint(n), func(t *testing.T) {
			if err := compileAndProve(t, hornerMachine(8, n), nil); err != nil {
				t.Fatalf("chain of %d rejected: %v", n, err)
			}
		})
	}
}
