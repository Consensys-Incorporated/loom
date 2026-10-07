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

// hornerBaseMachine runs HornerBase on chains of the given lengths and checks
// every result against a constant computed in Go.
func hornerBaseMachine(lengths ...int) *builder {
	r := rand.New(rand.NewPCG(3, 5))
	m := &builder{}
	y := randE6(r)
	ya := m.input(E6Cell(y))
	for _, n := range lengths {
		coeffs := make([]koalabear.Element, n)
		addrs := make([]int, n)
		for i := range coeffs {
			coeffs[i].SetUint64(r.Uint64())
			addrs[i] = m.input(ScalarCell(coeffs[i]))
		}
		m.AssertEq(m.HornerBase(ya, addrs), m.Const(E6Cell(hornerBaseWant(y, coeffs))))
	}
	return m
}

func TestHornerBase(t *testing.T) {
	if err := compileAndProve(t, hornerBaseMachine(1, 2, 3, 7, 16), nil); err != nil {
		t.Fatalf("valid Horner chains rejected: %v", err)
	}
}

// TestHornerBaseMatchesE6 checks HornerBase against the e6 chip's Horner on
// the same coefficients, lifted to E6 cells.
func TestHornerBaseMatchesE6(t *testing.T) {
	r := rand.New(rand.NewPCG(9, 11))
	m := &builder{}
	y := randE6(r)
	ya := m.input(E6Cell(y))
	const n = 12
	base := make([]int, n)
	lifted := make([]int, n)
	for i := range n {
		var c koalabear.Element
		c.SetUint64(r.Uint64())
		base[i] = m.input(ScalarCell(c))
		var e ext.E6
		e.B0.A0 = c
		lifted[i] = m.input(E6Cell(e))
	}
	m.AssertEq(m.HornerBase(ya, base), m.Horner(ya, lifted))
	if err := compileAndProve(t, m, nil); err != nil {
		t.Fatalf("HornerBase disagrees with the e6 Horner: %v", err)
	}
}

// TestHornerBaseRejects checks that the chain is actually constrained.
func TestHornerBaseRejects(t *testing.T) {
	// chains of 3 and 4: rows 0..2 are the first chain, 3..6 the second.
	rejects := map[string]func(trace.Trace){
		// a tampered accumulator inside a chain
		"accumulator": func(tr trace.Trace) { tr.Base["horner.o0"][1].SetUint64(5) },
		// a tampered accumulator on the first row of a chain
		"first row": func(tr trace.Trace) { tr.Base["horner.o0"][3].SetUint64(5) },
		// a coefficient that does not match the cell read on the bus
		"coefficient": func(tr trace.Trace) { tr.Base["horner.c"][2].SetUint64(5) },
		// a multiplier that does not match the cell read on the bus
		"multiplier": func(tr trace.Trace) { tr.Base["horner.y0"][1].SetUint64(5) },
		// a nonzero high lane on the first row, which must be c·e0
		"first lane": func(tr trace.Trace) { tr.Base["horner.o3"][0].SetUint64(5) },
		// the result cell, which the last row writes to the bus
		"result": func(tr trace.Trace) { tr.Base["horner.o1"][6].SetUint64(5) },
	}
	for name, tamper := range rejects {
		t.Run(name, func(t *testing.T) {
			err := compileAndProve(t, hornerBaseMachine(3, 4), witnessOnly(tamper))
			if err == nil {
				t.Fatal("tampered chain accepted")
			}
			t.Logf("rejected: %v", err)
		})
	}
}

// TestHornerBasePadding checks chains whose total length is not a power of
// two, so the chip has padding rows.
func TestHornerBasePadding(t *testing.T) {
	for _, n := range []int{5, 9, 17, 33} {
		t.Run(fmt.Sprint(n), func(t *testing.T) {
			if err := compileAndProve(t, hornerBaseMachine(n), nil); err != nil {
				t.Fatalf("chain of %d rejected: %v", n, err)
			}
		})
	}
}
