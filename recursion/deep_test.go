package recursion

import (
	"math/bits"
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/trace"
)

// deepMachine builds two DEEP chains of random base and Ext rows (random
// active and selected lanes, a partial cell, an all-skipped selection), and
// checks each result against Σ_i α^i·sel_i·x_i computed in Go, i counting the
// active lanes from the end of the chain.
func deepMachine() *builder {
	r := rand.New(rand.NewPCG(21, 22))
	m := &builder{}
	alphaV := randE6(r)
	alpha := m.input(E6Cell(alphaV))
	for chain := range 2 {
		var rows []DeepRow
		var want, pow ext.E6
		pow.SetOne()
		// The chain's values in decreasing index, so the sum is built from
		// the lowest index (the last lane of the last row) up.
		type term struct {
			x   ext.E6
			sel bool
		}
		var terms []term
		for i := range 6 + chain {
			if i%3 == 2 {
				x := randE6(r)
				sel := r.IntN(4) != 0
				var s uint8
				if sel {
					s = 1
				}
				rows = append(rows, DeepRow{Cell: m.input(E6Cell(x)), Ext: true, Act: 1, Sel: s})
				terms = append(terms, term{x, sel})
				continue
			}
			var c Cell
			act := uint8(r.Uint32()) | 1
			if i == 3 {
				act = 0b00011111 // a partial cell mid-chain: lanes 5..7 are padding
			}
			sel := uint8(r.Uint32()) & act
			for j := CellWidth - 1; j >= 0; j-- {
				c[j].SetUint64(r.Uint64())
				if act>>j&1 == 1 {
					var x ext.E6
					x.B0.A0 = c[j]
					terms = append(terms, term{x, sel>>j&1 == 1})
				}
			}
			rows = append(rows, DeepRow{Cell: m.input(c), Act: act, Sel: sel})
		}
		for i := len(terms) - 1; i >= 0; i-- {
			if terms[i].sel {
				var t ext.E6
				t.Mul(&pow, &terms[i].x)
				want.Add(&want, &t)
			}
			pow.Mul(&pow, &alphaV)
		}
		m.AssertEq(m.DeepHorner(alpha, rows), m.Const(E6Cell(want)))
	}
	return m
}

func TestDeepChip(t *testing.T) {
	if err := compileAndProve(t, deepMachine(), nil); err != nil {
		t.Fatalf("valid DEEP chains rejected: %v", err)
	}
	var one koalabear.Element
	one.SetOne()
	bump := func(name string, row int) func(_, w trace.Trace) {
		return witnessOnly(func(tr trace.Trace) { tr.Base[name][row].Add(&tr.Base[name][row], &one) })
	}
	rejects := map[string]func(s, w trace.Trace){
		// an intermediate h, and the last one
		"h3":     bump("deep.h3_2", 1),
		"result": bump("deep.h0_0", 5),
		// a selected lane's value
		"value": func(s, w trace.Trace) {
			for j := range CellWidth {
				if s.Base["deep.sel"+string(rune('0'+j))][1].IsOne() {
					x := w.Base["deep.x"+string(rune('0'+j))]
					x[1].Add(&x[1], &one)
					return
				}
			}
			panic("no selected lane in row 1")
		},
		// α
		"alpha": bump("deep.al4", 3),
		// a padding lane taken into account (act set in the setup)
		"padding lane": func(s, _ trace.Trace) { s.Base["deep.act6"][3].SetOne() },
		// an unselected lane added (sel set in the setup)
		"selection": func(s, _ trace.Trace) {
			for j := range CellWidth {
				col := s.Base["deep.sel"+string(rune('0'+j))]
				if s.Base["deep.act"+string(rune('0'+j))][1].IsOne() && col[1].IsZero() {
					col[1].SetOne()
					return
				}
			}
			panic("no unselected active lane in row 1")
		},
		// a chain continued from the previous one (first cleared)
		"chain start": func(s, _ trace.Trace) { s.Base["deep.first"][6].SetZero() },
	}
	for name, tamper := range rejects {
		t.Run(name, func(t *testing.T) {
			if err := compileAndProve(t, deepMachine(), tamper); err == nil {
				t.Fatal("tampered DEEP chain accepted")
			}
		})
	}
}

// TestDeepRowMasks checks that the test's rows cover what they claim.
func TestDeepRowMasks(t *testing.T) {
	m := deepMachine()
	ext, partial := 0, false
	for _, in := range m.deeps {
		for _, r := range in.rows {
			if r.Ext {
				ext++
			}
			if !r.Ext && bits.OnesCount8(r.Act) < CellWidth {
				partial = true
			}
		}
	}
	if ext == 0 || !partial {
		t.Fatalf("rows: %d Ext, partial %v", ext, partial)
	}
}
