package recursion

import (
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/trace"
)

// tableVals are the indices read in table A (8 entries), as the low 3 bits of
// these values: 5 twice, entries 2, 7 and 0, others never.
var tableVals = []uint64{5, 13, 2, 7, 8}

// tableMachine builds two tables at adjacent addresses, A (8 E6 entries) and
// B (4), and looks entries of A up at indices produced by Bits, checking the
// results against Go; and one entry of B.
func tableMachine() (*builder, []ext.E6, []ext.E6) {
	r := rand.New(rand.NewPCG(11, 12))
	m := &builder{}
	var a, b []ext.E6
	var cellsA, cellsB []int
	for range 8 {
		x := randE6(r)
		a = append(a, x)
		cellsA = append(cellsA, m.input(E6Cell(x)))
	}
	for range 4 {
		x := randE6(r)
		b = append(b, x)
		cellsB = append(cellsB, m.input(E6Cell(x)))
	}
	tabA, tabB := m.Table(cellsA), m.Table(cellsB)
	for _, v := range tableVals {
		idx := m.Bits(m.input(ScalarCell(koalabear.NewElement(v))), 3).Shr[0]
		m.AssertEq(m.Lookup(tabA, idx), m.Const(E6Cell(a[v&7])))
	}
	idx := m.Bits(m.input(ScalarCell(koalabear.NewElement(6))), 2).Shr[0]
	m.AssertEq(m.Lookup(tabB, idx), m.Const(E6Cell(b[2])))
	return m, a, b
}

func TestTableLookup(t *testing.T) {
	m, _, _ := tableMachine()
	if err := compileAndProve(t, m, nil); err != nil {
		t.Fatalf("valid lookups rejected: %v", err)
	}

	// Rows: table A's entries 0..7 then B's 0..3; lookups in program order.
	rejects := map[string]func(tr trace.Trace){
		// a lookup returns another value than its entry's
		"lookup value": func(tr trace.Trace) { tr.Base["lookup.v3"][0].SetUint64(5) },
		// an entry read twice, counted once, and another one counted instead
		"entry count": func(tr trace.Trace) {
			tr.Base["table.cnt"][5].SetUint64(1)
			tr.Base["table.cnt"][6].SetUint64(1)
		},
		// a lookup at another index than its index cell's, with that entry's
		// value and the counts moved accordingly
		"lookup index": func(tr trace.Trace) {
			moveLookup(tr, 2, 2, 3) // the third lookup reads entry 2: make it entry 3
		},
		// past the end of A, into B's first entry (A's base + 8): the index
		// cell still holds 7, so the read of the index fails
		"index out of the table": func(tr trace.Trace) {
			moveLookup(tr, 3, 7, 8)
		},
	}
	for name, tamper := range rejects {
		t.Run(name, func(t *testing.T) {
			m, _, _ := tableMachine()
			if err := compileAndProve(t, m, witnessOnly(tamper)); err == nil {
				t.Fatal("tampered lookup accepted")
			}
		})
	}

	t.Run("out of range at execution", func(t *testing.T) {
		m := &builder{}
		tab := m.Table([]int{m.input(Cell{}), m.input(Cell{})})
		m.Lookup(tab, m.input(ScalarCell(koalabear.NewElement(2))))
		p, err := m.Compile()
		if err != nil {
			t.Fatal(err)
		}
		if _, err := p.Execute(m.in); err == nil {
			t.Fatal("index 2 into a table of 2 executed")
		}
	})
}

// moveLookup makes lookup row read table row to instead of from: its index,
// its value, and both entries' counts (table rows: A then B).
func moveLookup(tr trace.Trace, row, from, to int) {
	idx := &tr.Base["lookup.idx"][row]
	idx.SetUint64(idx.Uint64() + uint64(to-from))
	for j := range CellWidth {
		lane := "v" + string(rune('0'+j))
		tr.Base["lookup."+lane][row] = tr.Base["table."+lane][to]
	}
	var one koalabear.Element
	one.SetOne()
	tr.Base["table.cnt"][from].Sub(&tr.Base["table.cnt"][from], &one)
	tr.Base["table.cnt"][to].Add(&tr.Base["table.cnt"][to], &one)
}
