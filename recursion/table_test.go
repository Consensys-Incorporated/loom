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

// tableCheatMachine builds two tables, A (8 E6 entries) and B (4), and one
// lookup into A at the index input idx (the last input: witness row 12), its
// result unread, so that only the tables bus checks it. Table rows: A's
// entries 0..7, B's 8..11, padding 12..15.
func tableCheatMachine(idx uint64) *builder {
	r := rand.New(rand.NewPCG(13, 14))
	b := &builder{}
	cellsA, cellsB := make([]int, 8), make([]int, 4)
	for i := range cellsA {
		cellsA[i] = b.inputKind(E6Cell(randE6(r)), KindE6)
	}
	for i := range cellsB {
		cellsB[i] = b.inputKind(E6Cell(randE6(r)), KindE6)
	}
	tabA := b.Table(cellsA)
	b.Table(cellsB)
	b.Lookup(tabA, b.inputKind(ScalarCell(koalabear.NewElement(idx)), KindScalar))
	return b
}

func addTo(e *koalabear.Element, d int64) {
	var x koalabear.Element
	x.SetInt64(d)
	e.Add(e, &x)
}

// TestLookupOutOfTable (recursion_bugs.txt, 2): a lookup into A at index 8,
// one past its end, returning B[0], with A[1]'s count lowered and B[0]'s
// raised. The index input holds 8, so the memory balances; with entries at
// consecutive addresses (A's base + 8 is B's base), the read would balance
// against B[0]. Tagged by its table, it matches no entry.
func TestLookupOutOfTable(t *testing.T) {
	if err := compileAndProve(t, tableCheatMachine(1), nil); err != nil {
		t.Fatalf("honest lookup of A[1] rejected: %v", err)
	}
	tamper := func(tr trace.Trace) {
		addTo(&tr.Base["witness.v0"][12], 7) // the index input: 1 → 8
		addTo(&tr.Base["lookup.idx"][0], 7)
		for j := range CellWidth {
			lane := laneName("v", j)
			tr.Base["lookup."+lane][0] = tr.Base["table."+lane][8] // B[0]
		}
		addTo(&tr.Base["table.cnt"][1], -1)
		addTo(&tr.Base["table.cnt"][8], 1)
	}
	if err := compileAndProve(t, tableCheatMachine(1), witnessOnly(tamper)); err == nil {
		t.Fatal("A[8] read as B[0] accepted")
	}
}

// TestTablePaddingEntry (recursion_bugs.txt, 3): a lookup of A[0] returning a
// forged value, A[0]'s count moved to padding row 12 of the table module,
// which writes the forged value as the entry (tag 0, idx 0): its setup is
// zero, so its source read is off and its value is free. The entries'
// multiplicity is gated by active: rejected.
func TestTablePaddingEntry(t *testing.T) {
	if err := compileAndProve(t, tableCheatMachine(0), nil); err != nil {
		t.Fatalf("honest lookup of A[0] rejected: %v", err)
	}
	tamper := func(tr trace.Trace) {
		addTo(&tr.Base["lookup.v3"][0], 5)
		for j := range CellWidth {
			lane := laneName("v", j)
			tr.Base["table."+lane][12] = tr.Base["lookup."+lane][0]
		}
		addTo(&tr.Base["table.cnt"][0], -1)
		addTo(&tr.Base["table.cnt"][12], 1)
	}
	if err := compileAndProve(t, tableCheatMachine(0), witnessOnly(tamper)); err == nil {
		t.Fatal("a forged entry on a padding row accepted")
	}
}
