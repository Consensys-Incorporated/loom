package recursion

import (
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/trace"
)

// TestSelect: Select picks a or b on all eight lanes; a selected value or
// bit other than the executed ones is rejected.
func TestSelect(t *testing.T) {
	build := func() *builder {
		b := &builder{}
		var a, c Cell
		for i := range CellWidth {
			a[i].SetUint64(uint64(10 + i))
			c[i].SetUint64(uint64(20 + i))
		}
		ca, cc := b.input(a), b.input(c)
		one, zero := b.input(ScalarCell(koalabear.One())), b.input(Cell{})
		b.AssertEq(b.Lanes(b.Select(one, ca, cc), 0, KindE6), b.Lanes(ca, 0, KindE6))
		b.AssertEq(b.Lanes(b.Select(zero, ca, cc), 2, KindE6), b.Lanes(cc, 2, KindE6))
		return b
	}
	if err := compileAndProve(t, build(), nil); err != nil {
		t.Fatalf("valid selections rejected: %v", err)
	}
	for name, tamper := range map[string]func(tr trace.Trace){
		// lane 7, beyond the E6 lanes the assertions read
		"lane 7": func(tr trace.Trace) { tr.Base["select.out7"][0].SetUint64(99) },
		"bit":    func(tr trace.Trace) { tr.Base["select.bit"][1].SetOne() },
	} {
		if err := compileAndProve(t, build(), witnessOnly(tamper)); err == nil {
			t.Fatalf("%s: tampered selection accepted", name)
		}
	}
}
