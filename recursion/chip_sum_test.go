package recursion

import (
	"fmt"
	"math/rand/v2"
	"testing"

	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/trace"
)

// sumMachine sums a chain per length and checks each total against a constant
// computed in Go.
func sumMachine(k int, lengths ...int) *builder {
	r := rand.New(rand.NewPCG(17, 19))
	b := &builder{}
	b.SumLanes = k
	for _, n := range lengths {
		addrs := make([]int, n)
		var want ext.E6
		for i := range addrs {
			v := randE6(r)
			addrs[i] = b.input(E6Cell(v))
			want.Add(&want, &v)
		}
		b.AssertEq(b.Sum(addrs), b.Const(E6Cell(want)))
	}
	return b
}

func TestSum(t *testing.T) {
	for _, k := range []int{1, 2, 3, 4, 8} {
		t.Run(fmt.Sprintf("lanes=%d", k), func(t *testing.T) {
			// lengths on, below and above the row boundary
			if err := compileAndProve(t, sumMachine(k, 2, 3, 7, 8, 9, 16, 17, 46), nil); err != nil {
				t.Fatalf("valid sums rejected: %v", err)
			}
		})
	}
}

// TestSumPadding exercises chains whose row count is not a power of two.
func TestSumPadding(t *testing.T) {
	for _, n := range []int{5, 9, 33, 46, 100} {
		t.Run(fmt.Sprint(n), func(t *testing.T) {
			if err := compileAndProve(t, sumMachine(8, n), nil); err != nil {
				t.Fatalf("chain of %d rejected: %v", n, err)
			}
		})
	}
}

// TestSumRejects checks that every column of the chain is constrained.
func TestSumRejects(t *testing.T) {
	const k = 4
	// chains of 8 and 12: rows 0..1 are the first chain, 2..4 the second.
	rejects := map[string]func(trace.Trace){
		"running total":    func(tr trace.Trace) { tr.Base["sum.o0"][1].SetUint64(5) },
		"first row":        func(tr trace.Trace) { tr.Base["sum.o0"][2].SetUint64(5) },
		"term lane 0":      func(tr trace.Trace) { tr.Base["sum.x0_0"][1].SetUint64(5) },
		"term lane k-1":    func(tr trace.Trace) { tr.Base[fmt.Sprintf("sum.x%d_0", k-1)][0].SetUint64(5) },
		"term high lane":   func(tr trace.Trace) { tr.Base["sum.x1_3"][1].SetUint64(5) },
		"result high lane": func(tr trace.Trace) { tr.Base["sum.o4"][4].SetUint64(5) },
	}
	for name, tamper := range rejects {
		t.Run(name, func(t *testing.T) {
			err := compileAndProve(t, sumMachine(k, 8, 12), witnessOnly(tamper))
			if err == nil {
				t.Fatal("tampered sum accepted")
			}
			t.Logf("rejected: %v", err)
		})
	}
}

// TestSumMatchesE6 checks Sum against a chain of e6 Adds on the same terms.
func TestSumMatchesE6(t *testing.T) {
	for _, k := range []int{1, 4, 8} {
		t.Run(fmt.Sprintf("lanes=%d", k), func(t *testing.T) {
			r := rand.New(rand.NewPCG(23, 29))
			b := &builder{}
			b.SumLanes = k
			const n = 13
			addrs := make([]int, n)
			for i := range addrs {
				addrs[i] = b.input(E6Cell(randE6(r)))
			}
			acc := addrs[0]
			for _, a := range addrs[1:] {
				acc = b.Add(acc, a)
			}
			b.AssertEq(b.Sum(addrs), acc)
			if err := compileAndProve(t, b, nil); err != nil {
				t.Fatalf("Sum disagrees with the e6 Add chain: %v", err)
			}
		})
	}
}

// TestSumPartialLastRow covers a chain whose last row is partly empty, where
// the unused lanes must read nothing and contribute nothing.
func TestSumPartialLastRow(t *testing.T) {
	// 9 terms at 8 lanes: the second row carries one term and 7 empty lanes.
	b := sumMachine(8, 9)
	p, r := b.run(t)
	if got := (sumChip{&b.Machine}).rows(); got != 2 {
		t.Fatalf("rows = %d, want 2", got)
	}
	for j := 1; j < 8; j++ {
		if v := p.Setup.Base[fmt.Sprintf("sum.%s", sumSelName(j))][1]; !v.IsZero() {
			t.Fatalf("lane %d of the partial row is selected", j)
		}
	}
	if err := prove(t, p, r); err != nil {
		t.Fatalf("partial last row rejected: %v", err)
	}
}
