package zkc

import (
	"math/bits"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
)

// refFoldXInv is fri's bitReversedFoldXInv for round j of query s, N = 2^L.
func refFoldXInv(s, j, L int) koalabear.Element {
	Nj := uint64(1) << (L - j)
	g, err := koalabear.Generator(Nj)
	if err != nil {
		panic(err)
	}
	g.Inverse(&g)
	width := L - j - 1
	row := uint(s>>j) &^ 1
	exp := 0
	if width > 0 {
		exp = int(bits.Reverse(row>>1) >> (bits.UintSize - width))
	}
	var r koalabear.Element
	r.ExpInt64(g, int64(exp))
	return r
}

func TestFoldPointRecurrence(t *testing.T) {
	const L = 7
	c := foldPointConstants(L)
	for s := range 1 << L {
		var x koalabear.Element
		x.SetOne()
		for i := range c {
			if s>>(1+i)&1 == 1 {
				x.Mul(&x, &c[i])
			}
		}
		for j := 0; j < L-1; j++ {
			want := refFoldXInv(s, j, L)
			if !x.Equal(&want) {
				t.Fatalf("s=%d round %d: got %s want %s", s, j, x.String(), want.String())
			}
			x.Square(&x)
			if s>>(j+1)&1 == 1 {
				x.Neg(&x)
			}
		}
	}
}
