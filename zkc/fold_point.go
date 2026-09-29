package zkc

import (
	"github.com/consensys/gnark-crypto/field/koalabear"
)

// foldPointConstants returns c_i = ω_N^{-2^(L-2-i)} for i = 0..L-2, where
// N = 2^L and ω_N generates the size-N subgroup. With them, the FRI folding
// point of round 0 for query s is
//
//	xInv_0 = Π_{i} (s_{1+i} ? c_i : 1)
//
// and the following rounds satisfy xInv_{j+1} = xInv_j² · (−1)^{s_{j+1}},
// where s_k is bit k of s. This matches fri's bitReversedFoldXInv:
// xInv_j = (ω_{N_j}^{-1})^{bitrev(s >> (j+1))} over log2(N_j/2) bits.
func foldPointConstants(L int) []koalabear.Element {
	g, err := koalabear.Generator(uint64(1) << L)
	if err != nil {
		panic(err)
	}
	var gInv koalabear.Element
	gInv.Inverse(&g)
	res := make([]koalabear.Element, L-1)
	for i := range res {
		res[i].Exp(gInv, bigPow2(L-2-i))
	}
	return res
}
