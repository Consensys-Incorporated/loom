package zkc

import (
	"fmt"
	"math/big"
	"math/rand/v2"
	"strings"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
)

func randE6(rng *rand.Rand) ext.E6 {
	var x ext.E6
	for _, c := range []*koalabear.Element{&x.B0.A0, &x.B0.A1, &x.B1.A0, &x.B1.A1, &x.B2.A0, &x.B2.A1} {
		c.SetUint64(rng.Uint64())
	}
	return x
}

func bigPow2(k int) *big.Int {
	return new(big.Int).Lsh(big.NewInt(1), uint(k))
}

// hexWords encodes 32-bit words as a zkc JSON hex byte string.
func hexWords(words []uint32) string {
	var sb strings.Builder
	sb.WriteString("0x")
	for _, w := range words {
		fmt.Fprintf(&sb, "%08x", w)
	}
	return sb.String()
}
