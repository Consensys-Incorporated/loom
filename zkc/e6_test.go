package zkc

import (
	"encoding/binary"
	"fmt"
	"math/rand/v2"
	"slices"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
)

// e6Words returns the six canonical words of x, in zkc layout.
func e6Words(x ext.E6) []uint32 {
	c := []koalabear.Element{x.B0.A0, x.B0.A1, x.B1.A0, x.B1.A1, x.B2.A0, x.B2.A1}
	res := make([]uint32, 6)
	for i := range c {
		res[i] = uint32(c[i].Uint64())
	}
	return res
}

// decodeWords decodes a zkc output byte string of big-endian 32-bit words.
func decodeWords(b []byte) []uint32 {
	res := make([]uint32, len(b)/4)
	for i := range res {
		res[i] = binary.BigEndian.Uint32(b[4*i:])
	}
	return res
}

// e6Driver reads, per case, x (6 words), y (6), c (1) and inv(x) (6), and
// writes x·y, x+y, x−y, c·x (24 words); it also asserts x·inv(x) = 1.
const e6Driver = `
input e6_n(address:u1) -> (n:u16)
input e6_in(address:u16) -> (w:u32)
output e6_out(address:u16) -> (w:u32)

fn main() {
    var n:u16 = e6_n[0]
    for i:u16 = 0; i < n; i = i + 1 {
        check(i * 19, i * 24)
    }
}

fn check(in:u16, out:u16) {
    var x0:𝔽 = e6_in[in + 0] as 𝔽
    var x1:𝔽 = e6_in[in + 1] as 𝔽
    var x2:𝔽 = e6_in[in + 2] as 𝔽
    var x3:𝔽 = e6_in[in + 3] as 𝔽
    var x4:𝔽 = e6_in[in + 4] as 𝔽
    var x5:𝔽 = e6_in[in + 5] as 𝔽
    var y0:𝔽 = e6_in[in + 6] as 𝔽
    var y1:𝔽 = e6_in[in + 7] as 𝔽
    var y2:𝔽 = e6_in[in + 8] as 𝔽
    var y3:𝔽 = e6_in[in + 9] as 𝔽
    var y4:𝔽 = e6_in[in + 10] as 𝔽
    var y5:𝔽 = e6_in[in + 11] as 𝔽
    var c:𝔽 = e6_in[in + 12] as 𝔽
    e6_assert_inv(x0, x1, x2, x3, x4, x5,
        e6_in[in + 13] as 𝔽, e6_in[in + 14] as 𝔽, e6_in[in + 15] as 𝔽,
        e6_in[in + 16] as 𝔽, e6_in[in + 17] as 𝔽, e6_in[in + 18] as 𝔽)
    var z0:𝔽, z1:𝔽, z2:𝔽, z3:𝔽, z4:𝔽, z5:𝔽
    z0, z1, z2, z3, z4, z5 = e6_mul(x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5)
    write6(out, z0, z1, z2, z3, z4, z5)
    z0, z1, z2, z3, z4, z5 = e6_add(x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5)
    write6(out + 6, z0, z1, z2, z3, z4, z5)
    z0, z1, z2, z3, z4, z5 = e6_sub(x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5)
    write6(out + 12, z0, z1, z2, z3, z4, z5)
    z0, z1, z2, z3, z4, z5 = e6_mul_base(x0, x1, x2, x3, x4, x5, c)
    write6(out + 18, z0, z1, z2, z3, z4, z5)
}

#[inline]
fn write6(at:u16, z0:𝔽, z1:𝔽, z2:𝔽, z3:𝔽, z4:𝔽, z5:𝔽) {
    e6_out[at + 0] = z0 as u32
    e6_out[at + 1] = z1 as u32
    e6_out[at + 2] = z2 as u32
    e6_out[at + 3] = z3 as u32
    e6_out[at + 4] = z4 as u32
    e6_out[at + 5] = z5 as u32
}
`

func TestE6(t *testing.T) {
	const n = 4
	rng := rand.New(rand.NewPCG(3, 4))
	var in, want []uint32
	for range n {
		x, y := randE6(rng), randE6(rng)
		var c koalabear.Element
		c.SetUint64(rng.Uint64())
		var inv, mul, add, sub, mulBase ext.E6
		inv.Inverse(&x)
		mul.Mul(&x, &y)
		add.Add(&x, &y)
		sub.Sub(&x, &y)
		mulBase.MulByElement(&x, &c)

		in = append(in, e6Words(x)...)
		in = append(in, e6Words(y)...)
		in = append(in, uint32(c.Uint64()))
		in = append(in, e6Words(inv)...)
		for _, z := range []ext.E6{mul, add, sub, mulBase} {
			want = append(want, e6Words(z)...)
		}
	}

	files := writeZkc(t, map[string]string{"e6.zkc": E6Source(), "main.zkc": e6Driver})
	res, err := zkcv.RunWith([]byte(fmt.Sprintf(`{"e6_n": "0x%04x", "e6_in": "%s"}`, n, hexWords(in))), Gadgets(), files...)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("\n%s", zkcv.FormatStats(res.Stats))
	if got := decodeWords(res.Outputs["e6_out"]); !slices.Equal(got, want) {
		t.Fatalf("e6_out mismatch:\ngot  %v\nwant %v", got, want)
	}
}
