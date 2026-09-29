package zkc

import (
	"fmt"
	"math/rand/v2"
	"slices"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
)

// TestChallenge checks a chain of three challenges against the Go transcript:
// "zeta" binds two digests, "alpha_DEEP" binds 13 elements, and "fri_query_1"
// binds the previous digest explicitly, as the FRI query chain does.
func TestChallenge(t *testing.T) {
	rng := rand.New(rand.NewPCG(7, 8))
	randElems := func(n int) []koalabear.Element {
		res := make([]koalabear.Element, n)
		for i := range res {
			res[i].SetUint64(rng.Uint64())
		}
		return res
	}
	b0, b1 := randElems(16), randElems(13)

	h := hash.NewPoseidon2SpongeHasher()
	fs := fiatshamir.NewTranscript(&h, "zeta", "alpha_DEEP", "fri_query_1")
	must := func(err error) {
		if err != nil {
			t.Fatal(err)
		}
	}
	must(fs.Bind("zeta", b0))
	zeta, err := fs.ComputeChallenge("zeta")
	must(err)
	must(fs.Bind("alpha_DEEP", b1))
	alpha, err := fs.ComputeChallenge("alpha_DEEP")
	must(err)
	must(fs.Bind("fri_query_1", alpha[:]))
	q1, err := fs.ComputeChallenge("fri_query_1")
	must(err)

	var in, want []uint32
	for _, xs := range [][]koalabear.Element{b0, b1} {
		for _, x := range xs {
			in = append(in, uint32(x.Uint64()))
		}
	}
	for _, d := range [][8]koalabear.Element{zeta, alpha, q1} {
		for _, x := range d {
			want = append(want, uint32(x.Uint64()))
		}
	}

	var e Emitter
	read := func(from, n int) []string {
		res := make([]string, n)
		for i := range res {
			res[i] = e.Let(fmt.Sprintf("t_in[%d] as 𝔽", from+i))
		}
		return res
	}
	cZeta := e.Challenge("zeta", nil, read(0, 16))
	cAlpha := e.Challenge("alpha_DEEP", cZeta, read(16, 13))
	cQ1 := e.Challenge("fri_query_1", cAlpha, cAlpha)
	for i, o := range slices.Concat(cZeta, cAlpha, cQ1) {
		e.Line("t_out[%d] = %s as u32", i, o)
	}
	var src strings.Builder
	src.WriteString("input t_in(address:u16) -> (w:u32)\noutput t_out(address:u16) -> (w:u32)\n\n")
	src.WriteString("fn main() {\n    check(0)\n}\n\n")
	fmt.Fprintf(&src, "fn check(base:u16) {\n%s}\n", e.String())

	files := writeZkc(t, map[string]string{"poseidon2.zkc": Poseidon2Source(), "main.zkc": src.String()})
	res, err := zkcv.RunWith([]byte(fmt.Sprintf(`{"t_in": "%s"}`, hexWords(in))), Gadgets(), files...)
	if err != nil {
		t.Fatal(err)
	}
	if got := decodeWords(res.Outputs["t_out"]); !slices.Equal(got, want) {
		t.Fatalf("t_out mismatch:\ngot  %v\nwant %v", got, want)
	}
}
