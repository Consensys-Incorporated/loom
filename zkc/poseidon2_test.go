package zkc

import (
	"fmt"
	"math/rand/v2"
	"slices"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
	"github.com/consensys/loom/internal/hash"
)

// hashDriver builds a zkc program that reads words from h_in and writes, in
// order: the permutation of one 24-word state, the node compression of two
// 8-word digests, and the sponge digest of each input length.
func hashDriver(lengths []int) string {
	var sb strings.Builder
	sb.WriteString("input h_in(address:u16) -> (w:u32)\noutput h_out(address:u16) -> (w:u32)\n\n")
	sb.WriteString("fn main() {\n    check(0)\n}\n\n")

	e := Emitter{Sponges: map[string]func() string{}}
	in := 0
	read := func(n int) []string {
		res := make([]string, n)
		for i := range res {
			res[i] = e.Let(fmt.Sprintf("h_in[base + %d] as 𝔽", in))
			in++
		}
		return res
	}
	var outs []string
	outs = append(outs, e.Perm(read(P2Width))...)
	outs = append(outs, e.Node(read(P2Digest), read(P2Digest))...)
	for _, n := range lengths {
		outs = append(outs, e.Sponge(read(n))...)
	}
	for i, o := range outs {
		e.Line("h_out[%d] = %s as u32", i, o)
	}
	fmt.Fprintf(&sb, "fn check(base:u16) {\n%s}\n", e.String())
	sb.WriteString(SpongeSources(e.Sponges))
	return sb.String()
}

func TestPoseidon2(t *testing.T) {
	lengths := []int{1, 7, 15, 16, 17, 32, 45, 250, 470}
	rng := rand.New(rand.NewPCG(5, 6))
	randElems := func(n int) []koalabear.Element {
		res := make([]koalabear.Element, n)
		for i := range res {
			res[i].SetUint64(rng.Uint64())
		}
		return res
	}
	var in, want []uint32
	appendElems := func(dst *[]uint32, xs []koalabear.Element) {
		for _, x := range xs {
			*dst = append(*dst, uint32(x.Uint64()))
		}
	}

	// permutation
	state := randElems(P2Width)
	appendElems(&in, state)
	perm := slices.Clone(state)
	if err := hash.NewPoseidon2SpongeHasher().Perm.Permutation(perm); err != nil {
		t.Fatal(err)
	}
	appendElems(&want, perm)

	// node compression
	var l, r hash.Digest
	copy(l[:], randElems(P2Digest))
	copy(r[:], randElems(P2Digest))
	appendElems(&in, l[:])
	appendElems(&in, r[:])
	node := hash.Poseidon2NodeCompress(NodeDomainTag, l, r)
	appendElems(&want, node[:])

	// sponge
	for _, n := range lengths {
		xs := randElems(n)
		appendElems(&in, xs)
		h := hash.NewPoseidon2SpongeHasher()
		h.WriteElements(xs...)
		d := h.Sum()
		appendElems(&want, d[:])
	}

	files := writeZkc(t, map[string]string{
		"poseidon2.zkc": Poseidon2Source(),
		"main.zkc":      hashDriver(lengths),
	})
	res, err := zkcv.RunWith([]byte(fmt.Sprintf(`{"h_in": "%s"}`, hexWords(in))), Gadgets(), files...)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("\n%s", zkcv.FormatStats(res.Stats))
	if got := decodeWords(res.Outputs["h_out"]); !slices.Equal(got, want) {
		t.Fatalf("h_out mismatch:\ngot  %v\nwant %v", got, want)
	}
}
