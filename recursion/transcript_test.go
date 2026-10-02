package recursion

import (
	"fmt"
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
)

// transcriptScript builds the same random transcript in circuit and with
// internal/fiat-shamir: challenges with no binding, bindings of every kind,
// constant runs of every length mod 8, and earlier digests bound again (as
// FRI's query chain does). It returns the builder, the circuit's digest
// cells and fiat-shamir's digests.
func transcriptScript(t *testing.T, seed uint64) (*builder, []int, []hash.Digest) {
	t.Helper()
	r := rand.New(rand.NewPCG(seed, 1))
	names := []string{"challenge@loom_0", "challenge@loom_1", "__zeta", "alpha_DEEP", "fri_fold_0", "fri_query_0"}
	b := &builder{}
	tr := NewTranscript(&b.Machine, names...)
	h := hash.NewPoseidon2SpongeHasher()
	fs := fiatshamir.NewTranscript(&h, names...)

	elem := func() koalabear.Element {
		var e koalabear.Element
		e.SetUint64(r.Uint64())
		return e
	}
	var cells []int
	var want []hash.Digest
	for i, name := range names {
		nb := r.IntN(6)
		if i == 0 {
			nb = 0 // a challenge with no binding
		}
		for range nb {
			var xs []koalabear.Element
			switch k := r.IntN(5); k {
			case 0, 1, 2: // an input of each kind
				kind := []int{KindScalar, KindE6, KindDigest}[k]
				var c Cell
				for j := range kind {
					c[j] = elem()
				}
				tr.Bind(name, Item{b.input(c), kind})
				xs = c[:kind]
			case 3: // a constant run
				for range r.IntN(20) {
					xs = append(xs, elem())
				}
				tr.BindElements(name, xs)
			case 4: // an earlier digest
				if i == 0 {
					continue
				}
				j := r.IntN(i)
				tr.Bind(name, Digest(cells[j]))
				xs = want[j][:]
			}
			if err := fs.Bind(name, xs); err != nil {
				t.Fatal(err)
			}
		}
		cells = append(cells, tr.Compute(name))
		d, err := fs.ComputeChallenge(name)
		if err != nil {
			t.Fatal(err)
		}
		want = append(want, d)
	}
	return b, cells, want
}

func TestTranscript(t *testing.T) {
	for seed := range uint64(8) {
		t.Run(fmt.Sprint(seed), func(t *testing.T) {
			b, cells, want := transcriptScript(t, seed)
			p, r := b.run(t)
			for i, c := range cells {
				got := r.Value(c)
				for j := range digest {
					if !got[j].Equal(&want[i][j]) {
						t.Fatalf("challenge %d: lane %d = %s, want %s", i, j, got[j].String(), want[i][j].String())
					}
				}
			}
			if seed == 0 {
				if err := prove(t, p, r); err != nil {
					t.Fatalf("valid transcript rejected: %v", err)
				}
			}
		})
	}
}
