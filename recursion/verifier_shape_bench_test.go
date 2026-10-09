package recursion

import (
	"fmt"
	"math/rand/v2"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/internal/hash"
)

// verifierShapedMachine builds the per-query work of a loom verifier for one
// committed batch: the leaf sponge and Merkle path of every query opening
// (from a real fixture), the DEEP-quotient accumulation of the opened values,
// and the FRI fold chain.
//
// It is a model, not the real circuit: the transcript, the bits
// decompositions of the query challenges and the window checks are absent,
// and the fold chain is built with zero injections so its witness is
// self-consistent without depending on the DEEP accumulator. Those parts are
// identical in every variant, so leaving them out only shrinks the
// denominator — the reported shares are upper bounds on the Horner's weight.
func verifierShapedMachine(t *testing.T, cfg FixtureConfig, nPolys, nShifts, foldRounds, lanes int) *builder {
	t.Helper()
	f, err := NewFixture(cfg)
	if err != nil {
		t.Fatal(err)
	}
	r := rand.New(rand.NewPCG(41, 43))
	b := newBuilder(lanes)

	var rootCell Cell
	copy(rootCell[:], f.Roots[0][:])
	root := b.input(rootCell)
	alpha := b.input(E6Cell(randE6(r)))

	var half koalabear.Element
	half.SetUint64(2)
	half.Inverse(&half)
	zeroCell := b.Const(Cell{})

	for k := range cfg.NumQueries {
		// --- opening: hash the queried row pair, then walk the path ---
		wp := f.Proof.PointSamplings[k][0]
		rows := wp.TopRows
		stream := []koalabear.Element{hash.NewElement(LeafDomainTag),
			hash.NewElement(uint64(2 * len(rows.Lo.RawRowBase))),
			hash.NewElement(uint64(2 * len(rows.Lo.RawRowExt)))}
		stream = append(stream, rows.Lo.RawRowBase...)
		stream = append(stream, rows.Hi.RawRowBase...)
		for _, v := range rows.Lo.RawRowExt {
			stream = append(stream, hash.ExtToElements(v)...)
		}
		for _, v := range rows.Hi.RawRowExt {
			stream = append(stream, hash.ExtToElements(v)...)
		}
		leaf := b.Sponge(b.inputStream(stream), len(stream))
		var sibs []int
		for _, s := range wp.Path.Siblings {
			var c Cell
			copy(c[:], s[:])
			sibs = append(sibs, b.input(c))
		}
		var idx Cell
		idx[0].SetUint64(uint64(wp.Path.LeafIdx))
		b.MerklePath(leaf, sibs, b.input(idx), root)

		// --- DEEP bridge: accumulate the opened values, divide by the
		// denominator of each opening point ---
		var terms []int
		for range nShifts {
			num := hornerChain(b, r, alpha, nPolys, lanes)
			terms = append(terms, b.Div(b.Sub(num, b.input(E6Cell(randE6(r)))),
				b.input(E6Cell(randE6(r)))))
		}
		acc := terms[0]
		for _, x := range terms[1:] {
			acc = b.Add(acc, x)
		}
		b.AssertEq(acc, acc)

		// --- FRI fold chain (zero injections, self-consistent) ---
		p, q := randE6(r), randE6(r)
		var chain []FoldRound
		for j := range foldRounds {
			fa := randE6(r)
			var xi koalabear.Element
			xi.SetUint64(r.Uint64())
			bit := r.IntN(2)
			var xb Cell
			xb[0], xb[1] = xi, koalabear.NewElement(uint64(bit))
			var sum, diff, next ext.E6
			sum.Add(&p, &q)
			sum.MulByElement(&sum, &half)
			diff.Sub(&p, &q)
			diff.MulByElement(&diff, &xi)
			diff.MulByElement(&diff, &half)
			diff.Mul(&diff, &fa)
			next.Add(&sum, &diff)
			chain = append(chain, FoldRound{
				P: b.input(E6Cell(p)), Q: b.input(E6Cell(q)),
				Alpha: b.input(E6Cell(fa)), XB: b.input(xb), Inj: zeroCell,
			})
			other := randE6(r)
			if bit == 0 {
				p, q = next, other
			} else {
				p, q = other, next
			}
			if j == foldRounds-1 {
				p = next
			}
		}
		b.FoldChain(chain, b.input(E6Cell(p)))
	}
	return b
}

// TestVerifierShapeImpact reports the whole-circuit effect of the Horner
// batching on a verifier-shaped workload.
func TestVerifierShapeImpact(t *testing.T) {
	cfg := FixtureConfig{
		Batches:    []BatchConfig{{{LogN: 14, NumBase: 64, NumExt: 8, Shifts: []int{0, 1}}}},
		NumQueries: 32,
		Seed:       2,
	}
	const (
		nPolys     = 72
		nShifts    = 2
		foldRounds = 14
		reps       = 2
	)
	type rec struct {
		lanes, total int
		wall         time.Duration
	}
	var out []rec
	for _, lanes := range []int{lanesE6, 8} {
		b := verifierShapedMachine(t, cfg, nPolys, nShifts, foldRounds, lanes)
		p, r := b.run(t)
		total := reportCosts(laneLabel(lanes), costsOf(p))
		wall := proveTime(t, p, r, reps)
		fmt.Printf("prove+verify (best of %d): %v\n", reps, wall)
		out = append(out, rec{lanes, total, wall})
	}
	fmt.Printf("\n=== verifier-shaped: %d queries, 2^%d x (64 base + 8 ext), %d fold rounds\n",
		cfg.NumQueries, cfg.Batches[0][0].LogN, foldRounds)
	for _, x := range out {
		fmt.Printf("%-30s %10d %8.1f%% %9v %7.1f%%\n", laneLabel(x.lanes), x.total,
			100*float64(x.total-out[0].total)/float64(out[0].total),
			x.wall.Round(time.Millisecond),
			100*float64(x.wall-out[0].wall)/float64(out[0].wall))
	}
}
