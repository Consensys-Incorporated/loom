package recursion

import (
	"fmt"
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/poseidon2"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/trace"
)

// proveP2AIRWidth builds a program made of the width-w Poseidon2 AIR alone,
// fills it from gnark-crypto's width-w permutation, proves and verifies it,
// and returns the module's committed column count and constraint degree.
func proveP2AIRWidth(t *testing.T, w, rf, rp int) (cols, deg, chunks int) {
	t.Helper()
	const n = 8
	module := fmt.Sprintf("p2_w%d", w)
	a := newP2AIR(w, rf, rp)
	inputs, outputs := make([]string, w), make([]string, w)
	for i := range inputs {
		inputs[i] = fmt.Sprintf("%s.s%d", module, i)
		outputs[i] = fmt.Sprintf("%s.r%d", module, i)
	}
	b := board.NewBuilder()
	m := board.NewModule(module)
	m.N = n
	b.AddModule(m)
	if err := a.Define(&b, module, inputs, outputs); err != nil {
		t.Fatal(err)
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}

	rng := rand.New(rand.NewPCG(9, 10))
	perm := poseidon2.NewPermutation(w, rf, rp)
	tr := trace.New()
	in, out := make([][]koalabear.Element, w), make([][]koalabear.Element, w)
	for i := range in {
		in[i], out[i] = make([]koalabear.Element, n), make([]koalabear.Element, n)
	}
	for row := 1; row < n; row++ {
		state := make([]koalabear.Element, w)
		for i := range state {
			state[i].SetUint64(rng.Uint64())
			in[i][row] = state[i]
		}
		if err := perm.Permutation(state); err != nil {
			t.Fatal(err)
		}
		for i := range state {
			out[i][row] = state[i]
		}
	}
	for i := range in {
		tr.SetBase(inputs[i], in[i])
		tr.SetBase(outputs[i], out[i])
	}
	// Fill agrees with gnark-crypto's permutation, or it errors on the
	// outputs already traced: this is what checks the width-w matrices.
	if err := a.Fill(tr, module, inputs, outputs); err != nil {
		t.Fatalf("width %d: %v", w, err)
	}
	pk, vk, err := loom.Setup(tr, pg)
	if err != nil {
		t.Fatal(err)
	}
	st := loom.Statement{Program: pg, VerificationKey: vk, PublicInputs: public.Inputs{}}
	prf, err := loom.Prove(st, loom.Witness{Trace: tr, ProvingKey: pk})
	if err != nil {
		t.Fatalf("width %d: %v", w, err)
	}
	if err := loom.Verify(st, prf); err != nil {
		t.Fatalf("width %d: %v", w, err)
	}

	mod := pg.Modules[module]
	deg = mod.VanishingRelation.Degree()
	chunks = poly.QuotientDomainSize(deg, mod.N) / mod.N
	for _, r := range pg.Rounds {
		for _, ref := range r.Staged {
			if ref.Module == module {
				cols++
			}
		}
	}
	return cols, deg, chunks
}

// TestP2WidthCost prices a narrower P2 core. The Merkle node compression has
// a fixed 17-lane input — the node domain tag and two 8-element digests — so
// a width-16 core cannot hash a node without dropping the tag lane, and the
// sponge needs the rate that width 24 gives it. A width-16 core is therefore
// only reachable by splitting the core in two again, which this prices
// against the single width-24 core the package uses.
func TestP2WidthCost(t *testing.T) {
	type core struct {
		w, cols, deg, chunks int
	}
	cores := map[int]core{}
	for _, w := range []int{16, 24} {
		c, d, ch := proveP2AIRWidth(t, w, P2FullRounds, P2PartialRounds)
		cores[w] = core{w, c, d, ch}
		t.Logf("width %2d, %d full / %d partial rounds: %3d AIR columns, degree %d, %d quotient chunks",
			w, P2FullRounds, P2PartialRounds, c, d, ch)
	}
	if got, want := cores[24].cols, P2Width*(P2FullRounds+1)+P2PartialRounds; got != want {
		t.Fatalf("width 24: %d columns, want %d", got, want)
	}
	if got, want := cores[16].cols, 16*(P2FullRounds+1)+P2PartialRounds; got != want {
		t.Fatalf("width 16: %d columns, want %d", got, want)
	}

	// The real verifier's mix of rows, which is what decides this: a narrower
	// core helps in proportion to the Merkle steps and hurts in proportion to
	// the sponge blocks, whose number doubles when the rate halves.
	ip := vmProofs(t, 3)[0]
	v, err := NewVerifier(ip.program, ip.vk, ShapeOf(ip.prf, ip.pi))
	if err != nil {
		t.Fatal(err)
	}
	spongeBlocks24, merkleSteps := v.M.spongeBlocks(), v.M.pathStepRows()
	// The control columns each chip adds: the sponge its block (rate lanes),
	// the Merkle path its 20 (b, idx, x, b0, cur0..7, sib0..7). A core's
	// per-row cost is base + 6·ext + 6·chunks, as in TestProfileVerifierCost.
	const merkleCtl = 20
	cost := func(rows, base, ext, chunks int) int { return rows * (base + 6*ext + 6*chunks) }
	type design struct {
		label string
		cost  int
		cols  int
	}
	// One width-24 core: both controls on every row, one AIR.
	one := cores[24]
	oneBase := one.cols + P2Rate + merkleCtl + 1 // + the dynamic paths' multiplicity
	oneRows := height(spongeBlocks24 + merkleSteps)
	// Two cores, the sponge at width 24 and the Merkle path at width 16: each
	// control only on its own rows, but the AIR instantiated twice.
	spBase := cores[24].cols + P2Rate
	mkBase := cores[16].cols + merkleCtl + 1
	// A single width-16 core would be narrower still, but it cannot hash a
	// node: the tag and two digests are 17 lanes. It is priced here only to
	// show what dropping the node domain tag would be worth — that is a
	// protocol and domain-separation decision, not an engineering one. Its
	// rate falls to 16 − 8 = 8, so the sponge takes twice the blocks.
	w16Base := cores[16].cols + (16 - P2Digest) + merkleCtl + 1
	designs := []design{
		{"one core, w=24", cost(oneRows, oneBase, 2, one.chunks), oneBase + 2},
		{"one core, w=16 (no node tag)",
			cost(height(2*spongeBlocks24+merkleSteps), w16Base, 2, 4), w16Base + 2},
		{"two cores, w=24 + w=16",
			cost(height(spongeBlocks24), spBase, 1, 4) + cost(height(merkleSteps), mkBase, 2, 4),
			spBase + 1 + mkBase + 2},
		{"two cores, w=24 + w=24",
			cost(height(spongeBlocks24), spBase, 1, 4) + cost(height(merkleSteps), cores[24].cols+merkleCtl+1, 2, 4),
			spBase + 1 + cores[24].cols + merkleCtl + 3},
	}
	t.Logf("projected on the vm verifier (%d sponge blocks, %d Merkle steps):", spongeBlocks24, merkleSteps)
	for _, d := range designs {
		t.Logf("  %-24s prover cost %7d, %3d core columns", d.label, d.cost, d.cols)
	}
}
