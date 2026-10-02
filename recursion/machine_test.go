package recursion

import (
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/trace"
)

// openingsMachine checks, for every query of a one-batch, one-group PCS
// fixture, that the opened row pair hashes to a leaf of the batch root. The
// program depends only on the fixture's shape; its inputs are the fixture's
// values.
func openingsMachine(t *testing.T, cfg FixtureConfig) *builder {
	t.Helper()
	f, err := NewFixture(cfg)
	if err != nil {
		t.Fatal(err)
	}
	b := &builder{}
	var root Cell
	copy(root[:], f.Roots[0][:])
	rootAddr := b.input(root)
	for k := range cfg.NumQueries {
		wp := f.Proof.PointSamplings[k][0]
		if len(wp.Injections) != 0 {
			t.Fatal("openingsMachine wants a single-group batch")
		}
		rows := wp.TopRows
		stream := []koalabear.Element{hash.NewElement(LeafDomainTag),
			hash.NewElement(uint64(2 * len(rows.Lo.RawRowBase))), hash.NewElement(uint64(2 * len(rows.Lo.RawRowExt)))}
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
		b.MerklePath(leaf, sibs, b.input(idx), rootAddr)
	}
	return b
}

var smallCfg = FixtureConfig{
	Batches:    []BatchConfig{{{LogN: 6, NumBase: 5, NumExt: 1, Shifts: []int{0, 1}}}},
	NumQueries: 4,
	Seed:       3,
}

func TestOpenings(t *testing.T) {
	p, r := openingsMachine(t, smallCfg).run(t)
	if err := prove(t, p, r); err != nil {
		t.Fatalf("valid openings rejected: %v", err)
	}
	logBreakdown(t, p)
}

// TestSetupOnce compiles and sets up the openings program once, then proves
// its execution on two PCS proofs of the same shape: only the inputs change.
func TestSetupOnce(t *testing.T) {
	p, err := openingsMachine(t, smallCfg).Compile()
	if err != nil {
		t.Fatal(err)
	}
	pk, vk := keys(t, p)
	for _, seed := range []uint64{3, 11} {
		cfg := smallCfg
		cfg.Seed = seed
		r, err := p.Execute(openingsMachine(t, cfg).in)
		if err != nil {
			t.Fatal(err)
		}
		if err := proveWith(p, pk, vk, r); err != nil {
			t.Fatalf("seed %d: valid openings rejected: %v", seed, err)
		}
	}
	// Inputs from one proof with the root of another: the paths fail.
	in := openingsMachine(t, smallCfg).in
	other := smallCfg
	other.Seed = 11
	in[0] = openingsMachine(t, other).in[0]
	r, err := p.Execute(in)
	if err != nil {
		t.Fatal(err)
	}
	if err := proveWith(p, pk, vk, r); err == nil {
		t.Fatal("openings under another root accepted")
	}
}

// logBreakdown logs, per chip, its rows and its columns by kind (base trace,
// E6 logup, multiplicity, E6 quotient chunks), and the next-level leaf cost.
func logBreakdown(t *testing.T, p *Program) {
	t.Helper()
	var sb []byte
	for _, l := range LeafBreakdownOf(p.Loom) {
		sb = fmt.Appendf(sb, "%-8s rows=%5d trace=%4d logup=%4d mult=%3d quotient=%3d  leaf elements=%4d\n",
			l.Module, p.Loom.Modules[l.Module].N, l.Trace/2, l.Logup/12, l.Mult/2, l.Quotient/12,
			l.Trace+l.Logup+l.Mult+l.Quotient)
	}
	leaf := LeafCostOf(p.Loom)
	t.Logf("\n%sleaf elements/query %d, leaf perms/query %d", sb, leaf.Elements, leaf.Perms)
}

func TestOpeningsRejects(t *testing.T) {
	cases := map[string]func(tr trace.Trace){
		// a proof value: the leaf no longer hashes to the root
		"witness value": func(tr trace.Trace) { tr.Base["witness.v3"][2].SetUint64(5) },
		// a sponge lane that differs from the cell it reads
		"sponge lane": func(tr trace.Trace) { tr.Base["sponge.x1"][0].SetUint64(6) },
		// the chained state
		"sponge output": func(tr trace.Trace) { tr.Base["sponge.out20"][0].SetUint64(7) },
		// a direction bit, flipped on a real level
		"merkle bit": func(tr trace.Trace) { flip(&tr.Base["merkle.b"][1]) },
		// the index recomposition
		"merkle index": func(tr trace.Trace) { tr.Base["merkle.idx"][2].SetUint64(1000) },
		// a sibling that differs from the proof
		"merkle sibling": func(tr trace.Trace) { tr.Base["merkle.s4"][3].SetUint64(8) },
	}
	for name, tamper := range cases {
		t.Run(name, func(t *testing.T) {
			err := compileAndProve(t, openingsMachine(t, smallCfg), func(_, w trace.Trace) { tamper(w) })
			if err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}
