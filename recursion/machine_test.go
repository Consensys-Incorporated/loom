package recursion

import (
	"fmt"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/trace"
)

// openingsMachine checks, for every query of a one-batch, one-group PCS
// fixture, that the opened row pair hashes to a leaf of the batch root.
func openingsMachine(t *testing.T, cfg FixtureConfig) *Machine {
	t.Helper()
	f, err := NewFixture(cfg)
	if err != nil {
		t.Fatal(err)
	}
	var m Machine
	var root Cell
	copy(root[:], f.Roots[0][:])
	rootAddr := m.Witness(root)
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
		leaf := m.Sponge(m.WitnessStream(stream), len(stream))

		var sibs []int
		for _, s := range wp.Path.Siblings {
			var c Cell
			copy(c[:], s[:])
			sibs = append(sibs, m.Witness(c))
		}
		var idx Cell
		idx[0].SetUint64(uint64(wp.Path.LeafIdx))
		m.MerklePath(leaf, sibs, m.Witness(idx), rootAddr)
	}
	return &m
}

func prove(t *testing.T, p *Program) error {
	t.Helper()
	pk, vk, err := loom.Setup(p.Trace, p.Loom)
	if err != nil {
		return err
	}
	st := loom.Statement{Program: p.Loom, VerificationKey: vk, PublicInputs: public.Inputs{}}
	prf, err := loom.Prove(st, loom.Witness{Trace: p.Trace, ProvingKey: pk})
	if err != nil {
		return err
	}
	return loom.Verify(st, prf)
}

var smallCfg = FixtureConfig{
	Batches:    []BatchConfig{{{LogN: 6, NumBase: 5, NumExt: 1, Shifts: []int{0, 1}}}},
	NumQueries: 4,
	Seed:       3,
}

func TestOpenings(t *testing.T) {
	m := openingsMachine(t, smallCfg)
	p, err := m.Compile()
	if err != nil {
		t.Fatal(err)
	}
	if err := prove(t, p); err != nil {
		t.Fatalf("valid openings rejected: %v", err)
	}
	logBreakdown(t, p)
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
		"merkle bit": func(tr trace.Trace) {
			b := &tr.Base["merkle.b"][1]
			if b.IsZero() {
				b.SetOne()
			} else {
				b.SetZero()
			}
		},
		// the index recomposition
		"merkle index": func(tr trace.Trace) { tr.Base["merkle.idx"][2].SetUint64(1000) },
		// a sibling that differs from the proof
		"merkle sibling": func(tr trace.Trace) { tr.Base["merkle.s4"][3].SetUint64(8) },
	}
	for name, tamper := range cases {
		t.Run(name, func(t *testing.T) {
			m := openingsMachine(t, smallCfg)
			p, err := m.Compile()
			if err != nil {
				t.Fatal(err)
			}
			tamper(p.Trace)
			if err := prove(t, p); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}
