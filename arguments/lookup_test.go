package arguments_test

import (
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/proof"
	"github.com/consensys/loom/public"
	"github.com/consensys/loom/trace"
)

const n = 8

// lookupProgram looks up three source columns of module "m" into the table
// column "tab.t" = 0..n-1.
func lookupProgram(t *testing.T) board.Program {
	t.Helper()
	b := board.NewBuilder()
	m := board.NewModule("m")
	m.N = n
	b.AddModule(m)
	tab := board.NewModule("tab")
	tab.N = n
	b.AddModule(tab)
	var S []board.Column
	for _, c := range []string{"m.s0", "m.s1", "m.s2"} {
		S = append(S, board.Column{Module: "m", In: expr.Col(c)})
	}
	if err := arguments.LookupUnion(&b, S, []board.Column{{Module: "tab", In: expr.Col("tab.t")}}); err != nil {
		t.Fatal(err)
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}
	return pg
}

func lookupTrace(bad bool) trace.Trace {
	tr := trace.New()
	col := func(f func(i int) uint64) []koalabear.Element {
		res := make([]koalabear.Element, n)
		for i := range res {
			res[i].SetUint64(f(i))
		}
		return res
	}
	tr.SetBase("tab.t", col(func(i int) uint64 { return uint64(i) }))
	tr.SetBase("m.s0", col(func(i int) uint64 { return uint64(i) }))
	tr.SetBase("m.s1", col(func(i int) uint64 { return uint64(n - 1 - i) }))
	tr.SetBase("m.s2", col(func(i int) uint64 {
		if bad && i == 5 {
			return 100 // not in the table
		}
		return 3
	}))
	return tr
}

func prove(t *testing.T, pg board.Program, tr trace.Trace) (loom.Statement, proof.Proof, error) {
	t.Helper()
	pk, vk, err := loom.Setup(tr, pg)
	if err != nil {
		t.Fatal(err)
	}
	st := loom.Statement{Program: pg, VerificationKey: vk, PublicInputs: public.Inputs{}}
	prf, err := loom.Prove(st, loom.Witness{Trace: tr, ProvingKey: pk})
	return st, prf, err
}

func TestBatchedCyclicLookup(t *testing.T) {
	pg := lookupProgram(t)

	// The three sources share one logup column in "m", of degree 4.
	logups := 0
	for _, r := range pg.Rounds {
		for _, c := range r.Staged {
			if c.Module == "m" && strings.Contains(c.Name, "logup") {
				logups++
			}
		}
	}
	if logups != 1 {
		t.Fatalf("module m has %d logup columns, want 1", logups)
	}
	if d := pg.Modules["m"].VanishingRelation.Degree(); d > board.MaxLogupDegree {
		t.Fatalf("module m has degree %d, want at most %d", d, board.MaxLogupDegree)
	}

	// The totals are exposed in the running-sums round, which must bind them
	// to the transcript before its challenge (an unbound total could be chosen
	// after the challenges, since the verifier evaluates T/N itself).
	if r := pg.Rounds[board.RoundRunningSums]; r.FSHook != board.BindExposedValues || len(r.ExposedValueNames()) != 2 {
		t.Fatalf("running-sums round: FS hook %d, %d exposed values; want BindExposedValues and 2", r.FSHook, len(r.ExposedValueNames()))
	}

	st, prf, err := prove(t, pg, lookupTrace(false))
	if err != nil {
		t.Fatal(err)
	}
	if err := loom.Verify(st, prf); err != nil {
		t.Fatalf("valid proof rejected: %v", err)
	}

	// Changing an exposed total must be caught: it is bound to the transcript
	// and balanced on the bus.
	for name, v := range prf.ExposedValues {
		tampered := make(proof.ExposedValues, len(prf.ExposedValues))
		for k, w := range prf.ExposedValues {
			tampered[k] = w
		}
		e := v.Entries[0]
		value := e.ExtValue()
		value.B0.A0.Add(&value.B0.A0, new(koalabear.Element).SetOne())
		e.SetExt(value)
		tampered[name] = proof.ExposedValue{Entries: []proof.ExposedEntry{e}}
		bad := prf
		bad.ExposedValues = tampered
		if err := loom.Verify(st, bad); err == nil {
			t.Fatalf("tampered total %s accepted", name)
		}
	}
}

// A source value outside the table is refused by the prover's multiplicity
// step; if a proof were produced anyway, the verifier must reject it.
func TestBatchedCyclicLookupRejectsMissingValue(t *testing.T) {
	pg := lookupProgram(t)
	st, prf, err := prove(t, pg, lookupTrace(true))
	if err != nil {
		return // the multiplicity step already refuses the trace
	}
	if err := loom.Verify(st, prf); err == nil {
		t.Fatal("lookup of a value outside the table accepted")
	}
}

// A source and a target in the same module share one logup column: the target
// fraction has a negated numerator, and the bus has a single total.
func TestSourceAndTargetShareColumn(t *testing.T) {
	b := board.NewBuilder()
	m := board.NewModule("m")
	m.N = n
	b.AddModule(m)
	if err := arguments.Lookup(&b, board.Column{Module: "m", In: expr.Col("m.s")}, board.Column{Module: "m", In: expr.Col("m.t")}); err != nil {
		t.Fatal(err)
	}
	pg, err := board.Compile(&b)
	if err != nil {
		t.Fatal(err)
	}
	if len(pg.LogupBus) != 1 || len(pg.LogupBus[0].Totals) != 1 {
		t.Fatalf("got buses %v, want one bus with one total", pg.LogupBus)
	}

	for _, bad := range []bool{false, true} {
		tr := trace.New()
		tab, src := make([]koalabear.Element, n), make([]koalabear.Element, n)
		for i := range n {
			tab[i].SetUint64(uint64(i))
			src[i].SetUint64(uint64((3 * i) % n))
		}
		if bad {
			src[2].SetUint64(100)
		}
		tr.SetBase("m.t", tab)
		tr.SetBase("m.s", src)
		st, prf, err := prove(t, pg, tr)
		if bad {
			if err == nil && loom.Verify(st, prf) == nil {
				t.Fatal("source outside the table accepted")
			}
			continue
		}
		if err != nil {
			t.Fatal(err)
		}
		if err := loom.Verify(st, prf); err != nil {
			t.Fatalf("valid proof rejected: %v", err)
		}
	}
}
