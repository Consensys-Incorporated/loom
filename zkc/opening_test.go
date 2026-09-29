package zkc

import (
	"testing"

	zkc_util "github.com/LFDT-Lineth/zkc/pkg/zkc/util"
	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
	"github.com/consensys/loom/trace"
)

// TestOpeningGadgetRejects tampers with the opening gadget's columns after
// Fill, and expects the proof to fail.
func TestOpeningGadgetRejects(t *testing.T) {
	cases := map[string]func(tr trace.Trace){
		"item value":    func(tr trace.Trace) { tr.Base["open_0_0_items.f0"][5].SetUint64(7) },
		"sponge lane":   func(tr trace.Trace) { tr.Base["open_0_0_sponge.x2"][1].SetUint64(8) }, // position 18 of query 0
		"accumulator":   func(tr trace.Trace) { tr.Base["open_1_0_items.acc0_2"][3].SetUint64(9) },
		"power":         func(tr trace.Trace) { tr.Base["open_0_1_items.pw4"][2].SetUint64(10) },
		"sponge output": func(tr trace.Trace) { tr.Base["open_0_0_sponge.out3"][0].SetUint64(11) },
		"io sum":        func(tr trace.Trace) { tr.Base["open_1_0.lo0_1"][1].SetUint64(12) },
	}
	f, err := NewFixture(smallFixture)
	if err != nil {
		t.Fatal(err)
	}
	p, err := GeneratePCSVerifier(f)
	if err != nil {
		t.Fatal(err)
	}
	files := writeZkc(t, p.Sources)
	in, err := zkc_util.ParseJsonInputFile(p.Input)
	if err != nil {
		t.Fatal(err)
	}
	for name, tamper := range cases {
		t.Run(name, func(t *testing.T) {
			binf, err := zkcv.CompileFiles(files...)
			if err != nil {
				t.Fatal(err)
			}
			pg, err := zkcv.NewProgram(binf, p.Gadgets)
			if err != nil {
				t.Fatal(err)
			}
			tr, _, err := pg.Trace(in)
			if err != nil {
				t.Fatal(err)
			}
			if _, ok := tr.Base[firstKey(name, cases)]; !ok {
				t.Fatalf("column to tamper with is missing")
			}
			tamper(tr)
			if _, err := pg.ProveAndVerify(tr); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}

// firstKey returns the column a tamper case writes, for the existence check.
func firstKey(name string, _ map[string]func(trace.Trace)) string {
	return map[string]string{
		"item value":    "open_0_0_items.f0",
		"sponge lane":   "open_0_0_sponge.x2",
		"accumulator":   "open_1_0_items.acc0_2",
		"power":         "open_0_1_items.pw4",
		"sponge output": "open_0_0_sponge.out3",
		"io sum":        "open_1_0.lo0_1",
	}[name]
}
