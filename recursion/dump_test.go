package recursion

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/consensys/loom/trace"
	"github.com/consensys/loom/viz"
)

// TestDumpTrace writes the trace of a tiny machine (one query, one leaf block)
// as one CSV per chip into $RECURSION_TRACE_DIR:
//
//	RECURSION_TRACE_DIR=$PWD/recursion go test -run TestDumpTrace ./recursion
func TestDumpTrace(t *testing.T) {
	dir := os.Getenv("RECURSION_TRACE_DIR")
	if dir == "" {
		t.Skip("RECURSION_TRACE_DIR not set")
	}
	cfg := FixtureConfig{
		Batches:    []BatchConfig{{{LogN: 3, NumBase: 2, NumExt: 0, Shifts: []int{0}}}},
		NumQueries: 1,
		Seed:       1,
	}
	p, err := openingsMachine(t, cfg).Compile()
	if err != nil {
		t.Fatal(err)
	}
	if err := prove(t, p); err != nil {
		t.Fatal(err)
	}
	for _, mod := range []string{witnessMod, spongeMod, merkleMod, p2Mod} {
		sub := trace.New()
		for name, v := range p.Trace.Base {
			if strings.HasPrefix(name, mod+".") {
				sub.SetBase(strings.TrimPrefix(name, mod+"."), v)
			}
		}
		f := filepath.Join(dir, "trace_"+mod+".csv")
		if err := viz.WriteRawTraceToCSV(f, sub); err != nil {
			t.Fatal(err)
		}
		t.Logf("%s: %d columns x %d rows", f, len(sub.Base), p.Loom.Modules[mod].N)
	}
}
