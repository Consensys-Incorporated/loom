package zkc

import (
	"encoding/json"
	"os"
	"sort"
	"strings"
	"testing"

	"github.com/consensys/loom/field"
	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
	"github.com/consensys/loom/internal/protocol"
	zkc_util "github.com/LFDT-Lineth/zkc/pkg/zkc/util"
)

type reportModule struct {
	Name     string `json:"name"`
	Rows     int    `json:"rows"`
	Trace    int    `json:"trace"`    // committed base trace columns
	TraceExt int    `json:"traceExt"` // committed extension trace columns (non logup)
	Setup    int    `json:"setup"`    // precommitted setup columns
	Logup    int    `json:"logup"`    // logup running sums (extension)
	Mult     int    `json:"mult"`     // lookup multiplicities (base)
	Quotient int    `json:"quotient"` // AIR quotient chunks (extension)
	Leaf     int    `json:"leaf"`     // leaf elements per query at the next level
}

type reportConfig struct {
	Name       string         `json:"name"`
	Groups     []GroupConfig  `json:"groups"`
	Batches    int            `json:"batches"`
	Queries    int            `json:"queries"`
	Perms      int            `json:"perms"`
	PermsQuery int            `json:"permsPerQuery"`
	LeafElems  int            `json:"leafElems"`
	LeafPerms  int            `json:"leafPerms"`
	Modules    []reportModule `json:"modules"`
}

// TestReport writes the per-module column report of the benchmark shapes as
// JSON to $ZKC_REPORT.
func TestReport(t *testing.T) {
	out := os.Getenv("ZKC_REPORT")
	if out == "" {
		t.Skip("set ZKC_REPORT to the output file")
	}
	var res []reportConfig
	for _, bc := range benchCases() {
		f, err := NewFixture(bc.cfg)
		if err != nil {
			t.Fatal(err)
		}
		p, err := GeneratePCSVerifier(f)
		if err != nil {
			t.Fatal(err)
		}
		binf, err := zkcv.CompileFiles(writeZkc(t, p.Sources)...)
		if err != nil {
			t.Fatal(err)
		}
		pg, err := zkcv.NewProgram(binf, p.Gadgets)
		if err != nil {
			t.Fatal(err)
		}
		in, _ := zkc_util.ParseJsonInputFile(p.Input)
		if _, _, err := pg.Trace(in); err != nil {
			t.Fatal(err)
		}
		prog := pg.Loom
		mods := map[string]*reportModule{}
		get := func(m string) *reportModule {
			if mods[m] == nil {
				mods[m] = &reportModule{Name: m, Rows: prog.Modules[m].N}
			}
			return mods[m]
		}
		for _, r := range prog.Rounds {
			for _, c := range r.Staged {
				m := get(c.Module)
				switch {
				case strings.Contains(c.Name, "logup"):
					m.Logup++
				case strings.HasPrefix(c.Name, "Mult_"):
					m.Mult++
				case c.Field == field.Ext:
					m.TraceExt++
				default:
					m.Trace++
				}
			}
		}
		for _, c := range prog.SetupColumns {
			get(c.Module).Setup++
		}
		layout := protocol.BuildLayout(prog, 0)
		for name := range layout.AIRChunkSlot {
			get(name[:strings.LastIndexByte(name, '.')]).Quotient++
		}
		// Permutations emitted in zkc code, plus the leaf-sponge blocks of the
		// opening gadgets.
		blocks := 0
		for _, gr := range newGroups(f, newPCSShape(f)) {
			blocks += gr.numBlocks()
		}
		rc := reportConfig{Name: bc.name, Batches: len(bc.cfg.Batches), Queries: bc.cfg.NumQueries,
			Perms: p.MainPerms + bc.cfg.NumQueries*(p.QueryPerms+blocks), PermsQuery: p.QueryPerms + blocks}
		for _, b := range bc.cfg.Batches {
			rc.Groups = append(rc.Groups, b...)
		}
		leaf := zkcv.LeafCostOf(prog)
		rc.LeafElems, rc.LeafPerms = leaf.Elements, leaf.Perms
		for _, m := range mods {
			m.Leaf = 2*(m.Trace+m.Setup+m.Mult) + 12*(m.TraceExt+m.Logup+m.Quotient)
			rc.Modules = append(rc.Modules, *m)
		}
		sort.Slice(rc.Modules, func(i, j int) bool { return rc.Modules[i].Leaf > rc.Modules[j].Leaf })
		res = append(res, rc)
	}
	data, err := json.MarshalIndent(res, "", " ")
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(out, data, 0o644); err != nil {
		t.Fatal(err)
	}
}
