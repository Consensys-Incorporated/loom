package recursion

import (
	"testing"
)

// TestOpeningsWidthIsFixed checks that the machine's width does not depend on
// the verified proof: more polynomials and queries only add rows.
func TestOpeningsWidthIsFixed(t *testing.T) {
	small := openingsMachine(t, smallCfg)
	big := openingsMachine(t, FixtureConfig{
		Batches:    []BatchConfig{{{LogN: 10, NumBase: 64, NumExt: 4, Shifts: []int{0, 1}}}},
		NumQueries: 32,
		Seed:       4,
	})
	var leaf [2]LeafCost
	for i, m := range []*Machine{small, big} {
		p, err := m.Compile()
		if err != nil {
			t.Fatal(err)
		}
		if i == 1 {
			if err := prove(t, p); err != nil {
				t.Fatalf("valid openings rejected: %v", err)
			}
		}
		leaf[i] = LeafCostOf(p.Loom)
		t.Logf("rows: p2 %d, sponge %d, merkle %d, witness %d; leaf elements/query %d, leaf perms/query %d",
			p.Loom.Modules[p2Mod].N, p.Loom.Modules[spongeMod].N, p.Loom.Modules[merkleMod].N,
			p.Loom.Modules[witnessMod].N, leaf[i].Elements, leaf[i].Perms)
	}
	// The leaf permutations can differ by a few: leaves are hashed per (tree,
	// group), and groups are formed by module height, which changes with the
	// row counts.
	if leaf[0].Elements != leaf[1].Elements {
		t.Fatalf("width depends on the verified proof: %d vs %d leaf elements", leaf[0].Elements, leaf[1].Elements)
	}
}
