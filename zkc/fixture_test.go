package zkc

import "testing"

// smallFixture has two batches: a mixed-size tree with sizes 2^6 and 2^4, and
// a single-size tree of size 2^5, so FRI has three levels.
var smallFixture = FixtureConfig{
	Batches: []BatchConfig{
		{
			{LogN: 6, NumBase: 3, NumExt: 1, Shifts: []int{0, 1}},
			{LogN: 4, NumBase: 2, NumExt: 0, Shifts: []int{0}},
		},
		{
			{LogN: 5, NumBase: 1, NumExt: 2, Shifts: []int{0, -1}},
		},
	},
	NumQueries: 4,
	Seed:       1,
}

func TestNewFixture(t *testing.T) {
	for name, cfg := range map[string]FixtureConfig{
		"single": {Batches: []BatchConfig{{{LogN: 5, NumBase: 2, Shifts: []int{0}}}}, NumQueries: 3, Seed: 2},
		"small":  smallFixture,
	} {
		t.Run(name, func(t *testing.T) {
			f, err := NewFixture(cfg)
			if err != nil {
				t.Fatal(err)
			}
			if got, want := len(f.Proof.DeepQuotientRoots), len(sizesDesc(cfg)); got != want {
				t.Fatalf("DEEP roots = %d, want %d", got, want)
			}
		})
	}
}

func sizesDesc(cfg FixtureConfig) []int {
	seen := map[int]bool{}
	var res []int
	for _, b := range cfg.Batches {
		for _, g := range b {
			if !seen[g.LogN] {
				seen[g.LogN] = true
				res = append(res, g.LogN)
			}
		}
	}
	return res
}
