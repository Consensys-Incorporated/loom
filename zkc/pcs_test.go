package zkc

import (
	"testing"

	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
)

func runProgram(t *testing.T, p *Program) (zkcv.Result, error) {
	t.Helper()
	files := writeZkc(t, p.Sources)
	return zkcv.RunWith(p.Input, p.Gadgets, files...)
}

func TestPCSVerifier(t *testing.T) {
	f, err := NewFixture(smallFixture)
	if err != nil {
		t.Fatal(err)
	}
	p, err := GeneratePCSVerifier(f)
	if err != nil {
		t.Fatal(err)
	}
	res, err := runProgram(t, p)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("\n%s", zkcv.FormatStats(res.Stats))
}

// TestPCSVerifierRejects tampers with the proof and expects the zkc verifier
// to fail.
func TestPCSVerifierRejects(t *testing.T) {
	cases := map[string]func(f *Fixture){
		// breaks the final polynomial's constancy and the query transcript
		"final poly": func(f *Fixture) { f.Proof.FRIProof.FinalPolyExt[1].B0.A0.SetUint64(12345) },
		// breaks a FRI layer's Merkle path
		"layer sibling": func(f *Fixture) { f.Proof.FRIProof.FRIQueries[2].Layers[1].Path.Siblings[0][3].SetUint64(7) },
		// breaks a level's Merkle path and the level injection
		"level leaf": func(f *Fixture) { f.Proof.FRIProof.LevelQueries[0][1].LeafQExt.B1.A1.SetUint64(9) },
		// changes the fold challenges and breaks the layer-1 Merkle paths
		"fri root": func(f *Fixture) { f.Proof.FRIProof.FRIRoots[0][0].SetUint64(11) },
		// breaks a batch leaf and the DEEP bridge
		"top row": func(f *Fixture) { f.Proof.PointSamplings[1][0].TopRows.Lo.RawRowBase[2].SetUint64(13) },
		// breaks an injected group's leaf and the DEEP bridge of its size
		"injected row": func(f *Fixture) { f.Proof.PointSamplings[3][0].Injections[0].Rows.Hi.RawRowBase[1].SetUint64(17) },
		// breaks a batch Merkle path
		"batch sibling": func(f *Fixture) { f.Proof.PointSamplings[0][1].Path.Siblings[2][5].SetUint64(19) },
		// changes alpha_DEEP and every later challenge, and breaks the bridge
		"claimed value": func(f *Fixture) { f.Proof.ClaimedValues[1][0].Ext[1][1].B2.A1.SetUint64(23) },
	}
	for name, tamper := range cases {
		t.Run(name, func(t *testing.T) {
			f, err := NewFixture(smallFixture)
			if err != nil {
				t.Fatal(err)
			}
			tamper(f)
			p, err := GeneratePCSVerifier(f)
			if err != nil {
				t.Fatal(err)
			}
			if _, err := runProgram(t, p); err == nil {
				t.Fatal("tampered proof accepted")
			}
		})
	}
}
