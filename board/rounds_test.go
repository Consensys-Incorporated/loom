package board

import (
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
)

// lookupShapedBuilder reproduces by hand the round structure of
// arguments.LookupUnionTuple:
//
//	round 0 (RoundFold):          stages s0 s1 t0 t1 and their multiplicity
//	round 1 (RoundLogDerivative): stages nothing, samples the lookup challenge
//	round 2 (RoundRunningSums):   computes the running sum, swept into it;
//	                              its challenge folds the relations
func lookupShapedBuilder() Builder {
	b := NewBuilder()
	m := NewModule("m")
	m.N = 8

	alpha := Coin(RoundFold)
	gamma := Coin(RoundLogDerivative)
	foldedS := expr.Col("s0").Add(expr.Col("s1").Mul(alpha))
	foldedT := expr.Col("t0").Add(expr.Col("t1").Mul(alpha))

	m.AssertZero(foldedS.Sub(foldedT))
	m.AssertZero(expr.Col("logup").Mul(foldedT.Sub(gamma)).Sub(expr.Col("mult_0")))
	b.AddModule(m)

	b.StageColumns(RoundFold, "s0", "s1", "t0", "t1")
	b.AddLookupMultiplicityStep(RoundFold, nil, nil,
		[][]expr.Expr{{expr.Col("s0"), expr.Col("s1")}},
		[][]expr.Expr{{expr.Col("t0"), expr.Col("t1")}}, "mult")
	b.StageColumns(RoundFold, "mult_0")

	b.AddStepAt(RoundRunningSums,
		NewProverStep([]expr.Expr{foldedT.Sub(gamma), expr.Col("mult_0")}, []string{"logup"}, LogUpStep, LogUpCtx{}))
	return b
}

func TestCompileRoundsShape(t *testing.T) {
	b := lookupShapedBuilder()
	prog, err := Compile(&b)
	if err != nil {
		t.Fatalf("Compile: %v", err)
	}

	if got := len(prog.Rounds); got != 3 {
		t.Fatalf("rounds = %d, want 3", got)
	}
	assertStaged(t, prog.Rounds[RoundFold], "s0", "s1", "t0", "t1", "mult_0")
	assertStaged(t, prog.Rounds[RoundLogDerivative])
	assertStaged(t, prog.Rounds[RoundRunningSums], "logup")

	// Every staged column must carry its owning module, since
	// internal/protocol/layout.go groups commitments by module size.
	for _, round := range prog.Rounds {
		for _, ref := range round.Staged {
			if ref.Module != "m" {
				t.Errorf("column %q module = %q, want m", ref.Name, ref.Module)
			}
		}
	}
	if len(prog.Late) != 0 {
		t.Errorf("Late = %v, want empty", prog.Late)
	}
}

func assertStaged(t *testing.T, round ProverRound, want ...string) {
	t.Helper()
	got := make([]string, len(round.Staged))
	for i, ref := range round.Staged {
		got[i] = ref.Name
	}
	if strings.Join(got, ",") != strings.Join(want, ",") {
		t.Errorf("staged = %v, want %v", got, want)
	}
}

func compileErr(t *testing.T, b *Builder, want string) {
	t.Helper()
	_, err := Compile(b)
	if err == nil {
		t.Fatalf("expected an error mentioning %q", want)
	}
	if !strings.Contains(err.Error(), want) {
		t.Errorf("error = %v, want it to mention %q", err, want)
	}
}

func TestCompileRoundsRejectsDoubleStaging(t *testing.T) {
	b := lookupShapedBuilder()
	b.StageColumns(RoundLogDerivative, "s0") // already staged at round 0
	compileErr(t, &b, "staged twice")
}

func TestStageColumnsSameRoundIsIdempotent(t *testing.T) {
	b := lookupShapedBuilder()
	b.StageColumns(RoundFold, "s0", "t1") // already staged at round 0
	prog, err := Compile(&b)
	if err != nil {
		t.Fatalf("Compile: %v", err)
	}
	assertStaged(t, prog.Rounds[RoundFold], "s0", "s1", "t0", "t1", "mult_0")
}

func TestCompileRoundsRejectsUnknownColumn(t *testing.T) {
	b := lookupShapedBuilder()
	b.StageColumns(RoundFold, "not_in_any_relation")
	compileErr(t, &b, "not referenced by any module relation")
}

// Property 2: a column committed a round before the step that fills it would be
// committed empty.
func TestValidateRejectsStagingBeforeProduction(t *testing.T) {
	b := NewBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("x").Sub(expr.Col("y")))
	b.AddModule(m)

	b.StageColumns(RoundFold, "x", "y")
	b.AddStepAt(RoundLogDerivative,
		NewProverStep([]expr.Expr{expr.Col("x")}, []string{"y"}, LogUpStep, LogUpCtx{}))
	compileErr(t, &b, "before it is filled")
}

// Staging is opt-in: a caller who declares nothing still gets a valid
// single-round protocol, with every column swept into it.
func TestCompileRoundsSweepsEverythingWhenNothingDeclared(t *testing.T) {
	b := NewBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("x").Sub(expr.Col("y")))
	b.AddModule(m)

	prog, err := Compile(&b)
	if err != nil {
		t.Fatalf("Compile: %v", err)
	}
	if got := len(prog.Rounds); got != 1 {
		t.Fatalf("rounds = %d, want 1", got)
	}
	assertStaged(t, prog.Rounds[0], "x", "y")
}

// An unstaged column produced by an earlier round's step is swept into the last
// round, and recorded in Late so the late commitment is visible.
func TestCompileRoundsSweepsEarlyProducedColumnAndRecordsIt(t *testing.T) {
	var one koalabear.Element
	one.SetOne()

	b := NewBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("logup").Mul(expr.Col("x")))
	b.AddModule(m)

	b.StageColumns(RoundFold, "x")
	b.AddStepAt(RoundFold,
		NewProverStep([]expr.Expr{expr.Col("x"), expr.Const(one)}, []string{"logup"}, LogUpStep, LogUpCtx{}))
	b.growTo(RoundLogDerivative) // last declared round: the sweep lands at 1

	prog, err := Compile(&b)
	if err != nil {
		t.Fatalf("Compile: %v", err)
	}
	assertStaged(t, prog.Rounds[1], "logup")
	if len(prog.Late) != 1 {
		t.Fatalf("Late = %v, want exactly one entry", prog.Late)
	}
	if got := prog.Late[0]; got.Name != "logup" || got.Produced != 0 || got.Staged != 1 {
		t.Errorf("Late[0] = %+v, want {logup 0 1}", got)
	}
	if err := prog.StrictNoLateStaging(); err == nil {
		t.Error("StrictNoLateStaging accepted a late-committed column")
	}
}

// Property 3: a step may not read a column produced later, even within its own
// round.
func TestValidateRejectsForwardColumnRead(t *testing.T) {
	b := NewBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("early").Sub(expr.Col("late")))
	b.AddModule(m)

	b.AddStepAt(RoundFold,
		NewProverStep([]expr.Expr{expr.Col("late")}, []string{"early"}, LogUpStep, LogUpCtx{}))
	b.AddStepAt(RoundFold,
		NewProverStep([]expr.Expr{expr.Col("early")}, []string{"late"}, LogUpStep, LogUpCtx{}))
	compileErr(t, &b, "before it is produced")
}

// Property 3: a step may not read a column committed after its round, since the
// prover could still choose that column.
func TestValidateRejectsReadOfLaterStagedColumn(t *testing.T) {
	b := NewBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("x").Sub(expr.Col("y")).Mul(expr.Col("m_0")))
	b.AddModule(m)

	b.AddLookupMultiplicityStep(RoundFold, nil, nil,
		[][]expr.Expr{{expr.Col("x")}}, [][]expr.Expr{{expr.Col("y")}}, "m")
	b.StageColumns(RoundFold, "m_0")
	b.growTo(RoundLogDerivative) // x and y are swept into round 1
	compileErr(t, &b, "staged later")
}

// Property 4: a step in round r may not consume the challenge that round r
// itself samples.
func TestValidateRejectsSameRoundChallengeUse(t *testing.T) {
	var one koalabear.Element
	one.SetOne()

	b := NewBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("logup").Mul(expr.Col("x").Sub(Coin(RoundLogDerivative))))
	b.AddModule(m)

	b.StageColumns(RoundFold, "x")
	b.AddStepAt(RoundLogDerivative,
		NewProverStep([]expr.Expr{expr.Col("x").Sub(Coin(RoundLogDerivative)), expr.Const(one)},
			[]string{"logup"}, LogUpStep, LogUpCtx{}))
	compileErr(t, &b, "only sampled at the end of round")
}

func TestValidateRejectsNonCanonicalChallenge(t *testing.T) {
	b := NewBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("x").Mul(expr.Challenge("gamma")))
	b.AddModule(m)
	compileErr(t, &b, "not a round coin")
}

// A relation may reference any round's challenge, but not one past the end.
func TestValidateRejectsOutOfRangeChallenge(t *testing.T) {
	b := lookupShapedBuilder()
	b.Modules["m"].AssertZero(expr.Col("s0").Mul(Coin(9)))
	compileErr(t, &b, "only 3 rounds")
}

func TestParseCanonicalChallengeName(t *testing.T) {
	for _, level := range []int{0, 1, 7, 42} {
		name := constants.CanonicalChallengeName(level)
		got, ok := constants.ParseCanonicalChallengeName(name)
		if !ok || got != level {
			t.Errorf("round-trip of %q = (%d, %v), want (%d, true)", name, got, ok, level)
		}
	}
	for _, bad := range []string{"gamma", "challenge@loom_", "challenge@loom_0x", "xchallenge@loom_0"} {
		if _, ok := constants.ParseCanonicalChallengeName(bad); ok {
			t.Errorf("ParseCanonicalChallengeName(%q) succeeded, want false", bad)
		}
	}
}
