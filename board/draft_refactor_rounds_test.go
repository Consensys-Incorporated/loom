package board

import (
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
)

// lookupShapedBuilder reproduces, by hand, the round structure that
// arguments.LookupUnionTuple produces today through inference:
//
//	round 0: fold challenge      stages the raw table columns s0 s1 t0 t1
//	round 1: log-derivative      stages the multiplicity column
//	round 2: folding (appended)  stages the logup running sum
//
// Anything this helper has to say twice is something the new API makes the
// caller responsible for, so it doubles as an ergonomics check.
func lookupShapedBuilder() RoundBuilder {
	b := NewRoundBuilder()
	m := NewModule("m")
	m.N = 8

	alpha := Coin(RoundFold)
	gamma := Coin(RoundLogDerivative)

	// Folded table columns feed the multiplicity and the running sum.
	foldedS := expr.Col("s0").Add(expr.Col("s1").Mul(alpha))
	foldedT := expr.Col("t0").Add(expr.Col("t1").Mul(alpha))

	m.AssertZero(foldedS.Sub(foldedT).Mul(expr.Col("mult")))
	m.AssertZero(expr.Col("logup").Mul(foldedT.Sub(gamma)).Sub(expr.Col("mult")))
	b.AddModule(m)

	b.StageColumns(RoundFold, "s0", "s1", "t0", "t1")

	b.AddStepAt(RoundLogDerivative,
		NewProverStep([]expr.Expr{foldedS, foldedT}, []string{"mult"}, CountMultiplicityStep, CMCtx{NbSources: 1, NbTargets: 1}))
	b.StageColumns(RoundLogDerivative, "mult")

	// "logup" is produced after the log-derivative challenge, so it is neither
	// staged nor given a round: CompileRounds sweeps it into the folding round.
	return b
}

func TestCompileRoundsShape(t *testing.T) {
	b := lookupShapedBuilder()
	prog, err := CompileRounds(&b)
	if err != nil {
		t.Fatalf("CompileRounds: %v", err)
	}

	if got := len(prog.Rounds); got != 3 {
		t.Fatalf("rounds = %d, want 3 (fold, log-derivative, folding)", got)
	}
	assertStaged(t, prog.Rounds[RoundFold], "s0", "s1", "t0", "t1")
	assertStaged(t, prog.Rounds[RoundLogDerivative], "mult")
	assertStaged(t, prog.Rounds[2], "logup")

	// Every staged column must carry its owning module, since
	// internal/protocol/layout.go groups commitments by module size.
	for _, round := range prog.Rounds {
		for _, ref := range round.Staged {
			if ref.Module != "m" {
				t.Errorf("column %q module = %q, want m", ref.Name, ref.Module)
			}
		}
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

func TestCompileRoundsRejectsDoubleStaging(t *testing.T) {
	b := lookupShapedBuilder()
	b.StageColumns(RoundLogDerivative, "s0") // already staged at round 0

	_, err := CompileRounds(&b)
	if err == nil {
		t.Fatal("expected an error when a column is staged twice")
	}
	if !strings.Contains(err.Error(), "staged twice") {
		t.Errorf("error = %v, want it to mention double staging", err)
	}
}

func TestCompileRoundsRejectsUnknownColumn(t *testing.T) {
	b := lookupShapedBuilder()
	b.StageColumns(RoundFold, "not_in_any_relation")

	_, err := CompileRounds(&b)
	if err == nil {
		t.Fatal("expected an error when staging a column no relation mentions")
	}
	if !strings.Contains(err.Error(), "not referenced by any module relation") {
		t.Errorf("error = %v, want it to mention the missing relation", err)
	}
}

// Property 2: a column committed a round before the step that fills it would be
// committed empty.
func TestValidateRejectsStagingBeforeProduction(t *testing.T) {
	b := NewRoundBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("x").Sub(expr.Col("y")))
	b.AddModule(m)

	b.StageColumns(RoundFold, "x", "y")
	// "y" is staged at round 0 but only produced at round 1.
	b.AddStepAt(RoundLogDerivative,
		NewProverStep([]expr.Expr{expr.Col("x")}, []string{"y"}, LogUpStep, LogUpCtx{}))

	_, err := CompileRounds(&b)
	if err == nil {
		t.Fatal("expected an error when a column is staged before it is produced")
	}
	if !strings.Contains(err.Error(), "before it is filled") {
		t.Errorf("error = %v, want it to mention premature commitment", err)
	}
}

// The folding round sweeps up unstaged columns, but must not absorb one that an
// earlier round's step produced: that column would cross a Fiat-Shamir boundary
// uncommitted. This is the case that distinguishes a genuine leftover from a
// staging mistake.
func TestCompileRoundsRefusesToSweepEarlyProducedColumn(t *testing.T) {
	var one koalabear.Element
	one.SetOne()

	b := NewRoundBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("logup").Mul(expr.Col("x")))
	b.AddModule(m)

	b.StageColumns(RoundFold, "x")
	// Produced at round 0 but never staged, so the sweep would otherwise commit
	// it two rounds later.
	b.AddStepAt(RoundFold,
		NewProverStep([]expr.Expr{expr.Col("x"), expr.Const(one)}, []string{"logup"}, LogUpStep, LogUpCtx{}))

	_, err := CompileRounds(&b)
	if err == nil {
		t.Fatal("expected an error when an early-produced column is left unstaged")
	}
	if !strings.Contains(err.Error(), "never staged") {
		t.Errorf("error = %v, want it to mention the missing staging", err)
	}
}

// Property 3: a step may not read a column a later round produces.
func TestValidateRejectsForwardColumnRead(t *testing.T) {
	b := NewRoundBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("early").Sub(expr.Col("late")))
	b.AddModule(m)

	b.AddStepAt(RoundFold,
		NewProverStep([]expr.Expr{expr.Col("late")}, []string{"early"}, LogUpStep, LogUpCtx{}))
	b.StageColumns(RoundFold, "early")
	b.AddStepAt(RoundLogDerivative,
		NewProverStep([]expr.Expr{expr.Col("early")}, []string{"late"}, LogUpStep, LogUpCtx{}))
	b.StageColumns(RoundLogDerivative, "late")

	_, err := CompileRounds(&b)
	if err == nil {
		t.Fatal("expected an error when a step reads a column produced later")
	}
	if !strings.Contains(err.Error(), "produced later") {
		t.Errorf("error = %v, want it to mention the forward read", err)
	}
}

// Property 4: the case old phase 3.5 defended against. A step in round r may
// not consume the challenge that round r itself samples — that challenge does
// not exist until after the round's commitment.
func TestValidateRejectsSameRoundChallengeUse(t *testing.T) {
	var one koalabear.Element
	one.SetOne()

	b := NewRoundBuilder()
	m := NewModule("m")
	m.N = 8
	m.AssertZero(expr.Col("logup").Mul(expr.Col("x").Sub(Coin(RoundLogDerivative))))
	b.AddModule(m)

	b.StageColumns(RoundFold, "x")
	// Staged in the same round it is produced, so property 2 holds and the only
	// thing wrong is the challenge: the step reads the coin its own round samples.
	b.AddStepAt(RoundLogDerivative,
		NewProverStep([]expr.Expr{expr.Col("x").Sub(Coin(RoundLogDerivative)), expr.Const(one)},
			[]string{"logup"}, LogUpStep, LogUpCtx{}))
	b.StageColumns(RoundLogDerivative, "logup")

	_, err := CompileRounds(&b)
	if err == nil {
		t.Fatal("expected an error when a step uses the challenge its own round samples")
	}
	if !strings.Contains(err.Error(), "only sampled at the end of round") {
		t.Errorf("error = %v, want it to mention the premature challenge use", err)
	}
}

// A relation may reference any round's challenge, including the appended
// folding round, but not one past the end.
func TestValidateRejectsOutOfRangeChallenge(t *testing.T) {
	b := lookupShapedBuilder()
	m := b.Modules["m"]
	m.AssertZero(expr.Col("s0").Mul(Coin(9)))

	_, err := CompileRounds(&b)
	if err == nil {
		t.Fatal("expected an error when a relation references a nonexistent round")
	}
	if !strings.Contains(err.Error(), "only 3 rounds") {
		t.Errorf("error = %v, want it to mention the round count", err)
	}
}

func TestParseCanonicalChallengeName(t *testing.T) {
	for _, level := range []int{0, 1, 7, 42} {
		name := constants.CanonicalChallengeName(level)
		got, ok := constants.ParseCanonicalChallengeName(name)
		if !ok || got != level {
			t.Errorf("round-trip of %q = (%d, %v), want (%d, true)", name, got, ok, level)
		}
	}
	// Argument-local challenge names must not be mistaken for round challenges.
	for _, bad := range []string{"gamma", "challenge@loom_", "challenge@loom_0x", "xchallenge@loom_0"} {
		if _, ok := constants.ParseCanonicalChallengeName(bad); ok {
			t.Errorf("ParseCanonicalChallengeName(%q) succeeded, want false", bad)
		}
	}
}

func TestStagedColumnsAddCol(t *testing.T) {
	var sc StagedColumns
	sc.AddCol("a")
	sc.AddCol("b", "c")
	if strings.Join(sc, ",") != "a,b,c" {
		t.Errorf("staged = %v, want [a b c]", sc)
	}
}
