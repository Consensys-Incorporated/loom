package board

import (
	"fmt"
	"sort"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/dag"
)

// Program the double slice [][] means that the steps are scheduled
type Program struct {
	Modules               map[string]CompiledModule
	SetupColumns          []ColumnRef   // setup columns, precommitted (ex: ql, qr, etc in plonk)
	FScolumnsDependencies [][]ColumnRef // one []ColumnRef per FS round
	ColumnFields          map[string]field.Kind
	LogupBus              []LogupBus
	Steps                 [][]ProverStep
}

// TODO group modules per size, fold the vanishing relations per modules of the same size -> less calls to ComputeQuotient
func (pg *Program) SetSize(module string, size int) {
	_, ok := pg.Modules[module]
	if !ok {
		panic(fmt.Errorf("module %s not found in the trace", module))
	}
	m := pg.Modules[module]
	m.N = int(ecc.NextPowerOfTwo(uint64(size)))
	m.D = fft.NewDomain(uint64(m.N))
	pg.Modules[module] = m
}

func Compile(b *Builder) (Program, error) {

	config := expr.NewConfig()
	onlyChallenges := expr.NewConfig(expr.OnlyChallenges...)

	isFSStep := make([]bool, len(b.Steps))
	for i, step := range b.Steps {
		_, isFSStep[i] = step.Ctx.(FSCtx)
	}

	// --- Phase 1: Initial level computation via fixed-point. ---
	// level[i] = max(varLevel[dep]+1 for all deps in Ins) or 0 if no known deps.

	stepLevel := make([]int, len(b.Steps))
	varLevel := map[string]int{}
	for i := 0; i < len(b.Steps); i++ {
		stepLevel[i] = -1
	}
	for {
		changed := false
		for i, step := range b.Steps {
			lvl := 0
			for _, inp := range step.Ins {
				for _, leaf := range inp.LeavesFull(config) {
					if l, ok := varLevel[leaf.Name]; ok && l+1 > lvl {
						lvl = l + 1
					}
				}
			}
			if stepLevel[i] != lvl {
				stepLevel[i] = lvl
				changed = true
			}
			for _, o := range step.Outs {
				varLevel[o] = lvl
			}
		}
		if !changed {
			break
		}
	}

	// --- Phase 2: Assign each FS step a "round". ---
	// Two FS steps belong to the same round when neither's challenge feeds the
	// other's inputs (directly or transitively through FS outputs only).
	// round[i] = 1 + max round of any FS step whose challenge appears in step i's inputs.

	challengeProducer := map[string]int{} // challenge name → index of the FS step that outputs it
	for i, step := range b.Steps {
		if isFSStep[i] {
			for _, o := range step.Outs {
				challengeProducer[o] = i
			}
		}
	}

	fsRound := make([]int, len(b.Steps))
	for i := 0; i < len(b.Steps); i++ {
		fsRound[i] = -1
	}
	for {
		changed := false
		for i, step := range b.Steps {
			if !isFSStep[i] {
				continue
			}
			round := 0
			for _, inp := range step.Ins {
				for _, name := range inp.Leaves(onlyChallenges) {
					if j, ok := challengeProducer[name]; ok && fsRound[j]+1 > round {
						round = fsRound[j] + 1
					}
				}
			}
			if fsRound[i] != round {
				fsRound[i] = round
				changed = true
			}
		}
		if !changed {
			break
		}
	}

	// --- Phase 3: Sync FS steps in the same round to the max level in that round. ---

	maxLevelForRound := map[int]int{}
	for i := range b.Steps {
		if !isFSStep[i] {
			continue
		}
		r := fsRound[i]
		if l, ok := maxLevelForRound[r]; !ok || stepLevel[i] > l {
			maxLevelForRound[r] = stepLevel[i]
		}
	}
	for i, step := range b.Steps {
		if !isFSStep[i] {
			continue
		}
		stepLevel[i] = maxLevelForRound[fsRound[i]]
		for _, o := range step.Outs {
			varLevel[o] = stepLevel[i]
		}
	}

	// --- Phase 3.5: Enforce strictly increasing levels across rounds. ---
	// Phase 3 syncs FS steps within each round to that round's max level, but
	// does not propagate the change to later rounds. If round r is bumped up,
	// round r+1 must also be bumped to at least round-r-level+1, and so on.
	// Without this, two FS steps from different rounds can land on the same
	// level and get merged into one canonical challenge — breaking arguments

	// (like grand product) that need distinct fold/randomness challenges.
	{
		rounds := make([]int, 0, len(maxLevelForRound))
		for r := range maxLevelForRound {
			rounds = append(rounds, r)
		}
		sort.Ints(rounds)
		minLevel := -1
		for _, r := range rounds {
			if maxLevelForRound[r] <= minLevel {
				maxLevelForRound[r] = minLevel + 1
			}
			minLevel = maxLevelForRound[r]
		}
		// Re-apply updated levels to FS steps and varLevel.
		for i, step := range b.Steps {
			if !isFSStep[i] {
				continue
			}
			stepLevel[i] = maxLevelForRound[fsRound[i]]
			for _, o := range step.Outs {
				varLevel[o] = stepLevel[i]
			}
		}
	}

	// --- Phase 4: Re-propagate non-FS levels, skipping over FS levels. ---
	// FS steps are frozen; non-FS steps are recomputed from dependencies,
	// then bumped past any FS level they land on.

	fsLevelSet := map[int]bool{}
	for i := range b.Steps {
		if isFSStep[i] {
			fsLevelSet[stepLevel[i]] = true
		}
	}

	for {
		changed := false
		for i, step := range b.Steps {
			if isFSStep[i] {
				continue
			}
			lvl := 0
			for _, inp := range step.Ins {
				for _, leaf := range inp.LeavesFull(config) {
					if l, ok := varLevel[leaf.Name]; ok && l+1 > lvl {
						lvl = l + 1
					}
				}
			}
			for fsLevelSet[lvl] {
				lvl++
			}
			if stepLevel[i] != lvl {
				stepLevel[i] = lvl
				changed = true
			}
			for _, o := range step.Outs {
				varLevel[o] = lvl
			}
		}
		if !changed {
			break
		}
	}

	// --- Phase 5: Group steps by level. ---

	maxLevel := 0
	for _, l := range stepLevel {
		if l > maxLevel {
			maxLevel = l
		}
	}

	var res Program
	res.Steps = make([][]ProverStep, maxLevel+1)
	for i, step := range b.Steps {
		res.Steps[stepLevel[i]] = append(res.Steps[stepLevel[i]], step)
	}

	// --- Phase 6: Add a FiatShamir at the highest level, to sample the folding challenge ---

	res.Steps = append(res.Steps, make([]ProverStep, 1))
	foldingChallenge, err := constants.RandomString(10)
	if err != nil {
		return res, err
	}
	res.Steps[maxLevel+1][0] = NewProverStep(nil, []string{foldingChallenge}, FSStep, FSCtx{})

	// --- Phase 7: Collapse FS steps of the same round (level) into one canonical step. ---

	// Config: keep committed and shifted committed columns; discard virtual verifier-side leaves.
	noLagrangeNoChallengeNoExposedCols := expr.NewConfig(
		expr.WithoutChallenges(),
		expr.WithoutSetupColumns(),
		expr.WithoutVerifierColumns(),
	)

	// Step 7a: Identify which levels are FS steps and assign round indices in level order.
	// from the preivous Phase, a level either contains only FS, or no FS at all
	levelToRound := map[int]int{}
	roundIdx := 0
	for lvl := 0; lvl < len(res.Steps); lvl++ {
		for _, step := range res.Steps[lvl] {
			if _, ok := step.Ctx.(FSCtx); ok {
				levelToRound[lvl] = roundIdx
				roundIdx++
				break // only one round per FS level
			}
		}
	}
	numRounds := roundIdx

	// Step 7b: Build rename map: old FS output name → canonical "challenge@loom_<i>".
	renameExprs := make(map[string]expr.Expr, numRounds)
	for lvl, round := range levelToRound {
		canonical := constants.CanonicalChallengeName(round)
		for _, step := range res.Steps[lvl] {
			if _, ok := step.Ctx.(FSCtx); ok {
				for _, o := range step.Outs {
					renameExprs[o] = expr.Challenge(canonical)
				}
			}
		}
	}
	applyRename := func(e expr.Expr) expr.Expr {
		return expr.ReplaceLeavesByMap(e, renameExprs)
	}

	// Step 7c: Apply rename to module relations in the builder.
	for _, m := range b.Modules {
		for i, rel := range m.Relations {
			m.Relations[i] = applyRename(rel)
		}
	}

	// Step 7d: Apply rename to non-FS step Ins in res.Steps.
	for lvl := range res.Steps {
		for j := range res.Steps[lvl] {
			if _, ok := res.Steps[lvl][j].Ctx.(FSCtx); ok {
				continue
			}
			for k, inp := range res.Steps[lvl][j].Ins {
				res.Steps[lvl][j].Ins[k] = applyRename(inp)
			}
		}
	}

	// Step 7e: Infer setup columns, build res.FiatShamir and replace
	// per-round FS steps with a single canonical one.
	res.SetupColumns = collectSetupColumns(b.Modules)
	res.FScolumnsDependencies = make([][]ColumnRef, numRounds)

	// Build a column-name → owning-module map by scanning every module's
	// relations. This lets us tag each FS-bound column with its module so the
	// prover can group commitments by polynomial size.
	columnModule := map[string]string{}
	for moduleName, m := range b.Modules {
		for _, rel := range m.Relations {
			for _, leaf := range rel.LeavesFull(noLagrangeNoChallengeNoExposedCols) {
				columnModule[leaf.Name] = moduleName
			}
		}
	}

	prevCovered := map[string]bool{}
	for _, c := range res.SetupColumns {
		prevCovered[c.Name] = true
	}
	for lvl := 0; lvl < len(res.Steps); lvl++ {
		round, ok := levelToRound[lvl]
		if !ok {
			continue
		}
		canonical := constants.CanonicalChallengeName(round)

		// Collect input column names for this round (disjoint from all previous rounds).
		for _, step := range res.Steps[lvl] {
			if _, ok := step.Ctx.(FSCtx); !ok {
				continue
			}
			for _, inp := range step.Ins {
				for _, leaf := range inp.LeavesFull(noLagrangeNoChallengeNoExposedCols) {
					if !prevCovered[leaf.Name] {
						prevCovered[leaf.Name] = true
						mod, ok := columnModule[leaf.Name]
						if !ok {
							return res, fmt.Errorf("Compile: column %q referenced by FS step has no owning module", leaf.Name)
						}
						res.FScolumnsDependencies[round] = append(res.FScolumnsDependencies[round], ColumnRef{Name: leaf.Name, Module: mod})
					}
				}
			}
		}

		// Replace all FS steps at this level with one canonical step (Ins is nil;
		// callers use res.FiatShamir[round] for the committed column list).
		newSteps := make([]ProverStep, 0, len(res.Steps[lvl]))
		for _, step := range res.Steps[lvl] {
			if _, ok := step.Ctx.(FSCtx); !ok {
				newSteps = append(newSteps, step)
			}
		}
		newSteps = append(newSteps, NewProverStep(nil, []string{canonical}, FSStep, FSCtx{}))
		res.Steps[lvl] = newSteps
	}

	// --- Phase 8: Extend the last FiatShamir entry (folding round) with all
	// module-relation columns not yet covered by any earlier round. ---
	// The last canonical FS step already has Ins=nil (set in phase 7e).

	lastRound := numRounds - 1
	for moduleName, m := range b.Modules {
		for _, rel := range m.Relations {
			for _, leaf := range rel.LeavesFull(noLagrangeNoChallengeNoExposedCols) {
				if !prevCovered[leaf.Name] {
					prevCovered[leaf.Name] = true
					res.FScolumnsDependencies[lastRound] = append(res.FScolumnsDependencies[lastRound], ColumnRef{Name: leaf.Name, Module: moduleName})
				}
			}
		}
	}

	res.ColumnFields = inferProgramColumnFields(&res, b.Modules)
	applyProgramColumnFields(&res)

	// --- Phase 9: create the compiled module. Fold the relations in each module,
	// and create a domain of the module.N for each module
	res.Modules = map[string]CompiledModule{}
	lastChallenge := expr.Challenge(fmt.Sprintf("challenge@loom_%d", lastRound))
	for k, m := range b.Modules {
		var cm CompiledModule
		cm.Name = m.Name
		cm.GenCol = make([]Gen, len(m.GenCol))
		copy(cm.GenCol, m.GenCol)
		cm.N = m.N
		cm.D = fft.NewDomain(uint64(m.N))
		foldedRelation := expr.Fold(lastChallenge, m.Relations)
		cm.VanishingRelation = dag.ExprToDAGWithColumnFields(foldedRelation, res.ColumnFields)
		res.Modules[k] = cm
	}

	// get the logup bus
	res.LogupBus = make([]LogupBus, len(b.LogupBus))
	copy(res.LogupBus, b.LogupBus)

	return res, nil
}

func inferProgramColumnFields(program *Program, modules map[string]*Module) map[string]field.Kind {
	fields := make(map[string]field.Kind)

	// Field inference is monotone: Base can only stay Base or be upgraded to
	// Ext, and Ext never downgrades. This makes the seeding order, relation
	// walk, and step iteration order irrelevant; every update is joined with
	// the current value.
	setField := func(name string, f field.Kind) {
		fields[name] = field.Join(fields[name], f)
	}

	for _, ref := range program.SetupColumns {
		setField(ref.Name, ref.Field)
	}

	// VerifierColumns are included: FieldKind pins them to Ext, so every column
	// the verifier evaluates at zeta is seeded as Ext here.
	columnConfig := expr.NewConfig(expr.WithoutChallenges())
	for _, m := range modules {
		for _, rel := range m.Relations {
			// Capture any explicitly-declared Ext leaves (e.g. via expr.ExtCol).
			// The fields-map argument is irrelevant here (single-leaf input ⇒
			// self-cancels via Join); we keep the general helper to mirror the
			// step walk's call shape below.
			for _, leaf := range rel.LeavesFull(columnConfig) {
				setField(leaf.Name, expr.FieldOfWithColumnFields(leaf, fields))
			}
		}
	}

	for _, level := range program.Steps {
		for _, step := range level {
			outFields := inferStepOutputFields(step, fields)
			for i, out := range step.Outs {
				f := field.Base
				if i < len(outFields) {
					f = outFields[i]
				}
				setField(out, f)
			}
		}
	}

	return fields
}

func collectSetupColumns(modules map[string]*Module) []ColumnRef {
	config := expr.NewConfig(expr.OnlySetupColumns...)
	byKey := make(map[string]ColumnRef)

	for moduleName, m := range modules {
		for _, rel := range m.Relations {
			for _, leaf := range rel.LeavesFull(config) {
				key := moduleName + "\x00" + leaf.Name
				ref := byKey[key]
				ref.Name = leaf.Name
				ref.Module = moduleName
				ref.Field = field.Join(ref.Field, leaf.FieldKind())
				byKey[key] = ref
			}
		}
	}

	keys := make([]string, 0, len(byKey))
	for key := range byKey {
		keys = append(keys, key)
	}
	sort.Strings(keys)

	res := make([]ColumnRef, 0, len(keys))
	for _, key := range keys {
		res = append(res, byKey[key])
	}
	return res
}

func applyProgramColumnFields(program *Program) {
	for i := range program.SetupColumns {
		ref := &program.SetupColumns[i]
		ref.Field = field.Join(ref.Field, program.ColumnFields[ref.Name])
	}
	for round := range program.FScolumnsDependencies {
		for i := range program.FScolumnsDependencies[round] {
			ref := &program.FScolumnsDependencies[round][i]
			ref.Field = field.Join(ref.Field, program.ColumnFields[ref.Name])
		}
	}
}

func inferStepOutputFields(step ProverStep, columnFields map[string]field.Kind) []field.Kind {
	res := make([]field.Kind, len(step.Outs))

	fieldOfInputs := func(ins []expr.Expr) field.Kind {
		f := field.Base
		for _, in := range ins {
			f = field.Join(f, expr.FieldOfWithColumnFields(in, columnFields))
		}
		return f
	}

	switch ctx := step.Ctx.(type) {
	case FSCtx:
		for i := range res {
			res[i] = field.Ext
		}
	case LogUpCtx, GPCtx:
		f := fieldOfInputs(step.Ins)
		for i := range res {
			res[i] = f
		}
	case ExposeEntriesCtx, ExposeIthValueCtx, ExposeRelativeIthValueCtx:
		f := field.Base
		if len(step.Ins) > 0 {
			f = expr.FieldOfWithColumnFields(step.Ins[0], columnFields)
		}
		for i := range res {
			res[i] = f
		}
	case CMCtx:
		for i := range res {
			res[i] = field.Base
		}
	case CMWCtx:
		f := field.Base
		for i := 0; i < ctx.NbSources && i < len(step.Ins); i++ {
			f = field.Join(f, expr.FieldOfWithColumnFields(step.Ins[i], columnFields))
		}
		for i := range res {
			res[i] = f
		}
	default:
		f := fieldOfInputs(step.Ins)
		for i := range res {
			res[i] = f
		}
	}

	return res
}
