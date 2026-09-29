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

// Program is a compiled protocol: modules with their folded vanishing
// relations, and the rounds in which the prover computes and commits columns.
type Program struct {
	Modules      map[string]CompiledModule
	SetupColumns []ColumnRef // setup columns, precommitted (ex: ql, qr, etc in plonk)
	ColumnFields map[string]field.Kind
	LogupBus     []LogupBus
	// Rounds are the Fiat-Shamir rounds, in order. The last one is the folding
	// round: Coin(len(Rounds)-1) folds the per-module relations.
	Rounds []ProverRound
	// Late lists columns committed later than the round that produces them. It
	// is diagnostic, not an error; see StrictNoLateStaging.
	Late []LateColumn
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

// Compile turns a Builder into a Program. It resolves and validates the
// declared rounds (see rounds.go), infers column fields, and folds each
// module's relations with the folding round's challenge.
func Compile(b *Builder) (Program, error) {
	var res Program

	rounds, late, err := compileRounds(b)
	if err != nil {
		return res, err
	}
	res.Rounds = rounds
	res.Late = late
	res.SetupColumns = collectSetupColumns(b.Modules)

	res.ColumnFields = inferProgramColumnFields(&res, b.Modules)
	applyProgramColumnFields(&res)

	// Create the compiled modules: fold the relations of each module with the
	// folding challenge, and create a domain of size module.N.
	res.Modules = map[string]CompiledModule{}
	foldingChallenge := Coin(len(res.Rounds) - 1)
	for k, m := range b.Modules {
		var cm CompiledModule
		cm.Name = m.Name
		cm.GenCol = make([]Gen, len(m.GenCol))
		copy(cm.GenCol, m.GenCol)
		cm.N = m.N
		cm.D = fft.NewDomain(uint64(m.N))
		foldedRelation := expr.Fold(foldingChallenge, m.Relations)
		cm.VanishingRelation = dag.ExprToDAGWithColumnFields(foldedRelation, res.ColumnFields)
		res.Modules[k] = cm
	}

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

	for r, round := range program.Rounds {
		setField(constants.CanonicalChallengeName(r), field.Ext)
		for _, step := range round.Steps {
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
	for r := range program.Rounds {
		for i := range program.Rounds[r].Staged {
			ref := &program.Rounds[r].Staged[i]
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

	switch step.Ctx.(type) {
	case CyclicLogUpCtx, GPCtx:
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
	case LMCtx:
		for i := range res {
			res[i] = field.Base
		}
	default:
		f := fieldOfInputs(step.Ins)
		for i := range res {
			res[i] = f
		}
	}

	return res
}
