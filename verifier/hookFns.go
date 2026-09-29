package verifier

import (
	"fmt"
	"github.com/consensys/gnark-crypto/field/koalabear"

	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/poly"
)

// HookFn evaluates one expr.VerifierColumn at zeta. Unlike committed columns,
// the value is reconstructed by the verifier rather than read from a prover
// opening, so each hook owns its own formula.
type HookFn func(vr *verifierRunTime, module board.CompiledModule, leaf *expr.Leaf) (ext.E6, error)

// HookMap resolves the HookID carried by a VerifierColumn leaf to its
// implementation. It is the single registry the merged computeVerifierColumns
// pass dispatches through; adding a new kind of verifier-computed column means
// registering a hook here rather than adding an expr.LeafType.
var HookMap map[expr.HookID]HookFn

func init() {
	HookMap = map[expr.HookID]HookFn{
		expr.LagrangeHook:       lagrange,
		expr.PublicInputHook:    publicInputs,
		expr.ExposedValueHook:   exposedColumns,
		expr.ExposedAverageHook: exposedAverage,
	}
}

func lagrange(vr *verifierRunTime, module board.CompiledModule, leaf *expr.Leaf) (ext.E6, error) {
	i := constants.ParseLagrangeName(leaf.Name)
	if i < 0 {
		i = module.N + i
	}
	return poly.LagrangeAtZetaExt(vr.zeta, module.N, i), nil
}

func publicInputs(vr *verifierRunTime, module board.CompiledModule, leaf *expr.Leaf) (ext.E6, error) {
	pi, ok := vr.publicInputs[leaf.Name]
	if !ok {
		return ext.E6{}, fmt.Errorf("publicInputs hook: %s not found in public inputs", leaf.Name)
	}
	if pi.Module != module.Name {
		return ext.E6{}, fmt.Errorf("publicInputs hook: %s belongs to module %q, used from module %q", leaf.Name, pi.Module, module.Name)
	}
	var val ext.E6
	for _, pe := range pi.Entries {
		if pe.Idx < 0 || pe.Idx >= module.N {
			return ext.E6{}, fmt.Errorf("publicInputs hook: %s entry index %d out of bounds for module %q of size %d", leaf.Name, pe.Idx, module.Name, module.N)
		}
		tmp := poly.LagrangeAtZetaExt(vr.zeta, module.N, pe.Idx)
		value := pe.ExtValue()
		tmp.Mul(&tmp, &value)
		val.Add(&val, &tmp)
	}
	return val, nil
}

// TODO bind the exposed values to FS -> either we add a step to bind the exposed values alone to FS
// OR we commit to the exposed columns, and use this hook only to let the verifier recompute the
// exposed column at zeta and check that it matches the prover's exposed columns at zeta
func exposedColumns(vr *verifierRunTime, module board.CompiledModule, leaf *expr.Leaf) (ext.E6, error) {
	pi, ok := vr.proof.ExposedValues[leaf.Name]
	if !ok {
		return ext.E6{}, fmt.Errorf("exposedColumns hook: %s not found in proof.ExposedValues", leaf.Name)
	}
	var lag ext.E6
	for _, pe := range pi.Entries {
		tmp := poly.LagrangeAtZetaExt(vr.zeta, module.N, pe.Idx)
		value := pe.ExtValue()
		tmp.Mul(&tmp, &value)
		lag.Add(&lag, &tmp)
	}
	return lag, nil
}

// exposedAverage evaluates the constant column T/N: T is the single entry the
// prover exposed under the leaf's name, and N the size of the module.
func exposedAverage(vr *verifierRunTime, module board.CompiledModule, leaf *expr.Leaf) (ext.E6, error) {
	pi, ok := vr.proof.ExposedValues[leaf.Name]
	if !ok || len(pi.Entries) != 1 {
		return ext.E6{}, fmt.Errorf("exposedAverage hook: %s must be exposed with exactly one entry", leaf.Name)
	}
	if module.N <= 0 {
		return ext.E6{}, fmt.Errorf("exposedAverage hook: module %q has size %d", module.Name, module.N)
	}
	var invN koalabear.Element
	invN.SetUint64(uint64(module.N))
	invN.Inverse(&invN)
	v := pi.Entries[0].ExtValue()
	v.MulByElement(&v, &invN)
	return v, nil
}
