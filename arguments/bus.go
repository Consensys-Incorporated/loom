// Copyright Consensys Software Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
// the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0

package arguments

import (
	"fmt"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/internal/constants"
)

// Bus argues that the messages sent and received balance: every tuple is sent
// as many times as it is received, where row(S[i]) is sent on the rows where
// selS[i] = 1 and row(R[i]) received on the rows where selR[i] = 1. The
// selectors must be boolean (the caller constrains them).
//
// It uses running ratios, as prover-ray's message bus does: each column
// multiplies the factors of the sends over those of the receives, so that a
// bus spanning several shards can be closed across them by multiplying their
// ends. A selected row contributes the factor
//
//	β + α^w + α^{w−1}·c_{w−1} + … + α·c_1 + c_0      (w = width, α^w a length sentinel)
//
// and an unselected row the factor 1, as sel·(factor − 1) + 1. The factors of
// each module are packed into running-ratio columns, sends as numerators and
// receives as denominators, within board.MaxLogupDegree; the product bus
// checks that the ends multiply to one. It uses the
// rounds of a lookup: α = Coin(RoundFold), β = Coin(RoundLogDerivative), the
// columns at RoundRunningSums.
func Bus(builder *board.Builder, selS, selR []expr.Expr, S, R []board.Table) error {
	if len(selS) != len(S) {
		return fmt.Errorf("selS has %d chunks, but S has %d chunks", len(selS), len(S))
	}
	if len(selR) != len(R) {
		return fmt.Errorf("selR has %d chunks, but R has %d chunks", len(selR), len(R))
	}
	if len(S) == 0 && len(R) == 0 {
		return nil
	}
	all := append(append([]board.Table(nil), S...), R...)
	if err := checkWidths(all[:1], all); err != nil {
		return err
	}
	for _, t := range all {
		builder.StageLeaves(board.RoundFold, t.In...)
	}
	builder.StageLeaves(board.RoundFold, selS...)
	builder.StageLeaves(board.RoundFold, selR...)

	ends, err := addRunningRatios(builder, busFactors(S, selS), busFactors(R, selR))
	if err != nil {
		return err
	}
	builder.AddProductBus(board.ProductBus{Ends: ends})
	return nil
}

// busFactor is the per-row factor of one port, in its module.
type busFactor struct {
	module string
	f      expr.Expr
}

// busFactors returns the factor sel·(β + fold(row) − 1) + 1 of each table.
func busFactors(tables []board.Table, sels []expr.Expr) []busFactor {
	alpha := board.Coin(board.RoundFold)
	beta := board.Coin(board.RoundLogDerivative)
	one := expr.Const(koalabear.One())
	res := make([]busFactor, len(tables))
	for i, t := range tables {
		// Horner from the sentinel: α^w + α^{w−1}·c_{w−1} + … + c_0
		fold := alpha.Add(t.In[len(t.In)-1])
		for j := len(t.In) - 2; j >= 0; j-- {
			fold = fold.Mul(alpha).Add(t.In[j])
		}
		res[i] = busFactor{t.Module, sels[i].Mul(fold.Add(beta).Sub(one)).Add(one)}
	}
	return res
}

// addRunningRatios groups the factors by module, in order of first
// appearance, into running-ratio columns num/den at RoundRunningSums within
// board.MaxLogupDegree, and returns the names of their exposed ends. Each
// column takes, alternately, the module's next denominator and next
// numerator while its degree allows.
func addRunningRatios(builder *board.Builder, num, den []busFactor) ([]string, error) {
	var order []string
	byModule := map[string]*[2][]expr.Expr{}
	add := func(fs []busFactor, side int) {
		for _, f := range fs {
			if _, ok := byModule[f.module]; !ok {
				order = append(order, f.module)
				byModule[f.module] = new([2][]expr.Expr)
			}
			byModule[f.module][side] = append(byModule[f.module][side], f.f)
		}
	}
	add(num, 0)
	add(den, 1)
	var ends []string
	for _, module := range order {
		nums, dens := byModule[module][0], byModule[module][1]
		for len(nums) > 0 || len(dens) > 0 {
			var cn, cd []expr.Expr
			for grown := true; grown; {
				grown = false
				if len(dens) > 0 && board.RunningRatioConstraintDegree(cn, append(cd, dens[0])) <= board.MaxLogupDegree {
					cd, dens, grown = append(cd, dens[0]), dens[1:], true
				}
				if len(nums) > 0 && board.RunningRatioConstraintDegree(append(cn, nums[0]), cd) <= board.MaxLogupDegree {
					cn, nums, grown = append(cn, nums[0]), nums[1:], true
				}
			}
			if len(cn) == 0 && len(cd) == 0 {
				return nil, fmt.Errorf("module %s: a bus factor alone exceeds degree %d", module, board.MaxLogupDegree)
			}
			base, err := constants.RandomString(10)
			if err != nil {
				return nil, err
			}
			end, err := builder.AddRunningRatioStep(board.RoundRunningSums, module, cn, cd, fmt.Sprintf("%s.busratio_%s", module, base))
			if err != nil {
				return nil, fmt.Errorf("module %s: %w", module, err)
			}
			ends = append(ends, end)
		}
	}
	return ends, nil
}
