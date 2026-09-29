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

	"github.com/consensys/loom/board"
)

// func AddLogupEqualityCheck(builder *board.Builder, moduleS, moduleT string, logupS, logupT []expr.Expr) {
func AddLogupEqualityCheck(builder *board.Builder, logupS, logupT []board.Column) {

	if (len(logupS) == 1) && len(logupT) == 1 && (logupS[0].Module == logupT[0].Module) {
		module := logupS[0].Module
		m := builder.Modules[module]
		positive := logupS[0].In
		negative := logupT[0].In
		m.AssertEqualRelativeAt(positive, negative, 0)
		builder.Modules[module] = m

	} else { // logup bus
		positives := make([]string, len(logupS))
		negatives := make([]string, len(logupT))
		for i, ls := range logupS {
			lsName := fmt.Sprintf("%s.%s_%d", ls.Module, ls.In.String(), 0)
			positives[i] = lsName
			builder.AddExposeLastEntryStep(board.RoundRunningSums, ls.Module, ls.In, lsName) // this step makes ls.In[N-1] accessible to the verifier
		}
		for i, lt := range logupT {
			ltName := fmt.Sprintf("%s.%s_%d", lt.Module, lt.In.String(), 0)
			negatives[i] = ltName
			builder.AddExposeLastEntryStep(board.RoundRunningSums, lt.Module, lt.In, ltName) // this step makes lt.In[N-1] accessible to the verifier
		}
		builder.AddLogupBus(board.NewLogupBus(positives, negatives))
	}
}
