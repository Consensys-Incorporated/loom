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

package protocol

import (
	"fmt"
	"sort"

	"github.com/consensys/loom/board"
	"github.com/consensys/loom/internal/constants"
	"github.com/consensys/loom/internal/fri"
)

// FRIParams returns the FRI parameters of a program's proofs: the domain of
// the maximum module size, RATE·2^MAX_LOG_MODULE_SIZE, whatever the program's
// module sizes (see fri.Proof: the rounds before the largest module's have no
// layer). It fails if a module exceeds the maximum size.
func FRIParams(program board.Program, numQueries int, lh fri.LeafHasher, nh fri.NodeHasher, opts ...fri.Option) (fri.Params, error) {
	const maxN = 1 << constants.MAX_LOG_MODULE_SIZE
	names := make([]string, 0, len(program.Modules))
	for name := range program.Modules {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		if n := program.Modules[name].N; n > maxN {
			return fri.Params{}, fmt.Errorf("module %q has size %d, above the maximum 2^%d", name, n, constants.MAX_LOG_MODULE_SIZE)
		}
	}
	return fri.NewParams(constants.RATE*maxN, maxN, numQueries, lh, nh, opts...)
}
