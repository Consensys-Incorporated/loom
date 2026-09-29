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

package expr

import "github.com/consensys/gnark-crypto/field/koalabear"

// Fold returns \Sigma_{i} v^iC[i].
// v can be any Expr (Var, Placeholder, etc.).
// Returns the zero constant when C is empty.
func Fold(v Expr, C []Expr) Expr {
	if len(C) == 0 {
		return Const(koalabear.Element{})
	}
	// Horner form, C[0] + v·(C[1] + v·(C[2] + …)): linear in len(C), whereas
	// expanding each v^i separately is quadratic. v is cloned per level so no
	// subtree is shared (Prune rewrites nodes in place).
	res := C[len(C)-1]
	for i := len(C) - 2; i >= 0; i-- {
		res = C[i].Add(Clone(v).Mul(res))
	}
	return res
}
