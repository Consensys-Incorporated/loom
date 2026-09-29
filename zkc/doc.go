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

// Package zkc contains a prototype of loom's PCS verifier written in zkc
// (github.com/LFDT-Lineth/zkc), for measuring the cost of recursive
// verification. The zkc sources are generated from Go, specialised to the
// shape of the proof being verified.
//
// zkc v1.2.32 constraints that shape the generated code:
//   - read/write memories are not yet sound, so only input, output and static
//     memories are used;
//   - multi-line functions cannot take 𝔽 parameters (the framing constraints
//     call Width() on native registers), so 𝔽 values only flow into
//     straight-line functions;
//   - #[global] functions compile to bus constraints, which the loom bridge
//     does not support.
package zkc
