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

package zkcverifier

import (
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/trace"
)

// Gadget supplies the constraints of a zkc #[native] function.
//
// zkc emits no constraints for a native function: its module is a table of
// the function's registers, and every call site looks up (arguments, returns)
// into the (inputs, outputs) columns of that table, without a selector. The
// bridge keeps only the input and output columns and lets the gadget define
// and fill everything else.
//
// Since the lookup target is unfiltered, every row of the module is part of
// the table, padding rows included. A gadget must therefore constrain every
// row, and Fill must turn zkc's padding rows into genuine instances.
type Gadget interface {
	// Define adds the gadget's columns and constraints to the module. inputs
	// and outputs are the loom names of the function's input and output
	// columns, in declaration order.
	Define(b *board.Builder, module string, inputs, outputs []string) error
	// Fill computes the gadget's columns from the traced inputs, on every row.
	// It overwrites the outputs, so that padding rows become valid instances,
	// and returns an error if a traced output disagrees on a non-padding row.
	Fill(t trace.Trace, module string, inputs, outputs []string) error
}

// Gadgets maps a native function name to its gadget.
type Gadgets map[string]Gadget

// nativeModule is a native function module and its gadget.
type nativeModule struct {
	gadget          Gadget
	inputs, outputs []string
	io              map[string]bool // loom names of the I/O columns
}
