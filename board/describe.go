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

package board

import (
	"fmt"
	"sort"
	"strings"

	"github.com/consensys/loom/internal/dag"
)

// Describe returns a canonical text description of a compiled program: its
// modules (size and vanishing relation), setup columns, column fields, buses,
// and rounds (prover steps' inputs and outputs, staged columns, Fiat-Shamir
// hooks). It contains no pointer and lists maps in key order, so two
// compilations of the same builder are equal exactly when their descriptions
// are. A recursive verifier is built from the program, so a program that
// compiles to different descriptions gets a different verifier, and a
// different verification key.
func Describe(pg Program) string {
	var b strings.Builder
	names := make([]string, 0, len(pg.Modules))
	for name := range pg.Modules {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		m := pg.Modules[name]
		fmt.Fprintf(&b, "module %s N=%d gens=%d\n", name, m.N, len(m.GenCol))
		describeDAG(&b, m.VanishingRelation)
	}
	for _, c := range pg.SetupColumns {
		fmt.Fprintf(&b, "setup %s %s %v\n", c.Module, c.Name, c.Field)
	}
	cols := make([]string, 0, len(pg.ColumnFields))
	for name := range pg.ColumnFields {
		cols = append(cols, name)
	}
	sort.Strings(cols)
	for _, name := range cols {
		fmt.Fprintf(&b, "field %s %v\n", name, pg.ColumnFields[name])
	}
	for i, bus := range pg.LogupBus {
		fmt.Fprintf(&b, "logup bus %d %v\n", i, bus.Totals)
	}
	for i, bus := range pg.ProductBus {
		fmt.Fprintf(&b, "product bus %d %+v\n", i, bus)
	}
	for r, round := range pg.Rounds {
		fmt.Fprintf(&b, "round %d hook=%d\n", r, round.FSHook)
		for _, st := range round.Steps {
			ins := make([]string, len(st.Ins))
			for i, in := range st.Ins {
				ins[i] = in.String()
			}
			fmt.Fprintf(&b, "  step ins=%v outs=%v\n", ins, st.Outs)
		}
		for _, c := range round.Staged {
			fmt.Fprintf(&b, "  staged %s %s %v\n", c.Module, c.Name, c.Field)
		}
	}
	for _, l := range pg.Late {
		fmt.Fprintf(&b, "late %+v\n", l)
	}
	return b.String()
}

// describeDAG writes a DAG's nodes in its topological order, each child by its
// position in that order.
func describeDAG(b *strings.Builder, d *dag.DAG) {
	if d == nil {
		b.WriteString("  no relation\n")
		return
	}
	index := make(map[*dag.DAGNode]int, len(d.Nodes))
	for i, n := range d.Nodes {
		index[n] = i
	}
	for i, n := range d.Nodes {
		children := make([]int, len(n.Children))
		for k, c := range n.Children {
			children[k] = index[c]
		}
		leaf := ""
		if n.Leaf != nil {
			leaf = fmt.Sprintf(" leaf=%d:%s:%d:%v:%d:%s", n.Leaf.Type, n.Leaf.Name, n.Leaf.Shift, n.Leaf.Field, n.Leaf.Hook, n.Leaf.Value.String())
		}
		fmt.Fprintf(b, "  %d kind=%d exp=%d field=%v children=%v%s\n", i, n.Kind, n.Exp, n.Field, children, leaf)
	}
	fmt.Fprintf(b, "  root=%d\n", index[d.Root])
}
