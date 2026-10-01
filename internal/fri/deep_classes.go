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

package fri

import (
	"fmt"
	"sort"
)

// DEEP classes. Every committed group belongs to one DEEP class, and the PCS
// builds one DEEP quotient per class, over all the class's polynomials across
// every batch. A class has a single native size. The caller assigns classes
// with WithDeepClasses (loom uses one class per module); by default the class
// of a group is its size, so that there is one DEEP quotient per distinct size.
//
// Classes are ordered by class id: alpha_DEEP bindings and DEEP alpha powers
// follow that order. The FRI levels are the classes ordered by decreasing size,
// stably (equal sizes in class order); level 0 is the first class of the
// largest size.

// WithDeepClasses assigns a DEEP class id to every group: classes[b][g] for
// group g of batch b. Ids are compared as integers; they need not be dense.
// Every group of a class must have the same native size.
func WithDeepClasses(classes [][]int) OpenOption {
	return func(c *OpenConfig) error {
		c.DeepClasses = classes
		return nil
	}
}

// deepPlan is the class assignment of a PCS opening.
type deepPlan struct {
	classOf [][]int // [batch][group] → class index, dense, in class order
	sizes   []int   // [class] → native size
	levelOf []int   // [class] → FRI level
	classAt []int   // [level] → class
}

func (d deepPlan) numClasses() int { return len(d.sizes) }

// levelSizes returns the native size of every FRI level, in level order.
func (d deepPlan) levelSizes() []int {
	res := make([]int, len(d.classAt))
	for l, c := range d.classAt {
		res[l] = d.sizes[c]
	}
	return res
}

// newDeepPlan builds the class assignment of groups of the given sizes. With
// classes nil, the class of a group is the rank of its size in decreasing
// order.
func newDeepPlan(sizes [][]int, classes [][]int) (deepPlan, error) {
	if classes == nil {
		desc := sizesDescFromSizes(sizes)
		rank := make(map[int]int, len(desc))
		for i, N := range desc {
			rank[N] = i
		}
		classes = make([][]int, len(sizes))
		for b, batch := range sizes {
			classes[b] = make([]int, len(batch))
			for g, N := range batch {
				classes[b][g] = rank[N]
			}
		}
	}
	if len(classes) != len(sizes) {
		return deepPlan{}, fmt.Errorf("fri: DEEP classes for %d batches, got %d", len(sizes), len(classes))
	}
	var ids []int
	seen := map[int]bool{}
	for b, batch := range sizes {
		if len(classes[b]) != len(batch) {
			return deepPlan{}, fmt.Errorf("fri: DEEP classes of batch %d: %d groups, got %d", b, len(batch), len(classes[b]))
		}
		for _, id := range classes[b] {
			if !seen[id] {
				seen[id] = true
				ids = append(ids, id)
			}
		}
	}
	sort.Ints(ids)
	dense := make(map[int]int, len(ids))
	for i, id := range ids {
		dense[id] = i
	}

	plan := deepPlan{classOf: make([][]int, len(sizes)), sizes: make([]int, len(ids))}
	for b, batch := range sizes {
		plan.classOf[b] = make([]int, len(batch))
		for g, N := range batch {
			c := dense[classes[b][g]]
			plan.classOf[b][g] = c
			if plan.sizes[c] == 0 {
				plan.sizes[c] = N
			} else if plan.sizes[c] != N {
				return deepPlan{}, fmt.Errorf("fri: DEEP class %d has groups of sizes %d and %d", classes[b][g], plan.sizes[c], N)
			}
		}
	}
	plan.classAt = make([]int, len(ids))
	for c := range plan.classAt {
		plan.classAt[c] = c
	}
	sort.SliceStable(plan.classAt, func(i, j int) bool { return plan.sizes[plan.classAt[i]] > plan.sizes[plan.classAt[j]] })
	plan.levelOf = make([]int, len(ids))
	for l, c := range plan.classAt {
		plan.levelOf[c] = l
	}
	return plan, nil
}
