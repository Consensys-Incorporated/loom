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

package merkle

import (
	"fmt"
	"testing"

	"github.com/consensys/loom/internal/hash"
)

// batchTestNodeHasher is testNodeHasher with the batched fast path, so that
// wide levels go through HashNodes.
type batchTestNodeHasher struct{ testNodeHasher }

func (batchTestNodeHasher) BatchSize() int { return 4 }

func (h batchTestNodeHasher) HashNodes(dst, left, right []hash.Digest) {
	for i := range dst {
		dst[i] = h.HashNode(left[i], right[i])
	}
}

// referenceRoot computes the root level by level, folding the injections of
// each level in schedule order, leaf level included.
func referenceRoot(leaves []hash.Digest, injections []LevelInjection, nh NodeHasher) hash.Digest {
	level := append([]hash.Digest(nil), leaves...)
	fold := func() {
		for _, inj := range injections {
			if inj.LevelWidth == len(level) {
				for j := range level {
					level[j] = nh.HashNode(level[j], inj.LeafHashes[j])
				}
			}
		}
	}
	fold()
	for len(level) > 1 {
		next := make([]hash.Digest, len(level)/2)
		for j := range next {
			next[j] = nh.HashNode(level[2*j], level[2*j+1])
		}
		level = next
		fold()
	}
	return level[0]
}

func injectionsOf(widths []int) []LevelInjection {
	res := make([]LevelInjection, len(widths))
	for k, w := range widths {
		res[k] = LevelInjection{LevelWidth: w, LeafHashes: testDigests(w, uint64(1000*(k+1)))}
	}
	return res
}

func TestInjectionSchedules(t *testing.T) {
	const nLeaves = 32
	schedules := [][]int{
		{16, 4},           // distinct widths, as before
		{16, 16, 4},       // two injections at one width
		{32},              // leaf level
		{32, 32, 8, 8, 8}, // leaf level and repeated widths
		{32, 16, 16, 2, 1, 1},
	}
	for _, nh := range []NodeHasher{testNodeHasher{}, batchTestNodeHasher{}} {
		for _, widths := range schedules {
			t.Run(fmt.Sprintf("%T/%v", nh, widths), func(t *testing.T) {
				leaves := testDigests(nLeaves, 10)
				injections := injectionsOf(widths)
				tree, err := NewWithInjections(nLeaves, nh, injections)
				if err != nil {
					t.Fatal(err)
				}
				if err := tree.Build(leaves); err != nil {
					t.Fatal(err)
				}
				if got, want := tree.Root(), referenceRoot(leaves, injections, nh); got != want {
					t.Fatalf("root %v, want %v", got, want)
				}
				for i := range nLeaves {
					proof, err := tree.OpenProof(i)
					if err != nil {
						t.Fatal(err)
					}
					if !VerifyWithInjections(tree.Root(), proof, leaves[i], widths, nh) {
						t.Fatalf("leaf %d: valid proof rejected", i)
					}
					bad := proof
					bad.InjectionLeaves = append([]hash.Digest(nil), proof.InjectionLeaves...)
					bad.InjectionLeaves[len(bad.InjectionLeaves)-1][0].SetUint64(7)
					if VerifyWithInjections(tree.Root(), bad, leaves[i], widths, nh) {
						t.Fatalf("leaf %d: tampered injection leaf accepted", i)
					}
				}
			})
		}
	}
}

// Swapping two injections of the same width changes the root: their order is
// part of the commitment.
func TestSameWidthOrderMatters(t *testing.T) {
	nh := testNodeHasher{}
	leaves := testDigests(8, 10)
	injections := injectionsOf([]int{4, 4})
	swapped := []LevelInjection{injections[1], injections[0]}
	roots := make([]hash.Digest, 2)
	for k, inj := range [][]LevelInjection{injections, swapped} {
		tree, err := NewWithInjections(8, nh, inj)
		if err != nil {
			t.Fatal(err)
		}
		if err := tree.Build(leaves); err != nil {
			t.Fatal(err)
		}
		roots[k] = tree.Root()
	}
	if roots[0] == roots[1] {
		t.Fatal("same-width injections commute")
	}
}

func TestInjectionScheduleValidation(t *testing.T) {
	nh := testNodeHasher{}
	for _, widths := range [][]int{{4, 8}, {16}, {3}} {
		if _, err := NewWithInjections(8, nh, injectionsOf(widths)); err == nil {
			t.Fatalf("schedule %v accepted", widths)
		}
	}
	// The verifier rejects a schedule whose widths increase, or exceed the
	// leaves, and a proof with leftover injection leaves.
	tree, _ := NewWithInjections(8, nh, injectionsOf([]int{4, 2}))
	leaves := testDigests(8, 10)
	_ = tree.Build(leaves)
	proof, _ := tree.OpenProof(3)
	for _, widths := range [][]int{{2, 4}, {16, 4}} {
		if VerifyWithInjections(tree.Root(), proof, leaves[3], widths, nh) {
			t.Fatalf("verifier accepted schedule %v", widths)
		}
	}
	if VerifyWithInjections(tree.Root(), proof, leaves[3], []int{4, 3}, nh) {
		t.Fatal("verifier accepted a non power of two width")
	}
}
