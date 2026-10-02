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

package recursion

import (
	"fmt"

	"github.com/consensys/gnark-crypto/field/koalabear"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/hash"
)

// Item is a transcript binding: the first Kind lanes of the cell at Addr
// (KindScalar, KindE6 or KindDigest).
type Item struct {
	Addr, Kind int
}

// Digest returns the item binding all the lanes of a digest cell.
func Digest(addr int) Item { return Item{addr, KindDigest} }

// E6 returns the item binding an E6 cell.
func E6(addr int) Item { return Item{addr, KindE6} }

// Scalar returns the item binding a scalar cell.
func Scalar(addr int) Item { return Item{addr, KindScalar} }

// Elements returns the items binding constant elements: const cells of
// CellWidth elements, then the remainder one scalar cell each.
func (m *Machine) Elements(xs []koalabear.Element) []Item {
	var res []Item
	for len(xs) >= CellWidth {
		var c Cell
		copy(c[:], xs[:CellWidth])
		res = append(res, Digest(m.Const(c)))
		xs = xs[CellWidth:]
	}
	for _, x := range xs {
		res = append(res, Scalar(m.Const(ScalarCell(x))))
	}
	return res
}

// Transcript is internal/fiat-shamir's transcript, in circuit: challenges are
// computed in registration order, and the digest of a challenge is the
// sponge of
//
//	FSID tag, its name, the previous challenge's digest (if any), its bindings
//
// built by Pack and Sponge. A challenge is a digest cell.
type Transcript struct {
	m        *Machine
	names    []string
	pos      map[string]int
	bindings [][]Item
	digests  []int // -1 until computed
}

// NewTranscript returns a transcript with the given challenges, in order.
func NewTranscript(m *Machine, names ...string) *Transcript {
	t := &Transcript{m: m, pos: map[string]int{}}
	for _, n := range names {
		t.NewChallenge(n)
	}
	return t
}

// NewChallenge appends a challenge.
func (t *Transcript) NewChallenge(name string) {
	if _, ok := t.pos[name]; ok {
		panic(fmt.Sprintf("transcript: challenge %q already exists", name))
	}
	t.pos[name] = len(t.names)
	t.names = append(t.names, name)
	t.bindings = append(t.bindings, nil)
	t.digests = append(t.digests, -1)
}

func (t *Transcript) index(name string) int {
	i, ok := t.pos[name]
	if !ok {
		panic(fmt.Sprintf("transcript: unknown challenge %q", name))
	}
	return i
}

// Bind appends items to a challenge's bindings.
func (t *Transcript) Bind(name string, items ...Item) {
	i := t.index(name)
	if t.digests[i] >= 0 {
		panic(fmt.Sprintf("transcript: challenge %q already computed", name))
	}
	t.bindings[i] = append(t.bindings[i], items...)
}

// BindElements binds constant elements.
func (t *Transcript) BindElements(name string, xs []koalabear.Element) {
	t.Bind(name, t.m.Elements(xs)...)
}

// Compute returns the digest cell of a challenge, computing it if needed; the
// previous challenge must be computed.
func (t *Transcript) Compute(name string) int {
	i := t.index(name)
	if t.digests[i] >= 0 {
		return t.digests[i]
	}
	items := t.m.Elements(hash.StringToElements(fiatshamir.ChallengeIDDomainTag, name))
	if i > 0 {
		if t.digests[i-1] < 0 {
			panic(fmt.Sprintf("transcript: challenge %q computed before %q", name, t.names[i-1]))
		}
		items = append(items, Digest(t.digests[i-1]))
	}
	items = append(items, t.bindings[i]...)
	addrs, kinds := make([]int, len(items)), make([]int, len(items))
	for k, it := range items {
		addrs[k], kinds[k] = it.Addr, it.Kind
	}
	stream, n := t.m.Pack(addrs, kinds)
	t.digests[i] = t.m.Sponge(stream, n)
	return t.digests[i]
}
