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

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/merkle"
	"github.com/consensys/loom/internal/parallel"
	"github.com/consensys/loom/internal/poly"
	"github.com/consensys/loom/internal/reedsolomon"
)

// Domain tags of the Merkle leaves (a leaf hashes LeafDomainTag, the row
// widths, then the row pair) and nodes (a node compresses NodeDomainTag with
// its children).
const (
	LeafDomainTag uint64 = 0x4c454146 // "LEAF"
	NodeDomainTag uint64 = 0x4e4f4445 // "NODE"
)

// LeafSource describes the encoded column-oriented data used to build Merkle
// leaves. Row i stores one encoded value at i for every base and extension
// polynomial.
type LeafSource struct {
	Base []poly.Polynomial
	Ext  []poly.ExtPolynomial
}

type RSCommit struct {
	// Encoder is the Reed-Solomon encoder built for the size N passed to
	// NewRSCommit / NewRSCommitWithDomainCache. It is reused inside Commit
	// whenever a group's size matches it; groups of any other size build a
	// fresh encoder on the fly (using rate). Kept exported for back-compat
	// with code that reads Encoder.Domain.Cardinality.
	Encoder    reedsolomon.Encoder
	LeafHasher LeafHasher
	NodeHasher NodeHasher

	// rate is the RS blowup factor (encoded domain size = rate * N).
	rate uint64
}

// Group bundles base- and extension-rail polynomials that share the same
// native size. A single Commit call accepts a slice of Groups: the first
// largest group occupies the actual Merkle leaves and every other group
// becomes a per-level injection in the underlying merkle.Tree (see
// internal/merkle/tree.go), groups of equal size in declaration order.
type Group struct {
	Base []poly.Polynomial
	Ext  []poly.ExtPolynomial
}

// GroupShape records the per-group layout of a committed tree, in
// decreasing-size order (groups[0] is the largest, hashed at the actual
// leaves; groups[1..] are injection levels). Rows is the number of encoded
// rows at this group's level, i.e. ρ · N_native. The underlying Merkle tree
// hashes adjacent row pairs, so its level width is Rows/2.
type GroupShape struct {
	Rows      int
	BaseWidth int
	ExtWidth  int
}

// BatchShapes gives, for every Group in a Batch (in declaration order),
// the per-group shape list.
type BatchShapes = []GroupShape

type WMerkleTree struct {
	Tree *merkle.Tree

	// groups in decreasing row-count order, equal row counts in declaration
	// order. Length 1 for the typical
	// single-size Commit call; length > 1 when multiple sizes were committed
	// into one tree via merkle injections.
	groups BatchShapes
}

// RawRow holds one encoded row for one Group of the committed tree: one base
// value per base-rail polynomial and one extension value per extension-rail
// polynomial, in declaration order.
type RawRow struct {
	RawRowBase []koalabear.Element
	RawRowExt  []ext.E6
}

// RawRowPair holds the two adjacent rows needed by the DEEP bridge.
type RawRowPair struct {
	Lo RawRow
	Hi RawRow
}

// WMerkleInjectionOpening is the compact opening payload for one injected
// smaller group. Rows is the canonical lo/hi row pair at that group's row
// domain and is authenticated as a pair leaf on the top Merkle path.
type WMerkleInjectionOpening struct {
	Rows RawRowPair
}

// WMerkleProof is an opening proof for a WMerkleTree at one query position.
//
// One top Merkle path authenticates the top row pair and every injected raw row
// pair crossed by that path. TopRows is the canonical lo/hi row pair for the
// top group. Path authenticates hash(TopRows.Lo || TopRows.Hi). Injections
// carries one compact opening per injected smaller group, in the same
// decreasing-size order as WMerkleTree.InjectionWidths().
type WMerkleProof struct {
	TopRows    RawRowPair
	Path       merkle.Proof
	Injections []WMerkleInjectionOpening
}

func (wt WMerkleTree) Root() hash.Digest {
	return wt.Tree.Root()
}

// NumRows returns the number of encoded rows of the top (largest) group.
func (wt WMerkleTree) NumRows() int {
	if len(wt.groups) == 0 {
		return 0
	}
	return wt.groups[0].Rows
}

// NumLeaves returns the number of actual Merkle leaves in the top group. Each
// leaf hashes one adjacent encoded row pair, so NumLeaves() == NumRows()/2 for
// valid committed trees.
func (wt WMerkleTree) NumLeaves() int {
	rows := wt.NumRows()
	if rows == 0 {
		return 0
	}
	n, err := pairLeafCount(rows)
	if err != nil {
		return 0
	}
	return n
}

// BaseWidth returns the number of base-field values in the top group row.
func (wt WMerkleTree) BaseWidth() int {
	if len(wt.groups) == 0 {
		return 0
	}
	return wt.groups[0].BaseWidth
}

// ExtWidth returns the number of extension-field values in the top group row.
func (wt WMerkleTree) ExtWidth() int {
	if len(wt.groups) == 0 {
		return 0
	}
	return wt.groups[0].ExtWidth
}

// Groups returns the per-group shape descriptors in decreasing-size order
// (groups[0] is the top / largest group). The returned slice is owned by
// the tree; callers must not mutate it.
func (wt WMerkleTree) Groups() BatchShapes {
	return wt.groups
}

// InjectionWidths returns the pair-leaf LevelWidth of each merkle injection in
// the same order as the tree's injection schedule (non-increasing widths; a
// group as large as the top one is injected at the leaf level). It is
// nil for single-group trees. Suitable for passing to merkle.VerifyWithInjections.
func (wt WMerkleTree) InjectionWidths() []int {
	if len(wt.groups) <= 1 {
		return nil
	}
	res := make([]int, len(wt.groups)-1)
	for i := range res {
		res[i] = mustPairLeafCount(wt.groups[i+1].Rows)
	}
	return res
}

// OpenProof returns the Merkle proof for pair leaf i. Raw row-pair values are
// reconstructed by the prover from the committed polynomials when needed. For
// multi-group trees the returned proof carries InjectionLeaves matching
// InjectionWidths.
func (wt WMerkleTree) OpenProof(i int) (merkle.Proof, error) {
	return wt.Tree.OpenProof(i)
}

func NewRSCommit(N uint64, rate uint64, leafHasher LeafHasher, nodehasher NodeHasher) RSCommit {
	return NewRSCommitWithDomainCache(N, rate, leafHasher, nodehasher, nil)
}

// NewRSCommitWithDomainCache constructs an RSCommit using cache for the
// Reed-Solomon encoder domain. N is the natural size used to seed the
// reusable Encoder; Commit can still accept groups of other sizes by
// building fresh encoders from rate on the fly.
func NewRSCommitWithDomainCache(N uint64, rate uint64, leafHasher LeafHasher, nodehasher NodeHasher, cache *poly.DomainCache) RSCommit {
	rsEncoder := reedsolomon.NewEncoder(rate*N, reedsolomon.WithCache(cache))
	return RSCommit{
		Encoder:    rsEncoder,
		LeafHasher: leafHasher,
		NodeHasher: nodehasher,
		rate:       rate,
	}
}

// CommitConfig configures RSCommit.Commit.
type CommitConfig struct {
	DomainCache *poly.DomainCache
}

// CommitOption configures RSCommit.Commit.
type CommitOption func(c *CommitConfig) error

// WithDomainCache reuses cache for input-polynomial FFT domains.
func WithDomainCache(cache *poly.DomainCache) CommitOption {
	return func(c *CommitConfig) error {
		c.DomainCache = cache
		return nil
	}
}

// Batch list of Group, one Group = one list of polynomials of the same size
type Batch = []Group

// Commit commits to one or more Groups of polynomials into a single Merkle
// tree. Each Group in batch must hold polynomials sharing a single power-of-two
// length. Groups are ordered by decreasing size, equal sizes in declaration
// order. The first group's encoded row-pair hashes form the actual tree
// leaves; each other group is folded in as a merkle.LevelInjection at the
// level whose width matches its number of encoded row pairs (the leaf level
// for groups as large as the first).
//
// Within a group, pair leaf i absorbs rows 2*i and 2*i+1: first all base
// polynomial values from the two rows, then all extension polynomial values
// from the two rows. Multi-group calls add injection levels above the top
// group.
//
// In addition to the committed tree, Commit returns the per-group LeafSource
// in the same decreasing-size order used internally to build the tree (i.e.
// sources[0] is the top group whose RS-encoded row pairs form the Merkle
// leaves; sources[k>0] corresponds to a smaller group folded in as a
// LevelInjection at the level whose width matches that group's number of
// encoded row pairs). Callers needing to reopen committed values at FRI query
// positions can read RS-encoded evaluations directly from the LeafSource.
func (rs *RSCommit) Commit(batch Batch, opts ...CommitOption) (WMerkleTree, []LeafSource, error) {
	var config CommitConfig
	for _, opt := range opts {
		if err := opt(&config); err != nil {
			return WMerkleTree{}, nil, err
		}
	}
	domainCache := config.DomainCache
	if domainCache == nil {
		domainCache = &poly.DomainCache{}
	}

	if len(batch) == 0 {
		return WMerkleTree{}, nil, fmt.Errorf("commitment: Commit requires at least one Group")
	}

	// 1- validate every group and sort by descending native size, stably.
	sizes := make([]int, len(batch))
	for k, g := range batch {
		N, err := groupNativeSize(g)
		if err != nil {
			return WMerkleTree{}, nil, fmt.Errorf("commitment: Group[%d]: %w", k, err)
		}
		sizes[k] = N
	}
	order := make([]int, len(batch))
	for i := range order {
		order[i] = i
	}
	sort.SliceStable(order, func(a, b int) bool { return sizes[order[a]] > sizes[order[b]] })

	// 2- encode each group's polynomials on its RS-encoded domain and hash
	//    one adjacent row pair into one digest per group. The largest
	//    group's slice is the tree's leaf layer; the rest become injections.
	//    The per-group LeafSource is retained and returned to the caller in
	//    the same `order` (decreasing native size) used here.
	perGroupLeaves := make([][]hash.Digest, len(batch))
	perGroupRows := make([]int, len(batch))
	sources := make([]LeafSource, len(batch))
	for k, gi := range order {
		g := batch[gi]
		N := sizes[gi]
		encoder := rs.encoderForSize(uint64(N), domainCache)

		fftOuter := max(len(g.Base), len(g.Ext))
		var fftOpt fft.Option
		if fftOuter > 0 {
			fftOpt = fft.WithNbTasks(parallel.NbTasksPerJob(fftOuter))
		}

		encodedBase := make([]poly.Polynomial, len(g.Base))
		parallel.Execute(len(g.Base), func(start, end int) {
			for i := start; i < end; i++ {
				pol := g.Base[i]
				if fftOpt != nil {
					encodedBase[i] = encoder.Encode(pol, domainCache.Get(uint64(len(pol))), fftOpt)
				} else {
					encodedBase[i] = encoder.Encode(pol, domainCache.Get(uint64(len(pol))))
				}
			}
		})

		encodedExt := make([]poly.ExtPolynomial, len(g.Ext))
		parallel.Execute(len(g.Ext), func(start, end int) {
			for i := start; i < end; i++ {
				pol := g.Ext[i]
				if fftOpt != nil {
					encodedExt[i] = encoder.EncodeExt(pol, domainCache.Get(uint64(len(pol))), fftOpt)
				} else {
					encodedExt[i] = encoder.EncodeExt(pol, domainCache.Get(uint64(len(pol))))
				}
			}
		})

		rows := int(encoder.Domain.Cardinality)
		src := LeafSource{
			Base: encodedBase,
			Ext:  encodedExt,
		}
		pairLeaves, err := pairLeafCount(rows)
		if err != nil {
			return WMerkleTree{}, nil, fmt.Errorf("commitment: Group[%d] encoded rows: %w", gi, err)
		}
		leaves := make([]hash.Digest, pairLeaves)
		HashLeafPairsParallel(rs.LeafHasher, leaves, src)
		perGroupLeaves[k] = leaves
		perGroupRows[k] = rows
		sources[k] = src
	}

	// 3- build the underlying merkle tree. Smaller groups become injections
	//    on the way up; their LevelWidth equals the number of encoded row
	//    pairs at that group's level.
	topLeaves := perGroupLeaves[0]
	var injections []merkle.LevelInjection
	if len(perGroupLeaves) > 1 {
		injections = make([]merkle.LevelInjection, len(perGroupLeaves)-1)
		for k := 1; k < len(perGroupLeaves); k++ {
			injections[k-1] = merkle.LevelInjection{
				LevelWidth: len(perGroupLeaves[k]),
				LeafHashes: perGroupLeaves[k],
			}
		}
	}
	tree, err := merkle.NewWithInjections(len(topLeaves), rs.NodeHasher, injections)
	if err != nil {
		return WMerkleTree{}, nil, err
	}
	if err := tree.Build(topLeaves); err != nil {
		return WMerkleTree{}, nil, err
	}

	// 4- record the per-group shape in decreasing-size order so callers can
	//    locate each rail's rows within the tree.
	shapes := make(BatchShapes, len(order))
	for k, gi := range order {
		shapes[k] = GroupShape{
			Rows:      perGroupRows[k],
			BaseWidth: len(batch[gi].Base),
			ExtWidth:  len(batch[gi].Ext),
		}
	}

	return WMerkleTree{
		Tree:   tree,
		groups: shapes,
	}, sources, nil
}

// groupNativeSize validates that every polynomial in g has the same
// power-of-two length and returns it. Empty groups are rejected.
func groupNativeSize(g Group) (int, error) {
	N := 0
	for k, p := range g.Base {
		if k == 0 {
			N = len(p)
			continue
		}
		if len(p) != N {
			return 0, fmt.Errorf("base polynomial %d has length %d, want %d", k, len(p), N)
		}
	}
	for k, p := range g.Ext {
		if N == 0 && k == 0 {
			N = len(p)
			continue
		}
		if len(p) != N {
			return 0, fmt.Errorf("ext polynomial %d has length %d, want %d", k, len(p), N)
		}
	}
	if N == 0 {
		return 0, fmt.Errorf("group has no polynomials")
	}
	if N&(N-1) != 0 {
		return 0, fmt.Errorf("group size %d is not a power of two", N)
	}
	return N, nil
}

// encoderForSize returns the committer's reusable Encoder when N matches its
// native size (typical single-group path), otherwise constructs a fresh
// encoder for the requested size. Both paths share the same domain cache.
func (rs *RSCommit) encoderForSize(N uint64, cache *poly.DomainCache) reedsolomon.Encoder {
	want := rs.rate * N
	if want == rs.Encoder.Domain.Cardinality {
		return rs.Encoder
	}
	return reedsolomon.NewEncoder(want, reedsolomon.WithCache(cache))
}

func pairLeafCount(rows int) (int, error) {
	if rows <= 0 {
		return 0, fmt.Errorf("pair leaf rows must be positive, got %d", rows)
	}
	if rows&1 != 0 {
		return 0, fmt.Errorf("pair leaf rows must be even, got %d", rows)
	}
	if rows&(rows-1) != 0 {
		return 0, fmt.Errorf("pair leaf rows must be a power of two, got %d", rows)
	}
	return rows / 2, nil
}

func mustPairLeafCount(rows int) int {
	n, err := pairLeafCount(rows)
	if err != nil {
		panic(err)
	}
	return n
}

func pairLeafIndexForRow(row int) int {
	lo, _ := siblingRows(row)
	return lo / 2
}

func pairRowsForIndex(pairIdx int) (int, int) {
	lo := 2 * pairIdx
	return lo, lo + 1
}

func hashRawRowPair(leafHasher LeafHasher, pair RawRowPair) hash.Digest {
	return leafHasher.HashLeafPair(pair.Lo, pair.Hi)
}

// HashLeafPairsParallel hashes len(dst) adjacent row-pair leaves from src.
// Pair k absorbs rows 2*k and 2*k+1.
func HashLeafPairsParallel(lh LeafHasher, dst []hash.Digest, src LeafSource) {
	if batchHasher, ok := lh.(BatchPairLeafHasher); ok {
		hashLeafPairsBatchParallel(batchHasher, dst, src)
		return
	}
	parallel.Execute(len(dst), func(start, end int) {
		hashLeafPairsScalar(lh, dst[start:end], src, start)
	})
}

func hashLeafPairsBatchParallel(lh BatchPairLeafHasher, dst []hash.Digest, src LeafSource) {
	batchSize := lh.BatchSize()
	if batchSize <= 0 {
		batchSize = 1
	}

	if batchSize == 1 || len(dst) < batchSize {
		parallel.Execute(len(dst), func(start, end int) {
			lh.HashLeafPairs(dst[start:end], src, start)
		})
		return
	}

	full := (len(dst) / batchSize) * batchSize
	parallel.Execute(full/batchSize, func(startBatch, endBatch int) {
		start := startBatch * batchSize
		end := endBatch * batchSize
		lh.HashLeafPairs(dst[start:end], src, start)
	})
	if full < len(dst) {
		lh.HashLeafPairs(dst[full:], src, full)
	}
}

func hashLeafPairsScalar(lh LeafHasher, dst []hash.Digest, src LeafSource, startPair int) {
	nBase := len(src.Base)
	nExt := len(src.Ext)
	// Pre-allocate once; lo occupies [0:n], hi occupies [n:2n] in each buffer.
	baseBuf := make([]koalabear.Element, 2*nBase)
	extBuf := make([]ext.E6, 2*nExt)
	for k := range dst {
		lo, hi := pairRowsForIndex(startPair + k)
		for j := range src.Base {
			baseBuf[j].Set(&src.Base[j][lo])
			baseBuf[nBase+j].Set(&src.Base[j][hi])
		}
		for j := range src.Ext {
			extBuf[j].Set(&src.Ext[j][lo])
			extBuf[nExt+j].Set(&src.Ext[j][hi])
		}
		dst[k] = lh.HashLeafPair(
			RawRow{RawRowBase: baseBuf[:nBase], RawRowExt: extBuf[:nExt]},
			RawRow{RawRowBase: baseBuf[nBase:], RawRowExt: extBuf[nExt:]},
		)
	}
}
