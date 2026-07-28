package fri

import (
	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/internal/hash"
)

//--------------- interfaces -----------------

// BatchPairLeafHasher hashes consecutive adjacent row pairs into dst.
// Pair k absorbs rows 2*k and 2*k+1 as
//
//	base(lo) || base(hi) || ext(lo) || ext(hi)
//
// through the same LeafHasher.HashLeaf interface used by single-row hashing.
type BatchPairLeafHasher interface {
	LeafHasher
	BatchSize() int
	HashLeafPairs(dst []hash.Digest, src LeafSource, startPair int)
}

type LeafHasher interface {
	HashLeaf(base []koalabear.Element, ext []ext.E6) hash.Digest
}

type NodeHasher interface {
	HashNode(left, right hash.Digest) hash.Digest
}

// --------------- default -----------------
var (
	DefaultLeafHasher Poseidon2LeafHasher
	DefaultNodeHasher Poseidon2NodeHasher
)

// --------------- poseidon2 -----------------
type Poseidon2LeafHasher struct{}

func (Poseidon2LeafHasher) HashLeaf(base []koalabear.Element, ext []ext.E6) hash.Digest {
	h := hash.NewPoseidon2SpongeHasher()
	h.WriteElements(hash.NewElement(leafDomainTag), hash.NewElement(uint64(len(base))), hash.NewElement(uint64(len(ext))))
	for _, v := range base {
		h.WriteElements(v)
	}
	for _, v := range ext {
		h.WriteExt(v)
	}
	return h.Sum()
}

func (Poseidon2LeafHasher) BatchSize() int {
	return hash.Poseidon2SpongeBatchSize
}

func (lh Poseidon2LeafHasher) HashLeafPairs(dst []hash.Digest, src LeafSource, startPair int) {
	if len(dst) < hash.Poseidon2SpongeBatchSize {
		hashLeafPairsScalar(lh, dst, src, startPair)
		return
	}

	fullBatches := len(dst) / hash.Poseidon2SpongeBatchSize
	for batch := 0; batch < fullBatches; batch++ {
		offset := batch * hash.Poseidon2SpongeBatchSize
		lh.hashLeafPairsBatch16(dst[offset:offset+hash.Poseidon2SpongeBatchSize], src, startPair+offset)
	}
	if tail := fullBatches * hash.Poseidon2SpongeBatchSize; tail < len(dst) {
		hashLeafPairsScalar(lh, dst[tail:], src, startPair+tail)
	}
}

func (lh Poseidon2LeafHasher) hashLeafPairsBatch16(dst []hash.Digest, src LeafSource, startPair int) {
	sponge := hash.NewPoseidon2SpongeBatch16()
	sponge.WriteSameElement(hash.NewElement(leafDomainTag))
	sponge.WriteSameElement(hash.NewElement(uint64(2 * len(src.Base))))
	sponge.WriteSameElement(hash.NewElement(uint64(2 * len(src.Ext))))

	for _, pol := range src.Base {
		var row [hash.Poseidon2SpongeBatchSize]koalabear.Element
		for lane := 0; lane < hash.Poseidon2SpongeBatchSize; lane++ {
			lo, _ := pairRowsForIndex(startPair + lane)
			row[lane].Set(&pol[lo])
		}
		sponge.WriteElementBatch(row)
	}
	for _, pol := range src.Base {
		var row [hash.Poseidon2SpongeBatchSize]koalabear.Element
		for lane := 0; lane < hash.Poseidon2SpongeBatchSize; lane++ {
			_, hi := pairRowsForIndex(startPair + lane)
			row[lane].Set(&pol[hi])
		}
		sponge.WriteElementBatch(row)
	}

	for _, pol := range src.Ext {
		var row [hash.Poseidon2SpongeBatchSize]ext.E6
		for lane := 0; lane < hash.Poseidon2SpongeBatchSize; lane++ {
			lo, _ := pairRowsForIndex(startPair + lane)
			row[lane].Set(&pol[lo])
		}
		sponge.WriteExtBatch(row)
	}
	for _, pol := range src.Ext {
		var row [hash.Poseidon2SpongeBatchSize]ext.E6
		for lane := 0; lane < hash.Poseidon2SpongeBatchSize; lane++ {
			_, hi := pairRowsForIndex(startPair + lane)
			row[lane].Set(&pol[hi])
		}
		sponge.WriteExtBatch(row)
	}

	sponge.SumInto(dst)
}

type Poseidon2NodeHasher struct{}

func (Poseidon2NodeHasher) HashNode(left, right hash.Digest) hash.Digest {
	return hash.Poseidon2NodeCompress(nodeDomainTag, left, right)
}

// BatchSize is the lane width of the SIMD-batched Poseidon2 permutation.
func (Poseidon2NodeHasher) BatchSize() int { return hash.Poseidon2SpongeBatchSize }

// HashNodes compresses BatchSize() (left, right) pairs in one batched
// permutation. dst, left, right must all have length BatchSize().
func (Poseidon2NodeHasher) HashNodes(dst, left, right []hash.Digest) {
	const n = hash.Poseidon2SpongeBatchSize
	if len(dst) != n || len(left) != n || len(right) != n {
		panic("Poseidon2NodeHasher.HashNodes: input slices must have length BatchSize()")
	}
	var l, r [n]hash.Digest
	copy(l[:], left)
	copy(r[:], right)
	out := hash.Poseidon2NodeCompressBatch16(nodeDomainTag, &l, &r)
	copy(dst, out[:])
}

//----------------- sha256 -----------------

type SHA256LeafHasher struct{}

func (SHA256LeafHasher) HashLeaf(base []koalabear.Element, ext []ext.E6) hash.Digest {
	h := hash.NewSHA256FieldHasher()
	h.WriteElements(hash.NewElement(leafDomainTag), hash.NewElement(uint64(len(base))), hash.NewElement(uint64(len(ext))))
	for _, v := range base {
		h.WriteElements(v)
	}
	for _, v := range ext {
		h.WriteExt(v)
	}
	return h.Sum()
}

func (SHA256LeafHasher) BatchSize() int {
	return 1
}

type SHA256NodeHasher struct{}

func (SHA256NodeHasher) HashNode(left, right hash.Digest) hash.Digest {
	h := hash.NewSHA256FieldHasher()
	h.WriteElements(hash.NewElement(nodeDomainTag))
	h.WriteElements(left[:]...)
	h.WriteElements(right[:]...)
	return h.Sum()
}

//----------------- blake3 -----------------

type Blake3LeafHasher struct{}

func (Blake3LeafHasher) HashLeaf(base []koalabear.Element, extElems []ext.E6) hash.Digest {
	h := hash.NewBlake3FieldHasher()
	h.WriteElements(hash.NewElement(leafDomainTag), hash.NewElement(uint64(len(base))), hash.NewElement(uint64(len(extElems))))
	for _, v := range base {
		h.WriteElements(v)
	}
	for _, v := range extElems {
		h.WriteExt(v)
	}
	return h.Sum()
}

type Blake3NodeHasher struct{}

func (Blake3NodeHasher) HashNode(left, right hash.Digest) hash.Digest {
	h := hash.NewBlake3FieldHasher()
	h.WriteElements(hash.NewElement(nodeDomainTag))
	h.WriteElements(left[:]...)
	h.WriteElements(right[:]...)
	return h.Sum()
}

//----------------- helpers-----------------

func hashLeavesScalar(lh LeafHasher, dst []hash.Digest, src LeafSource, start int) {
	baseLeaf := make([]koalabear.Element, len(src.Base))
	extLeaf := make([]ext.E6, len(src.Ext))
	for k := range dst {
		i := start + k
		if len(src.Base) > 0 {
			for j := range src.Base {
				baseLeaf[j].Set(&src.Base[j][i])
			}
		}
		if len(src.Ext) > 0 {
			for j := range src.Ext {
				extLeaf[j].Set(&src.Ext[j][i])
			}
		}
		dst[k] = lh.HashLeaf(baseLeaf, extLeaf)
	}
}
