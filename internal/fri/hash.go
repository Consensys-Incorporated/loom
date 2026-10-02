package fri

import (
	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/internal/hash"
)

//--------------- interfaces -----------------

// BatchPairLeafHasher extends LeafHasher with a SIMD-width batch path.
// Pair k absorbs rows 2*k and 2*k+1 as lo || hi.
type BatchPairLeafHasher interface {
	LeafHasher
	BatchSize() int
	HashLeafPairs(dst []hash.Digest, src LeafSource, startPair int)
}

type LeafHasher interface {
	// HashLeafPair hashes the (lo, hi) row pair that forms one Merkle leaf.
	// Implementations must produce lo.base || hi.base || lo.ext || hi.ext
	// in that element order, with length headers 2*nBase and 2*nExt.
	HashLeafPair(lo, hi RawRow) hash.Digest
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

func (Poseidon2LeafHasher) HashLeafPair(lo, hi RawRow) hash.Digest {
	nBase := len(lo.RawRowBase)
	nExt := len(lo.RawRowExt)
	h := hash.NewPoseidon2SpongeHasher()
	h.WriteElements(hash.NewElement(LeafDomainTag), hash.NewElement(uint64(2*nBase)), hash.NewElement(uint64(2*nExt)))
	for _, v := range lo.RawRowBase {
		h.WriteElements(v)
	}
	for _, v := range hi.RawRowBase {
		h.WriteElements(v)
	}
	for _, v := range lo.RawRowExt {
		h.WriteExt(v)
	}
	for _, v := range hi.RawRowExt {
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
	sponge.WriteSameElement(hash.NewElement(LeafDomainTag))
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
	return hash.Poseidon2NodeCompress(NodeDomainTag, left, right)
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
	out := hash.Poseidon2NodeCompressBatch16(NodeDomainTag, &l, &r)
	copy(dst, out[:])
}

//----------------- sha256 -----------------

type SHA256LeafHasher struct{}

func (SHA256LeafHasher) HashLeafPair(lo, hi RawRow) hash.Digest {
	nBase := len(lo.RawRowBase)
	nExt := len(lo.RawRowExt)
	h := hash.NewSHA256FieldHasher()
	h.WriteElements(hash.NewElement(LeafDomainTag), hash.NewElement(uint64(2*nBase)), hash.NewElement(uint64(2*nExt)))
	for _, v := range lo.RawRowBase {
		h.WriteElements(v)
	}
	for _, v := range hi.RawRowBase {
		h.WriteElements(v)
	}
	for _, v := range lo.RawRowExt {
		h.WriteExt(v)
	}
	for _, v := range hi.RawRowExt {
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
	h.WriteElements(hash.NewElement(NodeDomainTag))
	h.WriteElements(left[:]...)
	h.WriteElements(right[:]...)
	return h.Sum()
}

//----------------- blake3 -----------------

type Blake3LeafHasher struct{}

func (Blake3LeafHasher) HashLeafPair(lo, hi RawRow) hash.Digest {
	nBase := len(lo.RawRowBase)
	nExt := len(lo.RawRowExt)
	h := hash.NewBlake3FieldHasher()
	h.WriteElements(hash.NewElement(LeafDomainTag), hash.NewElement(uint64(2*nBase)), hash.NewElement(uint64(2*nExt)))
	for _, v := range lo.RawRowBase {
		h.WriteElements(v)
	}
	for _, v := range hi.RawRowBase {
		h.WriteElements(v)
	}
	for _, v := range lo.RawRowExt {
		h.WriteExt(v)
	}
	for _, v := range hi.RawRowExt {
		h.WriteExt(v)
	}
	return h.Sum()
}

type Blake3NodeHasher struct{}

func (Blake3NodeHasher) HashNode(left, right hash.Digest) hash.Digest {
	h := hash.NewBlake3FieldHasher()
	h.WriteElements(hash.NewElement(NodeDomainTag))
	h.WriteElements(left[:]...)
	h.WriteElements(right[:]...)
	return h.Sum()
}

