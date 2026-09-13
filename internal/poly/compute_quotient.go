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

package poly

import (
	"fmt"
	"math/big"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/gnark-crypto/field/koalabear/fft"
	"github.com/consensys/gnark-crypto/utils"
	"github.com/consensys/loom/expr"
	"github.com/consensys/loom/field"
	"github.com/consensys/loom/internal/dag"
	"github.com/consensys/loom/internal/parallel"
)

// quotientParallelThreshold is the smallest iteration count for which fan-out
// across goroutines is worth the scheduler overhead. Below this, the work
// runs serially in the calling goroutine.
const quotientParallelThreshold = 1 << 12

// QuotientConfig configures quotient computation.
type QuotientConfig struct {
	DomainCache *DomainCache
}

// QuotientOption configures quotient computation.
type QuotientOption func(c *QuotientConfig) error

// WithDomainCache reuses cache for FFT domains created during quotient
// computation and coset conversion.
func WithDomainCache(cache *DomainCache) QuotientOption {
	return func(c *QuotientConfig) error {
		c.DomainCache = cache
		return nil
	}
}

func newQuotientConfig(opts ...QuotientOption) (QuotientConfig, error) {
	var config QuotientConfig
	for _, opt := range opts {
		if err := opt(&config); err != nil {
			return QuotientConfig{}, err
		}
	}
	return config, nil
}

// ComputeQuotient computes E(PI)/X^N-1
// /!\ all polynomials must be in normal layout, lagrange basis
func ComputeQuotient(Pi map[string]Polynomial, vanishingRelation dag.DAG, N int, opts ...QuotientOption) (Polynomial, error) {
	config, err := newQuotientConfig(opts...)
	if err != nil {
		return nil, err
	}
	domainCache := config.DomainCache
	if domainCache == nil {
		domainCache = &DomainCache{}
	}

	// Degree of E(Pi) is at most E.Degree() * sizePi
	eDeg := vanishingRelation.Degree()
	if eDeg <= 0 {
		return Polynomial{}, fmt.Errorf("expression degree must be at least 1, got %d", eDeg)
	}
	N = nextPowerOfTwo(N)
	bigSize := nextPowerOfTwo(eDeg * N)
	if bigSize%N != 0 {
		return Polynomial{}, fmt.Errorf("big domain size %d is not divisible by vanishing domain size %d", bigSize, N)
	}

	// Assign Leaf.Idx by column name (shifted and non-shifted versions of the same
	// column share the same index and polynomial; EvalOnIthEntry handles shifts).
	// Copy each base polynomial once so FFT mutations don't affect the caller's trace.
	nameToIdx := make(map[string]int)
	baseCopies := make(map[string][]koalabear.Element)
	for _, n := range vanishingRelation.Nodes {
		if n.Kind != dag.KindLeaf || n.Leaf.Type == expr.ConstantColumn {
			continue
		}
		l := n.Leaf
		if _, ok := nameToIdx[l.Name]; !ok {
			nameToIdx[l.Name] = len(nameToIdx)
			src := Pi[l.Name]
			cp := make([]koalabear.Element, len(src))
			copy(cp, src)
			baseCopies[l.Name] = cp
		}
		l.Idx = nameToIdx[l.Name]
	}

	// _Pi[idx] is the (mutable) copy of the polynomial for that leaf name.
	// The FFT loop mutates these slices in-place; EvalOnIthEntry reads from them.
	_Pi := make([][]koalabear.Element, len(nameToIdx))
	for name, idx := range nameToIdx {
		_Pi[idx] = baseCopies[name]
	}

	// piNonConst: non-constant polynomial slices that need FFT (one per base column).
	piNonConst := make([][]koalabear.Element, 0, len(baseCopies))
	for _, poly := range baseCopies {
		if len(poly) > 1 {
			piNonConst = append(piNonConst, poly)
		}
	}

	numerator := make([]koalabear.Element, bigSize)

	// create domains
	bigDomain := domainCache.Get(uint64(bigSize))
	smallDomain := domainCache.Get(uint64(N))

	// number of cosets of smalldomain in bigdomain
	rho := bigSize / N

	// create the twiddles of size N (not bigSize):
	// after IFFT(DIF) of size N, output is BitReversed w.r.t. N, so twiddle[bitrev_N(k)] = g^k,
	// i.e. build powers of g then BitReverse with length N.
	twiddleFrMultiplicativeGen := make([]koalabear.Element, N)
	fft.BuildExpTable(bigDomain.FrMultiplicativeGen, twiddleFrMultiplicativeGen)
	utils.BitReverse(twiddleFrMultiplicativeGen)
	twiddleGeneratorBigDomain := make([]koalabear.Element, N)
	fft.BuildExpTable(bigDomain.Generator, twiddleGeneratorBigDomain)
	utils.BitReverse(twiddleGeneratorBigDomain)
	scaleByTwiddles := func(a, b []koalabear.Element) {
		for i := 0; i < N; i++ {
			a[i].Mul(&a[i], &b[i])
		}
	}

	// Each outer worker calls one FFT at a time; cap the FFT's internal
	// goroutines so outer × inner ≤ NumCPU.
	fftNbTasks := parallel.NbTasksPerJob(len(piNonConst))
	fftOpt := fft.WithNbTasks(fftNbTasks)

	// at this stage, all polynomials in PiCopies are in Lagrange form. We write them in canonical basis, shifted by twiddles[i][0]
	// to prepare the FFT on the cosets (twiddles[i][0] is <bigDomain.FrMultiplicativeGen^i>), used to avoid the zeroes on X^N-1).
	parallel.Execute(len(piNonConst), func(start, end int) {
		for k := start; k < end; k++ {
			pCopy := piNonConst[k]
			smallDomain.FFTInverse(pCopy, fft.DIF, fftOpt)
			scaleByTwiddles(pCopy, twiddleFrMultiplicativeGen)
		}
	})

	// at this stage, all the polynomials c[i] in c are in canonical, bit reverse, scaled by <bigDomain.FrMultiplicativeGen^i>
	for i := range rho {

		// evaluate the polys shifted by <bigDomain.FrMultiplicativeGen> on  <bigDomain.Generator^i> -> the result is the polys
		// evaluated on the coset bigDomain.FrMultiplicativeGen*<bigDomain.Generator^i>
		parallel.Execute(len(piNonConst), func(start, end int) {
			for k := start; k < end; k++ {
				smallDomain.FFT(piNonConst[k], fft.DIT, fftOpt)
			}
		})

		// at this stage, the polys are evaluated on bigDomain.FrMultiplicativeGen*<bigDomain.Generator^i>. We can compute the rho-ith
		// component of the numerator
		vals := vanishingRelation.EvalOnAllEntries(_Pi, N)
		for j := 0; j < N; j++ {
			numerator[rho*j+i] = vals[j]
		}

		// FFTInv on piNonConst -> polys become canonical again, k-th coeff shifted by bigDomain.FrMultiplicativeGen^k*<bigDomain.Generator^ik>
		parallel.Execute(len(piNonConst), func(start, end int) {
			for k := start; k < end; k++ {
				pCopy := piNonConst[k]
				smallDomain.FFTInverse(pCopy, fft.DIF, fftOpt)
				scaleByTwiddles(pCopy, twiddleGeneratorBigDomain)
			}
		})
	}

	// X^N-1 evaluated at coset representative FrGen·bigDomain.Generator^i:
	//   (FrGen·bigDomain.Generator^i)^N = FrGen^N · (bigDomain.Generator^N)^i
	// bigDomain.Generator^N has order rho, so only rho distinct values.
	// numerator[rho*j+i] was evaluated on coset i, so it must be divided by xnMinusOne[i].
	xnMinusOne := make([]koalabear.Element, rho)
	one := koalabear.One()
	var gn, frn koalabear.Element
	NBigInt := big.NewInt(int64(N))
	frn.Exp(bigDomain.FrMultiplicativeGen, NBigInt) // FrGen^N
	gn.Exp(bigDomain.Generator, NBigInt)            // bigDomain.Generator^N, has order rho
	accgn := koalabear.One()
	for i := range rho {
		xnMinusOne[i].Mul(&frn, &accgn).Sub(&xnMinusOne[i], &one) // FrGen^N · gn^i - 1
		accgn.Mul(&accgn, &gn)
	}

	// Precompute the rho distinct inverses once; the bigSize-element loop only
	// ever needs one of rho values, so doing Inverse() per row would be wasted
	// work (rho is typically tiny, e.g. 4 for a degree-4 relation on N=32K).
	xnMinusOneInv := make([]koalabear.Element, rho)
	for i := range rho {
		xnMinusOneInv[i].Inverse(&xnMinusOne[i])
	}
	parallel.ExecuteWithThreshold(bigSize, quotientParallelThreshold, func(start, end int) {
		for i := start; i < end; i++ {
			numerator[i].Mul(&numerator[i], &xnMinusOneInv[i%rho])
		}
	})

	return numerator, nil
}

// ComputeQuotientMixed computes E(Pi)/(X^N-1) for an extension-valued
// vanishing relation. Base columns stay on the base rail, extension columns
// stay on the extension rail, and mixed evaluation lifts base values only when
// an extension node consumes them. The returned quotient is in coset-Lagrange
// form, matching ComputeQuotient.
func ComputeQuotientMixed(PiBase map[string]Polynomial, PiExt map[string]ExtPolynomial, vanishingRelation dag.DAG, N int, opts ...QuotientOption) (ExtPolynomial, error) {
	config, err := newQuotientConfig(opts...)
	if err != nil {
		return nil, err
	}
	domainCache := config.DomainCache
	if domainCache == nil {
		domainCache = &DomainCache{}
	}

	if vanishingRelation.Root.Field != field.Ext {
		return nil, fmt.Errorf("ComputeQuotientMixed: root field is %s, want %s", vanishingRelation.Root.Field, field.Ext)
	}

	eDeg := vanishingRelation.Degree()
	if eDeg <= 0 {
		return nil, fmt.Errorf("expression degree must be at least 1, got %d", eDeg)
	}
	N = nextPowerOfTwo(N)
	bigSize := nextPowerOfTwo(eDeg * N)
	if bigSize%N != 0 {
		return nil, fmt.Errorf("big domain size %d is not divisible by vanishing domain size %d", bigSize, N)
	}

	baseNameToIdx := make(map[string]int)
	extNameToIdx := make(map[string]int)
	baseCopies := make(map[string][]koalabear.Element)
	extCopies := make(map[string][]ext.E6)
	for _, n := range vanishingRelation.Nodes {
		if n.Kind != dag.KindLeaf || n.Leaf.Type == expr.ConstantColumn {
			continue
		}
		l := n.Leaf
		if n.Field == field.Ext {
			if _, ok := extNameToIdx[l.Name]; !ok {
				src, ok := PiExt[l.Name]
				if !ok {
					// A leaf can be typed Ext while its witness lives on the
					// base rail — Lagrange selectors are materialized into
					// PiBase by GenCol but evaluate in E6. Lift instead of
					// failing, mirroring evalPointWiseMixedInto.
					base, baseOK := PiBase[l.Name]
					if !baseOK {
						return nil, fmt.Errorf("ComputeQuotientMixed: extension column %q not found", l.Name)
					}
					src = liftPolynomialToExt(base)
				}
				if len(src) != N && len(src) != 1 {
					return nil, fmt.Errorf("ComputeQuotientMixed: extension column %q has length %d, want %d or 1", l.Name, len(src), N)
				}
				extNameToIdx[l.Name] = len(extNameToIdx)
				cp := make([]ext.E6, len(src))
				copy(cp, src)
				extCopies[l.Name] = cp
			}
			l.Idx = extNameToIdx[l.Name]
			continue
		}

		if _, ok := baseNameToIdx[l.Name]; !ok {
			src, ok := PiBase[l.Name]
			if !ok {
				return nil, fmt.Errorf("ComputeQuotientMixed: base column %q not found", l.Name)
			}
			if len(src) != N && len(src) != 1 {
				return nil, fmt.Errorf("ComputeQuotientMixed: base column %q has length %d, want %d or 1", l.Name, len(src), N)
			}
			baseNameToIdx[l.Name] = len(baseNameToIdx)
			cp := make([]koalabear.Element, len(src))
			copy(cp, src)
			baseCopies[l.Name] = cp
		}
		l.Idx = baseNameToIdx[l.Name]
	}

	_PiBase := make([][]koalabear.Element, len(baseNameToIdx))
	for name, idx := range baseNameToIdx {
		_PiBase[idx] = baseCopies[name]
	}
	_PiExt := make([][]ext.E6, len(extNameToIdx))
	for name, idx := range extNameToIdx {
		_PiExt[idx] = extCopies[name]
	}

	baseNonConst := make([][]koalabear.Element, 0, len(baseCopies))
	for _, poly := range baseCopies {
		if len(poly) > 1 {
			baseNonConst = append(baseNonConst, poly)
		}
	}
	extNonConst := make([][]ext.E6, 0, len(extCopies))
	for _, poly := range extCopies {
		if len(poly) > 1 {
			extNonConst = append(extNonConst, poly)
		}
	}

	numerator := make(ExtPolynomial, bigSize)

	bigDomain := domainCache.Get(uint64(bigSize))
	smallDomain := domainCache.Get(uint64(N))
	rho := bigSize / N

	twiddleFrMultiplicativeGen := make([]koalabear.Element, N)
	fft.BuildExpTable(bigDomain.FrMultiplicativeGen, twiddleFrMultiplicativeGen)
	utils.BitReverse(twiddleFrMultiplicativeGen)
	twiddleGeneratorBigDomain := make([]koalabear.Element, N)
	fft.BuildExpTable(bigDomain.Generator, twiddleGeneratorBigDomain)
	utils.BitReverse(twiddleGeneratorBigDomain)
	scaleBaseByTwiddles := func(a, b []koalabear.Element) {
		for i := 0; i < N; i++ {
			a[i].Mul(&a[i], &b[i])
		}
	}
	scaleExtByTwiddles := func(a []ext.E6, b []koalabear.Element) {
		for i := 0; i < N; i++ {
			a[i].MulByElement(&a[i], &b[i])
		}
	}

	// Each FFT runs inside a parallel.Execute over polys; cap its inner
	// parallelism so the two layers together don't exceed NumCPU. We size the
	// budget on the larger rail to avoid starving when one rail is empty.
	fftOuter := max(len(baseNonConst), len(extNonConst))
	fftNbTasks := parallel.NbTasksPerJob(fftOuter)
	fftOpt := fft.WithNbTasks(fftNbTasks)

	parallel.Execute(len(baseNonConst), func(start, end int) {
		for k := start; k < end; k++ {
			pCopy := baseNonConst[k]
			smallDomain.FFTInverse(pCopy, fft.DIF, fftOpt)
			scaleBaseByTwiddles(pCopy, twiddleFrMultiplicativeGen)
		}
	})
	parallel.Execute(len(extNonConst), func(start, end int) {
		for k := start; k < end; k++ {
			pCopy := extNonConst[k]
			smallDomain.FFTInverseExt6(pCopy, fft.DIF, fftOpt)
			scaleExtByTwiddles(pCopy, twiddleFrMultiplicativeGen)
		}
	})

	vals := make([]ext.E6, N)
	var evalWorkspace dag.EvalWorkspace
	for i := range rho {
		parallel.Execute(len(baseNonConst), func(start, end int) {
			for k := start; k < end; k++ {
				smallDomain.FFT(baseNonConst[k], fft.DIT, fftOpt)
			}
		})
		parallel.Execute(len(extNonConst), func(start, end int) {
			for k := start; k < end; k++ {
				smallDomain.FFTExt6(extNonConst[k], fft.DIT, fftOpt)
			}
		})

		vanishingRelation.EvalOnAllEntriesMixedInto(vals, _PiBase, _PiExt, N, &evalWorkspace)
		for j := 0; j < N; j++ {
			numerator[rho*j+i] = vals[j]
		}

		parallel.Execute(len(baseNonConst), func(start, end int) {
			for k := start; k < end; k++ {
				pCopy := baseNonConst[k]
				smallDomain.FFTInverse(pCopy, fft.DIF, fftOpt)
				scaleBaseByTwiddles(pCopy, twiddleGeneratorBigDomain)
			}
		})
		parallel.Execute(len(extNonConst), func(start, end int) {
			for k := start; k < end; k++ {
				pCopy := extNonConst[k]
				smallDomain.FFTInverseExt6(pCopy, fft.DIF, fftOpt)
				scaleExtByTwiddles(pCopy, twiddleGeneratorBigDomain)
			}
		})
	}

	xnMinusOne := make([]koalabear.Element, rho)
	one := koalabear.One()
	var gn, frn koalabear.Element
	NBigInt := big.NewInt(int64(N))
	frn.Exp(bigDomain.FrMultiplicativeGen, NBigInt)
	gn.Exp(bigDomain.Generator, NBigInt)
	accgn := koalabear.One()
	for i := range rho {
		xnMinusOne[i].Mul(&frn, &accgn).Sub(&xnMinusOne[i], &one)
		accgn.Mul(&accgn, &gn)
	}

	// Precompute the rho distinct inverses once (same reason as ComputeQuotient).
	xnMinusOneInv := make([]koalabear.Element, rho)
	for i := range rho {
		xnMinusOneInv[i].Inverse(&xnMinusOne[i])
	}
	parallel.ExecuteWithThreshold(bigSize, quotientParallelThreshold, func(start, end int) {
		for i := start; i < end; i++ {
			numerator[i].MulByElement(&numerator[i], &xnMinusOneInv[i%rho])
		}
	})

	return numerator, nil
}

// CosetLagrangeToLagrangeNormal converts a polynomial from coset-Lagrange Normal form
// (as returned by ComputeQuotient, evaluated on {FrMultiplicativeGen * ω^j}) to
// standard Lagrange Normal form (evaluated on {ω^j}).
// The conversion is in-place.
func CosetLagrangeToLagrangeNormal(p Polynomial) {
	CosetLagrangeToLagrangeNormalWithCache(p, nil)
}

// CosetLagrangeToLagrangeNormalWithCache converts p in place using cache for
// the FFT domain.
func CosetLagrangeToLagrangeNormalWithCache(p Polynomial, cache *DomainCache) {
	CosetLagrangeNormalToCanonicalWithCache(p, cache)
	cache.Get(uint64(len(p))).FFT(p, fft.DIF)
	utils.BitReverse(p)
}

// CosetLagrangeNormalToCanonicalWithCache converts p in place from
// coset-Lagrange Normal form (evaluations on the coset {FrGen·ω^j}) to
// canonical Normal form (coefficients c_k in standard order). This is the
// first half of CosetLagrangeToLagrangeNormalWithCache; callers that
// subsequently need a different transform (e.g. AIR quotient chunking, which
// FFTs each N-sized chunk individually) avoid a redundant round-trip FFT.
func CosetLagrangeNormalToCanonicalWithCache(p Polynomial, cache *DomainCache) {
	d := cache.Get(uint64(len(p)))

	d.FFTInverse(p, fft.DIF) // coset-Lagrange Normal → coset-canonical BitReversed
	utils.BitReverse(p)      // → coset-canonical Normal

	// Multiply by invFrGen^k to get standard canonical coefficients c_k.
	// The serial acc dependency is broken per chunk by seeding acc with
	// invFrGen^chunkStart.
	invFrGen := d.FrMultiplicativeGen
	invFrGen.Inverse(&invFrGen)
	parallel.ExecuteWithThreshold(len(p), quotientParallelThreshold, func(start, end int) {
		acc := PowUint64(invFrGen, uint64(start))
		for k := start; k < end; k++ {
			p[k].Mul(&p[k], &acc)
			acc.Mul(&acc, &invFrGen)
		}
	})
}

// CosetExtLagrangeToLagrangeNormal converts an extension polynomial from
// coset-Lagrange normal form to standard Lagrange normal form.
func CosetExtLagrangeToLagrangeNormal(p ExtPolynomial) {
	CosetExtLagrangeToLagrangeNormalWithCache(p, nil)
}

// CosetExtLagrangeToLagrangeNormalWithCache converts p in place using cache for
// the FFT domain.
func CosetExtLagrangeToLagrangeNormalWithCache(p ExtPolynomial, cache *DomainCache) {
	CosetExtLagrangeNormalToCanonicalWithCache(p, cache)
	cache.Get(uint64(len(p))).FFTExt6(p, fft.DIF)
	utils.BitReverse(p)
}

// CosetExtLagrangeNormalToCanonicalWithCache is the ext-field counterpart of
// CosetLagrangeNormalToCanonicalWithCache.
func CosetExtLagrangeNormalToCanonicalWithCache(p ExtPolynomial, cache *DomainCache) {
	d := cache.Get(uint64(len(p)))

	d.FFTInverseExt6(p, fft.DIF)
	utils.BitReverse(p)

	invFrGen := d.FrMultiplicativeGen
	invFrGen.Inverse(&invFrGen)
	parallel.ExecuteWithThreshold(len(p), quotientParallelThreshold, func(start, end int) {
		acc := PowUint64(invFrGen, uint64(start))
		for k := start; k < end; k++ {
			p[k].MulByElement(&p[k], &acc)
			acc.Mul(&acc, &invFrGen)
		}
	})
}
