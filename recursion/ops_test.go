package recursion

import (
	"math/bits"
	"math/rand/v2"
	"testing"

	"github.com/consensys/gnark-crypto/field/koalabear"
	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/trace"
)

func randE6(r *rand.Rand) ext.E6 {
	var x ext.E6
	for _, c := range []*koalabear.Element{&x.B0.A0, &x.B0.A1, &x.B1.A0, &x.B1.A1, &x.B2.A0, &x.B2.A1} {
		c.SetUint64(r.Uint64())
	}
	return x
}

// compileAndProve compiles m, applies tamper to its trace (if any) and proves.
func compileAndProve(t *testing.T, m *Machine, tamper func(trace.Trace)) error {
	t.Helper()
	p, err := m.Compile()
	if err != nil {
		t.Fatal(err)
	}
	if tamper != nil {
		tamper(p.Trace)
	}
	return prove(t, p)
}

func wantE6(t *testing.T, m *Machine, addr int, want ext.E6, what string) {
	t.Helper()
	if got := m.e6(addr); !got.Equal(&want) {
		t.Fatalf("%s: got %s, want %s", what, got.String(), want.String())
	}
}

// e6Machine runs every E6 operation on witness inputs and checks the results
// against constants.
func e6Machine(t *testing.T) *Machine {
	r := rand.New(rand.NewPCG(1, 2))
	var m Machine
	x, y, z := randE6(r), randE6(r), randE6(r)
	a, b, c := m.Witness(E6Cell(x)), m.Witness(E6Cell(y)), m.Witness(E6Cell(z))

	var want ext.E6
	want.Mul(&x, &y)
	prod := m.Mul(a, b)
	wantE6(t, &m, prod, want, "mul")
	m.AssertEq(prod, m.Const(E6Cell(want)))

	want.Add(&x, &y)
	m.AssertEq(m.Add(a, b), m.Const(E6Cell(want)))
	want.Sub(&x, &y)
	m.AssertEq(m.Sub(a, b), m.Const(E6Cell(want)))

	want.Div(&x, &y)
	q := m.Div(a, b)
	wantE6(t, &m, q, want, "div")
	m.AssertEq(q, m.Const(E6Cell(want)))

	// x·z² + y·z + z, and a one-coefficient Horner
	var t1 ext.E6
	want.Mul(&x, &z)
	want.Add(&want, &y)
	want.Mul(&want, &z)
	want.Add(&want, &z)
	h := m.Horner(c, []int{a, b, c})
	wantE6(t, &m, h, want, "horner")
	m.AssertEq(h, m.Const(E6Cell(want)))
	t1 = x
	m.AssertEq(m.Horner(c, []int{a}), m.Const(E6Cell(t1)))

	// a base scalar is its E6 embedding
	var s koalabear.Element
	s.SetUint64(7)
	sc := m.Witness(ScalarCell(s))
	want.MulByElement(&x, &s)
	m.AssertEq(m.Mul(a, sc), m.Const(E6Cell(want)))
	return &m
}

func TestE6Chip(t *testing.T) {
	if err := compileAndProve(t, e6Machine(t), nil); err != nil {
		t.Fatalf("valid E6 operations rejected: %v", err)
	}
	for name, tamper := range map[string]func(trace.Trace){
		"product":  func(tr trace.Trace) { tr.Base["e6.o2"][0].SetUint64(5) },
		"operand":  func(tr trace.Trace) { tr.Base["e6.a0"][0].SetUint64(5) },
		"quotient": func(tr trace.Trace) { tr.Base["e6.b3"][6].SetUint64(5) },
		"horner":   func(tr trace.Trace) { tr.Base["e6.o1"][9].SetUint64(5) },
		"constant": func(tr trace.Trace) { tr.Base["const.v1"][0].SetUint64(5) },
	} {
		t.Run(name, func(t *testing.T) {
			if err := compileAndProve(t, e6Machine(t), tamper); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}

	t.Run("wrong claim", func(t *testing.T) {
		m := e6Machine(t)
		r := rand.New(rand.NewPCG(3, 4))
		x, y := randE6(r), randE6(r)
		m.AssertEq(m.Witness(E6Cell(x)), m.Witness(E6Cell(y)))
		if err := compileAndProve(t, m, nil); err == nil {
			t.Fatal("x = y accepted")
		}
	})
}

var bitsValues = []uint64{0, 1, 5, 1<<24 - 1, 1 << 24, 0x7f000000 /* p − 1 */, 0x12345678, 1<<30 + 3}

const bitsN = 10

func bitsMachine() (*Machine, []Bits) {
	var m Machine
	var outs []Bits
	for _, v := range bitsValues {
		outs = append(outs, m.Bits(m.Witness(ScalarCell(koalabear.NewElement(v))), bitsN))
	}
	return &m, outs
}

func TestBitsChip(t *testing.T) {
	m, outs := bitsMachine()
	for k, v := range bitsValues {
		low := v & (1<<bitsN - 1)
		for i := range bitsN {
			if got := m.cells[outs[k].Shr[i]][0].Uint64(); got != low>>i {
				t.Fatalf("value %d: Shr[%d] = %d, want %d", v, i, got, low>>i)
			}
			if got := m.cells[outs[k].Bit[i]][0].Uint64(); got != v>>i&1 {
				t.Fatalf("value %d: Bit[%d] = %d, want %d", v, i, got, v>>i&1)
			}
		}
		// read the outputs, so that they are bound by the bus
		m.AssertEq(outs[k].Shr[3], m.Const(ScalarCell(koalabear.NewElement(low>>3))))
		m.AssertEq(outs[k].Bit[2], m.Const(ScalarCell(koalabear.NewElement(v>>2&1))))
	}
	if err := compileAndProve(t, m, nil); err != nil {
		t.Fatalf("valid decompositions rejected: %v", err)
	}

	for name, tamper := range map[string]func(trace.Trace){
		"bit": func(tr trace.Trace) { flip(&tr.Base["bits.b"][2*BitsWidth+1]) },
		// the decomposition of v + p, for v = 5: the same value in the field,
		// but its bits are not the canonical ones
		"non canonical": func(tr trace.Trace) {
			const k, p = 2, 0x7f000001
			x := bitsValues[k] + p
			for i := range BitsWidth {
				row := k*BitsWidth + i
				tr.Base["bits.b"][row].SetUint64(x >> i & 1)
				tr.Base["bits.w"][row].SetUint64(x & (1<<i - 1))
				if i < bitsN {
					tr.Base["bits.r"][row].SetUint64((x & (1<<bitsN - 1)) >> i)
				}
			}
		},
	} {
		t.Run(name, func(t *testing.T) {
			m, _ := bitsMachine()
			if err := compileAndProve(t, m, tamper); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}

func flip(e *koalabear.Element) {
	if e.IsZero() {
		e.SetOne()
	} else {
		e.SetZero()
	}
}

// packMachine packs items of every kind, at offsets that do and do not cross
// a cell, and hashes the stream.
func packMachine() (*Machine, []int) {
	r := rand.New(rand.NewPCG(5, 6))
	var m Machine
	var d Cell
	for i := range d {
		d[i].SetUint64(r.Uint64())
	}
	items := []int{
		m.Witness(ScalarCell(koalabear.NewElement(9))),
		m.Witness(E6Cell(randE6(r))),
		m.Witness(d),
		m.Witness(E6Cell(randE6(r))),
		m.Const(ScalarCell(koalabear.NewElement(3))),
	}
	kinds := []int{KindScalar, KindE6, KindDigest, KindE6, KindScalar}
	stream, n := m.Pack(items, kinds)
	m.Sponge(stream, n)
	return &m, items
}

func TestWindowChip(t *testing.T) {
	m, items := packMachine()
	var want []koalabear.Element
	for _, it := range items[:2] {
		want = append(want, m.cells[it][:]...)
	}
	if err := compileAndProve(t, m, nil); err != nil {
		t.Fatalf("valid windows rejected: %v", err)
	}
	for name, tamper := range map[string]func(trace.Trace){
		// lane 3 of the E6 item, which starts at offset 1 of the first cell
		"item lane": func(tr trace.Trace) { tr.Base["window.i3"][1].SetUint64(5) },
		// the digest crosses from the first cell into the second
		"crossing lane": func(tr trace.Trace) { tr.Base["window.q0"][2].SetUint64(5) },
	} {
		t.Run(name, func(t *testing.T) {
			m, _ := packMachine()
			if err := compileAndProve(t, m, tamper); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}

func bitrev(i, width int) int {
	return int(bits.Reverse(uint(i)) >> (bits.UintSize - width))
}

// TestMerkleX checks the x⁻¹ accumulator against gInv^bitrev(index).
func TestMerkleX(t *testing.T) {
	m := openingsMachine(t, smallCfg)
	var gInv koalabear.Element
	gInv.SetUint64(123456789)
	var xbs []int
	paths := append([]pathInst(nil), m.paths...)
	for _, p := range paths {
		xb := m.MerklePathX(p.leaf, p.siblings, p.index, p.root, gInv)
		idx := int(m.cells[p.index][0].Uint64())
		var want koalabear.Element
		want.ExpInt64(gInv, int64(bitrev(idx, len(p.siblings))))
		if got := m.cells[xb][0]; !got.Equal(&want) {
			t.Fatalf("x⁻¹ = %s, want %s", got.String(), want.String())
		}
		if got := m.cells[xb][1].Uint64(); got != uint64(idx&1) {
			t.Fatalf("b0 = %d, want %d", got, idx&1)
		}
		m.AssertEq(xb, m.Const(m.cells[xb]))
		xbs = append(xbs, xb)
	}
	if err := compileAndProve(t, m, nil); err != nil {
		t.Fatalf("valid paths rejected: %v", err)
	}
	t.Run("accumulator", func(t *testing.T) {
		m := openingsMachine(t, smallCfg)
		for _, p := range paths {
			xb := m.MerklePathX(p.leaf, p.siblings, p.index, p.root, gInv)
			m.AssertEq(xb, m.Const(m.cells[xb]))
		}
		// the paths added by MerklePathX start after the first ones
		row := len(paths)*len(paths[0].siblings) + 1
		if err := compileAndProve(t, m, func(tr trace.Trace) { tr.Base["merkle.x"][row].SetUint64(5) }); err == nil {
			t.Fatal("tampered accumulator accepted")
		}
	})
}

// foldMachine builds a FRI query of the given number of rounds with random
// pairs, challenges and x⁻¹, and consistent next layers; round 1 has an
// injected term.
func foldMachine(rounds int, lie bool) *Machine {
	r := rand.New(rand.NewPCG(7, 8))
	var m Machine
	var half koalabear.Element
	half.SetUint64(2)
	half.Inverse(&half)
	zeroCell := m.Const(Cell{})

	p, q := randE6(r), randE6(r)
	var chain []FoldRound
	for j := range rounds {
		alpha := randE6(r)
		var xi koalabear.Element
		xi.SetUint64(r.Uint64())
		b := r.IntN(2)
		var xb Cell
		xb[0], xb[1] = xi, koalabear.NewElement(uint64(b))
		inj := zeroCell
		var injV ext.E6
		if j == 1 {
			injV = randE6(r)
			inj = m.Witness(E6Cell(injV))
		}
		// (p + q)/2 + α·(p − q)·x⁻¹/2 + inj
		var sum, diff, next ext.E6
		sum.Add(&p, &q)
		sum.MulByElement(&sum, &half)
		diff.Sub(&p, &q)
		diff.MulByElement(&diff, &xi)
		diff.MulByElement(&diff, &half)
		diff.Mul(&diff, &alpha)
		next.Add(&sum, &diff)
		next.Add(&next, &injV)
		chain = append(chain, FoldRound{
			P: m.Witness(E6Cell(p)), Q: m.Witness(E6Cell(q)),
			Alpha: m.Witness(E6Cell(alpha)), XB: m.Witness(xb), Inj: inj,
		})
		other := randE6(r)
		if b == 0 {
			p, q = next, other
		} else {
			p, q = other, next
		}
		if j == rounds-1 {
			p = next
		}
	}
	if lie {
		p.B1.A0.SetUint64(5)
	}
	m.FoldChain(chain, m.Witness(E6Cell(p)))
	return &m
}

func TestFoldChip(t *testing.T) {
	if err := compileAndProve(t, foldMachine(4, false), nil); err != nil {
		t.Fatalf("valid fold chain rejected: %v", err)
	}
	if err := compileAndProve(t, foldMachine(4, true), nil); err == nil {
		t.Fatal("wrong final value accepted")
	}
	for name, tamper := range map[string]func(trace.Trace){
		"selection bit": func(tr trace.Trace) { flip(&tr.Base["fold.bn"][0]) },
		"injection":     func(tr trace.Trace) { tr.Base["fold.j2"][1].SetUint64(5) },
		"challenge":     func(tr trace.Trace) { tr.Base["fold.al4"][2].SetUint64(5) },
	} {
		t.Run(name, func(t *testing.T) {
			if err := compileAndProve(t, foldMachine(4, false), tamper); err == nil {
				t.Fatal("tampered trace accepted")
			}
		})
	}
}

// TestChipWidths logs the next-level leaf cost of each chip, on a machine
// that uses them all.
func TestChipWidths(t *testing.T) {
	m := foldMachine(4, false)
	m.Bits(m.Witness(ScalarCell(koalabear.NewElement(77))), bitsN)
	r := rand.New(rand.NewPCG(9, 9))
	a, b := m.Witness(E6Cell(randE6(r))), m.Witness(E6Cell(randE6(r)))
	stream, n := m.Pack([]int{a, b}, []int{KindE6, KindE6})
	leaf := m.Sponge(stream, n)
	var sibs []int
	for range 3 {
		sibs = append(sibs, m.Witness(Cell{}))
	}
	m.MerklePathX(leaf, sibs, m.Witness(Cell{}), m.Witness(Cell{}), koalabear.One())
	m.Mul(a, b)
	p, err := m.Compile()
	if err != nil {
		t.Fatal(err)
	}
	logBreakdown(t, p)
}
