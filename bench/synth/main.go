// Command synth proves a synthetic AIR with configurable trace shape
// (rows × cols) and reports per-phase wall time, prove/verify totals and
// proof size. It is the loom counterpart of plonky3's prove_prime_field_31
// example: both stacks build a deg-2 row-local constraint over a tall or
// wide trace and use matching FRI parameters, so the two can be compared
// apples-to-apples.
//
// Per row group of 3 columns (a, b, c), one constraint is enforced:
//
//	a * b - c = 0
//
// Run examples:
//
//	go run ./bench/synth -log2-rows 20 -repetitions 8                         # tall
//	go run ./bench/synth -log2-rows 14 -repetitions 512                       # wide
//	go run ./bench/synth -log2-rows 20 -repetitions 8 -hash sha256 -fs-hash sha256
package main

import (
	"bytes"
	"encoding/gob"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"runtime/trace"
	"sort"
	"sync"
	"time"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/loom"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/setup"
	loomtrace "github.com/consensys/loom/trace"
	"github.com/consensys/loom/verifier"
)

var (
	log2Rows    = flag.Int("log2-rows", 20, "log2 of trace height (rows)")
	repetitions = flag.Int("repetitions", 16, "number of (a,b,c) tuples per row; trace width = 3 * repetitions")
	hashName    = flag.String("hash", "poseidon2", "Merkle tree hash backend: poseidon2 | sha256 | blake3")
	fsHashName  = flag.String("fs-hash", "poseidon2", "Fiat-Shamir transcript hasher: poseidon2 | sha256 | blake3")
	gomaxprocs  = flag.Int("gomaxprocs", 0, "override GOMAXPROCS (0 = leave default)")
	profileDir  = flag.String("profile-dir", "", "if non-empty, write cpu_prove.pprof + heap_after_prove.pprof + trace_prove.out into this directory (created if missing)")
)

const moduleName = "synth"

func colName(i int) string { return fmt.Sprintf("%s.c_%d", moduleName, i) }

func main() {
	flag.Parse()

	if *gomaxprocs > 0 {
		runtime.GOMAXPROCS(*gomaxprocs)
	}
	procs := runtime.GOMAXPROCS(0)
	rows := 1 << *log2Rows
	width := 3 * *repetitions

	fmt.Printf("loom synth   rows=2^%d (=%d)  width=%d (3 cols × %d reps)  cells=%d  hash=%s  fs-hash=%s  GOMAXPROCS=%d  NumCPU=%d\n\n",
		*log2Rows, rows, width, *repetitions, rows*width, *hashName, *fsHashName, procs, runtime.NumCPU())

	// Build module + compile program.
	builder := board.NewBuilder()
	m := board.NewModule(moduleName)
	m.N = rows
	for k := 0; k < *repetitions; k++ {
		a := expr.Col(colName(3 * k))
		b := expr.Col(colName(3*k + 1))
		c := expr.Col(colName(3*k + 2))
		m.AssertZero(a.Mul(b).Sub(c)) // a*b - c = 0
	}
	builder.AddModule(m)
	program, err := board.Compile(&builder)
	if err != nil {
		fail("Compile: %v", err)
	}

	// Synthesize trace (column-major). Values are derived from cheap
	// deterministic arithmetic so trace generation isn't the bottleneck.
	t := loomtrace.New(width)
	for k := 0; k < *repetitions; k++ {
		a := make([]koalabear.Element, rows)
		b := make([]koalabear.Element, rows)
		c := make([]koalabear.Element, rows)
		for i := 0; i < rows; i++ {
			a[i].SetUint64(uint64(i + 1 + k))
			b[i].SetUint64(uint64(2*i + 3 + k))
			c[i].Mul(&a[i], &b[i])
		}
		t.SetBase(colName(3*k), a)
		t.SetBase(colName(3*k+1), b)
		t.SetBase(colName(3*k+2), c)
	}

	hashBackend := resolveHashBackend(*hashName)
	fsHasher := resolveFSHasher(*fsHashName)

	// Prove with phase timings collected via the public WithPhaseCallback option.
	type phase struct {
		name string
		d    time.Duration
	}
	var (
		mu     sync.Mutex
		phases []phase
	)
	opts := []prover.Option{
		prover.WithHashBackend(hashBackend),
		prover.WithNewTranscriptHasher(fsHasher),
		prover.WithPhaseCallback(func(name string, d time.Duration) {
			mu.Lock()
			phases = append(phases, phase{name, d})
			mu.Unlock()
		}),
	}

	// Optional profiling: CPU + execution trace start before Prove,
	// stop after; heap profile is taken once Prove returns.
	var cpuFile, traceFile, heapFile *os.File
	if *profileDir != "" {
		if err := os.MkdirAll(*profileDir, 0o755); err != nil {
			fail("mkdir profile dir: %v", err)
		}
		var err error
		cpuFile, err = os.Create(filepath.Join(*profileDir, "cpu_prove.pprof"))
		if err != nil {
			fail("create cpu profile: %v", err)
		}
		if err := pprof.StartCPUProfile(cpuFile); err != nil {
			fail("start cpu profile: %v", err)
		}
		traceFile, err = os.Create(filepath.Join(*profileDir, "trace_prove.out"))
		if err != nil {
			fail("create trace: %v", err)
		}
		if err := trace.Start(traceFile); err != nil {
			fail("start trace: %v", err)
		}
	}

	t0 := time.Now()
	prf, err := prover.Prove(t, setup.ProvingKey{}, nil, program, opts...)
	if err != nil {
		fail("Prove: %v", err)
	}
	proveWall := time.Since(t0)

	if *profileDir != "" {
		pprof.StopCPUProfile()
		trace.Stop()
		if err := cpuFile.Close(); err != nil {
			fail("close cpu profile: %v", err)
		}
		if err := traceFile.Close(); err != nil {
			fail("close trace: %v", err)
		}
		runtime.GC()
		var herr error
		heapFile, herr = os.Create(filepath.Join(*profileDir, "heap_after_prove.pprof"))
		if herr != nil {
			fail("create heap profile: %v", herr)
		}
		if herr := pprof.Lookup("heap").WriteTo(heapFile, 0); herr != nil {
			fail("write heap profile: %v", herr)
		}
		if herr := heapFile.Close(); herr != nil {
			fail("close heap profile: %v", herr)
		}
		fmt.Printf("profiles -> %s\n", *profileDir)
	}

	// Serialize for size, then verify.
	var buf bytes.Buffer
	if err := gob.NewEncoder(&buf).Encode(&prf); err != nil {
		fail("encode proof: %v", err)
	}

	t0 = time.Now()
	if err := verifier.Verify(nil, setup.VerificationKey{}, program, prf,
		verifier.WithHashBackend(hashBackend),
		verifier.WithNewTranscriptHasher(fsHasher)); err != nil {
		fail("Verify: %v", err)
	}
	verifyWall := time.Since(t0)

	// Report — sorted by duration so the heaviest phases come first.
	sort.Slice(phases, func(i, j int) bool { return phases[i].d > phases[j].d })
	fmt.Println("prove-phase breakdown:")
	for _, p := range phases {
		share := 100 * float64(p.d) / float64(proveWall)
		fmt.Printf("  %-26s %s  %5.1f%%\n", p.name, fmtDur(p.d), share)
	}

	fmt.Printf("\nprove wall : %s\n", fmtDur(proveWall))
	fmt.Printf("verify wall: %s\n", fmtDur(verifyWall))
	fmt.Printf("proof size : %d B (gob)\n", buf.Len())
	fmt.Printf("proof      : %d commitments, %d FRI levels, %d query samplings\n",
		len(prf.Commitments), len(prf.Opening.FRIProof.LevelQueries)+1, len(prf.Opening.PointSamplings))
}

func resolveHashBackend(name string) loom.HashBackend {
	switch name {
	case "poseidon2":
		return loom.Poseidon2HashBackend()
	case "sha256":
		return loom.SHA256HashBackend()
	case "blake3":
		return loom.Blake3HashBackend()
	default:
		fail("unknown hash backend %q (want poseidon2 | sha256 | blake3)", name)
		return loom.HashBackend{}
	}
}

func resolveFSHasher(name string) fiatshamir.NewTranscriptHasher {
	h, err := fiatshamir.NewTranscriptHasherByID(name)
	if err != nil {
		fail("unknown fs-hash %q (want poseidon2 | sha256 | blake3)", name)
	}
	return h
}

func fmtDur(d time.Duration) string {
	switch {
	case d >= time.Second:
		return fmt.Sprintf("%.2fs", d.Seconds())
	case d >= time.Millisecond:
		return fmt.Sprintf("%.1fms", float64(d.Microseconds())/1000)
	default:
		return d.String()
	}
}

func fail(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "synth: "+format+"\n", args...)
	os.Exit(1)
}
