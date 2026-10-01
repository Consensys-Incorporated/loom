// loom bench: a beefy end-to-end benchmark that exercises the prover on an
// aggregated batch of PLONK instances and reports the metrics we care about
// when hunting for bottlenecks:
//
//   - wall time per phase
//   - CPU time per phase (user + GC), and the effective parallelization
//     factor (CPU/wall) so we can tell single-threaded sections at a glance
//   - bytes / objects allocated per phase
//   - peak heap during each phase (sampled in the background)
//   - GC count, GC CPU share, total CPU consumed
//
// pprof profiles (CPU, heap before/after Prove, allocations) are written to
// -profile-dir so we can drill down with `go tool pprof`.
//
// Run examples:
//
//	go run ./bench
//	go run ./bench -instances 80 -log2-size 16 -hash sha256 -fs-hash sha256
//	go run ./bench -skip-fri -profile-dir /tmp/loom-bench
package main

import (
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"runtime/metrics"
	"runtime/pprof"
	"sync/atomic"
	"text/tabwriter"
	"time"

	"github.com/consensys/loom"
	"github.com/consensys/loom/arguments"
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
	gnarkplonk "github.com/consensys/loom/integration_test/gnark_plonk"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/prover"
	"github.com/consensys/loom/setup"
	"github.com/consensys/loom/trace"
	"github.com/consensys/loom/verifier"
)

// Defaults are sized so that Prove runs for ~15-30s on a 16-32 core box: large
// enough that any phase under measurement collects plenty of pprof samples and
// short single-threaded sections (which would be invisible in a 1s run) become
// obvious. Tune down with -instances / -log2-size for quick iteration.
var (
	nbInstances = flag.Int("instances", 40, "number of PLONK instances to aggregate")
	log2Size    = flag.Int("log2-size", 17, "log2 of each PLONK instance size")
	hashName    = flag.String("hash", "poseidon2", "Merkle tree hash backend: poseidon2 | sha256 | blake3")
	fsHashName  = flag.String("fs-hash", "poseidon2", "Fiat-Shamir transcript hasher: poseidon2 | sha256 | blake3")
	profileDir  = flag.String("profile-dir", "bench_profiles", "directory to write pprof profiles")
	numQueries  = flag.Int("queries", 32, "number of FRI queries")
	skipFRI     = flag.Bool("skip-fri", false, "skip the FRI / sampling phase of Prove")
	gomaxprocs  = flag.Int("gomaxprocs", 0, "override GOMAXPROCS (0 = leave default)")
	sampleMs    = flag.Int("sample-ms", 50, "heap sampling interval (ms) for peak-heap tracking")
)

func main() {
	flag.Parse()

	if *gomaxprocs > 0 {
		runtime.GOMAXPROCS(*gomaxprocs)
	}
	if err := os.MkdirAll(*profileDir, 0o755); err != nil {
		fail("mkdir profile dir: %v", err)
	}

	hashBackend := resolveHashBackend(*hashName)
	fsHasher := resolveFSHasher(*fsHashName)
	procs := runtime.GOMAXPROCS(0)
	n := 1 << *log2Size

	fmt.Printf("loom bench   instances=%d  size=2^%d (=%d)  hash=%s  fs-hash=%s  queries=%d GOMAXPROCS=%d  NumCPU=%d\n",
		*nbInstances, *log2Size, n, *hashName, *fsHashName, *numQueries, procs, runtime.NumCPU())
	fmt.Printf("profiles ->  %s\n\n", *profileDir)

	var phases []phaseReport

	// ---- Phase 1: build modules + generate per-instance traces -----------
	tr := newTracker("traces+modules", *sampleMs)
	builder := board.NewBuilder()
	traces := make([]trace.Trace, *nbInstances)
	for i := 0; i < *nbInstances; i++ {
		t, sigma, size, err := gnarkplonk.GetIthPlonkTrace(n, i)
		if err != nil {
			fail("GetIthPlonkTrace[%d]: %v", i, err)
		}
		traces[i] = t
		builder.AddModule(gnarkplonk.PrepareIthPlonk(size, i))

		lro := []expr.Expr{
			expr.Col(gnarkplonk.Ith(gnarkplonk.ID_L, i)),
			expr.Col(gnarkplonk.Ith(gnarkplonk.ID_R, i)),
			expr.Col(gnarkplonk.Ith(gnarkplonk.ID_O, i)),
		}
		sigmaGen := board.NewPermutationGen(sigma, gnarkplonk.Ith("plonk.S", i))
		if err := arguments.CopyConstraint(&builder, gnarkplonk.Ith("plonk", i), lro, sigmaGen); err != nil {
			fail("CopyConstraint[%d]: %v", i, err)
		}
	}
	phases = append(phases, tr.stop())

	// ---- Phase 2: compile program ----------------------------------------
	tr = newTracker("compile", *sampleMs)
	program, err := board.Compile(&builder)
	if err != nil {
		fail("Compile: %v", err)
	}
	phases = append(phases, tr.stop())

	// ---- Phase 3: merge per-instance traces into one ---------------------
	tr = newTracker("merge-trace", *sampleMs)
	fullTrace := prover.MergeTrace(traces[0], traces[1:]...)
	traces = nil
	phases = append(phases, tr.stop())

	// Drop trace-generation junk so the Prove heap snapshot is clean.
	runtime.GC()
	dumpHeap(filepath.Join(*profileDir, "heap_before_prove.pprof"))

	// ---- Phase 4: prove --------------------------------------------------
	cpuFile := mustCreate(filepath.Join(*profileDir, "cpu_prove.pprof"))
	if err := pprof.StartCPUProfile(cpuFile); err != nil {
		fail("StartCPUProfile: %v", err)
	}

	opts := []prover.Option{prover.WithNumFriQueries(*numQueries), prover.WithHashBackend(hashBackend), prover.WithNewTranscriptHasher(fsHasher)}
	if *skipFRI {
		opts = append(opts, prover.SkipFRI())
	}

	tr = newTracker("prove", *sampleMs)
	prf, err := prover.Prove(fullTrace, setup.ProvingKey{}, nil, program, opts...)
	if err != nil {
		fail("Prove: %v", err)
	}
	phases = append(phases, tr.stop())

	pprof.StopCPUProfile()
	cpuFile.Close()
	dumpHeap(filepath.Join(*profileDir, "heap_after_prove.pprof"))
	dumpProfile("allocs", filepath.Join(*profileDir, "allocs_after_prove.pprof"))

	// ---- Phase 5: verify --------------------------------------------------
	runtime.GC()
	tr = newTracker("verify", *sampleMs)
	optsVerifier := []verifier.Option{verifier.WithNumFriQueries(*numQueries), verifier.WithHashBackend(hashBackend), verifier.WithNewTranscriptHasher(fsHasher)}
	if err = verifier.Verify(nil, setup.VerificationKey{}, program, prf, optsVerifier...); err != nil {
		fail("Verify: %v", err)
	}
	phases = append(phases, tr.stop())

	// ---- Report ----------------------------------------------------------
	fmt.Println()
	printSummary(phases, procs)

	// Touch the proof so the compiler doesn't get clever; also give a sense of
	// output size.
	fmt.Printf("\nproof: %d commitments, %d FRI levels, %d query samplings\n",
		len(prf.Commitments), len(prf.Opening.FRIProof.LevelQueries)+1, len(prf.Opening.PointSamplings))
}

// -----------------------------------------------------------------------------
// phase tracker
// -----------------------------------------------------------------------------

type phaseReport struct {
	name string

	wall time.Duration

	// cpuBusy is on-CPU time actually spent doing work: user goroutine time
	// + GC. Excludes idle, so cpuBusy/wall is a real parallelization metric
	// (cf. /cpu/classes/total which is just GOMAXPROCS × wall and tells you
	// nothing).
	cpuBusy time.Duration
	cpuUser time.Duration
	cpuGC   time.Duration

	allocBytes   uint64
	allocObjects uint64

	heapStart uint64
	heapEnd   uint64
	heapPeak  uint64

	gcCount uint32
}

type tracker struct {
	name string

	wallStart time.Time

	cpuUserStart float64
	cpuGCStart   float64

	allocBytesStart   uint64
	allocObjectsStart uint64

	memStart runtime.MemStats

	peakHeap atomic.Uint64
	stopCh   chan struct{}
	doneCh   chan struct{}
}

func newTracker(name string, sampleMs int) *tracker {
	t := &tracker{name: name}
	t.cpuUserStart, t.cpuGCStart = readCPU()
	t.allocBytesStart, t.allocObjectsStart = readAllocCounters()
	runtime.ReadMemStats(&t.memStart)
	t.peakHeap.Store(t.memStart.HeapAlloc)
	t.stopCh = make(chan struct{})
	t.doneCh = make(chan struct{})
	go t.sampleLoop(time.Duration(sampleMs) * time.Millisecond)
	t.wallStart = time.Now()
	return t
}

func (t *tracker) sampleLoop(interval time.Duration) {
	defer close(t.doneCh)
	if interval <= 0 {
		<-t.stopCh
		return
	}
	tk := time.NewTicker(interval)
	defer tk.Stop()
	var ms runtime.MemStats
	for {
		select {
		case <-t.stopCh:
			return
		case <-tk.C:
			runtime.ReadMemStats(&ms)
			if cur := ms.HeapAlloc; cur > t.peakHeap.Load() {
				t.peakHeap.Store(cur)
			}
		}
	}
}

func (t *tracker) stop() phaseReport {
	wall := time.Since(t.wallStart)
	close(t.stopCh)
	<-t.doneCh

	cpuUser, cpuGC := readCPU()
	allocBytes, allocObjects := readAllocCounters()
	var memEnd runtime.MemStats
	runtime.ReadMemStats(&memEnd)

	if memEnd.HeapAlloc > t.peakHeap.Load() {
		t.peakHeap.Store(memEnd.HeapAlloc)
	}

	dUser := secondsToDuration(cpuUser - t.cpuUserStart)
	dGC := secondsToDuration(cpuGC - t.cpuGCStart)

	return phaseReport{
		name:         t.name,
		wall:         wall,
		cpuBusy:      dUser + dGC,
		cpuUser:      dUser,
		cpuGC:        dGC,
		allocBytes:   allocBytes - t.allocBytesStart,
		allocObjects: allocObjects - t.allocObjectsStart,
		heapStart:    t.memStart.HeapAlloc,
		heapEnd:      memEnd.HeapAlloc,
		heapPeak:     t.peakHeap.Load(),
		gcCount:      memEnd.NumGC - t.memStart.NumGC,
	}
}

// -----------------------------------------------------------------------------
// runtime/metrics helpers
// -----------------------------------------------------------------------------

var cpuMetricNames = []string{
	"/cpu/classes/user:cpu-seconds",
	"/cpu/classes/gc/total:cpu-seconds",
}

var allocMetricNames = []string{
	"/gc/heap/allocs:bytes",
	"/gc/heap/allocs:objects",
}

// readCPU returns cumulative on-CPU seconds (user goroutine, GC) since
// process start. We deliberately avoid /cpu/classes/total because it counts
// idle slots (GOMAXPROCS × wall) and so tells you nothing about real CPU use.
func readCPU() (user, gc float64) {
	samples := make([]metrics.Sample, len(cpuMetricNames))
	for i, n := range cpuMetricNames {
		samples[i].Name = n
	}
	metrics.Read(samples)
	return samples[0].Value.Float64(), samples[1].Value.Float64()
}

func readAllocCounters() (bytes, objects uint64) {
	samples := make([]metrics.Sample, len(allocMetricNames))
	for i, n := range allocMetricNames {
		samples[i].Name = n
	}
	metrics.Read(samples)
	return samples[0].Value.Uint64(), samples[1].Value.Uint64()
}

func secondsToDuration(s float64) time.Duration {
	return time.Duration(s * float64(time.Second))
}

// -----------------------------------------------------------------------------
// reporting
// -----------------------------------------------------------------------------

func printSummary(phases []phaseReport, procs int) {
	var totalWall, totalCPU, totalGC time.Duration
	var totalAllocBytes, totalAllocObjects uint64
	var peakHeap uint64
	var gcCount uint32
	for _, p := range phases {
		totalWall += p.wall
		totalCPU += p.cpuBusy
		totalGC += p.cpuGC
		totalAllocBytes += p.allocBytes
		totalAllocObjects += p.allocObjects
		gcCount += p.gcCount
		if p.heapPeak > peakHeap {
			peakHeap = p.heapPeak
		}
	}

	w := tabwriter.NewWriter(os.Stdout, 0, 0, 2, ' ', 0)
	fmt.Fprintln(w, "phase\twall\tcpu\tpar\tgc%\talloc\tobjs\tpeakHeap\tGCs")
	fmt.Fprintln(w, "-----\t----\t---\t---\t---\t-----\t----\t--------\t---")
	for _, p := range phases {
		fmt.Fprintf(w, "%s\t%s\t%s\t%5.2fx\t%4.1f%%\t%s\t%s\t%s\t%d\n",
			p.name,
			fmtDur(p.wall),
			fmtDur(p.cpuBusy),
			parallelization(p.cpuBusy, p.wall),
			gcShare(p.cpuGC, p.cpuBusy),
			fmtBytes(p.allocBytes),
			fmtCount(p.allocObjects),
			fmtBytes(p.heapPeak),
			p.gcCount,
		)
	}
	fmt.Fprintln(w, "-----\t----\t---\t---\t---\t-----\t----\t--------\t---")
	fmt.Fprintf(w, "TOTAL\t%s\t%s\t%5.2fx\t%4.1f%%\t%s\t%s\t%s\t%d\n",
		fmtDur(totalWall),
		fmtDur(totalCPU),
		parallelization(totalCPU, totalWall),
		gcShare(totalGC, totalCPU),
		fmtBytes(totalAllocBytes),
		fmtCount(totalAllocObjects),
		fmtBytes(peakHeap),
		gcCount,
	)
	w.Flush()

	fmt.Println()
	fmt.Printf("cpu      = on-CPU time (user goroutines + GC); excludes idle\n")
	fmt.Printf("par      = cpu / wall   (ideal: %dx = %d cores fully busy; 1x = single-threaded)\n", procs, procs)
	fmt.Printf("gc%%      = GC CPU time / on-CPU time\n")
	fmt.Println("peakHeap = max HeapAlloc observed during phase (sampled in background)")
}

// -----------------------------------------------------------------------------
// formatting
// -----------------------------------------------------------------------------

func fmtDur(d time.Duration) string {
	switch {
	case d >= time.Minute:
		return fmt.Sprintf("%dm%02ds", int(d.Minutes()), int(d.Seconds())%60)
	case d >= time.Second:
		return fmt.Sprintf("%.2fs", d.Seconds())
	case d >= time.Millisecond:
		return fmt.Sprintf("%.1fms", float64(d.Microseconds())/1000)
	default:
		return d.String()
	}
}

func fmtBytes(b uint64) string {
	const (
		KiB = 1 << 10
		MiB = 1 << 20
		GiB = 1 << 30
	)
	switch {
	case b >= GiB:
		return fmt.Sprintf("%.2f GiB", float64(b)/GiB)
	case b >= MiB:
		return fmt.Sprintf("%.1f MiB", float64(b)/MiB)
	case b >= KiB:
		return fmt.Sprintf("%.1f KiB", float64(b)/KiB)
	default:
		return fmt.Sprintf("%d B", b)
	}
}

func fmtCount(n uint64) string {
	switch {
	case n >= 1_000_000_000:
		return fmt.Sprintf("%.2fB", float64(n)/1e9)
	case n >= 1_000_000:
		return fmt.Sprintf("%.2fM", float64(n)/1e6)
	case n >= 1_000:
		return fmt.Sprintf("%.1fk", float64(n)/1e3)
	default:
		return fmt.Sprintf("%d", n)
	}
}

func parallelization(cpu, wall time.Duration) float64 {
	if wall <= 0 {
		return 0
	}
	return float64(cpu) / float64(wall)
}

func gcShare(gc, cpu time.Duration) float64 {
	if cpu <= 0 {
		return 0
	}
	return 100 * float64(gc) / float64(cpu)
}

// -----------------------------------------------------------------------------
// misc helpers
// -----------------------------------------------------------------------------

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

func dumpHeap(path string) {
	f := mustCreate(path)
	defer f.Close()
	if err := pprof.WriteHeapProfile(f); err != nil {
		fail("WriteHeapProfile(%s): %v", path, err)
	}
}

func dumpProfile(name, path string) {
	p := pprof.Lookup(name)
	if p == nil {
		fail("pprof.Lookup(%q) returned nil", name)
	}
	f := mustCreate(path)
	defer f.Close()
	if err := p.WriteTo(f, 0); err != nil {
		fail("write %s profile: %v", name, err)
	}
}

func mustCreate(path string) *os.File {
	f, err := os.Create(path)
	if err != nil {
		fail("create %s: %v", path, err)
	}
	return f
}

func fail(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "bench: "+format+"\n", args...)
	os.Exit(1)
}
