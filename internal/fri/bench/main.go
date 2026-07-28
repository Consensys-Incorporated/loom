package main

import (
	"flag"
	"fmt"
	"os"
	"runtime"
	"runtime/metrics"
	"runtime/pprof"
	"sync/atomic"
	"text/tabwriter"
	"time"

	ext "github.com/consensys/gnark-crypto/field/koalabear/extensions"
	fiatshamir "github.com/consensys/loom/internal/fiat-shamir"
	"github.com/consensys/loom/internal/fri"
	"github.com/consensys/loom/internal/hash"
	"github.com/consensys/loom/internal/poly"
)

var (
	minLog2      = flag.Int("min-log2", 10, "smallest native polynomial size as log2(N)")
	maxLog2      = flag.Int("max-log2", 15, "largest native polynomial size as log2(N)")
	basePolys    = flag.Int("base-polys", 500, "number of base-field polynomials per size group")
	extPolys     = flag.Int("ext-polys", 500, "number of extension-field polynomials per size group")
	rate         = flag.Int("rate", 4, "Reed-Solomon blowup factor")
	numQueries   = flag.Int("queries", 32, "number of FRI queries")
	maxShifts    = flag.Int("max-shifts", 3, "maximum number of shifts per polynomial")
	fsHasher     = flag.String("fs-hash", "poseidon2", "fs-hash: poseidon2 | sha256 | blake3")
	hashName     = flag.String("hash", fri.HashBackendPoseidon2, "hash backend: poseidon2 | sha256 | blake3")
	seed         = flag.Uint64("seed", 1, "deterministic synthetic input seed")
	gomaxprocs   = flag.Int("gomaxprocs", 0, "override GOMAXPROCS (0 = leave default)")
	sampleMillis = flag.Int("sample-ms", 50, "heap sampling interval (ms)")
)

func main() {
	flag.Parse()

	if *gomaxprocs > 0 {
		runtime.GOMAXPROCS(*gomaxprocs)
	}
	validateConfig()

	backend, err := fri.HashBackendByID(*hashName)
	if err != nil {
		fail("%v", err)
	}

	maxN := 1 << *maxLog2
	params, err := fri.NewParams((*rate)*maxN, maxN, *numQueries, backend.LeafHasher, backend.NodeHasher)
	if err != nil {
		fail("NewParams: %v", err)
	}
	pcs := fri.NewPCSWithParams(params)

	fmt.Printf("fri pcs bench  sizes=2^%d..2^%d  base=%d/group  ext=%d/group  rate=%d  queries=%d  hash=%s hashFS=%s GOMAXPROCS=%d  NumCPU=%d\n\n",
		*minLog2, *maxLog2, *basePolys, *extPolys, *rate, *numQueries, backend.ID, *fsHasher, runtime.GOMAXPROCS(0), runtime.NumCPU())

	batch := makeSyntheticBatch(*minLog2, *maxLog2, *basePolys, *extPolys, *seed)
	batches := []fri.Batch{batch}
	shifts := makeSyntheticShifts(batch, *maxShifts, *seed^0x5eed)

	var domainCache poly.DomainCache
	var phases []phaseReport

	tr := newTracker("Commit", *sampleMillis)
	// cpuFile := mustCreate("cpu_prove.pprof")
	// if err := pprof.StartCPUProfile(cpuFile); err != nil {
	// 	fail("StartCPUProfile: %v", err)
	// }
	committed, err := pcs.Commit(batch, fri.WithDomainCache(&domainCache))
	if err != nil {
		fail("Commit: %v", err)
	}
	// pprof.StopCPUProfile()
	// cpuFile.Close()
	phases = append(phases, tr.stop())

	roots := []hash.Digest{committed.Tree.Root()}
	shapes := []fri.BatchShapes{committed.Shapes}

	newFsHasher, err := fiatshamir.NewTranscriptHasherByID(*fsHasher)
	if err != nil {
		fail("NewTranscriptHasherByID: %v", err)
	}

	proverFS, zeta := proverTranscript(newFsHasher, roots)

	tr = newTracker("Open", *sampleMillis)
	proof, err := pcs.Open(batches, []fri.Committed{committed}, []fri.BatchShifts{shifts}, zeta, proverFS, fri.WithOpenDomainCache(&domainCache))
	if err != nil {
		fail("Open: %v", err)
	}
	phases = append(phases, tr.stop())

	verifierFS, verifierZeta := verifierTranscript(newFsHasher, roots)
	if !verifierZeta.Equal(&zeta) {
		fail("verifier transcript sampled a different zeta")
	}

	tr = newTracker("Verify", *sampleMillis)

	// Drop trace-generation junk so the Verify heap snapshot is clean.
	runtime.GC()
	dumpHeap("heap_before_verify.pprof")
	cpuFile := mustCreate("cpu_verify.pprof")
	if err := pprof.StartCPUProfile(cpuFile); err != nil {
		fail("StartCPUProfile: %v", err)
	}
	if err := pcs.Verify(roots, shapes, []fri.BatchShifts{shifts}, zeta, proof, verifierFS); err != nil {
		fail("Verify: %v", err)
	}
	pprof.StopCPUProfile()
	cpuFile.Close()
	dumpHeap("heap_after_verify.pprof")
	phases = append(phases, tr.stop())

	fmt.Println()
	printSummary(phases, runtime.GOMAXPROCS(0))
	fmt.Printf("\nproof: %d DEEP roots, %d FRI roots, %d query samplings\n",
		len(proof.DeepQuotientRoots), len(proof.FRIProof.FRIRoots), len(proof.PointSamplings))
}

func mustCreate(path string) *os.File {
	f, err := os.Create(path)
	if err != nil {
		fail("create %s: %v", path, err)
	}
	return f
}

func dumpHeap(path string) {
	f := mustCreate(path)
	defer f.Close()
	if err := pprof.WriteHeapProfile(f); err != nil {
		fail("WriteHeapProfile(%s): %v", path, err)
	}
}

func validateConfig() {
	if *minLog2 < 1 {
		fail("-min-log2 must be >= 1")
	}
	if *maxLog2 < *minLog2 {
		fail("-max-log2 must be >= -min-log2")
	}
	if *basePolys < 0 || *extPolys < 0 {
		fail("-base-polys and -ext-polys must be non-negative")
	}
	if *basePolys == 0 && *extPolys == 0 {
		fail("at least one of -base-polys or -ext-polys must be positive")
	}
	if *rate <= 1 || *rate&(*rate-1) != 0 {
		fail("-rate must be a power of two greater than one")
	}
	if *numQueries <= 0 {
		fail("-queries must be positive")
	}
	if *maxShifts <= 0 {
		fail("-max-shifts must be positive")
	}
}

func makeSyntheticBatch(minLog2, maxLog2, nbBase, nbExt int, seed uint64) fri.Batch {
	batch := make(fri.Batch, 0, maxLog2-minLog2+1)
	for logN := minLog2; logN <= maxLog2; logN++ {
		N := 1 << logN
		group := fri.Group{
			Base: make([]poly.Polynomial, nbBase),
			Ext:  make([]poly.ExtPolynomial, nbExt),
		}
		for i := range group.Base {
			group.Base[i] = makeBasePolynomial(N, seed, logN, i)
		}
		for i := range group.Ext {
			group.Ext[i] = makeExtPolynomial(N, seed, logN, i)
		}
		batch = append(batch, group)
	}
	return batch
}

func makeBasePolynomial(n int, seed uint64, logN int, polyIdx int) poly.Polynomial {
	out := make(poly.Polynomial, n)
	x := seed ^ uint64(logN+1)*0x9e3779b185ebca87 ^ uint64(polyIdx+1)*0xc2b2ae3d27d4eb4f
	for i := range out {
		x = nextRand(x)
		out[i].SetUint64(x)
	}
	return out
}

func makeExtPolynomial(n int, seed uint64, logN int, polyIdx int) poly.ExtPolynomial {
	out := make(poly.ExtPolynomial, n)
	x := seed ^ uint64(logN+1)*0x165667b19e3779f9 ^ uint64(polyIdx+1)*0x85ebca77c2b2ae63
	for i := range out {
		for limb := 0; limb < 6; limb++ {
			x = nextRand(x)
			setExtLimb(&out[i], limb, x)
		}
	}
	return out
}

func setExtLimb(v *ext.E6, limb int, x uint64) {
	switch limb {
	case 0:
		v.B0.A0.SetUint64(x)
	case 1:
		v.B0.A1.SetUint64(x)
	case 2:
		v.B1.A0.SetUint64(x)
	case 3:
		v.B1.A1.SetUint64(x)
	case 4:
		v.B2.A0.SetUint64(x)
	case 5:
		v.B2.A1.SetUint64(x)
	}
}

func makeSyntheticShifts(batch fri.Batch, maxShifts int, seed uint64) fri.BatchShifts {
	rng := seed
	out := make(fri.BatchShifts, len(batch))
	for g, group := range batch {
		N := groupNativeSizeForBench(group)
		out[g].Base = make([][]int, len(group.Base))
		for i := range group.Base {
			out[g].Base[i], rng = makeShiftList(N, maxShifts, rng)
		}
		out[g].Ext = make([][]int, len(group.Ext))
		for i := range group.Ext {
			out[g].Ext[i], rng = makeShiftList(N, maxShifts, rng)
		}
	}
	return out
}

func groupNativeSizeForBench(group fri.Group) int {
	if len(group.Base) > 0 {
		return len(group.Base[0])
	}
	return len(group.Ext[0])
}

func makeShiftList(N, maxShifts int, rng uint64) ([]int, uint64) {
	if maxShifts > N {
		maxShifts = N
	}
	rng = nextRand(rng)
	count := 1 + int(rng%uint64(maxShifts))
	out := make([]int, 0, count)
	seen := make(map[int]struct{}, count)
	for len(out) < count {
		rng = nextRand(rng)
		shift := int(rng % uint64(N))
		if _, ok := seen[shift]; ok {
			continue
		}
		seen[shift] = struct{}{}
		out = append(out, shift)
	}
	return out, rng
}

func nextRand(x uint64) uint64 {
	x ^= x >> 12
	x ^= x << 25
	x ^= x >> 27
	return x * 2685821657736338717
}

const zetaChallengeName = "fri_bench_zeta"

func proverTranscript(newTranscriptHasher fiatshamir.NewTranscriptHasher, roots []hash.Digest) (*fiatshamir.Transcript, ext.E6) {
	fs := fiatshamir.NewTranscript(newTranscriptHasher())
	zeta := bindRootsAndSampleZeta(fs, roots)
	return fs, zeta
}

func verifierTranscript(newTranscriptHasher fiatshamir.NewTranscriptHasher, roots []hash.Digest) (*fiatshamir.Transcript, ext.E6) {
	fs := fiatshamir.NewTranscript(newTranscriptHasher())
	zeta := bindRootsAndSampleZeta(fs, roots)
	return fs, zeta
}

func bindRootsAndSampleZeta(fs *fiatshamir.Transcript, roots []hash.Digest) ext.E6 {
	if err := fs.NewChallenge(zetaChallengeName); err != nil {
		fail("register zeta challenge: %v", err)
	}
	for i, root := range roots {
		if err := fs.Bind(zetaChallengeName, root[:]); err != nil {
			fail("bind root %d: %v", i, err)
		}
	}
	out, err := fs.ComputeChallenge(zetaChallengeName)
	if err != nil {
		fail("sample zeta: %v", err)
	}
	return hash.OutputToExt(out)
}

type phaseReport struct {
	name string

	wall    time.Duration
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

var cpuMetricNames = []string{
	"/cpu/classes/user:cpu-seconds",
	"/cpu/classes/gc/total:cpu-seconds",
}

var allocMetricNames = []string{
	"/gc/heap/allocs:bytes",
	"/gc/heap/allocs:objects",
}

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

func fail(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "fri bench: "+format+"\n", args...)
	os.Exit(1)
}
