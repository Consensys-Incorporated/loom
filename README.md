# loom

> **WARNING: This code has not been audited and is not ready for production use. It is provided for research and experimentation purposes only. Do not use it to secure real assets or in any security-critical context.**

`loom` is a Go library for building and verifying **Interactive Oracle Proofs (IOPs)** over the [Koalabear](https://github.com/consensys/gnark-crypto) finite field.

It lets you describe a computation as a set of polynomial constraints over a **trace** (a collection of named columns), compile it into a proof system, and produce a succinct proof that all constraints vanish on the evaluation domain.

Fiat-Shamir challenges, including lookup/permutation challenges, canonical trace-round challenges, `__zeta`, `alpha_DEEP`, and FRI fold challenges, are sampled in the Koalabear E6 extension field. The `alpha_DEEP` challenge binds the claimed evaluations folded into the DEEP quotient. Base trace columns remain base-valued and are lifted only when evaluated at extension points. The resulting soundness error is approximately `N/2^186`.

## Benchmarks

Benchmarks are run on a MacBook pro apple M4 48GB, with 40x instances plonk-like traces of size 1<<14
(`cd bench && go run main.go -log2-size 14 -instances 40 -hash poseidon2 -queries 200`)


### Poseidon2 backend (no SIMD)

```text
phase           wall      cpu      par     gc%    alloc      objs   peakHeap   GCs
-----           ----      ---      ---     ---    -----      ----   --------   ---
traces+modules  195.5ms   421.5ms   2.16x   7.6%  676.0 MiB  1.54M  83.6 MiB   41
compile         8.6ms     0s        0.00x   0.0%  31.5 MiB   22.2k  109.4 MiB  0
merge-trace     31.917µs  0s        0.00x   0.0%  6.3 KiB    4      109.4 MiB  0
prove           4.39s     25.46s    5.80x   0.1%  2.03 GiB   60.0k  1.20 GiB   5
verify          181.5ms   0s        0.00x   0.0%  9.9 MiB    17.4k  77.5 MiB   0
-----           ----      ---      ---     ---    -----      ----   --------   ---
TOTAL           4.78s     25.88s    5.42x   0.2%  2.74 GiB   1.64M  1.20 GiB   46

cpu      = on-CPU time (user goroutines + GC); excludes idle
par      = cpu / wall   (ideal: 14x = 14 cores fully busy; 1x = single-threaded)
gc%      = GC CPU time / on-CPU time
peakHeap = max HeapAlloc observed during phase (sampled in background)

proof: 3 commitments, 1 FRI levels, 200 query samplings
```

### Sha256 backend

```text
phase           wall      cpu      par     gc%    alloc      objs    peakHeap   GCs
-----           ----      ---      ---     ---    -----      ----    --------   ---
traces+modules  172.3ms   376.9ms   2.19x   8.2%  675.1 MiB  1.54M   106.0 MiB  41
compile         8.6ms     0s        0.00x   0.0%  31.5 MiB   22.5k   128.8 MiB  0
merge-trace     31.916µs  0s        0.00x   0.0%  6.3 KiB    4       128.9 MiB  0
prove           1.74s     12.78s    7.36x   0.3%  3.04 GiB   62.55M  1.59 GiB   7
verify          35.4ms    0s        0.00x   0.0%  22.2 MiB   531.2k  90.1 MiB   0
-----           ----      ---      ---     ---    -----      ----    --------   ---
TOTAL           1.95s     13.16s    6.73x   0.5%  3.76 GiB   64.65M  1.59 GiB   48

cpu      = on-CPU time (user goroutines + GC); excludes idle
par      = cpu / wall   (ideal: 14x = 14 cores fully busy; 1x = single-threaded)
gc%      = GC CPU time / on-CPU time
peakHeap = max HeapAlloc observed during phase (sampled in background)

proof: 3 commitments, 1 FRI levels, 200 query samplings
```

### BLAKE3 backend

```text
phase           wall     cpu      par     gc%    alloc      objs    peakHeap   GCs
-----           ----     ---      ---     ---    -----      ----    --------   ---
traces+modules  198.6ms  412.8ms   2.08x   7.7%  674.6 MiB  1.54M   110.0 MiB  40
compile         10.1ms   50.6ms    5.03x   2.5%  33.0 MiB   28.7k   110.0 MiB  1
merge-trace     30.75µs  0s        0.00x   0.0%  6.3 KiB    4       103.4 MiB  0
prove           1.65s    9.68s     5.85x   0.1%  2.07 GiB   2.04M   1.22 GiB   5
verify          42.9ms   0s        0.00x   0.0%  11.9 MiB   137.2k  79.8 MiB   0
-----           ----     ---      ---     ---    -----      ----    --------   ---
TOTAL           1.90s    10.14s    5.32x   0.4%  2.78 GiB   3.75M   1.22 GiB   46

cpu      = on-CPU time (user goroutines + GC); excludes idle
par      = cpu / wall   (ideal: 14x = 14 cores fully busy; 1x = single-threaded)
gc%      = GC CPU time / on-CPU time
peakHeap = max HeapAlloc observed during phase (sampled in background)

proof: 3 commitments, 1 FRI levels, 200 query samplings
```

## Core concepts

| Concept | Type | Description |
|---|---|---|
| Trace | `trace.Trace` (`Base` and `Ext` column maps) | Named base or extension columns. Columns in the same module share the module size N; a program may contain several sizes |
| Relation | `expr.Expr` | A multivariate polynomial that must vanish row-wise |
| Builder | `board.Builder` | Accumulates modules, relations, and derivation steps before compilation |
| Module | `board.Module` | A named constraint domain; all columns within it share the same N |
| Program | `board.Program` | Compiled IOP: level-ordered step schedule + folded vanishing relations |
| Statement | `loom.Statement` | Verifier-owned data: program, verification key, and public inputs |
| Witness | `loom.Witness` | Prover-owned data: witness trace and proving key |
| Hash backend | `loom.HashBackend` | Hashes used by commitments, Merkle proofs, FRI, and Fiat-Shamir |
| Exposed values | `proof.Proof.ExposedValues` / `proof.ExposedValue` | Values produced by board steps such as `AddExposeIthValueStep` and carried by the proof |

## Workflow

```
1. Create a board.Builder and add one board.Module per constraint domain
2. Describe polynomial constraints on each module (AssertZero, …)
3. Attach standard arguments (permutation, lookup, …) from the arguments/ package
4. board.Compile(&builder) → Program
5. setup.Setup(setupTrace, program) → setup.ProvingKey + setup.VerificationKey, if the program has precommitted public columns
6. Build a `loom.Statement` from the program, verification key, and public inputs
7. Build a `loom.Witness` from the witness trace and proving key
8. loom.Prove(statement, witness) → Proof
9. loom.Verify(statement, proof)
```

## Example: PLONK gate + copy constraint

Prove that PLONK arithmetic gates are satisfied and that wires are consistently connected.

```go
builder := board.NewBuilder()
mod := board.NewModule("plonk")

// Arithmetic gate: QL·L + QR·R + QM·L·R + QO·O + QK = 0
gate := expr.Col("QL").Mul(expr.Col("L")).
    Add(expr.Col("QR").Mul(expr.Col("R"))).
    Add(expr.Col("QM").Mul(expr.Col("L")).Mul(expr.Col("R"))).
    Add(expr.Col("QO").Mul(expr.Col("O"))).
    Add(expr.Col("QK"))
mod.AssertZero(gate)
builder.AddModule(mod)

// Copy constraint: wires L, R, O are consistently permuted by S
arguments.CopyConstraint(&builder, "plonk", []expr.Expr{
    expr.Col("L"), expr.Col("R"), expr.Col("O"),
}, S)  // S is a board.PermutationGen

pg, err := board.Compile(&builder)
statement := loom.Statement{Program: pg}
witness := loom.Witness{Trace: trace}
prf, err := loom.Prove(statement, witness)
err = loom.Verify(statement, prf)
```

## Standard arguments (`arguments/`)

| Function | What it proves |
|---|---|
| `PermutationWithinModule(builder, module, A, B []expr.Expr)` | `{A[i]}` = `{B[i]}` as multisets (same module) |
| `PermutationTupleWithinModule(builder, module, A, B [][]expr.Expr)` | Same for row-tuples |
| `PermutationCrossModules(builder, A, B board.Column)` | Multiset equality across two modules |
| `CopyConstraint(builder, module, A []expr.Expr, S PermutationGen)` | PLONK-style copy constraint |
| `FixedPermutationWithinModule(builder, module, A, B [][]expr.Expr, S PermutationGen)` | Fixed permutation check |
| `Lookup(builder, S, T board.Column)` | Every value in `S` appears in `T` |
| `LookupTuple(builder, S, T board.Table)` | Same for row-tuples |
| `LookupUnion(builder, S, T []board.Column)` | Multiple S/T pairs sharing one challenge |
| `LookupUnionTuple(builder, S, T []board.Table)` | Same for row-tuples |
| `CLookup(builder, S, T board.Column, selS, selT expr.Expr)` | Conditional lookup with per-row selectors |
| `CLookupTuple(builder, S, T board.Table, selS, selT expr.Expr)` | Conditional lookup for row-tuples |
| `CLookupUnion(builder, selS, selT []expr.Expr, S, T []board.Column)` | Conditional lookup, multi-pair |
| `CLookupUnionTuple(builder, selS, selT []expr.Expr, S, T []board.Table)` | Conditional tuple lookup, multi-pair |
| `Range(builder, S board.Column, bound uint64)` | Every value in `S` is in `[0, bound)` |

`board.Column{Module: "name", In: expr}` and `board.Table{Module: "name", In: []expr}` are the two helper types used across all argument functions.

## Public values

Values exposed with `board.AddExposeIthValueStep`, `board.AddExposeRelativeIthValueStep`, `board.AddExposeLastEntryStep`, and `board.AddExposeValuesStep` are stored in `proof.Proof.ExposedValues`. The verifier reconstructs their sparse columns at `__zeta` and checks the constraints that bind them to the private trace.

```go
exposedValue := proof.ExposedValue{
    Entries: []proof.PublicEntry{
        {Idx: 0, Value: zeroElement},
        {Idx: 5, Value: someElement},
    },
}
```

The `PublicInputs` field on `loom.Statement` is reserved for verifier-supplied statement values. Prover-produced values should stay in `Proof.ExposedValues`.

For columns that require a setup commitment (e.g. PLONK selector columns), mark them with `builder.MakeColumnPublic` and use `setup.Setup` to pre-commit them:

```go
provingKey, verificationKey, err := loom.Setup(setupTrace, pg)

statement := loom.Statement{Program: pg, VerificationKey: verificationKey}
witness := loom.Witness{Trace: witnessTrace, ProvingKey: provingKey}
prf, err := loom.Prove(statement, witness)
err = loom.Verify(statement, prf)
```

`setupTrace` only needs the fixed columns registered with `MakeColumnPublic`.
The proving key stores those columns in Lagrange form and the setup Merkle
trees; `loom.Prove` overlays them with the per-instance witness trace.

## Hash backends

Loom supports configurable hash backends. `Poseidon2` is the default and is the
right backend for algebraic or recursive verification. `SHA-256` and `BLAKE3`
are available for non-recursive proving workflows where native hash performance
is preferred.

The selected backend is part of the protocol identity: setup keys and proofs
carry a `HashBackendID`, and the backend ID is bound into the Fiat-Shamir
transcript. Prover and verifier must use the same backend.

For programs without setup commitments, pass the backend to both proving and
verification:

```go
backend := loom.SHA256HashBackend()

prf, err := loom.Prove(
    statement,
    witness,
    loom.WithProverHashBackend(backend),
)
err = loom.Verify(
    statement,
    prf,
    loom.WithVerifierHashBackend(backend),
)
```

For programs with setup commitments, select the backend during setup. The
proving and verification keys then carry the backend metadata, so `Prove` and
`Verify` can infer it:

```go
backend := loom.SHA256HashBackend()

provingKey, verificationKey, err := loom.Setup(
    setupTrace,
    pg,
    loom.WithSetupHashBackend(backend),
)

statement := loom.Statement{Program: pg, VerificationKey: verificationKey}
witness := loom.Witness{Trace: witnessTrace, ProvingKey: provingKey}
prf, err := loom.Prove(statement, witness)
err = loom.Verify(statement, prf)
```

## Development

```sh
go mod download
go test ./integration_test/go_corset/zkc   # current Go-Corset/zkc integration path
go test ./...                              # full suite
```

Current Go-Corset/zkc fixtures live in `integration_test/go_corset/zkc/testdata`.

## Visualisation (`viz/`)

```go
viz.ViewDag(pg, "plan.html")         // interactive step-DAG in the browser
viz.WriteRawTraceToCSV("trace.csv", trace)  // column dump
```
