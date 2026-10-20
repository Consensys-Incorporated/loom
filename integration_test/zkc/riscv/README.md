# RISC-V guest, proven with loom

The zkc RISC-V (R5) interpreter and its Go glue, ported from
[lineth-monorepo](https://github.com/LFDT-Lineth/lineth-monorepo) at `main`
`9ff51bc01` (2026-10-20), dual-licensed Apache-2.0 / MIT there. The files are
copied verbatim, except for import paths and the notes below.

| Here           | lineth-monorepo                                                  |
| -------------- | ---------------------------------------------------------------- |
| `zkc/`         | `arithmetization/src/main` without `predecoding/` (the standalone predecoding program, which lineth does not compile into the interpreter either) |
| `riscv.go`     | `arithmetization/gopkg/embedded/embedded.go`: embeds `zkc/` instead of `src/main` |
| `elfmapping/`  | `arithmetization/gopkg/elfmapping`                               |
| `predecoding/` | `arithmetization/gopkg/predecoding`                              |
| `minimalelf/`  | `prover-ray/zkcdriver/minimal-elf` (synthetic guest ELFs)        |

`compile_test.go` compiles without zkc's AIR validation, which reports the
modules reached through the interpreter's call bus as unreachable (upstream
too).

`riscv_test.go` proves and verifies a guest end to end: ELF → predecoding
inputs → zkc trace (one shard) and check → loom, through the driver in
`integration_test/go_corset`. It is skipped with `-short`:

    go test ./integration_test/zkc/riscv -run TestRiscvAllInOne -v

To update the port, re-export the paths above from lineth (e.g. with
`git archive`) and rerun the tests.
