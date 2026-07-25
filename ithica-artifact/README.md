# ITHICA artifact — source

LLVM compiler passes that duplicate computations at compile time to detect
silent data corruption, applied to two real programs: **cpu-check** and
**FleetBench**.

This repository holds the **source and build recipes**. The large prebuilt
binaries and the packed toolchain image are published separately on Zenodo
(DOI: _TODO_) — they are not tracked here.

## Layout

- **`cpu-check-ae/`** — Google's `cpu_check`, instrumented with the ITHICA
  passes. Build from source with GNU Guix:
  ```bash
  cd cpu-check-ae
  ./guix.sh                 # enter the pinned clang/LLVM 14.0.6 environment
  make PASS=arith           # or CC | mem | memdiv | br | arithmem | ...
  ```
  (The `scripts/setup.sh` + `scripts/build.sh` path instead loads the packed
  toolchain image from Zenodo — use it if you don't have Guix.)

- **`fleetbench-ae/`** — Google's FleetBench, instrumented with the ITHICA
  passes. Build from source with Docker:
  ```bash
  cd fleetbench-ae
  scripts/setup.sh                              # docker build the image
  scripts/build.sh --bench=hashing --pass=arith
  ```

## The passes

The ITHICA pass sources are the `*Pass.cpp` files:
`ArithmeticPass`, `MemPass`, `MemDivPass`, `BranchPass`, and the combinations
`ArithMemPass`, `ArithMemDivPass`, `ArithMemDivBrPass` — found in
`fleetbench-ae/context/passes-src/` (and mirrored in `cpu-check-ae/`).
Compile a single pass quickly with `cpu-check-ae/scripts/build_pass.sh <pass>`.

See each subfolder's `README.md` and the paper's Artifact Appendix for full
instructions, requirements, and expected results.
