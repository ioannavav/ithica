# ITHICA Artifact Appendix

> **Author TODOs before release:**
> 1. Reserve a **Zenodo DOI** *before* the release (Zenodo's "Reserve DOI" button). Required for the ACM "Artifacts Available" badge — a GitHub URL alone does not qualify.
> 2. Public repository URL.
> 3. Confirm the ITHICA-pass license (MIT?). Keep the Apache-2.0 note for the vendored programs — redistributing them obliges stating their license.

## Abstract

This artifact includes the ITHICA LLVM IR passes (Arith, Mem, MemDiv, Br, and their combinations) used to transform real programs into tests for hardware defects (first contribution in §1). It demonstrates that ITHICA passes successfully instrument the two programs used in the paper: cpu-check and FleetBench. For ease of use, the artifact provides a pinned Docker build environment per program (kept separate due to disjoint build requirements), containing all dependencies needed to compile both programs (with and without ITHICA) from source. The artifact reproduces the runtime overhead and binary-size increase that ITHICA transformations impose relative to the uninstrumented cpu-check baseline, as reported in Table 6 of the paper. Pre-built binaries for all configurations of Table 6 are provided to reproduce the measurements directly, even without recompilation. The remaining results (§7–§8) require access to proprietary defective hardware owned by the hyperscaler, and therefore cannot be reproduced.

## Artifact check-list (meta-information)

- **Transformations:** Code for ITHICA's LLVM IR compiler passes — Arith, Mem, MemDiv, and Br — and their combinations ArithMem, ArithMemDiv, and ArithMemDivBr.
- **Program:** The input programs compiled with ITHICA: cpu-check and FleetBench. Both are open-source and shipped with the artifact.
- **Compilation:** No external dependencies. Clang/LLVM/lld 14.0.6 and bazel 7.3.1 are used within the two Docker images.
- **Binary:** Pre-built, statically linked x86-64 binaries available.
- **Hardware:** Required: x86-64 Linux machine with at least 16 GB of RAM and 40 GB of free disk space on the Docker filesystem. Preferred: 32 cores or more and hyperthreading enabled. (Reference host: Intel Xeon Gold 6226R; 2×16 cores, 2 threads/core, 500 GB.)
- **Runtime Environment:** Docker and Bash. Network access.
- **Metrics:** Runtime performance overhead and binary-size increase relative to the baseline.
- **Output:** Log files reproducing results similar to Table 6 (with expected fluctuations based on the hardware used, discussed in §Notes).
- **Experiments:** Two experiments (§Experiment workflow): E1 reproduces the results of Table 6 — it measures per-ITHICA-pass overhead and binary-size increase on cpu-check, including parameter sweeps for Arith; E2 measures the same metrics on FleetBench with and without Arith (not in the main paper). Separately, this artifact allows rebuilding both programs from source to demonstrate successful ITHICA use in practice.
- **How much disk space required (approximately)?:** 40 GB
- **How much time is needed to prepare workflow (approximately)?:** 10 minutes for Docker environment setup. To recompile all binaries from source: additional 8 hours.
- **How much time is needed to complete experiments (approximately)?:** 70 minutes total to execute all binaries.
- **Publicly available?:** yes (de-anonymized github link will be provided after shepherding): https://anonymous.4open.science/r/ithica-sdc
- **Code licenses (if publicly available)?:** MIT
- **Workflow automation framework used?:** Docker.
- **Archived (provide DOI)?:** **[TODO: Zenodo DOI]**

## Description

### How to access

The artifact is a source repository at **[TODO: public repository URL]**, archived on Zenodo (DOI above).

The artifact contains two directories, `cpu-check-ae/` and `fleetbench-ae/`, one per program. Each holds the ITHICA pass sources, the pinned program source, the pinned toolchain, pre-built binaries (to avoid heavy recompilation of some programs if needed), and three driver scripts: `setup.sh` provisions the toolchain, `build.sh` compiles the program with a chosen ITHICA pass, and `measure.sh` runs the (resulting or pre-built) binaries and reports the metrics.

### Hardware dependencies

x86-64 Linux machine with 40 GB of free disk space. 8 GB RAM suffices to run the pre-built binaries (`measure.sh`); 16 GB RAM are needed to optionally re-build binaries from source (`build.sh`). To reproduce the reported results closely, a host with at least 32 physical / 64 logical CPUs is recommended.

Reference host: Intel Xeon Gold 6226R — 2 sockets × 16 cores *per socket* = 32 physical cores, and 2 threads per core = 64 logical CPUs; 500 GB RAM. The results obtained are expected to vary depending on the underlying hardware (§Notes).

### Software dependencies

Only Docker (the cpu-check toolchain is exported from a pinned GNU Guix environment via `guix pack`, and the FleetBench image is built from a Dockerfile).

Network access is required while building either image. On hosts where Docker's bridge network cannot reach GitHub, add `--network=host` to `docker build`.

## Installation

Installation provisions the pinned Docker toolchain of each program; the build steps in §Evaluation use these images.

**For cpu-check:**

```bash
cd cpu-check-ae
scripts/setup.sh   # docker load (shipped image)
```

**For FleetBench:**

```bash
cd fleetbench-ae
scripts/setup.sh   # docker build (Dockerfile)
```

## Experiment workflow

The evaluation first builds the ITHICA passes (`build_pass.sh`) and uses them to compile the two programs (`build.sh`). Two script-driven experiments then measure the resulting binaries: for cpu-check, E1 measures the per-pass overhead and binary-size increase compared to the uninstrumented baseline (the main result, reproducing Table 6), and E2 measures the same two metrics for FleetBench with and without the Arith pass. The §Evaluation section gives commands and expected results.

ITHICA is not limited to these two programs: a small toy program (`toy_overhead/toy_program.cpp`) ships in the cpu-check image so users can quickly instrument and run it (`scripts/toy_overhead.sh`) or compile their own programs.

## Evaluation and expected results

**Table: Results equivalent to Table 6**, here measured on a non-industrial (non-proprietary) server. Performance overhead and binary-size increase for ITHICA transformations — and different block-size configurations — compared to cpu-check (uninstrumented baseline).

| ITHICA Pass   | Arith (1) | Arith (2) | Arith (4) | Arith (8) | Arith (dep) | Mem  | MemDiv | Br   |
|---------------|-----------|-----------|-----------|-----------|-------------|------|--------|------|
| Performance   | 2.18      | 1.79      | 1.64      | 1.52      | 1.75        | 1.17 | 53.67  | 1.17 |
| Binary Size   | 8.47      | 5.88      | 4.59      | 4.11      | 6.11        | 3.06 | 13.12  | 1.24 |

*Personal, non-industrial server — Intel Xeon Gold 6226R, 2.9 GHz, 2×16 cores, 2 threads/core, L1: 1MB D+I, L2: 32MB, L3: 44MB, Mem: 500 GB*

The central claim reproduced by this artifact is the per-pass **runtime overhead** and **binary-size increase** of the ITHICA transformations relative to the uninstrumented cpu-check baseline, i.e., the results of Table 6 and Obs. 8 in the paper. The first goal of the evaluation is to successfully use the ITHICA passes to compile the two programs; the measurement experiments then run the resulting binaries. Expected values on the reference host are given in the two tables here; absolute values vary with the underlying hardware (§Hardware dependencies).

### Getting started

`scripts/build_pass.sh` builds the ITHICA pass named next to it:

```bash
scripts/build_pass.sh arith   # or mem|memdiv|br|...
```

### Building the two programs

`build.sh` compiles each program with the chosen ITHICA pass.

For cpu-check:

```bash
cd cpu-check-ae
scripts/build.sh --pass=CC      # baseline, no ITHICA
scripts/build.sh --pass=arith   # ITHICA pass (e.g., Arith)
# knobs: --blocksize=1|2|4|8|0 --interleaving=1|2|4|8|0
```

For FleetBench:

```bash
cd fleetbench-ae
scripts/build.sh --bench=hashing --nopass      # baseline
scripts/build.sh --bench=hashing --pass=arith  # ITHICA
```

Each `build.sh --pass=P` (for cpu-check) run copies its binary into `built/P_cpu_check`; each `--bench=B` (for FleetBench) run extracts a self-contained bundle (with the benchmark's required runfiles) into `built/B_baseline` or `built/B_arith`.

> **Note:** the `build.sh` scripts are independent of `build_pass.sh`: each rebuilds the ITHICA pass itself before compiling the program, and emits verbose logs, including a "Running on function" message per compiled function confirming that the pass is applied throughout the program.

### Measuring

`measure.sh` runs the binaries in the directory specified with `--cc-dir=<dir>` (cpu-check) or `--fb-dir=<dir>` (FleetBench) — e.g., `built` from the step above. The directory must contain the uninstrumented baseline and at least one ITHICA-instrumented binary, otherwise the script exits with an error. Pre-built binaries ship in `Binaries/` but are not guaranteed to run on all hosts (§Notes).

### E1 — For cpu-check

Performance overhead and binary-size increase (main result; ~40 min for all Table 6 configurations). To run:

```bash
cd cpu-check-ae
scripts/measure.sh --sec=120 --cc-dir=built
# -> results/cpucheck_results.txt   (table)
#    results/logs/*.out             (raw binary outputs)
```

Each binary runs for a fixed budget (120 seconds); the overhead is the ratio of cpu-check's to the instrumented binary's throughput of rounds ("SUCCESSES" in raw logs) completed within the specified time.

**Expected Result:** Similar to the table above, also on par with the average (Avg) ratios in Table 6. The exact ratios will vary based on the hardware used (see §Notes). Binary sizes might slightly differ too, due to new log messages added for better user experience.

### E2 — For FleetBench

Same metrics as E1, with vs. without Arith (~25 min for all six benchmarks). To run:

```bash
cd fleetbench-ae
scripts/measure.sh --sec=120 --fb-dir=built
# -> results/fleetbench_results.txt (perf)
#    results/fleetbench_sizes.txt   (size)
#    results/logs/*.out             (raw binary outputs)
```

Each benchmark reports time per operation; the overhead is the ratio of the instrumented to the baseline median ns/op.

**Expected Result:** Similar to the table below (subset of sub-benchmarks).

**Table: FleetBench runtime overhead and binary-size increase** with Arith vs. uninstrumented baseline. Measured on the reference host of Table 11. Results can vary depending on the underlying hardware. Only one sub-benchmark per benchmark family reported here. Not part of the main paper results.

| Benchmark  | Sub-benchmark        | Performance × | Binary-Size × |
|------------|----------------------|---------------|---------------|
| `hashing`  | Computecrc32c (hot)  | 1.42          | 1.11          |
| `proto`    | Arena                | 1.44          | 2.87          |
| `swissmap` | InsertHit (cold)     | 2.99          | 2.31          |
| `stl`      | Cord                 | 2.79          | 5.81          |
| `libc`     | Memcpy               | 2.21          | 1.09          |
| `tcmalloc` | empirical_driver     | 1.82          | 1.18          |

## Experiment customization

- **Pass selection:** `arith`, `mem`, `memdiv`, `br`, plus the combinations `arithmem`, `arithmemdiv`, `arithmemdivbr`.
- **Pass configuration parameters:** `make PASS=arith BLOCKSIZE=X INTERLEAVING=Y`, with `X`, `Y` ∈ {0, 1, 2, 4, 8}.
- **Run duration:** `scripts/measure.sh --sec=N` sets the per-binary wall-clock budget (default 120).
- **CPU set:** `measure.sh` automatically pins one worker per available CPU (§Notes); for a manual `cpu_check` run, restrict the workers with `-c<list>`.

## Notes

- **Measurement stability.** The exact ratios in the two tables depend on the underlying hardware, including core count, hyperthreading, and AVX support. Because the Table 6 servers have very high core counts, a host with at least 32 cores is recommended for comparable results (§Hardware dependencies). Ratios also vary run to run on the same hardware, from frequency scaling or co-location with other load; the default 120 sec runs average over short-term fluctuation, but some variation remains.
- **Thread placement.** cpu-check sizes its worker pool from `std::thread::hardware_concurrency()` and spawns one worker per logical CPU, independent of cgroup/affinity limits; on a restricted host this over-spawns and distorts the measurement. The scripts pass an explicit `-c` list so exactly one worker runs per available CPU.
- **Slow builds.** Some programs can take 1–2 hours to compile (e.g., stl-cord and proto from FleetBench). Pre-built versions of all evaluated binaries are provided inside `Binaries/`. Pre-built binaries are not guaranteed to run on any hardware.
