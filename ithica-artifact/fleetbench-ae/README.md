# ITHICA × FleetBench

Google's FleetBench benchmarks compiled with and without the ITHICA `Arith`
pass. Requires an **x86-64 Linux** host with **Docker** and **Bash**; the
pre-built benchmark bundles are statically linked and run without Docker (from
inside each bundle directory).

## Quick start

```bash
scripts/measure.sh --fb-dir=Binaries --sec=120   # measure the shipped pre-built bundles, write results/ (no build)
scripts/measure.sh --fb-dir=built    --sec=120   # measure bundles you rebuilt with build.sh (see below)
scripts/setup.sh                               # build the toolchain image      (only needed to rebuild)
scripts/build.sh --bench=hashing --pass=arith  # (optional) rebuild one benchmark, instrumented
scripts/build.sh --bench=hashing --nopass      # (optional) rebuild one benchmark, baseline
```

- **Benchmarks:** `hashing`, `proto`, `swissmap`, `stl`, `libc`, `tcmalloc`
  (`compression` is excluded — it needs OpenMP, absent from the pinned toolchain).
- **Results** are written under `results/`: performance
  (`fleetbench_results.txt`), binary size (`fleetbench_sizes.txt`), and the raw
  per-benchmark output (`logs/*.out`).

See the paper's **Artifact Appendix** for full instructions, hardware/software
requirements, and expected results.
