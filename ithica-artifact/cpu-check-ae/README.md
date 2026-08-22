# ITHICA × cpu\_check

Google's `cpu_check` CPU stress tester, instrumented with the ITHICA LLVM passes
(`CC` = the uninstrumented baseline). Requires an **x86-64 Linux** host with
**Docker** and **Bash**; the pre-built binaries are statically linked and can run
without Docker or rebuilding.

## Quick start

> The prebuilt `Binaries/` live in the **Zenodo** archive, not the GitHub mirror — download from Zenodo to run the commands below.

```bash
scripts/measure.sh --cc-dir=Binaries --sec=120   # measure the shipped pre-built binaries, write results/ (no build, no Docker)
scripts/measure.sh --cc-dir=built    --sec=120   # measure binaries you rebuilt with build.sh (see below)
scripts/setup.sh                   # load the pinned toolchain image  (only needed to rebuild)
scripts/build.sh --pass=arith      # (optional) rebuild a configuration from source
scripts/toy_overhead.sh            # (optional) instrument + run a small toy program
```

- **Passes:** `CC` (uninstrumented baseline), `arith`, `mem`, `memdiv`, `br`,
  `arithmem`, `arithmemdiv`, `arithmemdivbr`.
- **Pass parameters** (rebuild): `--blocksize=1|2|4|8|0`, `--interleaving=1|2|4|8|0`.
- **Results** are written under `results/`: a parseable table
  (`cpucheck_results.txt`) and the raw per-binary output (`logs/*.out`).

See the paper's **Artifact Appendix** for full instructions, hardware/software
requirements, and expected results.
