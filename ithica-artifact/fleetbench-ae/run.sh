#!/usr/bin/env bash
# Artifact Evaluation driver: build/run fleetbench benchmarks with or without
# the ITHICA instrumentation passes.
set -euo pipefail
FB=/opt/ithica/fleetbench
PASSES=/opt/ithica/passes

declare -A PASS_SO=(
  [arith]=ArithmeticPass.so [mem]=MemPass.so [memdiv]=MemDivPass.so
  [br]=BranchPass.so [arithmem]=ArithMemPass.so
  [arithmemdiv]=ArithMemDivPass.so [arithmemdivbr]=ArithMemDivBrPass.so )

# Short benchmark name -> canonical bazel target. Every entry below has been
# built and run, baseline and instrumented. (compression is intentionally absent:
# it requires OpenMP, which the pinned toolchain does not provide.)
declare -A TARGET=(
  [hashing]=fleetbench/hashing:hashing_benchmark
  [proto]=fleetbench/proto:proto_benchmark
  [swissmap]=fleetbench/swissmap:swissmap_benchmark
  [stl]=fleetbench/stl:cord_benchmark
  [libc]=fleetbench/libc:mem_benchmark
  [tcmalloc]=fleetbench/tcmalloc:empirical_driver )

usage() {
  cat <<EOF
ITHICA x fleetbench -- Artifact Evaluation driver

  run.sh list
  run.sh build <bench> [--pass=P | --nopass]   (default: --pass=arith)
  run.sh run   <bench> [--pass=P | --nopass]   build then run the benchmark
  run.sh demo                                  hashing: baseline vs arith, side by side
  run.sh all   [--pass=P | --nopass]           build every benchmark

Passes:     ${!PASS_SO[@]}
Benchmarks: ${!TARGET[@]}

A "pass" build compiles the benchmark with the LLVM instrumentation loaded
(redundant-computation checks); "nopass" is the identical benchmark without it.
EOF
}

resolve() { echo "${TARGET[$1]:-$1}"; }   # accept a short name or a raw bazel target

parse_mode() { # sets MODE (pass|nopass) and PASS from the remaining args
  MODE=pass; PASS=arith
  for a in "$@"; do
    case "$a" in
      --nopass) MODE=nopass ;;
      --pass=*) MODE=pass; PASS="${a#--pass=}" ;;
    esac
  done
  [ "$MODE" = nopass ] || [ -n "${PASS_SO[$PASS]:-}" ] || { echo "unknown pass: $PASS"; exit 2; }
}

do_build() { # <bench> <mode> <pass>
  local tgt; tgt="$(resolve "$1")"
  cd "$FB"
  if [ "$2" = pass ]; then
    ln -sf "${PASS_SO[$3]}" "$PASSES/pass.so"
    echo ">> building $tgt WITH pass=$3"
    bazel build --spawn_strategy=local --config=clang-14 --config=opt --config=pass "$tgt"
  else
    echo ">> building $tgt WITHOUT pass (baseline)"
    bazel build --spawn_strategy=local --config=clang-14 --config=opt "$tgt"
  fi
}

bin_path() { cd "$FB"; echo "$FB/bazel-bin/$(resolve "$1" | sed 's/:/\//')"; }

cmd="${1:-list}"; shift || true
case "$cmd" in
  list|"") usage ;;
  build)   b="$1"; shift; parse_mode "$@"; do_build "$b" "$MODE" "$PASS" ;;
  run)     b="$1"; shift; parse_mode "$@"
           # everything that is not a mode flag is passed through to the benchmark
           BARGS=(); for a in "$@"; do case "$a" in --nopass|--pass=*) ;; *) BARGS+=("$a");; esac; done
           [ ${#BARGS[@]} -eq 0 ] && BARGS=(--benchmark_min_time=1s)   # default duration
           do_build "$b" "$MODE" "$PASS"
           "$(bin_path "$b")" "${BARGS[@]}" || true ;;
  demo)    do_build hashing nopass arith
           echo; echo "=== baseline built OK ==="; echo
           do_build hashing pass   arith
           echo; echo "=== instrumented (arith) built OK ===" ;;
  all)     parse_mode "$@"; for b in "${!TARGET[@]}"; do do_build "$b" "$MODE" "$PASS"; done ;;
  *)       usage; exit 2 ;;
esac
