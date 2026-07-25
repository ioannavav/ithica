#!/usr/bin/env bash
# Reviewer: measure FleetBench PERFORMANCE (median ns/op) and BINARY SIZE, and
# write pipe-separated tables plus the raw per-benchmark output.
#
#   scripts/measure.sh --fb-dir=DIR [--sec=120] [--out=DIR] [--in-docker] [--image=IMG]
#
#   --sec       ~seconds of wall time budgeted per benchmark (default 120)
#   --out        output directory (default ./results)
#   --fb-dir     REQUIRED -- which bundles to measure: prebuilt (shipped
#                pre-built) or built (what you recompiled with build.sh)
#   --in-docker  run this same measurement INSIDE the FleetBench image,
#                bind-mounting the artifact dir (numbers match a host run)
#   --image      image for --in-docker (default ithica-fleetbench:latest)
#
# metric: median ns per operation (google/benchmark).
#         overhead = arith ns / baseline ns
set -uo pipefail

SECS=120; OUT="./results"; FB_DIR=""
IN_DOCKER=0; IMG="ithica-fleetbench:latest"; PASSTHRU=""
for a in "$@"; do case "$a" in
  --in-docker) IN_DOCKER=1 ;;
  --image=*)   IMG="${a#--image=}" ;;
  --sec=*)    SECS="${a#--sec=}"; PASSTHRU="$PASSTHRU $a" ;;
  --out=*)     OUT="${a#--out=}";  PASSTHRU="$PASSTHRU $a" ;;
  --fb-dir=*)  FB_DIR="${a#--fb-dir=}"; PASSTHRU="$PASSTHRU $a" ;;
  -h|--help)   sed -n '2,16p' "$0"; exit 0 ;;
  *) echo "unknown argument: $a (try --help)"; exit 2 ;;
esac; done

if [ -z "$FB_DIR" ]; then
  echo "ERROR: choose which bundles to measure with --fb-dir=DIR:"
  echo "   --fb-dir=prebuilt   the shipped pre-built FleetBench bundles"
  echo "   --fb-dir=built      bundles you recompiled with scripts/build.sh"
  echo "example:  scripts/measure.sh --fb-dir=prebuilt --sec=120"
  exit 2
fi

# --in-docker: re-run this same script (minus --in-docker) INSIDE the FleetBench
# image, bind-mounting the artifact dir. The bundles are static, so the numbers
# match a host run; this just keeps the measurement inside Docker.
if [ "$IN_DOCKER" = 1 ]; then
  command -v docker >/dev/null || { echo "ERROR: docker not found"; exit 1; }
  docker image inspect "$IMG" >/dev/null 2>&1 || {
    echo "ERROR: image '$IMG' not found. Run scripts/setup.sh first."; exit 1; }
  ROOT="$(cd "$(dirname "$0")/.." && pwd)"
  echo ">> measuring inside $IMG (mount: $ROOT -> /ae)"
  exec docker run --rm -u "$(id -u):$(id -g)" -v "$ROOT":/ae -w /ae \
    --entrypoint bash "$IMG" -c "exec scripts/measure.sh$PASSTHRU"
fi
mkdir -p "$OUT"

# Overhead = arith / baseline, so each family needs BOTH <fam>_baseline and
# <fam>_arith. Find complete pairs; also note families with only one half so we
# can tell the reviewer exactly which build to run.
have=""; partial=""
for fam in hashing proto swissmap stl libc tcmalloc; do
  if [ -d "$FB_DIR/${fam}_baseline" ] && [ -d "$FB_DIR/${fam}_arith" ]; then
    have=1
  elif [ -d "$FB_DIR/${fam}_baseline" ] || [ -d "$FB_DIR/${fam}_arith" ]; then
    partial="$partial $fam"
  fi
done
if [ -z "$have" ]; then
  echo "ERROR: no complete family in '$FB_DIR' -- overhead needs BOTH halves"
  echo "       (<fam>_baseline and <fam>_arith)."
  if [ -n "$partial" ]; then
    for fam in $partial; do
      if [ -d "$FB_DIR/${fam}_arith" ]; then
        echo "       '$fam' has only the instrumented half; also build its baseline:"
        echo "           scripts/build.sh --bench=$fam --nopass"
      else
        echo "       '$fam' has only the baseline half; also build the instrumented one:"
        echo "           scripts/build.sh --bench=$fam --pass=arith"
      fi
    done
  else
    echo "       Nothing found in '$FB_DIR' (override with --fb-dir=DIR). Build a family, e.g.:"
    echo "           scripts/build.sh --bench=hashing --nopass"
    echo "           scripts/build.sh --bench=hashing --pass=arith"
  fi
  exit 1
fi

T="$OUT/fleetbench_results.txt"
echo "# FleetBench: performance (median ns/op) + binary size" > "$T"
echo "# overhead = arith ns / baseline ns" >> "$T"
printf "%-12s|%-44s|%11s|%7s|%11s|%7s|%9s\n" "family" "benchmark" "base_ns" "base_cv" "arith_ns" "ar_cv" "overhead" >> "$T"
echo "------------|--------------------------------------------|-----------|-------|-----------|-------|---------" >> "$T"
S="$OUT/fleetbench_sizes.txt"
printf "%-12s|%14s|%14s|%10s\n" "family" "baseline_bytes" "arith_bytes" "growth" > "$S"
echo "------------|--------------|--------------|----------" >> "$S"

# Budget ~SECS of wall time PER BINARY, spent as repetitions rather than one
# stretched run: repetitions give independent samples, so we get a median and
# a stddev instead of a single number. Rep count is calibrated per binary,
# since sub-benchmark counts differ (hashing 6, libc 5, swissmap 2, others 1).
medians() { # <bundle dir>   -> "name,median_ns,stddev_ns" lines
  local d="$1" bin; bin=$(ls "$d" 2>/dev/null | grep -v runfiles | head -1); [ -n "$bin" ] || return
  local t0 t1 dur reps
  t0=$(date +%s.%N); ( cd "$d" && ./"$bin" >/dev/null 2>&1 ); t1=$(date +%s.%N)
  dur=$(python3 -c "print(max(0.05, $t1-$t0))")
  reps=$(python3 -c "print(max(3, min(400, round($SECS/$dur))))")
  echo "      $(basename "$d"): 1 rep=${dur}s -> ${reps} reps (~$(python3 -c "print(round($reps*$dur))")s)" >&2
  mkdir -p "$OUT/logs"
  local raw="$OUT/logs/$(basename "$d").out"
  ( cd "$d" && ./"$bin" --benchmark_repetitions="$reps" \
      --benchmark_report_aggregates_only=true 2>/dev/null ) | tee "$raw" \
    | python3 -c "
import sys
med, sd = {}, {}
for ln in sys.stdin:
    ln = ln.rstrip()
    for tag, tgt in (('_median', med), ('_stddev', sd)):
        i = ln.find(tag)
        if i > 0:
            name = ln[:i]; rest = ln[i+len(tag):].split()
            for tok in rest:
                try: tgt[name] = float(tok); break
                except ValueError: pass
            break
for n, v in med.items():
    print(f'{n},{v},{sd.get(n, 0.0)}')
"
}
for fam in hashing proto swissmap stl libc tcmalloc; do
  bd="$FB_DIR/${fam}_baseline" ad="$FB_DIR/${fam}_arith"
  [ -d "$bd" ] && [ -d "$ad" ] || continue
  medians "$bd" > /tmp/m_b_$fam.txt; medians "$ad" > /tmp/m_a_$fam.txt
  python3 - "$fam" "$T" <<'PY'
import sys
fam,T=sys.argv[1],sys.argv[2]
def load(p):
    d={}
    try:
        for ln in open(p):
            ln=ln.strip()
            parts=ln.rsplit(',',2)          # name , median , stddev
            if len(parts)==3:
                try: d[parts[0]]=(float(parts[1]), float(parts[2]))
                except ValueError: pass
    except FileNotFoundError: pass
    return d
b=load(f'/tmp/m_b_{fam}.txt'); a=load(f'/tmp/m_a_{fam}.txt')
with open(T,'a') as f:
    for n in b:
        if n in a and b[n][0]>0:
            bm,bs=b[n]; am,asd=a[n]
            # stddev as % of median, so noisy rows are visible at a glance
            bcv = 100*bs/bm if bm else 0
            acv = 100*asd/am if am else 0
            f.write("%-12s|%-44s|%11.3f|%6.1f%%|%11.3f|%6.1f%%|%8.2fx\n"
                    %(fam,n[:44],bm,bcv,am,acv,am/bm))
PY
  sb=$(stat -Lc%s "$bd"/$(ls "$bd"|grep -v runfiles|head -1) 2>/dev/null)
  sa=$(stat -Lc%s "$ad"/$(ls "$ad"|grep -v runfiles|head -1) 2>/dev/null)
  [ -n "$sb" ] && [ -n "$sa" ] && \
    printf "%-12s|%14s|%14s|%9.2fx\n" "$fam" "$sb" "$sa" \
      "$(python3 -c "print(f'{$sa/$sb:.2f}')")" >> "$S"
  echo "   measured $fam"
done
echo ">> wrote $T and $S"
echo ">> done. results in $OUT/"
