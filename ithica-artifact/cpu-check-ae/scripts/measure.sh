#!/usr/bin/env bash
# Reviewer: measure cpu_check PERFORMANCE and BINARY SIZE, and write a
# pipe-separated table plus the raw per-binary output.
#
#   scripts/measure.sh --cc-dir=DIR [--sec=120] [--out=DIR] [--in-docker] [--image=IMG]
#
#   --sec       seconds per binary (default 120)
#   --out        output directory (default ./results)
#   --cc-dir     REQUIRED -- which binaries to measure: Binaries (shipped
#                pre-built) or built (what you recompiled with build.sh)
#   --in-docker  run this same measurement INSIDE the pinned toolchain image,
#                bind-mounting the artifact dir (numbers match a host run)
#   --image      image for --in-docker (default ithica-guix-toolchain:latest)
#
# metric: successful test rounds completed in a fixed wall-clock budget.
#         overhead = CC rounds/sec / variant rounds/sec
set -uo pipefail

SECS=120; OUT="./results"; CC_DIR=""
IN_DOCKER=0; IMG="ithica-guix-toolchain:latest"; PASSTHRU=""
for a in "$@"; do case "$a" in
  --in-docker) IN_DOCKER=1 ;;
  --image=*)   IMG="${a#--image=}" ;;
  --sec=*)    SECS="${a#--sec=}"; PASSTHRU="$PASSTHRU $a" ;;
  --out=*)     OUT="${a#--out=}";  PASSTHRU="$PASSTHRU $a" ;;
  --cc-dir=*)  CC_DIR="${a#--cc-dir=}"; PASSTHRU="$PASSTHRU $a" ;;
  -h|--help)   sed -n '2,16p' "$0"; exit 0 ;;
  *) echo "unknown argument: $a (try --help)"; exit 2 ;;
esac; done

if [ -z "$CC_DIR" ]; then
  echo "ERROR: choose which binaries to measure with --cc-dir=DIR:"
  echo "   --cc-dir=Binaries   the shipped pre-built cpu_check binaries"
  echo "   --cc-dir=built      binaries you recompiled with scripts/build.sh"
  echo "example:  scripts/measure.sh --cc-dir=Binaries --sec=120"
  exit 2
fi

# --in-docker: re-run this same script (minus --in-docker) INSIDE the toolchain
# image, bind-mounting the artifact dir. cpu_check binaries are static, so the
# numbers match a host run; this just keeps the measurement inside Docker.
if [ "$IN_DOCKER" = 1 ]; then
  command -v docker >/dev/null || { echo "ERROR: docker not found"; exit 1; }
  docker image inspect "$IMG" >/dev/null 2>&1 || {
    echo "ERROR: image '$IMG' not loaded. Run scripts/setup.sh first."; exit 1; }
  ROOT="$(cd "$(dirname "$0")/.." && pwd)"
  echo ">> measuring inside $IMG (mount: $ROOT -> /ae)"
  exec docker run --rm -u "$(id -u):$(id -g)" -v "$ROOT":/ae -w /ae \
    --entrypoint bash "$IMG" \
    -c "export PATH=/usr/bin:\$PATH; exec scripts/measure.sh$PASSTHRU"
fi
mkdir -p "$OUT"

# CPUs this process may actually use: cpu_check sizes its worker pool from
# hardware_concurrency() (all logical CPUs) regardless of cgroup limits, which
# over-spawns in a restricted cpuset. Pin it explicitly.
CLIST="$(python3 -c "
line=[l for l in open('/proc/self/status') if l.startswith('Cpus_allowed_list')][0].split()[1]
out=[]
for p in line.split(','):
    a,b=(p.split('-')+[p])[:2]; out+=range(int(a),int(b)+1)
print(','.join(map(str,out)))" 2>/dev/null || echo "")"
NCPU=$(printf '%s' "$CLIST" | tr ',' '\n' | grep -c . 2>/dev/null || echo 0)

# CC/vanilla first (so it becomes the baseline), then the rest alphabetically.
# Deliberately awk-free: the pinned cpu-check toolchain image ships coreutils and
# grep but not awk, so measure.sh can also be run *inside* that image.
names=$(ls "$CC_DIR" 2>/dev/null | grep -E 'cpu_check$' | sed 's/_cpu_check$//')
if [ -z "$names" ]; then
  echo "ERROR: no *_cpu_check binaries in '$CC_DIR' (override with --cc-dir=DIR)"; exit 1
fi
# A subset without the baseline still measures fine, but the overhead ratio is
# only meaningful against CC. Warn rather than silently report the first binary
# as 1.00x.
if ! printf '%s\n' "$names" | grep -qxE 'CC|vanilla'; then
  echo "WARNING: no CC/vanilla baseline binary in '$CC_DIR'. The 'overhead' column"
  echo "         will be relative to the first binary, not the CC baseline --"
  echo "         build --pass=CC (or measure ./Binaries) for a true baseline."
fi
order=$( { printf '%s\n' "$names" | grep -xE 'CC|vanilla'
           printf '%s\n' "$names" | grep -xvE 'CC|vanilla' | sort; } )

T="$OUT/cpucheck_results.txt"
echo "# cpu_check: performance + binary size" > "$T"
echo "# host CPUs used: $NCPU   seconds per binary: $SECS" >> "$T"
echo "# overhead = CC rounds/sec / variant rounds/sec" >> "$T"
printf "%-26s|%14s|%12s|%12s|%10s\n" "binary" "size_bytes" "successes" "rounds/sec" "overhead" >> "$T"
echo "---------------------------|--------------|------------|------------|----------" >> "$T"

base_sps=""
mkdir -p "$OUT/logs"
for p in $order; do
  b="$CC_DIR/${p}_cpu_check"; [ -x "$b" ] || continue
  size=$(stat -Lc%s "$b")
  # save the full raw output per binary, then parse it (results AND output on disk)
  raw="$OUT/logs/${p}_cpu_check.out"
  "$b" ${CLIST:+-c$CLIST} -t"$SECS" > "$raw" 2>&1
  n=$(grep -oE '[0-9]+ SUCCESSES' "$raw" | tail -1 | grep -oE '[0-9]+'); n=${n:-0}
  sps=$(python3 -c "print(f'{$n/$SECS:.2f}')")
  [ -z "$base_sps" ] && base_sps="$sps"
  ov=$(python3 -c "b=$base_sps; x=$sps; print(f'{(b/x):.2f}x' if x>0 else 'n/a')")
  printf "%-26s|%14s|%12s|%12s|%10s\n" "$p" "$size" "$n" "$sps" "$ov" >> "$T"
  echo "   measured $p: $sps rounds/sec ($ov)"
done
echo ">> wrote $T"
echo ">> done. results in $OUT/"
