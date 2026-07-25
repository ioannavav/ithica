#!/usr/bin/env bash
# Reviewer: build one FleetBench benchmark inside the image, with or without an
# ITHICA pass, and copy the resulting self-contained bundle (binary + runfiles)
# to ./built/ so you can measure YOUR OWN build instead of the shipped ones:
#     scripts/build.sh --bench=hashing --nopass                    # your baseline
#     scripts/build.sh --bench=hashing --pass=arith                # your instrumented
#     scripts/measure.sh --fb-dir=built                      # measure them
# (measure.sh needs both <bench>_baseline and <bench>_arith to report overhead.)
#
# This uses the image's existing `build` step and then `docker cp`s the bundle
# out -- no image rebuild, no special image support required. bazel's runfiles
# contain symlinks that point back inside the container, so the copy is
# dereferenced (cp -L / -rL) before it leaves the container; the host bundle is
# self-contained. Requires only docker + bash, and the image from scripts/setup.sh.
#
#   scripts/build.sh --bench=<B> [--pass=<P> | --nopass] [--image=IMG] [--out=DIR]
#
#   --bench=hashing|proto|swissmap|stl|libc|tcmalloc
#   --pass=arith|mem|memdiv|br|arithmem|arithmemdiv|arithmemdivbr   (default arith)
#   --nopass                                          uninstrumented baseline
#   --out=DIR                                          host dir for the bundle (default ./built)
#
# (compression is intentionally unavailable: it requires OpenMP, which the
#  pinned toolchain does not provide.)
set -euo pipefail
BENCH=""; MODE="--pass=arith"; IMG="ithica-fleetbench"; OUT="built"
for a in "$@"; do case "$a" in
  --bench=*)  BENCH="${a#--bench=}" ;;
  --pass=*)   MODE="$a" ;;
  --nopass)   MODE="--nopass" ;;
  --image=*)  IMG="${a#--image=}" ;;
  --out=*)    OUT="${a#--out=}" ;;
  -h|--help)  sed -n '2,24p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
  *) echo "unknown argument: $a (try --help)"; exit 2 ;;
esac; done

command -v docker >/dev/null || { echo "ERROR: docker not found"; exit 1; }
docker image inspect "$IMG" >/dev/null 2>&1 || {
  echo "ERROR: image '$IMG' not found. Run scripts/setup.sh first."; exit 1; }
[ -n "$BENCH" ] || { echo "ERROR: --bench required (hashing|proto|swissmap|stl|libc|tcmalloc)"; exit 2; }

# bench -> path of the built binary under bazel-bin/fleetbench/ (dir/target).
# (Note tcmalloc's target is empirical_driver, not *_benchmark; stl's is cord_benchmark.)
case "$BENCH" in
  hashing)  REL=hashing/hashing_benchmark ;;
  proto)    REL=proto/proto_benchmark ;;
  swissmap) REL=swissmap/swissmap_benchmark ;;
  stl)      REL=stl/cord_benchmark ;;
  libc)     REL=libc/mem_benchmark ;;
  tcmalloc) REL=tcmalloc/empirical_driver ;;
  *) echo "ERROR: unknown --bench=$BENCH (hashing|proto|swissmap|stl|libc|tcmalloc)"; exit 2 ;;
esac

mkdir -p "$OUT"; OUT="$(cd "$OUT" && pwd)"
LABEL=baseline; [ "$MODE" = "--nopass" ] || LABEL="${MODE#--pass=}"
echo ">> building $BENCH ($MODE) in $IMG; bundle -> $OUT/${BENCH}_${LABEL}/"

# Build in a NAMED (non-rm) container so the freshly built binary survives, then
# copy it to the host with `docker cp` -- files land owned by the invoking user,
# not root. The container stages a dereferenced copy under /out first so the
# bundle carries no symlinks back into the (soon-removed) container.
CID="ithica_fb_build_$$"
cleanup() { docker rm -f "$CID" >/dev/null 2>&1 || true; }
trap cleanup EXIT

docker run --name "$CID" --entrypoint bash "$IMG" -c "
  set -e
  /opt/ithica/run.sh build $BENCH $MODE
  src=/opt/ithica/fleetbench/bazel-bin/fleetbench/$REL
  [ -e \"\$src\" ] || { echo \"ERROR: built binary not found at \$src\"; exit 1; }
  dest=/out/${BENCH}_${LABEL}
  rm -rf \"\$dest\"; mkdir -p \"\$dest\"
  cp -L  \"\$src\"          \"\$dest/\"
  cp -rL \"\$src\".runfiles \"\$dest/\$(basename \"\$src\").runfiles\"
" || { echo "ERROR: build/stage failed"; exit 1; }

docker cp "$CID:/out/${BENCH}_${LABEL}" "$OUT/"
echo ">> extracted: $OUT/${BENCH}_${LABEL}/"
ls -1 "$OUT/${BENCH}_${LABEL}" | sed 's/^/     /'
echo ">> measure with: scripts/measure.sh --fb-dir=$(basename "$OUT")"
