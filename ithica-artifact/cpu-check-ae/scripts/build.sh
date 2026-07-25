#!/usr/bin/env bash
# Reviewer: build cpu_check from source inside the pinned toolchain image,
# either uninstrumented (CC) or instrumented with one ITHICA pass.
# Requires only docker + bash.
#
#   scripts/build.sh --pass=<P> [--blocksize=B] [--interleaving=I] [--src=DIR] [--image=IMG]
#
#   --pass=CC              the original, uninstrumented cpu-check (baseline)
#   --pass=arith           Arith
#   --pass=mem | memdiv | br | arithmem | arithmemdiv | arithmemdivbr
#   --blocksize=1|2|4|8|0     (default 1)
#   --interleaving=1|2|4|8|0  (default 1)
#
# Result: <src>/<pass>_install_bs<B>_intr<I>/cpu-check/bin/cpu_check
# Each configuration installs under its own prefix, so building several passes
# does not overwrite earlier binaries.
#
# Takes ~20 min per configuration. The FIRST build additionally clones ~4 GB of
# pinned dependency sources (llvm-project, OpenSSL, Abseil, zlib) into
# third_party/; later builds reuse them.
set -euo pipefail

PASS=""; BS=1; INTR=1; SRC="."; IMG="ithica-guix-toolchain:latest"
for a in "$@"; do
  case "$a" in
    --pass=*)         PASS="${a#--pass=}" ;;
    --blocksize=*)    BS="${a#--blocksize=}" ;;
    --interleaving=*) INTR="${a#--interleaving=}" ;;
    --src=*)          SRC="${a#--src=}" ;;
    --image=*)        IMG="${a#--image=}" ;;
    -h|--help) sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument: $a (try --help)"; exit 2 ;;
  esac
done

if [ -z "$PASS" ]; then
  echo "ERROR: no --pass specified. Choose one of:"
  echo "  --pass=CC     the original, uninstrumented cpu-check (baseline)"
  echo "  --pass=arith | mem | memdiv | br | arithmem | arithmemdiv | arithmemdivbr"
  echo "Optional: --blocksize=1|2|4|8|0 (default 1)  --interleaving=1|2|4|8|0 (default 1)"
  exit 2
fi
SRC="$(cd "$SRC" && pwd)"

command -v docker >/dev/null || { echo "ERROR: docker not found"; exit 1; }
docker image inspect "$IMG" >/dev/null 2>&1 || {
  echo "ERROR: image '$IMG' not loaded. Run scripts/setup.sh first."; exit 1; }
[ -f "$SRC/Makefile" ] || { echo "ERROR: no Makefile in $SRC"; exit 1; }

echo ">> building cpu_check: PASS=$PASS BLOCKSIZE=$BS INTERLEAVING=$INTR"
echo ">> source: $SRC   image: $IMG"
START=$(date +%s)
# NOTE: do NOT pass -j to this top-level make. The `all` target is intentionally
# sequential -- each stage consumes the install prefix produced by the previous
# one (libc++ needs libllvmlibc.a; abseil/cpu_check need the libc++ overlay).
# Each stage already parallelises internally via the Makefile's JOBS variable.
docker run --rm --network=host \
  -v "$SRC:/work" -w /work \
  --entrypoint /bin/sh "$IMG" -c \
  "export PATH=/usr/bin:\$PATH && make PASS=$PASS BLOCKSIZE=$BS INTERLEAVING=$INTR"
END=$(date +%s)

BIN="$SRC/${PASS}_install_bs${BS}_intr${INTR}/cpu-check/bin/cpu_check"
echo ">> build time: $(( (END-START)/60 ))m$(( (END-START)%60 ))s"
if [ -x "$BIN" ]; then
  echo ">> binary: $BIN"
  echo ">> size:   $(stat -Lc%s "$BIN") bytes"
  # Collect the result under the name measure.sh expects, so a reviewer can
  # measure the from-source builds with:  scripts/measure.sh --cc-dir=built
  mkdir -p "$SRC/built"
  cp -f "$BIN" "$SRC/built/${PASS}_cpu_check"
  echo ">> collected: built/${PASS}_cpu_check  (measure with: scripts/measure.sh --cc-dir=built)"
else
  echo ">> WARNING: expected binary not found at $BIN"; exit 1
fi
