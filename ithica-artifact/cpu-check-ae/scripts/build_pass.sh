#!/usr/bin/env bash
# Reviewer: compile a single ITHICA LLVM pass plugin (.so) from source -- fast
# (~10s), without building cpu_check or FleetBench. Runs in the pinned toolchain
# image (docker + bash only). Mount-free: the source is streamed in and the .so
# streamed back out, so it works from any directory (no bind-mount needed).
#
#   scripts/build_pass.sh <pass> [--blocksize=B] [--interleaving=I] [--libname=NAME]
#                          [--out=DIR] [--image=IMG]
#
#   <pass>            arith | mem | memdiv | br | arithmem | arithmemdiv | arithmemdivbr
#   --blocksize=B     1|2|4|8|0  (default 1)  -- how many checks per chain
#   --interleaving=I  1|2|4|8|0  (default 1)  -- where duplicate instrs are placed
#   --libname=NAME    label printed when a corruption is detected (default ithica)
#   --out=DIR         where to write the .so (default ./passes)
set -euo pipefail

PASS=""; BS=1; INTR=1; LIBNAME=ithica; OUT="passes"; IMG="ithica-guix-toolchain:latest"
for a in "$@"; do case "$a" in
  --blocksize=*)    BS="${a#--blocksize=}" ;;
  --interleaving=*) INTR="${a#--interleaving=}" ;;
  --libname=*)      LIBNAME="${a#--libname=}" ;;
  --out=*)          OUT="${a#--out=}" ;;
  --image=*)        IMG="${a#--image=}" ;;
  -h|--help)        sed -n '2,14p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
  --*)              echo "unknown option: $a (try --help)"; exit 2 ;;
  *)                PASS="$a" ;;
esac; done

PASSES="arith mem memdiv br arithmem arithmemdiv arithmemdivbr"
case "$PASS" in
  arith)         CPP=ArithmeticPass.cpp ;;
  mem)           CPP=MemPass.cpp ;;
  memdiv)        CPP=MemDivPass.cpp ;;
  br)            CPP=BranchPass.cpp ;;
  arithmem)      CPP=ArithMemPass.cpp ;;
  arithmemdiv)   CPP=ArithMemDivPass.cpp ;;
  arithmemdivbr) CPP=ArithMemDivBrPass.cpp ;;
  "") echo "ERROR: no pass given. Choose one of: $PASSES"; exit 2 ;;
  *)  echo "ERROR: unknown pass '$PASS'. Choose one of: $PASSES"; exit 2 ;;
esac
case " 0 1 2 4 8 " in *" $BS "*) ;;   *) echo "ERROR: --blocksize must be 0,1,2,4,8"; exit 2 ;; esac
case " 0 1 2 4 8 " in *" $INTR "*) ;; *) echo "ERROR: --interleaving must be 0,1,2,4,8"; exit 2 ;; esac

ROOT="$(cd "$(dirname "$0")/.." && pwd)"      # the cpu-check-ae directory
SRC="$ROOT/$CPP"
[ -f "$SRC" ] || { echo "ERROR: pass source not found: $SRC"; exit 1; }
command -v docker >/dev/null || { echo "ERROR: docker not found"; exit 1; }
docker image inspect "$IMG" >/dev/null 2>&1 || {
  echo "ERROR: image '$IMG' not loaded. Run scripts/setup.sh first."; exit 1; }

case "$OUT" in /*) : ;; *) OUT="$ROOT/$OUT" ;; esac    # resolve relative --out under the artifact
mkdir -p "$OUT"
SO="${CPP%.cpp}.so"; DEST="$OUT/$SO"

echo ">> compiling '$PASS' pass ($CPP, blocksize=$BS interleaving=$INTR) in $IMG"
# Mount-free: feed the single .cpp on stdin, compile inside the image, and send
# the resulting .so back on stdout (compile diagnostics go to stderr). No bind
# mount, so this runs even where docker cannot mount the source path.
rc=0
docker run -i --rm --network=host \
  -e BS="$BS" -e INTR="$INTR" -e LIBNAME="$LIBNAME" \
  --entrypoint bash "$IMG" -c '
    set -e
    cat > /tmp/pass.cpp
    export PATH=/usr/bin:$PATH
    clang++ -shared -fPIC -w -o /tmp/out.so \
      -DBLOCKSIZE="$BS" -DINTERLEAVING="$INTR" -DLIBRARYNAME="\"$LIBNAME\"" \
      /tmp/pass.cpp $(llvm-config --cxxflags) 1>&2
    cat /tmp/out.so
  ' < "$SRC" > "$DEST" || rc=$?
if [ "$rc" -ne 0 ] || [ ! -s "$DEST" ]; then
  echo "ERROR: failed to build the '$PASS' pass (see messages above)"; rm -f "$DEST"; exit 1
fi

REL="${DEST#"$ROOT"/}"
cat <<EOF

✓ Successfully built the '$PASS' pass
    plugin:  $DEST
    load it into clang-14 with:
      -flegacy-pass-manager -Xclang -load -Xclang $REL

Try it on a small toy C++ program (compiles a toy .cpp with and without the
pass, then reports the runtime overhead):
    scripts/toy_overhead.sh --pass=$PASS

Apply it to the paper's programs:
    cpu-check:   scripts/build.sh --pass=$PASS
    FleetBench:  cd ../fleetbench-ae && scripts/build.sh --bench=hashing --pass=$PASS
EOF
