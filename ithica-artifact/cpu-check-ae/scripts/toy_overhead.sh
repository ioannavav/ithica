#!/usr/bin/env bash
# Quick try-out: compile a small toy program with and without an ITHICA pass and
# report the runtime overhead. Runs in the pinned toolchain image (docker+bash);
# sources are streamed in via docker cp (no bind-mount), so it works anywhere.
#
#   scripts/toy_overhead.sh [--pass=P] [--blocksize=B] [--interleaving=I] [--image=IMG]
#
#   --pass  arith | mem | memdiv | br | arithmem | arithmemdiv | arithmemdivbr  (default arith)
#
# Not a paper experiment: shows the pass applies to arbitrary code and gives a
# ~1 minute sanity check that the toolchain image works before a full build.
set -euo pipefail
PASS=arith; BS=1; INTR=1; IMG="ithica-guix-toolchain:latest"
for a in "$@"; do case "$a" in
  --pass=*)         PASS="${a#--pass=}" ;;
  --blocksize=*)    BS="${a#--blocksize=}" ;;
  --interleaving=*) INTR="${a#--interleaving=}" ;;
  --image=*)        IMG="${a#--image=}" ;;
  -h|--help)        sed -n '2,11p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
  *) echo "unknown argument: $a (try --help)"; exit 2 ;;
esac; done

case "$PASS" in
  arith) CPP=ArithmeticPass.cpp ;;  mem) CPP=MemPass.cpp ;;  memdiv) CPP=MemDivPass.cpp ;;
  br) CPP=BranchPass.cpp ;;         arithmem) CPP=ArithMemPass.cpp ;;
  arithmemdiv) CPP=ArithMemDivPass.cpp ;;  arithmemdivbr) CPP=ArithMemDivBrPass.cpp ;;
  *) echo "ERROR: unknown pass '$PASS' (arith mem memdiv br arithmem arithmemdiv arithmemdivbr)"; exit 2 ;;
esac

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
command -v docker >/dev/null || { echo "ERROR: docker not found"; exit 1; }
docker image inspect "$IMG" >/dev/null 2>&1 || {
  echo "ERROR: image '$IMG' not loaded. Run scripts/setup.sh first."; exit 1; }
for f in "$CPP" mmap_file.c toy_overhead/toy_program.cpp; do
  [ -f "$ROOT/$f" ] || { echo "ERROR: missing source $ROOT/$f"; exit 1; }
done

echo ">> toy overhead for the '$PASS' pass (compiling in $IMG)"
# Mount-free: keep a container alive, docker cp the sources in, compile+run+time
# inside, then remove it. No bind-mount, so this works even where docker cannot
# mount the source path.
CID="ithica_toy_$$"
cleanup() { docker rm -f "$CID" >/dev/null 2>&1 || true; }
trap cleanup EXIT
docker run -d --name "$CID" --network=host --entrypoint sleep "$IMG" 600 >/dev/null
docker cp "$ROOT/$CPP"                      "$CID:/tmp/" >/dev/null
docker cp "$ROOT/mmap_file.c"               "$CID:/tmp/" >/dev/null
docker cp "$ROOT/toy_overhead/toy_program.cpp" "$CID:/tmp/" >/dev/null
docker exec -e CPP="$CPP" -e BS="$BS" -e INTR="$INTR" "$CID" bash -c '
  set -e
  export PATH=/usr/bin:$PATH
  cd /tmp
  echo "[1/3] runtime helper + pass plugin ($CPP)"
  clang mmap_file.c -fPIC -Wno-format-security -c -o libpassmmap
  clang++ -shared -fPIC -w -o pass.so \
    -DBLOCKSIZE="$BS" -DINTERLEAVING="$INTR" -DLIBRARYNAME="\"toy\"" \
    "$CPP" $(llvm-config --cxxflags)
  echo "[2/3] compile toy_program.cpp: baseline + instrumented (-O2 -static, scalar)"
  NOVEC="-fno-vectorize -fno-slp-vectorize"
  clang++ -O2 -static $NOVEC toy_program.cpp libpassmmap -o base
  # -load needs a path with a slash (an absolute path here); a bare name would be
  # searched on the library path instead of found in the cwd. Keep the pass'\''s
  # per-function chatter out of the way, but surface real errors.
  if ! clang++ -O2 -static $NOVEC -flegacy-pass-manager -Xclang -load -Xclang /tmp/pass.so \
       toy_program.cpp libpassmmap -o instr 2>/tmp/instr.err; then
    echo "ERROR: instrumented compile failed:"; sed -n "1,15p" /tmp/instr.err; exit 1
  fi
  echo "[3/3] timing (average of 3)"
  avg() { sum=0; for r in 1 2 3; do s=$(date +%s.%N); ./"$1" >/dev/null; e=$(date +%s.%N);
             sum=$(python3 -c "print($sum + ($e - $s))"); done
           python3 -c "print($sum / 3)"; }
  BB=$(avg base); BA=$(avg instr)
  echo "-------------------------------------------"
  python3 -c "print(f\"baseline : {$BB:.3f} s\"); print(f\"$CPP : {$BA:.3f} s\"); print(f\"overhead : {$BA/$BB:.2f}x\")"
  echo "-------------------------------------------"
'
