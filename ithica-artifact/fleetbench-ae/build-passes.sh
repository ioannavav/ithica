#!/usr/bin/env bash
# Build the ITHICA LLVM pass plugins (.so) and the tiny runtime helpers from
# source, using the image's clang-14 / llvm-14. Run once at image build time.
set -euo pipefail
SRC=/opt/ithica/passes-src
OUT=/opt/ithica/passes
mkdir -p "$OUT"

# Pass build knobs (defaults match the paper's main configuration).
BLOCKSIZE="${BLOCKSIZE:-1}"
INTERLEAVING="${INTERLEAVING:-1}"
CXXFLAGS="$(llvm-config-14 --cxxflags)"

build_pass() { # <source.cpp> <output.so>
  echo "  [pass] $2"
  clang++-14 -shared -fPIC -o "$OUT/$2" \
    -DBLOCKSIZE="$BLOCKSIZE" -DINTERLEAVING="$INTERLEAVING" -DLIBRARYNAME='"fleetbench"' \
    "$SRC/$1" $CXXFLAGS
}

build_pass ArithmeticPass.cpp    ArithmeticPass.so
build_pass MemPass.cpp           MemPass.so
build_pass MemDivPass.cpp        MemDivPass.so
build_pass BranchPass.cpp        BranchPass.so
build_pass ArithMemPass.cpp      ArithMemPass.so
build_pass ArithMemDivPass.cpp   ArithMemDivPass.so
build_pass ArithMemDivBrPass.cpp ArithMemDivBrPass.so

echo "  [runtime] libpassmmap, libpassInstrTracker"
clang-14 -fPIC -Wno-format-security -c "$SRC/mmap_file.c"             -o "$OUT/libpassmmap"
clang-14 -fPIC -Wno-format-security -c "$SRC/instr_tracker_runtime.c" -o "$OUT/libpassInstrTracker"

# The BUILD files load /opt/ithica/passes/pass.so; point it at the default pass.
ln -sf ArithmeticPass.so "$OUT/pass.so"
echo "Built passes in $OUT (default pass.so -> ArithmeticPass.so)"
