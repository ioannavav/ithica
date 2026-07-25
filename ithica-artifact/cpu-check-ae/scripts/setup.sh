#!/usr/bin/env bash
# Reviewer setup: load the cpu-check toolchain image. Requires only docker + bash.
#
# The cpu-check toolchain is shipped as a pre-packed Docker image rather than a
# Dockerfile, because it is exported from a pinned GNU Guix environment
# (clang/LLVM/lld 14.0.6) -- the exact toolchain the paper's binaries were built
# with. Reviewers therefore do NOT need Guix installed.
#
#   scripts/setup.sh [image_tarball] [expected_sha256_file]
set -euo pipefail
TARBALL="${1:-ithica-cpucheck-toolchain.tar.gz}"
SHAFILE="${2:-${TARBALL}.sha256}"

command -v docker >/dev/null || { echo "ERROR: docker not found"; exit 1; }
docker info >/dev/null 2>&1 || {
  echo "ERROR: cannot reach the docker daemon."
  echo "       Start it, or add yourself to the 'docker' group (then re-login)."; exit 1; }
[ -f "$TARBALL" ] || { echo "ERROR: image tarball not found: $TARBALL"; exit 1; }

if [ -f "$SHAFILE" ]; then
  echo ">> verifying checksum"
  # The .sha256 file records a bare filename, so verify from the tarball's own
  # directory rather than the caller's cwd.
  ( cd "$(dirname "$TARBALL")" && sha256sum -c "$(basename "$SHAFILE")" ) \
    || { echo "ERROR: checksum mismatch -- re-download the tarball."; exit 1; }
else
  echo ">> (no checksum file next to the tarball; skipping verification)"
fi

echo ">> loading image (this unpacks ~2 GB; takes a few minutes)"
docker load < "$TARBALL"

echo ">> loaded images:"
docker images --format '   {{.Repository}}:{{.Tag}}  {{.Size}}' | grep -i ithica || true
echo ">> sanity check: compiler version inside the image"
IMG=$(docker images --format '{{.Repository}}:{{.Tag}}' | grep -i 'cpucheck\|guix-toolchain' | head -1)
docker run --rm --entrypoint /bin/sh "$IMG" -c 'clang --version | head -1'
echo ">> ready. Build cpu_check with:  scripts/build.sh --pass=<P>"
