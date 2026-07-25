#!/usr/bin/env bash
# Reviewer setup: build the FleetBench image. Requires only docker + bash.
#   scripts/setup.sh [context_dir] [image_tag]
set -euo pipefail
CTX="${1:-.}"; TAG="${2:-ithica-fleetbench}"
command -v docker >/dev/null || { echo "ERROR: docker not found"; exit 1; }
docker info >/dev/null 2>&1 || { echo "ERROR: cannot talk to the docker daemon (is it running? are you in the 'docker' group?)"; exit 1; }
echo ">> building $TAG from $CTX (needs network; one-time)"
docker build -t "$TAG" "$CTX"
echo ">> done. image:"; docker images "$TAG" --format '   {{.Repository}}:{{.Tag}}  {{.Size}}'
