#!/bin/sh
# Enter the pinned, reproducible build environment for the ITHICA artifact.
#
# This drops you into a Guix shell that provides clang/LLVM 14.0.6 + lld and the
# other build tools declared in manifest.scm. Run `make` from inside this shell.
#
#   ./guix.sh
#   [env]$ make            # builds cpu_check instrumented with the ITHICA pass
#
# --network        : allow the Makefile to fetch pinned dependency sources.
# --emulate-fhs    : expose a standard /usr, /bin, /lib layout (needed by the
#                    dependency build systems and by clang's driver).
# --container      : isolate from the host so the build only sees the pinned
#                    toolchain (maximizes reproducibility).
#
# For a fully offline run (once all third_party/ sources are already present),
# drop --network:
#   guix shell --emulate-fhs --container -m manifest.scm
exec guix shell --network --emulate-fhs --container -m manifest.scm
