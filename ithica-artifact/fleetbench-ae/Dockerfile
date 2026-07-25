# ITHICA x fleetbench -- Artifact Evaluation image.
# Rebuilds the fleetbench benchmarks with and without the ITHICA LLVM
# instrumentation passes, using a pinned clang-14 toolchain.
# Ubuntu 24.04 is REQUIRED, not 22.04: its apt clang-14 is 1:14.0.6-19build4,
# matching the clang 14.0.6 the paper's binaries were built with. Ubuntu 22.04
# ships clang-14 at 14.0.0 -- a different compiler build.
FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
      clang-14 lld-14 llvm-14-dev libclang-14-dev \
      build-essential cmake ninja-build git python3 python3-dev \
      unzip zip wget ca-certificates openjdk-17-jdk-headless \
    && rm -rf /var/lib/apt/lists/*

# The exact bazel version the benchmarks were built with (7.3.1). Baked in so the
# WORKSPACE dependency graph resolves identically; newer bazel drops WORKSPACE
# support and mis-resolves the transitive toolchain deps.
COPY context/bazel-7.3.1 /usr/local/bin/bazel
RUN chmod +x /usr/local/bin/bazel

# Pass sources + the fleetbench working tree (pinned; not re-cloned).
COPY context/passes-src /opt/ithica/passes-src
COPY context/fleetbench /opt/ithica/fleetbench
COPY build-passes.sh /opt/ithica/

# Compile the passes into /opt/ithica/passes at image build time.
RUN chmod +x /opt/ithica/build-passes.sh && /opt/ithica/build-passes.sh

# Warm the dependency graph at image-build time: fetch + build the baseline of
# the demo benchmark. This bakes the pinned external deps into the image so that
# reviewer `docker run` invocations build offline and fast (no 3GB re-download).
RUN cd /opt/ithica/fleetbench \
    && bazel build --spawn_strategy=local --config=clang-14 --config=opt \
         //fleetbench/hashing:hashing_benchmark \
         //fleetbench/proto:proto_benchmark \
         //fleetbench/swissmap:swissmap_benchmark \
         //fleetbench/stl:cord_benchmark \
         //fleetbench/libc:mem_benchmark \
         //fleetbench/tcmalloc:empirical_driver

# The driver is copied last so editing it does not invalidate the warm-up layer.
COPY run.sh /opt/ithica/
RUN chmod +x /opt/ithica/run.sh

ENV PATH=/opt/ithica:$PATH
WORKDIR /opt/ithica/fleetbench
ENTRYPOINT ["/opt/ithica/run.sh"]
CMD ["list"]
