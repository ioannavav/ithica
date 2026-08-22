define newline


endef
# =============================================================================
# ITHICA -- build cpu-check instrumented with an ITHICA compiler pass
# =============================================================================
#
# This Makefile reproduces the full instrumented software stack used in the
# ITHICA paper: the LLVM libc / libc++ overlay, OpenSSL, Abseil, zlib and
# finally Google's cpu-check are each compiled with an ITHICA pass loaded into
# clang (legacy pass manager). The final cpu-check binary is linked against the
# `libpassmmap` runtime helper (mmap_file.c), which the passes call to report a
# detected corruption.
#
# REQUIRED TOOLCHAIN: clang / LLVM / lld 14.0.6. The passes use the LLVM legacy
# pass manager, which does not exist in clang >= 15. Get the exact toolchain by
# entering the pinned Guix environment first:
#
#     ./guix.sh                 # drops into a shell with clang-14 + tools
#     [env]$ make               # == make all
#
# COMMON USAGE:
#     make PASS=arith               # choose the pass (default: arith)
#     make BLOCKSIZE=1 INTERLEAVING=1 LIBRARYNAME=cpu_check
#     make cpu_check                # build a single stage (deps must exist)
#     make clean                    # remove build/ and install prefix
#     make distclean                # also remove fetched dependency sources
#
# The build is intentionally sequential and ordered (see `all`): each stage
# depends on the install prefix produced by the previous one.
#
# RUNNING THE RESULT:
#     install_bs$(BLOCKSIZE)_intr$(INTERLEAVING)/cpu-check/bin/cpu_check
#   See README.md ("Running the artifact") for runtime notes that affect the
#   user experience (word list, what a detected corruption looks like, etc.).
# =============================================================================

# ---- Toolchain (provided by the Guix environment; override if needed) -------
# CC/CXX have built-in make defaults (cc/g++), so `?=` won't override them.
# Replace only the built-in default while still honoring env/command-line values.
ifeq ($(origin CC),default)
CC := clang
endif
ifeq ($(origin CXX),default)
CXX := clang++
endif
LLVM_CONFIG ?= llvm-config
JOBS        ?= $(shell nproc)

# ---- Pass parameters (see README.md "Parameter selection") ------------------
# BLOCKSIZE:    1,2,4,8 or 0 (=insert checks at the dependency-chain end)
# INTERLEAVING: 1,2,4,8 or 0 (=place duplicate instructions at end of block)
# LIBRARYNAME:  string printed when a corruption is detected
BLOCKSIZE    ?= 1
INTERLEAVING ?= 1
VALID_KNOBS  := 0 1 2 4 8
ifeq ($(filter $(BLOCKSIZE),$(VALID_KNOBS)),)
$(error Invalid BLOCKSIZE='$(BLOCKSIZE)'. Valid: $(VALID_KNOBS))
endif
ifeq ($(filter $(INTERLEAVING),$(VALID_KNOBS)),)
$(error Invalid INTERLEAVING='$(INTERLEAVING)'. Valid: $(VALID_KNOBS))
endif
LIBRARYNAME  ?= cpu_check

# ---- Directory layout -------------------------------------------------------
ROOT    := $(CURDIR)
TP      := $(ROOT)/third_party
BUILD   := $(ROOT)/build
MMAP    := $(BUILD)/libpassmmap
# INSTALL (and LIBLLVMLIBC) are defined after the pass selection below, because
# the install prefix is named after the selected pass.

# ---- Pass selection ---------------------------------------------------------
# PASS selects which ITHICA transformation to apply. Each maps to one of the
# pass source files in this directory (registered pass name in parentheses).
# No default: building the wrong configuration silently is worse than stopping.
# `make help` still works without PASS so the options are discoverable.
PASS ?=
ifeq ($(strip $(PASS)),)
ifneq ($(MAKECMDGOALS),help)
$(error No PASS specified. Choose one of:$(newline)  make PASS=CC              original cpu-check, no ITHICA pass (baseline)$(newline)  make PASS=arith           Arith$(newline)  make PASS=mem|memdiv|br|arithmem|arithmemdiv|arithmemdivbr$(newline)Optional: BLOCKSIZE=1|2|4|8|0 (default 1)  INTERLEAVING=1|2|4|8|0 (default 1))
endif
endif

# PASS=CC selects the ORIGINAL, UNINSTRUMENTED cpu-check: the upstream program
# built with no ITHICA pass loaded at all. It is the baseline every instrumented
# configuration below is compared against. ("CC" = cpu-check, as used in the paper.)
#
# PASS value -> source file (registered pass name):
#   arith          ArithmeticPass.cpp    (arithmeticpass)
#   mem            MemPass.cpp           (mempass)
#   memdiv         MemDivPass.cpp        (memdivpass)
#   br             BranchPass.cpp        (branchpass)
#   arithmem       ArithMemPass.cpp      (arithmempass)
#   arithmemdiv    ArithMemDivPass.cpp   (arithmemdivpass)
#   arithmemdivbr  ArithMemDivBrPass.cpp (arithmemdivbrpass)
PASS_SRC_arith         := ArithmeticPass.cpp
PASS_SRC_mem           := MemPass.cpp
PASS_SRC_memdiv        := MemDivPass.cpp
PASS_SRC_br            := BranchPass.cpp
PASS_SRC_arithmem      := ArithMemPass.cpp
PASS_SRC_arithmemdiv   := ArithMemDivPass.cpp
PASS_SRC_arithmemdivbr := ArithMemDivBrPass.cpp

# Optional (secondary) -- not part of the default pass set. These "original"
# variants reproduce the paper binary sizes (see README, "Binary sizes"); default
# users should use the primary passes above. Build e.g.: make PASS=original_br
PASS_SRC_original_mem    := Original_MemPass.cpp
PASS_SRC_original_memdiv := Original_MemDivPass.cpp
PASS_SRC_original_br     := Original_BranchPass.cpp

# PASS=CC builds the uninstrumented baseline (no pass plugin loaded).
ifeq ($(PASS),CC)
PASS_SRC :=
PASS_SO  :=
else ifeq ($(strip $(PASS)),)
# Empty only reaches here for `make help`; the guard above stops real builds.
PASS_SRC :=
PASS_SO  :=
else
PASS_SRC := $(PASS_SRC_$(PASS))
ifeq ($(PASS_SRC),)
$(error Unknown PASS='$(PASS)'. Valid: CC arith mem memdiv br arithmem arithmemdiv arithmemdivbr)
endif
PASS_SO := $(BUILD)/$(basename $(PASS_SRC)).so
endif

# Install prefix is per-configuration: pass + block size + interleaving, so
# building several passes no longer overwrites the previous binary.
INSTALL := $(ROOT)/$(PASS)_install_bs$(BLOCKSIZE)_intr$(INTERLEAVING)
LIBLLVMLIBC := $(INSTALL)/libc/lib/x86_64-unknown-linux-gnu/libllvmlibc.a

# ---- Pinned dependency sources ----------------------------------------------
# Cloned into third_party/ on first build (needs --network in guix.sh). If the
# directory already exists it is reused as-is, so pre-populating third_party/
# for a fully offline build changes nothing else in this Makefile.
ZLIB_URL       ?= https://github.com/madler/zlib.git
ZLIB_TAG       ?= v1.2.8
ABSEIL_URL     ?= https://github.com/abseil/abseil-cpp.git
# abseil LTS 20230125.4
ABSEIL_COMMIT  ?= 1b66579c740e9b3548600dc338fc584682ad04f7
OPENSSL_URL    ?= https://github.com/openssl/openssl.git
# openssl 3.4.0-alpha1-279-g (exact commit used by the legacy build)
OPENSSL_COMMIT ?= eaf4da97c9b9c09a407b9f1a47ad7dd99c05884c
LLVM_URL       ?= https://github.com/llvm/llvm-project.git
LLVM_TAG       ?= llvmorg-17.0.6

# ---- Compiler flag sets (ported from the legacy build) ----------------------
# How the pass is injected into clang: load the plugin and force the legacy
# pass manager, then link the runtime helper into the produced objects/binary.
ifeq ($(PASS),CC)
PASS_LOAD :=
else
PASS_LOAD := -flegacy-pass-manager -Xclang -load -Xclang $(PASS_SO)
endif

# Used for C stages and for building the libc/libc++ overlay itself (no overlay
# headers here, since these produce/precede the overlay).
C_PASS_FLAGS := -O2 -static -ffp-contract=on -fno-limit-debug-info -fno-slp-vectorize \
                -fuse-ld=lld -Wno-unused-command-line-argument $(MMAP) $(PASS_LOAD)

# Used for C++ stages that consume the overlay (abseil, cpu-check). Matches the
# legacy build's -std=c++11; abseil and cpu-check raise it to C++17 via their
# own CMake CXX_STANDARD, which wins.
CXX_PASS_FLAGS := -O2 -static -ffp-contract=on -fno-limit-debug-info -fno-slp-vectorize \
                  -std=c++11 -fuse-ld=lld -Wno-unused-command-line-argument \
                  -nostdinc++ -nostdlib++ \
                  -isystem $(INSTALL)/libstdc++/include/c++/v1 \
                  -L $(INSTALL)/libstdc++/lib \
                  -Wl,-rpath,$(INSTALL)/libstdc++/lib \
                  -lc++ -lc++abi $(MMAP) $(PASS_LOAD)  

# =============================================================================
# Aggregate targets
# =============================================================================
.DEFAULT_GOAL := all

# Full instrumented stack, in dependency order.
.PHONY: all
all: llvmlibc llvmlibcpp openssl abseil zlib cpu_check

.PHONY: help
help:
	@echo "Targets: all llvmlibc llvmlibcpp openssl abseil zlib cpu_check pass clean distclean"
	@echo "PASS:    CC = original uninstrumented cpu-check (no ITHICA pass);"
	@echo "         arith mem memdiv br arithmem arithmemdiv arithmemdivbr"
	@echo "Vars:    PASS=$(PASS)  BLOCKSIZE=$(BLOCKSIZE)  INTERLEAVING=$(INTERLEAVING)  LIBRARYNAME=$(LIBRARYNAME)"
	@echo "Pass:    $(PASS_SRC) -> $(PASS_SO)"
	@echo "Install: $(INSTALL)"

# =============================================================================
# Pass plugin + runtime helper
# =============================================================================
$(BUILD):
	mkdir -p $(BUILD)

# Runtime helper linked into every instrumented binary.
$(MMAP): mmap_file.c | $(BUILD)
	$(CC) mmap_file.c -fPIC -Wno-format-security -c -o $@

# Build the pass plugin. Kept .PHONY so that each stage can (re)build it with a
# stage-specific LIBRARYNAME, matching the legacy per-library build.
# For PASS=CC there is no pass plugin to build, so this is a no-op: the stages
# still invoke it, but the uninstrumented baseline loads no plugin.
.PHONY: pass
pass: $(MMAP) | $(BUILD)
ifneq ($(PASS),CC)
	$(CXX) -shared -fPIC -o $(PASS_SO) \
	    -DBLOCKSIZE=$(BLOCKSIZE) -DINTERLEAVING=$(INTERLEAVING) \
	    -DLIBRARYNAME='"$(LIBRARYNAME)"' \
	    $(PASS_SRC) `$(LLVM_CONFIG) --cxxflags`
endif

# =============================================================================
# Dependency sources (fetched once, then reused / offline-friendly)
# =============================================================================
# Clones are atomic: fetch into <dir>.tmp and rename into place only on full
# success. An interrupted clone therefore never leaves a half-populated
# <dir> that would be mistaken for "already fetched" on the next run.
$(TP)/zlib:
	rm -rf $@ $@.tmp
	git clone --depth 1 --branch $(ZLIB_TAG) $(ZLIB_URL) $@.tmp
	mv $@.tmp $@

$(TP)/abseil-cpp:
	rm -rf $@ $@.tmp
	git clone $(ABSEIL_URL) $@.tmp
	cd $@.tmp && git checkout --detach $(ABSEIL_COMMIT)
	mv $@.tmp $@

$(TP)/openssl:
	rm -rf $@ $@.tmp
	git clone $(OPENSSL_URL) $@.tmp
	cd $@.tmp && git checkout --detach $(OPENSSL_COMMIT)
	mv $@.tmp $@

$(TP)/llvm-project:
	rm -rf $@ $@.tmp
	git clone --depth 1 --branch $(LLVM_TAG) $(LLVM_URL) $@.tmp
	mv $@.tmp $@

# =============================================================================
# Stage 1: LLVM libc overlay  ->  install/libc  (produces libllvmlibc.a)
# =============================================================================
.PHONY: llvmlibc
llvmlibc: $(TP)/llvm-project
	$(MAKE) pass LIBRARYNAME=llvmlibc
	rm -rf $(BUILD)/libc-build
	mkdir -p $(BUILD)/libc-build
	cd $(BUILD)/libc-build && cmake $(TP)/llvm-project/llvm -G "Unix Makefiles" \
	    -DLLVM_ENABLE_PROJECTS="libc" \
	    -DCMAKE_C_COMPILER=$(CC) -DCMAKE_CXX_COMPILER=$(CXX) \
	    -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
	    -DCMAKE_C_FLAGS="$(C_PASS_FLAGS)" -DCMAKE_CXX_FLAGS="$(C_PASS_FLAGS)" \
	    -DCMAKE_BUILD_TYPE=Release \
	    -DCMAKE_INSTALL_PREFIX=$(INSTALL)/libc
	cd $(BUILD)/libc-build && $(MAKE) install-libc -j$(JOBS)

# =============================================================================
# Stage 2: libc++/libc++abi/libunwind overlay  ->  install/libstdc++
# =============================================================================
.PHONY: llvmlibcpp
llvmlibcpp: $(TP)/llvm-project
	$(MAKE) pass LIBRARYNAME=llvmlibcpp
	rm -rf $(TP)/llvm-project/build
	cd $(TP)/llvm-project && cmake -G "Unix Makefiles" -S runtimes -B build \
	    -DLIBCXX_ENABLE_SHARED=OFF \
	    -DLIBCXXABI_ENABLE_SHARED=OFF \
	    -DLIBUNWIND_ENABLE_SHARED=OFF \
	    -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
	    -DLLVM_ENABLE_RUNTIMES="libcxx;libcxxabi;libunwind" \
	    -DCMAKE_C_COMPILER=$(CC) -DCMAKE_CXX_COMPILER=$(CXX) \
	    -DCMAKE_C_FLAGS="$(C_PASS_FLAGS)" -DCMAKE_CXX_FLAGS="$(C_PASS_FLAGS)" \
	    -DCMAKE_INSTALL_PREFIX=$(INSTALL)/libstdc++ \
	    -DCMAKE_STATIC_LINKER_FLAGS="$(LIBLLVMLIBC)"
	cd $(TP)/llvm-project/build && $(MAKE) cxx cxxabi unwind -j$(JOBS)
	cd $(TP)/llvm-project/build && $(MAKE) install-cxx install-cxxabi install-unwind -j$(JOBS)

# =============================================================================
# Stage 3: OpenSSL  ->  install/openssl
# =============================================================================
.PHONY: openssl
openssl: $(TP)/openssl
	$(MAKE) pass LIBRARYNAME=openssl
	-cd $(TP)/openssl && $(MAKE) distclean
	cd $(TP)/openssl && ./config no-shared no-pic no-tests \
	    --prefix=$(INSTALL)/openssl \
	    CC=$(CC) CXX=$(CXX) \
	    CFLAGS="$(C_PASS_FLAGS)" CXXFLAGS="$(CXX_PASS_FLAGS)"
	cd $(TP)/openssl && $(MAKE) install

# =============================================================================
# Stage 4: Abseil  ->  install/abseil
# =============================================================================
.PHONY: abseil
abseil: $(TP)/abseil-cpp
	$(MAKE) pass LIBRARYNAME=abseil
	rm -rf $(BUILD)/abseil-build
	mkdir -p $(BUILD)/abseil-build
	cd $(BUILD)/abseil-build && cmake $(TP)/abseil-cpp -G "Unix Makefiles" \
	    -DCMAKE_CXX_COMPILER=$(CXX) \
	    -DCMAKE_CXX_FLAGS="$(CXX_PASS_FLAGS)" \
	    -DCMAKE_CXX_STANDARD_REQUIRED=ON -DCMAKE_CXX_STANDARD=17 \
	    -DCMAKE_INSTALL_PREFIX=$(INSTALL)/abseil \
	    -DCMAKE_STATIC_LINKER_FLAGS="$(LIBLLVMLIBC)"
	cd $(BUILD)/abseil-build && $(MAKE) install -j$(JOBS)

# =============================================================================
# Stage 5: zlib  ->  install/zlib
# =============================================================================
.PHONY: zlib
zlib: $(TP)/zlib
	$(MAKE) pass LIBRARYNAME=zlib
	rm -rf $(BUILD)/zlib-build $(INSTALL)/zlib
	mkdir -p $(BUILD)/zlib-build
	cd $(BUILD)/zlib-build && cmake $(TP)/zlib -G "Unix Makefiles" \
	    -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
	    -DCMAKE_C_COMPILER=$(CC) \
	    -DCMAKE_C_FLAGS="$(C_PASS_FLAGS)" \
	    -DCMAKE_INSTALL_PREFIX=$(INSTALL)/zlib \
	    -DCMAKE_STATIC_LINKER_FLAGS="$(LIBLLVMLIBC)"
	cd $(BUILD)/zlib-build && $(MAKE) zlibstatic -j$(JOBS)
	mkdir -p $(INSTALL)/zlib/lib $(INSTALL)/zlib/include
	# zlib.h copied from source (the legacy build omitted it, which breaks find_package(ZLIB))
	cp $(TP)/zlib/zlib.h $(INSTALL)/zlib/include
	cp $(BUILD)/zlib-build/zconf.h $(INSTALL)/zlib/include
	cp $(BUILD)/zlib-build/zlib.pc $(INSTALL)/zlib/include
	cp $(BUILD)/zlib-build/libz.a $(INSTALL)/zlib/lib

# =============================================================================
# Stage 6: cpu-check (vendored)  ->  install/cpu-check
# =============================================================================
.PHONY: cpu_check
cpu_check: $(TP)/cpu-check
	$(MAKE) pass LIBRARYNAME=cpu_check
	rm -rf $(BUILD)/cpu-check-build
	mkdir -p $(BUILD)/cpu-check-build
	cd $(BUILD)/cpu-check-build && cmake $(TP)/cpu-check -G "Unix Makefiles" \
	    -Dabsl_DIR=$(INSTALL)/abseil/lib64/cmake/absl \
	    -DBUILD_STATIC=ON \
	    -DOPENSSL_USE_STATIC_LIBS=true \
	    -DCMAKE_PREFIX_PATH=$(INSTALL)/zlib \
	    -DCMAKE_C_COMPILER=$(CC) -DCMAKE_CXX_COMPILER=$(CXX) \
	    -DOPENSSL_ROOT_DIR=$(INSTALL)/openssl \
	    -DOPENSSL_INCLUDE_DIRS=$(INSTALL)/openssl/include \
	    -DCMAKE_C_FLAGS="$(C_PASS_FLAGS)" \
	    -DCMAKE_CXX_FLAGS="$(CXX_PASS_FLAGS)" \
	    -DCMAKE_INSTALL_PREFIX=$(INSTALL)/cpu-check
	cd $(BUILD)/cpu-check-build && $(MAKE) install

# =============================================================================
# Cleanup
# =============================================================================
.PHONY: clean
clean:
	rm -rf $(BUILD) $(INSTALL)

# Also removes fetched dependency sources (keeps the vendored cpu-check).
.PHONY: distclean
distclean: clean
	rm -rf $(TP)/zlib $(TP)/abseil-cpp $(TP)/openssl $(TP)/llvm-project
