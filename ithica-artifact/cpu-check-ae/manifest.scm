;; GNU Guix manifest pinning the exact toolchain used to build the ITHICA
;; artifact (clang/LLVM 14.0.6 + lld 14.0.6). The ITHICA passes are written
;; against the LLVM *legacy* pass manager, which is unavailable in clang >= 15,
;; so a clang-14 toolchain is mandatory. Enter the environment with ./guix.sh.

(concatenate-manifests
 (list
  (packages->manifest (list `(,(@@ (gnu packages gcc) gcc) "lib")))

  (specifications->manifest
   '("coreutils"
     "findutils"
     "screen"
     "grep"
     "binutils-gold"
     "cmake"
     "clang-toolchain@14.0.6"
     "valgrind"
     "lld@14.0.6"
     "make"
     "ninja"
     "libtool"
     "sed"
     "bash"
     "libomp"
     ;; CA certificate bundle so `git clone` over HTTPS works inside the
     ;; --container guix shell (sets SSL_CERT_DIR/SSL_CERT_FILE). Only needed
     ;; for the network fetch of pinned dependency sources.
     "nss-certs"
     ;; Original version was python@3.10.7 (not available after Jan 2026 guix reinstall)
     "python@3.10.19"
     "vim"
     "perl"
     "git"
     "openssl@3.0.8"))))
