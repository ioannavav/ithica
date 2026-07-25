_ITHICA_PASS = [
    "-flegacy-pass-manager",
    "-Xclang", "-load", "-Xclang", "/opt/ithica/passes/pass.so",
]
STL_LLVM_COPT_FLAGS = ["-Wno-unused-variable", "-O2", "-static", "-fuse-ld=lld"]
STL_DEFAULT_COPTS = select({
    "//fleetbench:llvm": STL_LLVM_COPT_FLAGS,
    "//conditions:default": [],
}) + select({
    "//fleetbench:with_pass": _ITHICA_PASS,
    "//conditions:default": [],
})
STL_DEFAULT_LINKOPTS = select({"//conditions:default": []})
