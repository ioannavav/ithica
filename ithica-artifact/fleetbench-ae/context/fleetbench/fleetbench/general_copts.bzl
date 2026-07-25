# ITHICA instrumentation copts. The pass plugin is loaded only under
# --config=pass (config_setting //fleetbench:with_pass); otherwise the target is
# compiled as an un-instrumented baseline. /opt/ithica/passes/pass.so is a
# symlink to the selected pass (default: ArithmeticPass.so).
_ITHICA_PASS = [
    "-flegacy-pass-manager",
    "-Xclang", "-load", "-Xclang", "/opt/ithica/passes/pass.so",
]
GENERAL_LLVM_COPT_FLAGS = [
    "-Wno-unused-variable", "-O2", "-static", "-fuse-ld=lld", "-static-libstdc++",
]
GENERAL_DEFAULT_COPTS = select({
    "//fleetbench:llvm": GENERAL_LLVM_COPT_FLAGS,
    "//conditions:default": [],
}) + select({
    "//fleetbench:with_pass": _ITHICA_PASS,
    "//conditions:default": [],
})
# Runtime helpers are linked globally via --config=pass (see .bazelrc).
STL_DEFAULT_LINKOPTS = select({"//conditions:default": []})
