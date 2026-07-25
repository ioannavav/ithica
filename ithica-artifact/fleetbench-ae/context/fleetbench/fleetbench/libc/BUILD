package(default_visibility = ["//visibility:private"])
load("@rules_pkg//pkg:pkg.bzl", "pkg_tar")
load("//fleetbench:general_copts.bzl", "GENERAL_DEFAULT_COPTS")

cc_library(
    name = "utils",
    srcs = ["utils.cc"],
    hdrs = ["utils.h"],
    copts = GENERAL_DEFAULT_COPTS,
    deps = ["@com_google_absl//absl/log:check"],
)


cc_import(
    name = "llvmlibc",
    static_library = "libllvmlibc.a",
    visibility = ["//visibility:public"],
)


cc_library(
    name = "mem_benchmark_lib",
    #testonly = True,
    srcs = ["mem_benchmark.cc"],
    data = glob(
        ["distributions/**"],
    ),
    copts = GENERAL_DEFAULT_COPTS,
    visibility = ["//fleetbench:__pkg__"],
    deps = [
         ":utils",
        "//fleetbench:dynamic_registrar",
        "//fleetbench/common",
        "@com_google_absl//absl/algorithm:container",
        "@com_google_absl//absl/container:btree",
        "@com_google_absl//absl/log:check",
        "@com_google_absl//absl/random:distributions",
        "@com_google_absl//absl/strings",
        "@com_google_benchmark//:benchmark",
    ],
    alwayslink = True,
    linkstatic = True,
)

cc_binary(
    name = "mem_benchmark",
    linkstatic = 1,
    copts = GENERAL_DEFAULT_COPTS,
    malloc = "@com_google_tcmalloc//tcmalloc",
    deps = [
        ":mem_benchmark_lib",
        "//fleetbench:benchmark_main",
	":llvmlibc",
    ],
    linkopts = ["-static"],
)

cc_test(
    name = "utils_test",
    srcs = ["utils_test.cc"],
    deps = [
        ":utils",
        "@com_google_absl//absl/types:span",
        "@com_google_googletest//:gtest_main",
    ],
)


pkg_tar(
    name = "mem_benchmark_tar",
    srcs = [
        ":mem_benchmark",
        #"distributions/**", # Include data files or directories if needed
    ],
    #files = glob(["distributions/**"]),
    include_runfiles = True,
    mode = "0755",
    #package_dir = "hashing_benchmark_package",
    out = "mem_benchmark.tar",
    visibility = ["//visibility:public"],
)

