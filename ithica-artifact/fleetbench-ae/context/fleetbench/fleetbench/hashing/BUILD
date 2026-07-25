load("//fleetbench:general_copts.bzl", "GENERAL_DEFAULT_COPTS")
package(default_visibility = ["//visibility:private"])
load("@rules_pkg//pkg:pkg.bzl", "pkg_tar")

cc_library(
    name = "hashing_benchmark_lib",
    #testonly = True,
    copts = GENERAL_DEFAULT_COPTS,
    srcs = ["hashing_benchmark.cc"],
    data = glob(["distributions/**"]),
    visibility = ["//fleetbench:__pkg__"],
    deps = [
        "//fleetbench:dynamic_registrar",
        "//fleetbench/common",
        "@com_google_absl//absl/container:btree",
        "@com_google_absl//absl/crc:crc32c",
        "@com_google_absl//absl/hash",
        "@com_google_absl//absl/strings",
        "@com_google_benchmark//:benchmark",
    ],
    alwayslink = True,
    linkstatic=True,
)

cc_binary(
    name = "hashing_benchmark",
    linkstatic = 1,
    malloc = "@com_google_tcmalloc//tcmalloc",
    copts = GENERAL_DEFAULT_COPTS,
    deps = [
        ":hashing_benchmark_lib",
        "//fleetbench:benchmark_main",
	#"@bazel_tools//tools/bash/runfiles",
    ],
    linkopts = ["-static"],
)



pkg_tar(
    name = "hashing_benchmark_tar",
    srcs = [
        ":hashing_benchmark",
        #"distributions/**", # Include data files or directories if needed
    ],
    #files = glob(["distributions/**"]),
    include_runfiles = True,
    mode = "0755",
    #package_dir = "hashing_benchmark_package",
    out = "hashing_benchmark.tar",
    visibility = ["//visibility:public"],
)

