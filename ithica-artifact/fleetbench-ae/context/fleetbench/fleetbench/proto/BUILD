load("@rules_cc//cc:defs.bzl", "cc_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")
load("//fleetbench:general_copts.bzl", "GENERAL_DEFAULT_COPTS")

package(default_visibility = ["//visibility:private"])

[proto_library(
    name = "Message%d_proto" % id,
    testonly = True,
    srcs = ["Message%d.proto" % id],
) for id in range(0, 10)]

[cc_proto_library(
    name = "Message%d_cc_proto" % id,
    testonly = True,
    deps = [":Message%d_proto" % id],
) for id in range(0, 10)]


# Separate cc_library for lifecycle.cc without copts
cc_library(
    name = "lifecycle_lib",
    testonly = True,
    copts = GENERAL_DEFAULT_COPTS,
    srcs = ["lifecycle.cc"],
    hdrs = ["access_message%d.h" % id for id in range(0, 10)] + [
        "lifecycle.h",
        "receiver.h",
    ],
    visibility = ["//fleetbench:__pkg__"],
    deps = (
        [":Message%d_cc_proto" % id for id in range(0, 10)] + [
            "//fleetbench:dynamic_registrar",
            "//fleetbench/common",
            "@com_google_absl//absl/strings:cord",
            "@com_google_absl//absl/strings:string_view",
            "@com_google_benchmark//:benchmark",
            "@com_google_protobuf//:protobuf",
        ]
    ),
    alwayslink = True,
)

# Separate cc_library for benchmark.cc with GENERAL_DEFAULT_COPTS
cc_library(
    name = "benchmark_lib",
    testonly = True,
    copts = GENERAL_DEFAULT_COPTS,
    srcs = ["benchmark.cc"],
    hdrs = ["receiver.h"],
    visibility = ["//fleetbench:__pkg__"],
    deps = (
        [":lifecycle_lib"] + 
        [":Message%d_cc_proto" % id for id in range(0, 10)] + [
            "//fleetbench:dynamic_registrar",
            "//fleetbench/common",
            "@com_google_absl//absl/strings:cord",
            "@com_google_absl//absl/strings:string_view",
            "@com_google_benchmark//:benchmark",
            "@com_google_protobuf//:protobuf",
        ]
    ),
    alwayslink = True,
)

# Main library that combines both lifecycle_lib and benchmark_lib
cc_library(
    name = "proto_benchmark_lib",
    testonly = True,
    hdrs = ["access_message%d.h" % id for id in range(0, 10)] + [
        "lifecycle.h",
        "receiver.h",
    ],
    visibility = ["//fleetbench:__pkg__"],
    deps = [
        ":benchmark_lib",
        ":lifecycle_lib",
    ],
    alwayslink = True,
    linkstatic = True,
)

cc_test(
    name = "proto_benchmark",
    linkstatic = 1,
    copts = GENERAL_DEFAULT_COPTS,
    malloc = "@com_google_tcmalloc//tcmalloc",
    deps = [
        ":proto_benchmark_lib",
        "//fleetbench:benchmark_main",
    ],
    linkopts = ["-static"],
)
