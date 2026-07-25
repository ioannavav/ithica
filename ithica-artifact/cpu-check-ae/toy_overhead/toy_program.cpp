// A small but non-trivial kernel with a realistic mix: a per-element arithmetic
// body over an array (loads/stores), plus one loop-carried multiply-accumulate.
// The loop-carried chain has real latency, so it provides partial instruction-
// level parallelism -- the CPU overlaps some of the duplicated work with it.
// This is representative of everyday code, and gives an apples-to-apples read on
// the ITHICA Arith pass's overhead: the pass duplicates each arithmetic
// instruction and checks its result, while loads/stores are left untouched. The
// driver compiles both builds with vectorization disabled (scalar-vs-scalar).
#include <cstdio>
#include <cstdint>

static double a[8192];

int main() {
  const int  SIZE  = 8192;
  const long ITERS = 300000;

  for (int i = 0; i < SIZE; ++i) a[i] = (double)i * 0.5 + 1.0;

  double s = 1.0;
  for (long it = 0; it < ITERS; ++it) {
    for (int i = 0; i < SIZE; ++i) {
      double x = a[i];                         // load  (not duplicated)
      double y = x * 1.0000001 + 0.5;          // arithmetic (duplicated)
      double z = y * 0.9999998 - x * 0.25;     // arithmetic (duplicated)
      a[i] = z;                                // store (not duplicated)
      s = s * 0.9999999 + z * 0.5;             // loop-carried MAC: partial ILP
    }
  }

  volatile double sink = s + a[SIZE - 1];      // keep the loop live
  printf("%f\n", (double)sink);
  return 0;
}
