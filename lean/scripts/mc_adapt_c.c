/*
 * Differential-harness twin of the C's MC-adaptivity key computation
 * (`tool_cluster_range`, kronecker in `src/tinyvdb_sparse_tools.c`):
 * the exact per-axis guard, driven by the same seeded xorshift64 corpus as
 * the Lean twin `Vdb/McAdaptKey.lean` (`mckeycheck`). Prints one summary
 * line:
 *
 *     ok <n> overflow <n> checksum <n>
 *
 *   checksum = wrapping uint64 sum of the raw bits of the accepted (integral)
 *   keys, in the order the twin walks vertices and axes.
 *
 * The corpus generator (xorshift64*, mixDouble, the adversarial tables and
 * the folding rules) is a line-for-line mirror of the Lean one; any drift
 * between the two sides shows up as a checksum mismatch.
 *
 * Build: cc -O2 -std=c11 -o mc_adapt_c mc_adapt_c.c -lm
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

static uint64_t xs64(uint64_t s) {
  s ^= s >> 12;
  s ^= s << 25;
  s ^= s >> 27;
  return s * 0x2545F4914F6CDD1DULL;
}

static double u64_to_double_bits(uint64_t bits) {
  double d;
  memcpy(&d, &bits, sizeof(d));
  return d;
}
static uint64_t double_to_u64_bits(double d) {
  uint64_t b;
  memcpy(&b, &d, sizeof(b));
  return b;
}

/* Mirror of Vdb.McAdaptKey.mixDouble. */
static double mixDouble(uint64_t bits) {
  uint64_t sign = bits & 0x8000000000000000ULL;
  uint64_t mantissa = bits & 0x000FFFFFFFFFFFFFULL;
  uint64_t exp = 0x3F00000000000000ULL + (bits >> 12) % 0x7F0000000000ULL;
  return u64_to_double_bits(sign | exp | mantissa);
}

/* Mirror of Vdb.McAdaptKey.adversarialV. */
static double adversarialV(uint64_t j) {
  switch (j % 24) {
    case 0: return 0.0;
    case 1: return -0.0;
    case 2: return 1.0 / 0.0;
    case 3: return -(1.0 / 0.0);
    case 4: return 0.0 / 0.0;
    case 5: return 5e-324;
    case 6: return -5e-324;
    case 7: return u64_to_double_bits(0x43E0000000000000ULL);
    case 8: return u64_to_double_bits(0x43DFFFFFFFFFFFFFULL);
    case 9: return u64_to_double_bits(0x43E0000000000001ULL);
    case 10: return u64_to_double_bits(0xC3E0000000000000ULL);
    case 11: return u64_to_double_bits(0xC3DFFFFFFFFFFFFFULL);
    case 12: return u64_to_double_bits(0xC3E0000000000001ULL);
    case 13: return 9007199254740992.0;
    case 14: return -9007199254740992.0;
    case 15: return 1e308;
    case 16: return -1e308;
    case 17: return 4.5e15;
    case 18: return -4.5e15;
    case 19: return u64_to_double_bits(0x7FF8000000000001ULL);
    case 20: return u64_to_double_bits(0x7FFFFFFFFFFFFFFFULL);
    case 21: return u64_to_double_bits(0xFFFF000000000001ULL);
    default: return u64_to_double_bits(0xFFF0000000000000ULL);
  }
}

/* Mirror of Vdb.McAdaptKey.corpusStepAdv. */
static double corpusStepAdv(uint64_t i) {
  switch (i % 8) {
    case 0: return 3.7e-4;
    case 1: return 1.0;
    case 2: return 1e3;
    case 3: return 1e-6;
    case 4: return 1e300;
    case 5: return 5e-324;
    case 6: return 0.0 / 0.0;
    default: return 1.0 / 0.0;
  }
}

/* Mirror of Vdb.McAdaptKey.corpusV. */
static double corpusV(uint64_t j) {
  if (j % 4 == 0) return adversarialV(j);
  return mixDouble(xs64(0x243F6A8885A308D3ULL + j * 0x9E3779B97F4A7C15ULL));
}

/* Mirror of Vdb.McAdaptKey.corpusStepAt. */
static double corpusStepAt(uint64_t i) {
  if (i % 4 == 0) return corpusStepAdv(i);
  return mixDouble(xs64(0xBB67AE8584CAA73BULL + i * 0xC2B2AE3D27D4EB4FULL));
}

/* The exact C guard from tool_cluster_range. Returns 0 on no overflow,
 * 1 on overflow; on success *key_out (if non-NULL) receives the key. */
static int mcKeyAxis(double v, double step, double* key_out) {
  const double q = floor(v / step);
  if (!isfinite(q) || q < -9223372036854775808.0 ||
      q >= 9223372036854775808.0)
    return 1;
  if (key_out) *key_out = q;
  return 0;
}

int main(int argc, char** argv) {
  const size_t n = argc > 1 ? (size_t)strtoull(argv[1], NULL, 10) : 1000000;
  uint64_t ok = 0, ov = 0, bits = 0;
  for (uint64_t i = 0; i < (uint64_t)n; ++i) {
    const double step = corpusStepAt(i);
    for (int a = 0; a < 3; ++a) {
      const double v = corpusV(3 * i + (uint64_t)a);
      double q;
      if (mcKeyAxis(v, step, &q) == 0) {
        ok += 1;
        bits += double_to_u64_bits(q);
      } else {
        ov += 1;
      }
    }
  }
  printf("ok %" PRIu64 " overflow %" PRIu64 " checksum %" PRIu64 "\n",
         ok, ov, bits);
  return 0;
}
