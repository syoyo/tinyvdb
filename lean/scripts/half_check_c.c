/* Differential harness for the half-float conversions.
 *
 *   h2f:  dump `h hex16 bits hex32` for all 65536 half bit patterns;
 *         the Lean model's `halfToFloatBits` must match the C
 *         `tvdb__half_to_float` bit-for-bit.
 *
 *   f2h:  dump `u hex32 h hex16` for one witness per rounding fiber of
 *         `float -> half` RNE. Every 32-bit input falls into a fiber;
 *         two inputs in the same fiber produce the same half (the
 *         rounding decision depends only on the sign, the exponent, the
 *         kept mantissa bits q and whether the dropped residue rem is
 *         below/equal/above half the unit of the kept bit). The witnesses
 *         are compared byte-wise against the Lean model's `floatToHalfRNE`.
 *
 *   audit: brute-force all 2^32 inputs and verify that every observed
 *         input really maps to the same half as its fiber witness (table
 *         lookup per fiber; "fiber" = the fiber_id used by `f2h`). Prints
 *         `audit fibers=<N> mismatches=<M>`; M must be 0 and N must equal
 *         the number of witnesses `f2h` emits (so no feasible fiber is
 *         ever left out of the comparison).
 *
 * Compile: cc -std=c11 -O2 -I<repo>/src half_check_c.c <repo>/src/lz4.c <repo>/src/miniz.c -o half_check_c
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint16_t float_to_half_u(uint32_t u) {
    float f;
    memcpy(&f, &u, 4);
    return tvdb__float_to_half(f);
}

static uint32_t fiber_id(uint32_t u) {
    uint32_t sign = u >> 31, e = (u >> 23) & 0xffu, mant = u & 0x7fffffu;
    if (e == 0xff) {
        if (mant == 0) return 0 + sign * 1025 + 0;
        return 0 + sign * 1025 + 1 + (mant >> 13);
    }
    if (e >= 143) return 2051 + (e - 143) * 2 + sign;
    if (e >= 113) {
        uint32_t x = 0x800000u | mant;
        uint32_t q = x >> 13, rem = x & 0x1fffu, half = 0x1000u;
        uint32_t cls = (rem < half) ? 0 : (rem == half) ? 1 : 2;
        return 2275 + (e - 113) * 6144 + sign * 3072 + (q - 0x400u) * 3 + cls;
    }
    if (e >= 102) {
        uint32_t k = 126 - e;
        uint32_t x = 0x800000u | mant;
        uint32_t q = x >> k, rem = x & ((1u << k) - 1u), half = 1u << (k - 1);
        uint32_t qmin = 0x800000u >> k;
        uint32_t cls = (rem < half) ? 0 : (rem == half) ? 1 : 2;
        return 186595 + (e - 102) * 6144 + sign * 3072 + (q - qmin) * 3 + cls;
    }
    return 254179 + e * 2 + sign;
}

#define F_TOTAL 254383

static void usage(const char *argv0) {
    fprintf(stderr, "usage: %s {h2f|f2h|audit}\n", argv0);
    exit(2);
}

static void run_h2f(void) {
    for (uint32_t h = 0; h < 65536; h++) {
        uint16_t hh = (uint16_t)h;
        float f = tvdb__half_to_float(hh);
        uint32_t bits;
        memcpy(&bits, &f, 4);
        printf("%04x %08x\n", h, bits);
    }
}

static void emit(uint32_t u, unsigned *count) {
    printf("%08x %04x\n", u, float_to_half_u(u));
    (*count)++;
}

static void run_f2h(void) {
    unsigned count = 0;
    /* e == 0xFF: Inf fiber (mant == 0) and one NaN fiber per
       (sign, payload-10-bits). Low mantissa bits never reach the output. */
    for (uint32_t sign = 0; sign < 2; sign++) {
        emit((sign << 31) | 0x7f800000u, &count);
        for (uint32_t t = 0; t < 1024; t++) {
            uint32_t mant = t ? (t << 13) : 1; /* t == 0: any nonzero low bits -> payload 0 */
            emit((sign << 31) | 0x7f800000u | mant, &count);
        }
    }
    /* e in [143, 254]: overflow -> Inf, one witness each. */
    for (uint32_t e = 143; e <= 254; e++) {
        for (uint32_t sign = 0; sign < 2; sign++)
            emit((sign << 31) | (e << 23), &count);
    }
    /* e in [113, 142] (normal half): x = 0x800000|mant, k = 13. */
    for (uint32_t e = 113; e <= 142; e++) {
        for (uint32_t sign = 0; sign < 2; sign++) {
            for (uint32_t q = 0x400; q <= 0x7ff; q++) {
                for (uint32_t cls = 0; cls < 3; cls++) {
                    uint32_t rem = (cls == 0) ? 0x0000u : (cls == 1) ? 0x1000u : 0x1001u;
                    uint32_t x = (q << 13) | rem;
                    uint32_t mant = x & 0x7fffffu;
                    emit((sign << 31) | (e << 23) | mant, &count);
                }
            }
        }
    }
    /* e in [102, 112] (subnormal half): k = 126 - e in [14, 24]. */
    for (uint32_t e = 102; e <= 112; e++) {
        uint32_t k = 126 - e;
        uint32_t qmin = 0x800000u >> k, qmax = 0xffffffu >> k;
        uint32_t half = 1u << (k - 1), maxrem = (1u << k) - 1u;
        for (uint32_t sign = 0; sign < 2; sign++) {
            for (uint32_t q = qmin; q <= qmax; q++) {
                uint32_t xlo = 0x800000u > (q << k) ? 0x800000u : (q << k);
                uint32_t xhi = (q << k) | maxrem;
                if (xhi > 0xffffffu) xhi = 0xffffffu;
                uint32_t lo = xlo - (q << k), hi = xhi - (q << k);
                /* one witness per feasible residue class */
                if (lo < half) emit((sign << 31) | (e << 23) | ((xlo & 0x7fffffu)), &count);
                if (lo <= half && half <= hi) emit((sign << 31) | (e << 23) | (((q << k) | half) & 0x7fffffu), &count);
                if (hi > half) emit((sign << 31) | (e << 23) | ((xhi & 0x7fffffu)), &count);
            }
        }
    }
    /* e in [0, 101]: everything flushes to +-0 (validated by `audit`);
       one witness per (e, sign) fiber: the all-ones mantissa, the case
       most likely to carry a wrong round-up. */
    for (uint32_t e = 0; e <= 101; e++) {
        for (uint32_t sign = 0; sign < 2; sign++) {
            emit((sign << 31) | (e << 23) | 0x7fffffu, &count); /* all mant bits */
        }
    }
    fprintf(stderr, "f2h witnesses=%u\n", count);
}

static void run_audit(void) {
    uint16_t *val = (uint16_t *)malloc((size_t)F_TOTAL * sizeof(uint16_t));
    uint8_t *seen = (uint8_t *)calloc((size_t)F_TOTAL, 1);
    size_t fibers_seen = 0, mismatches = 0;
    if (!val || !seen) { fprintf(stderr, "oom\n"); return; }
    for (uint64_t i = 0; i < 4294967296ULL; i++) {
        uint32_t u = (uint32_t)i;
        uint32_t id = fiber_id(u);
        uint16_t h = float_to_half_u(u);
        if (id >= F_TOTAL) { fprintf(stderr, "fiber id out of range\n"); exit(1); }
        if (!seen[id]) { seen[id] = 1; val[id] = h; fibers_seen++; }
        else if (val[id] != h) {
            if (mismatches < 5)
                fprintf(stderr, "fiber %u mismatch: %04x vs %04x at u=%08x\n",
                        id, val[id], h, u);
            mismatches++;
        }
    }
    printf("audit fibers=%zu mismatches=%zu\n", fibers_seen, mismatches);
    free(val); free(seen);
    if (mismatches) exit(1);
}

int main(int argc, char **argv) {
    if (argc != 2) usage(argv[0]);
    if (!strcmp(argv[1], "h2f")) { run_h2f(); return 0; }
    if (!strcmp(argv[1], "f2h")) { run_f2h(); return 0; }
    if (!strcmp(argv[1], "audit")) { run_audit(); return 0; }
    usage(argv[0]);
}
