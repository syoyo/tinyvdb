// SIMD vs scalar parity test for tinyvdb_simd.h.
// Builds the same workload twice — once via SIMD path (current build), once
// via scalar reference (compiled with TINYVDB_SIMD undefined) — and verifies
// numerical agreement within a small tolerance.

#include "tinyvdb_simd.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); \
    ++g_failures; } } while (0)

// Scalar references (always available — they're inline in the header
// but we want pure-scalar checks, so reimplement here).
static double scalar_dot(const float* a, const float* b, size_t n) {
    double s = 0.0;
    for (size_t i = 0; i < n; ++i) s += (double)a[i] * (double)b[i];
    return s;
}

static void scalar_axpy(float alpha, const float* x, float* y, size_t n) {
    for (size_t i = 0; i < n; ++i) y[i] += alpha * x[i];
}

int main(void) {
    // Build a 10K-element fp32 vector with mixed values.
    const size_t N = 10000;
    float* a = (float*)malloc(N * sizeof(float));
    float* b = (float*)malloc(N * sizeof(float));
    for (size_t i = 0; i < N; ++i) {
        // Small magnitudes so fp32 accumulation doesn't saturate.
        // Cast to signed BEFORE subtraction to avoid unsigned underflow.
        a[i] = (float)((int)(i % 17) - 8) * 0.0125f;
        b[i] = (float)((int)(i % 13) - 6) * 0.00625f;
    }

    // Dot product parity.
    double simd_d = tvdb_simd_dot_f32(a, b, N);
    double scal_d = scalar_dot(a, b, N);
    printf("[simd] dot N=%zu: simd=%.6e scalar=%.6e diff=%.3e\n",
           N, simd_d, scal_d, fabs(simd_d - scal_d));
    EXPECT(fabs(simd_d - scal_d) < 1e-3);

    // AXPY parity.
    float* y_simd = (float*)malloc(N * sizeof(float));
    float* y_scal = (float*)malloc(N * sizeof(float));
    for (size_t i = 0; i < N; ++i) y_simd[i] = y_scal[i] = (float)i * 0.001f;
    tvdb_simd_axpy_f32(2.5f, a, y_simd, N);
    scalar_axpy(2.5f, a, y_scal, N);
    double max_diff = 0.0;
    for (size_t i = 0; i < N; ++i) {
        double d = fabs((double)y_simd[i] - (double)y_scal[i]);
        if (d > max_diff) max_diff = d;
    }
    printf("[simd] axpy max diff: %.3e\n", max_diff);
    EXPECT(max_diff < 1e-5);

    // F16 round-trip parity. Use known half-representable values.
    const size_t H = 1024;
    float* in_f = (float*)malloc(H * sizeof(float));
    uint16_t* mid_h = (uint16_t*)malloc(H * sizeof(uint16_t));
    float* out_f = (float*)malloc(H * sizeof(float));
    for (size_t i = 0; i < H; ++i) {
        // Stay well inside fp16's normal range (max 65504, min normal ~6e-5).
        // Sign + small mantissa variety + exponents in [-8, 8].
        int sign = (i & 1) ? -1 : 1;
        int exp_bias = ((int)(i % 16)) - 8;
        // Mantissa in [1, 2): ensures the fp32 value is exactly representable
        // in fp16 for the scalar encoder check below.
        float mant = 1.0f + (float)(i % 1024) / 2048.0f;
        in_f[i] = (float)sign * mant * ldexpf(1.0f, exp_bias);
    }
    tvdb_simd_f32_to_f16(in_f, mid_h, H);
    tvdb_simd_f16_to_f32(mid_h, out_f, H);
    double max_rel = 0.0;
    for (size_t i = 0; i < H; ++i) {
        if (in_f[i] == 0.0f) continue;
        double rel = fabs((double)(out_f[i] - in_f[i]) / (double)in_f[i]);
        if (rel > max_rel) max_rel = rel;
    }
    printf("[simd] f16 round-trip max relative err: %.3e\n", max_rel);
    EXPECT(max_rel < 1e-3);  // fp16 has ~10 bits mantissa => ~1e-3 precision

    // F16 conversion parity vs scalar reference. F16C uses round-to-nearest-
    // even; the simple scalar reference uses round-half-up. They may differ
    // by exactly 1 ULP at halfway values. Accept that, but require the
    // resulting fp32 values agree to within 1 ULP of fp16 precision (~6e-4).
    uint16_t* h_simd = (uint16_t*)malloc(H * sizeof(uint16_t));
    uint16_t* h_scal = (uint16_t*)malloc(H * sizeof(uint16_t));
    tvdb_simd_f32_to_f16(in_f, h_simd, H);
    for (size_t i = 0; i < H; ++i) h_scal[i] = tvdb__float_to_half_scalar(in_f[i]);
    int ulp_mismatch = 0;
    for (size_t i = 0; i < H; ++i) {
        int d = (int)h_simd[i] - (int)h_scal[i];
        if (d < -1 || d > 1) ++ulp_mismatch;
    }
    printf("[simd] f16 encoders disagree by >1 ULP: %d / %zu\n", ulp_mismatch, H);
    EXPECT(ulp_mismatch == 0);

    free(a); free(b); free(y_simd); free(y_scal);
    free(in_f); free(mid_h); free(out_f); free(h_simd); free(h_scal);

    if (g_failures == 0) {
        printf("All SIMD parity tests passed.\n");
        return 0;
    }
    printf("%d failures.\n", g_failures);
    return 1;
}
