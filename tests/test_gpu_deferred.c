#include "tinyvdb_gpu.h"
#include <stdio.h>
#include <string.h>
#ifdef TVDB_TEST_GENERATED_SPV
#include "tinyvdb_gpu_axpy_spv.inc"
#else
#include "tinyvdb_gpu_spv_fallback.inc"
#endif

static int queue_axpy(tvdb_gpu_context_t *ctx, float *out, float *roundtrip, tvdb_error_t *err) {
    float x[4] = {1, 2, 3, 4};
    struct { uint32_t n; float alpha; uint32_t pad[2]; } u = {4, 2, {0, 0}};
    tvdb_gpu_binding_t bindings[4] = {
        {TVDB_GPU_BIND_STORAGE_IN, x, sizeof(x)},
        {TVDB_GPU_BIND_STORAGE_INOUT, roundtrip, sizeof(x)},
        {TVDB_GPU_BIND_STORAGE_OUT, out, sizeof(x)},
        {TVDB_GPU_BIND_UNIFORM, &u, sizeof(u)}
    };
    tvdb_gpu_dispatch_spec_t spec;
    memset(&spec, 0, sizeof(spec));
    spec.spv = kTvdbGpuAxpySpv; spec.spv_len = kTvdbGpuAxpySpv_len;
    spec.bindings = bindings; spec.num_bindings = 4;
    spec.group_count_x = 1; spec.defer = 1;
    /* Stack inputs are copied; both output bindings remain valid until flush. */
    return tvdb_gpu_dispatch(ctx, &spec, err) == TVDB_OK;
}

int main(void) {
    tvdb_gpu_context_t *a = NULL, *b = NULL;
    tvdb_error_t err = {0};
    int failed = 0;
    float oa[4] = {0}, ob[4] = {0};
    float ya[4] = {10,20,30,40}, yb[4] = {10,20,30,40};
    if (!tvdb_gpu_spirv_available() ||
        tvdb_gpu_context_create(TVDB_GPU_BACKEND_VULKAN, 0, &a, &err) != TVDB_OK)
        return 77;
    if (tvdb_gpu_context_create(TVDB_GPU_BACKEND_VULKAN, 0, &b, &err) != TVDB_OK) {
        tvdb_gpu_context_destroy(a); return 77;
    }
    if (!queue_axpy(a, oa, ya, &err) || !queue_axpy(b, ob, yb, &err) ||
        tvdb_gpu_dispatch_flush(b, &err) != TVDB_OK) failed = 1;
    for (int i = 0; i < 4; ++i)
        if (ob[i] != 12.0f * (i + 1) || oa[i] != 0.0f) failed = 1;
    if (tvdb_gpu_dispatch_flush(a, &err) != TVDB_OK) failed = 1;
    for (int i = 0; i < 4; ++i)
        if (oa[i] != 12.0f * (i + 1)) failed = 1;
    if (tvdb_gpu_dispatch_flush(a, &err) != TVDB_OK) failed = 1;
    /* Exceed the bounded deferred queue and verify every output binding. */
    float outputs[12][4] = {{0}}, passthrough[12][4];
    for (int n = 0; n < 12; ++n) {
        for (int i = 0; i < 4; ++i) passthrough[n][i] = (float)(10 * (i + 1) + n);
        if (!queue_axpy(a, outputs[n], passthrough[n], &err)) failed = 1;
    }
    if (tvdb_gpu_dispatch_flush(a, &err) != TVDB_OK) failed = 1;
    for (int n = 0; n < 12; ++n) for (int i = 0; i < 4; ++i) {
        if (outputs[n][i] != 12.0f * (i + 1) + n ||
            passthrough[n][i] != 10.0f * (i + 1) + n) failed = 1;
    }
    /* Context teardown must also drain and release queued buffers. */
    if (!queue_axpy(a, oa, ya, &err)) failed = 1;
    tvdb_gpu_context_destroy(a);
    tvdb_gpu_context_destroy(b);
    if (failed) fprintf(stderr, "deferred dispatch regression: %s\n", err.message);
    return failed;
}
