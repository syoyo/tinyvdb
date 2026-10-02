#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static size_t calls, fail_at;
static void *fault_malloc(size_t n) { return ++calls == fail_at ? NULL : malloc(n); }
static void *fault_calloc(size_t n, size_t s) { return ++calls == fail_at ? NULL : calloc(n, s); }
static void *fault_realloc(void *p, size_t n) { return ++calls == fail_at ? NULL : realloc(p, n); }
#define malloc fault_malloc
#define calloc fault_calloc
#define realloc fault_realloc
#define TINYVDB_NANOVDB_IMPLEMENTATION
#include "tinyvdb_nanovdb.h"
#undef malloc
#undef calloc
#undef realloc
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "line %d fail_at=%zu: %s\n", __LINE__, fail_at, #x);                   \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)
int main(void) {
    tvdb_error_t err = {0};
    tvdb_raster_output_t out = {0};
    tvdb_projected_gaussian_t g = {2, 2, .1f, 0, .1f, .7f, 1, 8, {.4f, .2f, .8f}};
    calls = 0;
    CHECK(tvdb_gaussian_rasterize_forward(&g, 1, 8, 8, 3, NULL, 1e-12f, &out, &err) == TVDB_OK);
    size_t total = calls;
    tvdb_raster_output_destroy(&out);
    for (size_t n = 1; n <= total; ++n) {
        calls = 0;
        fail_at = n;
        CHECK(tvdb_gaussian_rasterize_forward(&g, 1, 8, 8, 3, NULL, 1e-12f, &out, &err) ==
              TVDB_ERROR_OUT_OF_MEMORY);
        CHECK(!out.image && !out.alpha && !out.last_ids);
        tvdb_raster_output_destroy(&out);
    }
    fail_at = 0;
    CHECK(tvdb_gaussian_rasterize_forward(&g, 1, 8, 8, 3, NULL, 1e-12f, &out, &err) == TVDB_OK);
    tvdb_gaussian_grad_t grad = {0};
    calls = 0;
    CHECK(tvdb_gaussian_grad_init(&grad, 1, 3) == TVDB_OK);
    total = calls;
    tvdb_gaussian_grad_destroy(&grad);
    for (size_t n = 1; n <= total; ++n) {
        calls = 0;
        fail_at = n;
        CHECK(tvdb_gaussian_grad_init(&grad, 1, 3) == TVDB_ERROR_OUT_OF_MEMORY);
        CHECK(!grad.owns_data);
        tvdb_gaussian_grad_destroy(&grad);
    }
    fail_at = 0;
    CHECK(tvdb_gaussian_grad_init(&grad, 1, 3) == TVDB_OK);
    float dc[64 * 3];
    for (int i = 0; i < 64 * 3; ++i)
        dc[i] = 1;
    calls = 0;
    CHECK(tvdb_gaussian_rasterize_backward(&g, 1, &out, dc, NULL, NULL, 1e-12f, &grad, &err) ==
          TVDB_OK);
    total = calls;
    float saved[9] = {*grad.grad_x,         *grad.grad_y,         *grad.grad_conic_a,
                      *grad.grad_conic_b,   *grad.grad_conic_c,   *grad.grad_opacity,
                      grad.grad_feature[0], grad.grad_feature[1], grad.grad_feature[2]};
    for (size_t n = 1; n <= total; ++n) {
        calls = 0;
        fail_at = n;
        CHECK(tvdb_gaussian_rasterize_backward(&g, 1, &out, dc, NULL, NULL, 1e-12f, &grad, &err) ==
              TVDB_ERROR_OUT_OF_MEMORY);
        float actual[9] = {*grad.grad_x,         *grad.grad_y,         *grad.grad_conic_a,
                           *grad.grad_conic_b,   *grad.grad_conic_c,   *grad.grad_opacity,
                           grad.grad_feature[0], grad.grad_feature[1], grad.grad_feature[2]};
        CHECK(!memcmp(saved, actual, sizeof(saved)));
    }
    fail_at = 0;
    tvdb_gaussian_grad_destroy(&grad);
    tvdb_raster_output_destroy(&out);
    puts("raster allocation failures passed");
    return 0;
}
