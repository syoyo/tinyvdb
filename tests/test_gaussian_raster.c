#include "tinyvdb_nanovdb.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "line %d: %s (%s)\n", __LINE__, #x, err.message);                      \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)
/* Independent pixel compositor: no tile data structure. */
static float reference(const tvdb_projected_gaussian_t *g, int n, int x, int y, float bg,
                       float *alpha) {
    double c = 0, a = 0;
    for (int i = 0; i < n; ++i) {
        double dx = g[i].x - x, dy = g[i].y - y;
        /* Radius bounds select tiles, so evaluate any pixel in those tiles. */
        int tx = x / 16, ty = y / 16;
        if (tx < floor((g[i].x - g[i].radius) / 16) || tx > floor((g[i].x + g[i].radius) / 16) ||
            ty < floor((g[i].y - g[i].radius) / 16) || ty > floor((g[i].y + g[i].radius) / 16))
            continue;
        double sigma =
            .5 * (g[i].conic_a * dx * dx + 2 * g[i].conic_b * dx * dy + g[i].conic_c * dy * dy);
        if (sigma > 10)
            continue;
        double al = g[i].opacity * exp(-sigma), T = 1 - a;
        if (al < 1e-12 || T < .001)
            continue;
        c += g[i].feature[0] * al * T;
        a += al * T;
    }
    *alpha = (float)a;
    return (float)(c + bg * (1 - a));
}
int main(void) {
    tvdb_error_t err = {0};
    tvdb_raster_output_t out = {0};
    float bg[3] = {.3f, .2f, .1f};
    tvdb_projected_gaussian_t g[3] = {{32, 32, .02f, 0, .02f, .8f, 1, 20, {.5f, 0, 0}},
                                      {32, 32, .01f, 0, .01f, .4f, 1, 40, {1, 0, 0}},
                                      {-2, -1, .03f, 0, .03f, .7f, 2, 20, {.2f, 0, 0}}};
    CHECK(tvdb_gaussian_rasterize_forward(g, 3, 65, 65, 1, bg, 1e-12f, &out, &err) == TVDB_OK);
    for (int y = 0; y < 65; ++y)
        for (int x = 0; x < 65; ++x) {
            float a, c = reference(g, 3, x, y, bg[0], &a);
            size_t p = (size_t)y * 65 + x;
            CHECK(fabsf(out.image[p] - c) < 2e-6f && fabsf(out.alpha[p] - a) < 2e-6f);
        }
    tvdb_raster_output_destroy(&out);
    g[0] = (tvdb_projected_gaussian_t){128, 128, .0001f, 0, .0001f, .8f, 1, 160, {1, 0, 0}};
    CHECK(tvdb_gaussian_rasterize_forward(g, 1, 256, 256, 1, NULL, 1e-12f, &out, &err) == TVDB_OK);
    CHECK(out.alpha[136 * 256 + 200] > 0 &&
          out.alpha[136 * 256 + 200] == out.alpha[200 * 256 + 136]);
    tvdb_raster_output_destroy(&out);
    /* Opaque front splat: no divide by residual transmittance in backward. */
    g[0] = (tvdb_projected_gaussian_t){0, 0, 1, 0, 1, 1, 1, 2, {.7f, 0, 0}};
    g[1] = g[0];
    g[1].depth = 2;
    g[1].feature[0] = .9f;
    CHECK(tvdb_gaussian_rasterize_forward(g, 2, 1, 1, 1, bg, 1e-12f, &out, &err) == TVDB_OK);
    tvdb_gaussian_grad_t grad = {0};
    CHECK(tvdb_gaussian_grad_init(&grad, 2, 1) == TVDB_OK);
    float dc = 1, da = .2f;
    CHECK(tvdb_gaussian_rasterize_backward(g, 2, &out, &dc, &da, bg, 1e-12f, &grad, &err) ==
          TVDB_OK);
    CHECK(fabsf(grad.grad_opacity[0] - (.7f - bg[0] + da)) < 1e-6f);
    CHECK(grad.grad_feature[0] == 1 && grad.grad_feature[1] == 0 && grad.grad_opacity[1] == 0);
    /* Numeric failure leaves all existing gradient accumulators intact. */
    dc = NAN;
    CHECK(tvdb_gaussian_rasterize_backward(g, 2, &out, &dc, &da, bg, 1e-12f, &grad, &err) !=
          TVDB_OK);
    CHECK(grad.grad_feature[0] == 1);
    tvdb_gaussian_grad_destroy(&grad);
    tvdb_raster_output_destroy(&out);
    g[0].x = NAN;
    CHECK(tvdb_gaussian_rasterize_forward(g, 1, 1, 1, 1, bg, 1e-12f, &out, &err) != TVDB_OK);
    CHECK(!out.image && !out.alpha && !out.last_ids);
    tvdb_raster_output_destroy(&out);
    g[0].x = 0;
    g[0].conic_b = 2;
    CHECK(tvdb_gaussian_rasterize_forward(g, 1, 1, 1, 1, bg, 1e-12f, &out, &err) != TVDB_OK);
    CHECK(tvdb_gaussian_rasterize_forward(NULL, 0, 1, 1, 4, bg, 1e-12f, &out, &err) != TVDB_OK);
    CHECK(tvdb_gaussian_rasterize_forward(NULL, 0, 1, 1, 1, bg, 1e-12f, &out, &err) == TVDB_OK);
    CHECK(out.image[0] == bg[0] && out.alpha[0] == 0 && out.last_ids[0] == -1);
    tvdb_raster_output_destroy(&out);
    puts("raster contracts passed");
    return 0;
}
