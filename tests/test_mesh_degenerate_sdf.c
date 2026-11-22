/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Regression coverage for mesh -> SDF inputs that stress the closest-point
 * kernel: degenerate (zero-area / collinear) faces and very large coordinates.
 * This is a C-side robustness gate, not a Lean differential: the C fallback
 * `mesh_triangle_double` needs double->float32 rounding that core Lean lacks.
 * The Lean twin's unmirrored-stage banner records the same boundary. */
#include "tinyvdb_mesh_conversion.h"
#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x);                                \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)

static int finite_grid(const tvdb_dense_grid *g) {
    for (size_t i = 0; i < (size_t)g->nx * (size_t)g->ny * (size_t)g->nz; ++i)
        if (!isfinite(g->data[i]))
            return 0;
    return 1;
}

static int run_case(const char *name, const tvdb_triangle_mesh *m, float h, float band) {
    tvdb_dense_grid g;
    memset(&g, 0, sizeof(g));
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));
    tvdb_status_t st = tvdb_mesh_to_sdf_ex(m, h, band, NULL, &g, NULL, &err);
    CHECK(st == TVDB_OK);
    CHECK(g.data && g.nx > 0 && g.ny > 0 && g.nz > 0);
    CHECK(finite_grid(&g));
    printf("%s: %dx%dx%d finite values\n", name, g.nx, g.ny, g.nz);
    tvdb_dense_grid_free(&g);
    return 0;
}

int main(void) {
    /* 1. A collapsed slab: all six faces lie in z = 0 and two are zero-area.
     * Normalisation of degenerate faces must not produce NaNs. */
    {
        tvdb_vec3f v[6] = {{-1, -1, 0}, {1, -1, 0}, {1, 1, 0},
                           {-1, 1, 0}, {0, 0, 0},  {0, 0, 0}};
        tvdb_triangle f[8] = {{0, 1, 2}, {0, 2, 3}, {0, 1, 4}, {1, 2, 4},
                              {2, 3, 4}, {3, 0, 4}, {1, 2, 5}, {0, 1, 5}};
        tvdb_triangle_mesh m = {v, 6, 6, f, 8, 8};
        if (run_case("degenerate", &m, 0.25f, 0.5f))
            return 1;
    }

    /* 2. A collinear triangle soup (every face has a zero-length edge). */
    {
        tvdb_vec3f v[4] = {{0, 0, 0}, {1, 0, 0}, {2, 0, 0}, {3, 0, 0}};
        tvdb_triangle f[4] = {{0, 1, 2}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}};
        tvdb_triangle_mesh m = {v, 4, 4, f, 4, 4};
        if (run_case("collinear", &m, 0.25f, 0.5f))
            return 1;
    }

    /* 3. Large coordinates: 1e6 scale with a correspondingly large spacing. */
    {
        const float s = 100000.0f;
        tvdb_vec3f v[8] = {{-s, -s, -s}, {s, -s, -s}, {s, s, -s}, {-s, s, -s},
                           {-s, -s, s},  {s, -s, s},  {s, s, s},  {-s, s, s}};
        tvdb_triangle f[12] = {{0, 2, 1}, {0, 3, 2}, {4, 5, 6}, {4, 6, 7},
                               {0, 4, 7}, {0, 7, 3}, {1, 2, 6}, {1, 6, 5},
                               {0, 1, 5}, {0, 5, 4}, {3, 7, 6}, {3, 6, 2}};
        tvdb_triangle_mesh m = {v, 8, 8, f, 12, 12};
        if (run_case("large_coords", &m, 50000.0f, 100000.0f))
            return 1;
    }

    /* 4. Failure preservation: nonfinite sample and invalid spacing leave the
     * output grid byte-identical. */
    {
        tvdb_vec3f v[3] = {{0, 0, 0}, {1, 0, 0}, {0, 1, 0}};
        tvdb_triangle f[1] = {{0, 1, 2}};
        tvdb_triangle_mesh m = {v, 3, 3, f, 1, 1};
        tvdb_dense_grid g;
        memset(&g, 0, sizeof(g));
        tvdb_dense_grid_init(&g, 4, 4, 4);
        CHECK(g.data);
        for (size_t i = 0; i < 64; ++i)
            g.data[i] = 777.0f;
        tvdb_dense_grid saved = g;

        v[1].x = NAN;
        CHECK(tvdb_mesh_to_sdf_ex(&m, 0.25f, 0.5f, NULL, &g, NULL, NULL) != TVDB_OK);
        CHECK(!memcmp(&g, &saved, sizeof(g)));
        for (size_t i = 0; i < 64; ++i)
            CHECK(g.data[i] == 777.0f);
        v[1].x = 1.0f;

        CHECK(tvdb_mesh_to_sdf_ex(&m, 0.0f, 0.5f, NULL, &g, NULL, NULL) != TVDB_OK);
        CHECK(!memcmp(&g, &saved, sizeof(g)));
        tvdb_dense_grid_free(&g);
    }

    printf("test_mesh_degenerate_sdf: degenerate/collinear/large inputs finite; "
           "failures preserve output\n");
    return 0;
}
