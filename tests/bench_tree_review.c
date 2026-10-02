/* Common entrypoints allow compiling this harness against the previous
 * revision too. Timings include workspace construction and output allocation. */
#include "sdf_tree_fixture.h"
#include "tinyvdb_nanovdb.h"
#include <stdio.h>
#include <time.h>
static double now(void) {
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return t.tv_sec + t.tv_nsec * 1e-9;
}
int main(int argc, char **argv) {
    int n = argc > 1 ? atoi(argv[1]) : 64;
    unsigned ng = argc > 2 ? (unsigned)atoi(argv[2]) : 4000;
    if (n < 8 || n > 128 || n % 8 || !ng || ng > 100000)
        return 1;
    tvdb_grid_t grid = {0};
    if (!sdf_fixture_cube(&grid, n, 1, 1))
        return 1;
    double best = 1e20, checksum = 0;
    size_t count = 0;
    for (int pass = 0; pass < 4; ++pass) {
        tvdb_sparse_grid out = {0};
        double t = now();
        if (!tvdb_grid_erode_active(&grid, 3, &out))
            return 1;
        t = now() - t;
        if (pass && t < best)
            best = t;
        checksum = 0;
        for (size_t i = 0; i < out.count; ++i)
            checksum += out.values[i];
        count = out.count;
        tvdb_sparse_grid_free(&out);
    }
    printf("erode3 n=%d active=%zu ms=%.3f checksum=%.9g\n", n, count, best * 1000, checksum);
    tvdb_grid_destroy_owned(&grid);
    tvdb_projected_gaussian_t *g = calloc(ng, sizeof(*g));
    if (!g)
        return 1;
    for (unsigned i = 0; i < ng; ++i) {
        g[i] = (tvdb_projected_gaussian_t){8 + 16 * (float)((i * 37) % 16),
                                           8 + 16 * (float)((i * 71 / 16) % 16),
                                           .2f,
                                           0,
                                           .2f,
                                           .03f,
                                           (float)((i * 97) % ng),
                                           1,
                                           {.7f, .4f, .2f}};
    }
    tvdb_error_t err = {0};
    best = 1e20;
    for (int pass = 0; pass < 4; ++pass) {
        tvdb_raster_output_t out = {0};
        double t = now();
        if (tvdb_gaussian_rasterize_forward(g, ng, 256, 256, 3, NULL, 1e-12f, &out, &err) !=
            TVDB_OK)
            return 1;
        t = now() - t;
        if (pass && t < best)
            best = t;
        checksum = 0;
        for (size_t i = 0; i < 256 * 256 * 3; ++i)
            checksum += out.image[i];
        tvdb_raster_output_destroy(&out);
    }
    printf("raster gaussians=%u image=256x256 ms=%.3f checksum=%.9g\n", ng, best * 1000, checksum);
    free(g);
    return 0;
}
