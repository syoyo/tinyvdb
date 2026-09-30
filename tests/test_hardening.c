#include "tinyvdb_grid_index.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_ops.h"
#include "tvdb_memory.h"
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #c); ++failures; } } while (0)

static void test_coordinates(void) {
    int32_t active[] = {0,0,0, 2097152,0,0, 0,0,0, INT32_MAX,1,2, INT32_MIN,1,2};
    int32_t query[] = {0,0,0, 2097152,0,0, -2097152,0,0, INT32_MAX,1,2, INT32_MIN,1,2};
    int64_t idx[5]; uint8_t present[5]; int32_t counts[5];
    CHECK(tvdb_ijk_to_index(active, 5, query, 5, idx));
    CHECK(idx[0] == 0 && idx[1] == 1 && idx[2] == -1 && idx[3] == 3 && idx[4] == 4);
    CHECK(tvdb_coords_in_set(active, 5, query, 5, present));
    CHECK(present[0] && present[1] && !present[2] && present[3] && present[4]);
    CHECK(tvdb_neighbor_counts(active, 5, 26, counts));
    for (int i = 0; i < 5; ++i) CHECK(counts[i] == 0);
    CHECK(!tvdb_neighbor_counts(active, 5, 7, counts));
    CHECK(!tvdb_ijk_to_index(NULL, 1, query, 5, idx));
    CHECK(!tvdb_ijk_to_index(active, SIZE_MAX, query, 5, idx));

    float size[3] = {1,1,1}, origin[3] = {0,0,0};
    float points[] = {0,0,0, 2097152,0,0, 0,0,0};
    int32_t *coords = NULL; size_t count = 0;
    CHECK(tvdb_voxelize_points(points, 3, size, origin, &coords, &count));
    CHECK(count == 2 && coords && coords[0] == 0 && coords[3] == 2097152);
    free(coords);
    float bad[] = {NAN, INFINITY, 2147483648.0f}; int32_t converted[3] = {42,42,42};
    tvdb_world_to_ijk(bad, 1, size, origin, converted);
    CHECK(converted[0] == 0 && converted[1] == 0 && converted[2] == 0);
    uint8_t output = 42;
    CHECK(!tvdb_points_in_set(bad, 1, size, origin, active, 5, &output));
    CHECK(output == 42);
    CHECK(!tvdb_voxelize_points(bad, 1, size, origin, &coords, &count));
    CHECK(coords == NULL && count == 0);
    size[0] = NAN;
    CHECK(!tvdb_points_in_set(points, 1, size, origin, active, 5, &output));
}

static void test_sparse(void) {
    tvdb_vec3i ac[] = {{0,0,0}}, bc[] = {{2097152,0,0}};
    float av[] = {-1}, bv[] = {-2};
    tvdb_sparse_grid a = {ac,av,1,0,1,0,0,0}, b = {bc,bv,1,0,1,0,0,0}, out;
    tvdb_sparse_grid_init(&out);
    CHECK(tvdb_csg_union_sparse(&a, &b, 1, &out));
    CHECK(out.count == 2 && out.values[0] == -1 && out.values[1] == -2);
    tvdb_sparse_grid_free(&out);
    tvdb_vec3i edge[] = {{INT32_MAX,0,0}};
    a.coords = edge;
    CHECK(tvdb_dilate_sparse(&a, 1, 1, &out));
    CHECK(out.count == 6);
    tvdb_sparse_grid_free(&out);
    CHECK(tvdb_erode_sparse(&a, 1, &out)); CHECK(out.count == 0);
    tvdb_sparse_grid_free(&out);
    CHECK(!tvdb_sparse_grid_reserve(&a, 2));
    CHECK(tvdb_sparse_grid_reserve(&out, 1));
    out.coords[0] = ac[0]; out.values[0] = av[0]; out.count = 1;
    tvdb_vec3i *saved_coords = out.coords; float *saved_values = out.values;
    CHECK(!tvdb_sparse_grid_reserve(&out, SIZE_MAX));
    CHECK(out.coords == saved_coords && out.values == saved_values && out.capacity == 1 && out.values[0] == -1);
    tvdb_sparse_grid_free(&out);
}

static int cmp_float(const void *a, const void *b) {
    float x = *(const float*)a, y = *(const float*)b;
    return (x > y) - (x < y);
}
static void test_median(void) {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 4, 3, 2);
    float reference[24], old[24], window[27];
    for (int i = 0; i < 24; ++i) g.data[i] = reference[i] = (float)((i * 19) % 23 - 11);
    for (int it = 0; it < 3; ++it) {
        memcpy(old, reference, sizeof(old));
        for (int z = 0; z < 2; ++z) for (int y = 0; y < 3; ++y) for (int x = 0; x < 4; ++x) {
            int n = 0;
            for (int dz = -1; dz <= 1; ++dz) for (int dy = -1; dy <= 1; ++dy) for (int dx = -1; dx <= 1; ++dx) {
                int xx = x+dx, yy = y+dy, zz = z+dz;
                if (xx < 0) xx = 0; if (xx > 3) xx = 3;
                if (yy < 0) yy = 0; if (yy > 2) yy = 2;
                if (zz < 0) zz = 0; if (zz > 1) zz = 1;
                window[n++] = old[(zz*3+yy)*4+xx];
            }
            qsort(window, 27, sizeof(float), cmp_float);
            reference[(z*3+y)*4+x] = window[13];
        }
    }
    tvdb_median_filter(&g, INT_MAX, 1);
    CHECK(g.data[0] == -11);
    tvdb_median_filter(&g, 1, 3);
    CHECK(memcmp(g.data, reference, sizeof(reference)) == 0);
    tvdb_dense_grid_free(&g);
}

static void test_alloc_sizes(void) {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, -1, 2, 2);
    CHECK(!g.data && g.nx == 0);
    tvdb_dense_grid_init(&g, INT_MAX, INT_MAX, INT_MAX);
    CHECK(!g.data && g.nx == 0);
    tvdb_dense_vec_grid v; tvdb_dense_vec_grid_init(&v, INT_MAX, INT_MAX, INT_MAX);
    CHECK(!v.data && v.nx == 0);
    tvdb_dense_grid_d d; tvdb_dense_grid_d_init(&d, INT_MAX, INT_MAX, INT_MAX);
    CHECK(!d.data && d.nx == 0);
    tvdb_arena_allocator_t arena; tvdb_arena_init(&arena, malloc(32), 32);
    CHECK(tvdb_arena_alloc(&arena, 8) != NULL);
    size_t offset = arena.current_offset;
    CHECK(!tvdb_arena_alloc(&arena, SIZE_MAX) && arena.current_offset == offset);
    arena.current_offset = SIZE_MAX;
    CHECK(!tvdb_arena_alloc(&arena, 1) && arena.current_offset == SIZE_MAX);
    tvdb_arena_destroy(&arena);
}
int main(void) {
    test_coordinates(); test_sparse(); test_median(); test_alloc_sizes();
    return failures != 0;
}
