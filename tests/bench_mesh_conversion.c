/* Self-contained performance inputs. Optional legacy-only compilation allows
 * the same harness to link a saved pre-change library for fair comparisons. */
#include "tinyvdb_mesh.h"
#ifndef TVDB_BENCH_LEGACY
#include "tinyvdb_mesh_conversion.h"
#endif
#include <math.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
static double now(void) {
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return t.tv_sec + t.tv_nsec * 1e-9;
}
int main(int argc, char **argv) {
    int n = argc > 1 ? atoi(argv[1]) : 64, checker = argc > 2 ? atoi(argv[2]) : 0;
    if (n < 8 || n > 256)
        return 1;
    tvdb_dense_grid g = {0};
    tvdb_dense_grid_init(&g, n, n, n);
    if (!g.data)
        return 1;
    g.ox = g.oy = g.oz = -1;
    g.voxel_size = 2.f / n;
    for (int z = 0; z < n; ++z)
        for (int y = 0; y < n; ++y)
            for (int x = 0; x < n; ++x) {
                float a = -1 + (x + .5f) * g.voxel_size, b = -1 + (y + .5f) * g.voxel_size,
                      c = -1 + (z + .5f) * g.voxel_size;
                g.data[((size_t)z * n + y) * n + x] =
                    checker ? (((x + y + z) & 1) ? -1 : 1) : sqrtf(a * a + b * b + c * c) - .7f;
            }
    tvdb_triangle_mesh mesh = {0};
    double best = 1e20;
    for (int i = 0; i < 4; ++i) {
        tvdb_triangle_mesh_free(&mesh);
        double t = now();
        if (!tvdb_sdf_to_mesh(&g, 0, &mesh, NULL))
            return 1;
        t = now() - t;
        if (i && t < best)
            best = t;
    }
    printf("n=%d checker=%d mc_ms=%.3f vertices=%zu faces=%zu capacity_bytes=%zu\n", n, checker,
           best * 1e3, mesh.vertex_count, mesh.face_count,
           mesh.vertex_capacity * sizeof(tvdb_vec3f) + mesh.face_capacity * sizeof(tvdb_triangle));
    if (checker) {
        tvdb_triangle_mesh_free(&mesh);
        tvdb_dense_grid_free(&g);
        return 0;
    }
    /* Legacy table points inward. Reverse it for negative-inside voxelization. */
    for (size_t i = 0; i < mesh.face_count; ++i) {
        uint32_t k = mesh.faces[i].v1;
        mesh.faces[i].v1 = mesh.faces[i].v2;
        mesh.faces[i].v2 = k;
    }
    double legacy = 1e20;
    tvdb_dense_grid out = {0};
    for (int i = 0; i < 4; ++i) {
        tvdb_dense_grid_free(&out);
        double t = now();
        if (!tvdb_mesh_to_sdf(&mesh, g.voxel_size, 3 * g.voxel_size, &out, NULL))
            return 1;
        t = now() - t;
        if (i && t < legacy)
            legacy = t;
    }
    printf("mesh_to_sdf_default_ms=%.3f voxels=%zu\n", legacy * 1e3,
           (size_t)out.nx * out.ny * out.nz);
#ifndef TVDB_BENCH_LEGACY
    tvdb_mesh_sdf_t *w = NULL;
    double t = now();
    if (tvdb_mesh_sdf_create(&mesh, &w, NULL) != TVDB_OK)
        return 1;
    double build = now() - t;
    tvdb_mesh_sdf_info_t info;
    tvdb_mesh_sdf_info(w, &info);
    for (size_t workers = 1; workers <= 8; workers *= 8) {
        tvdb_thread_pool_t *pool = NULL;
        if (tvdb_thread_pool_create(workers, &pool, NULL) != TVDB_OK)
            return 1;
        best = 1e20;
        for (int i = 0; i < 4; ++i) {
            t = now();
            if (tvdb_mesh_sdf_generate(w, g.voxel_size, 3 * g.voxel_size, pool, &out, NULL, NULL) !=
                TVDB_OK)
                return 1;
            t = now() - t;
            if (i && t < best)
                best = t;
        }
        printf("backend=%s workers=%zu mesh_sdf_reuse_ms=%.3f bvh_build_ms=%.3f "
               "acceleration_bytes=%zu\n",
               tvdb_thread_backend_name(), tvdb_thread_pool_size(pool), best * 1e3, build * 1e3,
               info.acceleration_bytes);
        tvdb_thread_pool_destroy(pool);
    }
    tvdb_mesh_sdf_destroy(w);
#endif
    tvdb_dense_grid_free(&out);
    tvdb_triangle_mesh_free(&mesh);
    tvdb_dense_grid_free(&g);
    return 0;
}
