/* All coordinates collide in the initial hash slot. Reordered duplicates and
 * a zero key exercise publication of newly claimed slots across invocations. */
#include "tinyvdb_gpu.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int cuda = argc > 1 && argv[1][0] == 'c';
    tvdb_error_t err = {0};
    tvdb_gpu_context_t *ctx = NULL;
    if (tvdb_gpu_context_create(cuda ? TVDB_GPU_BACKEND_CUDA : TVDB_GPU_BACKEND_VULKAN, 0, &ctx,
                                &err) != TVDB_OK) {
        printf("SKIP: %s\n", err.message);
        return 77;
    }
    if (!cuda && !tvdb_gpu_spirv_available()) {
        tvdb_gpu_context_destroy(ctx);
        puts("SKIP: no generated SPIR-V");
        return 77;
    }
    enum { UNIQUE = 256, POINTS = 512 };
    float points[POINTS * 3], spacing[3] = {1, 1, 1}, origin[3] = {0, 0, 0};
    for (int pass = 0; pass < 32; ++pass) {
        int npoints = pass < 16 ? UNIQUE : POINTS;
        for (int i = 0; i < npoints; ++i) {
            int key = (i * 73 + pass * 41) % UNIQUE;
            points[3 * i] = points[3 * i + 1] = .25f;
            points[3 * i + 2] = 4096.f * key + .25f;
        }
        int32_t *coords = NULL;
        size_t count = 0;
        tvdb_status_t st = tvdb_gpu_voxelize_points_unbounded(ctx, points, (size_t)npoints, spacing,
                                                              origin, &coords, &count, &err);
        int valid = st == TVDB_OK && count == UNIQUE;
        unsigned char seen[UNIQUE] = {0};
        for (size_t i = 0; valid && i < count; ++i) {
            int z = coords[3 * i + 2], key = z / 4096;
            if (coords[3 * i] || coords[3 * i + 1] || z < 0 || z % 4096 || key >= UNIQUE ||
                seen[key])
                valid = 0;
            else
                seen[key] = 1;
        }
        free(coords);
        if (!valid) {
            fprintf(stderr, "hash publication pass %d: status=%d count=%zu expected=%d (%s)\n",
                    pass, (int)st, count, UNIQUE, err.message);
            tvdb_gpu_context_destroy(ctx);
            return 1;
        }
    }
    tvdb_gpu_context_destroy(ctx);
    printf("%s hash publication passed\n", cuda ? "CUDA" : "Vulkan");
    return 0;
}
