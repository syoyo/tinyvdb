// Round-trip test for tvdb_grid_from_sparse_using_template.
// Loads sphere.vdb, extracts as sparse_grid, builds a fresh grid using
// the loaded one as a template, swaps it into the file, saves, reloads,
// and verifies the active set / value sum match.

#include "tinyvdb_io.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_sparse_tree.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// No-op leaf visitor — used to count leaves.
static int noop_leaf_cb(const tvdb_leaf_view_t *leaf, void *user) {
    (void)leaf; (void)user;
    return 0;
}

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); \
    ++g_failures; } } while (0)

int main(int argc, char **argv) {
    const char *path = argc > 1 ? argv[1] : "../sphere.vdb";

    tvdb_file_t file;
    memset(&file, 0, sizeof(file));
    tvdb_error_t err = {0};
    if (tvdb_file_open(&file, path, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "tvdb_file_open failed: %s\n", err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&file, &err) != TVDB_OK) {
        fprintf(stderr, "tvdb_read_all_grids failed: %s\n", err.message);
        return 1;
    }
    if (file.num_grids == 0) {
        fprintf(stderr, "FAIL: empty file\n");
        return 1;
    }

    const tvdb_grid_t *src = &file.grids[0];
    size_t orig_count = tvdb_grid_active_voxel_count(src);
    printf("[from-sparse] original active count: %zu\n", orig_count);
    EXPECT(orig_count > 0);

    // Extract original to sparse, sum values for later compare.
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    EXPECT(tvdb_grid_to_sparse(src, &sg));
    double orig_sum = 0.0;
    for (size_t i = 0; i < sg.count; ++i) orig_sum += sg.values[i];
    printf("[from-sparse] original value sum: %.4f\n", orig_sum);

    // Build a new grid from sparse, using src as the template.
    tvdb_grid_t built;
    bool ok = tvdb_grid_from_sparse_using_template(src, &sg, "rebuilt",
                                                   /*background=*/0.0f, &built);
    EXPECT(ok);
    if (!ok) { tvdb_sparse_grid_free(&sg); tvdb_file_close(&file); return 1; }

    size_t built_count = tvdb_grid_active_voxel_count(&built);
    printf("[from-sparse] rebuilt active count: %zu\n", built_count);
    EXPECT(built_count == orig_count);

    // Verify the rebuilt grid's sparse extraction matches in sum.
    tvdb_sparse_grid sg_built; tvdb_sparse_grid_init(&sg_built);
    EXPECT(tvdb_grid_to_sparse(&built, &sg_built));
    double built_sum = 0.0;
    for (size_t i = 0; i < sg_built.count; ++i) built_sum += sg_built.values[i];
    printf("[from-sparse] rebuilt value sum:  %.4f\n", built_sum);
    EXPECT(built_sum == orig_sum);  // exact bytes copy → exact sum

    // Save: swap built into file.grids[0] (free original first).
    // Note: file.grids[0] was allocated by the loader; tvdb_file_close will
    // try to free it. We need to ensure ownership. Easiest: keep the loaded
    // grid intact, build a new file_t with grids = &built, then save.
    tvdb_file_t out_file;
    memset(&out_file, 0, sizeof(out_file));
    out_file.header = file.header;
    out_file.alloc = file.alloc;
    out_file.grids = &built;
    out_file.num_grids = 1;

    const char *out_path = "/tmp/_tvdb_rebuilt.vdb";
    if (tvdb_file_save(&out_file, out_path, 0, 0, 0, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: tvdb_file_save: %s\n", err.message);
        ++g_failures;
    } else {
        printf("[from-sparse] saved %s\n", out_path);

        // Reload the saved file and verify.
        tvdb_file_t reload;
        memset(&reload, 0, sizeof(reload));
        if (tvdb_file_open(&reload, out_path, NULL, &err) != TVDB_OK) {
            fprintf(stderr, "FAIL: reload open: %s\n", err.message);
            ++g_failures;
        } else if (tvdb_read_all_grids(&reload, &err) != TVDB_OK) {
            fprintf(stderr, "FAIL: reload read: %s\n", err.message);
            tvdb_file_close(&reload);
            ++g_failures;
        } else {
            EXPECT(reload.num_grids == 1);
            size_t reloaded_count = tvdb_grid_active_voxel_count(&reload.grids[0]);
            printf("[from-sparse] reloaded active count: %zu\n", reloaded_count);
            EXPECT(reloaded_count == orig_count);

            tvdb_sparse_grid sg_reload; tvdb_sparse_grid_init(&sg_reload);
            EXPECT(tvdb_grid_to_sparse(&reload.grids[0], &sg_reload));
            double reload_sum = 0.0;
            for (size_t i = 0; i < sg_reload.count; ++i) reload_sum += sg_reload.values[i];
            printf("[from-sparse] reloaded value sum:  %.4f\n", reload_sum);
            EXPECT(reload_sum == orig_sum);
            tvdb_sparse_grid_free(&sg_reload);
            tvdb_file_close(&reload);
        }
    }

    tvdb_sparse_grid_free(&sg_built);
    tvdb_sparse_grid_free(&sg);
    tvdb_grid_destroy_owned(&built);
    tvdb_file_close(&file);

    // Synthetic test: build a sparse_grid spanning many leaves and verify
    // that the rebuilt grid contains all leaves and active voxels.
    // We simulate "dilate_topology"-like output by enumerating voxel
    // coords spanning a 3x3x3 grid of leaves (origins -8, 0, 8 per axis).
    {
        tvdb_grid_t built2;
        // Reload sphere as template.
        tvdb_file_t f2; memset(&f2, 0, sizeof(f2));
        EXPECT(tvdb_file_open(&f2, path, NULL, &err) == TVDB_OK);
        EXPECT(tvdb_read_all_grids(&f2, &err) == TVDB_OK);
        const tvdb_grid_t *tmpl = &f2.grids[0];

        tvdb_sparse_grid sg2; tvdb_sparse_grid_init(&sg2);
        // Add one voxel per leaf, at slot (0,0,0): the leaf's origin itself.
        // 3*3*3 = 27 coords; expected leaf count = 27.
        EXPECT(tvdb_sparse_grid_reserve(&sg2, 27));
        size_t k = 0;
        for (int xi = -8; xi <= 8; xi += 8) {
            for (int yi = -8; yi <= 8; yi += 8) {
                for (int zi = -8; zi <= 8; zi += 8) {
                    sg2.coords[k].x = xi;
                    sg2.coords[k].y = yi;
                    sg2.coords[k].z = zi;
                    sg2.values[k] = (float)k * 0.1f;
                    ++k;
                }
            }
        }
        sg2.count = 27;

        EXPECT(tvdb_grid_from_sparse_using_template(tmpl, &sg2, "synthetic", 0.0f, &built2));
        size_t synth_count = tvdb_grid_active_voxel_count(&built2);
        size_t synth_leaves = tvdb_grid_visit_leaves_float(&built2, noop_leaf_cb, NULL);
        printf("[from-sparse synthetic] active=%zu leaves=%zu (expect 27 / 27)\n",
               synth_count, synth_leaves);
        EXPECT(synth_count == 27);
        EXPECT(synth_leaves == 27);

        tvdb_sparse_grid_free(&sg2);
        tvdb_grid_destroy_owned(&built2);
        tvdb_file_close(&f2);
    }

    if (g_failures == 0) {
        printf("All tvdb_grid_from_sparse_using_template tests passed.\n");
        return 0;
    }
    printf("%d failures.\n", g_failures);
    return 1;
}
