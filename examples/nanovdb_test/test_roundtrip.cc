#include <cstdio>
#include <cstdlib>
#include <cstring>
#include "tinyvdb_nanovdb.h"

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;

    printf("=== Testing NanoVDB API ===\n\n");

    printf("Node size calculations:\n");
    printf("  Leaf node (float): %zu bytes\n", (size_t)tvdb_nanovdb_leaf_node_size(TVDB_NANOVDB_GRID_TYPE_FLOAT));
    printf("  Lower node (float): %zu bytes\n", (size_t)tvdb_nanovdb_lower_node_size(TVDB_NANOVDB_GRID_TYPE_FLOAT));
    printf("  Upper node (float): %zu bytes\n", (size_t)tvdb_nanovdb_upper_node_size(TVDB_NANOVDB_GRID_TYPE_FLOAT));
    printf("  Root tile: %zu bytes\n", (size_t)tvdb_nanovdb_root_tile_size());
    printf("  Value size (float): %u bytes\n", tvdb_nanovdb_value_size(TVDB_NANOVDB_GRID_TYPE_FLOAT));
    printf("  Value size (double): %u bytes\n", tvdb_nanovdb_value_size(TVDB_NANOVDB_GRID_TYPE_DOUBLE));
    printf("  Value size (vec3f): %u bytes\n", tvdb_nanovdb_value_size(TVDB_NANOVDB_GRID_TYPE_VEC3F));
    printf("\n");

    printf("Testing grid creation API:\n");
    tvdb_nanovdb_grid_t grid;
    int32_t min_coord[3] = {0, 0, 0};
    int32_t max_coord[3] = {99, 99, 99};

    tvdb_status_t st = tvdb_nanovdb_create_grid(&grid, "TestGrid",
                                                  TVDB_NANOVDB_GRID_TYPE_FLOAT,
                                                  TVDB_NANOVDB_GRID_CLASS_LEVEL_SET,
                                                  min_coord, max_coord, NULL, NULL);
    if (st != TVDB_OK) {
        fprintf(stderr, "Failed to create grid\n");
        return EXIT_FAILURE;
    }
    printf("  Created grid: '%s'\n", grid.name);
    printf("  Grid type: %s\n", tvdb_nanovdb_grid_type_name(grid.grid_type));
    printf("  Grid class: %s\n", tvdb_nanovdb_grid_class_name(grid.grid_class));
    printf("  Index bbox: [(%d,%d,%d), (%d,%d,%d)]\n",
           grid.index_bbox_min[0], grid.index_bbox_min[1], grid.index_bbox_min[2],
           grid.index_bbox_max[0], grid.index_bbox_max[1], grid.index_bbox_max[2]);
    printf("  Nodes: %u leaf, %u lower, %u upper, %u root\n",
           grid.node_count[0], grid.node_count[1], grid.node_count[2], grid.node_count[3]);

    tvdb_nanovdb_destroy_grid(&grid, NULL);
    printf("  Destroyed grid\n\n");

    printf("Testing round-trip with memory buffer:\n");
    tvdb_nanovdb_file_t file;
    memset(&file, 0, sizeof(file));

    file.num_grids = 1;
    file.grids = (tvdb_nanovdb_grid_t *)calloc(1, sizeof(tvdb_nanovdb_grid_t));
    if (!file.grids) {
        fprintf(stderr, "Failed to allocate grid\n");
        return EXIT_FAILURE;
    }

    tvdb_nanovdb_grid_t *g = &file.grids[0];
    g->name = (char *)"TestGrid";
    g->grid_type = TVDB_NANOVDB_GRID_TYPE_FLOAT;
    g->grid_class = TVDB_NANOVDB_GRID_CLASS_LEVEL_SET;
    g->voxel_size[0] = 0.1;
    g->voxel_size[1] = 0.1;
    g->voxel_size[2] = 0.1;
    g->world_bbox_min[0] = 0.0;
    g->world_bbox_min[1] = 0.0;
    g->world_bbox_min[2] = 0.0;
    g->world_bbox_max[0] = 10.0;
    g->world_bbox_max[1] = 10.0;
    g->world_bbox_max[2] = 10.0;
    g->index_bbox_min[0] = 0;
    g->index_bbox_min[1] = 0;
    g->index_bbox_min[2] = 0;
    g->index_bbox_max[0] = 99;
    g->index_bbox_max[1] = 99;
    g->index_bbox_max[2] = 99;
    g->active_voxel_count = 1000;
    g->node_count[0] = 1;
    g->node_count[1] = 1;
    g->node_count[2] = 1;
    g->node_count[3] = 1;
    g->tile_count[0] = 0;
    g->tile_count[1] = 0;
    g->tile_count[2] = 0;
    g->size = 4096;

    g->data = (uint8_t *)malloc(g->size);
    if (!g->data) {
        fprintf(stderr, "Failed to allocate grid data\n");
        free(file.grids);
        return EXIT_FAILURE;
    }
    memset(g->data, 0, g->size);
    g->owns_data = 1;

    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    uint8_t *out_data = NULL;
    size_t out_size = 0;

    printf("Writing to memory...\n");
    st = tvdb_nanovdb_write_to_memory(&file, 0, &out_data, &out_size, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Write failed: %s\n", err.message);
        free(g->data);
        free(file.grids);
        return EXIT_FAILURE;
    }

    printf("Written %zu bytes to memory\n", out_size);

    tvdb_nanovdb_file_t file2;
    memset(&file2, 0, sizeof(file2));

    printf("Reading back...\n");
    st = tvdb_nanovdb_file_open_memory(&file2, out_data, out_size, NULL, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Read failed: %s\n", err.message);
        free(out_data);
        free(g->data);
        free(file.grids);
        return EXIT_FAILURE;
    }

    printf("Successfully read back:\n");
    printf("  Grids: %zu\n", tvdb_nanovdb_grid_count(&file2));
    for (size_t i = 0; i < tvdb_nanovdb_grid_count(&file2); i++) {
        const char *name = tvdb_nanovdb_grid_name(&file2, i);
        uint32_t gtype = tvdb_nanovdb_grid_type(&file2, i);
        uint32_t gclass = tvdb_nanovdb_grid_class(&file2, i);
        printf("  Grid[%zu]: name='%s', type=%s, class=%s, size=%zu\n",
               i, name ? name : "(null)",
               tvdb_nanovdb_grid_type_name(gtype),
               tvdb_nanovdb_grid_class_name(gclass),
               (size_t)file2.grids[i].size);
    }

    free(out_data);
    tvdb_nanovdb_file_close(&file2);
    free(g->data);
    free(file.grids);

    printf("\n=== NanoVDB Tests PASSED! ===\n\n");

    printf("=== Testing Gaussian Splat PLY I/O ===\n\n");

    tvdb_gaussian_splat_t *splat = (tvdb_gaussian_splat_t *)calloc(1, sizeof(tvdb_gaussian_splat_t));
    if (!splat) {
        fprintf(stderr, "Failed to allocate splat\n");
        return EXIT_FAILURE;
    }

    splat->num_gaussians = 3;
    splat->owns_data = 1;
    splat->sh_degree = 0;
    splat->sh_dim = 3;

    splat->means = (float *)malloc(9 * sizeof(float));
    splat->quats = (float *)malloc(12 * sizeof(float));
    splat->log_scales = (float *)malloc(9 * sizeof(float));
    splat->logit_opacities = (float *)malloc(3 * sizeof(float));
    splat->sh_coeffs = (float *)malloc(9 * sizeof(float));

    for (uint32_t i = 0; i < splat->num_gaussians; i++) {
        splat->means[i * 3 + 0] = (float)i;
        splat->means[i * 3 + 1] = (float)i + 0.5f;
        splat->means[i * 3 + 2] = (float)i + 1.0f;
        splat->quats[i * 4 + 0] = 1.0f;
        splat->quats[i * 4 + 1] = 0.0f;
        splat->quats[i * 4 + 2] = 0.0f;
        splat->quats[i * 4 + 3] = 0.0f;
        splat->log_scales[i * 3 + 0] = -0.1f;
        splat->log_scales[i * 3 + 1] = -0.1f;
        splat->log_scales[i * 3 + 2] = -0.1f;
        splat->logit_opacities[i] = 0.5f;
        splat->sh_coeffs[i * 3 + 0] = 1.0f;
        splat->sh_coeffs[i * 3 + 1] = 0.0f;
        splat->sh_coeffs[i * 3 + 2] = 0.0f;
    }

    printf("Created splat with %u Gaussians:\n", tvdb_gaussian_splat_count(splat));
    for (uint32_t i = 0; i < tvdb_gaussian_splat_count(splat); i++) {
        float means[3], quats[4], scales[3], opacity;
        tvdb_gaussian_splat_get(splat, i, means, quats, scales, &opacity);
        printf("  Gaussian %u: pos=(%.2f, %.2f, %.2f), opacity=%.2f\n",
               i, means[0], means[1], means[2], opacity);
    }

    const char *test_ply = "/tmp/test_splat.ply";
    printf("\nSaving to %s...\n", test_ply);
    memset(&err, 0, sizeof(err));
    st = tvdb_gaussian_splat_save(test_ply, splat, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Save failed: %s\n", err.message);
        tvdb_gaussian_splat_destroy(splat);
        return EXIT_FAILURE;
    }
    printf("Saved successfully\n");

    printf("Loading from %s...\n", test_ply);
    tvdb_gaussian_splat_t *loaded = tvdb_gaussian_splat_load(test_ply, &err);
    if (!loaded) {
        fprintf(stderr, "Load failed: %s\n", err.message);
        tvdb_gaussian_splat_destroy(splat);
        return EXIT_FAILURE;
    }
    printf("Loaded %u Gaussians:\n", tvdb_gaussian_splat_count(loaded));
    for (uint32_t i = 0; i < tvdb_gaussian_splat_count(loaded); i++) {
        float means[3], quats[4], scales[3], opacity;
        tvdb_gaussian_splat_get(loaded, i, means, quats, scales, &opacity);
        printf("  Gaussian %u: pos=(%.2f, %.2f, %.2f), opacity=%.2f\n",
               i, means[0], means[1], means[2], opacity);
    }

    tvdb_gaussian_splat_destroy(splat);
    tvdb_gaussian_splat_destroy(loaded);

    printf("\n=== Gaussian Splat Tests PASSED! ===\n\n");

    printf("=== Testing Gaussian Splat CPU Rasterization ===\n\n");

    tvdb_gaussian_splat_t *gs = (tvdb_gaussian_splat_t *)calloc(1, sizeof(tvdb_gaussian_splat_t));
    gs->num_gaussians = 100;
    gs->owns_data = 1;
    gs->means = (float *)malloc(100 * 3 * sizeof(float));
    gs->quats = (float *)malloc(100 * 4 * sizeof(float));
    gs->log_scales = (float *)malloc(100 * 3 * sizeof(float));
    gs->logit_opacities = (float *)malloc(100 * sizeof(float));
    gs->sh_coeffs = (float *)malloc(100 * 3 * sizeof(float));

    for (uint32_t i = 0; i < 100; i++) {
        gs->means[i * 3 + 0] = (float)(i % 10) - 5.0f;
        gs->means[i * 3 + 1] = (float)(i / 10) - 5.0f;
        gs->means[i * 3 + 2] = -10.0f;
        gs->quats[i * 4 + 0] = 1.0f;
        gs->quats[i * 4 + 1] = 0.0f;
        gs->quats[i * 4 + 2] = 0.0f;
        gs->quats[i * 4 + 3] = 0.0f;
        gs->log_scales[i * 3 + 0] = 0.0f;
        gs->log_scales[i * 3 + 1] = 0.0f;
        gs->log_scales[i * 3 + 2] = 0.0f;
        gs->logit_opacities[i] = 0.5f;
        gs->sh_coeffs[i * 3 + 0] = 1.0f;
        gs->sh_coeffs[i * 3 + 1] = 0.5f;
        gs->sh_coeffs[i * 3 + 2] = 0.25f;
    }

    float extrinsics[16] = {
        1, 0, 0, 0,
        0, 1, 0, 0,
        0, 0, -1, 0,
        0, 0, 10, 1
    };
    tvdb_camera_t *cam = tvdb_camera_create_perspective(100.0f, 100.0f, 64.0f, 64.0f,
                                                         128.0f, 128.0f, 0.1f, 100.0f,
                                                         extrinsics);
    printf("Created perspective camera\n");

    uint32_t num_projected = 0;
    tvdb_projected_gaussian_t *proj_gaussians = tvdb_gaussian_project(gs, cam, &num_projected, &err);
    printf("Projected %u Gaussians\n", num_projected);

    uint32_t img_width = 128, img_height = 128;
    float bg[3] = {0.1f, 0.1f, 0.1f};
    tvdb_raster_output_t output;
    memset(&output, 0, sizeof(output));

    st = tvdb_gaussian_rasterize_forward(proj_gaussians, num_projected,
                                          img_width, img_height, 3, bg,
                                          0.001f, &output, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Rasterization failed: %s\n", err.message);
        tvdb_projected_gaussian_destroy(proj_gaussians);
        tvdb_camera_destroy(cam);
        tvdb_gaussian_splat_destroy(gs);
        return EXIT_FAILURE;
    }

    printf("First gaussian: x=%.2f, y=%.2f, radius=%.2f, opacity=%.2f, depth=%.2f\n",
           proj_gaussians[0].x, proj_gaussians[0].y, proj_gaussians[0].radius,
           proj_gaussians[0].opacity, proj_gaussians[0].depth);
    uint32_t center_idx = 55;
    printf("Center gaussian (idx %u): x=%.2f, y=%.2f, radius=%.2f, opacity=%.2f, depth=%.2f\n",
           center_idx,
           proj_gaussians[center_idx].x, proj_gaussians[center_idx].y, proj_gaussians[center_idx].radius,
           proj_gaussians[center_idx].opacity, proj_gaussians[center_idx].depth);
    printf("GS logit_opacity[55] = %.2f\n", gs->logit_opacities ? gs->logit_opacities[55] : -999.0f);
    printf("Rasterized to %ux%u image\n", output.width, output.height);

    size_t center_pixel = ((size_t)img_height / 2) * img_width + (size_t)img_width / 2;
    printf("Center pixel RGBA: (%.3f, %.3f, %.3f, %.3f)\n",
           output.image[center_pixel * 3 + 0],
           output.image[center_pixel * 3 + 1],
           output.image[center_pixel * 3 + 2],
           output.alpha[center_pixel]);

    float sum_alpha = 0.0f;
    for (size_t p = 0; p < (size_t)img_width * img_height; p++) {
        sum_alpha += output.alpha[p];
    }
    printf("Total alpha sum: %.3f\n", sum_alpha);

    tvdb_raster_output_destroy(&output);
    tvdb_projected_gaussian_destroy(proj_gaussians);
    tvdb_camera_destroy(cam);
    tvdb_gaussian_splat_destroy(gs);

    printf("\n=== Rasterization Tests PASSED! ===\n");
    printf("\n=== All Tests PASSED! ===\n");
    return EXIT_SUCCESS;
}
