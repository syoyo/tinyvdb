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

    printf("\n=== All tests PASSED! ===\n");
    return EXIT_SUCCESS;
}
