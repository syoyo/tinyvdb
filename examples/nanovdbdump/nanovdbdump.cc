#include <cstdio>
#include <cstdlib>
#include <cstring>
#include "tinyvdb_nanovdb.h"

static const char *codec_name(uint16_t codec) {
    switch (codec) {
        case TVDB_NANOVDB_CODEC_NONE:  return "none";
        case TVDB_NANOVDB_CODEC_ZIP:   return "zip";
        case TVDB_NANOVDB_CODEC_BLOSC: return "blosc";
        default:                        return "unknown";
    }
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <input.nvdb> [--verbose]\n", argv[0]);
        return EXIT_FAILURE;
    }

    const char *infile = argv[1];
    int verbose = (argc > 2 && strcmp(argv[2], "--verbose") == 0);

    tvdb_nanovdb_file_t file;
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    tvdb_status_t st = tvdb_nanovdb_file_open(&file, infile, NULL, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Error opening %s: %s\n", infile, err.message);
        return EXIT_FAILURE;
    }

    printf("File: %s\n", infile);
    printf("  NanoVDB version: %u\n", file.version);
    printf("  Grids: %zu\n", tvdb_nanovdb_grid_count(&file));
    printf("  Codec: %s\n", codec_name(file.codec));

    for (size_t i = 0; i < tvdb_nanovdb_grid_count(&file); i++) {
        const char *name = tvdb_nanovdb_grid_name(&file, i);
        uint32_t grid_type = tvdb_nanovdb_grid_type(&file, i);
        uint32_t grid_class = tvdb_nanovdb_grid_class(&file, i);
        double voxel_size = tvdb_nanovdb_grid_voxel_size(&file, i, 0);

        printf("\nGrid[%zu]: \"%s\"\n", i, name ? name : "(unnamed)");
        printf("  Type: %s\n", tvdb_nanovdb_grid_type_name(grid_type));
        printf("  Class: %s\n", tvdb_nanovdb_grid_class_name(grid_class));

        const tvdb_nanovdb_grid_t *g = &file.grids[i];
        printf("  Grid size: %zu bytes\n", (size_t)g->size);
        printf("  Voxel size: (%.6g, %.6g, %.6g)\n",
               g->voxel_size[0], g->voxel_size[1], g->voxel_size[2]);
        printf("  World bbox: [(%.6g, %.6g, %.6g), (%.6g, %.6g, %.6g)]\n",
               g->world_bbox_min[0], g->world_bbox_min[1], g->world_bbox_min[2],
               g->world_bbox_max[0], g->world_bbox_max[1], g->world_bbox_max[2]);
        printf("  Index bbox: [(%d, %d, %d), (%d, %d, %d)]\n",
               g->index_bbox_min[0], g->index_bbox_min[1], g->index_bbox_min[2],
               g->index_bbox_max[0], g->index_bbox_max[1], g->index_bbox_max[2]);
        printf("  Active voxels: %zu\n", (size_t)g->active_voxel_count);
        printf("  Nodes: %u leaf, %u lower, %u upper\n",
               g->node_count[0], g->node_count[1], g->node_count[2]);
        printf("  Tiles: %u level0, %u level1, %u level2\n",
               g->tile_count[0], g->tile_count[1], g->tile_count[2]);

        if (verbose) {
            printf("  Tree offsets: root=%ld, leaf=%ld, lower=%ld, upper=%ld\n",
                   (long)g->root_data_offset,
                   (long)g->leaf_data_offset,
                   (long)g->lower_data_offset,
                   (long)g->upper_data_offset);
        }
    }

    tvdb_nanovdb_file_close(&file);

    printf("\nOK\n");
    return EXIT_SUCCESS;
}
