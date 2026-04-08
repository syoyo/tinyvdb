/*
 * test_read_vdb.c — Minimal unit test for TinyVDBIO C11 API.
 *
 * Opens a VDB file, reads all grids, and verifies the result is TVDB_OK.
 * Returns EXIT_SUCCESS on success, EXIT_FAILURE on error.
 *
 * Usage: test_read_vdb <input.vdb>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdbio.h"

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <input.vdb>\n", argv[0]);
        return EXIT_FAILURE;
    }

    const char *infile = argv[1];
    tvdb_file_t file;
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    /* Open */
    tvdb_status_t st = tvdb_file_open(&file, infile, NULL, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "FAIL: tvdb_file_open(%s): %s (%s)\n",
                infile, err.message, tvdb_status_string(st));
        return EXIT_FAILURE;
    }

    printf("Opened %s  (version %u, %zu grids)\n",
           infile, file.header.file_version, file.num_grids);

    /* Read all grids */
    st = tvdb_read_all_grids(&file, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "FAIL: tvdb_read_all_grids: %s (%s)\n",
                err.message, tvdb_status_string(st));
        tvdb_file_close(&file);
        return EXIT_FAILURE;
    }

    /* Basic sanity checks */
    if (file.num_grids == 0) {
        fprintf(stderr, "FAIL: expected at least one grid\n");
        tvdb_file_close(&file);
        return EXIT_FAILURE;
    }

    for (size_t i = 0; i < file.num_grids; i++) {
        const tvdb_grid_t *g = &file.grids[i];
        printf("  Grid[%zu]: \"%s\" (%s) — %zu nodes\n",
               i, g->descriptor.grid_name, g->descriptor.grid_type,
               g->tree.num_nodes);
        if (g->tree.num_nodes == 0) {
            fprintf(stderr, "FAIL: grid %zu has zero nodes\n", i);
            tvdb_file_close(&file);
            return EXIT_FAILURE;
        }
    }

    tvdb_file_close(&file);
    printf("PASS\n");
    return EXIT_SUCCESS;
}
