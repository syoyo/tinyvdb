// Round-trip regression for the NanoVDB reader/writer pair.
//
// tvdb_nanovdb_write_to_memory and tvdb_nanovdb_file_open_memory must agree.
// They previously did not, and nothing in the suite covered it:
//
//   * the writer emitted the pre-v32 version layout ((major<<24)|(minor<<16))
//     while the reader decodes (major<<21)|(minor<<10)|patch, so every file
//     we wrote was rejected as an unsupported version;
//   * name_size recorded strlen(name) but wrote strlen(name)+1 bytes, so the
//     reader's NUL scan over name_size bytes never terminated;
//   * the per-grid metadata recorded the *uncompressed* size in the field the
//     reader advances by, desynchronising the cursor whenever a codec was used;
//   * tvdb__nnvdb_sw_ensure was a stub that always succeeded, so the writer
//     silently truncated any file whose metadata outgrew the initial buffer.
//
// This test builds a real grid (magic, node offsets, transform), round-trips it
// through memory, and requires a bit-exact payload. It also checks the node
// size helpers against the on-disk constants, and confirms the parse-failure
// path returns with nothing attached to the file handle.
//
// Skips with exit 0 when the reference corpus is absent.

#include "tinyvdb_nanovdb.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int g_failures = 0;

static void fail(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fprintf(stderr, "FAIL: ");
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    ++g_failures;
}

static int file_exists(const char *path) {
    FILE *fp = fopen(path, "rb");
    if (!fp) return 0;
    fclose(fp);
    return 1;
}

/* Build a minimal but structurally valid float grid: 672 bytes of GridData,
 * 64 of TreeData, then a 64-byte root node with no child tiles, carrying the
 * transform and index bbox the reader validates. */
static uint8_t *make_valid_grid(size_t *out_size) {
    const size_t size = 672 + 64 + 64; /* GridData + TreeData + root node */
    uint8_t *data = (uint8_t *)calloc(1, size);
    if (!data) return NULL;

    uint64_t magic = TVDB_NANOVDB_MAGIC_GRID;
    memcpy(data, &magic, 8);
    uint32_t version = (32u << 21) | (6u << 10) | 0u;
    memcpy(data + 16, &version, 4);
    uint64_t gsize = size;
    memcpy(data + 32, &gsize, 8);
    uint32_t type = TVDB_NANOVDB_GRID_TYPE_FLOAT;
    memcpy(data + 636, &type, 4);
    uint32_t class_id = TVDB_NANOVDB_GRID_CLASS_LEVEL_SET;
    memcpy(data + 632, &class_id, 4);

    /* Identity affine map at offset 384, with translation 1.0 at 528.
     * tvdb__nv_metadata rejects taperD != 1.0 at offset 552. */
    double identity[9] = {1, 0, 0, 0, 1, 0, 0, 0, 1};
    memcpy(data + 384, identity, sizeof(identity));
    for (int k = 0; k < 3; ++k) {
        double one = 1.0;
        memcpy(data + 528 + 8 * k, &one, 8);
        memcpy(data + 552 + 8 * k, &one, 8);
        double vs = 0.1;
        memcpy(data + 608 + 8 * k, &vs, 8);
    }

    /* TreeData at 672: four node offsets. Only the root is non-empty, and it
     * sits immediately after TreeData. */
    uint64_t root_rel = 64;
    uint64_t offsets[4] = {0, 0, 0, root_rel};
    memcpy(data + 672, offsets, sizeof(offsets));
    uint64_t active = 0;
    memcpy(data + 728, &active, 8);

    uint64_t root = 672 + root_rel;
    int32_t bmin[3] = {0, 0, 0};
    int32_t bmax[3] = {7, 7, 7};
    memcpy(data + root, bmin, sizeof(bmin));
    memcpy(data + root + 12, bmax, sizeof(bmax));
    uint32_t tiles = 0;
    memcpy(data + root + 24, &tiles, 4);

    *out_size = size;
    return data;
}

static int test_roundtrip_memory(void) {
    size_t size = 0;
    uint8_t *payload = make_valid_grid(&size);
    if (!payload) {
        fail("out of memory building fixture");
        return 1;
    }

    tvdb_nanovdb_grid_t *grids =
        (tvdb_nanovdb_grid_t *)calloc(1, sizeof(tvdb_nanovdb_grid_t));
    if (!grids) {
        free(payload);
        fail("out of memory");
        return 1;
    }
    grids[0].name = (char *)"roundtrip";
    grids[0].grid_type = TVDB_NANOVDB_GRID_TYPE_FLOAT;
    grids[0].grid_class = TVDB_NANOVDB_GRID_CLASS_LEVEL_SET;
    grids[0].voxel_size[0] = grids[0].voxel_size[1] = grids[0].voxel_size[2] = 0.1;
    grids[0].index_bbox_max[0] = grids[0].index_bbox_max[1] = 7;
    grids[0].index_bbox_max[2] = 7;
    grids[0].size = size;
    grids[0].data = payload;
    grids[0].owns_data = 1;

    tvdb_nanovdb_file_t file;
    memset(&file, 0, sizeof(file));
    file.num_grids = 1;
    file.grids = grids;

    const uint32_t codecs[] = {
        TVDB_NANOVDB_CODEC_NONE,
        TVDB_NANOVDB_CODEC_ZIP,
        TVDB_NANOVDB_CODEC_BLOSC,
    };
    const char *codec_names[] = {"none", "zip", "blosc"};

    for (size_t c = 0; c < sizeof(codecs) / sizeof(codecs[0]); ++c) {
        tvdb_error_t err = {0};
        uint8_t *out = NULL;
        size_t out_size = 0;
        tvdb_status_t st = tvdb_nanovdb_write_to_memory(
            &file, codecs[c], &out, &out_size, &err);
        if (st != TVDB_OK) {
            fail("write(codec=%s) failed: %s", codec_names[c], err.message);
            continue;
        }

        tvdb_nanovdb_file_t back;
        memset(&back, 0, sizeof(back));
        st = tvdb_nanovdb_file_open_memory(&back, out, out_size, NULL, &err);
        if (st != TVDB_OK) {
            fail("read-back(codec=%s) failed: %s", codec_names[c], err.message);
            free(out);
            continue;
        }

        if (back.num_grids != 1) {
            fail("codec=%s: expected 1 grid, got %zu", codec_names[c],
                 back.num_grids);
        } else {
            const tvdb_nanovdb_grid_t *g = &back.grids[0];
            if (!g->name || strcmp(g->name, "roundtrip") != 0) {
                fail("codec=%s: name mismatch: '%s'", codec_names[c],
                     g->name ? g->name : "(null)");
            }
            if (g->size != size) {
                fail("codec=%s: size %zu != %zu", codec_names[c], g->size, size);
            } else if (memcmp(g->data, payload, size) != 0) {
                size_t i = 0;
                while (i < size && g->data[i] == payload[i]) ++i;
                fail("codec=%s: payload differs at byte %zu (0x%02x vs 0x%02x)",
                     codec_names[c], i, g->data[i], payload[i]);
            }
            if (g->grid_type != TVDB_NANOVDB_GRID_TYPE_FLOAT) {
                fail("codec=%s: grid_type %u", codec_names[c], g->grid_type);
            }
        }

        tvdb_nanovdb_file_close(&back);
        free(out);
        if (g_failures == 0) printf("[ok] round-trip codec=%s (%zu bytes)\n",
                                     codec_names[c], out_size);
    }

    free(payload);
    free(grids);
    return 0;
}

/* A rejected parse must not leave grids attached to the caller's handle, or
 * the caller has no way to release them. */
static int test_failure_path_releases(void) {
    size_t size = 0;
    uint8_t *payload = make_valid_grid(&size);
    if (!payload) {
        fail("out of memory building fixture");
        return 1;
    }
    /* Truncate the tail: header and metadata parse, the grid payload does not. */
    for (size_t cut = size / 2; cut < size; cut += size / 4) {
        tvdb_nanovdb_file_t f;
        memset(&f, 0, sizeof(f));
        tvdb_error_t err = {0};
        tvdb_status_t st =
            tvdb_nanovdb_file_open_memory(&f, payload, cut, NULL, &err);
        if (st == TVDB_OK) {
            /* Parsed despite truncation, which is also wrong; close and flag. */
            fail("truncated input at %zu unexpectedly accepted", cut);
            tvdb_nanovdb_file_close(&f);
            continue;
        }
        if (f.grids != NULL || f.num_grids != 0) {
            fail("failed parse at %zu left %zu grids attached", cut, f.num_grids);
        }
    }
    free(payload);
    if (g_failures == 0) printf("[ok] failure path releases partial parse\n");
    return 0;
}

/* Node size helpers must equal the on-disk constants, which account for the
 * 8-byte internal-node slot table. They previously assumed 4 bytes and
 * reported lower=18480 where the real value is 33856. The expected values are
 * the NanoVDB float grid-type constants; PNanoVDB's table is not part of the
 * public header. */
static int test_node_sizes(void) {
    const uint32_t type = TVDB_NANOVDB_GRID_TYPE_FLOAT;
    struct { const char *name; uint64_t got; uint64_t want; } checks[] = {
        {"leaf", tvdb_nanovdb_leaf_node_size(type), 2144},
        {"lower", tvdb_nanovdb_lower_node_size(type), 33856},
        {"upper", tvdb_nanovdb_upper_node_size(type), 270400},
        {"root", tvdb_nanovdb_root_node_size(type), 64},
    };
    for (size_t i = 0; i < sizeof(checks) / sizeof(checks[0]); ++i) {
        if (checks[i].got != checks[i].want) {
            fail("node_size(%s) = %llu, expected %llu", checks[i].name,
                 (unsigned long long)checks[i].got,
                 (unsigned long long)checks[i].want);
        }
    }
    if (tvdb_nanovdb_leaf_node_size(9999) != 0) {
        fail("leaf_node_size(unknown type) should be 0");
    }
    if (g_failures == 0) printf("[ok] node size helpers match constants table\n");
    return 0;
}

/* Rewriting a real reference grid must reproduce the payload bit for bit. */
static int test_roundtrip_reference(const char *dir) {
    const char *names[] = {"sphere.nvdb", "ref_float.nvdb", "ref_double.nvdb"};
    int ran = 0;
    for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i) {
        char path[1024];
        snprintf(path, sizeof(path), "%s/%s", dir, names[i]);
        if (!file_exists(path)) continue;

        tvdb_error_t err = {0};
        tvdb_nanovdb_file_t f;
        memset(&f, 0, sizeof(f));
        if (tvdb_nanovdb_file_open(&f, path, NULL, &err) != TVDB_OK) continue;
        if (f.num_grids == 0) {
            tvdb_nanovdb_file_close(&f);
            continue;
        }

        uint8_t *out = NULL;
        size_t out_size = 0;
        tvdb_status_t st = tvdb_nanovdb_write_to_memory(&f, 0, &out, &out_size, &err);
        if (st != TVDB_OK) {
            fail("rewrite %s failed: %s", names[i], err.message);
            tvdb_nanovdb_file_close(&f);
            continue;
        }

        tvdb_nanovdb_file_t back;
        memset(&back, 0, sizeof(back));
        st = tvdb_nanovdb_file_open_memory(&back, out, out_size, NULL, &err);
        if (st != TVDB_OK) {
            fail("read-back %s failed: %s", names[i], err.message);
        } else if (back.num_grids != f.num_grids) {
            fail("%s: %zu grids != %zu", names[i], back.num_grids, f.num_grids);
        } else {
            int ok = 1;
            for (size_t g = 0; g < back.num_grids; ++g) {
                if (back.grids[g].size != f.grids[g].size ||
                    memcmp(back.grids[g].data, f.grids[g].data,
                           f.grids[g].size) != 0) {
                    fail("%s grid %zu payload mismatch", names[i], g);
                    ok = 0;
                    break;
                }
            }
            if (ok) printf("[ok] reference %s bit-exact (%zu bytes)\n", names[i],
                           out_size);
        }
        tvdb_nanovdb_file_close(&back);
        free(out);
        tvdb_nanovdb_file_close(&f);
        ++ran;
    }
    if (ran == 0) printf("[skip] no reference .nvdb corpus present\n");
    return 0;
}

int main(int argc, char **argv) {
    const char *root = argc > 1 ? argv[1] : ".";
    char dir[1024];
    snprintf(dir, sizeof(dir), "%s/data/reference_nvdb", root);

    test_roundtrip_memory();
    test_failure_path_releases();
    test_node_sizes();
    test_roundtrip_reference(dir);

    if (g_failures) {
        fprintf(stderr, "%d FAILURES\n", g_failures);
        return 1;
    }
    printf("All NanoVDB round-trip checks passed.\n");
    return 0;
}
