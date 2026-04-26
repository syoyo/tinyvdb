// Audit scalar writer paths for non-float types (INT32, INT64, DOUBLE).
//
// Strategy: take sphere.vdb as a Tree_float_5_4_3 layout template, retype its
// leaf-level value_type to the audited type, build a small grid of known
// (coord, value) pairs via the typed builder, save it as a .vdb, reload, and
// check that every active voxel reads back the original value.
//
// Rationale: tinyvdb's leaf-buffer reader/writer takes a generic
// (vsize, value_type) pair, so if the FLOAT path round-trips correctly
// (covered by test_grid_from_sparse and many others) and the value_size
// table is right, the same machinery should work for any fixed-width
// scalar type. This test confirms that empirically.
//
// BOOL is intentionally skipped: OpenVDB stores BOOL leaves as a bare
// 64-byte value mask (no separate value array), which our generic
// path doesn't currently special-case. That's a separate fix that
// needs an OpenVDB-produced reference .vdb to validate against.

#include "tinyvdb_io.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_sparse_tree.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails = 0;
#define EXPECT(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fails; } \
} while (0)

// Build a coord+value pair list across multiple leaves; values are deterministic.
typedef struct {
    int32_t  count;
    tvdb_vec3i  coords[64];
    union {
        int32_t  i32_vals[64];
        int64_t  i64_vals[64];
        double   f64_vals[64];
        uint8_t  bool_vals[64];
    };
} test_data_t;

static void make_test_coords(test_data_t *td) {
    int k = 0;
    // 4x4x4 = 64 coords spanning a couple of leaves.
    for (int z = 0; z < 4; ++z)
        for (int y = 0; y < 4; ++y)
            for (int x = 0; x < 4; ++x) {
                td->coords[k].x = x;
                td->coords[k].y = y;
                td->coords[k].z = z;
                ++k;
            }
    td->count = 64;
}

// BOOL note: tinyvdb's internal storage for BOOL is 1 byte per voxel (0 / 1)
// rather than OpenVDB's 1-bit-per-voxel bit-packed buffer. This means BOOL
// .vdb files we write are self-consistent (our reader unpacks them back
// correctly) but NOT byte-compatible with the official OpenVDB format —
// they will fail to load in DCCs. Closing that gap properly needs an
// OpenVDB-produced reference BOOL .vdb to validate against; this test
// only checks self-consistency.

// Run a round-trip for a typed grid and verify every active voxel matches.
//
// Strategy: open sphere.vdb fresh, build our typed grid using its layout
// as template, swap the typed grid into the file in place (replacing the
// float SDF), save. This piggybacks on the file's already-populated
// allocator/header/metadata.
static int run_round_trip(const char *type_name, tvdb_value_type_t value_type,
                          const void *values, const void *background,
                          const char *out_path, const char *tmpl_path,
                          const test_data_t *td) {
    tvdb_file_t f; memset(&f, 0, sizeof(f));
    tvdb_error_t err = {0};
    if (tvdb_file_open(&f, tmpl_path, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: open: %s\n", type_name, err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&f, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: read: %s\n", type_name, err.message);
        tvdb_file_close(&f);
        return 1;
    }
    if (f.num_grids == 0) { tvdb_file_close(&f); return 1; }
    tvdb_grid_t *tmpl = &f.grids[0];

    // Retype template's leaf-level value_type for this audit. (Internal
    // levels share the same value type in OpenVDB layouts.)
    tvdb_grid_t retyped = *tmpl;
    for (int i = 0; i < retyped.tree.layout.num_levels; ++i)
        retyped.tree.layout.levels[i].value_type = value_type;

    tvdb_grid_t built; memset(&built, 0, sizeof(built));
    bool ok = tvdb_grid_from_sparse_typed_using_template(
        &retyped, td->coords, values, (size_t)td->count, value_type,
        background, "audit", &built);
    if (!ok) {
        fprintf(stderr, "FAIL [%s]: builder failed\n", type_name);
        tvdb_file_close(&f);
        return 1;
    }

    // Replace the file's first grid with our built grid (matches the
    // approach in tvdb_py_replace_grid_from_sparse).
    tvdb_grid_destroy_owned(tmpl);
    *tmpl = built;

    if (tvdb_file_save(&f, out_path, TVDB_COMPRESS_NONE, 0, 0, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: save: %s\n", type_name, err.message);
        tvdb_file_close(&f);
        return 1;
    }
    tvdb_file_close(&f);

    // Reload.
    tvdb_file_t f2; memset(&f2, 0, sizeof(f2));
    if (tvdb_file_open(&f2, out_path, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: reopen: %s\n", type_name, err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&f2, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: read: %s\n", type_name, err.message);
        tvdb_file_close(&f2);
        return 1;
    }
    if (f2.num_grids != 1) {
        fprintf(stderr, "FAIL [%s]: expected 1 grid, got %zu\n",
                type_name, f2.num_grids);
        tvdb_file_close(&f2);
        return 1;
    }

    // Walk leaves and look up each test coord; compare to expected value.
    const tvdb_grid_t *g = &f2.grids[0];
    int leaf_lv = g->tree.layout.num_levels - 1;
    int leaf_log2dim = g->tree.layout.levels[leaf_lv].log2dim;
    int leaf_dim = 1 << leaf_log2dim;
    int leaf_dim_mask = leaf_dim - 1;
    size_t vsize = tvdb_value_type_size(value_type);

    int errs = 0;
    for (int i = 0; i < td->count; ++i) {
        int32_t cx = td->coords[i].x, cy = td->coords[i].y, cz = td->coords[i].z;
        int32_t lx = (cx >> leaf_log2dim) << leaf_log2dim;
        int32_t ly = (cy >> leaf_log2dim) << leaf_log2dim;
        int32_t lz = (cz >> leaf_log2dim) << leaf_log2dim;
        int slot = ((cx & leaf_dim_mask) << (2 * leaf_log2dim))
                 | ((cy & leaf_dim_mask) << leaf_log2dim)
                 | (cz & leaf_dim_mask);

        // Find the matching leaf.
        const tvdb_leaf_node_t *leaf = NULL;
        for (size_t n = 0; n < g->tree.num_nodes; ++n) {
            if (g->tree.nodes[n].type != TVDB_NODE_LEAF) continue;
            if (g->tree.nodes[n].origin[0] == lx &&
                g->tree.nodes[n].origin[1] == ly &&
                g->tree.nodes[n].origin[2] == lz) {
                leaf = &g->tree.nodes[n].u.leaf;
                break;
            }
        }
        if (!leaf) { ++errs; continue; }
        if (memcmp(leaf->data + (size_t)slot * vsize,
                   (const uint8_t *)values + (size_t)i * vsize,
                   vsize) != 0) {
            if (errs < 3) {
                fprintf(stderr, "FAIL [%s] coord (%d,%d,%d) value mismatch\n",
                        type_name, cx, cy, cz);
            }
            ++errs;
        }
    }
    tvdb_file_close(&f2);
    if (errs > 0) {
        fprintf(stderr, "FAIL [%s]: %d voxel mismatches\n", type_name, errs);
        return 1;
    }
    printf("[%s] %d voxels round-tripped OK\n", type_name, td->count);
    return 0;
}

int main(int argc, char **argv) {
    const char *tmpl_path = argc > 1 ? argv[1] : "../sphere.vdb";
    const char *out_dir   = argc > 2 ? argv[2] : "/tmp";

    test_data_t td;
    make_test_coords(&td);

    // ---- INT32 ----
    {
        for (int i = 0; i < td.count; ++i) td.i32_vals[i] = i * 17 - 100;
        int32_t bg = -1;
        char path[256];
        snprintf(path, sizeof(path), "%s/audit_int32.vdb", out_dir);
        if (run_round_trip("INT32", TVDB_VALUE_INT32, td.i32_vals, &bg,
                            path, tmpl_path, &td)) ++fails;
    }
    // ---- INT64 ----
    {
        for (int i = 0; i < td.count; ++i) td.i64_vals[i] = (int64_t)i * 1234567 - 99;
        int64_t bg = (int64_t)-1;
        char path[256];
        snprintf(path, sizeof(path), "%s/audit_int64.vdb", out_dir);
        if (run_round_trip("INT64", TVDB_VALUE_INT64, td.i64_vals, &bg,
                            path, tmpl_path, &td)) ++fails;
    }
    // ---- DOUBLE ----
    {
        for (int i = 0; i < td.count; ++i)
            td.f64_vals[i] = (double)i * 0.0001234567890123 - 0.5;
        double bg = 0.0;
        char path[256];
        snprintf(path, sizeof(path), "%s/audit_double.vdb", out_dir);
        if (run_round_trip("DOUBLE", TVDB_VALUE_DOUBLE, td.f64_vals, &bg,
                            path, tmpl_path, &td)) ++fails;
    }
    // ---- BOOL (self-consistency only — 1 byte per voxel; not byte-compat
    // with OpenVDB's bit-packed BOOL leaf format, see comment above) ----
    {
        // Alternating pattern: even indices = 1, odd = 0.
        for (int i = 0; i < td.count; ++i) td.bool_vals[i] = (uint8_t)((i & 1) == 0);
        uint8_t bg = 0;
        char path[256];
        snprintf(path, sizeof(path), "%s/audit_bool.vdb", out_dir);
        if (run_round_trip("BOOL", TVDB_VALUE_BOOL, td.bool_vals, &bg,
                            path, tmpl_path, &td)) ++fails;
    }

    if (fails) { fprintf(stderr, "%d FAILURES\n", fails); return 1; }
    printf("All scalar writer audit tests passed.\n");
    return 0;
}
