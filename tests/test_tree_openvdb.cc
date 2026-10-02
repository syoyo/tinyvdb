/* Optional reference test. Use a matching installed OpenVDB header/library
 * pair. The default tinyvdb build has no OpenVDB dependency. */
#include "sdf_tree_fixture.h"
#include "tinyvdb_tree_internal.h"
#include <cstdio>
#include <openvdb/openvdb.h>
#include <openvdb/tools/Diagnostics.h>
#include <openvdb/tools/Prune.h>
#include <openvdb/tools/SignedFloodFill.h>
#include <vector>
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            std::fprintf(stderr, "line %d: %s (%s)\n", __LINE__, #x, err.message);                 \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)
static int compare(const tvdb_grid_t *g, const openvdb::FloatGrid &ref, int extent,
                   tvdb_error_t &err) {
    tvdb_tree_diagnostics_t diagnostics;
    CHECK(tvdb_grid_diagnose(g, TVDB_TREE_DIAG_GENERIC, 0, 0, &diagnostics, &err) == TVDB_OK);
    openvdb::tools::Diagnose<openvdb::FloatGrid> diagnose(ref);
    CHECK(diagnostics.valid ==
          diagnose.check(openvdb::tools::CheckFinite<openvdb::FloatGrid>()).empty());
    tvdb_tree_index p;
    CHECK(tvdb_tree_index_create(g, 1, &p, &err) == TVDB_OK);
    auto access = ref.getConstAccessor();
    for (int x = -extent; x <= extent; ++x)
        for (int y = -extent; y <= extent; ++y)
            for (int z = -extent; z <= extent; ++z) {
                int32_t xyz[3] = {x, y, z};
                int active;
                float v = tvdb_tree_get(&p, xyz, &active);
                openvdb::Coord c(x, y, z);
                if (v != access.getValue(c) || !!active != access.isValueOn(c)) {
                    std::fprintf(stderr, "mismatch at %d,%d,%d: tiny=%g/%d reference=%g/%d\n", x, y,
                                 z, v, active, access.getValue(c), access.isValueOn(c));
                    tvdb_tree_index_destroy(&p);
                    return 1;
                }
            }
    CHECK(p.active_voxels == ref.activeVoxelCount());
    tvdb_tree_index_destroy(&p);
    return 0;
}
int main() {
    openvdb::initialize();
    tvdb_error_t err = {};
    tvdb_grid_t tmpl, g = {}, filled = {}, pruned = {};
    sdf_fixture_template(&tmpl);
    auto ref = openvdb::FloatGrid::create(2);
    ref->setGridClass(openvdb::GRID_LEVEL_SET);
    auto access = ref->getAccessor();
    std::vector<tvdb_vec3i> coords;
    std::vector<float> values;
    for (int x = -10; x <= 10; ++x)
        for (int y = -10; y <= 10; ++y)
            for (int z = -10; z <= 10; ++z) {
                float v = std::sqrt(float(x * x + y * y + z * z)) - 6;
                if (std::fabs(v) < 2) {
                    coords.push_back({x, y, z});
                    values.push_back(v);
                    access.setValue(openvdb::Coord(x, y, z), v);
                }
            }
    tvdb_sparse_grid sparse = {coords.data(), values.data(), coords.size(), 0, 1, 0, 0, 0};
    CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sparse, "oracle", 2, &g));
    CHECK(!compare(&g, *ref, 12, err));
    openvdb::tools::signedFloodFillWithValues(ref->tree(), 2.f, -3.f, false);
    CHECK(tvdb_grid_signed_flood_fill(&g, 2, -3, &filled, &err) == TVDB_OK);
    CHECK(!compare(&filled, *ref, 12, err));
    openvdb::tools::prune(ref->tree(), 0.f, false);
    CHECK(tvdb_grid_prune(&filled, &pruned, &err) == TVDB_OK);
    CHECK(!compare(&pruned, *ref, 12, err));
    CHECK(pruned.tree.num_nodes == 1 + ref->tree().nonLeafCount() - 1 + ref->tree().leafCount());
    tvdb_grid_destroy_owned(&pruned);
    tvdb_grid_destroy_owned(&filled);
    tvdb_grid_destroy_owned(&g);
    /* Uniform active voxels collapse to an active tile on both sides. */
    ref = openvdb::FloatGrid::create(0);
    access = ref->getAccessor();
    coords.clear();
    values.clear();
    for (int x = 0; x < 8; ++x)
        for (int y = 0; y < 8; ++y)
            for (int z = 0; z < 8; ++z) {
                coords.push_back({x, y, z});
                values.push_back(1);
                access.setValue(openvdb::Coord(x, y, z), 1);
            }
    sparse.coords = coords.data();
    sparse.values = values.data();
    sparse.count = coords.size();
    CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sparse, "tile", 0, &g));
    CHECK(tvdb_grid_prune(&g, &pruned, &err) == TVDB_OK);
    openvdb::tools::prune(ref->tree(), 0.f, false);
    CHECK(!compare(&pruned, *ref, 10, err));
    tvdb_tree_diagnostics_t d;
    CHECK(tvdb_grid_diagnose(&pruned, TVDB_TREE_DIAG_GENERIC, 0, 0, &d, &err) == TVDB_OK);
    CHECK(d.active_tiles == ref->tree().activeTileCount());
    tvdb_grid_destroy_owned(&pruned);
    tvdb_grid_destroy_owned(&g);
    std::printf("OpenVDB %s maintenance oracle passed\n", OPENVDB_LIBRARY_VERSION_STRING);
    return 0;
}
