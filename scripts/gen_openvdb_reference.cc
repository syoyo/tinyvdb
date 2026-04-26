// Generate reference .vdb files using libopenvdb. Each file holds a small
// grid with deterministic active voxels and values, suitable as a
// known-good reference for tinyvdb's reader/writer round-trip tests.
//
// Build (with the OpenVDB build tree in /home/syoyo/work/openvdb):
//
//   g++ -std=c++17 scripts/gen_openvdb_reference.cc \
//     -I/home/syoyo/work/openvdb/openvdb/openvdb \
//     -I/home/syoyo/work/openvdb/build/openvdb/openvdb \
//     -L/home/syoyo/work/openvdb/build/openvdb/openvdb \
//     -lopenvdb -ltbb -lz -lblosc \
//     -o /tmp/gen_openvdb_reference
//
//   LD_LIBRARY_PATH=/home/syoyo/work/openvdb/build/openvdb/openvdb \
//     /tmp/gen_openvdb_reference data/reference/

#include <openvdb/openvdb.h>
#include <openvdb/io/Stream.h>
#include <openvdb/Types.h>

#include <cstdio>
#include <iostream>
#include <string>

template <typename GridT, typename ValueT>
void make_grid(const std::string& path, const std::string& name,
               ValueT background) {
    typename GridT::Ptr g = GridT::create(background);
    g->setName(name);
    auto acc = g->getAccessor();
    // Fill 4x4x4 = 64 active voxels with deterministic pattern.
    int idx = 0;
    for (int z = 0; z < 4; ++z) {
        for (int y = 0; y < 4; ++y) {
            for (int x = 0; x < 4; ++x) {
                ValueT v;
                if constexpr (std::is_same_v<ValueT, bool>) {
                    v = (idx & 1) == 0;
                } else if constexpr (std::is_same_v<ValueT, openvdb::Vec3f>) {
                    v = openvdb::Vec3f(float(x), float(y), float(z));
                } else if constexpr (std::is_floating_point_v<ValueT>) {
                    v = ValueT(idx) * ValueT(0.125) - ValueT(1);
                } else {
                    v = ValueT(idx) * ValueT(7) - ValueT(50);
                }
                acc.setValue(openvdb::Coord(x, y, z), v);
                ++idx;
            }
        }
    }
    openvdb::GridPtrVec grids;
    grids.push_back(g);
    openvdb::io::File file(path);
    // Disable all compression so the on-disk layout is uncompressed and
    // straightforward to parse. (BLOSC + active-mask compression on by
    // default in OpenVDB; turning them off produces larger but simpler
    // files for reference testing.)
    file.setCompression(openvdb::io::COMPRESS_NONE);
    file.write(grids);
    file.close();
    std::cout << "wrote " << path << "  (" << g->activeVoxelCount()
              << " active)" << std::endl;
}

int main(int argc, char** argv) {
    const std::string outdir = (argc > 1) ? argv[1] : ".";

    openvdb::initialize();

    make_grid<openvdb::BoolGrid, bool>(outdir + "/ref_bool.vdb",
                                       "bool_test", false);
    make_grid<openvdb::FloatGrid, float>(outdir + "/ref_float.vdb",
                                          "float_test", 0.5f);
    make_grid<openvdb::DoubleGrid, double>(outdir + "/ref_double.vdb",
                                            "double_test", 0.0);
    make_grid<openvdb::Int32Grid, int32_t>(outdir + "/ref_int32.vdb",
                                            "int32_test", -1);
    make_grid<openvdb::Int64Grid, int64_t>(outdir + "/ref_int64.vdb",
                                            "int64_test", int64_t(-1));
    make_grid<openvdb::Vec3SGrid, openvdb::Vec3f>(
        outdir + "/ref_vec3s.vdb", "vec3s_test",
        openvdb::Vec3f(0.0f, 0.0f, 0.0f));

    return 0;
}
