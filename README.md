# TinyVDB, lightweight C/C++ VDB library

[![PyPI](https://img.shields.io/pypi/v/tinyvdb)](https://pypi.org/project/tinyvdb/)

TinyVDB provides lightweight C/C++ libraries for working with OpenVDB data. It includes VDB file I/O, mesh-to-SDF conversion, grid operations, and more — without depending on the full OpenVDB library.

TinyVDB is suitable for genAI, graphics applications, HPC visualization tools, physics simulation, and any project that needs lightweight VDB functionality.

## Modules

All public APIs are pure-C11 with `extern "C"` linkage (consumable from
C and C++).

| Header | Description |
|--------|-------------|
| `tinyvdb_io.h` | OpenVDB read/write with custom allocator + mmap support |
| `tinyvdb_nanovdb.h` | NanoVDB read/write, hierarchical accessor, trilinear sampler, CRC32, Gaussian-splat rasterizer (CPU forward+backward) |
| `tinyvdb_to_nanovdb.c` | VDB → NanoVDB FloatGrid converter (byte-compatible with libnanovdb) |
| `tinyvdb_mesh.h` | Mesh ↔ SDF, marching cubes, manifold preprocessing |
| `tinyvdb_ops.h` | Dense ops: morphology, filtering, CSG, differential operators, Poisson PCG, advection, fast sweeping, fp64 variants |
| `tinyvdb_sample.h` / `tinyvdb_tsdf.h` | Trilinear sampling/splatting; depth-frame TSDF fusion (single-frame and in-place multi-frame) |
| `tinyvdb_topology.h` / `tinyvdb_ray.h` | Coarsen / refine / prune / clip / merge / pool; Amanatides–Woo DDA, ray-cast SDF, segments-along-ray, batched marching cubes |
| `tinyvdb_sparse.h` / `tinyvdb_sparse_tree.h` | Flat sparse-grid representation (hash-based CSG/morphology, sparse 3D conv); operations on a loaded `tvdb_grid_t` (leaf iter, dilate/erode active or topology, tree-aware CSG, from-scratch rebuilders) |
| `tinyvdb_autograd.h` | Per-op CPU VJPs (sample, splat, CSG, sparse_conv3d) — framework-free |
| `tinyvdb_simd.h` | Optional SSE4.2/AVX2/F16C primitives gated on `TINYVDB_SIMD` |
| `tinyvdb_gpu.h` | Optional runtime-loaded GPU backend: Vulkan and CUDA kernels for analytic sphere/box/torus SDF generation, dense CSG, dense trilinear batch sampling, and same-topology sparse conv3d |

## Features

### I/O (`tinyvdb_io.h`)

* [x] Dependency-free C11 code (header-only, single file)
* [x] Custom memory allocator interface (arena/pool allocator friendly)
* [x] mmap-based file access with heap-buffer fallback
* [x] UTF-8 path support on all platforms (Windows WideChar + long path `\\?\` prefix)
* [x] Cross-platform (Linux, macOS, Windows)
* [x] Big endian support (e.g., Power, SPARC)
* [x] Read and write OpenVDB files (version 220 to 225)
* [x] Multiple grid/tree topologies (not limited to `Tree_float_5_4_3`)
* [x] ZIP compression (via bundled miniz or system zlib)
* [x] BLOSC compression (built-in for OpenVDB `.vdb` files via bundled LZ4; NanoVDB BLOSC needs system libblosc — see `TINYVDB_USE_SYSTEM_BLOSC`)
* [x] Active mask compression (per-node flags 0-6)
* [x] Half-float (FP16) grid support
* [x] PointIndexGrid (`Tree_ptidx32_*`) leaf payload read/write
* [x] PointDataGrid (`Tree_ptdataidx32_*`) topology read + opaque point payload round-trip

### NanoVDB I/O (`tinyvdb_nanovdb.h`)

* [x] Read and write NanoVDB files (version 32+)
* [x] All standard grid types (Float, Double, Vec3f, Int32, …)
* [x] Compressed files: ZIP via miniz/zlib; **BLOSC** via system libblosc
  (opt-in `TINYVDB_USE_SYSTEM_BLOSC=ON`) — verified on
  `nanovdb_convert --blosc` output
* [x] Real Root → Upper → Lower → Leaf hierarchical accessor
  (`tvdb_nanovdb_get_voxel_f` / `_d`) — backed by vendored
  `nanovdb::PNanoVDB.h` (Apache-2.0)
* [x] Trilinear sampler (`tvdb_nanovdb_sample_trilinear_f`,
  cell-center convention)
* [x] Active-voxel test (`tvdb_nanovdb_is_voxel_active`) consults the
  real leaf value mask
* [x] CRC32 checksum compute / validate
  (`tvdb_nanovdb_compute_head_checksum`, `_compute_tail_checksum`,
  `_validate_checksum`) — head + 4KB-blocked tail, matches
  `nanovdb::tools::GridChecksum` byte-for-byte
* [x] **VDB → NanoVDB FloatGrid builder** (`tvdb_grid_to_nanovdb_float`)
  — converts a loaded `Tree_float_5_4_3` `tvdb_grid_t` into an
  in-memory NanoVDB byte buffer that passes `nanovdb_validate`
* [x] World ↔ index transforms (`tvdb_nanovdb_index_to_world` /
  `_world_to_index`) with adjugate-determinant inverse for
  rotation+scale+translation maps
* [x] Endianness handling, memory buffer I/O, node-size utilities

### Mesh (`tinyvdb_mesh.h`)

* [x] Triangle mesh to signed distance field (dense 3D grid)
* [x] SDF to triangle mesh (marching cubes)
* [x] Manifold preprocessing (mesh to SDF to mesh round-trip)
* [x] Configurable sign determination (flood fill or sweep)

### Grid operations (`tinyvdb_ops.h` + sibling headers)

* [x] Morphological dilation / erosion / open / close (dense, sparse,
  and tree-aware variants — `dilate_active` / `dilate_topology`)
* [x] Gaussian, mean, and Laplacian SDF filtering (dense + sparse)
* [x] CSG union / intersection / difference (dense, sparse, tree-aware)
* [x] Surface area and volume measurement
* [x] Differential operators: gradient, divergence, Laplacian, curl
* [x] Finite-difference stencils: central / forward / backward
* [x] Semi-Lagrangian advection (RK2)
* [x] Poisson solver (preconditioned conjugate gradient; fp32 + fp64)
* [x] Fast sweeping (Eikonal redistance, sign-preserving)
* [x] Ray-SDF intersection (sphere tracing); voxel-walk DDA;
  segments-along-ray; uniform ray samples
* [x] Trilinear sampling and splatting (single + batched, world↔voxel
  transforms); TSDF fusion (depth + RGB)
* [x] Topology ops: coarsen / refine / prune / clip / merge / max-pool /
  avg-pool
* [x] Sparse 3D convolution (single + multi-channel, hash-based O(1)
  neighbor lookup)
* [x] Volume to spheres (greedy adaptive sphere packing)
* [x] Particles to SDF (sphere stamping)
* [x] Level-set fracture (cutter-based volume splitting)
* [x] CPU autograd: per-op VJPs for sample, splat, CSG, and
  sparse_conv3d — gradient-checked against finite differences

### GPU backend (`tinyvdb_gpu.h`)

* [x] Optional `tinyvdb_gpu` C target (`TINYVDB_BUILD_GPU=ON`) with no
  compile-time Vulkan SDK, CUDA SDK, `vulkan.h`, `cuda.h`, `nvcc`, or SDK
  library requirement.
* [x] Runtime-loaded Vulkan compute backend (`libvulkan` / `vulkan-1.dll`)
  using local ABI definitions and SPIR-V kernels generated at build time when
  `glslangValidator` and `xxd` are available.
* [x] Runtime-loaded CUDA Driver API + NVRTC backend (`libcuda`/`nvcuda.dll`
  plus `libnvrtc`) that compiles kernels to PTX at runtime.
* [x] Blocking high-level C entrypoints for analytic sphere/box/torus SDF generation,
  dense CSG, dense trilinear batch sampling, and same-topology
  `tvdb_sparse_conv3d` on Vulkan and CUDA.
* [x] Vulkan sparse 3D image capability is reported in the context info field.
  Dense sampling has experimental regular and sparse-resident Vulkan
  `sampler3D` paths benchmarked against the default SSBO sampler, plus a
  persistent partial-residency path that binds only pages containing active
  sparse voxels, reuses sampler dispatch resources across queries, and supports
  device-resident query batches with batch-owned async submit/poll/wait.

### Gaussian-splat rasterizer (`tinyvdb_nanovdb.h`)

* [x] CPU forward (`tvdb_gaussian_rasterize_forward`): per-tile
  depth-sorted alpha blend with fast tile binning
* [x] CPU backward (`tvdb_gaussian_rasterize_backward`): analytic
  gradients w.r.t. each gaussian's projected x/y, conic_a/b/c,
  opacity, and per-feature color — reverses the alpha blend without
  saving per-pixel intersection lists. Gradient-checked against
  central FD for all parameters
* [x] PLY I/O for splat scenes (load + save)

## Validation

tinyvdb is cross-validated against libopenvdb 13.0 + libnanovdb 32.9 in
the test suite (build with `-DTINYVDB_BUILD_TESTS=ON` and run `ctest`):

* **VDB**: 6-type reference corpus generated by libopenvdb
  (`scripts/gen_openvdb_reference.cc`) — `bool`, `float`, `double`,
  `int32`, `int64`, `vec3s` — round-trips through tinyvdb's
  reader/writer and the tinyvdb-written output reads back successfully
  in libopenvdb's `vdb_print`. Real `.vdb` corpus (sphere v224 BLOSC,
  bunny/cube/smoke v222 half-precision FLOAT) round-trips bit-exact
  (drift < 1e-10 for 5.5M-voxel bunny).
* **NanoVDB**: corpus generated by `nanovdb_convert` round-trips
  through tinyvdb's hierarchical accessor, trilinear sampler, and
  CRC32 head + 4KB-blocked tail validator (matches
  `nanovdb::tools::GridChecksum` byte-for-byte).
* **VDB → NanoVDB**: `tvdb_grid_to_nanovdb_float` produces NanoVDB
  buffers that `nanovdb_validate` accepts (exit 0) and
  `nanovdb_convert` reads back into a valid `Tree_float_5_4_3` `.vdb`
  with matching topology and value range.
* **Gaussian-splat rasterizer**: backward-pass gradients are
  gradient-checked against central finite differences for every
  parameter.
* **GPU backend**: when a Vulkan runtime/device is available,
  `test_gpu_backend` compares GPU analytic sphere/box/torus SDF generation, dense CSG,
  dense sampling, and sparse conv3d against the CPU implementations. The test
  skips cleanly when no runtime backend is available. Set
  `TVDB_GPU_TEST_VRAM_MB=1024` or `2048` for the opt-in larger Vulkan
  sparse-image benchmark; the planner treats this as a hard ceiling and uses a
  conservative fraction of it to avoid exhausting shared 8 GiB GPUs.

The test suite has 19 ctest targets when optional GPU tests are enabled — see
`tasks.md` for the full table.

## Supported VDB versions

| Version | Feature |
|---------|---------|
| 220 | Selective compression |
| 221 | Float frustum bbox |
| 222 | Node mask compression, per-grid compression flags |
| 223 | BLOSC compression, point index grid |
| 224 | Multipass I/O |
| 225 | Half-float grid type |

## How to use

### I/O library

Copy `src/tinyvdb_io.h`, `src/miniz.c`, `src/miniz.h`, `src/lz4.c`, and `src/lz4.h` to your project. BLOSC compression (LZ4) is built-in — no external dependency needed.

```c
/* In exactly one .c or .cc file: */
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"
```

#### Reading a VDB file

```c
tvdb_file_t file;
tvdb_error_t err = {0};

tvdb_status_t st = tvdb_file_open(&file, "input.vdb", NULL, &err);
if (st != TVDB_OK) { /* handle error */ }

st = tvdb_read_all_grids(&file, &err);
if (st != TVDB_OK) { /* handle error */ }

for (size_t i = 0; i < tvdb_grid_count(&file); i++) {
    printf("Grid: %s  Type: %s\n",
           tvdb_grid_name(&file, i),
           tvdb_grid_type_name(&file, i));
}

tvdb_file_close(&file);
```

#### Writing a VDB file

```c
/* After reading/modifying a file, write it back: */
tvdb_status_t st = tvdb_file_save(&file, "output.vdb",
                                  TVDB_COMPRESS_BLOSC | TVDB_COMPRESS_ACTIVE_MASK,
                                  /*use_mmap=*/0, &err);
```

Or write to a memory buffer:

```c
uint8_t *data = NULL;
size_t data_size = 0;
tvdb_status_t st = tvdb_write_to_memory(&file,
                                        TVDB_COMPRESS_ZIP | TVDB_COMPRESS_ACTIVE_MASK,
                                        &data, &data_size, &err);
/* ... use data ... */
free(data);
```

### NanoVDB I/O library

```c
/* In exactly one .c or .cc file: */
#define TINYVDB_NANOVDB_IMPLEMENTATION
#include "tinyvdb_nanovdb.h"
```

#### Reading a NanoVDB file

```c
tvdb_nanovdb_file_t file;
tvdb_error_t err;
memset(&err, 0, sizeof(err));

tvdb_status_t st = tvdb_nanovdb_file_open(&file, "input.nvdb", NULL, &err);
if (st != TVDB_OK) { /* handle error */ }

for (size_t i = 0; i < tvdb_nanovdb_grid_count(&file); i++) {
    printf("Grid: %s  Type: %s\n",
           tvdb_nanovdb_grid_name(&file, i),
           tvdb_nanovdb_grid_type_name(tvdb_nanovdb_grid_type(&file, i)));
}

tvdb_nanovdb_file_close(&file);
```

#### Custom allocator

```c
tvdb_allocator_t alloc = {
    .malloc_fn  = my_malloc,
    .realloc_fn = my_realloc,
    .free_fn    = my_free,
    .user_ctx   = my_arena
};

tvdb_file_open(&file, "input.vdb", &alloc, &err);
```

The allocator passes `old_size` to `realloc_fn` and `size` to `free_fn`, enabling arena/pool allocators that don't track allocation sizes internally.

### Mesh library

Include `tinyvdb_mesh.h` and compile/link `src/tinyvdb_mesh.c`.

```cpp
// Mesh to SDF
tvdb_mesh::DenseGrid grid;
tvdb_mesh::MeshToSDF(mesh, voxel_size, band_width, &grid);

// SDF to mesh (marching cubes)
tvdb_mesh::TriangleMesh output;
tvdb_mesh::SDFToMesh(grid, 0.0f, &output);

// Manifold preprocessing (mesh -> SDF -> mesh round-trip)
tvdb_mesh::MakeManifold(input, resolution, isovalue, &output);
```

### Grid operations

Include `tinyvdb_ops.h` and compile/link `src/tinyvdb_ops.c` (plus the
sibling `.c` files for the ops you use; see CMake's
`tinyvdb_mesh_ops` target for the canonical list).

```cpp
// CSG union of two SDF grids
tvdb_ops::CSGUnion(grid_a, grid_b, &result);

// Gaussian smoothing
tvdb_ops::GaussianFilter(&grid, /*width=*/1, /*iterations=*/3);

// Ray-SDF intersection
tvdb_ops::RayHit hit;
if (tvdb_ops::RayCastSDF(grid, origin, dir, max_t, &hit)) {
    // hit.position, hit.normal, hit.t
}
```

## Compile-time defines

| Define | Description |
|--------|-------------|
| `TVDB_USE_SYSTEM_ZLIB` | Use system zlib instead of bundled miniz |
| `TVDB_HAVE_BLOSC` | Route NanoVDB BLOSC decompression through system libblosc (set automatically by `TINYVDB_USE_SYSTEM_BLOSC=ON`) |
| `TVDB_USE_ZSTD` | Enable ZSTD inside BLOSC frames |
| `TVDB_NO_MMAP` | Disable mmap; always read into heap buffer |

## CMake build

CMake build is provided for example/test builds.

### Setup

```
$ git submodule update --init --recursive --depth 1
```

### Build

```
$ mkdir build
$ cd build
$ cmake ..
$ make
```

### CMake options

| Option | Default | Description |
|--------|---------|-------------|
| `TINYVDB_BUILD_TESTS` | `OFF` | Build the 15-target ctest suite |
| `TINYVDB_BUILD_EXAMPLES` | `ON` | Build `vdbdump`, `nanovdbdump`, etc. |
| `TINYVDB_BUILD_VDBRENDER` | `ON` | Build the vdbrender volume path tracer |
| `TINYVDB_BUILD_PYTHON` | `OFF` | Build Python extension |
| `TINYVDB_USE_SYSTEM_ZLIB` | `OFF` | Use system zlib instead of bundled miniz |
| `TINYVDB_USE_ZSTD` | `ON` | Enable ZSTD inside BLOSC frames (bundled or system) |
| `TINYVDB_USE_SYSTEM_ZSTD` | `OFF` | Link system libzstd instead of `deps/zstd.c` |
| `TINYVDB_USE_SYSTEM_BLOSC` | `OFF` | Link system libblosc — required to read NanoVDB BLOSC files produced by libnanovdb |
| `TINYVDB_OPENMP` | `OFF` | Enable OpenMP parallelism in dense ops, Poisson CG, sparse conv, sample batches, TSDF fusion |
| `TINYVDB_SIMD` | `ON` | Enable SSE4.2/AVX2/F16C (x86-64 only; scalar fallback otherwise) |

## vdbdump example

A command-line tool that reads a VDB file and prints its structure:

```
$ ./vdbdump input.vdb --verbose
File: input.vdb
  VDB version: 224  (lib 6.2)
  UUID: 1569c382-d056-4c66-aa3e-9b0ca351fe91
  Grids: 1

Grid[0]: "surface"
  Type: Tree_float_5_4_3
  Tree: 4 levels [Root, Internal(log2dim=5), Internal(log2dim=4), Leaf(log2dim=3)]
  Background: 0.3
  Root: 0 tiles, 8 children
  Nodes: 25 total (16 internal, 8 leaf)
  Active voxels: 2.08K
  Transform: UniformScale
    Voxel size: (0.1, 0.1, 0.1)
  Compression: blosc+active_mask (0x6)
```

Write a copy with `--write` or `--write-mmap`:

```
$ ./vdbdump input.vdb --write output.vdb
$ ./vdbdump input.vdb --write-mmap output_mmap.vdb
```

## nanovdbdump example

A command-line tool that reads a NanoVDB file and prints its structure:

```
$ ./nanovdbdump input.nvdb --verbose
File: input.nvdb
  NanoVDB version: 32
  Grids: 1
  Codec: blosc

Grid[0]: "surface"
  Type: Float
  Class: LevelSet
  Grid size: 123456 bytes
  Voxel size: (0.1, 0.1, 0.1)
  World bbox: [(0, 0, 0), (100, 100, 100)]
  Index bbox: [(0, 0, 0), (999, 999, 999)]
  Active voxels: 123456
  Nodes: 10 leaf, 5 lower, 2 upper
  Tiles: 0 level0, 0 level1, 0 level2
```

## Python bindings

Install the Python extension:

```bash
pip install tinyvdb
```

Or build from source:

```bash
cd python && pip install .
```

Usage:

```python
import tinyvdb

# Open a NanoVDB file
with tinyvdb.NanoVDBFile("input.nvdb") as f:
    print(f"Grids: {f.grid_count()}")
    for i in range(f.grid_count()):
        print(f"Grid {i}: {f.grid_name(i)}")
        print(f"  Type: {f.grid_type(i)}")
        print(f"  BBox: {f.bbox(i)}")
        print(f"  Voxel size: {f.voxel_size(i, 0)}")

# Get a voxel value
val = f.get(0, 100, 100, 100)
print(f"Value at (100, 100, 100): {val}")
```

Writing:

```python
# Save to file
f.save("output.nvdb", codec=tinyvdb.CODEC_BLOSC)

# Write to bytes
data = f.to_bytes(codec=tinyvdb.CODEC_ZIP)
```

Writing a dense grid to `.vdb` (value type chosen from the numpy dtype —
`float32`/`float64`/`int32`/`int64`/`bool` scalar grids, or a `(nx, ny, nz, 3)`
`float32` array for a `vec3f` grid):

```python
import numpy as np, tinyvdb

sdf = np.random.randn(32, 32, 24).astype(np.float32)
tinyvdb.write_dense_grid("sdf.vdb", sdf, voxel_size=0.05)     # Tree_float_5_4_3
arr, voxel_size, origin = tinyvdb.read_dense_grid("sdf.vdb")  # dtype preserved
```

See `python/README.md` for the full dtype table and the `bool` caveat (tinyvdb's
1-byte-per-voxel BOOL layout is not byte-compatible with OpenVDB's bit-packed
format).

Utility functions:

```python
import tinyvdb

# Get node sizes
leaf_size = tinyvdb.leaf_node_size()      # Default: Float
leaf_size = tinyvdb.leaf_node_size(tinyvdb.GRID_TYPE_DOUBLE)

# Get value size
val_size = tinyvdb.value_size()            # 4 for Float
val_size = tinyvdb.value_size(tinyvdb.GRID_TYPE_VEC3F)  # 12
```

## Notes

### Terms

`background` is a uniform constant value used when there is no voxel data.

`Node` is composed of Root, Internal, and Leaf.
Leaf contains actual voxel data.

Root and Internal nodes have `Value` or a pointer to a child node, where `Value` is a constant value for the node.

There are two bit masks, `child mask` and `value mask`, for each internal node.

## License

TinyVDB is licensed under the [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0).

```
Copyright 2026 - Present Syoyo Fujita

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```

### Third party licenses

| Library | License |
|---------|---------|
| OpenVDB (original I/O logic) | Apache 2.0 |
| LZ4 | BSD 2-Clause |
| miniz | MIT |
| tinyexr (vdbrender example) | BSD 3-Clause |
