# TinyVDB, header-only C/C++ VDB library

[![PyPI](https://img.shields.io/pypi/v/tinyvdb)](https://pypi.org/project/tinyvdb/)

TinyVDB is a collection of header-only C/C++ libraries for working with OpenVDB data. It provides lightweight VDB file I/O, mesh-to-SDF conversion, grid operations, and more — without depending on the full OpenVDB library.

TinyVDB is suitable for genAI, graphics applications, HPC visualization tools, physics simulation, and any project that needs lightweight VDB functionality.

## Modules

| Header | Language | Description |
|--------|----------|-------------|
| `tinyvdb_io.h` | C11 | OpenVDB file I/O with custom memory allocator support |
| `tinyvdb_mesh.h` | C++11 | Mesh-to-SDF, marching cubes, manifold preprocessing |
| `tinyvdb_ops.h` | C++11 | Grid operations: morphology, filtering, CSG, differential operators, advection, ray tracing, fracture |

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
* [x] BLOSC compression (built-in, using bundled LZ4 — no external blosc dependency)
* [x] Active mask compression (per-node flags 0-6)
* [x] Half-float (FP16) grid support
* [x] PointIndexGrid (`Tree_ptidx32_*`) leaf payload read/write
* [x] PointDataGrid (`Tree_ptdataidx32_*`) topology read + opaque point payload round-trip

### Mesh (`tinyvdb_mesh.h`)

* [x] Triangle mesh to signed distance field (dense 3D grid)
* [x] SDF to triangle mesh (marching cubes)
* [x] Manifold preprocessing (mesh to SDF to mesh round-trip)
* [x] Configurable sign determination (flood fill or sweep)

### Grid operations (`tinyvdb_ops.h`)

* [x] Morphological dilation/erosion, open/close
* [x] Gaussian, mean, and Laplacian SDF filtering
* [x] CSG operations (union, intersection, difference)
* [x] Surface area and volume measurement
* [x] Differential operators (gradient, divergence, Laplacian, curl)
* [x] Finite difference stencils (central, forward, backward)
* [x] Semi-Lagrangian advection (RK2)
* [x] Poisson solver (preconditioned conjugate gradient)
* [x] Ray-SDF intersection (sphere tracing)
* [x] Volume to spheres (greedy adaptive sphere packing)
* [x] Particles to SDF (sphere stamping)
* [x] Level set fracture (cutter-based volume splitting)

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

```cpp
// In exactly one .cc file:
#define TINYVDB_MESH_IMPLEMENTATION
#include "tinyvdb_mesh.h"
```

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

```cpp
// In exactly one .cc file:
#define TINYVDB_OPS_IMPLEMENTATION
#include "tinyvdb_ops.h"
```

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

## Compile flags

| Flag | Description |
|------|-------------|
| `TVDB_USE_SYSTEM_ZLIB` | Use system zlib instead of bundled miniz |
| `TVDB_NO_MMAP` | Disable mmap, always read into heap buffer |

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
| `TINYVDB_USE_SYSTEM_ZLIB` | `OFF` | Use system zlib instead of bundled miniz |
| `TINYVDB_BUILD_EXAMPLES` | `ON` | Build the vdbdump example |
| `TINYVDB_BUILD_VDBRENDER` | `ON` | Build the vdbrender volume path tracer |

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
