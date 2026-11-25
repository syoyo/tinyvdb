# How to use and compile-time defines

> Extracted from the [TinyVDB README](../README.md) for detailed reference.

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
