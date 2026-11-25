# TinyVDB, lightweight C/C++ VDB library

[![Sponsor on GitHub](https://img.shields.io/badge/Sponsor-GitHub-ea4aaa?logo=githubsponsors)](https://github.com/sponsors/syoyo)
[![PyPI version](https://img.shields.io/pypi/v/tinyvdb?label=PyPI%20version)](https://pypi.org/project/tinyvdb/)
[![npm version](https://img.shields.io/npm/v/tinyvdb?label=npm)](https://www.npmjs.com/package/tinyvdb)

TinyVDB is a lightweight C11/C++ library for OpenVDB data: VDB and NanoVDB
file I/O, mesh↔SDF conversion, dense and sparse volume operations, and optional
Vulkan/CUDA/HIP acceleration — without depending on the full OpenVDB library.
It is suited to genAI, graphics, HPC visualization and physics simulation.

## Documentation

| Topic | Page |
| --- | --- |
| Modules, API contracts, tree maintenance, sparse/SDF/mesh ops | [doc/api.md](doc/api.md) |
| Feature lists (I/O, mesh, ops, GPU, rasterizer) | [doc/features.md](doc/features.md) |
| Validation and supported VDB versions | [doc/validation.md](doc/validation.md) |
| Usage examples and compile-time defines | [doc/usage.md](doc/usage.md) |
| CMake build and `vdbdump`/`nanovdbdump` tools | [doc/build.md](doc/build.md) |
| Python and WebAssembly bindings | [doc/bindings.md](doc/bindings.md) |
| Terms, license, third-party licenses | [doc/notes.md](doc/notes.md) |
| File format notes and release/releasing docs | [doc/](doc/) |

## Quick start

```sh
cmake -S . -B build -DTINYVDB_BUILD_TESTS=ON
cmake --build build -j
ctest --test-dir build --output-on-failure
```

Read a VDB file with the header-only reader:

```c
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"

tvdb_file_t file = {0};
tvdb_error_t err = {0};
if (tvdb_file_open(&file, "scene.vdb", NULL, &err) == TVDB_OK) {
    /* read grids and voxel data; see doc/usage.md */
    tvdb_file_close(&file);
}
```

See [doc/usage.md](doc/usage.md) for the full I/O, NanoVDB, mesh and grid
examples, and [doc/build.md](doc/build.md) for CMake options and examples.

## Formalization and validation

A Lean 4 verified model of the `.vdb` format and volume operators ships with
the project; the C library is checked against the model by differential
harnesses. See [LEAN.md](LEAN.md) for the status overview and
[lean/VERIFICATION.md](lean/VERIFICATION.md) for the theorem inventory,
boundaries, findings and gate results.

## Release history

- **2026-11-22** — Add Lean 4 formalization and validation status:
  [LEAN.md](LEAN.md) and [lean/VERIFICATION.md](lean/VERIFICATION.md).
- **0.9.1** — Checked tree maintenance and sparse volume tools; see
  [CHANGELOG.md](CHANGELOG.md) for API changes and migration details.
  Python bindings require Python 3.11 or newer.

## License

Apache License 2.0 — see [doc/notes.md](doc/notes.md) and
[LICENSE](LICENSE) for details.
