# Build, CMake and example tools

> Extracted from the [TinyVDB README](../README.md) for detailed reference.

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
| `TINYVDB_BUILD_TESTS` | `OFF` | Build the test suite (24 CPU tests, or 48 with GPU tests enabled) |
| `TINYVDB_BUILD_BENCH` | `OFF` | Build `bench_tinyvdb`, the measurement harness behind `doc/bench-baseline.md` |
| `TINYVDB_BUILD_EXAMPLES` | `ON` | Build `vdbdump`, `nanovdbdump`, etc. |
| `TINYVDB_BUILD_VDBRENDER` | `ON` | Build the vdbrender volume path tracer |
| `TINYVDB_BUILD_PYTHON` | `OFF` | Build Python extension |
| `TINYVDB_USE_SYSTEM_ZLIB` | `OFF` | Use system zlib instead of bundled miniz |
| `TINYVDB_USE_ZSTD` | `ON` | Enable ZSTD inside BLOSC frames (bundled or system) |
| `TINYVDB_USE_SYSTEM_ZSTD` | `OFF` | Link system libzstd instead of `deps/zstd.c` |
| `TINYVDB_USE_SYSTEM_BLOSC` | `OFF` | Link system libblosc — required to read NanoVDB BLOSC files produced by libnanovdb |
| `TINYVDB_OPENMP` | `OFF` | Enable OpenMP parallelism in dense ops, Poisson CG, sparse conv, sample batches, TSDF fusion |
| `TINYVDB_SIMD` | `ON` | Enable SSE4.2/AVX2/F16C (x86-64 only; scalar fallback otherwise) |
| `TINYVDB_BUILD_GPU` | `ON` | Build the runtime-loaded Vulkan/CUDA/HIP backend and `tinyvdb_gpu_compute` (no SDK needed at build time) |
| `TINYVDB_BUILD_TVDBVIEW` | `ON` | Build the `tvdbview` viewer |
| `TINYVDB_USE_CCACHE` | `ON` | Use ccache when available |

`TINYVDB_BUILD_GPU` generates SPIR-V with `glslangValidator` when it is on `PATH`
and falls back to a build with no shaders otherwise; point
`TINYVDB_GLSLANG_VALIDATOR` at the binary to override the search. Without shaders a
context still creates and every GPU op returns `UNIMPLEMENTED`, so a caller can
tell "not built for this" from "genuinely unsupported" via
`tvdb_gpu_spirv_available()`.

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
