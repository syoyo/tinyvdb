# tinyvdb

Lightweight Python bindings for [TinyVDB](https://github.com/syoyo/tinyvdb) — a lightweight C/C++ library for OpenVDB and NanoVDB file I/O, mesh-to-SDF conversion, and grid operations. No OpenVDB dependency required.

Built with the Python C Stable API (abi3) for broad compatibility: one wheel per platform works across Python 3.11+.

## Installation

```bash
pip install tinyvdb
```

Pre-built wheels are available for:

| Platform | Architectures |
|----------|--------------|
| Linux | x86_64, aarch64 |
| macOS | x86_64, arm64 |
| Windows | AMD64 |

## Quick start

### Read a VDB file

```python
import tinyvdb

with tinyvdb.open("smoke.vdb") as f:
    print(f.grid_count, "grids")
    print(f.header)

    f.read_grids()
    grid = f.grid(0)
    print(grid.name, grid.type_name)
    print(grid.transform)
    print(grid.metadata)

    # Access tree structure
    tree = grid.tree
    node = tree.node(0)
    print(node.type, node.origin)
```

### Read a NanoVDB file

```python
import tinyvdb

with tinyvdb.NanoVDBFile("sphere.nvdb") as f:
    print(f.grid_count, "grids")
    for i in range(f.grid_count):
        print(f"  Grid {i}: {f.grid_name(i)}")
        print(f"  Type: {f.grid_type(i)}")
        print(f"  Class: {f.grid_class(i)}")
        print(f"  Voxel size: {f.voxel_size(i)}")
        print(f"  BBox: {f.bbox(i)}")
        print(f"  World BBox: {f.world_bbox(i)}")
        print(f"  Node counts: {f.node_counts(i)}")
        print(f"  Active voxels: {f.active_voxel_count(i)}")
```

### NanoVDB utilities

```python
import tinyvdb

# Node sizes
leaf_size = tinyvdb.leaf_node_size()          # Default: Float
lower_size = tinyvdb.lower_node_size()         # Default: Float
upper_size = tinyvdb.upper_node_size()         # Default: Float

# Value sizes
float_size = tinyvdb.value_size()              # 4 bytes
vec3f_size = tinyvdb.value_size(tinyvdb.GRID_TYPE_VEC3F)  # 12 bytes
double_size = tinyvdb.value_size(tinyvdb.GRID_TYPE_DOUBLE) # 8 bytes

# Grid type names
name = tinyvdb.grid_type_name(tinyvdb.GRID_TYPE_FLOAT)  # "Float"
```

### Load from bytes / save round-trip

```python
data = open("input.vdb", "rb").read()
f = tinyvdb.from_bytes(data)
f.read_grids()

# Serialize back
output = f.to_bytes(compression=tinyvdb.COMPRESS_ZIP, level=5)
open("output.vdb", "wb").write(output)
f.close()
```

### Mesh to SDF and back

```python
import struct
import tinyvdb

# Vertices as flat float32 buffer, faces as flat uint32 buffer
vertices = struct.pack("9f", 0,0,0, 1,0,0, 0,1,0)
faces = struct.pack("3I", 0, 1, 2)

# Convert mesh to signed distance field
sdf = tinyvdb.mesh_to_sdf(vertices, faces, voxel_size=0.05, band_width=3.0)
print(sdf.shape)  # (nx, ny, nz)

# Extract mesh via marching cubes
mesh = tinyvdb.sdf_to_mesh(sdf, isovalue=0.0)
print(mesh.num_vertices, mesh.num_faces)
```

### Write a dense grid / SDF to `.vdb`

Write an existing dense scalar field (e.g. an SDF you already computed) to a fresh `.vdb`
file. `world = voxel_size * index + origin` (per-axis `ScaleTranslateMap`).

```python
import numpy as np
import tinyvdb

sdf = np.random.randn(32, 32, 24).astype(np.float32)   # your dense (nx, ny, nz) field

# numpy convenience (round-trips bit-exactly):
tinyvdb.write_dense_grid("sdf.vdb", sdf, voxel_size=(0.05, 0.06, 0.07),
                         origin=(1.0, 2.0, 3.0), name="sdf")
arr, voxel_size, origin = tinyvdb.read_dense_grid("sdf.vdb")
assert np.array_equal(arr, sdf)

# numpy-free raw API (values is an nx*ny*nz float32 buffer in C order):
import struct
buf = struct.pack("24f", *range(24))
tinyvdb.write_float_grid("grid.vdb", buf, 2, 3, 4,
                         voxel_size=(0.1, 0.1, 0.1), origin=(0.0, 0.0, 0.0))
```

### CSG operations

```python
union = tinyvdb.csg_union(sdf_a, sdf_b)
intersection = tinyvdb.csg_intersection(sdf_a, sdf_b)
difference = tinyvdb.csg_difference(sdf_a, sdf_b)
```

### Morphology and filtering

```python
dilated = tinyvdb.dilate(sdf, iterations=2)
eroded = tinyvdb.erode(sdf, iterations=1)
smoothed = tinyvdb.gaussian_filter(sdf, width=1, iterations=3)
```

### Measurement

```python
area = tinyvdb.surface_area(sdf)
vol = tinyvdb.volume(sdf)
```

### Ray casting

```python
hit = tinyvdb.ray_cast_sdf(sdf,
                            origin=(0, 0, -5),
                            direction=(0, 0, 1),
                            max_t=100.0)
if hit:
    print(hit["t"], hit["position"], hit["normal"])
```

### Differential operators

```python
grad = tinyvdb.gradient(sdf)          # -> DenseVecGrid
div  = tinyvdb.divergence(grad)       # -> DenseGrid
lap  = tinyvdb.laplacian(sdf)         # -> DenseGrid
c    = tinyvdb.curl(vec_field)        # -> DenseVecGrid
```

### Advection and Poisson solver

```python
advected = tinyvdb.advect(field, velocity, dt=0.01)
solution, iterations = tinyvdb.solve_poisson(rhs, max_iters=500, tolerance=1e-6)
```

### Particles and fracture

```python
# Rasterize particles into SDF
sdf = tinyvdb.particles_to_sdf(positions, radii,
                                voxel_size=0.05, band_width=3.0)

# Fill volume interior with spheres
result = tinyvdb.volume_to_spheres(sdf, min_radius=0.01, max_spheres=500)

# Fracture volume with cutter SDFs
pieces = tinyvdb.fracture(volume, [cutter1, cutter2])
```

### Manifold repair

```python
mesh = tinyvdb.make_manifold(vertices, faces,
                              resolution=50, isovalue=0.55)
```

## numpy interop

`DenseGrid` supports the buffer protocol, so zero-copy access works with numpy:

```python
import numpy as np

grid = tinyvdb.mesh_to_sdf(verts, faces, 0.1, 3.0)
arr = np.frombuffer(grid, dtype=np.float32).reshape(grid.shape)
```

## API reference

### Types

| Type | Description |
|------|-------------|
| `VDBFile` | VDB file handle (context manager) |
| `VDBGrid` | Grid accessor (name, type, transform, metadata, tree) |
| `VDBTree` | Tree structure with node access |
| `VDBNode` | Tree node (root, internal, or leaf) |
| `DenseGrid` | 3D scalar grid with buffer protocol |
| `DenseVecGrid` | 3D vector field (3-component) with buffer protocol |
| `TriangleMesh` | Triangle mesh (vertices + faces as bytes) |
| `VDBError` | Exception type (subclass of RuntimeError) |

### Constants

#### Compression

| Constant | Value | Description |
|----------|-------|-------------|
| `COMPRESS_NONE` | 0 | No compression |
| `COMPRESS_ZIP` | 1 | ZIP (zlib/miniz) |
| `COMPRESS_ACTIVE_MASK` | 2 | Compress node masks |
| `COMPRESS_BLOSC` | 4 | BLOSC (LZ4) |
| `SIGN_FLOOD_FILL` | 0 | Exterior flood fill sign method |
| `SIGN_SWEEP` | 1 | Directional sweep sign method |

#### NanoVDB Codecs

| Constant | Value | Description |
|----------|-------|-------------|
| `CODEC_NONE` | 0 | No compression |
| `CODEC_ZIP` | 1 | ZIP compression |
| `CODEC_BLOSC` | 2 | BLOSC compression |

#### NanoVDB Grid Types

| Constant | Value | Description |
|----------|-------|-------------|
| `GRID_TYPE_FLOAT` | 1 | 32-bit float |
| `GRID_TYPE_DOUBLE` | 2 | 64-bit double |
| `GRID_TYPE_INT32` | 4 | 32-bit integer |
| `GRID_TYPE_INT64` | 5 | 64-bit integer |
| `GRID_TYPE_VEC3F` | 6 | 3D float vector |
| `GRID_TYPE_VEC3D` | 7 | 3D double vector |

#### NanoVDB Grid Classes

| Constant | Value | Description |
|----------|-------|-------------|
| `GRID_CLASS_LEVEL_SET` | 1 | Level set |
| `GRID_CLASS_FOG_VOLUME` | 2 | Fog volume |
| `GRID_CLASS_POINT_DATA` | 6 | Point data |

## Supported VDB versions

Reads and writes OpenVDB files version 220 through 225 (OpenVDB 3.x to 10.x+).

## License

Apache License 2.0
