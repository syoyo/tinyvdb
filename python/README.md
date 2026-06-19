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

### Level-set primitives & SDF utilities

Generate analytic narrow-band SDFs (parallels OpenVDB's `LevelSetSphere` /
`LevelSetPlatonic` / `LevelSetTubes`) as `DenseGrid`s, then operate on them with
the dense ops (CSG, filters, marching cubes) or write them to `.vdb`. Every voxel
holds the true signed distance clamped to `±half_width * voxel_size`; negative is
inside. The grid is sized to enclose the primitive plus the band margin.

```python
import numpy as np
import tinyvdb

sphere  = tinyvdb.level_set_sphere(radius=1.0, center=(0, 0, 0), voxel_size=0.05)
box     = tinyvdb.level_set_box(half_extents=(0.5, 0.4, 0.6))
torus   = tinyvdb.level_set_torus(major_radius=1.0, minor_radius=0.3)   # XZ plane, axis Y
capsule = tinyvdb.level_set_capsule(p0=(-0.5, 0, 0), p1=(0.5, 0, 0), radius=0.25)

# Platonic solids (radius = circumradius). Either the generic form or a named
# wrapper; the field is the convex half-space SDF (exact isosurface).
ico   = tinyvdb.level_set_icosahedron(radius=1.0)
solid = tinyvdb.level_set_platonic(face_count=12, radius=1.0)   # 4/6/8/12/20

print(sphere.shape, sphere.voxel_size, sphere.origin)
arr = np.array(sphere, copy=False)        # zero-copy float32 view

# Combine and re-mesh
both = tinyvdb.csg_union(sphere, box)
mesh = tinyvdb.sdf_to_mesh(both, isovalue=0.0)

# SDF utilities
fog  = tinyvdb.sdf_to_fog_volume(sphere)             # density = clamp(-sdf/(hw*voxel), 0, 1)
mask = tinyvdb.sdf_interior_mask(sphere, isovalue=0.0)  # 1.0 inside, 0.0 outside

# Split disjoint objects; extract sealed cavities
segments = tinyvdb.sdf_segmentation(grid, isovalue=0.0, connectivity=6)  # list[DenseGrid]
voids    = tinyvdb.sdf_extract_enclosed_regions(grid)  # 1.0 mask of interior cavities

# Topology measures of the isosurface
chi   = tinyvdb.level_set_euler_characteristic(torus)   # 0.0  (2 for a sphere)
genus = tinyvdb.level_set_genus(torus)                  # 1    (0 for a sphere)

# Rebuild a clean SDF from the isosurface (renormalize and/or resample)
clean = tinyvdb.level_set_rebuild(damaged, isovalue=0.0, voxel_size=0.05)
```

> **Note:** `level_set_rebuild` (and `mesh_to_sdf`) use a brute-force
> mesh-to-SDF (O(voxels × triangles)); keep the voxel size coarse for large
> surfaces.

All generators take `voxel_size=` and `half_width=` (band width in voxels,
default 3, matching OpenVDB's `LEVEL_SET_HALF_WIDTH`).

### Statistics & diagnostics

```python
s = tinyvdb.grid_statistics(grid)        # {min, max, mean, stddev, sum, count}
h = tinyvdb.grid_histogram(grid, -1.0, 1.0, nbins=32)   # list of bin counts

# A valid narrow-band SDF has |grad| == 1 in the band:
chk = tinyvdb.check_level_set(grid, band_width=0.1, tol=0.1)   # {mean_grad_mag, ...}
# A valid fog volume has all values in [0, 1]:
ok = tinyvdb.check_fog_volume(grid)["valid"]
```

### Operators & filters

```python
# Vector-grid operators (GridOperators)
mag  = tinyvdb.magnitude(vec)            # DenseVecGrid -> DenseGrid (|v|)
unit = tinyvdb.normalize(vec)            # DenseVecGrid -> DenseVecGrid (v/|v|)
near = tinyvdb.cpt(sdf)                  # closest-point transform of an SDF

# Per-voxel composite of two same-shape grids
u = tinyvdb.comp_max(a, b)   # also comp_min / comp_sum / comp_mult

# In-place-style filters (return a new DenseGrid)
m = tinyvdb.median_filter(grid, radius=1, iterations=1)
s = tinyvdb.mean_curvature_flow(grid, dt=0.0003, iterations=8)   # keep dt small
```

### Write a dense grid to `.vdb`

Write an existing dense field (e.g. an SDF you already computed) to a fresh `.vdb`
file. `world = voxel_size * index + origin` (per-axis `ScaleTranslateMap`).

The grid value type is selected from the numpy array's dtype:

| array | grid type written |
| --- | --- |
| `(nx, ny, nz)` `float32` | `Tree_float_5_4_3` |
| `(nx, ny, nz)` `float64` | `Tree_double_5_4_3` |
| `(nx, ny, nz)` `int32` | `Tree_int32_5_4_3` |
| `(nx, ny, nz)` `int64` | `Tree_int64_5_4_3` |
| `(nx, ny, nz)` `bool` | `Tree_bool_5_4_3` (see note) |
| `(nx, ny, nz, 3)` `float32` | `Tree_vec3s_5_4_3` (vec3f) |

```python
import numpy as np
import tinyvdb

sdf = np.random.randn(32, 32, 24).astype(np.float32)   # your dense (nx, ny, nz) field

# numpy convenience (round-trips bit-exactly, dtype preserved):
tinyvdb.write_dense_grid("sdf.vdb", sdf, voxel_size=(0.05, 0.06, 0.07),
                         origin=(1.0, 2.0, 3.0), name="sdf")
arr, voxel_size, origin = tinyvdb.read_dense_grid("sdf.vdb")
assert np.array_equal(arr, sdf)

# other scalar types and vec3f, same call:
labels = np.random.randint(0, 10, (16, 16, 16)).astype(np.int32)
tinyvdb.write_dense_grid("labels.vdb", labels)              # Tree_int32_5_4_3
velocity = np.random.randn(16, 16, 16, 3).astype(np.float32)
tinyvdb.write_dense_grid("vel.vdb", velocity)              # Tree_vec3s_5_4_3

# numpy-free raw API for float (values is an nx*ny*nz float32 buffer in C order):
import struct
buf = struct.pack("24f", *range(24))
tinyvdb.write_float_grid("grid.vdb", buf, 2, 3, 4,
                         voxel_size=(0.1, 0.1, 0.1), origin=(0.0, 0.0, 0.0))
```

> **Note on `bool`:** tinyvdb stores BOOL grids as 1 byte/voxel rather than
> OpenVDB's bit-packed 1-bit format. Such files round-trip self-consistently
> through `read_dense_grid` but are **not** byte-compatible with OpenVDB and will
> not load in DCCs (Houdini/Blender/etc).

### Write a sparse grid to `.vdb`

When you only have a set of active voxels (not a full dense block), write them
directly with `write_sparse_grid` — same dtype rules as `write_dense_grid`
(scalar `(N,)` arrays, or `(N, 3)` `float32` for vec3f). Coords are world-voxel
indices and need not be contiguous.

```python
import numpy as np, tinyvdb

coords = np.array([[0, 0, 0], [10, 2, 3], [100, 100, 100]], dtype=np.int32)
values = np.array([1.0, 2.0, 3.0], dtype=np.float32)
tinyvdb.write_sparse_grid("sparse.vdb", coords, values, voxel_size=0.1, name="pts")

coords_out, values_out, voxel_size, origin = tinyvdb.read_sparse_grid("sparse.vdb")
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
