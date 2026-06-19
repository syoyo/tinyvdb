"""TinyVDB — lightweight OpenVDB I/O, mesh, and grid operations."""

from tinyvdb._tinyvdb import (
    # Exception
    VDBError,
    # Types
    VDBFile,
    VDBGrid,
    VDBTree,
    VDBNode,
    DenseGrid,
    DenseVecGrid,
    TriangleMesh,
    # I/O
    open,
    from_bytes,
    write_float_grid,
    write_grid,
    write_sparse_grid as _write_sparse_grid_c,
    # Mesh
    mesh_to_sdf,
    sdf_to_mesh,
    make_manifold,
    # Level-set primitives & SDF utilities
    level_set_sphere,
    level_set_box,
    level_set_torus,
    level_set_capsule,
    level_set_platonic,
    sdf_to_fog_volume,
    sdf_interior_mask,
    sdf_segmentation,
    sdf_extract_enclosed_regions,
    level_set_euler_characteristic,
    level_set_genus,
    level_set_rebuild,
    # Morphology
    dilate,
    erode,
    open_op,
    close_op,
    # Filtering
    gaussian_filter,
    mean_filter,
    laplacian_filter,
    # CSG
    csg_union,
    csg_intersection,
    csg_difference,
    # Measurement
    surface_area,
    volume,
    grid_statistics,
    grid_histogram,
    check_level_set,
    check_fog_volume,
    # Differential operators
    gradient,
    divergence,
    laplacian,
    curl,
    magnitude,
    normalize,
    cpt,
    comp_max,
    comp_min,
    comp_sum,
    comp_mult,
    median_filter,
    mean_curvature_flow,
    signed_flood_fill,
    # Advection & Poisson
    advect,
    solve_poisson,
    solve_poisson_d,
    fast_sweeping,
    # Ray casting
    ray_cast_sdf,
    # Particles
    particles_to_sdf,
    volume_to_spheres,
    # Fracture
    fracture,
    # Sampling / TSDF / topology / pooling
    sample_trilinear,
    integrate_tsdf,
    coarsen_grid,
    refine_grid,
    resample_grid,
    max_pool,
    avg_pool,
    splat_trilinear,
    voxels_along_ray,
    uniform_ray_samples,
    segments_along_ray,
    clip_grid,
    prune_grid,
    merge_grids,
    integrate_tsdf_into,
    integrate_tsdf_with_color_into,
    sparse_conv3d,
    sparse_conv3d_mc,
    sparse_conv3d_vjp_values,
    sparse_conv3d_vjp_kernel,
    # Constants
    COMPRESS_NONE,
    COMPRESS_ZIP,
    COMPRESS_ACTIVE_MASK,
    COMPRESS_BLOSC,
    SIGN_FLOOD_FILL,
    SIGN_SWEEP,
)

def write_obj(mesh, path):
    """Write a TriangleMesh to a Wavefront OBJ file.

    Uses the zero-copy `mesh.vertices` / `mesh.faces` memoryviews so this
    works without numpy. If numpy is installed, output is identical.
    """
    nv = int(mesh.num_vertices)
    nf = int(mesh.num_faces)
    if nv == 0 or nf == 0:
        # Still write a valid (empty) OBJ.
        with builtins_open(path, "w") as f:
            f.write("# tinyvdb empty mesh\n")
        return
    verts = mesh.vertices  # 2D memoryview shape (nv, 3) float32
    faces = mesh.faces     # 2D memoryview shape (nf, 3) uint32
    with builtins_open(path, "w") as f:
        f.write(f"# tinyvdb mesh: {nv} verts, {nf} faces\n")
        for i in range(nv):
            f.write(f"v {verts[i, 0]:.6f} {verts[i, 1]:.6f} {verts[i, 2]:.6f}\n")
        for i in range(nf):
            # OBJ is 1-indexed
            f.write(f"f {int(faces[i, 0]) + 1} {int(faces[i, 1]) + 1} {int(faces[i, 2]) + 1}\n")


# Avoid name collision with our re-exported `open` (VDB file opener).
import builtins as _builtins
builtins_open = _builtins.open


def gaussian_filter_sparse(sparse_or_grid, width, sigma=None, voxel_size=1.0,
                            origin=(0.0, 0.0, 0.0)):
    """Apply a 3D Gaussian filter to a sparse grid (same-topology output).

    Accepts either a dict with `coords`/`values` bytes (from
    `VDBGrid.to_sparse()` / `dilate_topology()` / etc.) or a
    `VDBGrid` instance (in which case the grid is extracted via
    `to_sparse()` first; voxel_size/origin are read from the grid).

    The Gaussian is applied as a separable 1-D outer product collapsed
    into a single 3-D kernel of `width^3` taps; sigma defaults to
    `width / 3.0` (matches the dense `gaussian_filter` convention).
    Out-of-active-set taps contribute 0.

    Returns a dict {coords, values, count} with the same topology
    as the input.
    """
    try:
        import numpy as _np  # noqa
    except ImportError:
        raise RuntimeError("gaussian_filter_sparse requires numpy")
    if sigma is None:
        sigma = width / 3.0
    if width < 1:
        raise ValueError("width must be >= 1")
    half = width // 2
    xs = _np.arange(-half, -half + width, dtype=_np.float32)
    g1 = _np.exp(-(xs ** 2) / (2.0 * sigma ** 2))
    g1 = g1 / g1.sum()
    # 3D separable kernel via three outer products. Layout matches
    # sparse_conv3d expectation: kernel[((dk*ky+dj)*kx+di)].
    k3 = _np.einsum('i,j,k->kji', g1, g1, g1).astype(_np.float32)
    # Kernel layout: index = ((dk*ky+dj)*kx+di), corresponds to k3[dk, dj, di]
    # k3 already has shape (kz=width, ky=width, kx=width) so a flatten() gives
    # the right linear order.
    kernel_bytes = k3.flatten().tobytes()
    if isinstance(sparse_or_grid, dict):
        sg = sparse_or_grid
        vs = float(voxel_size)
        ox, oy, oz = origin
    elif hasattr(sparse_or_grid, "to_sparse"):
        sg = sparse_or_grid.to_sparse()
        # If the grid exposes a transform, reuse it; otherwise default.
        vs = float(voxel_size)
        ox, oy, oz = origin
    else:
        raise TypeError("expected dict or VDBGrid")
    return sparse_conv3d(coords=sg["coords"], values=sg["values"],
                         kernel=kernel_bytes, kx=width, ky=width, kz=width,
                         voxel_size=vs, ox=ox, oy=oy, oz=oz, pad_value=0.0)


def mean_filter_sparse(sparse_or_grid, width=3, voxel_size=1.0,
                       origin=(0.0, 0.0, 0.0)):
    """Apply a uniform box (mean) filter to a sparse grid (same topology).

    Each output voxel is the unweighted average of its kx*ky*kz neighborhood
    (with `width` taps per axis). Out-of-active-set taps contribute 0 (so
    boundary voxels see slight darkening).
    """
    try:
        import numpy as _np
    except ImportError:
        raise RuntimeError("mean_filter_sparse requires numpy")
    if width < 1:
        raise ValueError("width must be >= 1")
    n = width * width * width
    kernel = _np.full(n, 1.0 / n, dtype=_np.float32)
    if isinstance(sparse_or_grid, dict):
        sg = sparse_or_grid
    elif hasattr(sparse_or_grid, "to_sparse"):
        sg = sparse_or_grid.to_sparse()
    else:
        raise TypeError("expected dict or VDBGrid")
    return sparse_conv3d(coords=sg["coords"], values=sg["values"],
                         kernel=kernel.tobytes(), kx=width, ky=width, kz=width,
                         voxel_size=voxel_size, ox=origin[0], oy=origin[1], oz=origin[2],
                         pad_value=0.0)


def laplacian_filter_sparse(sparse_or_grid, voxel_size=1.0,
                            origin=(0.0, 0.0, 0.0)):
    """Apply a 7-point discrete Laplacian to a sparse grid (same topology).

    Out-of-active-set neighbors contribute 0 (Dirichlet boundary).
    """
    try:
        import numpy as _np
    except ImportError:
        raise RuntimeError("laplacian_filter_sparse requires numpy")
    # 3x3x3 kernel with center=-6, six face-neighbors=+1, rest=0.
    kernel = _np.zeros((3, 3, 3), dtype=_np.float32)
    kernel[1, 1, 1] = -6.0
    kernel[0, 1, 1] = kernel[2, 1, 1] = 1.0
    kernel[1, 0, 1] = kernel[1, 2, 1] = 1.0
    kernel[1, 1, 0] = kernel[1, 1, 2] = 1.0
    h2 = float(voxel_size) * float(voxel_size)
    kernel /= h2
    if isinstance(sparse_or_grid, dict):
        sg = sparse_or_grid
    elif hasattr(sparse_or_grid, "to_sparse"):
        sg = sparse_or_grid.to_sparse()
    else:
        raise TypeError("expected dict or VDBGrid")
    return sparse_conv3d(coords=sg["coords"], values=sg["values"],
                         kernel=kernel.flatten().tobytes(), kx=3, ky=3, kz=3,
                         voxel_size=voxel_size, ox=origin[0], oy=origin[1], oz=origin[2],
                         pad_value=0.0)


# numpy dtype <-> the writer's dtype string. ``vec3f`` is handled specially
# (a trailing length-3 axis), so it is not in this scalar table.
_DTYPE_TO_NAME = {
    "float32": "float32",
    "float64": "float64",
    "int32": "int32",
    "int64": "int64",
    "bool": "bool",
}
# Writer dtype string -> numpy dtype for reading back.
_NAME_TO_NPDTYPE = {
    "float32": "float32",
    "float64": "float64",
    "int32": "int32",
    "int64": "int64",
    "bool": "bool",
    "vec3f": "float32",
}


def write_dense_grid(path, array, voxel_size=1.0, origin=(0.0, 0.0, 0.0),
                     name="sdf", background=0.0, compression=COMPRESS_ZIP, level=5):
    """Write a dense numpy array to a ``.vdb`` file.

    The grid value type is selected from the array:

    * scalar grids — a 3D array ``(nx, ny, nz)`` of ``float32`` (SDF / level set),
      ``float64``, ``int32``, ``int64`` or ``bool``;
    * vector grids — a 4D ``float32`` array ``(nx, ny, nz, 3)`` writes a
      ``Tree_vec3s_5_4_3`` (vec3f) grid.

    Parameters
    ----------
    path : str
        Output ``.vdb`` path.
    array : numpy.ndarray
        Dense grid as described above. Cast to a contiguous buffer as-is (no
        dtype conversion beyond making it contiguous), so the dtype you pass is
        the dtype written.
    voxel_size : float or (3,) sequence
        World size of one voxel (scalar = isotropic, or per-axis).
    origin : (3,) sequence
        World position of voxel index ``(0, 0, 0)``. ``world = voxel_size * index + origin``.
    name : str
        Grid name stored in the file.
    background : scalar
        Background value for inactive voxels (all voxels written here are active).
        For vec3f a scalar fills all three components.
    compression, level :
        Passed through to the writer (``COMPRESS_NONE``/``COMPRESS_ZIP``/``COMPRESS_BLOSC``).

    Notes
    -----
    ``bool`` grids are stored 1 byte/voxel (tinyvdb's internal layout), which is
    self-consistent with :func:`read_dense_grid` but **not** byte-compatible with
    OpenVDB's bit-packed BOOL leaves — such files will not load in DCCs.
    """
    try:
        import numpy as _np
    except ImportError:
        raise RuntimeError("write_dense_grid requires numpy")
    a = _np.ascontiguousarray(array)

    # vec3f: (nx, ny, nz, 3) float32.
    if a.ndim == 4 and a.shape[3] == 3:
        a = _np.ascontiguousarray(a, dtype=_np.float32)
        nx, ny, nz = (int(d) for d in a.shape[:3])
        dtype_name = "vec3f"
        bg = _np.asarray(background, dtype=_np.float32)
        bg = _np.broadcast_to(bg, (3,)).astype(_np.float32, copy=True)
    elif a.ndim == 3:
        dtype_name = _DTYPE_TO_NAME.get(a.dtype.name)
        if dtype_name is None:
            raise ValueError(
                f"unsupported array dtype {a.dtype}; expected one of "
                f"{sorted(_DTYPE_TO_NAME)} (or a (nx,ny,nz,3) float32 array for vec3f)")
        nx, ny, nz = (int(d) for d in a.shape)
        bg = _np.asarray(background, dtype=a.dtype)
    else:
        raise ValueError(
            f"array must be 3D (nx, ny, nz) or 4D (nx, ny, nz, 3) for vec3f, got shape {a.shape}")

    vs = (float(voxel_size),) * 3 if _np.isscalar(voxel_size) else tuple(float(v) for v in voxel_size)
    org = tuple(float(v) for v in origin)
    write_grid(path, a.reshape(-1).tobytes(), nx, ny, nz, dtype_name,
               voxel_size=vs, origin=org, name=name, background=bg.tobytes(),
               compression=int(compression), level=int(level))


def read_dense_grid(path, index=0):
    """Read a grid from a ``.vdb`` file back into a dense numpy array.

    Inverse of :func:`write_dense_grid`. Returns ``(array, voxel_size, origin)``
    where ``array`` spans the grid's active voxels with shape ``(nx, ny, nz)``
    (scalar grids) or ``(nx, ny, nz, 3)`` (vec3f), and dtype matching the grid's
    value type. ``voxel_size`` is a 3-tuple and ``origin`` is the world position
    of the array's first voxel. ``world = voxel_size*index + origin``.
    """
    try:
        import numpy as _np
    except ImportError:
        raise RuntimeError("read_dense_grid requires numpy")
    with open(path) as f:
        f.read_grids()
        g = f.grid(index)
        sparse = g.to_sparse_typed()
        name = sparse["dtype"]
        np_dtype = _NAME_TO_NPDTYPE.get(name)
        if np_dtype is None:
            raise ValueError(f"read_dense_grid: unsupported grid dtype '{name}'")
        ncomp = 3 if name == "vec3f" else 1
        empty_shape = (0, 0, 0, 3) if ncomp == 3 else (0, 0, 0)
        coords = _np.frombuffer(sparse["coords"], dtype=_np.int32).reshape(-1, 3)
        if coords.size == 0:
            return _np.empty(empty_shape, dtype=np_dtype), (1.0, 1.0, 1.0), (0.0, 0.0, 0.0)
        values = _np.frombuffer(sparse["values"], dtype=np_dtype)
        if ncomp == 3:
            values = values.reshape(-1, 3)
        cmin = coords.min(axis=0)
        cmax = coords.max(axis=0)
        shape = tuple(int(v) for v in (cmax - cmin + 1))
        out_shape = shape + (3,) if ncomp == 3 else shape
        arr = _np.zeros(out_shape, dtype=np_dtype)
        idx = tuple((coords[:, d] - cmin[d]) for d in range(3))
        arr[idx] = values
        tr = g.transform
        voxel_size = tuple(float(v) for v in tr.get("voxel_size", (1.0, 1.0, 1.0)))
        translation = tuple(float(v) for v in tr.get("translation", (0.0, 0.0, 0.0)))
        # Account for a non-zero active-voxel min: origin of arr[0,0,0].
        origin = tuple(translation[i] + voxel_size[i] * float(cmin[i]) for i in range(3))
        return arr, voxel_size, origin


def write_sparse_grid(path, coords, values, voxel_size=1.0, origin=(0.0, 0.0, 0.0),
                      name="grid", background=0.0, compression=COMPRESS_ZIP, level=5):
    """Write a sparse grid (explicit active voxels) to a ``.vdb`` file from scratch.

    The grid value type is selected from ``values`` exactly as in
    :func:`write_dense_grid`: a 1D array of ``float32`` / ``float64`` / ``int32`` /
    ``int64`` / ``bool`` writes the matching scalar grid, and a ``(N, 3)``
    ``float32`` array writes a ``Tree_vec3s`` (vec3f) grid.

    Parameters
    ----------
    path : str
        Output ``.vdb`` path.
    coords : numpy.ndarray
        ``(N, 3)`` integer array of world-voxel indices (cast to int32).
    values : numpy.ndarray
        ``(N,)`` scalar array, or ``(N, 3)`` ``float32`` for vec3f. ``len(values)``
        must equal ``len(coords)``. Paired with ``coords`` by position.
    voxel_size, origin, name, background, compression, level :
        As in :func:`write_dense_grid`. ``world = voxel_size * index + origin``.

    Notes
    -----
    The ``bool`` caveat from :func:`write_dense_grid` applies here too.
    """
    try:
        import numpy as _np
    except ImportError:
        raise RuntimeError("write_sparse_grid requires numpy")
    c = _np.ascontiguousarray(coords, dtype=_np.int32)
    if c.ndim != 2 or c.shape[1] != 3:
        raise ValueError(f"coords must be (N, 3), got shape {c.shape}")
    v = _np.ascontiguousarray(values)

    if v.ndim == 2 and v.shape[1] == 3:
        v = _np.ascontiguousarray(v, dtype=_np.float32)
        dtype_name = "vec3f"
        bg = _np.broadcast_to(_np.asarray(background, dtype=_np.float32), (3,)).astype(_np.float32, copy=True)
    elif v.ndim == 1:
        dtype_name = _DTYPE_TO_NAME.get(v.dtype.name)
        if dtype_name is None:
            raise ValueError(
                f"unsupported values dtype {v.dtype}; expected one of "
                f"{sorted(_DTYPE_TO_NAME)} (or an (N,3) float32 array for vec3f)")
        bg = _np.asarray(background, dtype=v.dtype)
    else:
        raise ValueError(f"values must be 1D (N,) or 2D (N, 3) for vec3f, got shape {v.shape}")

    if c.shape[0] != v.shape[0]:
        raise ValueError(f"coords and values length mismatch: {c.shape[0]} vs {v.shape[0]}")

    vs = (float(voxel_size),) * 3 if _np.isscalar(voxel_size) else tuple(float(x) for x in voxel_size)
    org = tuple(float(x) for x in origin)
    _write_sparse_grid_c(path, c.reshape(-1).tobytes(), v.reshape(-1).tobytes(), dtype_name,
                         voxel_size=vs, origin=org, name=name, background=bg.tobytes(),
                         compression=int(compression), level=int(level))


def read_sparse_grid(path, index=0):
    """Read a grid's active voxels from a ``.vdb`` file as a sparse array.

    Inverse of :func:`write_sparse_grid`. Returns ``(coords, values, voxel_size, origin)``
    where ``coords`` is an ``(N, 3)`` int32 array of world-voxel indices and ``values`` is
    ``(N,)`` (scalar grids) or ``(N, 3)`` (vec3f) with dtype matching the grid's value type.
    ``world = voxel_size * index + origin``.
    """
    try:
        import numpy as _np
    except ImportError:
        raise RuntimeError("read_sparse_grid requires numpy")
    with open(path) as f:
        f.read_grids()
        g = f.grid(index)
        sparse = g.to_sparse_typed()
        name = sparse["dtype"]
        np_dtype = _NAME_TO_NPDTYPE.get(name)
        if np_dtype is None:
            raise ValueError(f"read_sparse_grid: unsupported grid dtype '{name}'")
        coords = _np.frombuffer(sparse["coords"], dtype=_np.int32).reshape(-1, 3).copy()
        values = _np.frombuffer(sparse["values"], dtype=np_dtype)
        if name == "vec3f":
            values = values.reshape(-1, 3)
        values = values.copy()
        tr = g.transform
        voxel_size = tuple(float(v) for v in tr.get("voxel_size", (1.0, 1.0, 1.0)))
        origin = tuple(float(v) for v in tr.get("translation", (0.0, 0.0, 0.0)))
        return coords, values, voxel_size, origin


# Named platonic-solid convenience wrappers around level_set_platonic. `radius`
# is the circumradius (center-to-vertex distance).
def level_set_tetrahedron(radius, center=(0.0, 0.0, 0.0), voxel_size=0.1, half_width=3.0):
    """Narrow-band SDF of a regular tetrahedron (4 faces). See :func:`level_set_platonic`."""
    return level_set_platonic(4, radius, center=center, voxel_size=voxel_size, half_width=half_width)


def level_set_cube(radius, center=(0.0, 0.0, 0.0), voxel_size=0.1, half_width=3.0):
    """Narrow-band SDF of a cube (6 faces); `radius` is the circumradius. For a
    cube given by half-extents with a true Euclidean SDF, use :func:`level_set_box`."""
    return level_set_platonic(6, radius, center=center, voxel_size=voxel_size, half_width=half_width)


def level_set_octahedron(radius, center=(0.0, 0.0, 0.0), voxel_size=0.1, half_width=3.0):
    """Narrow-band SDF of a regular octahedron (8 faces). See :func:`level_set_platonic`."""
    return level_set_platonic(8, radius, center=center, voxel_size=voxel_size, half_width=half_width)


def level_set_dodecahedron(radius, center=(0.0, 0.0, 0.0), voxel_size=0.1, half_width=3.0):
    """Narrow-band SDF of a regular dodecahedron (12 faces). See :func:`level_set_platonic`."""
    return level_set_platonic(12, radius, center=center, voxel_size=voxel_size, half_width=half_width)


def level_set_icosahedron(radius, center=(0.0, 0.0, 0.0), voxel_size=0.1, half_width=3.0):
    """Narrow-band SDF of a regular icosahedron (20 faces). See :func:`level_set_platonic`."""
    return level_set_platonic(20, radius, center=center, voxel_size=voxel_size, half_width=half_width)


__version__ = "0.9.0"

__all__ = [
    "VDBError",
    "VDBFile",
    "VDBGrid",
    "VDBTree",
    "VDBNode",
    "DenseGrid",
    "DenseVecGrid",
    "TriangleMesh",
    "open",
    "from_bytes",
    "write_float_grid",
    "write_grid",
    "write_dense_grid",
    "read_dense_grid",
    "write_sparse_grid",
    "read_sparse_grid",
    "mesh_to_sdf",
    "sdf_to_mesh",
    "make_manifold",
    "level_set_sphere",
    "level_set_box",
    "level_set_torus",
    "level_set_capsule",
    "level_set_platonic",
    "level_set_tetrahedron",
    "level_set_cube",
    "level_set_octahedron",
    "level_set_dodecahedron",
    "level_set_icosahedron",
    "sdf_to_fog_volume",
    "sdf_interior_mask",
    "sdf_segmentation",
    "sdf_extract_enclosed_regions",
    "level_set_euler_characteristic",
    "level_set_genus",
    "level_set_rebuild",
    "dilate",
    "erode",
    "open_op",
    "close_op",
    "gaussian_filter",
    "mean_filter",
    "laplacian_filter",
    "csg_union",
    "csg_intersection",
    "csg_difference",
    "surface_area",
    "volume",
    "grid_statistics",
    "grid_histogram",
    "check_level_set",
    "check_fog_volume",
    "gradient",
    "divergence",
    "laplacian",
    "curl",
    "magnitude",
    "normalize",
    "cpt",
    "comp_max",
    "comp_min",
    "comp_sum",
    "comp_mult",
    "median_filter",
    "mean_curvature_flow",
    "signed_flood_fill",
    "advect",
    "solve_poisson",
    "solve_poisson_d",
    "fast_sweeping",
    "ray_cast_sdf",
    "particles_to_sdf",
    "volume_to_spheres",
    "fracture",
    "sample_trilinear",
    "integrate_tsdf",
    "coarsen_grid",
    "refine_grid",
    "resample_grid",
    "max_pool",
    "avg_pool",
    "splat_trilinear",
    "voxels_along_ray",
    "uniform_ray_samples",
    "segments_along_ray",
    "clip_grid",
    "prune_grid",
    "merge_grids",
    "integrate_tsdf_into",
    "integrate_tsdf_with_color_into",
    "sparse_conv3d",
    "sparse_conv3d_mc",
    "sparse_conv3d_vjp_values",
    "sparse_conv3d_vjp_kernel",
    "gaussian_filter_sparse",
    "mean_filter_sparse",
    "laplacian_filter_sparse",
    "write_obj",
    "COMPRESS_NONE",
    "COMPRESS_ZIP",
    "COMPRESS_ACTIVE_MASK",
    "COMPRESS_BLOSC",
    "SIGN_FLOOD_FILL",
    "SIGN_SWEEP",
]
