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
    # Mesh
    mesh_to_sdf,
    sdf_to_mesh,
    make_manifold,
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
    # Differential operators
    gradient,
    divergence,
    laplacian,
    curl,
    # Advection & Poisson
    advect,
    solve_poisson,
    solve_poisson_d,
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


__version__ = "0.8.2"

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
    "mesh_to_sdf",
    "sdf_to_mesh",
    "make_manifold",
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
    "gradient",
    "divergence",
    "laplacian",
    "curl",
    "advect",
    "solve_poisson",
    "solve_poisson_d",
    "ray_cast_sdf",
    "particles_to_sdf",
    "volume_to_spheres",
    "fracture",
    "sample_trilinear",
    "integrate_tsdf",
    "coarsen_grid",
    "refine_grid",
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
    "gaussian_filter_sparse",
    "write_obj",
    "COMPRESS_NONE",
    "COMPRESS_ZIP",
    "COMPRESS_ACTIVE_MASK",
    "COMPRESS_BLOSC",
    "SIGN_FLOOD_FILL",
    "SIGN_SWEEP",
]
