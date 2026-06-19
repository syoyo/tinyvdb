"""Unit tests for the dense-grid writer / reader.

Covers the raw C-backed API (``write_float_grid``, numpy-free via ``struct``) and the numpy
conveniences (``write_dense_grid`` / ``read_dense_grid``): geometry/value round-trips, the
``world = voxel_size*index + origin`` transform, compression modes, multi-leaf grids, an analytic
sphere SDF, error handling, and the typed paths (``float64`` / ``int32`` / ``int64`` / ``vec3f`` /
``bool``) where the grid value type is chosen from the array dtype. Also covers the sparse
writer/reader (``write_sparse_grid`` / ``read_sparse_grid``) over the same dtype set.
"""

import math
import struct

import pytest

import tinyvdb


# --------------------------------------------------------------------------- helpers


def _pack_c_order(nx, ny, nz, fn):
    """Flat float32 buffer with C-order layout: index = (i*ny + j)*nz + k."""
    vals = [float(fn(i, j, k)) for i in range(nx) for j in range(ny) for k in range(nz)]
    return struct.pack(f"{len(vals)}f", *vals), vals


def _materialize_c_order(grid, nx, ny, nz):
    """Materialize the exact [0,n) box and return values indexed [i][j][k] (undoing x-fastest layout)."""
    dg = grid.materialize_dense((0, 0, 0), (nx, ny, nz))
    flat = struct.unpack(f"{nx * ny * nz}f", dg.to_bytes())  # x-fastest (Fortran)

    def at(i, j, k):
        return flat[i + nx * (j + ny * k)]

    return at


# --------------------------------------------------------------------------- raw API (numpy-free)


def test_write_float_grid_metadata(tmp_path):
    nx, ny, nz = 5, 4, 3
    buf, _ = _pack_c_order(nx, ny, nz, lambda i, j, k: (i * ny + j) * nz + k)
    path = str(tmp_path / "grid.vdb")
    tinyvdb.write_float_grid(path, buf, nx, ny, nz, voxel_size=(0.1, 0.2, 0.3),
                             origin=(1.0, 2.0, 3.0), name="mygrid",
                             compression=tinyvdb.COMPRESS_NONE)
    with tinyvdb.open(path) as f:
        f.read_grids()
        g = f.grid(0)
        assert g.name == "mygrid"
        assert g.type_name == "Tree_float_5_4_3"
        assert g.active_voxel_count() == nx * ny * nz
        tr = g.transform
        assert tr["type"] == "scale_translate"
        assert tuple(round(v, 6) for v in tr["voxel_size"]) == (0.1, 0.2, 0.3)
        assert tuple(round(v, 6) for v in tr["scale"]) == (0.1, 0.2, 0.3)
        assert tuple(round(v, 6) for v in tr["translation"]) == (1.0, 2.0, 3.0)


def test_write_float_grid_value_ordering(tmp_path):
    """Each voxel (i,j,k) must carry the value written for that index (C-order in -> correct voxel)."""
    nx, ny, nz = 6, 5, 4
    buf, vals = _pack_c_order(nx, ny, nz, lambda i, j, k: 100 * i + 10 * j + k)
    path = str(tmp_path / "order.vdb")
    tinyvdb.write_float_grid(path, buf, nx, ny, nz, compression=tinyvdb.COMPRESS_NONE)
    with tinyvdb.open(path) as f:
        f.read_grids()
        at = _materialize_c_order(f.grid(0), nx, ny, nz)
        for i in range(nx):
            for j in range(ny):
                for k in range(nz):
                    assert at(i, j, k) == 100 * i + 10 * j + k


def test_write_float_grid_single_voxel(tmp_path):
    buf = struct.pack("1f", 42.5)
    path = str(tmp_path / "one.vdb")
    tinyvdb.write_float_grid(path, buf, 1, 1, 1, compression=tinyvdb.COMPRESS_NONE)
    with tinyvdb.open(path) as f:
        f.read_grids()
        g = f.grid(0)
        assert g.active_voxel_count() == 1
        assert _materialize_c_order(g, 1, 1, 1)(0, 0, 0) == 42.5


@pytest.mark.parametrize("compression", [tinyvdb.COMPRESS_NONE, tinyvdb.COMPRESS_ZIP, tinyvdb.COMPRESS_BLOSC])
def test_write_float_grid_compression_modes(tmp_path, compression):
    nx, ny, nz = 8, 8, 8
    buf, _ = _pack_c_order(nx, ny, nz, lambda i, j, k: math.sin(i) + j - 0.5 * k)
    path = str(tmp_path / f"comp_{compression}.vdb")
    tinyvdb.write_float_grid(path, buf, nx, ny, nz, compression=compression, level=5)
    with tinyvdb.open(path) as f:
        f.read_grids()
        g = f.grid(0)
        assert g.active_voxel_count() == nx * ny * nz
        at = _materialize_c_order(g, nx, ny, nz)
        assert at(1, 2, 3) == pytest.approx(math.sin(1) + 2 - 1.5)


def test_write_float_grid_multi_leaf(tmp_path):
    """Grid larger than a single 8^3 leaf must span multiple leaves and preserve all voxels."""
    nx, ny, nz = 20, 17, 9   # spans 3x3x2 leaves
    buf, _ = _pack_c_order(nx, ny, nz, lambda i, j, k: i - j + 2 * k)
    path = str(tmp_path / "multi.vdb")
    tinyvdb.write_float_grid(path, buf, nx, ny, nz, compression=tinyvdb.COMPRESS_ZIP)
    with tinyvdb.open(path) as f:
        f.read_grids()
        g = f.grid(0)
        assert g.active_voxel_count() == nx * ny * nz
        at = _materialize_c_order(g, nx, ny, nz)
        assert at(0, 0, 0) == 0
        assert at(19, 16, 8) == 19 - 16 + 16
        assert at(10, 5, 3) == 10 - 5 + 6


def test_write_float_grid_bad_count(tmp_path):
    with pytest.raises(ValueError):
        tinyvdb.write_float_grid(str(tmp_path / "bad.vdb"), struct.pack("3f", 0, 1, 2), 2, 2, 2)


def test_write_float_grid_zero_dims(tmp_path):
    with pytest.raises((ValueError, tinyvdb.VDBError)):
        tinyvdb.write_float_grid(str(tmp_path / "z.vdb"), struct.pack("0f"), 0, 0, 0)


# --------------------------------------------------------------------------- numpy conveniences


def test_dense_grid_numpy_roundtrip(tmp_path):
    np = pytest.importorskip("numpy")
    rng = np.random.default_rng(1)
    field = rng.standard_normal((12, 10, 8)).astype(np.float32)
    path = str(tmp_path / "dense.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=0.05, origin=(0.0, 0.0, 0.0))
    arr, voxel_size, origin = tinyvdb.read_dense_grid(path)
    assert arr.shape == field.shape
    assert np.array_equal(arr, field)
    assert tuple(round(v, 6) for v in voxel_size) == (0.05, 0.05, 0.05)
    assert tuple(round(v, 6) for v in origin) == (0.0, 0.0, 0.0)


def test_dense_grid_anisotropic_transform(tmp_path):
    np = pytest.importorskip("numpy")
    field = np.arange(7 * 6 * 5, dtype=np.float32).reshape(7, 6, 5)
    path = str(tmp_path / "aniso.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=(0.05, 0.06, 0.07), origin=(1.0, -2.0, 3.5))
    arr, voxel_size, origin = tinyvdb.read_dense_grid(path)
    assert np.array_equal(arr, field)
    assert tuple(round(v, 6) for v in voxel_size) == (0.05, 0.06, 0.07)
    assert tuple(round(v, 6) for v in origin) == (1.0, -2.0, 3.5)


def test_dense_grid_requires_3d(tmp_path):
    np = pytest.importorskip("numpy")
    with pytest.raises(ValueError):
        tinyvdb.write_dense_grid(str(tmp_path / "2d.vdb"), np.zeros((4, 4), dtype=np.float32))


def test_dense_grid_float64_roundtrip(tmp_path):
    """A float64 array writes a Tree_double grid and reads back bit-exact float64."""
    np = pytest.importorskip("numpy")
    field = (np.arange(4 * 4 * 4).reshape(4, 4, 4)).astype(np.float64) * 0.0001234567890123
    path = str(tmp_path / "double.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=0.1)
    arr, _, _ = tinyvdb.read_dense_grid(path)
    assert arr.dtype == np.float64
    assert np.array_equal(arr, field)
    with tinyvdb.open(path) as f:
        f.read_grids()
        assert f.grid(0).type_name == "Tree_double_5_4_3"


def test_sphere_sdf_roundtrip(tmp_path):
    """An analytic sphere SDF round-trips bit-exactly and its zero crossing is geometrically sane."""
    np = pytest.importorskip("numpy")
    n = 24
    radius = 0.3
    voxel = 1.0 / n
    coords = (np.arange(n) + 0.5) * voxel - 0.5            # voxel centers in [-0.5, 0.5]
    X, Y, Z = np.meshgrid(coords, coords, coords, indexing="ij")
    sdf = (np.sqrt(X**2 + Y**2 + Z**2) - radius).astype(np.float32)

    path = str(tmp_path / "sphere_sdf.vdb")
    tinyvdb.write_dense_grid(path, sdf, voxel_size=voxel, origin=(-0.5, -0.5, -0.5),
                             name="sphere", compression=tinyvdb.COMPRESS_ZIP)
    arr, voxel_size, origin = tinyvdb.read_dense_grid(path)

    assert arr.shape == sdf.shape
    assert np.array_equal(arr, sdf)                        # bit-exact
    assert round(voxel_size[0], 6) == round(voxel, 6)
    # interior negative, exterior positive
    assert arr[n // 2, n // 2, n // 2] < 0.0
    assert arr[0, 0, 0] > 0.0


# ------------------------------------------------------------------- typed dense grids
#
# write_dense_grid selects the .vdb value type from the array dtype. These mirror
# the float cases for double / int32 / int64 / vec3f / bool. The underlying C
# builder is separately validated in tests/test_scalar_writer_audit.c.


@pytest.mark.parametrize("dtype, type_name", [
    ("int32", "Tree_int32_5_4_3"),
    ("int64", "Tree_int64_5_4_3"),
])
def test_dense_grid_int_roundtrip(tmp_path, dtype, type_name):
    np = pytest.importorskip("numpy")
    field = (np.arange(6 * 5 * 4).reshape(6, 5, 4) * 17 - 100).astype(dtype)
    path = str(tmp_path / f"{dtype}.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=(0.1, 0.2, 0.3), origin=(1.0, -2.0, 3.0))
    arr, voxel_size, origin = tinyvdb.read_dense_grid(path)
    assert arr.dtype == np.dtype(dtype)
    assert np.array_equal(arr, field)
    assert tuple(round(v, 6) for v in voxel_size) == (0.1, 0.2, 0.3)
    assert tuple(round(v, 6) for v in origin) == (1.0, -2.0, 3.0)
    with tinyvdb.open(path) as f:
        f.read_grids()
        assert f.grid(0).type_name == type_name


def test_dense_grid_int_multi_leaf(tmp_path):
    """Int grid spanning several 8^3 leaves round-trips exactly."""
    np = pytest.importorskip("numpy")
    field = (np.arange(20 * 17 * 9).reshape(20, 17, 9)).astype(np.int32)
    path = str(tmp_path / "int_multi.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=0.5)
    arr, _, _ = tinyvdb.read_dense_grid(path)
    assert arr.dtype == np.int32
    assert np.array_equal(arr, field)


def test_dense_grid_large_roundtrip(tmp_path):
    """Regression: a wide grid (an internal node with >64 leaf children) must not
    drop voxels. The tree-bridge DFS work-stack used to be fixed-size."""
    np = pytest.importorskip("numpy")
    field = np.arange(48 * 48 * 48, dtype=np.float32).reshape(48, 48, 48)
    path = str(tmp_path / "big.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=0.05)
    with tinyvdb.open(path) as f:
        f.read_grids()
        assert f.grid(0).active_voxel_count() == field.size
    arr, _, _ = tinyvdb.read_dense_grid(path)
    assert arr.shape == field.shape
    assert np.array_equal(arr, field)


def test_dense_grid_vec3f_roundtrip(tmp_path):
    """A (nx, ny, nz, 3) float32 field writes a Tree_vec3s grid and round-trips bit-exactly."""
    np = pytest.importorskip("numpy")
    rng = np.random.default_rng(7)
    field = rng.standard_normal((8, 6, 5, 3)).astype(np.float32)
    path = str(tmp_path / "vec3f.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=0.25, origin=(0.5, 0.5, 0.5), name="vel")
    arr, voxel_size, origin = tinyvdb.read_dense_grid(path)
    assert arr.shape == field.shape
    assert arr.dtype == np.float32
    assert np.array_equal(arr, field)
    assert tuple(round(v, 6) for v in voxel_size) == (0.25, 0.25, 0.25)
    with tinyvdb.open(path) as f:
        f.read_grids()
        assert f.grid(0).type_name == "Tree_vec3s_5_4_3"
        assert f.grid(0).name == "vel"


def test_dense_grid_bool_roundtrip(tmp_path):
    """BOOL grids round-trip self-consistently. NOTE: tinyvdb stores BOOL as
    1 byte/voxel, not OpenVDB's bit-packed format, so these files are NOT
    expected to load in DCCs (Houdini/Blender/etc)."""
    np = pytest.importorskip("numpy")
    field = (np.indices((5, 4, 3)).sum(axis=0) % 2 == 0)
    assert field.dtype == np.bool_
    path = str(tmp_path / "bool.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=0.1)
    arr, _, _ = tinyvdb.read_dense_grid(path)
    assert arr.dtype == np.bool_
    assert np.array_equal(arr, field)
    with tinyvdb.open(path) as f:
        f.read_grids()
        assert f.grid(0).type_name == "Tree_bool_5_4_3"


def test_dense_grid_unsupported_dtype(tmp_path):
    np = pytest.importorskip("numpy")
    with pytest.raises(ValueError):
        tinyvdb.write_dense_grid(str(tmp_path / "u.vdb"),
                                 np.zeros((3, 3, 3), dtype=np.uint16))


def test_write_grid_optional_args(tmp_path):
    """Low-level write_grid honors its documented-optional args (regression: the
    format string was missing `|`, making them mandatory)."""
    np = pytest.importorskip("numpy")
    a = np.arange(2 * 3 * 4, dtype=np.float32).reshape(2, 3, 4)
    path = str(tmp_path / "wg.vdb")
    # Omit voxel_size / origin / name / background / compression / level -> defaults.
    tinyvdb.write_grid(path, a.reshape(-1).tobytes(), 2, 3, 4, "float32")
    arr, vs, org = tinyvdb.read_dense_grid(path)
    assert arr.shape == (2, 3, 4) and np.array_equal(arr, a)
    assert tuple(round(v, 6) for v in vs) == (1.0, 1.0, 1.0)   # default voxel size


# ------------------------------------------------------------------- sparse grids
#
# write_sparse_grid / read_sparse_grid: explicit (coords, values) active voxels,
# value type chosen from the values dtype. Coords need not be contiguous.


def _sorted_pairs(coords, values):
    """Sort (coords, values) by coord for order-independent comparison."""
    import numpy as np
    order = np.lexsort(coords.T)
    return coords[order], values[order]


@pytest.mark.parametrize("dtype, type_name", [
    ("float32", "Tree_float_5_4_3"),
    ("float64", "Tree_double_5_4_3"),
    ("int32", "Tree_int32_5_4_3"),
    ("int64", "Tree_int64_5_4_3"),
])
def test_sparse_grid_scalar_roundtrip(tmp_path, dtype, type_name):
    np = pytest.importorskip("numpy")
    # Coords spanning several leaves, deliberately unordered and sparse.
    coords = np.array([[0, 0, 0], [10, 2, 3], [100, 100, 100], [5, 5, 5], [8, 0, 0]],
                      dtype=np.int32)
    values = (np.arange(len(coords)) * 7 - 3).astype(dtype)
    path = str(tmp_path / f"sparse_{dtype}.vdb")
    tinyvdb.write_sparse_grid(path, coords, values, voxel_size=(0.1, 0.2, 0.3),
                              origin=(1.0, -2.0, 3.0), name="sp")
    rc, rv, vs, org = tinyvdb.read_sparse_grid(path)
    assert rv.dtype == np.dtype(dtype)
    assert len(rc) == len(coords)
    ic, iv = _sorted_pairs(coords, values)
    oc, ov = _sorted_pairs(rc, rv)
    assert np.array_equal(oc, ic)
    assert np.array_equal(ov, iv)
    assert tuple(round(v, 6) for v in vs) == (0.1, 0.2, 0.3)
    assert tuple(round(v, 6) for v in org) == (1.0, -2.0, 3.0)
    with tinyvdb.open(path) as f:
        f.read_grids()
        assert f.grid(0).type_name == type_name
        assert f.grid(0).name == "sp"


def test_sparse_grid_vec3f_roundtrip(tmp_path):
    np = pytest.importorskip("numpy")
    coords = np.array([[0, 0, 0], [9, 9, 9], [40, 1, 2]], dtype=np.int32)
    values = np.random.default_rng(3).standard_normal((len(coords), 3)).astype(np.float32)
    path = str(tmp_path / "sparse_vec3f.vdb")
    tinyvdb.write_sparse_grid(path, coords, values, voxel_size=0.25)
    rc, rv, _, _ = tinyvdb.read_sparse_grid(path)
    assert rv.shape == values.shape and rv.dtype == np.float32
    order_in = np.lexsort(coords.T)
    order_out = np.lexsort(rc.T)
    assert np.array_equal(rc[order_out], coords[order_in])
    assert np.array_equal(rv[order_out], values[order_in])
    with tinyvdb.open(path) as f:
        f.read_grids()
        assert f.grid(0).type_name == "Tree_vec3s_5_4_3"


def test_sparse_grid_bool_roundtrip(tmp_path):
    np = pytest.importorskip("numpy")
    coords = np.array([[0, 0, 0], [1, 2, 3], [16, 16, 16]], dtype=np.int32)
    values = np.array([True, False, True])
    path = str(tmp_path / "sparse_bool.vdb")
    tinyvdb.write_sparse_grid(path, coords, values)
    rc, rv, _, _ = tinyvdb.read_sparse_grid(path)
    assert rv.dtype == np.bool_
    order_in = np.lexsort(coords.T)
    order_out = np.lexsort(rc.T)
    assert np.array_equal(rv[order_out], values[order_in])


def test_sparse_grid_length_mismatch(tmp_path):
    np = pytest.importorskip("numpy")
    with pytest.raises(ValueError):
        tinyvdb.write_sparse_grid(str(tmp_path / "m.vdb"),
                                  np.zeros((4, 3), dtype=np.int32),
                                  np.zeros((3,), dtype=np.float32))


def test_sparse_grid_bad_coords_shape(tmp_path):
    np = pytest.importorskip("numpy")
    with pytest.raises(ValueError):
        tinyvdb.write_sparse_grid(str(tmp_path / "m.vdb"),
                                  np.zeros((4, 2), dtype=np.int32),
                                  np.zeros((4,), dtype=np.float32))


def test_sparse_dense_consistency(tmp_path):
    """A dense grid materialized to sparse coords/values writes the same file."""
    np = pytest.importorskip("numpy")
    field = np.arange(6 * 5 * 4, dtype=np.float32).reshape(6, 5, 4)
    # Build the explicit (coords, values) for every voxel in C order.
    ii, jj, kk = np.meshgrid(np.arange(6), np.arange(5), np.arange(4), indexing="ij")
    coords = np.stack([ii.ravel(), jj.ravel(), kk.ravel()], axis=1).astype(np.int32)
    values = field.ravel()
    sp = str(tmp_path / "sp.vdb")
    tinyvdb.write_sparse_grid(sp, coords, values, voxel_size=0.5)
    arr, _, _ = tinyvdb.read_dense_grid(sp)   # read back densely
    assert arr.shape == field.shape
    assert np.array_equal(arr, field)
