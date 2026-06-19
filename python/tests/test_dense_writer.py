"""Unit tests for the dense-grid writer / reader.

Covers the raw C-backed API (``write_float_grid``, numpy-free via ``struct``) and the numpy
conveniences (``write_dense_grid`` / ``read_dense_grid``): geometry/value round-trips, the
``world = voxel_size*index + origin`` transform, compression modes, multi-leaf grids, an analytic
sphere SDF, error handling, and the typed paths (``float64`` / ``int32`` / ``int64`` / ``vec3f`` /
``bool``) where the grid value type is chosen from the array dtype.
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
