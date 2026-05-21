"""Unit tests for the dense float-grid / SDF writer.

Covers the raw C-backed API (``write_float_grid``, numpy-free via ``struct``) and the numpy
conveniences (``write_dense_grid`` / ``read_dense_grid``): geometry/value round-trips, the
``world = voxel_size*index + origin`` transform, compression modes, multi-leaf grids, an analytic
sphere SDF, and error handling.
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


def test_dense_grid_casts_to_float32(tmp_path):
    np = pytest.importorskip("numpy")
    field = (np.arange(4 * 4 * 4).reshape(4, 4, 4)).astype(np.float64)
    path = str(tmp_path / "cast.vdb")
    tinyvdb.write_dense_grid(path, field, voxel_size=0.1)
    arr, _, _ = tinyvdb.read_dense_grid(path)
    assert arr.dtype == np.float32
    assert np.array_equal(arr, field.astype(np.float32))


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
