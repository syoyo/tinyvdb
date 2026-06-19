"""Level-set primitive generators + SDF utilities.

Covers tinyvdb.level_set_sphere/box/torus/capsule (analytic narrow-band SDFs)
and the sdf_to_fog_volume / sdf_interior_mask utilities, including an analytic
correctness check on the sphere and a write/read round-trip.
"""

import math

import pytest

import tinyvdb


def _voxel_centers(grid):
    """Return (X, Y, Z) meshgrids of world voxel-center coords for a DenseGrid."""
    np = pytest.importorskip("numpy")
    nx, ny, nz = grid.shape
    ox, oy, oz = grid.origin
    vs = grid.voxel_size
    xs = ox + (np.arange(nx) + 0.5) * vs
    ys = oy + (np.arange(ny) + 0.5) * vs
    zs = oz + (np.arange(nz) + 0.5) * vs
    return np.meshgrid(xs, ys, zs, indexing="ij")


def test_sphere_analytic():
    np = pytest.importorskip("numpy")
    radius, vs, hw = 1.0, 0.1, 3.0
    bg = hw * vs
    g = tinyvdb.level_set_sphere(radius, center=(0.3, -0.2, 0.5),
                                 voxel_size=vs, half_width=hw)
    arr = np.array(g, copy=False)
    assert arr.dtype == np.float32
    X, Y, Z = _voxel_centers(g)
    ref = np.sqrt((X - 0.3) ** 2 + (Y + 0.2) ** 2 + (Z - 0.5) ** 2) - radius
    ref = np.clip(ref, -bg, bg)
    assert np.max(np.abs(arr - ref)) < 1e-4
    assert (arr < 0).any() and (arr > 0).any()
    assert arr.min() >= -bg - 1e-6 and arr.max() <= bg + 1e-6


def test_box_torus_capsule_sane():
    np = pytest.importorskip("numpy")
    vs, hw = 0.1, 3.0
    bg = hw * vs
    for g in (tinyvdb.level_set_box((0.5, 0.4, 0.6), voxel_size=vs),
              tinyvdb.level_set_torus(1.0, 0.3, voxel_size=vs),
              tinyvdb.level_set_capsule((-0.5, 0.0, 0.0), (0.5, 0.0, 0.2), 0.25, voxel_size=vs)):
        a = np.array(g, copy=False)
        assert a.dtype == np.float32
        assert min(g.shape) > 0
        assert (a < 0).any() and (a > 0).any()        # interior + exterior
        assert a.min() >= -bg - 1e-6 and a.max() <= bg + 1e-6


def test_box_corner_distance():
    """Outside a box corner, distance equals the analytic corner distance."""
    np = pytest.importorskip("numpy")
    he = (0.5, 0.5, 0.5)
    g = tinyvdb.level_set_box(he, center=(0, 0, 0), voxel_size=0.1)
    X, Y, Z = _voxel_centers(g)
    qx = np.abs(X) - he[0]
    qy = np.abs(Y) - he[1]
    qz = np.abs(Z) - he[2]
    outside = np.sqrt(np.maximum(qx, 0) ** 2 + np.maximum(qy, 0) ** 2 + np.maximum(qz, 0) ** 2)
    inside = np.minimum(np.maximum(qx, np.maximum(qy, qz)), 0.0)
    ref = np.clip(outside + inside, -0.3, 0.3)
    assert np.max(np.abs(np.array(g, copy=False) - ref)) < 1e-4


def test_sdf_to_fog_volume():
    np = pytest.importorskip("numpy")
    g = tinyvdb.level_set_sphere(1.0, voxel_size=0.1, half_width=3.0)
    sdf = np.array(g, copy=False)
    fog = np.array(tinyvdb.sdf_to_fog_volume(g, half_width=3.0), copy=False)
    assert fog.shape == sdf.shape
    assert fog.min() >= 0.0 and fog.max() <= 1.0
    assert np.all(fog[sdf >= 0.0] == 0.0)          # exterior is empty
    assert fog.max() > 0.99                         # deep interior saturates


def test_sdf_interior_mask():
    np = pytest.importorskip("numpy")
    g = tinyvdb.level_set_sphere(1.0, voxel_size=0.1)
    sdf = np.array(g, copy=False)
    mask = np.array(tinyvdb.sdf_interior_mask(g, isovalue=0.0), copy=False)
    assert set(np.unique(mask).tolist()) <= {0.0, 1.0}
    assert np.array_equal(mask == 1.0, sdf < 0.0)
    # Non-zero isovalue grows the interior.
    mask2 = np.array(tinyvdb.sdf_interior_mask(g, isovalue=0.1), copy=False)
    assert mask2.sum() > mask.sum()


def test_primitive_roundtrips_to_vdb(tmp_path):
    """A generated SDF writes to .vdb and reads back bit-exactly."""
    np = pytest.importorskip("numpy")
    g = tinyvdb.level_set_torus(1.0, 0.3, voxel_size=0.08)
    a = np.array(g, copy=True)
    path = str(tmp_path / "torus.vdb")
    tinyvdb.write_dense_grid(path, a, voxel_size=g.voxel_size, origin=g.origin, name="torus")
    b, vs, org = tinyvdb.read_dense_grid(path)
    assert np.array_equal(a, b)
    assert round(vs[0], 6) == round(g.voxel_size, 6)


def test_error_paths():
    with pytest.raises((ValueError, tinyvdb.VDBError)):
        tinyvdb.level_set_sphere(-1.0)              # negative radius
    with pytest.raises((ValueError, tinyvdb.VDBError)):
        tinyvdb.level_set_sphere(1.0, voxel_size=0.0)
