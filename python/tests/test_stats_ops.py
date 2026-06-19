"""Statistics / diagnostics and dense operators (Theme B).

Covers grid_statistics / grid_histogram / check_level_set / check_fog_volume,
plus the magnitude/normalize/cpt/composite/filter operators.
"""

import math

import pytest

import tinyvdb


def _dense(arr, voxel_size=0.1):
    """Wrap a 3D float32 numpy array in a DenseGrid (numpy view is (nz,ny,nx))."""
    np = pytest.importorskip("numpy")
    a = np.ascontiguousarray(arr, dtype=np.float32)
    nz, ny, nx = a.shape
    dg = tinyvdb.DenseGrid(nx=nx, ny=ny, nz=nz, voxel_size=float(voxel_size))
    np.asarray(dg)[:] = a
    return dg


# --------------------------------------------------------------- statistics

def test_grid_statistics_known():
    np = pytest.importorskip("numpy")
    field = np.arange(1000, dtype=np.float32).reshape(10, 10, 10)
    s = tinyvdb.grid_statistics(_dense(field))
    assert s["count"] == 1000
    assert s["min"] == 0.0 and s["max"] == 999.0
    assert abs(s["mean"] - 499.5) < 1e-4
    assert abs(s["sum"] - 499500.0) < 1.0
    assert abs(s["stddev"] - math.sqrt((1e6 - 1) / 12.0)) < 1e-2


def test_grid_statistics_constant():
    np = pytest.importorskip("numpy")
    s = tinyvdb.grid_statistics(_dense(np.full((4, 4, 4), 2.5, dtype=np.float32)))
    assert s["min"] == 2.5 and s["max"] == 2.5 and s["stddev"] == 0.0


def test_grid_histogram():
    np = pytest.importorskip("numpy")
    field = np.arange(1000, dtype=np.float32).reshape(10, 10, 10)
    counts = tinyvdb.grid_histogram(_dense(field), 0.0, 1000.0, nbins=10)
    assert len(counts) == 10
    assert sum(counts) == 1000
    assert all(c == 100 for c in counts)


# --------------------------------------------------------------- diagnostics

def test_check_level_set_clean_vs_damaged():
    np = pytest.importorskip("numpy")
    s = tinyvdb.level_set_sphere(1.0, voxel_size=0.05)
    clean = tinyvdb.check_level_set(s, band_width=0.08, tol=0.05)
    assert clean["band_count"] > 0
    assert abs(clean["mean_grad_mag"] - 1.0) < 0.05
    assert clean["bad_fraction"] < 0.05

    np.asarray(s)[:] *= 3.0
    damaged = tinyvdb.check_level_set(s, band_width=0.08, tol=0.05)
    assert abs(damaged["mean_grad_mag"] - 3.0) < 0.1
    assert damaged["bad_fraction"] > 0.9


def test_check_fog_volume():
    s = tinyvdb.level_set_sphere(1.0, voxel_size=0.05)
    assert tinyvdb.check_fog_volume(s)["valid"] is False          # SDF has negatives
    fog = tinyvdb.sdf_to_fog_volume(s)
    chk = tinyvdb.check_fog_volume(fog)
    assert chk["valid"] is True
    assert chk["min"] >= -1e-5 and chk["max"] <= 1.0 + 1e-5


# ----------------------------------------------------------- vector operators

def test_magnitude_and_normalize():
    np = pytest.importorskip("numpy")
    s = tinyvdb.level_set_sphere(1.0, voxel_size=0.06)
    grad = tinyvdb.gradient(s)                       # |grad| ~ 1 in the band
    mag = np.asarray(tinyvdb.magnitude(grad), copy=False)
    assert abs(float(np.median(mag[mag > 0])) - 1.0) < 0.05
    nrm = np.asarray(tinyvdb.normalize(grad), copy=False).reshape(-1, 3)
    lens = np.linalg.norm(nrm, axis=1)
    nz = lens > 1e-6
    assert np.allclose(lens[nz], 1.0, atol=1e-4)     # unit length where nonzero


def test_cpt_maps_onto_sphere():
    np = pytest.importorskip("numpy")
    s = tinyvdb.level_set_sphere(1.0, center=(0, 0, 0), voxel_size=0.06)
    cp = np.asarray(tinyvdb.cpt(s), copy=False).reshape(-1, 3)
    sdf = np.asarray(s, copy=False).reshape(-1)
    band = np.abs(sdf) < 0.1
    dist = np.linalg.norm(cp[band], axis=1)          # |cpt - center| ~ R = 1
    assert np.all(np.abs(dist - 1.0) < 0.06)


# ----------------------------------------------------------------- composite

def test_composite():
    np = pytest.importorskip("numpy")
    a = tinyvdb.DenseGrid(nx=3, ny=3, nz=3, voxel_size=0.1)
    b = tinyvdb.DenseGrid(nx=3, ny=3, nz=3, voxel_size=0.1)
    np.asarray(a)[:] = 2.0
    np.asarray(b)[:] = 5.0
    assert np.asarray(tinyvdb.comp_max(a, b))[0, 0, 0] == 5.0
    assert np.asarray(tinyvdb.comp_min(a, b))[0, 0, 0] == 2.0
    assert np.asarray(tinyvdb.comp_sum(a, b))[0, 0, 0] == 7.0
    assert np.asarray(tinyvdb.comp_mult(a, b))[0, 0, 0] == 10.0
    with pytest.raises((ValueError, tinyvdb.VDBError)):
        tinyvdb.comp_max(a, tinyvdb.DenseGrid(nx=2, ny=2, nz=2, voxel_size=0.1))


# ------------------------------------------------------------------- filters

def test_median_filter_removes_impulse():
    np = pytest.importorskip("numpy")
    g = tinyvdb.DenseGrid(nx=5, ny=5, nz=5, voxel_size=0.1)
    np.asarray(g)[:] = 1.0
    np.asarray(g)[2, 2, 2] = 1000.0
    out = np.asarray(tinyvdb.median_filter(g, radius=1, iterations=1), copy=False)
    assert abs(out[2, 2, 2] - 1.0) < 1e-5


def test_mean_curvature_flow_shrinks_sphere():
    s = tinyvdb.level_set_sphere(1.0, voxel_size=0.05)
    v0 = tinyvdb.volume(s)
    out = tinyvdb.mean_curvature_flow(s, 0.0003, iterations=8)
    v1 = tinyvdb.volume(out)
    assert 0.0 < v1 < v0
