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
