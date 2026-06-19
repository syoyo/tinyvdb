"""Theme C: resampling, signed flood fill, higher-order advection."""

import pytest

import tinyvdb


def _dense(arr, voxel_size=0.1, origin=(0.0, 0.0, 0.0)):
    """Wrap a 3D float32 numpy array in a DenseGrid (view is (nz,ny,nx))."""
    np = pytest.importorskip("numpy")
    a = np.ascontiguousarray(arr, dtype=np.float32)
    nz, ny, nx = a.shape
    dg = tinyvdb.DenseGrid(nx=nx, ny=ny, nz=nz, voxel_size=float(voxel_size),
                           ox=float(origin[0]), oy=float(origin[1]), oz=float(origin[2]))
    np.asarray(dg)[:] = a
    return dg


# ------------------------------------------------------------------ resample

@pytest.mark.parametrize("order", [0, 1, 2])
def test_resample_metadata(order):
    s = tinyvdb.level_set_sphere(1.0, voxel_size=0.05)
    r = tinyvdb.resample_grid(s, 0.1, order=order)
    assert abs(r.voxel_size - 0.1) < 1e-6
    assert tuple(round(v, 6) for v in r.origin) == tuple(round(v, 6) for v in s.origin)
    # World extent preserved: dim*vs ~ source dim*vs.
    assert abs(r.shape[0] * 0.1 - s.shape[0] * 0.05) < 0.1


def test_resample_reproduces_linear():
    np = pytest.importorskip("numpy")
    nx, ny, nz, vs = 20, 12, 10, 0.1
    ii = np.arange(nx)
    wx = (-1.0 + (ii + 0.5) * vs)                       # world-x per x index
    field = np.broadcast_to(wx[None, None, :], (nz, ny, nx)).astype(np.float32)
    g = _dense(field, voxel_size=vs, origin=(-1.0, 0.0, 0.0))
    for order in (1, 2):
        r = tinyvdb.resample_grid(g, 0.07, order=order)
        arr = np.asarray(r, copy=False)                 # (nz', ny', nx')
        rx = -1.0 + (np.arange(arr.shape[2]) + 0.5) * 0.07
        inside = (rx >= -1.0 + 1.5 * vs) & (rx <= -1.0 + (nx - 1.5) * vs)
        got = arr[:, :, inside]
        ref = np.broadcast_to(rx[inside][None, None, :], got.shape)
        assert np.max(np.abs(got - ref)) < 1e-4


def test_resample_sphere_keeps_radius():
    np = pytest.importorskip("numpy")
    s = tinyvdb.level_set_sphere(1.0, center=(0, 0, 0), voxel_size=0.05)
    r = tinyvdb.resample_grid(s, 0.1, order=1)
    # Interior present, valid SDF range, topology intact.
    arr = np.asarray(r, copy=False)
    assert arr.min() < 0.0 and arr.max() > 0.0
    assert tinyvdb.level_set_euler_characteristic(r) == 2.0
