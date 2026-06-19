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


# ----------------------------------------------------------- signed flood fill

def test_signed_flood_fill_restores_interior():
    np = pytest.importorskip("numpy")
    band = 0.15
    s = tinyvdb.level_set_sphere(1.0, center=(0, 0, 0), voxel_size=0.05, half_width=3.0)
    a = np.asarray(s, copy=False)
    far = np.abs(a) >= band - 1e-5
    a[far] = band                                    # wipe the far interior sign
    # Far -band voxels are gone; only the narrow band's negatives remain (> -band).
    assert a.min() > -band + 1e-5
    out = tinyvdb.signed_flood_fill(s, band)
    o = np.asarray(out, copy=False)
    assert o.min() >= -band - 1e-5 and o.max() <= band + 1e-5
    # The deep interior is restored to exactly -band.
    assert o.min() == pytest.approx(-band, abs=1e-5)


# ------------------------------------------------------------------ advection

def _uniform_velocity(nx, ny, nz, vec, voxel_size=0.1, origin=(0.0, 0.0, 0.0)):
    np = pytest.importorskip("numpy")
    g = tinyvdb.DenseVecGrid(nx=nx, ny=ny, nz=nz, voxel_size=float(voxel_size),
                             ox=float(origin[0]), oy=float(origin[1]), oz=float(origin[2]))
    a = np.asarray(g)
    a[..., 0], a[..., 1], a[..., 2] = vec
    return g


@pytest.mark.parametrize("scheme", [
    tinyvdb.ADVECT_RK1, tinyvdb.ADVECT_RK2, tinyvdb.ADVECT_RK3,
    tinyvdb.ADVECT_RK4, tinyvdb.ADVECT_MACCORMACK, tinyvdb.ADVECT_BFECC,
])
def test_advect_shifts_linear_field(scheme):
    np = pytest.importorskip("numpy")
    nx, ny, nz, vs = 24, 8, 8, 0.1
    f = _dense(np.broadcast_to((-1.0 + (np.arange(nx) + 0.5) * vs)[None, None, :],
                               (nz, ny, nx)), voxel_size=vs, origin=(-1.0, 0.0, 0.0))
    vel = _uniform_velocity(nx, ny, nz, (1.0, 0.0, 0.0), voxel_size=vs, origin=(-1.0, 0, 0))
    r = np.asarray(tinyvdb.advect(f, vel, 0.1, scheme=scheme, clamp=1), copy=False)
    wx = -1.0 + (np.arange(nx) + 0.5) * vs
    ref = np.broadcast_to((wx - 0.1)[None, None, 2:nx-2], r[:, :, 2:nx-2].shape)
    assert np.max(np.abs(r[:, :, 2:nx-2] - ref)) < 1e-3


def test_advect_maccormack_less_diffusive_than_rk1():
    np = pytest.importorskip("numpy")
    n, vs = 24, 0.1
    c = (n - 1) / 2.0
    g1 = np.exp(-((np.arange(n) - c) ** 2) / (2 * 4.0 ** 2)).astype(np.float32)
    bump = (g1[:, None, None] * g1[None, :, None] * g1[None, None, :]).astype(np.float32)
    f = _dense(bump, voxel_size=vs)
    vel = _uniform_velocity(n, n, n, (1.0, 0.0, 0.0), voxel_size=vs)
    f0 = np.asarray(f, copy=True)

    def roundtrip_err(scheme):
        fwd = tinyvdb.advect(f, vel, 0.05, scheme=scheme, clamp=1)   # 0.5-voxel shift
        back = tinyvdb.advect(fwd, vel, -0.05, scheme=scheme, clamp=1)
        return float(np.max(np.abs(np.asarray(back, copy=False) - f0)))

    err_rk1 = roundtrip_err(tinyvdb.ADVECT_RK1)
    err_mac = roundtrip_err(tinyvdb.ADVECT_MACCORMACK)
    assert err_mac < err_rk1                                          # less numerical diffusion
