"""Theme D: coordinate utilities and point/coordinate spatial queries."""

import pytest

import tinyvdb


def test_world_ijk_roundtrip():
    np = pytest.importorskip("numpy")
    vs, org = (0.1, 0.2, 0.05), (-1.0, 0.5, 2.0)
    ijk = np.array([[3, -2, 17], [0, 0, 0], [10, 5, -4]], dtype=np.int32)
    w = tinyvdb.ijk_to_world(ijk, vs, org)
    assert np.array_equal(tinyvdb.world_to_ijk(w, vs, org), ijk)


def test_morton_roundtrip():
    np = pytest.importorskip("numpy")
    c = np.array([[0, 0, 0], [1, 2, 3], [-5, 7, -9], [1000, -1000, 500], [-1, -1, -1]],
                 dtype=np.int32)
    assert np.array_equal(tinyvdb.morton_decode(tinyvdb.morton_encode(c)), c)


def test_voxelize_points_dedup():
    np = pytest.importorskip("numpy")
    org = (-1.0, 0.5, 2.0)
    vs = (0.1, 0.2, 0.05)
    pts = np.array([
        [-1.0 + 0.05, 0.5 + 0.05, 2.0 + 0.01],   # (0,0,0)
        [-1.0 + 0.07, 0.5 + 0.09, 2.0 + 0.02],   # (0,0,0)
        [-1.0 + 0.15, 0.5 + 0.05, 2.0 + 0.01],   # (1,0,0)
        [-1.0 + 0.05, 0.5 + 0.25, 2.0 + 0.01],   # (0,1,0)
    ], dtype=np.float32)
    vox = tinyvdb.voxelize_points(pts, vs, org)
    assert vox.shape == (3, 3)
    # Round-trip: every original point's voxel is in the voxelized set.
    assert tinyvdb.points_in_grid(pts, vox, vs, org).all()


def test_membership_and_index():
    np = pytest.importorskip("numpy")
    active = np.array([[0, 0, 0], [5, 5, 5], [-3, 2, 1]], dtype=np.int32)
    query = np.array([[5, 5, 5], [0, 0, 0], [9, 9, 9], [-3, 2, 1]], dtype=np.int32)
    assert tinyvdb.coords_in_grid(active, query).tolist() == [True, True, False, True]
    assert tinyvdb.ijk_to_index(active, query).tolist() == [1, 0, -1, 2]


def test_points_in_grid():
    np = pytest.importorskip("numpy")
    active = np.array([[5, 5, 5]], dtype=np.int32)
    pts = np.array([[0.53, 0.53, 0.53], [5.0, 0.0, 0.0]], dtype=np.float32)  # vs=0.1
    assert tinyvdb.points_in_grid(pts, active, 0.1).tolist() == [True, False]


def test_neighbor_counts():
    np = pytest.importorskip("numpy")
    blk = np.array([[x, y, z] for z in range(2) for y in range(2) for x in range(2)],
                   dtype=np.int32)
    assert tinyvdb.neighbor_counts(blk, 6).tolist() == [3] * 8
    assert tinyvdb.neighbor_counts(blk, 26).tolist() == [7] * 8
    # An isolated voxel has no neighbors.
    assert tinyvdb.neighbor_counts(np.array([[100, 100, 100]], dtype=np.int32)).tolist() == [0]


def test_sample_quadratic_reproduces_linear():
    np = pytest.importorskip("numpy")
    nx, ny, nz, vs = 20, 8, 8, 0.1
    g = tinyvdb.DenseGrid(nx=nx, ny=ny, nz=nz, voxel_size=vs, ox=-1.0)
    wx = -1.0 + (np.arange(nx) + 0.5) * vs
    np.asarray(g)[:] = np.broadcast_to(wx[None, None, :], (nz, ny, nx))
    # Sample away from the border (the 3-wide stencil clamps at the outer cell).
    pts = np.array([[-0.5, 0.2, 0.3], [0.3, 0.1, 0.4], [0.0, 0.3, 0.2]], dtype=np.float32)
    q = np.frombuffer(tinyvdb.sample_quadratic(g, pts.tobytes()), dtype=np.float32)
    assert np.allclose(q, pts[:, 0], atol=1e-4)


def test_points_to_mask():
    np = pytest.importorskip("numpy")
    pts = np.array([[0.05, 0.05, 0.05], [0.35, 0.05, 0.05], [0.05, 0.05, 0.05]],
                   dtype=np.float32)
    mask = tinyvdb.points_to_mask(pts, 0.1)
    arr = np.asarray(mask, copy=False)
    assert arr.shape == (1, 1, 4)             # (nz, ny, nx); x spans voxels 0..3
    assert arr.sum() == 2.0                   # two distinct occupied voxels
    assert arr[0, 0, 0] == 1.0 and arr[0, 0, 3] == 1.0


def test_scatter_points_in_sdf():
    np = pytest.importorskip("numpy")
    s = tinyvdb.level_set_sphere(1.0, center=(0, 0, 0), voxel_size=0.1)
    pts = tinyvdb.scatter_points_in_sdf(s, 400, seed=3)
    assert pts.shape == (400, 3)
    # All points lie inside the sphere (within a voxel of the surface).
    assert np.all(np.linalg.norm(pts, axis=1) < 1.0 + 0.1)
