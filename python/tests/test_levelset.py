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


_PLATONIC = [
    (4, 1.0 / 3.0, "tetrahedron", tinyvdb.level_set_tetrahedron),
    (6, 0.57735027, "cube", tinyvdb.level_set_cube),
    (8, 0.57735027, "octahedron", tinyvdb.level_set_octahedron),
    (12, 0.79465447, "dodecahedron", tinyvdb.level_set_dodecahedron),
    (20, 0.79465447, "icosahedron", tinyvdb.level_set_icosahedron),
]


@pytest.mark.parametrize("face_count, ratio, name, wrapper", _PLATONIC)
def test_platonic_geometry(face_count, ratio, name, wrapper):
    """Each platonic sits between its inscribed (R*ratio) and circumscribed (R) sphere."""
    np = pytest.importorskip("numpy")
    R, vs, hw = 1.0, 0.05, 3.0
    bg = hw * vs
    center = (0.2, -0.1, 0.3)
    g = tinyvdb.level_set_platonic(face_count, R, center=center, voxel_size=vs, half_width=hw)
    a = np.array(g, copy=False)
    assert a.dtype == np.float32
    assert (a < 0).any() and (a > 0).any()
    assert a.min() >= -bg - 1e-6 and a.max() <= bg + 1e-6

    X, Y, Z = _voxel_centers(g)
    dist = np.sqrt((X - center[0]) ** 2 + (Y - center[1]) ** 2 + (Z - center[2]) ** 2)
    near = np.abs(a) <= vs
    assert near.any()
    nd = dist[near]
    inrad = R * ratio
    assert nd.min() >= inrad - 2 * vs and nd.min() <= inrad + 2 * vs   # touches inradius
    assert nd.max() >= R - 2 * vs                                       # reaches vertices
    assert nd.max() <= R + 3 * vs                                       # no further out

    # Named wrapper matches the face_count form bit-for-bit.
    gw = wrapper(R, center=center, voxel_size=vs, half_width=hw)
    assert np.array_equal(np.array(gw, copy=False), a)


def test_platonic_composes_and_roundtrips(tmp_path):
    np = pytest.importorskip("numpy")
    ico = tinyvdb.level_set_icosahedron(1.0, voxel_size=0.06)
    # Meshes via marching cubes (integration with the dense ops).
    mesh = tinyvdb.sdf_to_mesh(ico, isovalue=0.0)
    assert mesh.num_vertices > 0 and mesh.num_faces > 0
    # Transform-aware SDF union with an offset sphere (differing bboxes).
    sph = tinyvdb.level_set_sphere(0.9, center=(0.5, 0, 0), voxel_size=0.06)
    union = tinyvdb.merge_grids(ico, sph, background=ico.voxel_size * 3.0)
    assert min(union.shape) > 0
    # Round-trip the raw SDF.
    a = np.array(ico, copy=True)
    path = str(tmp_path / "ico.vdb")
    tinyvdb.write_dense_grid(path, a, voxel_size=ico.voxel_size, origin=ico.origin)
    b, _, _ = tinyvdb.read_dense_grid(path)
    assert np.array_equal(a, b)


def _dense_from_array(arr, voxel_size=0.1, origin=(0.0, 0.0, 0.0)):
    """Wrap a 3D float32 numpy array in a DenseGrid whose numpy view equals it.

    DenseGrid stores data x-fastest, so its numpy view has shape ``(nz, ny, nx)``;
    we size the grid accordingly so ``np.asarray(dg) == arr``.
    """
    np = pytest.importorskip("numpy")
    a = np.ascontiguousarray(arr, dtype=np.float32)
    nz, ny, nx = (int(d) for d in a.shape)
    dg = tinyvdb.DenseGrid(nx=nx, ny=ny, nz=nz, voxel_size=float(voxel_size),
                           ox=float(origin[0]), oy=float(origin[1]), oz=float(origin[2]))
    np.asarray(dg)[:] = a
    return dg


def test_sdf_segmentation_two_spheres():
    np = pytest.importorskip("numpy")
    # SDF union (min) of two well-separated spheres in one dense grid.
    nx, ny, nz, vs = 70, 32, 32, 0.1
    ii, jj, kk = np.meshgrid(np.arange(nx), np.arange(ny), np.arange(nz), indexing="ij")
    x, y, z = (ii + 0.5) * vs, (jj + 0.5) * vs, (kk + 0.5) * vs
    da = np.sqrt((x - 1.5) ** 2 + (y - 1.6) ** 2 + (z - 1.6) ** 2) - 0.7
    db = np.sqrt((x - 5.5) ** 2 + (y - 1.6) ** 2 + (z - 1.6) ** 2) - 0.7
    field = np.minimum(da, db).astype(np.float32)
    grid = _dense_from_array(field, voxel_size=vs)

    segs = tinyvdb.sdf_segmentation(grid, isovalue=0.0)
    assert len(segs) == 2
    total_neg = 0
    centroids = []
    for s in segs:
        arr = np.array(s, copy=False)
        assert arr.shape == field.shape
        neg = arr < 0.0
        assert neg.any()
        total_neg += int(neg.sum())
        xs = np.argwhere(neg)[:, 0]
        assert xs.max() - xs.min() < nx * 0.5      # one localized blob
        centroids.append(xs.mean())
    assert total_neg == int((field < 0.0).sum())    # exact partition
    assert abs(centroids[0] - centroids[1]) > 20    # the two blobs are far apart in x


def test_sdf_segmentation_single_component():
    np = pytest.importorskip("numpy")
    g = tinyvdb.level_set_sphere(1.0, voxel_size=0.1)
    segs = tinyvdb.sdf_segmentation(g)
    assert len(segs) == 1
    assert np.array_equal(np.array(segs[0], copy=False), np.array(g, copy=False))


def test_sdf_extract_enclosed_regions_shell():
    np = pytest.importorskip("numpy")
    # Spherical shell SDF: solid between ri and R, hollow cavity for |p| < ri.
    n, vs = 40, 0.1
    R, ri = 1.2, 0.7
    c = np.arange(n) * vs - 2.0 + 0.5 * vs
    X, Y, Z = np.meshgrid(c, c, c, indexing="ij")
    rr = np.sqrt(X ** 2 + Y ** 2 + Z ** 2)
    shell = np.maximum(rr - R, ri - rr).astype(np.float32)
    dg = _dense_from_array(shell, voxel_size=vs, origin=(-2.0, -2.0, -2.0))

    mask = np.array(tinyvdb.sdf_extract_enclosed_regions(dg, isovalue=0.0), copy=False)
    assert set(np.unique(mask).tolist()) <= {0.0, 1.0}
    marked = mask == 1.0
    assert marked.any()
    # Everything marked is inside the cavity; deep cavity is marked; open air isn't.
    assert np.all(rr[marked] <= ri + 1e-4)
    assert np.all(mask[rr < ri - vs] == 1.0)
    assert mask[0, 0, 0] == 0.0                    # corner = open exterior

    # A solid sphere has no enclosed regions.
    solid = tinyvdb.level_set_sphere(1.0, voxel_size=0.1)
    assert np.array(tinyvdb.sdf_extract_enclosed_regions(solid), copy=False).sum() == 0.0


@pytest.mark.parametrize("maker, euler, genus", [
    (lambda: tinyvdb.level_set_sphere(1.0, voxel_size=0.06), 2.0, 0),
    (lambda: tinyvdb.level_set_box((0.6, 0.5, 0.7), voxel_size=0.06), 2.0, 0),
    (lambda: tinyvdb.level_set_icosahedron(1.0, voxel_size=0.06), 2.0, 0),
    (lambda: tinyvdb.level_set_torus(1.0, 0.35, voxel_size=0.06), 0.0, 1),
])
def test_level_set_euler_genus(maker, euler, genus):
    g = maker()
    assert tinyvdb.level_set_euler_characteristic(g) == euler
    assert tinyvdb.level_set_genus(g) == genus


def test_level_set_genus_multi_component():
    np = pytest.importorskip("numpy")
    # Two separated tori -> euler 0, total genus 2.
    nx, ny, nz, vs = 100, 34, 34, 0.1
    ii, jj, kk = np.meshgrid(np.arange(nx), np.arange(ny), np.arange(nz), indexing="ij")
    x, y, z = (ii + 0.5) * vs, (jj + 0.5) * vs, (kk + 0.5) * vs
    R, r = 1.0, 0.35
    def torus(cx):
        q = np.sqrt((x - cx) ** 2 + (z - 1.7) ** 2) - R
        return np.sqrt(q ** 2 + (y - 1.7) ** 2) - r
    field = np.minimum(torus(1.7), torus(6.2)).astype(np.float32)
    g = _dense_from_array(field, voxel_size=vs)
    assert tinyvdb.level_set_euler_characteristic(g) == 0.0
    assert tinyvdb.level_set_genus(g) == 2


def test_level_set_rebuild_renormalizes():
    """Rebuilding a damaged (scaled) SDF recovers a clean sphere level set."""
    np = pytest.importorskip("numpy")
    # Coarse: mesh_to_sdf is brute-force O(voxels * triangles).
    s = tinyvdb.level_set_sphere(1.0, center=(0, 0, 0), voxel_size=0.15, half_width=2.0)
    np.asarray(s)[:] *= 3.0                         # break |grad|=1; zero crossing unchanged
    out = tinyvdb.level_set_rebuild(s, isovalue=0.0, voxel_size=0.15, half_width=2.0)
    assert abs(out.voxel_size - 0.15) < 1e-6
    # Topology preserved; a proper interior (negative band) exists again.
    assert tinyvdb.level_set_euler_characteristic(out) == 2.0
    assert tinyvdb.level_set_genus(out) == 0
    arr = np.asarray(out, copy=False)
    assert arr.min() < 0.0 and arr.max() > 0.0


def test_level_set_rebuild_resample_preserves_genus():
    out = tinyvdb.level_set_torus(1.0, 0.35, voxel_size=0.12, half_width=2.0)
    rebuilt = tinyvdb.level_set_rebuild(out, voxel_size=0.2, half_width=2.0)  # coarser
    assert abs(rebuilt.voxel_size - 0.2) < 1e-6
    assert tinyvdb.level_set_genus(rebuilt) == 1


def test_error_paths():
    with pytest.raises((ValueError, tinyvdb.VDBError)):
        tinyvdb.level_set_sphere(-1.0)              # negative radius
    with pytest.raises((ValueError, tinyvdb.VDBError)):
        tinyvdb.level_set_sphere(1.0, voxel_size=0.0)
    with pytest.raises((ValueError, tinyvdb.VDBError)):
        tinyvdb.level_set_platonic(5, 1.0)         # not a platonic face count
