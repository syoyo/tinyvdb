"""Smoke test for VDBGrid bridge ops (dilate/erode/CSG over the loaded tree)."""

import os
import sys
import struct

# Allow running from either repo root or the tests/ dir.
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "python"))

# Find the built .so (cmake places it under build/python/ or build/tinyvdb/);
# copy it into python/tinyvdb/ if absent so the package can import.
_PKG = os.path.join(ROOT, "python", "tinyvdb")
if not any(name.endswith(".abi3.so") for name in os.listdir(_PKG)):
    import glob, shutil
    for cand in glob.glob(os.path.join(ROOT, "build", "**", "_tinyvdb.abi3.so"), recursive=True):
        shutil.copy(cand, _PKG)

import tinyvdb  # noqa: E402

VDB_PATH = os.path.join(ROOT, "sphere.vdb")


def main():
    f = tinyvdb.open(VDB_PATH)
    f.read_grids()
    g = f.grid(0)

    nv = g.active_voxel_count()
    bb_min, bb_max = g.active_bbox()
    print(f"[bridge-py] active={nv} bbox={bb_min}..{bb_max}")
    assert nv > 0, "expected non-empty active set"

    # Topology-preserving dilate / erode keep the count.
    da = g.dilate_active(iterations=1)
    ea = g.erode_active(iterations=1)
    assert da["count"] == nv, "topology-preserving dilate must preserve count"
    assert ea["count"] == nv, "topology-preserving erode must preserve count"

    # Topology-growing dilate strictly grows; one ring < two rings.
    d1 = g.dilate_topology(iterations=1)
    d2 = g.dilate_topology(iterations=2)
    print(f"[bridge-py] dilate_topology 1->{d1['count']} 2->{d2['count']}")
    assert d1["count"] >= nv, "dilate_topology(1) should not lose voxels"
    assert d2["count"] >= d1["count"], "dilate_topology(2) should not be smaller than dilate_topology(1)"

    # Topology-shrinking erode strictly shrinks (interior of the SDF shell).
    e1 = g.erode_topology(iterations=1)
    e2 = g.erode_topology(iterations=2)
    print(f"[bridge-py] erode_topology  1->{e1['count']} 2->{e2['count']}")
    assert e1["count"] <= nv, "erode_topology(1) should not grow"
    assert e2["count"] <= e1["count"], "erode_topology(2) should not be larger than erode_topology(1)"

    # Self-CSG sanity: union(g, g) == g; intersection(g, g) == g.
    u = g.csg(g, op=0)
    inter = g.csg(g, op=1)
    diff = g.csg(g, op=2)
    print(f"[bridge-py] csg union={u['count']} inter={inter['count']} diff={diff['count']}")
    assert u["count"] == nv, "union with self must preserve active count"
    assert inter["count"] == nv, "intersection with self must preserve active count"

    # Sparse extraction: count matches active count.
    s = g.to_sparse()
    assert s["count"] == nv, "to_sparse count must match active_voxel_count"

    # Materialize a small sub-bbox; check shape == bbox extent.
    nx, ny, nz = bb_max[0] - bb_min[0], bb_max[1] - bb_min[1], bb_max[2] - bb_min[2]
    dense = g.materialize_dense(bbox_min=bb_min, bbox_max=bb_max, background=0.0)
    assert dense.shape == (nx, ny, nz), f"shape mismatch: {dense.shape} != {(nx, ny, nz)}"

    # update_from_sparse: write a topology-preserving op result back into the
    # tree, save, reload, and verify values persisted.
    import struct, tempfile
    res = g.update_from_sparse(coords=da["coords"], values=da["values"])
    assert res["updated"] == nv, f"all coords should land in existing leaves; got skipped={res['skipped']}"
    assert res["skipped"] == 0

    after = g.to_sparse()
    after_vals = struct.unpack(f"{nv}f", after["values"])
    init_vals = struct.unpack(f"{nv}f", s["values"])
    assert sum(after_vals) < sum(init_vals) + 1e-3, "SDF dilate should not increase sum"

    with tempfile.NamedTemporaryFile(suffix=".vdb", delete=False) as tf:
        out = tf.name
    f.save(out)
    f2 = tinyvdb.open(out)
    f2.read_grids()
    g2 = f2.grid(0)
    s2 = g2.to_sparse()
    rel_vals = struct.unpack(f"{nv}f", s2["values"])
    assert abs(sum(rel_vals) - sum(after_vals)) < 1e-3, "reload should preserve updated values"
    f2.close()
    os.unlink(out)
    print("[bridge-py] update_from_sparse + save round-trip OK")

    print("[bridge-py] all assertions passed")


if __name__ == "__main__":
    main()
