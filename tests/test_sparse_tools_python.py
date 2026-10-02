"""Sparse tools: independent ownership, affine geometry, budgets and reports."""
import os
from pathlib import Path
import sys
import tempfile
import math
import struct
from python_test_bootstrap import load_extensions

load_extensions()
ROOT = Path(__file__).resolve().parent.parent
if os.environ.get("TINYVDB_TEST_INSTALLED") != "1":
    sys.path.insert(0, str(ROOT / "python"))
import tinyvdb


def raises(kind, call):
    try:
        call()
    except kind:
        return
    raise AssertionError("expected " + kind.__name__)


def write_sparse(path, coords, values, background=0):
    # Exercise the byte-buffer binding; this native API suite needs no NumPy.
    coord_bytes = struct.pack(f"{3 * len(coords)}i", *(v for c in coords for v in c))
    value_bytes = struct.pack(f"{len(values)}f", *values)
    tinyvdb._write_sparse_grid_c(path, coord_bytes, value_bytes, "float32",
                              background=struct.pack("f", background))


def main():
    with tempfile.TemporaryDirectory() as directory:
        path = str(Path(directory) / "sphere.vdb")
        coords, values = [], []
        for x in range(-8, 9):
            for y in range(-8, 9):
                for z in range(-8, 9):
                    phi = 2 * (math.sqrt(x*x + y*y + z*z) - 5)
                    if abs(phi) < 4:
                        coords.append((x, y, z))
                        values.append(phi)
        write_sparse(path, coords, values, background=4)
        f = tinyvdb.open(path)
        # Calling before read must fail safely.
        raises((ValueError, tinyvdb.VDBError), lambda: f.grid(0).track_level_set())
        f.read_grids()
        g = f.grid(0).signed_flood_fill()
        original = g.to_sparse()
        tracked = g.track_level_set(outside_width=3, inside_width=3)
        rebuilt = g.rebuild_level_set(isovalue=.5, outside_width=2, inside_width=2)
        assert tracked.active_voxel_count() > original["count"]
        assert tracked.diagnose(kind="level_set", tolerance=0)["valid"]
        assert rebuilt.active_voxel_count() > 0
        uniform = g.volume_to_mesh()
        adaptive = g.volume_to_mesh(adaptivity=1)
        assert adaptive.num_vertices < uniform.num_vertices
        assert adaptive.num_faces < uniform.num_faces
        identity = [[float(a == b) for b in range(4)] for a in range(4)]
        sampled = g.resample(identity, sampler="nearest")
        assert sampled.to_sparse() == original
        affine = [[0, -.5, .2, .25], [.5, 0, 0, 0], [0, 0, .75, 0], [0, 0, 0, 1]]
        transformed = g.resample(affine)
        assert transformed.diagnose()["valid"]
        for call in (lambda: g.resample(identity, max_voxels=1),
                     lambda: g.volume_to_mesh(max_cells=1),
                     lambda: g.track_level_set(max_voxels=1)):
            raises(tinyvdb.VDBError, call)
        raises(ValueError, lambda: g.resample([1, 2, 3]))
        raises(ValueError, lambda: g.resample(identity, sampler="cubic"))
        raises(ValueError, lambda: g.track_level_set(inside_width=-3))
        raises(ValueError, lambda: g.volume_to_mesh(adaptivity=float("nan")))
        assert g.to_sparse() == original
        f.close()
        assert transformed.diagnose()["valid"]
        payload = transformed.to_bytes()
        reload = tinyvdb.from_bytes(payload)
        reload.read_grids()
        assert reload.grid(0).diagnose()["valid"]
        reload.close()
        # Manufactured constant Dirichlet solution on a sparse domain.
        coords = [(x, y, z) for x in range(4) for y in range(4) for z in range(4)]
        write_sparse(path, coords, [0] * len(coords))
        f = tinyvdb.open(path)
        f.read_grids()
        g = f.grid(0)
        solution, report = g.solve_poisson(boundary_value=2)
        assert report["converged"] and report["iterations"] > 0
        assert all(abs(v[0] - 2) <= 1e-5 for v in
                   struct.iter_unpack("f", solution.to_sparse()["values"]))
        zero, report = g.solve_poisson(boundary="neumann")
        assert report["converged"] and report["iterations"] == 0
        budget, report = g.solve_poisson(boundary_value=2, max_iterations=0)
        assert not report["converged"]
        raises(ValueError, lambda: g.solve_poisson(coefficient=0))
        raises(tinyvdb.VDBError, lambda: g.solve_poisson(max_voxels=1))
        f.close()
        assert solution.diagnose()["valid"]
        raises(ValueError, lambda: g.solve_poisson())
        # Matrix conversion can run arbitrary Python; revalidate afterward.
        f = tinyvdb.open(path)
        f.read_grids()
        g = f.grid(0)
        class ClosingMatrix:
            def __len__(self):
                return 4
            def __getitem__(self, index):
                if index == 0:
                    f.close()
                return identity[index]
        raises(ValueError, lambda: g.resample(ClosingMatrix()))
    print("Python sparse tools passed")


if __name__ == "__main__":
    main()
