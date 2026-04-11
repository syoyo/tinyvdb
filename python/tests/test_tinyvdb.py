"""Tests for tinyvdb Python bindings."""

import os
import struct
import pytest
import tinyvdb


def test_version():
    assert hasattr(tinyvdb, "__version__")
    assert tinyvdb.__version__ == "0.8.0"


def test_constants():
    assert tinyvdb.COMPRESS_NONE == 0
    assert tinyvdb.COMPRESS_ZIP == 1
    assert tinyvdb.COMPRESS_ACTIVE_MASK == 2
    assert tinyvdb.COMPRESS_BLOSC == 4
    assert tinyvdb.SIGN_FLOOD_FILL == 0
    assert tinyvdb.SIGN_SWEEP == 1


def test_vdbfile_no_args():
    """VDBFile with no args creates empty object."""
    f = tinyvdb.VDBFile()
    assert f.grid_count == 0
    f.close()


def test_vdbfile_open_nonexistent():
    with pytest.raises(tinyvdb.VDBError):
        tinyvdb.open("/nonexistent/path.vdb")


def test_vdbfile_context_manager():
    """Context manager calls close."""
    f = tinyvdb.VDBFile()
    with f:
        pass
    # After close, grid_count should be 0
    assert f.grid_count == 0


class TestDenseGrid:
    def test_create_empty(self):
        g = tinyvdb.DenseGrid()
        assert g.shape == (0, 0, 0)
        assert g.voxel_size == 1.0

    def test_create_with_dims(self):
        g = tinyvdb.DenseGrid(nx=4, ny=5, nz=6, voxel_size=0.5)
        assert g.shape == (4, 5, 6)
        assert g.voxel_size == 0.5
        assert g.size() == 120

    def test_get_set(self):
        g = tinyvdb.DenseGrid(nx=3, ny=3, nz=3, voxel_size=1.0)
        g.set((1, 1, 1), 42.0)
        assert abs(g.get((1, 1, 1)) - 42.0) < 1e-6

    def test_buffer_protocol(self):
        g = tinyvdb.DenseGrid(nx=2, ny=2, nz=2, voxel_size=1.0)
        buf = bytes(g)
        assert len(buf) == 2 * 2 * 2 * 4  # 8 floats * 4 bytes

    def test_to_bytes(self):
        g = tinyvdb.DenseGrid(nx=2, ny=2, nz=2)
        b = g.to_bytes()
        assert len(b) == 32  # 8 * sizeof(float)

    def test_origin(self):
        g = tinyvdb.DenseGrid(nx=1, ny=1, nz=1, ox=1.0, oy=2.0, oz=3.0)
        assert g.origin == (1.0, 2.0, 3.0)


class TestTriangleMesh:
    def test_create_empty(self):
        m = tinyvdb.TriangleMesh()
        assert m.num_vertices == 0
        assert m.num_faces == 0


class TestMeshToSDF:
    @staticmethod
    def _cube_mesh():
        """Simple cube mesh: 8 vertices, 12 triangles."""
        verts = struct.pack("24f",
            0, 0, 0,  1, 0, 0,  1, 1, 0,  0, 1, 0,
            0, 0, 1,  1, 0, 1,  1, 1, 1,  0, 1, 1)
        faces = struct.pack("36I",
            0,2,1, 0,3,2,  # -Z
            4,5,6, 4,6,7,  # +Z
            0,1,5, 0,5,4,  # -Y
            2,3,7, 2,7,6,  # +Y
            0,4,7, 0,7,3,  # -X
            1,2,6, 1,6,5)  # +X
        return verts, faces

    def test_mesh_to_sdf(self):
        verts, faces = self._cube_mesh()
        grid = tinyvdb.mesh_to_sdf(verts, faces, 0.1, 3.0)
        assert isinstance(grid, tinyvdb.DenseGrid)
        nx, ny, nz = grid.shape
        assert nx > 0 and ny > 0 and nz > 0

    def test_sdf_to_mesh(self):
        verts, faces = self._cube_mesh()
        grid = tinyvdb.mesh_to_sdf(verts, faces, 0.1, 3.0)
        mesh = tinyvdb.sdf_to_mesh(grid, 0.0)
        assert isinstance(mesh, tinyvdb.TriangleMesh)
        assert mesh.num_vertices > 0
        assert mesh.num_faces > 0


class TestCSG:
    def test_union(self):
        g1 = tinyvdb.DenseGrid(nx=4, ny=4, nz=4, voxel_size=1.0)
        g2 = tinyvdb.DenseGrid(nx=4, ny=4, nz=4, voxel_size=1.0)
        # Fill with positive values (exterior)
        for x in range(4):
            for y in range(4):
                for z in range(4):
                    g1.set((x, y, z), 1.0)
                    g2.set((x, y, z), 0.5)
        result = tinyvdb.csg_union(g1, g2)
        assert result.shape == (4, 4, 4)
        # Union = min, so all values should be 0.5
        assert abs(result.get((0, 0, 0)) - 0.5) < 1e-6


class TestMeasurement:
    def test_surface_area(self):
        g = tinyvdb.DenseGrid(nx=4, ny=4, nz=4, voxel_size=1.0)
        area = tinyvdb.surface_area(g)
        assert isinstance(area, float)

    def test_volume_val(self):
        g = tinyvdb.DenseGrid(nx=4, ny=4, nz=4, voxel_size=1.0)
        vol = tinyvdb.volume(g)
        assert isinstance(vol, float)


class TestVDBFileIO:
    """Tests requiring VDB files - skipped if no test data available."""

    @pytest.fixture
    def sphere_path(self, data_dir):
        p = os.path.join(data_dir, "sphere.vdb")
        if not os.path.exists(p):
            pytest.skip("sphere.vdb not found")
        return p

    def test_open_and_read(self, sphere_path):
        with tinyvdb.open(sphere_path) as f:
            assert f.grid_count > 0
            name = f.grid_name(0)
            assert isinstance(name, str)
            f.read_grids()
            g = f.grid(0)
            assert g.name == name

    def test_header(self, sphere_path):
        with tinyvdb.open(sphere_path) as f:
            h = f.header
            assert "file_version" in h
            assert "uuid" in h

    def test_tree_access(self, sphere_path):
        with tinyvdb.open(sphere_path) as f:
            f.read_grids()
            g = f.grid(0)
            tree = g.tree
            assert tree.num_nodes > 0
            node = tree.node(0)
            assert node.type in ("root", "internal", "leaf")

    def test_round_trip_bytes(self, sphere_path):
        with tinyvdb.open(sphere_path) as f:
            f.read_grids()
            data = f.to_bytes()
            assert len(data) > 0

        f2 = tinyvdb.from_bytes(data)
        f2.read_grids()
        assert f2.grid_count > 0
        f2.close()
