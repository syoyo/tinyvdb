import math
import numpy as np
import pytest
import tinyvdb


@pytest.fixture(scope="session")
def data_dir(tmp_path_factory):
    """Generate a closed analytic band without downloaded test data."""
    directory = tmp_path_factory.mktemp("vdb-fixtures")
    coords, values = [], []
    for x in range(-8, 9):
        for y in range(-8, 9):
            for z in range(-8, 9):
                phi = math.sqrt(x*x + y*y + z*z) - 5
                if abs(phi) < 3:
                    coords.append((x, y, z))
                    values.append(phi)
    path = str(directory / "sphere.vdb")
    tinyvdb.write_sparse_grid(path, np.asarray(coords, dtype=np.int32),
                             np.asarray(values, dtype=np.float32), background=3)
    with tinyvdb.open(path) as file:
        file.read_grids()
        filled = file.grid(0).signed_flood_fill()
    filled.save(path)
    return str(directory)
