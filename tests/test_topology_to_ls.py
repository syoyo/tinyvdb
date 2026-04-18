import tinyvdb
import numpy as np

# Create a simple dense grid
grid = tinyvdb.DenseGrid(nx=10, ny=10, nz=10, voxel_size=1.0)
data = np.zeros((10, 10, 10), dtype=np.float32)
data[4:6, 4:6, 4:6] = 1.0 # Active region
grid.set_data(data)

# Test topology_to_level_set
sdf = tinyvdb.topology_to_level_set(grid)
print("SDF data shape:", sdf.get_data().shape)
assert sdf.get_data().shape == (10, 10, 10)
print("Success: TopologyToLevelSet python test passed.")
