import os
import pytest

@pytest.fixture
def data_dir():
    """Return path to test data directory (repo root)."""
    return os.path.join(os.path.dirname(__file__), "..", "..")
