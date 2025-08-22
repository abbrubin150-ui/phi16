import math
import sys
from pathlib import Path

import pytest

# Ensure the project root is on the import path
sys.path.append(str(Path(__file__).resolve().parents[1]))

from sim_replay import entropy  # noqa: E402


def test_uniform_distribution():
    n = 4
    p = [1 / n] * n
    assert entropy(p) == pytest.approx(math.log2(n))


def test_zero_probability_entries():
    p = [0.5, 0.5, 0.0]
    assert entropy(p) == pytest.approx(1.0)


def test_degenerate_single_value():
    p = [1.0]
    assert entropy(p) == pytest.approx(0.0)
