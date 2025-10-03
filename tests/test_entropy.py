import math
from pathlib import Path
import sys

import pytest

# Ensure the project root is on the import path
sys.path.append(str(Path(__file__).resolve().parents[1]))

from sim_replay import entropy  # noqa: E402
from generative.entropy_tools import concept_entropy, distribution_from_concepts  # noqa: E402
from generative.protocol import generate  # noqa: E402


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


def test_entropy_increases_with_broader_sets():
    narrow = generate(["a"], rng_seed=1)
    wide = generate(["a", "b"], rng_seed=1)
    assert wide.entropy > narrow.entropy


def test_generation_is_deterministic_with_seed():
    first = generate(["x", "y"], rng_seed=123)
    second = generate(["x", "y"], rng_seed=123)
    assert first.concepts == second.concepts
    assert first.distribution == second.distribution


def test_generate_rejects_empty_seeds():
    with pytest.raises(ValueError, match="seeds"):
        generate([])


def test_generate_rejects_non_positive_per_seed():
    with pytest.raises(ValueError, match="per_seed"):
        generate(["x"], per_seed=0)
    with pytest.raises(ValueError, match="per_seed"):
        generate(["x"], per_seed=-1)


def test_entropy_rejects_invalid_total():
    with pytest.raises(ValueError):
        entropy([0.4, 0.4])


def test_entropy_accepts_total_close_to_one():
    p = [0.1] * 10
    expected = -sum(pi * math.log2(pi) for pi in p if pi > 0)
    assert entropy(p) == pytest.approx(expected)


def test_concept_entropy_empty_input_returns_zero():
    assert concept_entropy([]) == 0.0
    assert distribution_from_concepts([]) == []
