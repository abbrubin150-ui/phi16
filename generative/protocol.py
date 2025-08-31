"""Prototype concept generator aiming for high entropy.

The protocol accepts a small set of seed tags and deterministically
expands them into a list of concept identifiers.  Each seed is given an
equal number of generated concepts which yields a near uniform
probability distribution – maximising entropy for the given seeds.

The module outputs both the generated concept list and the corresponding
probability distribution so callers can evaluate the entropy using the
helpers from :mod:`generative.entropy_tools`.
"""
from __future__ import annotations

import random
from dataclasses import dataclass
from typing import List, Sequence

from .entropy_tools import (
    concept_entropy,
    distribution_from_concepts,
    normalised_entropy,
)


@dataclass
class GenerationResult:
    """Container returned by :func:`generate`.

    Attributes
    ----------
    concepts:
        The list of generated concept labels.
    distribution:
        Probability distribution derived from ``concepts``.
    entropy:
        Shannon entropy of ``distribution``.
    normalised_entropy:
        Entropy normalised by ``log2`` of the number of distinct concepts.
    """

    concepts: List[str]
    distribution: List[float]
    entropy: float
    normalised_entropy: float


def generate(
    seeds: Sequence[str],
    per_seed: int = 1,
    *,
    rng_seed: int | None = None,
) -> GenerationResult:
    """Generate a high-entropy concept set.

    Parameters
    ----------
    seeds:
        Seed labels used as the basis for concept generation.
    per_seed:
        How many concepts to derive from each ``seed``.  ``1`` by default.
    rng_seed:
        Optional random seed to keep generation deterministic in tests.

    Raises
    ------
    ValueError:
        If ``seeds`` is empty or ``per_seed`` is not a positive integer.
    """

    if not seeds:
        raise ValueError("seeds must be non-empty")
    if per_seed <= 0:
        raise ValueError("per_seed must be a positive integer")

    rng = random.Random(rng_seed)
    concepts: list[str] = []
    for tag in seeds:
        for i in range(per_seed):
            # Attach a random suffix to each seed to produce unique labels.
            suffix = rng.randint(0, 2**32 - 1)
            concepts.append(f"{tag}_{suffix}")
    rng.shuffle(concepts)

    distribution = distribution_from_concepts(concepts)
    H = concept_entropy(concepts)
    nH = normalised_entropy(concepts)
    return GenerationResult(concepts, distribution, H, nH)


__all__ = ["GenerationResult", "generate"]
