"""Utilities for evaluating concept distributions.

This module wraps the :func:`sim_replay.entropy` function and provides
helpers to normalise entropy scores across varying sample sizes.

The tools are intentionally lightweight – they operate on in-memory
collections of concept labels and are designed for use in prototype
content generators.
"""
from __future__ import annotations

from collections import Counter
from math import log2
from typing import Iterable, Sequence

from sim_replay import entropy


def _normalise(values: Sequence[float]) -> list[float]:
    """Return ``values`` scaled to sum to ``1.0``.

    Any negative entries raise ``ValueError``.  Zero totals yield an empty
    distribution which results in an entropy of ``0.0``.
    """

    if any(v < 0 for v in values):
        raise ValueError("values must be non-negative")
    total = sum(values)
    if total == 0:
        return []
    return [v / total for v in values]


def distribution_from_concepts(concepts: Iterable[str]) -> list[float]:
    """Convert ``concepts`` into a probability distribution."""

    counts = Counter(concepts)
    return _normalise(list(counts.values()))


def concept_entropy(concepts: Iterable[str]) -> float:
    """Shannon entropy of ``concepts``.

    ``concepts`` may contain repeated labels.  The function converts the
    sequence into a distribution and delegates the actual calculation to
    :func:`sim_replay.entropy`.
    """

    return entropy(distribution_from_concepts(concepts))


def normalised_entropy(concepts: Iterable[str]) -> float:
    """Entropy normalised to the theoretical maximum for ``concepts``.

    The score is scaled by ``log2(n)`` where ``n`` is the number of distinct
    concepts, making scores comparable across sample sizes.
    """

    p = distribution_from_concepts(concepts)
    distinct = len(p)
    if distinct <= 1:
        return 0.0
    H = entropy(p)
    return H / log2(distinct)


__all__ = [
    "distribution_from_concepts",
    "concept_entropy",
    "normalised_entropy",
]
