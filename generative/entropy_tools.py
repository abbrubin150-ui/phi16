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
    distribution which callers should interpret as a zero-entropy case
    without delegating to :func:`sim_replay.entropy`.
    """

    if any(v < 0 for v in values):
        raise ValueError("values must be non-negative")
    total = sum(values)
    if total == 0:
        return []
    return [v / total for v in values]


def distribution_from_concepts(concepts: Iterable[str]) -> list[float]:
    """Convert ``concepts`` into a probability distribution.

    Empty inputs result in an empty distribution; callers may short-circuit
    rather than calling :func:`sim_replay.entropy`.
    """

    counts = Counter(concepts)
    return _normalise(list(counts.values()))


def concept_entropy(concepts: Iterable[str]) -> float:
    """Shannon entropy of ``concepts``.

    ``concepts`` may contain repeated labels.  Empty inputs short-circuit to
    ``0.0`` without invoking :func:`sim_replay.entropy`.  Non-empty
    collections are converted into a distribution before delegating to
    :func:`sim_replay.entropy`.
    """

    distribution = distribution_from_concepts(concepts)
    if not distribution:
        return 0.0
    return entropy(distribution)


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
