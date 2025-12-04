"""
Hebrew Token System - Ethical-Logical Governance Framework

This package implements the 15-token Hebrew Token System that provides
an explicit ethical control layer over the Φ-OS technical operations.

Core Principle: "Ethics before technology"
In any conflict between computational efficiency and ethical considerations,
ethical values ALWAYS prevail.

Structure:
- 15 core tokens (T01-T15) organized in 6 hierarchical layers
- Explicit dependencies and constraints
- Emergency control (T15 Seriousness)
- Moral triangle feedback loop (T10 ↔ T11 ↔ T12)
"""

from .base import Token, TokenLayer, TokenState
from .registry import TokenRegistry

__all__ = [
    'Token',
    'TokenLayer',
    'TokenState',
    'TokenRegistry',
]
