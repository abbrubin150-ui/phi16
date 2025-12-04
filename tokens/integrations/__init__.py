"""
Φ-OS Integration Modules for Hebrew Token System

This package provides integration between the Hebrew Token System
and the core Φ-OS architecture components:

- R/DIA (Reflexive/Dialectic Intelligence Architecture)
- NAND-only operations
- Multi-agent workflow

Each integration module maps tokens to their corresponding
architectural components while maintaining the ethical hierarchy.
"""

from .rdia_integration import RDIAIntegration
from .nand_integration import NANDIntegration
from .agent_integration import AgentWorkflowIntegration
from .phi_os_integration import PhiOSIntegration

__all__ = [
    'RDIAIntegration',
    'NANDIntegration',
    'AgentWorkflowIntegration',
    'PhiOSIntegration',
]
