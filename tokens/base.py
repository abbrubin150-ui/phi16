"""
Base Token Class

Defines the foundational structure for all tokens in the Hebrew Token System.
Each token has:
- A unique ID (T01-T15)
- A name in English and Hebrew
- A priority weight (85-96)
- A hierarchical layer (1-6)
- Dependencies on other tokens
- State management
"""

from enum import Enum
from typing import Set, Optional, Dict, Any
from dataclasses import dataclass, field
from datetime import datetime


class TokenLayer(Enum):
    """6 hierarchical layers - higher numbers = higher priority"""
    INFRASTRUCTURE = 6      # T02, T14
    EXECUTION = 5           # T07, T03, T04
    GOVERNANCE = 4          # T08, T09, T05
    MORAL_CONTROL = 3       # T10, T11, T12
    ABSOLUTE_VALUES = 2     # T13, T06, T01
    META_CONTROL = 1        # T15


class TokenState(Enum):
    """Operational states for tokens"""
    ACTIVE = "active"
    SUSPENDED = "suspended"
    HALTED = "halted"
    DEGRADED = "degraded"


@dataclass
class TokenMetrics:
    """Performance and operational metrics for a token"""
    activations: int = 0
    violations: int = 0
    last_activation: Optional[datetime] = None
    last_violation: Optional[datetime] = None
    total_uptime_seconds: float = 0.0
    dependency_check_failures: int = 0


class Token:
    """
    Base class for all tokens in the Hebrew Token System.

    Each token represents an ethical or operational principle with:
    - Hierarchical priority
    - Dependencies on other tokens
    - State management
    - Integration hooks with Φ-OS
    """

    def __init__(
        self,
        token_id: str,
        name_en: str,
        name_he: str,
        priority: int,
        layer: TokenLayer,
        description: str = "",
    ):
        self.token_id = token_id
        self.name_en = name_en
        self.name_he = name_he
        self.priority = priority
        self.layer = layer
        self.description = description

        # Dependencies
        self.absolute_dependencies: Set[str] = set()  # Cannot function without these
        self.ethical_constraints: Dict[str, str] = {}  # Unbreakable rules with reasons
        self.controlled_by: Set[str] = set()  # Tokens that can control this one
        self.controls: Set[str] = set()  # Tokens this one can control

        # State
        self.state = TokenState.ACTIVE
        self.metrics = TokenMetrics()
        self.phi_os_mappings: Set[str] = set()  # Which Φ-OS components this maps to

        # Control flags
        self._suspended_by: Optional[str] = None  # Which token suspended this
        self._suspension_reason: Optional[str] = None

    def __repr__(self) -> str:
        return f"{self.token_id}({self.name_en}/{self.name_he}, P{self.priority}, {self.layer.name})"

    def add_absolute_dependency(self, token_id: str) -> None:
        """Add a token that this token absolutely requires to function"""
        self.absolute_dependencies.add(token_id)

    def add_ethical_constraint(self, token_id: str, reason: str) -> None:
        """Add an ethical constraint - an unbreakable rule involving another token"""
        self.ethical_constraints[token_id] = reason

    def add_control_relationship(self, controlled_token_id: str) -> None:
        """Declare that this token can control another token"""
        self.controls.add(controlled_token_id)

    def add_controlled_by(self, controller_token_id: str) -> None:
        """Declare that this token can be controlled by another token"""
        self.controlled_by.add(controller_token_id)

    def can_activate(self, registry: 'TokenRegistry') -> tuple[bool, Optional[str]]:
        """
        Check if this token can be activated based on dependencies.

        Returns:
            (can_activate, reason_if_not)
        """
        # Check absolute dependencies
        for dep_id in self.absolute_dependencies:
            dep_token = registry.get_token(dep_id)
            if dep_token is None:
                return False, f"Missing dependency: {dep_id}"
            if dep_token.state not in [TokenState.ACTIVE, TokenState.DEGRADED]:
                return False, f"Dependency {dep_id} is not active (state: {dep_token.state})"

        # Check ethical constraints
        for constraint_token_id, reason in self.ethical_constraints.items():
            constraint_token = registry.get_token(constraint_token_id)
            if constraint_token and constraint_token.state != TokenState.ACTIVE:
                return False, f"Ethical constraint violated: {reason}"

        return True, None

    def activate(self, registry: 'TokenRegistry') -> bool:
        """
        Attempt to activate this token.

        Returns:
            True if successfully activated, False otherwise
        """
        can_activate, reason = self.can_activate(registry)
        if not can_activate:
            self.metrics.dependency_check_failures += 1
            return False

        self.state = TokenState.ACTIVE
        self.metrics.activations += 1
        self.metrics.last_activation = datetime.now()
        return True

    def suspend(self, reason: str, suspended_by: Optional[str] = None) -> None:
        """Suspend this token's operation"""
        self.state = TokenState.SUSPENDED
        self._suspended_by = suspended_by
        self._suspension_reason = reason

    def halt(self, reason: str) -> None:
        """Completely halt this token (stronger than suspend)"""
        self.state = TokenState.HALTED
        self._suspension_reason = reason

    def degrade(self, reason: str) -> None:
        """Put token in degraded mode - still functioning but limited"""
        self.state = TokenState.DEGRADED
        self._suspension_reason = reason

    def resume(self, registry: 'TokenRegistry') -> bool:
        """
        Attempt to resume operation from suspended/halted state.

        Returns:
            True if successfully resumed, False otherwise
        """
        can_resume, reason = self.can_activate(registry)
        if not can_resume:
            return False

        self.state = TokenState.ACTIVE
        self._suspended_by = None
        self._suspension_reason = None
        return True

    def check_violation(self, registry: 'TokenRegistry') -> Optional[str]:
        """
        Check if this token is currently in violation of any constraints.

        Returns:
            Violation description if violated, None otherwise
        """
        if self.state != TokenState.ACTIVE:
            return None

        # Check dependencies
        for dep_id in self.absolute_dependencies:
            dep_token = registry.get_token(dep_id)
            if dep_token and dep_token.state != TokenState.ACTIVE:
                return f"{self.token_id} requires {dep_id} but {dep_id} is {dep_token.state.value}"

        # Check ethical constraints
        for constraint_token_id, reason in self.ethical_constraints.items():
            constraint_token = registry.get_token(constraint_token_id)
            if constraint_token and constraint_token.state != TokenState.ACTIVE:
                return f"{self.token_id} violates: {reason}"

        return None

    def record_violation(self, violation_description: str) -> None:
        """Record a violation for metrics tracking"""
        self.metrics.violations += 1
        self.metrics.last_violation = datetime.now()

    def get_status(self) -> Dict[str, Any]:
        """Get comprehensive status of this token"""
        return {
            'token_id': self.token_id,
            'name': f"{self.name_en} / {self.name_he}",
            'priority': self.priority,
            'layer': self.layer.name,
            'state': self.state.value,
            'suspended_by': self._suspended_by,
            'suspension_reason': self._suspension_reason,
            'dependencies': list(self.absolute_dependencies),
            'ethical_constraints': self.ethical_constraints,
            'controls': list(self.controls),
            'controlled_by': list(self.controlled_by),
            'metrics': {
                'activations': self.metrics.activations,
                'violations': self.metrics.violations,
                'last_activation': self.metrics.last_activation.isoformat() if self.metrics.last_activation else None,
                'last_violation': self.metrics.last_violation.isoformat() if self.metrics.last_violation else None,
            }
        }
