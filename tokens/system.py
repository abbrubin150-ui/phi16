"""
Hebrew Token System Initialization

This module initializes the complete Hebrew Token System with all 15 tokens,
their relationships, constraints, and control mechanisms.

Usage:
    from tokens.system import HebrewTokenSystem

    system = HebrewTokenSystem()
    system.initialize()

    # Access tokens
    t15 = system.get_token("T15")

    # Check system status
    status = system.get_system_status()
"""

from typing import Dict, Any, Optional
from .registry import TokenRegistry
from .constraints import ConstraintEnforcer
from .hierarchy import HierarchyController
from .moral_triangle import MoralTriangle
from .integrations import (
    RDIAIntegration,
    NANDIntegration,
    AgentWorkflowIntegration,
    PhiOSIntegration
)

# Import all token classes
from .t15_seriousness import SeriousnessToken
from .t05_identity import IdentityToken
from .layer2_absolute import RightsToken, SecurityToken, DataToken
from .layer3_moral import MeasureToken, MonitorToken, LearnToken
from .layer4_governance import GovernToken, StandardizeToken
from .layer5_execution import AutomationToken, ComputeToken, StorageToken
from .layer6_infrastructure import NetworkToken, CommonsToken


class HebrewTokenSystem:
    """
    Complete Hebrew Token System.

    Provides a unified interface for initializing and managing
    all 15 tokens with their relationships and constraints.
    """

    def __init__(self):
        self.registry = TokenRegistry()
        self.constraint_enforcer: Optional[ConstraintEnforcer] = None
        self.hierarchy_controller: Optional[HierarchyController] = None
        self.moral_triangle: Optional[MoralTriangle] = None

        # Φ-OS Integrations
        self.phi_os: Optional[PhiOSIntegration] = None
        self.rdia: Optional[RDIAIntegration] = None
        self.nand: Optional[NANDIntegration] = None
        self.agents: Optional[AgentWorkflowIntegration] = None

        self._initialized = False
        self._phi_os_enabled = False

    def initialize(self) -> None:
        """
        Initialize the complete Hebrew Token System.

        Creates all 15 tokens, establishes relationships, and validates structure.
        """
        if self._initialized:
            raise RuntimeError("System already initialized")

        # Create and register all tokens
        self._create_tokens()

        # Establish relationships and constraints
        self._setup_relationships()

        # Initialize subsystems
        self.constraint_enforcer = ConstraintEnforcer(self.registry)
        self.hierarchy_controller = HierarchyController(self.registry)
        self.moral_triangle = MoralTriangle(self.registry)

        # Validate the system
        self._validate_system()

        self._initialized = True

    def _create_tokens(self) -> None:
        """Create all 15 tokens and register them"""

        # Layer 1: Meta-Control
        self.registry.register_token(SeriousnessToken())

        # Layer 2: Absolute Values
        self.registry.register_token(RightsToken())
        self.registry.register_token(SecurityToken())
        self.registry.register_token(DataToken())

        # Layer 3: Moral Control
        self.registry.register_token(MeasureToken())
        self.registry.register_token(MonitorToken())
        self.registry.register_token(LearnToken())

        # Layer 4: Governance
        self.registry.register_token(GovernToken())
        self.registry.register_token(StandardizeToken())
        self.registry.register_token(IdentityToken())

        # Layer 5: Execution
        self.registry.register_token(AutomationToken())
        self.registry.register_token(ComputeToken())
        self.registry.register_token(StorageToken())

        # Layer 6: Infrastructure
        self.registry.register_token(NetworkToken())
        self.registry.register_token(CommonsToken())

    def _setup_relationships(self) -> None:
        """
        Set up all token relationships and constraints.

        This establishes the dependencies, ethical constraints,
        and control relationships between tokens.
        """
        # These relationships are mostly defined in the token classes themselves,
        # but we can add any additional cross-cutting relationships here

        # T15 controls relationship (already defined in token classes)
        t15 = self.registry.get_token("T15")
        t07 = self.registry.get_token("T07")
        t14 = self.registry.get_token("T14")

        if t07:
            t07.add_controlled_by("T15")
        if t14:
            t14.add_controlled_by("T15")

    def _validate_system(self) -> None:
        """
        Validate the system structure.

        Raises:
            RuntimeError if validation fails
        """
        # Validate dependencies
        dep_errors = self.registry.validate_dependencies()
        if dep_errors:
            raise RuntimeError(f"Dependency validation failed: {dep_errors}")

        # Validate hierarchy
        if self.hierarchy_controller:
            hierarchy_warnings = self.hierarchy_controller.validate_hierarchy()
            if hierarchy_warnings:
                print(f"Hierarchy warnings: {hierarchy_warnings}")

    def get_token(self, token_id: str):
        """Get a specific token by ID"""
        return self.registry.get_token(token_id)

    def get_system_status(self) -> Dict[str, Any]:
        """
        Get comprehensive system status.

        Returns:
            Dictionary with complete system state
        """
        if not self._initialized:
            return {'error': 'System not initialized'}

        status = {
            'initialized': self._initialized,
            'registry': self.registry.get_system_status(),
            'constraints': self.constraint_enforcer.get_constraint_status() if self.constraint_enforcer else {},
            'hierarchy': self.hierarchy_controller.get_hierarchy_map() if self.hierarchy_controller else {},
            'moral_triangle': self.moral_triangle.get_triangle_health() if self.moral_triangle else {}
        }

        return status

    def enforce_all_constraints(self) -> Dict[str, Any]:
        """
        Enforce all constraints and return results.

        Returns:
            Dictionary with enforcement results
        """
        if not self.constraint_enforcer:
            return {'error': 'Constraint enforcer not initialized'}

        violations = self.constraint_enforcer.enforce_constraints()

        return {
            'total_violations': len(violations),
            'violations': [
                {
                    'constraint_id': v.constraint_id,
                    'description': v.description,
                    'violating_token': v.violating_token,
                    'required_token': v.required_token,
                    'severity': v.severity
                }
                for v in violations
            ]
        }

    def trigger_emergency(
        self,
        reason: str,
        triggered_by: str = "SYSTEM"
    ) -> None:
        """
        Trigger emergency seriousness mode (T15).

        Args:
            reason: Why seriousness mode is being activated
            triggered_by: What triggered this (default "SYSTEM")
        """
        t15 = self.registry.get_token("T15")
        if isinstance(t15, SeriousnessToken):
            t15.activate_emergency(reason, triggered_by, self.registry)

    def release_emergency(self, force: bool = False) -> bool:
        """
        Attempt to release emergency mode.

        Args:
            force: Force release even if conditions not met

        Returns:
            True if released, False otherwise
        """
        t15 = self.registry.get_token("T15")
        if isinstance(t15, SeriousnessToken):
            return t15.release(self.registry, force=force)
        return False

    def execute_moral_triangle_cycle(
        self,
        monitored_event: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        Execute a moral triangle feedback cycle.

        Args:
            monitored_event: Event from monitoring

        Returns:
            Cycle results
        """
        if not self.moral_triangle:
            return {'error': 'Moral triangle not initialized'}

        return self.moral_triangle.execute_cycle(monitored_event)

    def get_token_relationships(self, token_id: str) -> Dict[str, Any]:
        """
        Get all relationships for a specific token.

        Args:
            token_id: Token to query

        Returns:
            Dictionary of relationships
        """
        token = self.registry.get_token(token_id)
        if not token:
            return {'error': f'Token {token_id} not found'}

        return {
            'token_id': token_id,
            'name': f"{token.name_en} / {token.name_he}",
            'layer': token.layer.name,
            'priority': token.priority,
            'state': token.state.value,
            'dependencies': list(token.absolute_dependencies),
            'ethical_constraints': token.ethical_constraints,
            'controls': list(token.controls),
            'controlled_by': list(token.controlled_by),
            'phi_os_mappings': list(token.phi_os_mappings)
        }

    def demonstrate_system(self) -> None:
        """
        Demonstrate the system by showing key features.

        Prints a comprehensive overview of the system.
        """
        print("=" * 80)
        print("HEBREW TOKEN SYSTEM - DEMONSTRATION")
        print("=" * 80)
        print()

        # Show hierarchy
        print("HIERARCHICAL STRUCTURE:")
        print("-" * 80)
        if self.hierarchy_controller:
            hierarchy = self.hierarchy_controller.get_hierarchy_map()
            for layer_name, token_ids in hierarchy.items():
                print(f"{layer_name:25} : {', '.join(token_ids)}")
        print()

        # Show constraints
        print("CONSTRAINT STATUS:")
        print("-" * 80)
        if self.constraint_enforcer:
            status = self.constraint_enforcer.get_constraint_status()
            print(f"Total Constraints: {status['total_constraints']}")
            print(f"Active Violations: {status['violations']}")
            for constraint_id, info in status['constraints'].items():
                symbol = "✓" if info['satisfied'] else "✗"
                print(f"  {symbol} {constraint_id}: {info['description']}")
        print()

        # Show moral triangle
        print("MORAL TRIANGLE STATUS:")
        print("-" * 80)
        if self.moral_triangle:
            health = self.moral_triangle.get_triangle_health()
            print(f"T10 (Measure):  {health['t10_status']}")
            print(f"T11 (Monitor):  {health['t11_status']}")
            print(f"T12 (Learn):    {health['t12_status']}")
            print(f"Synergy Active: {health['synergy_active']}")
            print(f"Multiplier:     {health['synergy_multiplier']:.2f}x")
        print()

        print("=" * 80)

    # ========== Φ-OS Integration Methods ==========

    def enable_phi_os_integration(self) -> None:
        """
        Enable Φ-OS integration with R/DIA, NAND-only, and Multi-agent workflow.

        This connects the Hebrew Token System to the complete Φ-OS architecture,
        enabling accountability (R/DIA), verifiability (NAND-only), and
        separation of powers (Multi-agent).
        """
        if not self._initialized:
            raise RuntimeError("System must be initialized before enabling Φ-OS integration")

        if self._phi_os_enabled:
            print("Φ-OS integration already enabled")
            return

        print("Enabling Φ-OS integration...")

        # Initialize integration modules
        self.rdia = RDIAIntegration(self)
        self.nand = NANDIntegration(self)
        self.agents = AgentWorkflowIntegration(self)
        self.phi_os = PhiOSIntegration(self)

        self._phi_os_enabled = True

        print("✓ Φ-OS integration enabled")
        print("  - R/DIA: Memory = Accountability")
        print("  - NAND-only: Verifiable Simplicity")
        print("  - Multi-agent: Proposal ≠ Commitment")
        print()

    def process_phi_os_request(self, request: Dict[str, Any]) -> Dict[str, Any]:
        """
        Process a request through the complete Φ-OS pipeline.

        Args:
            request: Request with action and data

        Returns:
            dict: Processing result with audit trail
        """
        if not self._phi_os_enabled:
            raise RuntimeError("Φ-OS integration not enabled. Call enable_phi_os_integration() first.")

        return self.phi_os.process_request(request)

    def get_phi_os_status(self) -> Dict[str, Any]:
        """
        Get comprehensive Φ-OS integration status.

        Returns:
            dict: System state across all integrations
        """
        if not self._phi_os_enabled:
            return {'error': 'Φ-OS integration not enabled'}

        return self.phi_os.validate_system_state()

    def replay_phi_os_system(self) -> Dict[str, Any]:
        """
        Replay entire Φ-OS system from ledger.

        Returns:
            dict: Full system replay result
        """
        if not self._phi_os_enabled:
            return {'error': 'Φ-OS integration not enabled'}

        return self.phi_os.replay_full_system()

    def phi_os_emergency_hold(self, reason: str) -> bool:
        """
        Trigger emergency HOLD via T15 and Φ-OS.

        Args:
            reason: Reason for emergency

        Returns:
            bool: True if HOLD activated
        """
        if not self._phi_os_enabled:
            raise RuntimeError("Φ-OS integration not enabled")

        return self.phi_os.emergency_hold(reason)

    def phi_os_resume_operations(self) -> bool:
        """
        Resume Φ-OS operations from HOLD/SAFE to RUN.

        Returns:
            bool: True if resumed successfully
        """
        if not self._phi_os_enabled:
            raise RuntimeError("Φ-OS integration not enabled")

        return self.phi_os.resume_operations()

    def get_phi_os_info(self) -> Dict[str, Any]:
        """
        Get comprehensive Φ-OS system information.

        Returns:
            dict: Complete system information
        """
        if not self._phi_os_enabled:
            return {'error': 'Φ-OS integration not enabled'}

        return self.phi_os.get_system_info()
