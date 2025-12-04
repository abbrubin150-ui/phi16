"""
T15 - Seriousness (רצינות)

Layer 1: Meta-Control (Highest Priority)
Priority: 96

Emergency control state activated when rights, data, or system integrity is threatened.
Can halt all other tokens. Maps to Φ-OS HOLD state.

Critical Behaviors:
- Activates IMMEDIATELY (0 steps) when T13 (Rights) is violated
- Suspends T07 (Automation) when active
- Limits T03 (Compute) when active
- Closes discriminatory T14 (Commons) when active
- Cannot be bypassed - even in emergencies
"""

from typing import Optional, List, Dict, Any
from datetime import datetime
from .base import Token, TokenLayer, TokenState


class SeriousnessToken(Token):
    """
    T15 - Seriousness (Emergency Control)

    The highest priority token that can halt the entire system
    when ethical violations or critical threats are detected.
    """

    def __init__(self):
        super().__init__(
            token_id="T15",
            name_en="Seriousness",
            name_he="רצינות",
            priority=96,
            layer=TokenLayer.META_CONTROL,
            description="Emergency control state for critical violations"
        )

        # T15 controls these tokens when activated
        self.add_control_relationship("T07")  # Automation
        self.add_control_relationship("T03")  # Compute
        self.add_control_relationship("T14")  # Commons

        # Φ-OS mapping
        self.phi_os_mappings.add("HOLD State")

        # Seriousness-specific state
        self._active_reason: Optional[str] = None
        self._activation_time: Optional[datetime] = None
        self._triggered_by: Optional[str] = None
        self._suspended_tokens: List[str] = []
        self._activation_history: List[Dict[str, Any]] = []

    def activate_emergency(
        self,
        reason: str,
        triggered_by: str,
        registry: 'TokenRegistry'
    ) -> None:
        """
        Activate emergency seriousness mode.

        This is the critical path that executes when rights violations
        or system integrity threats are detected.

        Args:
            reason: Why seriousness mode is being activated
            triggered_by: Which token or event triggered this (e.g., "T13")
            registry: Token registry for accessing other tokens
        """
        if self.state == TokenState.ACTIVE and self._active_reason:
            # Already in seriousness mode - log additional trigger
            self._activation_history.append({
                'timestamp': datetime.now(),
                'reason': reason,
                'triggered_by': triggered_by,
                'status': 'already_active'
            })
            return

        # Activate seriousness mode
        self.state = TokenState.ACTIVE
        self._active_reason = reason
        self._activation_time = datetime.now()
        self._triggered_by = triggered_by

        # Execute emergency protocol
        self._execute_emergency_protocol(registry)

        # Log activation
        self._activation_history.append({
            'timestamp': self._activation_time,
            'reason': reason,
            'triggered_by': triggered_by,
            'suspended_tokens': self._suspended_tokens.copy(),
            'status': 'activated'
        })

    def _execute_emergency_protocol(self, registry: 'TokenRegistry') -> None:
        """
        Execute the emergency protocol:
        1. Suspend T07 (Automation)
        2. Limit T03 (Compute)
        3. Close discriminatory T14 (Commons)
        """
        self._suspended_tokens = []

        # Suspend Automation
        t07 = registry.get_token("T07")
        if t07 and t07.state == TokenState.ACTIVE:
            t07.suspend("Halted by T15 Seriousness mode", suspended_by="T15")
            self._suspended_tokens.append("T07")

        # Limit Compute
        t03 = registry.get_token("T03")
        if t03 and t03.state == TokenState.ACTIVE:
            t03.degrade("Limited by T15 Seriousness mode")
            self._suspended_tokens.append("T03")

        # Close discriminatory Commons
        t14 = registry.get_token("T14")
        if t14 and t14.state == TokenState.ACTIVE:
            t14.suspend("Closed by T15 Seriousness mode", suspended_by="T15")
            self._suspended_tokens.append("T14")

    def can_release(self, registry: 'TokenRegistry') -> tuple[bool, Optional[str]]:
        """
        Check if seriousness mode can be safely released.

        Returns:
            (can_release, reason_if_not)
        """
        if not self._active_reason:
            return True, None

        # Check that the triggering condition has been resolved
        if self._triggered_by == "T13":
            # Rights violation - must verify T13 is now healthy
            t13 = registry.get_token("T13")
            if not t13:
                return False, "Cannot verify T13 (Rights) status"
            if t13.state != TokenState.ACTIVE:
                return False, "T13 (Rights) is not active - violation not resolved"

            # Check for ongoing violations
            violation = t13.check_violation(registry)
            if violation:
                return False, f"T13 still in violation: {violation}"

        # Check that system is in stable state
        violations = registry.check_all_constraints()
        if violations:
            return False, f"System has {len(violations)} active violations"

        return True, None

    def release(self, registry: 'TokenRegistry', force: bool = False) -> bool:
        """
        Release seriousness mode and restore normal operation.

        Args:
            registry: Token registry
            force: If True, release even if conditions aren't met (use with caution)

        Returns:
            True if released, False if conditions not met
        """
        if not force:
            can_release, reason = self.can_release(registry)
            if not can_release:
                return False

        # Release suspended tokens
        for token_id in self._suspended_tokens:
            token = registry.get_token(token_id)
            if token:
                # Attempt to resume
                token.resume(registry)

        # Log release
        self._activation_history.append({
            'timestamp': datetime.now(),
            'reason': self._active_reason,
            'duration_seconds': (datetime.now() - self._activation_time).total_seconds() if self._activation_time else 0,
            'status': 'released',
            'forced': force
        })

        # Clear state
        self._active_reason = None
        self._activation_time = None
        self._triggered_by = None
        self._suspended_tokens = []

        return True

    def is_active_emergency(self) -> bool:
        """Check if currently in emergency mode"""
        return self._active_reason is not None

    def get_emergency_status(self) -> Dict[str, Any]:
        """Get detailed emergency status"""
        base_status = self.get_status()
        base_status.update({
            'emergency_active': self.is_active_emergency(),
            'active_reason': self._active_reason,
            'activation_time': self._activation_time.isoformat() if self._activation_time else None,
            'triggered_by': self._triggered_by,
            'suspended_tokens': self._suspended_tokens,
            'duration_seconds': (datetime.now() - self._activation_time).total_seconds() if self._activation_time else 0,
            'activation_history': self._activation_history[-10:]  # Last 10 activations
        })
        return base_status
