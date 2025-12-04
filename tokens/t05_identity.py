"""
T05 - Identity (זהות)

Layer 4: Governance & Standards
Priority: 88

Identifies and authenticates actors - creates traceability.
REQUIRED CONDITION: Every action must have identity, otherwise forbidden.

Maps to: Agent IDs (Φ, A1, A2, B1, B2) in Φ-OS

Critical Behaviors:
- Every event in the ledger must have an identity
- No anonymous actions allowed
- Required by T08 (Govern) and T11 (Monitor)
- Enables full traceability and accountability
"""

from typing import Optional, Set, Dict, Any
from datetime import datetime
from .base import Token, TokenLayer, TokenState


class IdentityToken(Token):
    """
    T05 - Identity (Actor Authentication)

    Ensures that every action in the system can be traced to
    an authenticated actor. No anonymous operations allowed.
    """

    def __init__(self):
        super().__init__(
            token_id="T05",
            name_en="Identity",
            name_he="זהות",
            priority=88,
            layer=TokenLayer.GOVERNANCE,
            description="Actor identification and authentication for traceability"
        )

        # Φ-OS mappings
        self.phi_os_mappings.add("Agent IDs")
        self.phi_os_mappings.add("Φ-Architect")
        self.phi_os_mappings.add("A1 Substantive Approver")
        self.phi_os_mappings.add("A2 Procedural Verifier")
        self.phi_os_mappings.add("B1 Actuator")
        self.phi_os_mappings.add("B2 Safety Monitor")

        # T05 is required by these tokens
        # (They should add T05 to their dependencies)

        # Identity-specific state
        self._registered_identities: Set[str] = set()
        self._identity_metadata: Dict[str, Dict[str, Any]] = {}
        self._anonymous_action_attempts: int = 0

    def register_identity(
        self,
        identity_id: str,
        identity_type: str,
        metadata: Optional[Dict[str, Any]] = None
    ) -> None:
        """
        Register an identity in the system.

        Args:
            identity_id: Unique identifier (e.g., "PHI", "A1", "A2", "B1", "B2")
            identity_type: Type of identity (e.g., "architect", "approver", "actuator")
            metadata: Additional metadata about this identity
        """
        if identity_id in self._registered_identities:
            raise ValueError(f"Identity {identity_id} already registered")

        self._registered_identities.add(identity_id)
        self._identity_metadata[identity_id] = {
            'type': identity_type,
            'registered_at': datetime.now(),
            'metadata': metadata or {},
            'action_count': 0,
            'last_action': None
        }

    def is_identity_registered(self, identity_id: str) -> bool:
        """Check if an identity is registered"""
        return identity_id in self._registered_identities

    def validate_action_identity(self, identity_id: Optional[str]) -> tuple[bool, Optional[str]]:
        """
        Validate that an action has a proper identity.

        This is the critical enforcement point: NO ACTION WITHOUT IDENTITY.

        Args:
            identity_id: The claimed identity for an action

        Returns:
            (is_valid, error_message)
        """
        if identity_id is None:
            self._anonymous_action_attempts += 1
            return False, "Action attempted without identity - FORBIDDEN"

        if identity_id not in self._registered_identities:
            return False, f"Unknown identity: {identity_id} - must be registered first"

        # Valid identity
        return True, None

    def record_action(self, identity_id: str) -> None:
        """
        Record that an identity performed an action.

        Updates metrics for traceability.
        """
        if identity_id not in self._registered_identities:
            raise ValueError(f"Cannot record action for unregistered identity: {identity_id}")

        metadata = self._identity_metadata[identity_id]
        metadata['action_count'] += 1
        metadata['last_action'] = datetime.now()

    def get_identity_info(self, identity_id: str) -> Optional[Dict[str, Any]]:
        """Get detailed information about an identity"""
        if identity_id not in self._registered_identities:
            return None

        return self._identity_metadata[identity_id].copy()

    def get_all_identities(self) -> Set[str]:
        """Get all registered identities"""
        return self._registered_identities.copy()

    def revoke_identity(self, identity_id: str, reason: str) -> bool:
        """
        Revoke an identity (use with caution).

        Returns:
            True if revoked, False if identity didn't exist
        """
        if identity_id not in self._registered_identities:
            return False

        self._registered_identities.remove(identity_id)
        metadata = self._identity_metadata.pop(identity_id)
        metadata['revoked_at'] = datetime.now()
        metadata['revocation_reason'] = reason

        return True

    def get_identity_status(self) -> Dict[str, Any]:
        """Get comprehensive identity system status"""
        base_status = self.get_status()
        base_status.update({
            'total_identities': len(self._registered_identities),
            'registered_identities': list(self._registered_identities),
            'anonymous_action_attempts': self._anonymous_action_attempts,
            'identity_details': {
                identity_id: {
                    'type': metadata['type'],
                    'action_count': metadata['action_count'],
                    'last_action': metadata['last_action'].isoformat() if metadata['last_action'] else None
                }
                for identity_id, metadata in self._identity_metadata.items()
            }
        })
        return base_status


def validate_event_identity(event: Dict[str, Any], identity_token: IdentityToken) -> tuple[bool, Optional[str]]:
    """
    Utility function to validate that an event has proper identity.

    This should be called before adding any event to the ledger.

    Args:
        event: Event dictionary that should contain an 'identity' field
        identity_token: The T05 Identity token instance

    Returns:
        (is_valid, error_message)
    """
    identity_id = event.get('identity')
    return identity_token.validate_action_identity(identity_id)
