"""
Layer 6: Infrastructure

Contains foundational infrastructure tokens:
- T02 (Network / רשת) - Priority 90
- T14 (Commons / משאבים משותפים) - Priority 85

These tokens provide the basic infrastructure layer.
"""

from typing import Optional, Dict, Any, List, Set
from datetime import datetime
from .base import Token, TokenLayer, TokenState


class NetworkToken(Token):
    """
    T02 - Network (רשת)

    Defines connectivity and connection between all entities.

    CONSTRAINT: No anonymous network - requires T05 + T06

    Maps to: Communication Layer
    """

    def __init__(self):
        super().__init__(
            token_id="T02",
            name_en="Network",
            name_he="רשת",
            priority=90,
            layer=TokenLayer.INFRASTRUCTURE,
            description="Connectivity between system entities"
        )

        # T02 requires T05 (Identity) and T06 (Security) - "No anonymous network"
        self.add_ethical_constraint("T05", "No anonymous network - requires identity")
        self.add_ethical_constraint("T06", "No anonymous network - requires security")

        # Φ-OS mappings
        self.phi_os_mappings.add("Communication Layer")

        # Network-specific state
        self._connections: Dict[str, Dict[str, Any]] = {}
        self._connection_history: List[Dict[str, Any]] = []

    def establish_connection(
        self,
        connection_id: str,
        from_identity: str,
        to_identity: str,
        connection_type: str,
        is_encrypted: bool = True
    ) -> tuple[bool, Optional[str]]:
        """
        Establish a network connection.

        ENFORCES: No anonymous connections (must have identity and security).

        Args:
            connection_id: Unique connection identifier
            from_identity: Identity of source
            to_identity: Identity of destination
            connection_type: Type of connection
            is_encrypted: Whether connection is encrypted

        Returns:
            (success, error_if_failed)
        """
        # Enforce no anonymous network
        if not from_identity or not to_identity:
            return False, "Cannot establish anonymous connection - identity required (T05)"

        if not is_encrypted:
            return False, "Cannot establish unencrypted connection - security required (T06)"

        connection = {
            'from': from_identity,
            'to': to_identity,
            'type': connection_type,
            'encrypted': is_encrypted,
            'established_at': datetime.now(),
            'status': 'active'
        }

        self._connections[connection_id] = connection
        self._connection_history.append({
            'timestamp': datetime.now(),
            'connection_id': connection_id,
            'action': 'established',
            'connection': connection
        })

        return True, None

    def close_connection(self, connection_id: str) -> bool:
        """Close a network connection"""
        if connection_id not in self._connections:
            return False

        self._connections[connection_id]['status'] = 'closed'
        self._connections[connection_id]['closed_at'] = datetime.now()

        self._connection_history.append({
            'timestamp': datetime.now(),
            'connection_id': connection_id,
            'action': 'closed'
        })

        return True

    def get_active_connections(self) -> List[Dict[str, Any]]:
        """Get all active connections"""
        return [
            {'id': conn_id, **conn}
            for conn_id, conn in self._connections.items()
            if conn['status'] == 'active'
        ]

    def get_connection(self, connection_id: str) -> Optional[Dict[str, Any]]:
        """Get a specific connection"""
        return self._connections.get(connection_id)


class CommonsToken(Token):
    """
    T14 - Commons (משאבים משותפים)

    Shared, public resources available to all.

    Must not discriminate - controlled by T13 and T15.

    Maps to: Open Datasets + Public Tools
    """

    def __init__(self):
        super().__init__(
            token_id="T14",
            name_en="Commons",
            name_he="משאבים משותפים",
            priority=85,
            layer=TokenLayer.INFRASTRUCTURE,
            description="Shared public resources available to all"
        )

        # T14 requires T13 (Rights) - must not discriminate
        self.add_ethical_constraint("T13", "Commons must not discriminate")

        # T14 is controlled by T15 (Seriousness)
        self.add_controlled_by("T15")

        # Φ-OS mappings
        self.phi_os_mappings.add("Open Datasets")
        self.phi_os_mappings.add("Public Tools")

        # Commons-specific state
        self._resources: Dict[str, Dict[str, Any]] = {}
        self._access_log: List[Dict[str, Any]] = []

    def register_resource(
        self,
        resource_id: str,
        resource_type: str,
        description: str,
        access_policy: str = "public",
        restrictions: Optional[Set[str]] = None
    ) -> None:
        """
        Register a commons resource.

        Args:
            resource_id: Unique resource identifier
            resource_type: Type of resource (e.g., "dataset", "tool", "knowledge")
            description: What this resource is
            access_policy: Access policy (default "public")
            restrictions: Any restrictions (should be minimal for true commons)
        """
        if restrictions:
            # Commons should not discriminate - only allow legitimate restrictions
            # (e.g., "requires_attribution", not "exclude_group_X")
            pass

        self._resources[resource_id] = {
            'type': resource_type,
            'description': description,
            'access_policy': access_policy,
            'restrictions': restrictions or set(),
            'registered_at': datetime.now(),
            'access_count': 0
        }

    def access_resource(
        self,
        resource_id: str,
        identity_id: str,
        purpose: str
    ) -> tuple[bool, Optional[str]]:
        """
        Access a commons resource.

        Args:
            resource_id: Which resource to access
            identity_id: Who is accessing it
            purpose: What they'll use it for

        Returns:
            (success, error_if_failed)
        """
        if resource_id not in self._resources:
            return False, f"Resource {resource_id} not found"

        resource = self._resources[resource_id]

        # If suspended by T15, close discriminatory access
        if self.state == TokenState.SUSPENDED:
            return False, "Commons access suspended by T15 (Seriousness)"

        # Record access
        resource['access_count'] += 1
        self._access_log.append({
            'timestamp': datetime.now(),
            'resource_id': resource_id,
            'identity_id': identity_id,
            'purpose': purpose
        })

        return True, None

    def get_resource(self, resource_id: str) -> Optional[Dict[str, Any]]:
        """Get a specific resource"""
        return self._resources.get(resource_id)

    def get_all_resources(self) -> Dict[str, Dict[str, Any]]:
        """Get all commons resources"""
        return self._resources.copy()

    def check_discrimination(self, resource_id: str) -> Optional[str]:
        """
        Check if a resource has discriminatory restrictions.

        Returns:
            Discrimination description if found, None otherwise
        """
        if resource_id not in self._resources:
            return None

        resource = self._resources[resource_id]
        restrictions = resource['restrictions']

        # Check for discriminatory restrictions
        discriminatory_patterns = [
            'exclude_', 'only_', 'restrict_to_'
        ]

        for restriction in restrictions:
            for pattern in discriminatory_patterns:
                if pattern in restriction.lower():
                    return f"Potentially discriminatory restriction: {restriction}"

        return None
