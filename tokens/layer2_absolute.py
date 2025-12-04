"""
Layer 2: Absolute Values (Non-Negotiable)

Contains three tokens that represent the foundational, unbreakable values:
- T13 (Rights / זכויות אדם) - Priority 94
- T06 (Security / אבטחה) - Priority 92
- T01 (Data / נתונים) - Priority 95

These tokens cannot be violated under any circumstances.
Any violation triggers T15 (Seriousness) immediately.
"""

from typing import Optional, Dict, Any, List, Set
from datetime import datetime
from .base import Token, TokenLayer, TokenState


class RightsToken(Token):
    """
    T13 - Rights (זכויות אדם)

    Human rights as supreme, unbreakable value.
    Any violation triggers T15 immediately.

    Maps to: VSD (Value Sensitive Design) / FAT (Fairness, Accountability, Transparency)
    """

    def __init__(self):
        super().__init__(
            token_id="T13",
            name_en="Rights",
            name_he="זכויות אדם",
            priority=94,
            layer=TokenLayer.ABSOLUTE_VALUES,
            description="Human rights as supreme, unbreakable value"
        )

        # Φ-OS mappings
        self.phi_os_mappings.add("VSD Principles")
        self.phi_os_mappings.add("FAT Ethics")

        # Rights-specific state
        self._rights_violations: List[Dict[str, Any]] = []
        self._protected_rights: Set[str] = {
            "privacy",
            "data_ownership",
            "informed_consent",
            "non_discrimination",
            "transparency",
            "right_to_explanation",
            "right_to_rectification",
            "right_to_erasure"
        }

    def check_rights_violation(
        self,
        action: str,
        context: Dict[str, Any]
    ) -> Optional[str]:
        """
        Check if an action violates human rights.

        Args:
            action: Description of the action being performed
            context: Context about the action (who, what, when, why)

        Returns:
            Violation description if violated, None otherwise
        """
        # Check for explicit violations
        if context.get('discriminates'):
            return f"Action '{action}' discriminates - violates non_discrimination right"

        if context.get('lacks_consent'):
            return f"Action '{action}' lacks informed consent"

        if context.get('violates_privacy'):
            return f"Action '{action}' violates privacy rights"

        if context.get('unauthorized_data_use'):
            return f"Action '{action}' uses data without authorization"

        return None

    def record_violation(
        self,
        violation_description: str,
        action: str,
        context: Dict[str, Any]
    ) -> None:
        """
        Record a rights violation.

        This should trigger T15 (Seriousness) immediately.
        """
        violation_record = {
            'timestamp': datetime.now(),
            'description': violation_description,
            'action': action,
            'context': context,
            'severity': 'CRITICAL'
        }
        self._rights_violations.append(violation_record)
        super().record_violation(violation_description)

    def get_violations(self, limit: Optional[int] = None) -> List[Dict[str, Any]]:
        """Get rights violations (most recent first)"""
        violations = self._rights_violations[::-1]
        if limit:
            return violations[:limit]
        return violations

    def get_protected_rights(self) -> Set[str]:
        """Get the set of protected rights"""
        return self._protected_rights.copy()


class SecurityToken(Token):
    """
    T06 - Security (אבטחה)

    Comprehensive protection preventing damage to data, identities, rights.

    Maps to: B2 Safety Monitor + Cryptographic Chain
    """

    def __init__(self):
        super().__init__(
            token_id="T06",
            name_en="Security",
            name_he="אבטחה",
            priority=92,
            layer=TokenLayer.ABSOLUTE_VALUES,
            description="Comprehensive protection for data, identities, and rights"
        )

        # Φ-OS mappings
        self.phi_os_mappings.add("B2 Safety Monitor")
        self.phi_os_mappings.add("Cryptographic Chain")

        # Security-specific state
        self._security_incidents: List[Dict[str, Any]] = []
        self._threat_level: str = "NORMAL"  # NORMAL, ELEVATED, HIGH, CRITICAL
        self._security_policies: Dict[str, bool] = {
            "encryption_required": True,
            "authentication_required": True,
            "audit_logging_required": True,
            "data_integrity_checks": True,
            "access_control_enforcement": True
        }

    def check_security_threat(
        self,
        action: str,
        context: Dict[str, Any]
    ) -> Optional[str]:
        """
        Check if an action poses a security threat.

        Args:
            action: Description of the action
            context: Security context

        Returns:
            Threat description if detected, None otherwise
        """
        if context.get('unencrypted_data') and self._security_policies['encryption_required']:
            return f"Action '{action}' transmits unencrypted data"

        if context.get('unauthenticated') and self._security_policies['authentication_required']:
            return f"Action '{action}' lacks authentication"

        if context.get('integrity_compromised'):
            return f"Action '{action}' has compromised data integrity"

        if context.get('unauthorized_access'):
            return f"Action '{action}' attempts unauthorized access"

        return None

    def record_incident(
        self,
        incident_description: str,
        severity: str,
        action: str,
        context: Dict[str, Any]
    ) -> None:
        """Record a security incident"""
        incident_record = {
            'timestamp': datetime.now(),
            'description': incident_description,
            'severity': severity,
            'action': action,
            'context': context
        }
        self._security_incidents.append(incident_record)
        super().record_violation(incident_description)

        # Escalate threat level if needed
        if severity == "CRITICAL":
            self._threat_level = "CRITICAL"

    def get_threat_level(self) -> str:
        """Get current system threat level"""
        return self._threat_level

    def set_threat_level(self, level: str) -> None:
        """Set system threat level"""
        valid_levels = ["NORMAL", "ELEVATED", "HIGH", "CRITICAL"]
        if level not in valid_levels:
            raise ValueError(f"Invalid threat level: {level}")
        self._threat_level = level


class DataToken(Token):
    """
    T01 - Data (נתונים)

    The foundational basis for all decisions.
    "The token exclusively determines who sees what, when, and under what conditions"

    Maps to: Append-Only Log (L)
    """

    def __init__(self):
        super().__init__(
            token_id="T01",
            name_en="Data",
            name_he="נתונים",
            priority=95,
            layer=TokenLayer.ABSOLUTE_VALUES,
            description="Foundational data that drives all decisions"
        )

        # Φ-OS mappings
        self.phi_os_mappings.add("Append-Only Log (L)")
        self.phi_os_mappings.add("DIA Monotonicity")

        # Data-specific state
        self._access_policies: Dict[str, Dict[str, Any]] = {}
        self._data_lineage: List[Dict[str, Any]] = []

    def define_access_policy(
        self,
        data_id: str,
        who: List[str],
        when: Optional[str] = None,
        conditions: Optional[Dict[str, Any]] = None
    ) -> None:
        """
        Define who can access what data, when, and under what conditions.

        This is the exclusive mechanism for data access control.

        Args:
            data_id: Identifier for the data
            who: List of identity IDs that can access this data
            when: Time-based conditions (e.g., "business_hours", "always")
            conditions: Additional conditions for access
        """
        self._access_policies[data_id] = {
            'who': who,
            'when': when or "always",
            'conditions': conditions or {},
            'defined_at': datetime.now()
        }

    def can_access(
        self,
        data_id: str,
        identity_id: str,
        context: Optional[Dict[str, Any]] = None
    ) -> tuple[bool, Optional[str]]:
        """
        Check if an identity can access specific data.

        Args:
            data_id: The data being accessed
            identity_id: Who is trying to access it
            context: Additional context for conditional checks

        Returns:
            (can_access, reason_if_not)
        """
        if data_id not in self._access_policies:
            return False, f"No access policy defined for data: {data_id}"

        policy = self._access_policies[data_id]

        # Check who
        if identity_id not in policy['who']:
            return False, f"Identity {identity_id} not authorized for data {data_id}"

        # Check when
        # (In a real implementation, this would check time-based conditions)
        if policy['when'] != "always":
            # Simplified - would need actual time checking
            pass

        # Check conditions
        if policy['conditions']:
            context = context or {}
            for condition_key, condition_value in policy['conditions'].items():
                if context.get(condition_key) != condition_value:
                    return False, f"Condition not met: {condition_key}"

        return True, None

    def record_access(
        self,
        data_id: str,
        identity_id: str,
        action: str,
        result: str
    ) -> None:
        """Record data access for lineage tracking"""
        self._data_lineage.append({
            'timestamp': datetime.now(),
            'data_id': data_id,
            'identity_id': identity_id,
            'action': action,
            'result': result
        })

    def get_data_lineage(
        self,
        data_id: Optional[str] = None,
        limit: Optional[int] = None
    ) -> List[Dict[str, Any]]:
        """Get data access lineage"""
        if data_id:
            lineage = [l for l in self._data_lineage if l['data_id'] == data_id]
        else:
            lineage = self._data_lineage

        lineage = lineage[::-1]  # Most recent first
        if limit:
            return lineage[:limit]
        return lineage
