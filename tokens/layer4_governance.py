"""
Layer 4: Governance & Standards

Contains tokens for strategic direction and standardization:
- T08 (Govern / ממשל) - Priority 85
- T09 (Standardize / תקינה) - Priority 87
- T05 (Identity / זהות) - Priority 88 [Already implemented separately]

These tokens provide policy, rules, and uniformity.
"""

from typing import Optional, Dict, Any, List
from datetime import datetime
from .base import Token, TokenLayer, TokenState


class GovernToken(Token):
    """
    T08 - Govern (ממשל)

    Strategic direction and policy rules that guide and bind.
    Updates from T12 (learning governance).

    Maps to: A1 Substantive Approver
    """

    def __init__(self):
        super().__init__(
            token_id="T08",
            name_en="Govern",
            name_he="ממשל",
            priority=85,
            layer=TokenLayer.GOVERNANCE,
            description="Strategic direction and policy rules"
        )

        # T08 requires T05 (Identity) - no governance without identity
        self.add_absolute_dependency("T05")

        # T08 requires T13 (Rights) - "No governance without rights"
        self.add_ethical_constraint("T13", "No governance without rights")

        # Φ-OS mappings
        self.phi_os_mappings.add("A1 Substantive Approver")

        # Govern-specific state
        self._policies: Dict[str, Dict[str, Any]] = {}
        self._policy_history: List[Dict[str, Any]] = []

    def define_policy(
        self,
        policy_id: str,
        policy_type: str,
        rules: Dict[str, Any],
        rationale: str,
        source: str = "manual"
    ) -> None:
        """
        Define a governance policy.

        Args:
            policy_id: Unique policy identifier
            policy_type: Type of policy (e.g., "access", "data_usage", "automation")
            rules: The policy rules
            rationale: Why this policy exists
            source: Where this came from (e.g., "manual", "T12_learning")
        """
        policy = {
            'type': policy_type,
            'rules': rules,
            'rationale': rationale,
            'source': source,
            'created_at': datetime.now(),
            'updated_at': datetime.now(),
            'version': 1
        }

        if policy_id in self._policies:
            # Update existing policy
            old_policy = self._policies[policy_id]
            policy['version'] = old_policy['version'] + 1
            self._policy_history.append({
                'policy_id': policy_id,
                'action': 'updated',
                'old_policy': old_policy,
                'new_policy': policy,
                'timestamp': datetime.now()
            })

        self._policies[policy_id] = policy

    def get_policy(self, policy_id: str) -> Optional[Dict[str, Any]]:
        """Get a specific policy"""
        return self._policies.get(policy_id)

    def update_policy_from_learning(
        self,
        policy_id: str,
        updated_rules: Dict[str, Any],
        learning_insight: str
    ) -> None:
        """
        Update a policy based on T12 (Learning) insights.

        This is the "learning governance" mechanism.
        """
        if policy_id not in self._policies:
            raise ValueError(f"Policy {policy_id} does not exist")

        old_policy = self._policies[policy_id].copy()
        self._policies[policy_id]['rules'].update(updated_rules)
        self._policies[policy_id]['updated_at'] = datetime.now()
        self._policies[policy_id]['version'] += 1

        self._policy_history.append({
            'policy_id': policy_id,
            'action': 'learned_update',
            'learning_insight': learning_insight,
            'old_rules': old_policy['rules'],
            'new_rules': self._policies[policy_id]['rules'],
            'timestamp': datetime.now()
        })

    def check_policy_compliance(
        self,
        policy_id: str,
        action: Dict[str, Any]
    ) -> tuple[bool, Optional[str]]:
        """
        Check if an action complies with a policy.

        Returns:
            (is_compliant, violation_reason)
        """
        if policy_id not in self._policies:
            return False, f"Policy {policy_id} not found"

        policy = self._policies[policy_id]
        rules = policy['rules']

        # Simple rule checking (can be extended)
        for rule_key, rule_value in rules.items():
            action_value = action.get(rule_key)
            if action_value != rule_value:
                return False, f"Action violates rule '{rule_key}': expected {rule_value}, got {action_value}"

        return True, None

    def get_all_policies(self) -> Dict[str, Dict[str, Any]]:
        """Get all current policies"""
        return self._policies.copy()


class StandardizeToken(Token):
    """
    T09 - Standardize (תקינה)

    Uniformity enabling common language and system communication.

    Maps to: NAND-only Policy + Formal Verification
    """

    def __init__(self):
        super().__init__(
            token_id="T09",
            name_en="Standardize",
            name_he="תקינה",
            priority=87,
            layer=TokenLayer.GOVERNANCE,
            description="Uniformity and standardization for system coherence"
        )

        # T09 requires T10 (Measure) and T13 (Rights) - "No unfair standard"
        self.add_ethical_constraint("T10", "No unfair standard without measurement")
        self.add_ethical_constraint("T13", "No unfair standard that violates rights")

        # Φ-OS mappings
        self.phi_os_mappings.add("NAND-only Policy")
        self.phi_os_mappings.add("Formal Verification")

        # Standardize-specific state
        self._standards: Dict[str, Dict[str, Any]] = {}
        self._compliance_checks: List[Dict[str, Any]] = []

    def define_standard(
        self,
        standard_id: str,
        standard_type: str,
        specification: Dict[str, Any],
        rationale: str
    ) -> None:
        """
        Define a standard.

        Args:
            standard_id: Unique standard identifier
            standard_type: Type (e.g., "data_format", "protocol", "interface")
            specification: The standard specification
            rationale: Why this standard exists
        """
        self._standards[standard_id] = {
            'type': standard_type,
            'specification': specification,
            'rationale': rationale,
            'created_at': datetime.now(),
            'version': 1
        }

    def check_compliance(
        self,
        standard_id: str,
        implementation: Dict[str, Any]
    ) -> tuple[bool, List[str]]:
        """
        Check if an implementation complies with a standard.

        Returns:
            (is_compliant, list_of_violations)
        """
        if standard_id not in self._standards:
            return False, [f"Standard {standard_id} not found"]

        standard = self._standards[standard_id]
        spec = standard['specification']
        violations = []

        # Check each specification requirement
        for spec_key, spec_value in spec.items():
            impl_value = implementation.get(spec_key)
            if impl_value != spec_value:
                violations.append(f"'{spec_key}': expected {spec_value}, got {impl_value}")

        is_compliant = len(violations) == 0

        # Record check
        self._compliance_checks.append({
            'timestamp': datetime.now(),
            'standard_id': standard_id,
            'is_compliant': is_compliant,
            'violations': violations
        })

        return is_compliant, violations

    def get_standard(self, standard_id: str) -> Optional[Dict[str, Any]]:
        """Get a specific standard"""
        return self._standards.get(standard_id)

    def get_all_standards(self) -> Dict[str, Dict[str, Any]]:
        """Get all standards"""
        return self._standards.copy()
