"""
Constraints System

Implements and enforces all ethical constraints in the Hebrew Token System.

Critical Constraints:
1. No automation without monitoring (T07 ← T11)
2. No computation without security (T03 ← T06)
3. No governance without rights (T08 ← T13)
4. No unfair standard (T09 ← T10, T13)
5. No anonymous network (T02 ← T05, T06)
6. No storage of violations (T04 ← T13)

Plus absolute dependencies like:
- No learning without storage (T12 ← T04)
- No automation without compute (T07 ← T03)
- No governance without identity (T08 ← T05)
- No monitoring without identity (T11 ← T05)
"""

from typing import Dict, List, Tuple, Optional
from .registry import TokenRegistry


class ConstraintViolation:
    """Represents a constraint violation"""

    def __init__(
        self,
        constraint_id: str,
        description: str,
        violating_token: str,
        required_token: str,
        severity: str = "high"
    ):
        self.constraint_id = constraint_id
        self.description = description
        self.violating_token = violating_token
        self.required_token = required_token
        self.severity = severity

    def __repr__(self):
        return f"Violation({self.constraint_id}: {self.description})"


class ConstraintEnforcer:
    """
    Enforces all constraints in the token system.

    This is the mechanism that makes ethics structurally impossible to bypass.
    """

    def __init__(self, registry: TokenRegistry):
        self.registry = registry
        self._constraints = self._define_constraints()

    def _define_constraints(self) -> Dict[str, Dict]:
        """
        Define all constraints.

        Returns a dictionary mapping constraint_id to constraint definition.
        """
        return {
            'C01_NO_AUTOMATION_WITHOUT_MONITORING': {
                'description': 'No automation without monitoring',
                'source_token': 'T07',
                'required_tokens': ['T11'],
                'type': 'ethical',
                'severity': 'critical'
            },
            'C02_NO_COMPUTE_WITHOUT_SECURITY': {
                'description': 'No computation without security',
                'source_token': 'T03',
                'required_tokens': ['T06'],
                'type': 'ethical',
                'severity': 'critical'
            },
            'C03_NO_GOVERNANCE_WITHOUT_RIGHTS': {
                'description': 'No governance without rights',
                'source_token': 'T08',
                'required_tokens': ['T13'],
                'type': 'ethical',
                'severity': 'critical'
            },
            'C04_NO_UNFAIR_STANDARD': {
                'description': 'No unfair standard',
                'source_token': 'T09',
                'required_tokens': ['T10', 'T13'],
                'type': 'ethical',
                'severity': 'critical'
            },
            'C05_NO_ANONYMOUS_NETWORK': {
                'description': 'No anonymous network',
                'source_token': 'T02',
                'required_tokens': ['T05', 'T06'],
                'type': 'ethical',
                'severity': 'critical'
            },
            'C06_NO_STORAGE_OF_VIOLATIONS': {
                'description': 'No storage of rights violations',
                'source_token': 'T04',
                'required_tokens': ['T13'],
                'type': 'ethical',
                'severity': 'critical'
            },
            'D01_LEARNING_REQUIRES_STORAGE': {
                'description': 'No memory = no learning',
                'source_token': 'T12',
                'required_tokens': ['T04'],
                'type': 'dependency',
                'severity': 'high'
            },
            'D02_AUTOMATION_REQUIRES_COMPUTE': {
                'description': 'No automation without computational power',
                'source_token': 'T07',
                'required_tokens': ['T03'],
                'type': 'dependency',
                'severity': 'high'
            },
            'D03_GOVERNANCE_REQUIRES_IDENTITY': {
                'description': 'No governance without identity',
                'source_token': 'T08',
                'required_tokens': ['T05'],
                'type': 'dependency',
                'severity': 'high'
            },
            'D04_MONITORING_REQUIRES_IDENTITY': {
                'description': 'No responsible monitoring without identity',
                'source_token': 'T11',
                'required_tokens': ['T05'],
                'type': 'dependency',
                'severity': 'high'
            },
        }

    def check_constraint(
        self,
        constraint_id: str
    ) -> Optional[ConstraintViolation]:
        """
        Check a specific constraint.

        Returns:
            ConstraintViolation if violated, None otherwise
        """
        if constraint_id not in self._constraints:
            return None

        constraint = self._constraints[constraint_id]
        source_token = self.registry.get_token(constraint['source_token'])

        if not source_token:
            return None

        # Only check if source token is active
        from .base import TokenState
        if source_token.state != TokenState.ACTIVE:
            return None

        # Check all required tokens
        for required_token_id in constraint['required_tokens']:
            required_token = self.registry.get_token(required_token_id)

            if not required_token:
                return ConstraintViolation(
                    constraint_id=constraint_id,
                    description=f"{constraint['description']}: {required_token_id} not found",
                    violating_token=constraint['source_token'],
                    required_token=required_token_id,
                    severity=constraint['severity']
                )

            if required_token.state != TokenState.ACTIVE:
                return ConstraintViolation(
                    constraint_id=constraint_id,
                    description=f"{constraint['description']}: {required_token_id} is {required_token.state.value}",
                    violating_token=constraint['source_token'],
                    required_token=required_token_id,
                    severity=constraint['severity']
                )

        return None

    def check_all_constraints(self) -> List[ConstraintViolation]:
        """
        Check all constraints in the system.

        Returns:
            List of violations
        """
        violations = []

        for constraint_id in self._constraints:
            violation = self.check_constraint(constraint_id)
            if violation:
                violations.append(violation)

        return violations

    def enforce_constraints(self) -> List[ConstraintViolation]:
        """
        Enforce all constraints by suspending violating tokens.

        This is the active enforcement mechanism.

        Returns:
            List of violations that were enforced
        """
        violations = self.check_all_constraints()

        for violation in violations:
            # Suspend the violating token
            source_token = self.registry.get_token(violation.violating_token)
            if source_token:
                source_token.suspend(
                    reason=violation.description,
                    suspended_by="ConstraintEnforcer"
                )

        return violations

    def get_constraint_status(self) -> Dict:
        """Get status of all constraints"""
        status = {
            'total_constraints': len(self._constraints),
            'violations': 0,
            'constraints': {}
        }

        for constraint_id, constraint in self._constraints.items():
            violation = self.check_constraint(constraint_id)
            is_satisfied = violation is None

            status['constraints'][constraint_id] = {
                'description': constraint['description'],
                'type': constraint['type'],
                'severity': constraint['severity'],
                'satisfied': is_satisfied,
                'violation': str(violation) if violation else None
            }

            if not is_satisfied:
                status['violations'] += 1

        return status
