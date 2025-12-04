"""
Token Registry

Global registry for managing all tokens in the Hebrew Token System.
Provides:
- Token registration and lookup
- Dependency validation
- Constraint enforcement
- Hierarchy management
- Violation detection and handling
"""

from typing import Dict, List, Optional, Set, Tuple
from .base import Token, TokenLayer, TokenState


class TokenRegistry:
    """
    Central registry for all tokens in the system.

    Maintains the complete token graph with dependencies, constraints,
    and hierarchical relationships. Enforces ethical rules and provides
    global system state management.
    """

    def __init__(self):
        self._tokens: Dict[str, Token] = {}
        self._layer_map: Dict[TokenLayer, Set[str]] = {
            layer: set() for layer in TokenLayer
        }
        self._violation_history: List[Dict] = []

    def register_token(self, token: Token) -> None:
        """Register a token in the system"""
        if token.token_id in self._tokens:
            raise ValueError(f"Token {token.token_id} already registered")

        self._tokens[token.token_id] = token
        self._layer_map[token.layer].add(token.token_id)

    def get_token(self, token_id: str) -> Optional[Token]:
        """Get a token by ID"""
        return self._tokens.get(token_id)

    def get_tokens_by_layer(self, layer: TokenLayer) -> List[Token]:
        """Get all tokens in a specific layer"""
        return [self._tokens[tid] for tid in self._layer_map[layer]]

    def get_all_tokens(self) -> List[Token]:
        """Get all registered tokens"""
        return list(self._tokens.values())

    def validate_dependencies(self) -> List[str]:
        """
        Validate that all declared dependencies exist.

        Returns:
            List of error messages (empty if valid)
        """
        errors = []
        for token in self._tokens.values():
            # Check absolute dependencies
            for dep_id in token.absolute_dependencies:
                if dep_id not in self._tokens:
                    errors.append(f"{token.token_id} depends on non-existent token {dep_id}")

            # Check ethical constraints
            for constraint_id in token.ethical_constraints.keys():
                if constraint_id not in self._tokens:
                    errors.append(f"{token.token_id} has constraint on non-existent token {constraint_id}")

            # Check control relationships
            for controlled_id in token.controls:
                if controlled_id not in self._tokens:
                    errors.append(f"{token.token_id} claims to control non-existent token {controlled_id}")

        return errors

    def check_all_constraints(self) -> List[Tuple[str, str]]:
        """
        Check all active tokens for constraint violations.

        Returns:
            List of (token_id, violation_description) tuples
        """
        violations = []
        for token in self._tokens.values():
            if token.state == TokenState.ACTIVE:
                violation = token.check_violation(self)
                if violation:
                    violations.append((token.token_id, violation))
                    token.record_violation(violation)

        # Record in history
        if violations:
            from datetime import datetime
            self._violation_history.append({
                'timestamp': datetime.now(),
                'violations': violations
            })

        return violations

    def enforce_constraints(self) -> None:
        """
        Enforce all constraints by suspending violating tokens.

        This is the enforcement mechanism that automatically suspends
        tokens that violate their constraints.
        """
        violations = self.check_all_constraints()
        for token_id, violation in violations:
            token = self._tokens[token_id]
            if token.state == TokenState.ACTIVE:
                token.suspend(f"Constraint violation: {violation}", suspended_by="SYSTEM")

    def get_token_by_priority(self, descending: bool = True) -> List[Token]:
        """Get tokens sorted by priority"""
        return sorted(
            self._tokens.values(),
            key=lambda t: t.priority,
            reverse=descending
        )

    def get_dependency_chain(self, token_id: str, visited: Optional[Set[str]] = None) -> List[str]:
        """
        Get the full dependency chain for a token (recursive).

        Returns:
            List of token IDs in dependency order
        """
        if visited is None:
            visited = set()

        if token_id in visited:
            return []  # Circular dependency or already processed

        token = self._tokens.get(token_id)
        if not token:
            return []

        visited.add(token_id)
        chain = [token_id]

        for dep_id in token.absolute_dependencies:
            chain.extend(self.get_dependency_chain(dep_id, visited))

        return chain

    def can_token_control(self, controller_id: str, target_id: str) -> bool:
        """
        Check if one token can control another based on hierarchy.

        Rules:
        1. Higher layers always control lower layers
        2. Explicit control relationships override layer rules
        3. Same layer = no control unless explicit
        """
        controller = self._tokens.get(controller_id)
        target = self._tokens.get(target_id)

        if not controller or not target:
            return False

        # Explicit control relationship
        if target_id in controller.controls:
            return True

        # Layer hierarchy (lower number = higher priority)
        if controller.layer.value < target.layer.value:
            return True

        return False

    def get_system_status(self) -> Dict:
        """Get comprehensive system status across all tokens"""
        layer_status = {}
        for layer in TokenLayer:
            tokens = self.get_tokens_by_layer(layer)
            layer_status[layer.name] = {
                'total': len(tokens),
                'active': sum(1 for t in tokens if t.state == TokenState.ACTIVE),
                'suspended': sum(1 for t in tokens if t.state == TokenState.SUSPENDED),
                'halted': sum(1 for t in tokens if t.state == TokenState.HALTED),
                'degraded': sum(1 for t in tokens if t.state == TokenState.DEGRADED),
            }

        return {
            'total_tokens': len(self._tokens),
            'layers': layer_status,
            'recent_violations': len(self._violation_history),
            'tokens': {tid: token.get_status() for tid, token in self._tokens.items()}
        }

    def reset_all_tokens(self) -> None:
        """Reset all tokens to initial state (use with caution)"""
        for token in self._tokens.values():
            token.state = TokenState.ACTIVE
            token._suspended_by = None
            token._suspension_reason = None

    def get_violation_history(self, limit: Optional[int] = None) -> List[Dict]:
        """Get violation history (most recent first)"""
        history = self._violation_history[::-1]
        if limit:
            return history[:limit]
        return history
