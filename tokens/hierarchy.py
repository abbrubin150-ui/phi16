"""
Hierarchy System

Implements the 6-layer hierarchical structure where higher layers
always control lower layers.

Layer 1: Meta-Control (T15) - Priority 96
Layer 2: Absolute Values (T13, T06, T01) - Priority 92-95
Layer 3: Moral Control (T10, T11, T12) - Priority 89-93
Layer 4: Governance (T08, T09, T05) - Priority 85-88
Layer 5: Execution (T07, T03, T04) - Priority 85-86
Layer 6: Infrastructure (T02, T14) - Priority 85-90

Rules:
1. Higher layers always control lower layers
2. In conflicts, higher layer always wins
3. No "emergency exceptions" that bypass ethics
"""

from typing import Dict, List, Optional, Tuple
from .base import TokenLayer, Token
from .registry import TokenRegistry


class HierarchyController:
    """
    Manages the hierarchical relationships between tokens.

    Ensures that higher layers maintain control over lower layers.
    """

    def __init__(self, registry: TokenRegistry):
        self.registry = registry

        # Layer ordering (lower number = higher priority)
        self.layer_priority = {
            TokenLayer.META_CONTROL: 1,
            TokenLayer.ABSOLUTE_VALUES: 2,
            TokenLayer.MORAL_CONTROL: 3,
            TokenLayer.GOVERNANCE: 4,
            TokenLayer.EXECUTION: 5,
            TokenLayer.INFRASTRUCTURE: 6
        }

    def can_control(
        self,
        controller_token_id: str,
        target_token_id: str
    ) -> Tuple[bool, Optional[str]]:
        """
        Check if one token can control another based on hierarchy.

        Args:
            controller_token_id: Token attempting to control
            target_token_id: Token being controlled

        Returns:
            (can_control, reason_if_not)
        """
        controller = self.registry.get_token(controller_token_id)
        target = self.registry.get_token(target_token_id)

        if not controller:
            return False, f"Controller token {controller_token_id} not found"
        if not target:
            return False, f"Target token {target_token_id} not found"

        # Check explicit control relationship first
        if target_token_id in controller.controls:
            return True, None

        # Check layer hierarchy
        controller_priority = self.layer_priority[controller.layer]
        target_priority = self.layer_priority[target.layer]

        if controller_priority < target_priority:
            # Controller is in higher layer - can control
            return True, None
        elif controller_priority == target_priority:
            # Same layer - check token priority
            if controller.priority > target.priority:
                return True, None
            else:
                return False, f"Same layer but {target_token_id} has higher priority"
        else:
            return False, f"{controller_token_id} in lower layer than {target_token_id}"

    def resolve_conflict(
        self,
        token_id_a: str,
        token_id_b: str
    ) -> str:
        """
        Resolve a conflict between two tokens.

        Returns the ID of the token that should win based on hierarchy.

        Args:
            token_id_a: First token
            token_id_b: Second token

        Returns:
            ID of winning token
        """
        token_a = self.registry.get_token(token_id_a)
        token_b = self.registry.get_token(token_id_b)

        if not token_a:
            return token_id_b
        if not token_b:
            return token_id_a

        # Compare layers first
        priority_a = self.layer_priority[token_a.layer]
        priority_b = self.layer_priority[token_b.layer]

        if priority_a < priority_b:
            return token_id_a  # A is in higher layer
        elif priority_b < priority_a:
            return token_id_b  # B is in higher layer
        else:
            # Same layer - compare token priorities
            if token_a.priority > token_b.priority:
                return token_id_a
            else:
                return token_id_b

    def get_layer_tokens(self, layer: TokenLayer) -> List[Token]:
        """Get all tokens in a specific layer"""
        return self.registry.get_tokens_by_layer(layer)

    def get_hierarchy_map(self) -> Dict[str, List[str]]:
        """
        Get a map of the hierarchy.

        Returns:
            Dict mapping layer name to list of token IDs
        """
        hierarchy = {}

        for layer in TokenLayer:
            tokens = self.get_layer_tokens(layer)
            hierarchy[layer.name] = [t.token_id for t in tokens]

        return hierarchy

    def validate_hierarchy(self) -> List[str]:
        """
        Validate that the hierarchy is correctly structured.

        Returns:
            List of warnings/errors
        """
        warnings = []

        # Check that T15 is alone in META_CONTROL
        meta_tokens = self.get_layer_tokens(TokenLayer.META_CONTROL)
        if len(meta_tokens) != 1 or meta_tokens[0].token_id != "T15":
            warnings.append("META_CONTROL layer should contain only T15")

        # Check that each layer has the expected tokens
        expected_structure = {
            TokenLayer.META_CONTROL: ["T15"],
            TokenLayer.ABSOLUTE_VALUES: ["T13", "T06", "T01"],
            TokenLayer.MORAL_CONTROL: ["T10", "T11", "T12"],
            TokenLayer.GOVERNANCE: ["T08", "T09", "T05"],
            TokenLayer.EXECUTION: ["T07", "T03", "T04"],
            TokenLayer.INFRASTRUCTURE: ["T02", "T14"]
        }

        for layer, expected_tokens in expected_structure.items():
            actual_tokens = [t.token_id for t in self.get_layer_tokens(layer)]
            for expected in expected_tokens:
                if expected not in actual_tokens:
                    warnings.append(f"Token {expected} missing from {layer.name}")

        return warnings

    def enforce_hierarchy(self) -> None:
        """
        Enforce hierarchical control.

        This ensures that if a higher-layer token suspends a lower-layer token,
        the lower-layer token cannot resume until permitted.
        """
        # Check all tokens to ensure they respect hierarchy
        for token in self.registry.get_all_tokens():
            if token._suspended_by:
                # Check if suspended by higher layer
                suspender = self.registry.get_token(token._suspended_by)
                if suspender:
                    can_control, _ = self.can_control(token._suspended_by, token.token_id)
                    if not can_control:
                        # Suspender doesn't have authority - release
                        token.resume(self.registry)

    def get_dominance_matrix(self) -> Dict[str, Dict[str, bool]]:
        """
        Get a matrix showing which tokens can dominate which others.

        Returns:
            Dict[controller_id][target_id] = can_control
        """
        all_tokens = self.registry.get_all_tokens()
        matrix = {}

        for controller in all_tokens:
            matrix[controller.token_id] = {}
            for target in all_tokens:
                if controller.token_id == target.token_id:
                    matrix[controller.token_id][target.token_id] = False
                else:
                    can_control, _ = self.can_control(controller.token_id, target.token_id)
                    matrix[controller.token_id][target.token_id] = can_control

        return matrix
