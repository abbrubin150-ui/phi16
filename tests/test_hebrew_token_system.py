"""
Comprehensive Tests for Hebrew Token System

Tests all major components:
- Token relationships and dependencies
- Ethical constraints
- Moral triangle feedback loop
- Emergency seriousness mode
- Hierarchy enforcement
"""

import sys
sys.path.insert(0, '/home/user/phi16')

import pytest
from tokens.system import HebrewTokenSystem
from tokens.base import TokenState
from tokens.t15_seriousness import SeriousnessToken
from tokens.t05_identity import IdentityToken
from tokens.layer2_absolute import RightsToken
from tokens.layer3_moral import MonitorToken, MeasureToken, LearnToken
from tokens.layer5_execution import AutomationToken


class TestSystemInitialization:
    """Test system initialization and structure"""

    def test_system_initializes(self):
        """Test that the system initializes successfully"""
        system = HebrewTokenSystem()
        system.initialize()

        assert system._initialized
        assert system.registry is not None
        assert system.constraint_enforcer is not None
        assert system.hierarchy_controller is not None
        assert system.moral_triangle is not None

    def test_all_15_tokens_created(self):
        """Test that all 15 tokens are created"""
        system = HebrewTokenSystem()
        system.initialize()

        expected_tokens = [
            "T01", "T02", "T03", "T04", "T05", "T06", "T07", "T08",
            "T09", "T10", "T11", "T12", "T13", "T14", "T15"
        ]

        for token_id in expected_tokens:
            token = system.get_token(token_id)
            assert token is not None, f"Token {token_id} not found"

    def test_all_tokens_active_initially(self):
        """Test that all tokens start in ACTIVE state"""
        system = HebrewTokenSystem()
        system.initialize()

        for token in system.registry.get_all_tokens():
            assert token.state == TokenState.ACTIVE


class TestConstraints:
    """Test ethical constraints enforcement"""

    def test_no_automation_without_monitoring(self):
        """Test C01: No automation without monitoring (T07 ← T11)"""
        system = HebrewTokenSystem()
        system.initialize()

        t07 = system.get_token("T07")
        t11 = system.get_token("T11")

        # Suspend T11 (Monitor)
        t11.suspend("Testing constraint", suspended_by="TEST")

        # Check constraint
        violations = system.constraint_enforcer.check_all_constraints()
        automation_violations = [
            v for v in violations
            if v.constraint_id == "C01_NO_AUTOMATION_WITHOUT_MONITORING"
        ]

        assert len(automation_violations) > 0, "Should detect automation without monitoring"

    def test_no_compute_without_security(self):
        """Test C02: No computation without security (T03 ← T06)"""
        system = HebrewTokenSystem()
        system.initialize()

        t03 = system.get_token("T03")
        t06 = system.get_token("T06")

        # Suspend T06 (Security)
        t06.suspend("Testing constraint", suspended_by="TEST")

        # Check constraint
        violations = system.constraint_enforcer.check_all_constraints()
        compute_violations = [
            v for v in violations
            if v.constraint_id == "C02_NO_COMPUTE_WITHOUT_SECURITY"
        ]

        assert len(compute_violations) > 0, "Should detect compute without security"

    def test_no_anonymous_network(self):
        """Test C05: No anonymous network (T02 ← T05, T06)"""
        system = HebrewTokenSystem()
        system.initialize()

        t02 = system.get_token("T02")
        t05 = system.get_token("T05")

        # Suspend T05 (Identity)
        t05.suspend("Testing constraint", suspended_by="TEST")

        # Check constraint
        violations = system.constraint_enforcer.check_all_constraints()
        network_violations = [
            v for v in violations
            if v.constraint_id == "C05_NO_ANONYMOUS_NETWORK"
        ]

        assert len(network_violations) > 0, "Should detect anonymous network attempt"

    def test_constraint_enforcement(self):
        """Test that constraints are automatically enforced"""
        system = HebrewTokenSystem()
        system.initialize()

        t11 = system.get_token("T11")
        t07 = system.get_token("T07")

        # Suspend monitoring
        t11.suspend("Testing enforcement", suspended_by="TEST")

        # Enforce constraints
        violations = system.constraint_enforcer.enforce_constraints()

        # T07 should now be suspended
        assert t07.state == TokenState.SUSPENDED, "T07 should be suspended when T11 is inactive"


class TestEmergencyMode:
    """Test T15 Seriousness emergency mode"""

    def test_emergency_activation(self):
        """Test that emergency mode can be activated"""
        system = HebrewTokenSystem()
        system.initialize()

        t15 = system.get_token("T15")

        system.trigger_emergency("Test emergency", triggered_by="TEST")

        assert isinstance(t15, SeriousnessToken)
        assert t15.is_active_emergency()

    def test_emergency_suspends_automation(self):
        """Test that T15 suspends T07 (Automation)"""
        system = HebrewTokenSystem()
        system.initialize()

        t07 = system.get_token("T07")

        # Trigger emergency
        system.trigger_emergency("Test emergency", triggered_by="TEST")

        # T07 should be suspended
        assert t07.state == TokenState.SUSPENDED

    def test_emergency_limits_compute(self):
        """Test that T15 degrades T03 (Compute)"""
        system = HebrewTokenSystem()
        system.initialize()

        t03 = system.get_token("T03")

        # Trigger emergency
        system.trigger_emergency("Test emergency", triggered_by="TEST")

        # T03 should be degraded
        assert t03.state == TokenState.DEGRADED

    def test_emergency_release(self):
        """Test that emergency can be released when safe"""
        system = HebrewTokenSystem()
        system.initialize()

        t15 = system.get_token("T15")
        t07 = system.get_token("T07")

        # Trigger and release
        system.trigger_emergency("Test emergency", triggered_by="TEST")
        released = system.release_emergency(force=True)

        assert released
        assert not isinstance(t15, SeriousnessToken) or not t15.is_active_emergency()


class TestMoralTriangle:
    """Test T10 ↔ T11 ↔ T12 feedback loop"""

    def test_moral_triangle_cycle(self):
        """Test that a complete moral triangle cycle executes"""
        system = HebrewTokenSystem()
        system.initialize()

        monitored_event = {
            'state_name': 'test_metric',
            'value': 100,
            'expected_range': (0, 50)  # Anomaly: value outside range
        }

        result = system.execute_moral_triangle_cycle(monitored_event)

        assert 'cycle_id' in result
        assert 'steps' in result
        assert len(result['steps']) > 0

    def test_synergy_multiplier(self):
        """Test synergy multiplier calculation"""
        system = HebrewTokenSystem()
        system.initialize()

        # Initially all active, but need to activate them
        t10 = system.get_token("T10")
        t11 = system.get_token("T11")
        t12 = system.get_token("T12")

        # Activate all to establish baseline
        t10.activate(system.registry)
        t11.activate(system.registry)
        t12.activate(system.registry)

        multiplier = system.moral_triangle.calculate_synergy_multiplier()

        # Should be between 1.0 and 2.5
        assert 1.0 <= multiplier <= 2.5

    def test_synergy_conditions(self):
        """Test synergy conditions checking"""
        system = HebrewTokenSystem()
        system.initialize()

        # All tokens active initially
        synergy_active, reason = system.moral_triangle.check_synergy_conditions()

        # Should be False initially (no activations yet)
        assert synergy_active is False


class TestHierarchy:
    """Test hierarchical control"""

    def test_higher_layer_controls_lower(self):
        """Test that higher layers can control lower layers"""
        system = HebrewTokenSystem()
        system.initialize()

        # T15 (Layer 1) should control T07 (Layer 5)
        can_control, _ = system.hierarchy_controller.can_control("T15", "T07")
        assert can_control

    def test_lower_cannot_control_higher(self):
        """Test that lower layers cannot control higher layers"""
        system = HebrewTokenSystem()
        system.initialize()

        # T07 (Layer 5) should NOT control T15 (Layer 1)
        can_control, reason = system.hierarchy_controller.can_control("T07", "T15")
        assert not can_control

    def test_conflict_resolution(self):
        """Test that conflicts are resolved by hierarchy"""
        system = HebrewTokenSystem()
        system.initialize()

        # Conflict between T15 and T07
        winner = system.hierarchy_controller.resolve_conflict("T15", "T07")
        assert winner == "T15"  # Higher layer wins

    def test_hierarchy_validation(self):
        """Test hierarchy structure validation"""
        system = HebrewTokenSystem()
        system.initialize()

        warnings = system.hierarchy_controller.validate_hierarchy()
        # Should have no critical errors (warnings are ok)
        assert isinstance(warnings, list)


class TestIdentity:
    """Test T05 Identity token"""

    def test_identity_registration(self):
        """Test identity registration"""
        system = HebrewTokenSystem()
        system.initialize()

        t05 = system.get_token("T05")
        assert isinstance(t05, IdentityToken)

        t05.register_identity("TEST_ID", "test_agent", {"description": "Test agent"})
        assert t05.is_identity_registered("TEST_ID")

    def test_no_action_without_identity(self):
        """Test that actions without identity are forbidden"""
        system = HebrewTokenSystem()
        system.initialize()

        t05 = system.get_token("T05")
        assert isinstance(t05, IdentityToken)

        # Try to validate action without identity
        is_valid, error = t05.validate_action_identity(None)

        assert not is_valid
        assert "FORBIDDEN" in error


class TestRights:
    """Test T13 Rights token"""

    def test_rights_violation_detection(self):
        """Test that rights violations are detected"""
        system = HebrewTokenSystem()
        system.initialize()

        t13 = system.get_token("T13")
        assert isinstance(t13, RightsToken)

        # Check for discrimination
        violation = t13.check_rights_violation(
            "test_action",
            {"discriminates": True}
        )

        assert violation is not None
        assert "discriminate" in violation.lower()


class TestIntegration:
    """Integration tests for the complete system"""

    def test_complete_system_status(self):
        """Test getting complete system status"""
        system = HebrewTokenSystem()
        system.initialize()

        status = system.get_system_status()

        assert status['initialized']
        assert 'registry' in status
        assert 'constraints' in status
        assert 'hierarchy' in status
        assert 'moral_triangle' in status

    def test_token_relationships(self):
        """Test getting token relationships"""
        system = HebrewTokenSystem()
        system.initialize()

        relationships = system.get_token_relationships("T07")

        assert relationships['token_id'] == "T07"
        assert 'dependencies' in relationships
        assert 'ethical_constraints' in relationships
        assert 'controls' in relationships
        assert 'controlled_by' in relationships


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "-s"])
