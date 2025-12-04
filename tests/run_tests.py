#!/usr/bin/env python3
"""
Simple test runner for the Hebrew Token System (no pytest required)
"""

import sys
sys.path.insert(0, '/home/user/phi16')

from tokens.system import HebrewTokenSystem
from tokens.base import TokenState


def test_system_initialization():
    """Test that the system initializes successfully"""
    print("Testing system initialization... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()
        assert system._initialized
        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def test_all_15_tokens_created():
    """Test that all 15 tokens are created"""
    print("Testing all 15 tokens created... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()

        expected_tokens = [
            "T01", "T02", "T03", "T04", "T05", "T06", "T07", "T08",
            "T09", "T10", "T11", "T12", "T13", "T14", "T15"
        ]

        for token_id in expected_tokens:
            token = system.get_token(token_id)
            assert token is not None, f"Token {token_id} not found"

        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def test_constraint_no_automation_without_monitoring():
    """Test C01: No automation without monitoring"""
    print("Testing constraint: No automation without monitoring... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()

        t11 = system.get_token("T11")
        t11.suspend("Testing", suspended_by="TEST")

        violations = system.constraint_enforcer.check_all_constraints()
        automation_violations = [
            v for v in violations
            if v.constraint_id == "C01_NO_AUTOMATION_WITHOUT_MONITORING"
        ]

        assert len(automation_violations) > 0
        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def test_emergency_mode():
    """Test T15 emergency mode activation"""
    print("Testing emergency mode... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()

        system.trigger_emergency("Test", triggered_by="TEST")

        t15 = system.get_token("T15")
        from tokens.t15_seriousness import SeriousnessToken
        assert isinstance(t15, SeriousnessToken)
        assert t15.is_active_emergency()

        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def test_emergency_suspends_automation():
    """Test that emergency mode suspends automation"""
    print("Testing emergency suspends automation... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()

        system.trigger_emergency("Test", triggered_by="TEST")

        t07 = system.get_token("T07")
        assert t07.state == TokenState.SUSPENDED

        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def test_moral_triangle_cycle():
    """Test moral triangle feedback cycle"""
    print("Testing moral triangle cycle... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()

        # Define metric first
        t10 = system.get_token("T10")
        from tokens.layer3_moral import MeasureToken
        if isinstance(t10, MeasureToken):
            t10.define_metric("test_metric", "count")

        monitored_event = {
            'state_name': 'test_metric',
            'value': 100,
            'expected_range': (0, 50)
        }

        result = system.execute_moral_triangle_cycle(monitored_event)
        assert 'cycle_id' in result
        assert len(result['steps']) > 0

        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def test_hierarchy_control():
    """Test hierarchical control"""
    print("Testing hierarchy control... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()

        # T15 should control T07
        can_control, _ = system.hierarchy_controller.can_control("T15", "T07")
        assert can_control

        # T07 should NOT control T15
        can_control, _ = system.hierarchy_controller.can_control("T07", "T15")
        assert not can_control

        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def test_identity_enforcement():
    """Test identity enforcement"""
    print("Testing identity enforcement... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()

        t05 = system.get_token("T05")
        from tokens.t05_identity import IdentityToken

        if isinstance(t05, IdentityToken):
            t05.register_identity("TEST", "test")
            is_valid, _ = t05.validate_action_identity("TEST")
            assert is_valid

            is_valid, error = t05.validate_action_identity(None)
            assert not is_valid
            assert "FORBIDDEN" in error

        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def test_rights_violation_detection():
    """Test rights violation detection"""
    print("Testing rights violation detection... ", end="")
    try:
        system = HebrewTokenSystem()
        system.initialize()

        t13 = system.get_token("T13")
        from tokens.layer2_absolute import RightsToken

        if isinstance(t13, RightsToken):
            violation = t13.check_rights_violation(
                "test_action",
                {"discriminates": True}
            )
            assert violation is not None

        print("✓ PASS")
        return True
    except Exception as e:
        print(f"✗ FAIL: {e}")
        return False


def main():
    """Run all tests"""
    print("=" * 80)
    print("HEBREW TOKEN SYSTEM - TEST SUITE")
    print("=" * 80)
    print()

    tests = [
        test_system_initialization,
        test_all_15_tokens_created,
        test_constraint_no_automation_without_monitoring,
        test_emergency_mode,
        test_emergency_suspends_automation,
        test_moral_triangle_cycle,
        test_hierarchy_control,
        test_identity_enforcement,
        test_rights_violation_detection,
    ]

    passed = 0
    failed = 0

    for test in tests:
        if test():
            passed += 1
        else:
            failed += 1

    print()
    print("=" * 80)
    print(f"TEST RESULTS: {passed} passed, {failed} failed")
    print("=" * 80)

    if failed > 0:
        sys.exit(1)
    else:
        print()
        print("✓ All tests passed!")


if __name__ == "__main__":
    main()
