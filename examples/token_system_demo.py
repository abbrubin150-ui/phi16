#!/usr/bin/env python3
"""
Hebrew Token System Demonstration

This script demonstrates the key features of the Hebrew Token System:
1. System initialization with all 15 tokens
2. Constraint enforcement
3. Emergency seriousness mode (T15)
4. Moral triangle feedback loop
5. Identity and rights protection
"""

import sys
sys.path.insert(0, '/home/user/phi16')

from tokens.system import HebrewTokenSystem
from tokens.t05_identity import IdentityToken
from tokens.layer2_absolute import RightsToken
from tokens.layer3_moral import MonitorToken, MeasureToken
import json


def print_section(title):
    """Print a section header"""
    print("\n" + "=" * 80)
    print(f"  {title}")
    print("=" * 80)


def demo_system_initialization():
    """Demonstrate system initialization"""
    print_section("1. SYSTEM INITIALIZATION")

    system = HebrewTokenSystem()
    system.initialize()

    print("✓ Hebrew Token System initialized successfully")
    print(f"✓ All 15 tokens created and registered")
    print(f"✓ Constraint enforcer active")
    print(f"✓ Hierarchy controller active")
    print(f"✓ Moral triangle feedback loop ready")

    return system


def demo_hierarchy(system):
    """Demonstrate hierarchical structure"""
    print_section("2. HIERARCHICAL STRUCTURE")

    hierarchy = system.hierarchy_controller.get_hierarchy_map()

    for layer_name, token_ids in hierarchy.items():
        tokens_str = ", ".join(token_ids)
        print(f"{layer_name:25} : {tokens_str}")


def demo_constraints(system):
    """Demonstrate constraint checking"""
    print_section("3. ETHICAL CONSTRAINTS")

    constraint_status = system.constraint_enforcer.get_constraint_status()

    print(f"Total constraints: {constraint_status['total_constraints']}")
    print(f"Active violations: {constraint_status['violations']}")
    print()

    for constraint_id, info in constraint_status['constraints'].items():
        if info['type'] == 'ethical':
            symbol = "✓" if info['satisfied'] else "✗"
            print(f"  {symbol} {constraint_id}")
            print(f"     {info['description']}")


def demo_identity(system):
    """Demonstrate identity requirements"""
    print_section("4. IDENTITY ENFORCEMENT (T05)")

    t05 = system.get_token("T05")
    if isinstance(t05, IdentityToken):
        # Register Φ-OS agents
        agents = [
            ("PHI", "architect", "Φ-Architect - Main reasoner"),
            ("A1", "approver", "A1 Substantive Approver"),
            ("A2", "verifier", "A2 Procedural Verifier"),
            ("B1", "actuator", "B1 Actuator"),
            ("B2", "monitor", "B2 Safety Monitor")
        ]

        print("Registering Φ-OS agents:")
        for agent_id, agent_type, description in agents:
            t05.register_identity(
                agent_id,
                agent_type,
                {"description": description}
            )
            print(f"  ✓ {agent_id}: {description}")

        print()
        print("Testing identity validation:")

        # Valid identity
        is_valid, error = t05.validate_action_identity("PHI")
        print(f"  Action with identity 'PHI': {'✓ ALLOWED' if is_valid else '✗ DENIED'}")

        # No identity
        is_valid, error = t05.validate_action_identity(None)
        print(f"  Action without identity: {'✓ ALLOWED' if is_valid else '✗ DENIED'}")
        if error:
            print(f"    Reason: {error}")


def demo_rights_protection(system):
    """Demonstrate rights protection"""
    print_section("5. RIGHTS PROTECTION (T13)")

    t13 = system.get_token("T13")
    if isinstance(t13, RightsToken):
        print("Protected rights:")
        for right in sorted(t13.get_protected_rights()):
            print(f"  • {right}")

        print()
        print("Testing rights violation detection:")

        # Check various scenarios
        scenarios = [
            ("Normal operation", {}),
            ("Discriminatory action", {"discriminates": True}),
            ("Lacks consent", {"lacks_consent": True}),
            ("Privacy violation", {"violates_privacy": True})
        ]

        for scenario_name, context in scenarios:
            violation = t13.check_rights_violation(scenario_name, context)
            if violation:
                print(f"  ✗ {scenario_name}: VIOLATION DETECTED")
                print(f"    {violation}")
            else:
                print(f"  ✓ {scenario_name}: No violation")


def demo_emergency_mode(system):
    """Demonstrate emergency seriousness mode"""
    print_section("6. EMERGENCY SERIOUSNESS MODE (T15)")

    print("Current state:")
    t07 = system.get_token("T07")
    t03 = system.get_token("T03")
    print(f"  T07 (Automation): {t07.state.value}")
    print(f"  T03 (Compute): {t03.state.value}")

    print()
    print("Triggering emergency mode (simulated rights violation)...")
    system.trigger_emergency("Rights violation detected", triggered_by="T13")

    print(f"  T07 (Automation): {t07.state.value}")
    print(f"  T03 (Compute): {t03.state.value}")

    print()
    print("Releasing emergency mode (forced)...")
    released = system.release_emergency(force=True)
    if released:
        print("  ✓ Emergency mode released")
        print(f"  T07 (Automation): {t07.state.value}")
        print(f"  T03 (Compute): {t03.state.value}")


def demo_moral_triangle(system):
    """Demonstrate moral triangle feedback loop"""
    print_section("7. MORAL TRIANGLE FEEDBACK LOOP")

    print("Moral Triangle Health:")
    health = system.moral_triangle.get_triangle_health()
    print(f"  T10 (Measure):  {health['t10_status']}")
    print(f"  T11 (Monitor):  {health['t11_status']}")
    print(f"  T12 (Learn):    {health['t12_status']}")
    print(f"  Synergy Active: {health['synergy_active']}")
    print(f"  Multiplier:     {health['synergy_multiplier']:.2f}x")

    print()
    print("Executing feedback cycle (simulated anomaly)...")

    # Define the metric first
    t10 = system.get_token("T10")
    if isinstance(t10, MeasureToken):
        t10.define_metric(
            "system_load",
            "ratio",
            ethical_value="system_stability"
        )

    monitored_event = {
        'state_name': 'system_load',
        'value': 95,
        'expected_range': (0, 80)  # Anomaly: value exceeds expected
    }

    result = system.execute_moral_triangle_cycle(monitored_event)

    print(f"  Cycle ID: {result['cycle_id']}")
    print(f"  Duration: {result['duration_ms']:.2f}ms")
    print(f"  Steps executed: {len(result['steps'])}")

    for step in result['steps']:
        print(f"    • {step['step'].upper()} ({step['token']})")


def demo_constraint_violation(system):
    """Demonstrate constraint violation and enforcement"""
    print_section("8. CONSTRAINT VIOLATION & ENFORCEMENT")

    print("Simulating constraint violation:")
    print("  Suspending T11 (Monitor)...")

    t11 = system.get_token("T11")
    t11.suspend("Demonstration of constraint enforcement", suspended_by="DEMO")

    print()
    print("Checking constraints...")
    violations = system.constraint_enforcer.check_all_constraints()

    if violations:
        print(f"  Found {len(violations)} violation(s):")
        for v in violations:
            print(f"    ✗ {v.constraint_id}: {v.description}")

    print()
    print("Enforcing constraints...")
    system.constraint_enforcer.enforce_constraints()

    t07 = system.get_token("T07")
    print(f"  T07 (Automation) state: {t07.state.value}")
    print(f"    Reason: {t07._suspension_reason}")

    # Restore
    print()
    print("Restoring T11...")
    t11.resume(system.registry)
    t07.resume(system.registry)


def main():
    """Main demonstration function"""
    print("=" * 80)
    print("HEBREW TOKEN SYSTEM - COMPREHENSIVE DEMONSTRATION")
    print("=" * 80)
    print()
    print("This demonstration shows the key features of the Hebrew Token System,")
    print("an ethical-logical governance framework for Φ-OS.")
    print()

    # Run demonstrations
    system = demo_system_initialization()
    demo_hierarchy(system)
    demo_constraints(system)
    demo_identity(system)
    demo_rights_protection(system)
    demo_moral_triangle(system)
    demo_emergency_mode(system)
    demo_constraint_violation(system)

    print_section("DEMONSTRATION COMPLETE")
    print()
    print("The Hebrew Token System provides:")
    print("  ✓ Explicit ethical control layer over technical operations")
    print("  ✓ Hierarchical governance with 6 layers")
    print("  ✓ Unbreakable ethical constraints enforced in code")
    print("  ✓ Emergency control mechanisms")
    print("  ✓ Continuous learning and improvement feedback loops")
    print("  ✓ Complete traceability through identity requirements")
    print()
    print("Core Principle: 'Ethics before technology'")
    print()


if __name__ == "__main__":
    main()
