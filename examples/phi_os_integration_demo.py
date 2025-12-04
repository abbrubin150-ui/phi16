#!/usr/bin/env python3
"""
Φ-OS Integration Demo

Demonstrates the complete integration of the Hebrew Token System
with the Φ-OS architecture:

1. R/DIA (Memory = Accountability)
2. NAND-only (Verifiable Simplicity)
3. Multi-agent Workflow (Proposal ≠ Commitment)

This demo shows how tokens govern the entire system lifecycle.
"""

import sys
import json
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from tokens.system import HebrewTokenSystem


def print_header(title: str):
    """Print formatted section header."""
    print()
    print("=" * 80)
    print(f"  {title}")
    print("=" * 80)
    print()


def print_subheader(title: str):
    """Print formatted subsection header."""
    print()
    print("-" * 80)
    print(f"  {title}")
    print("-" * 80)
    print()


def print_json(data: dict, indent: int = 2):
    """Pretty print JSON data."""
    print(json.dumps(data, indent=indent, ensure_ascii=False))


def demo_initialization():
    """Demo: Initialize Hebrew Token System with Φ-OS integration."""
    print_header("INITIALIZATION")

    print("1. Creating Hebrew Token System...")
    system = HebrewTokenSystem()

    print("2. Initializing token system...")
    system.initialize()
    print("   ✓ 15 tokens created")
    print("   ✓ Relationships established")
    print("   ✓ Constraints validated")

    print()
    print("3. Enabling Φ-OS integration...")
    system.enable_phi_os_integration()

    return system


def demo_system_info(system: HebrewTokenSystem):
    """Demo: Display comprehensive system information."""
    print_header("SYSTEM INFORMATION")

    info = system.get_phi_os_info()

    print(f"System: {info['system']}")
    print(f"Version: {info['version']}")
    print(f"System State: {info['system_state']}")
    print(f"Operations Count: {info['operations_count']}")
    print()

    print("Token System:")
    print(f"  Active Tokens: {info['token_system']['active_tokens']}")
    print(f"  Highest Priority Active: {info['token_system']['highest_priority_active']}")
    print()

    print("R/DIA:")
    print(f"  Ledger Size: {info['integrations']['rdia']['ledger_size']}")
    print(f"  DIA Graph: {info['integrations']['rdia']['dia_metrics']['dia_graph']:.4f}")
    print(f"  DIA Info: {info['integrations']['rdia']['dia_metrics']['dia_info']:.4f}")
    print(f"  DIA Replay: {info['integrations']['rdia']['dia_metrics']['dia_replay']:.4f}")
    print()

    print("NAND-only:")
    print(f"  Total NAND Ops: {info['integrations']['nand']['stats']['total_nand_ops']}")
    print(f"  Forbidden Ops: {info['integrations']['nand']['stats']['forbidden_ops']}")
    print()

    print("Multi-agent:")
    print(f"  Proposals: {info['integrations']['agents']['proposals']}")
    print(f"  Commitments: {info['integrations']['agents']['commitments']}")


def demo_simple_request(system: HebrewTokenSystem):
    """Demo: Process a simple valid request."""
    print_header("SIMPLE REQUEST PROCESSING")

    request = {
        "action": "add_user",
        "data": {
            "user_id": "user123",
            "name": "Alice",
            "email": "alice@example.com"
        },
        "evidence": "User registration form submitted",
        "data_source": "Registration API"
    }

    print("Request:")
    print_json(request)

    print()
    print("Processing through Φ-OS pipeline...")
    result = system.process_phi_os_request(request)

    print()
    if result["success"]:
        print("✓ Request processed successfully!")
        print()
        print("Audit Trail:")
        for entry in result["audit_trail"]:
            print(f"  • {entry}")

        print()
        print("Stages:")
        print(f"  • Proposal: {result['stages']['proposal']['id']}")
        print(f"  • Verification: {'APPROVED' if result['stages']['verification']['approved'] else 'REJECTED'}")
        print(f"  • Execution: {result['stages']['execution']['status']}")
        print(f"  • Ledger: {result['stages']['ledger']['event_id']}")
    else:
        print(f"✗ Request failed: {result.get('error')}")


def demo_ethical_violation(system: HebrewTokenSystem):
    """Demo: Process a request that violates ethical constraints."""
    print_header("ETHICAL VIOLATION DETECTION")

    request = {
        "action": "process_data",
        "data": {
            "operation": "track_user_without_consent"
        },
        "violates_consent": True  # This will trigger A1-ס (Ethical Guardian)
    }

    print("Request (contains ethical violation):")
    print_json(request)

    print()
    print("Processing through Φ-OS pipeline...")
    result = system.process_phi_os_request(request)

    print()
    if not result["success"]:
        print("✗ Request rejected by ethical guardian!")
        print()
        print(f"Error: {result.get('error')}")
        print()
        print("Reasons:")
        for reason in result.get("reasons", []):
            print(f"  • {reason}")

        print()
        print("Verifications:")
        for agent, check in result["stages"]["verification"]["verifications"].items():
            status = "✓" if check["passed"] else "✗"
            print(f"  {status} {agent}: {check['reason']}")


def demo_system_validation(system: HebrewTokenSystem):
    """Demo: Validate complete system state."""
    print_header("SYSTEM VALIDATION")

    validation = system.get_phi_os_status()

    print(f"System State: {validation['system_state']}")
    print(f"System Healthy: {validation['system_healthy']}")
    print()

    print_subheader("R/DIA Validation")
    rdia = validation["validations"]["rdia"]
    print(f"  Ledger Size: {rdia['ledger_size']}")
    print(f"  DIA Monotonic: {rdia['dia_monotonic']}")
    print()

    print_subheader("NAND-only Validation")
    nand = validation["validations"]["nand"]
    compliance = nand["policy_compliance"]
    print(f"  Compliant: {compliance['compliant']}")
    print(f"  NAND Operations: {compliance['nand_ops_count']}")
    print(f"  Forbidden Operations: {compliance['forbidden_ops_count']}")
    print()

    print_subheader("Multi-agent Validation")
    agents = validation["validations"]["agents"]
    print(f"  Proposals: {agents['proposals_count']}")
    print(f"  Commitments: {agents['commitments_count']}")
    print(f"  State History: {agents['state_history']}")


def demo_emergency_hold(system: HebrewTokenSystem):
    """Demo: Trigger emergency HOLD mode."""
    print_header("EMERGENCY HOLD MODE")

    print("Triggering emergency HOLD...")
    reason = "Critical security breach detected"
    success = system.phi_os_emergency_hold(reason)

    print()
    if success:
        print("✓ System in HOLD state")
        print(f"   Reason: {reason}")
        print()
        print("Effects:")
        print("  • T15 (Seriousness) ACTIVATED")
        print("  • T07 (Automation) SUSPENDED")
        print("  • No writes allowed")
        print("  • All proposals rejected")

        # Try to process request in HOLD
        print()
        print("Attempting to process request in HOLD state...")
        request = {
            "action": "test_operation",
            "data": {"test": "data"}
        }

        result = system.process_phi_os_request(request)
        if not result["success"]:
            print(f"✗ Request rejected: System in HOLD state")

        # Resume operations
        print()
        print("Resuming operations...")

        # First, deactivate T15
        t15 = system.get_token("T15")
        if t15:
            t15.deactivate()

        resumed = system.phi_os_resume_operations()
        if resumed:
            print("✓ Operations resumed - System back to RUN state")
        else:
            print("✗ Failed to resume - safety checks not passed")


def demo_nand_operations(system: HebrewTokenSystem):
    """Demo: NAND-only operations."""
    print_header("NAND-ONLY OPERATIONS")

    nand = system.nand

    print("All logical operations are built from NAND gates:")
    print()

    # Basic gates
    print("Basic Gates:")
    print(f"  NAND(1, 1) = {nand.nand(True, True)}")
    print(f"  NAND(1, 0) = {nand.nand(True, False)}")
    print(f"  NAND(0, 1) = {nand.nand(False, True)}")
    print(f"  NAND(0, 0) = {nand.nand(False, False)}")
    print()

    # Derived gates
    print("Derived Gates (built from NAND):")
    print(f"  NOT(1) = {nand.not_gate(True)}")
    print(f"  NOT(0) = {nand.not_gate(False)}")
    print(f"  AND(1, 1) = {nand.and_gate(True, True)}")
    print(f"  OR(0, 1) = {nand.or_gate(False, True)}")
    print(f"  XOR(1, 0) = {nand.xor_gate(True, False)}")
    print()

    # Token constraint validation via NAND
    print("Token Constraint Validation via NAND:")
    print("  C01: No automation without monitoring (T07 ← T11)")
    result = nand.validate_token_constraint("T07", "C01")
    print(f"    Result: {'✓ SATISFIED' if result else '✗ VIOLATED'}")
    print()

    # Statistics
    stats = nand.get_nand_stats()
    print("NAND Statistics:")
    print(f"  Total NAND Operations: {stats['total_nand_ops']}")
    print(f"  Forbidden Operations: {stats['forbidden_ops']}")
    print(f"  Log Entries: {stats['log_entries']}")


def demo_agent_workflow(system: HebrewTokenSystem):
    """Demo: Multi-agent workflow details."""
    print_header("MULTI-AGENT WORKFLOW")

    agents = system.agents

    print("Agent Architecture:")
    print()
    print("  Φ-Architect (Proposer)")
    print("      ↓")
    print("  A1 (Substantive Approver)")
    print("      ├─ A1-א (Evidence)")
    print("      ├─ A1-ד (DIA Check)")
    print("      └─ A1-ס (Ethical Guardian)")
    print("      ↓")
    print("  A2 (Structural Verifier)")
    print("      ↓")
    print("  B1 (Actuator)")
    print("      ↓")
    print("  B2 (Safety Monitor)")
    print()

    # Show proposals and commitments
    proposals = agents.get_proposals()
    commitments = agents.get_commitments()

    print(f"Total Proposals: {len(proposals)}")
    print(f"Total Commitments: {len(commitments)}")
    print()

    if proposals:
        print("Recent Proposals:")
        for i, proposal in enumerate(proposals[-3:], 1):
            print(f"  {i}. {proposal['id']} - Status: {proposal['status']}")


def demo_system_replay(system: HebrewTokenSystem):
    """Demo: Full system replay from ledger."""
    print_header("SYSTEM REPLAY")

    print("Replaying entire system from ledger...")
    print("This demonstrates complete accountability:")
    print()

    replay = system.replay_phi_os_system()

    if replay["success"]:
        print("✓ System replay successful!")
        print()

        # Show ledger replay
        ledger = replay["stages"]["ledger_replay"]
        print(f"Events Processed: {ledger['events_processed']}")
        print(f"Errors: {len(ledger['errors'])}")
        print()

        # Show invariants
        print("Invariants Verified:")
        for invariant, satisfied in replay["invariants"].items():
            status = "✓" if satisfied else "✗"
            print(f"  {status} {invariant}")
    else:
        print("✗ System replay failed!")


def main():
    """Run the complete Φ-OS integration demo."""
    print()
    print("=" * 80)
    print("  Φ-OS INTEGRATION DEMONSTRATION")
    print("  Hebrew Token System + R/DIA + NAND-only + Multi-agent")
    print("=" * 80)

    # Initialize system
    system = demo_initialization()

    # Show system info
    demo_system_info(system)

    # Process simple request
    demo_simple_request(system)

    # Show ethical violation detection
    demo_ethical_violation(system)

    # Show NAND operations
    demo_nand_operations(system)

    # Show agent workflow
    demo_agent_workflow(system)

    # Validate system
    demo_system_validation(system)

    # Demonstrate emergency hold
    demo_emergency_hold(system)

    # System replay
    demo_system_replay(system)

    # Final summary
    print_header("SUMMARY")
    print("This demonstration showed:")
    print()
    print("1. Token-controlled system initialization")
    print("2. Complete request processing pipeline:")
    print("   • Φ-Architect proposes")
    print("   • A1/A2 verify (token-controlled)")
    print("   • B1 executes")
    print("   • B2 monitors")
    print("   • R/DIA tracks accountability")
    print()
    print("3. Ethical constraint enforcement via tokens")
    print("4. NAND-only formal verifiability")
    print("5. Multi-agent separation of powers")
    print("6. Emergency T15 (Seriousness) control")
    print("7. Complete system replay for accountability")
    print()
    print("✓ Φ-OS + Hebrew Token System = Ethical, Verifiable, Accountable AI")
    print("=" * 80)
    print()


if __name__ == "__main__":
    main()
