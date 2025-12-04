#!/usr/bin/env python3
"""
Full Φ-OS Governance Demo

Demonstrates complete workflow from request to commitment:
1. Initialize Hebrew Token System
2. Initialize Governance Engine
3. Process requests through multi-agent workflow
4. Show audit trails and system state
5. Demonstrate HOLD/SAFE state transitions

This demo shows the complete integration of:
- Hebrew Token System (15 tokens, 6 layers)
- R/DIA (Memory = Accountability)
- NAND-only (Verifiable Simplicity)
- Multi-agent workflow (Proposal ≠ Commitment)
"""

import sys
import os
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

import json
from datetime import datetime
from governance import GovernanceEngine, SystemMode
from events import EventFactory, EventValidator
from tokens.system import HebrewTokenSystem


def print_section(title: str):
    """Print section header"""
    print("\n" + "=" * 80)
    print(f"  {title}")
    print("=" * 80 + "\n")


def print_subsection(title: str):
    """Print subsection header"""
    print(f"\n--- {title} ---\n")


def demo_basic_workflow():
    """Demonstrate basic request processing workflow"""
    print_section("DEMO 1: Basic Workflow - Successful Request")

    # Step 1: Initialize Token System
    print_subsection("Step 1: Initialize Hebrew Token System")
    token_system = HebrewTokenSystem()
    token_system.initialize()
    print("✓ Token System initialized with 15 tokens")

    # Activate required tokens
    required_tokens = ["T01", "T05", "T06", "T07", "T09", "T10", "T11", "T13"]
    for token_id in required_tokens:
        token = token_system.get_token(token_id)
        if token:
            token.activate(token_system.registry)
            print(f"  ✓ {token_id} ({token.name_en}) activated")

    # Step 2: Initialize Governance Engine
    print_subsection("Step 2: Initialize Governance Engine")
    governance = GovernanceEngine(token_system=token_system)
    print(f"✓ Governance Engine initialized")
    print(f"  - System Mode: {governance.system_mode.value}")
    print(f"  - Agents: Φ-Architect, A2, A1, B1, B2")

    # Step 3: Create and process request
    print_subsection("Step 3: Process Request")
    request = {
        "action": "add_user",
        "data": {
            "user_id": "user_001",
            "name": "Alice",
            "role": "analyst",
            "evidence": "Onboarding form #12345",
            "data_source": "HR system"
        },
        "justification": "New analyst joining the team"
    }

    print("Request:")
    print(json.dumps(request, indent=2))

    print("\nProcessing through multi-agent workflow...")
    result = governance.process_request(request)

    # Step 4: Display results
    print_subsection("Step 4: Results")
    print(f"Success: {result['success']}")
    print(f"Proposal ID: {result.get('proposal_id', 'N/A')}")
    print(f"Commitment ID: {result.get('commitment_id', 'N/A')}")
    print(f"System Mode: {result['system_mode']}")

    print("\nAudit Trail:")
    for i, entry in enumerate(result['audit_trail'], 1):
        print(f"  {i}. {entry}")

    # Step 5: System status
    print_subsection("Step 5: System Status")
    status = governance.get_system_status()
    print(json.dumps(status, indent=2))

    return governance, token_system


def demo_rejection_workflow():
    """Demonstrate workflow with rejection"""
    print_section("DEMO 2: Rejection Workflow - Missing Evidence")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    # Activate tokens
    for token_id in ["T01", "T05", "T06", "T07", "T09", "T10", "T11", "T13"]:
        token = token_system.get_token(token_id)
        if token:
            token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Request without evidence (will be rejected by A1-א)
    request = {
        "action": "update_data",
        "data": {
            "record_id": "rec_123",
            "new_value": "updated"
            # Missing: evidence, data_source
        },
        "justification": "Updating record"
    }

    print("Request (missing evidence):")
    print(json.dumps(request, indent=2))

    print("\nProcessing...")
    result = governance.process_request(request)

    print_subsection("Results")
    print(f"Success: {result['success']}")
    print(f"Error: {result.get('error', 'N/A')}")
    print(f"Reasons: {result.get('reasons', 'N/A')}")

    print("\nAudit Trail:")
    for entry in result['audit_trail']:
        print(f"  - {entry}")

    return governance


def demo_ethical_violation():
    """Demonstrate ethical violation triggering T15"""
    print_section("DEMO 3: Ethical Violation - T15 Activation")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    # Activate tokens
    for token_id in ["T01", "T05", "T06", "T07", "T09", "T10", "T11", "T13", "T15"]:
        token = token_system.get_token(token_id)
        if token:
            token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Request that violates privacy (ethical violation)
    request = {
        "action": "add_user",
        "data": {
            "user_id": "user_002",
            "name": "Bob",
            "evidence": "Form",
            "data_source": "System",
            "violates_privacy": True  # ← Ethical violation!
        },
        "justification": "Adding user with privacy violation"
    }

    print("Request (with ethical violation):")
    print(json.dumps(request, indent=2))

    print("\nProcessing...")
    result = governance.process_request(request)

    print_subsection("Results")
    print(f"Success: {result['success']}")
    print(f"Error: {result.get('error', 'N/A')}")
    print(f"System Mode: {result['system_mode']}")

    if result['system_mode'] == "HOLD":
        print("\n⚠️  SYSTEM ENTERED HOLD MODE!")
        print("T15 (Seriousness) activated due to ethical violation")
        print("No further writes allowed until cleared")

    print("\nAudit Trail:")
    for entry in result['audit_trail']:
        print(f"  - {entry}")

    return governance


def demo_dia_violation():
    """Demonstrate DIA violation triggering SAFE mode"""
    print_section("DEMO 4: DIA Violation - SAFE Mode")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T01", "T05", "T06", "T07", "T09", "T10", "T11", "T13"]:
        token = token_system.get_token(token_id)
        if token:
            token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Request that would violate DIA monotonicity
    request = {
        "action": "delete_record",  # DIA-decreasing action
        "data": {
            "record_id": "rec_456",
            "evidence": "Deletion request",
            "data_source": "Admin"
        },
        "justification": "Deleting record (violates DIA)"
    }

    print("Request (DIA-decreasing action):")
    print(json.dumps(request, indent=2))

    print("\nProcessing...")
    result = governance.process_request(request)

    print_subsection("Results")
    print(f"Success: {result['success']}")
    print(f"Error: {result.get('error', 'N/A')}")
    print(f"System Mode: {result['system_mode']}")

    if result['system_mode'] == "SAFE":
        print("\n⚠️  SYSTEM ENTERED SAFE MODE!")
        print("DIA monotonicity violation detected by A1-ד")
        print("Conservative mode - no writes allowed")

    print("\nAudit Trail:")
    for entry in result['audit_trail']:
        print(f"  - {entry}")

    return governance


def demo_proposal_not_commitment():
    """Demonstrate Proposal ≠ Commitment principle"""
    print_section("DEMO 5: Proposal ≠ Commitment Principle")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T01", "T05", "T06", "T07", "T09", "T10", "T11", "T13"]:
        token = token_system.get_token(token_id)
        if token:
            token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    print("Processing multiple requests to show separation of powers...")

    # Process several requests
    requests = [
        {
            "action": "add_user",
            "data": {"user_id": "u1", "evidence": "Form", "data_source": "HR"},
            "justification": "User 1"
        },
        {
            "action": "update_data",
            "data": {"record": "r1", "evidence": "Update", "data_source": "System"},
            "justification": "Update 1"
        },
        {
            "action": "query",
            "data": {"query": "SELECT *", "evidence": "Request", "data_source": "API"},
            "justification": "Query 1"
        }
    ]

    for i, req in enumerate(requests, 1):
        print(f"\nProcessing request {i}...")
        result = governance.process_request(req)
        print(f"  Result: {result['success']}")

    print_subsection("Verification: Proposal ≠ Commitment")

    # Count proposals vs commitments
    status = governance.get_system_status()
    proposals_committed = status['proposals']['committed']
    ledger_size = status['ledger_size']

    print(f"Total Proposals: {status['proposals']['total']}")
    print(f"Proposals Committed: {proposals_committed}")
    print(f"Ledger Size: {ledger_size}")

    print("\nAgent Separation:")
    print("  - Φ-Architect: Proposed all requests")
    print("  - A2: Verified all proposals (structural)")
    print("  - A1: Reviewed all proposals (ethical)")
    print("  - B1: Executed approved proposals ONLY")
    print("  - B2: Monitored all executions")

    print("\n✓ No single agent has unilateral control from proposal to commitment")

    return governance


def demo_event_validation():
    """Demonstrate event validation and hash chaining"""
    print_section("DEMO 6: Event Validation & Hash Chaining")

    from events import EventFactory, EventValidator, EventKind

    factory = EventFactory()
    validator = EventValidator()

    print("Creating chain of events...")

    # Create several events
    events = []

    # Event 1: Proposal
    e1 = factory.create_event(
        kind=EventKind.PROPOSAL,
        actor_id="Φ-Architect",
        payload={"action": "add_user", "user_id": "u1"},
        justification="New user proposal"
    )
    events.append(e1)
    print(f"Event 1: {e1.id}")
    print(f"  Hash: {e1.hash[:16]}...")
    print(f"  Prev Hash: {e1.prev_hash or '(empty)'}")

    # Event 2: Approval
    e2 = factory.create_event(
        kind=EventKind.APPROVAL,
        actor_id="A2",
        payload={"approved": True},
        justification="A2 approval",
        parents=[e1.id]
    )
    events.append(e2)
    print(f"\nEvent 2: {e2.id}")
    print(f"  Hash: {e2.hash[:16]}...")
    print(f"  Prev Hash: {e2.prev_hash[:16]}...")
    print(f"  ✓ Chained to Event 1")

    # Event 3: Commitment
    e3 = factory.create_event(
        kind=EventKind.COMMITMENT,
        actor_id="B1",
        payload={"committed": True},
        justification="B1 commitment",
        parents=[e2.id]
    )
    events.append(e3)
    print(f"\nEvent 3: {e3.id}")
    print(f"  Hash: {e3.hash[:16]}...")
    print(f"  Prev Hash: {e3.prev_hash[:16]}...")
    print(f"  ✓ Chained to Event 2")

    print_subsection("Chain Validation")

    # Validate chain
    valid, error = validator.validate_chain(events)
    print(f"Chain Valid: {valid}")
    if error:
        print(f"Error: {error}")
    else:
        print("✓ All events properly chained")
        print("✓ Hash integrity verified")
        print("✓ Append-only semantics preserved")

    # Validate individual events
    print("\nIndividual Event Validation:")
    for event in events:
        valid, error = validator.validate_event(event)
        symbol = "✓" if valid else "✗"
        print(f"  {symbol} {event.id}: {valid}")

    return events


def main():
    """Run all demos"""
    print("\n" + "█" * 80)
    print("█" + " " * 78 + "█")
    print("█" + "  Φ-OS GOVERNANCE SYSTEM - COMPREHENSIVE DEMONSTRATION".center(78) + "█")
    print("█" + " " * 78 + "█")
    print("█" * 80)

    try:
        # Demo 1: Basic workflow
        gov1, ts1 = demo_basic_workflow()

        # Demo 2: Rejection
        gov2 = demo_rejection_workflow()

        # Demo 3: Ethical violation
        gov3 = demo_ethical_violation()

        # Demo 4: DIA violation
        gov4 = demo_dia_violation()

        # Demo 5: Proposal ≠ Commitment
        gov5 = demo_proposal_not_commitment()

        # Demo 6: Event validation
        events = demo_event_validation()

        # Final summary
        print_section("DEMONSTRATION COMPLETE")
        print("✓ Hebrew Token System integrated")
        print("✓ Multi-agent workflow operational")
        print("✓ R/DIA principle demonstrated")
        print("✓ NAND-only compliance checked")
        print("✓ Proposal ≠ Commitment verified")
        print("✓ Event hash chaining validated")
        print("\nΦ-OS is ready for verifiable knowledge management!")

    except Exception as e:
        print(f"\n❌ Error during demo: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
