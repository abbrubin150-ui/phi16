"""
Tests for governance.py - Multi-Agent Governance Engine

Test Coverage:
1. PhiArchitect proposal creation
2. AgentA2 formal verification
3. AgentA1 ethical review
4. B1Actuator execution
5. B2SafetyMonitor monitoring
6. Complete workflow integration
7. System state transitions (RUN/HOLD/SAFE)
8. Invariant enforcement
"""

import sys
import os
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from governance import (
    GovernanceEngine,
    PhiArchitect,
    AgentA2,
    AgentA1,
    B1Actuator,
    B2SafetyMonitor,
    Proposal,
    ProposalStatus,
    SystemMode
)
from tokens.system import HebrewTokenSystem


def test_phi_architect_proposal_creation():
    """Test Φ-Architect can create proposals"""
    print("Test: Φ-Architect proposal creation")

    # Setup
    token_system = HebrewTokenSystem()
    token_system.initialize()

    # Activate T05 (Identity)
    t05 = token_system.get_token("T05")
    t05.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Test proposal creation
    request = {
        "action": "test_action",
        "data": {"key": "value"},
        "justification": "Test proposal"
    }

    proposal = governance.phi_architect.propose(request)

    # Assertions
    assert proposal is not None, "Proposal should be created"
    assert proposal.action == "test_action"
    assert proposal.proposer == "Φ-Architect"
    assert proposal.status == ProposalStatus.PROPOSED
    assert len(proposal.events) > 0, "Proposal should have events in audit trail"

    print("  ✓ Φ-Architect creates proposals successfully")
    return True


def test_phi_architect_cannot_propose_without_t05():
    """Test Φ-Architect blocked when T05 inactive"""
    print("Test: Φ-Architect blocked without T05")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    # Suspend T05 to make it inactive
    t05 = token_system.get_token("T05")
    t05.suspend("Test: ensuring T05 is inactive")

    governance = GovernanceEngine(token_system=token_system)

    request = {
        "action": "test_action",
        "justification": "Test"
    }

    proposal = governance.phi_architect.propose(request)

    assert proposal is None, "Proposal should fail without T05"

    print("  ✓ Φ-Architect correctly blocked without T05")
    return True


def test_a2_formal_verification():
    """Test A2 formal verification"""
    print("Test: A2 formal verification")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    # Activate required tokens
    for token_id in ["T05", "T09", "T06"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Create proposal
    request = {
        "action": "add_user",  # Valid NAND-verified action
        "data": {"user_id": "u1"},
        "justification": "Test"
    }
    proposal = governance.phi_architect.propose(request)

    # A2 verification
    verdict = governance.agent_a2.verify(proposal)

    assert verdict["approved"] == True, "A2 should approve valid proposal"
    assert proposal.a2_approved == True
    assert proposal.status == ProposalStatus.A2_APPROVED
    assert len(verdict["violations"]) == 0

    print("  ✓ A2 verification successful")
    return True


def test_a2_rejects_invalid_action():
    """Test A2 rejects invalid NAND action"""
    print("Test: A2 rejects invalid action")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T05", "T09", "T06"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Invalid action (not in NAND-verified set)
    request = {
        "action": "invalid_action",
        "data": {},
        "justification": "Test"
    }
    proposal = governance.phi_architect.propose(request)

    verdict = governance.agent_a2.verify(proposal)

    assert verdict["approved"] == False, "A2 should reject invalid action"
    assert proposal.a2_approved == False
    assert proposal.status == ProposalStatus.A2_REJECTED
    assert len(verdict["violations"]) > 0

    print("  ✓ A2 correctly rejects invalid actions")
    return True


def test_a1_ethical_review():
    """Test A1 ethical review with sub-agents"""
    print("Test: A1 ethical review")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T01", "T10", "T13"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Valid proposal with evidence
    request = {
        "action": "add_user",
        "data": {
            "user_id": "u1",
            "evidence": "Form #123",  # A1-א needs evidence
            "data_source": "HR"
        },
        "justification": "Test"
    }
    proposal = governance.phi_architect.propose(request)
    proposal.status = ProposalStatus.A2_APPROVED  # Assume A2 approved

    verdict = governance.agent_a1.review(proposal)

    assert verdict["approved"] == True, "A1 should approve valid proposal"
    assert proposal.a1_approved == True
    assert proposal.status == ProposalStatus.A1_APPROVED

    # Check sub-agent checks
    assert "A1-א" in verdict["sub_agents"]  # Evidence validation
    assert "A1-ד" in verdict["sub_agents"]  # DIA check
    assert "A1-ס" in verdict["sub_agents"]  # Ethical review

    assert verdict["sub_agents"]["A1-א"]["passed"] == True
    assert verdict["sub_agents"]["A1-ד"]["passed"] == True
    assert verdict["sub_agents"]["A1-ס"]["passed"] == True

    print("  ✓ A1 ethical review successful")
    return True


def test_a1_rejects_missing_evidence():
    """Test A1-א rejects proposals without evidence"""
    print("Test: A1-א rejects missing evidence")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T01", "T10", "T13"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Proposal WITHOUT evidence
    request = {
        "action": "add_user",
        "data": {"user_id": "u1"},  # No evidence or data_source
        "justification": "Test"
    }
    proposal = governance.phi_architect.propose(request)

    verdict = governance.agent_a1.review(proposal)

    assert verdict["approved"] == False, "A1 should reject proposal without evidence"
    assert proposal.status == ProposalStatus.A1_REJECTED
    assert verdict["sub_agents"]["A1-א"]["passed"] == False

    print("  ✓ A1-א correctly rejects missing evidence")
    return True


def test_a1_rejects_ethical_violations():
    """Test A1-ס rejects ethical violations"""
    print("Test: A1-ס rejects ethical violations")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T01", "T10", "T13", "T15"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Proposal with privacy violation
    request = {
        "action": "add_user",
        "data": {
            "user_id": "u1",
            "evidence": "Form",
            "violates_privacy": True  # Ethical violation!
        },
        "justification": "Test"
    }
    proposal = governance.phi_architect.propose(request)

    verdict = governance.agent_a1.review(proposal)

    assert verdict["approved"] == False, "A1 should reject ethical violations"
    assert verdict["sub_agents"]["A1-ס"]["passed"] == False
    assert verdict["sub_agents"]["A1-ס"]["severity"] == "high"

    # Should trigger HOLD mode
    assert governance.system_mode == SystemMode.HOLD, "Ethical violation should trigger HOLD"

    print("  ✓ A1-ס correctly rejects ethical violations")
    return True


def test_a1_rejects_dia_violations():
    """Test A1-ד rejects DIA-violating actions"""
    print("Test: A1-ד rejects DIA violations")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T01", "T10", "T13"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # DIA-decreasing action
    request = {
        "action": "delete_record",  # Violates DIA monotonicity
        "data": {"record_id": "r1", "evidence": "Request"},
        "justification": "Test"
    }
    proposal = governance.phi_architect.propose(request)

    verdict = governance.agent_a1.review(proposal)

    assert verdict["approved"] == False, "A1 should reject DIA violations"
    assert verdict["sub_agents"]["A1-ד"]["passed"] == False
    assert verdict["sub_agents"]["A1-ד"]["critical"] == True

    # Should trigger SAFE mode
    assert governance.system_mode == SystemMode.SAFE, "DIA violation should trigger SAFE"

    print("  ✓ A1-ד correctly rejects DIA violations")
    return True


def test_b1_execution():
    """Test B1 execution of approved proposals"""
    print("Test: B1 execution")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T07", "T04"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Create approved proposal
    request = {"action": "test", "data": {}, "justification": "Test"}
    proposal = governance.phi_architect.propose(request)
    proposal.a2_approved = True
    proposal.a1_approved = True
    proposal.status = ProposalStatus.READY_FOR_EXECUTION

    # Execute
    result = governance.b1_actuator.execute(proposal)

    assert result["success"] == True, "B1 should execute approved proposal"
    assert result["commitment_id"] is not None
    assert proposal.status == ProposalStatus.COMMITTED
    assert proposal.commitment_id is not None

    # Check ledger
    assert len(governance.ledger) > 0, "Execution should append to ledger"

    print("  ✓ B1 execution successful")
    return True


def test_b1_blocks_unapproved():
    """Test B1 blocks unapproved proposals"""
    print("Test: B1 blocks unapproved proposals")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    t07 = token_system.get_token("T07")
    t07.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Create proposal without approvals
    request = {"action": "test", "data": {}, "justification": "Test"}
    proposal = governance.phi_architect.propose(request)
    # Don't set approvals

    result = governance.b1_actuator.execute(proposal)

    assert result["success"] == False, "B1 should block unapproved proposals"
    assert "not fully approved" in result["error"]

    print("  ✓ B1 correctly blocks unapproved proposals")
    return True


def test_complete_workflow():
    """Test complete workflow: request → commitment"""
    print("Test: Complete workflow")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    # Activate all required tokens
    for token_id in ["T01", "T05", "T06", "T07", "T09", "T10", "T11", "T13"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Valid request
    request = {
        "action": "add_user",
        "data": {
            "user_id": "u1",
            "name": "Alice",
            "evidence": "Form #123",
            "data_source": "HR"
        },
        "justification": "New user onboarding"
    }

    result = governance.process_request(request)

    # Verify complete workflow
    assert result["success"] == True, "Complete workflow should succeed"
    assert result["proposal_id"] is not None
    assert result["commitment_id"] is not None
    assert result["system_mode"] == "RUN"
    assert len(result["audit_trail"]) >= 5  # All stages

    # Verify audit trail
    trail = " ".join(result["audit_trail"])
    assert "Φ-Architect" in trail
    assert "A2" in trail
    assert "A1" in trail
    assert "B1" in trail

    print("  ✓ Complete workflow successful")
    return True


def test_system_state_transitions():
    """Test system state transitions (RUN → HOLD → RUN)"""
    print("Test: System state transitions")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    governance = GovernanceEngine(token_system=token_system)

    # Initial state
    assert governance.system_mode == SystemMode.RUN

    # Trigger HOLD
    governance._trigger_hold_mode("Test HOLD")
    assert governance.system_mode == SystemMode.HOLD
    assert len(governance.mode_history) == 1

    # Trigger SAFE
    governance.system_mode = SystemMode.RUN  # Reset
    governance._trigger_safe_mode("Test SAFE")
    assert governance.system_mode == SystemMode.SAFE

    print("  ✓ System state transitions work correctly")
    return True


def test_proposal_not_commitment():
    """Test Proposal ≠ Commitment invariant"""
    print("Test: Proposal ≠ Commitment invariant")

    token_system = HebrewTokenSystem()
    token_system.initialize()

    for token_id in ["T01", "T05", "T06", "T07", "T09", "T10", "T11", "T13"]:
        token = token_system.get_token(token_id)
        token.activate(token_system.registry)

    governance = GovernanceEngine(token_system=token_system)

    # Create multiple proposals
    for i in range(5):
        request = {
            "action": "add_user",
            "data": {
                "user_id": f"u{i}",
                "evidence": f"Form {i}",
                "data_source": "HR"
            },
            "justification": f"User {i}"
        }
        governance.process_request(request)

    status = governance.get_system_status()

    # Proposals should equal commitments (all succeeded)
    # But they went through separate agents
    assert status["proposals"]["total"] >= 5
    assert status["proposals"]["committed"] >= 5

    # Verify no single agent did both propose and commit
    # This is structurally enforced by the classes
    assert governance.phi_architect.agent_id == "Φ-Architect"
    assert governance.b1_actuator.agent_id == "B1-Actuator"
    assert governance.phi_architect.agent_id != governance.b1_actuator.agent_id

    print("  ✓ Proposal ≠ Commitment invariant maintained")
    return True


def run_all_tests():
    """Run all governance tests"""
    print("\n" + "=" * 80)
    print("  GOVERNANCE MODULE TESTS")
    print("=" * 80 + "\n")

    tests = [
        test_phi_architect_proposal_creation,
        test_phi_architect_cannot_propose_without_t05,
        test_a2_formal_verification,
        test_a2_rejects_invalid_action,
        test_a1_ethical_review,
        test_a1_rejects_missing_evidence,
        test_a1_rejects_ethical_violations,
        test_a1_rejects_dia_violations,
        test_b1_execution,
        test_b1_blocks_unapproved,
        test_complete_workflow,
        test_system_state_transitions,
        test_proposal_not_commitment
    ]

    passed = 0
    failed = 0

    for test in tests:
        try:
            result = test()
            if result:
                passed += 1
        except AssertionError as e:
            print(f"  ✗ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"  ✗ ERROR: {e}")
            failed += 1

    print("\n" + "=" * 80)
    print(f"  RESULTS: {passed} passed, {failed} failed")
    print("=" * 80 + "\n")

    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
