"""
Φ-OS Multi-Agent Governance Engine

Implements the complete multi-agent workflow ensuring "Proposal ≠ Commitment".

Architecture:
    Φ-Architect → A2 (Formal) → A1 (Ethical) → B1 (Actuator) → B2 (Safety Monitor)
    Proposes      Verifies       Approves      Executes       Monitors

Key Principles:
- No single agent has unilateral control from proposal to execution
- All operations governed by Hebrew Token System
- Complete audit trail in append-only ledger
- Fail-closed: errors trigger HOLD state
"""

from __future__ import annotations

import hashlib
import json
import logging
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional
from dataclasses import dataclass, field

# Import TokenState for checking token states
try:
    from tokens.base import TokenState
except ImportError:
    # If tokens not available, define minimal enum
    class TokenState(Enum):
        ACTIVE = "active"
        SUSPENDED = "suspended"
        HALTED = "halted"

logger = logging.getLogger(__name__)


class ProposalStatus(Enum):
    """Status of a proposal in the workflow"""
    DRAFT = "draft"
    PROPOSED = "proposed"
    A2_REVIEW = "a2_review"
    A2_APPROVED = "a2_approved"
    A2_REJECTED = "a2_rejected"
    A1_REVIEW = "a1_review"
    A1_APPROVED = "a1_approved"
    A1_REJECTED = "a1_rejected"
    READY_FOR_EXECUTION = "ready_for_execution"
    EXECUTING = "executing"
    COMMITTED = "committed"
    FAILED = "failed"


class SystemMode(Enum):
    """System operating modes"""
    RUN = "RUN"      # Normal operation
    HOLD = "HOLD"    # Consensus failure, no writes
    SAFE = "SAFE"    # Policy violation, no writes


@dataclass
class Proposal:
    """Proposal structure for governance workflow"""
    id: str
    timestamp: str
    proposer: str  # Agent ID
    action: str
    payload: Dict[str, Any]
    justification: str
    status: ProposalStatus = ProposalStatus.DRAFT

    # Approval tracking
    a2_approved: bool = False
    a2_verdict: Optional[Dict] = None
    a1_approved: bool = False
    a1_verdict: Optional[Dict] = None

    # Execution tracking
    commitment_id: Optional[str] = None
    executed_at: Optional[str] = None

    # Audit trail
    events: List[Dict] = field(default_factory=list)

    def add_event(self, event_type: str, agent: str, details: Dict[str, Any]):
        """Add event to proposal audit trail"""
        self.events.append({
            "timestamp": datetime.now().isoformat(),
            "type": event_type,
            "agent": agent,
            "details": details
        })


class PhiArchitect:
    """
    Φ-Architect: Proposes changes, cannot commit.

    Role: Sanitize external requests and create formal proposals.
    Capabilities: propose, sanitize, ingest
    Cannot: approve, execute, commit

    Token Dependencies: T05 (Identity)
    """

    def __init__(self, governance_engine: GovernanceEngine):
        self.engine = governance_engine
        self.agent_id = "Φ-Architect"
        self.proposals_created = 0

    def propose(self, request: Dict[str, Any]) -> Optional[Proposal]:
        """
        Create a formal proposal from a request.

        Args:
            request: External request with action and data

        Returns:
            Proposal object or None if validation fails
        """
        # Validate T05 (Identity)
        if not self.engine.token_system:
            logger.error("Token system not available")
            return None

        t05 = self.engine.token_system.get_token("T05")
        if not t05 or t05.state != TokenState.ACTIVE:
            logger.error("T05 (Identity) not active - cannot identify proposer")
            return None

        # Check system mode
        if self.engine.system_mode != SystemMode.RUN:
            logger.warning(f"System in {self.engine.system_mode.value} - proposals blocked")
            return None

        # Sanitize and validate request
        sanitized = self._sanitize_request(request)
        if not sanitized:
            logger.error("Request sanitization failed")
            return None

        # Create proposal
        self.proposals_created += 1
        proposal = Proposal(
            id=f"P-{self.proposals_created:06d}",
            timestamp=datetime.now().isoformat(),
            proposer=self.agent_id,
            action=sanitized["action"],
            payload=sanitized.get("payload", {}),
            justification=sanitized.get("justification", "No justification provided"),
            status=ProposalStatus.PROPOSED
        )

        proposal.add_event("PROPOSED", self.agent_id, {
            "action": proposal.action,
            "payload_hash": self._hash_payload(proposal.payload)
        })

        logger.info(f"{self.agent_id} created proposal {proposal.id}")
        return proposal

    def _sanitize_request(self, request: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """Sanitize external request"""
        if not request:
            return None

        # Require action field
        if "action" not in request:
            logger.error("Request missing 'action' field")
            return None

        return {
            "action": request["action"],
            "payload": request.get("data", request.get("payload", {})),
            "justification": request.get("justification", request.get("reason", ""))
        }

    def _hash_payload(self, payload: Dict) -> str:
        """Hash payload for audit trail"""
        payload_str = json.dumps(payload, sort_keys=True)
        return hashlib.sha256(payload_str.encode()).hexdigest()[:16]


class AgentA2:
    """
    A2: Formal/Structural Approver

    Role: Verify structural invariants, NAND-only compliance, TLA+ consistency.
    Capabilities: verify_structure, gate, veto
    Cannot: propose, execute

    Token Dependencies: T09 (Standardize), T06 (Security)
    """

    def __init__(self, governance_engine: GovernanceEngine):
        self.engine = governance_engine
        self.agent_id = "A2-Formal-Verifier"
        self.verdicts_issued = 0

    def verify(self, proposal: Proposal) -> Dict[str, Any]:
        """
        Verify proposal against formal invariants.

        Checks:
        1. Structural validity
        2. NAND-only compliance (via T09)
        3. TLA+ invariants (simplified)
        4. Security constraints (via T06)

        Args:
            proposal: Proposal to verify

        Returns:
            Verdict dictionary
        """
        proposal.status = ProposalStatus.A2_REVIEW
        proposal.add_event("A2_REVIEW_STARTED", self.agent_id, {})

        verdict = {
            "agent": self.agent_id,
            "proposal_id": proposal.id,
            "timestamp": datetime.now().isoformat(),
            "approved": False,
            "checks": {},
            "violations": []
        }

        # Check 1: Structural validity
        structural_check = self._check_structure(proposal)
        verdict["checks"]["structure"] = structural_check
        if not structural_check["passed"]:
            verdict["violations"].append(structural_check["reason"])

        # Check 2: NAND-only compliance (T09)
        nand_check = self._check_nand_compliance(proposal)
        verdict["checks"]["nand_only"] = nand_check
        if not nand_check["passed"]:
            verdict["violations"].append(nand_check["reason"])

        # Check 3: TLA+ invariants
        invariant_check = self._check_invariants(proposal)
        verdict["checks"]["invariants"] = invariant_check
        if not invariant_check["passed"]:
            verdict["violations"].append(invariant_check["reason"])

        # Check 4: Security (T06)
        security_check = self._check_security(proposal)
        verdict["checks"]["security"] = security_check
        if not security_check["passed"]:
            verdict["violations"].append(security_check["reason"])

        # Final verdict
        verdict["approved"] = len(verdict["violations"]) == 0

        # Update proposal
        proposal.a2_approved = verdict["approved"]
        proposal.a2_verdict = verdict

        if verdict["approved"]:
            proposal.status = ProposalStatus.A2_APPROVED
            proposal.add_event("A2_APPROVED", self.agent_id, verdict)
            logger.info(f"{self.agent_id} APPROVED proposal {proposal.id}")
        else:
            proposal.status = ProposalStatus.A2_REJECTED
            proposal.add_event("A2_REJECTED", self.agent_id, verdict)
            logger.warning(f"{self.agent_id} REJECTED proposal {proposal.id}: {verdict['violations']}")

        self.verdicts_issued += 1
        return verdict

    def _check_structure(self, proposal: Proposal) -> Dict[str, Any]:
        """Verify structural validity"""
        required_fields = ["id", "action", "payload", "justification"]

        for field in required_fields:
            if not hasattr(proposal, field) or getattr(proposal, field) is None:
                return {
                    "passed": False,
                    "reason": f"Missing required field: {field}"
                }

        return {"passed": True, "reason": "Structure valid"}

    def _check_nand_compliance(self, proposal: Proposal) -> Dict[str, Any]:
        """Check NAND-only compliance (T09)"""
        if not self.engine.token_system:
            return {"passed": False, "reason": "Token system not available"}

        t09 = self.engine.token_system.get_token("T09")
        if not t09 or t09.state != TokenState.ACTIVE:
            return {"passed": False, "reason": "T09 (Standardize) not active"}

        # Simplified: check if action is in allowed set
        # Full implementation would validate via NAND-IR
        allowed_actions = {"add_user", "update_data", "delete_record", "query"}

        if proposal.action not in allowed_actions:
            return {
                "passed": False,
                "reason": f"Action '{proposal.action}' not in NAND-verified set"
            }

        return {"passed": True, "reason": "NAND-only compliant"}

    def _check_invariants(self, proposal: Proposal) -> Dict[str, Any]:
        """Check TLA+ invariants"""
        # Simplified: would check against actual TLA+ model
        # For now, just verify basic invariants

        # AppendOnlyMonotone: proposals are append-only
        if proposal.id in [p.id for p in self.engine.proposals]:
            return {
                "passed": False,
                "reason": "Duplicate proposal ID violates AppendOnlyMonotone"
            }

        return {"passed": True, "reason": "Invariants satisfied"}

    def _check_security(self, proposal: Proposal) -> Dict[str, Any]:
        """Check security constraints (T06)"""
        if not self.engine.token_system:
            return {"passed": False, "reason": "Token system not available"}

        t06 = self.engine.token_system.get_token("T06")
        if not t06 or t06.state != TokenState.ACTIVE:
            return {"passed": False, "reason": "T06 (Security) not active"}

        # Check for security-sensitive actions
        sensitive_actions = {"delete_record", "modify_permissions"}

        if proposal.action in sensitive_actions:
            # Require additional security justification
            if "security_clearance" not in proposal.payload:
                return {
                    "passed": False,
                    "reason": "Sensitive action requires security_clearance"
                }

        return {"passed": True, "reason": "Security checks passed"}


class AgentA1:
    """
    A1: Substantive/Ethical Approver

    Role: Verify ethical compliance, DIA preservation, epistemic justice.
    Sub-agents:
        - A1-א (Aleph): Evidence validation (T01)
        - A1-ד (Dalet): DIA check (T10)
        - A1-ס (Samekh): Ethical Guardian (T13)

    Token Dependencies: T13 (Rights), T10 (Measure), T01 (Data)
    """

    def __init__(self, governance_engine: GovernanceEngine):
        self.engine = governance_engine
        self.agent_id = "A1-Substantive-Approver"
        self.verdicts_issued = 0

    def review(self, proposal: Proposal) -> Dict[str, Any]:
        """
        Review proposal for ethical and substantive compliance.

        Sub-agent checks:
        1. A1-א: Evidence validation
        2. A1-ד: DIA impact check
        3. A1-ס: Ethical review

        Args:
            proposal: Proposal to review

        Returns:
            Verdict dictionary
        """
        proposal.status = ProposalStatus.A1_REVIEW
        proposal.add_event("A1_REVIEW_STARTED", self.agent_id, {})

        verdict = {
            "agent": self.agent_id,
            "proposal_id": proposal.id,
            "timestamp": datetime.now().isoformat(),
            "approved": False,
            "sub_agents": {},
            "violations": []
        }

        # A1-א: Evidence validation (T01)
        evidence_check = self._check_evidence(proposal)
        verdict["sub_agents"]["A1-א"] = evidence_check
        if not evidence_check["passed"]:
            verdict["violations"].append(evidence_check["reason"])

        # A1-ד: DIA impact (T10)
        dia_check = self._check_dia_impact(proposal)
        verdict["sub_agents"]["A1-ד"] = dia_check
        if not dia_check["passed"]:
            verdict["violations"].append(dia_check["reason"])
            # DIA violations are critical
            if dia_check.get("critical", False):
                self.engine._trigger_safe_mode("DIA violation detected")

        # A1-ס: Ethical review (T13)
        ethical_check = self._check_ethics(proposal)
        verdict["sub_agents"]["A1-ס"] = ethical_check
        if not ethical_check["passed"]:
            verdict["violations"].append(ethical_check["reason"])
            # Ethical violations trigger T15
            if ethical_check.get("severity") == "high":
                self.engine._trigger_hold_mode("Ethical violation - T13")

        # Final verdict
        verdict["approved"] = len(verdict["violations"]) == 0

        # Update proposal
        proposal.a1_approved = verdict["approved"]
        proposal.a1_verdict = verdict

        if verdict["approved"]:
            proposal.status = ProposalStatus.A1_APPROVED
            proposal.add_event("A1_APPROVED", self.agent_id, verdict)
            logger.info(f"{self.agent_id} APPROVED proposal {proposal.id}")
        else:
            proposal.status = ProposalStatus.A1_REJECTED
            proposal.add_event("A1_REJECTED", self.agent_id, verdict)
            logger.warning(f"{self.agent_id} REJECTED proposal {proposal.id}: {verdict['violations']}")

        self.verdicts_issued += 1
        return verdict

    def _check_evidence(self, proposal: Proposal) -> Dict[str, Any]:
        """A1-א: Validate evidence (T01)"""
        if not self.engine.token_system:
            return {"passed": False, "reason": "Token system not available"}

        t01 = self.engine.token_system.get_token("T01")
        if not t01 or t01.state != TokenState.ACTIVE:
            return {"passed": False, "reason": "T01 (Data) not active"}

        # Check if proposal has evidence/data source
        has_evidence = (
            "evidence" in proposal.payload or
            "data_source" in proposal.payload or
            "reference" in proposal.payload
        )

        if not has_evidence:
            return {
                "passed": False,
                "reason": "Missing evidence/data source (A1-א)",
                "sub_agent": "A1-א"
            }

        return {
            "passed": True,
            "reason": "Evidence validated (A1-א)",
            "sub_agent": "A1-א"
        }

    def _check_dia_impact(self, proposal: Proposal) -> Dict[str, Any]:
        """A1-ד: Check DIA impact (T10)"""
        if not self.engine.token_system:
            return {"passed": False, "reason": "Token system not available"}

        t10 = self.engine.token_system.get_token("T10")
        if not t10 or t10.state != TokenState.ACTIVE:
            return {"passed": False, "reason": "T10 (Measure) not active"}

        # Simulate DIA impact
        # Full implementation would compute actual DIA change
        action_type = proposal.action

        # Actions that decrease DIA
        dia_decreasing_actions = {"delete_record", "remove_evidence"}

        if action_type in dia_decreasing_actions:
            return {
                "passed": False,
                "reason": "Action would violate DIA monotonicity (A1-ד)",
                "sub_agent": "A1-ד",
                "critical": True
            }

        return {
            "passed": True,
            "reason": "DIA monotonicity preserved (A1-ד)",
            "sub_agent": "A1-ד"
        }

    def _check_ethics(self, proposal: Proposal) -> Dict[str, Any]:
        """A1-ס: Ethical review (T13)"""
        if not self.engine.token_system:
            return {"passed": False, "reason": "Token system not available"}

        t13 = self.engine.token_system.get_token("T13")
        if not t13 or t13.state != TokenState.ACTIVE:
            return {
                "passed": False,
                "reason": "T13 (Rights) not active - CRITICAL",
                "severity": "high",
                "sub_agent": "A1-ס"
            }

        # Check for ethical red flags
        payload = proposal.payload

        ethical_violations = []

        if payload.get("violates_privacy", False):
            ethical_violations.append("Privacy violation")

        if payload.get("violates_consent", False):
            ethical_violations.append("Consent violation")

        if payload.get("discriminatory", False):
            ethical_violations.append("Discriminatory action")

        if payload.get("bypasses_rights", False):
            ethical_violations.append("Rights bypass attempt")

        if ethical_violations:
            return {
                "passed": False,
                "reason": f"Ethical violations: {', '.join(ethical_violations)} (A1-ס)",
                "severity": "high",
                "sub_agent": "A1-ס",
                "violations": ethical_violations
            }

        return {
            "passed": True,
            "reason": "No ethical violations (A1-ס)",
            "sub_agent": "A1-ס"
        }


class B1Actuator:
    """
    B1: Actuator

    Role: Execute approved proposals and commit to ledger.
    Capabilities: execute, commit_to_ledger
    Cannot: propose, approve

    Token Dependencies: T07 (Automation), T04 (Storage)
    """

    def __init__(self, governance_engine: GovernanceEngine):
        self.engine = governance_engine
        self.agent_id = "B1-Actuator"
        self.executions = 0

    def execute(self, proposal: Proposal) -> Dict[str, Any]:
        """
        Execute approved proposal.

        Requires:
        - A2 approved
        - A1 approved
        - System in RUN mode
        - T07 (Automation) active

        Args:
            proposal: Approved proposal

        Returns:
            Execution result
        """
        result = {
            "agent": self.agent_id,
            "proposal_id": proposal.id,
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "commitment_id": None,
            "error": None
        }

        # Verify approvals
        if not (proposal.a2_approved and proposal.a1_approved):
            result["error"] = "Proposal not fully approved (A2 and A1 required)"
            logger.error(f"{self.agent_id}: Cannot execute {proposal.id} - not approved")
            return result

        # Check system mode
        if self.engine.system_mode != SystemMode.RUN:
            result["error"] = f"System in {self.engine.system_mode.value} - execution blocked"
            logger.error(f"{self.agent_id}: Cannot execute - system not in RUN mode")
            return result

        # Check T07 (Automation)
        if not self.engine.token_system:
            result["error"] = "Token system not available"
            return result

        t07 = self.engine.token_system.get_token("T07")
        if not t07 or t07.state != TokenState.ACTIVE:
            result["error"] = "T07 (Automation) not active"
            logger.error(f"{self.agent_id}: T07 not active - cannot execute")
            return result

        # Execute
        proposal.status = ProposalStatus.EXECUTING
        proposal.add_event("EXECUTION_STARTED", self.agent_id, {})

        try:
            # Actual execution logic would go here
            # For now, simulate successful execution
            self.executions += 1
            commitment_id = f"C-{self.executions:06d}"

            # Commit to ledger (via T04 Storage)
            ledger_success = self._commit_to_ledger(proposal, commitment_id)

            if not ledger_success:
                raise RuntimeError("Ledger commit failed")

            # Mark as committed
            proposal.status = ProposalStatus.COMMITTED
            proposal.commitment_id = commitment_id
            proposal.executed_at = datetime.now().isoformat()
            proposal.add_event("COMMITTED", self.agent_id, {
                "commitment_id": commitment_id
            })

            result["success"] = True
            result["commitment_id"] = commitment_id

            logger.info(f"{self.agent_id} executed proposal {proposal.id} -> {commitment_id}")

        except Exception as e:
            proposal.status = ProposalStatus.FAILED
            proposal.add_event("EXECUTION_FAILED", self.agent_id, {"error": str(e)})
            result["error"] = str(e)
            logger.error(f"{self.agent_id} execution failed: {e}")

        return result

    def _commit_to_ledger(self, proposal: Proposal, commitment_id: str) -> bool:
        """Commit to ledger via T04"""
        if not self.engine.token_system:
            return False

        t04 = self.engine.token_system.get_token("T04")
        if not t04 or t04.state != TokenState.ACTIVE:
            logger.error("T04 (Storage) not active - cannot commit to ledger")
            return False

        # Create ledger event
        event = {
            "id": commitment_id,
            "type": "COMMITMENT",
            "timestamp": datetime.now().isoformat(),
            "proposal_id": proposal.id,
            "action": proposal.action,
            "payload": proposal.payload,
            "justification": proposal.justification,
            "approvals": {
                "A2": proposal.a2_approved,
                "A1": proposal.a1_approved
            }
        }

        # Append to engine's ledger
        self.engine.ledger.append(event)
        logger.debug(f"Committed {commitment_id} to ledger")

        return True


class B2SafetyMonitor:
    """
    B2: Safety Monitor

    Role: Continuous monitoring and safety enforcement.
    Capabilities: monitor, trigger_hold, veto_after_commit
    Cannot: propose, approve, execute

    Token Dependencies: T11 (Monitor), T06 (Security), T15 (Seriousness)
    """

    def __init__(self, governance_engine: GovernanceEngine):
        self.engine = governance_engine
        self.agent_id = "B2-Safety-Monitor"
        self.alerts = []

    def monitor(self, proposal: Proposal, execution_result: Dict[str, Any]) -> Dict[str, Any]:
        """
        Monitor execution and trigger safety responses if needed.

        Args:
            proposal: Executed proposal
            execution_result: Result from B1

        Returns:
            Monitoring result
        """
        if not self.engine.token_system:
            return {"error": "Token system not available"}

        t11 = self.engine.token_system.get_token("T11")
        if not t11 or t11.state != TokenState.ACTIVE:
            logger.warning("T11 (Monitor) not active - limited monitoring")

        monitor_result = {
            "agent": self.agent_id,
            "proposal_id": proposal.id,
            "timestamp": datetime.now().isoformat(),
            "status": "monitoring",
            "alerts": []
        }

        # Check for anomalies
        if not execution_result.get("success", False):
            alert = {
                "severity": "high",
                "type": "execution_failure",
                "message": f"Execution failed: {execution_result.get('error')}",
                "timestamp": datetime.now().isoformat()
            }
            monitor_result["alerts"].append(alert)
            self.alerts.append(alert)

            # Trigger safety response
            self._trigger_safety_response("execution_failure", alert)

        # Check DIA after execution
        dia_check = self._check_post_execution_dia()
        if not dia_check["monotonic"]:
            alert = {
                "severity": "critical",
                "type": "dia_violation",
                "message": "DIA monotonicity violated post-execution",
                "timestamp": datetime.now().isoformat()
            }
            monitor_result["alerts"].append(alert)
            self.alerts.append(alert)

            # DIA violation triggers SAFE mode
            self.engine._trigger_safe_mode("DIA violation detected by B2")

        monitor_result["status"] = "complete"
        logger.info(f"{self.agent_id} monitored {proposal.id}: {len(monitor_result['alerts'])} alerts")

        return monitor_result

    def _check_post_execution_dia(self) -> Dict[str, bool]:
        """Check DIA monotonicity after execution"""
        # Simplified: would actually compute DIA from ledger
        # For now, assume monotonic unless explicitly violated
        return {"monotonic": True}

    def _trigger_safety_response(self, trigger_type: str, alert: Dict):
        """Trigger appropriate safety response"""
        severity = alert.get("severity", "low")

        if severity == "critical":
            # Critical: activate T15 and enter HOLD
            self.engine._trigger_hold_mode(f"Critical alert: {alert['message']}")
        elif severity == "high":
            # High: enter SAFE mode
            self.engine._trigger_safe_mode(f"High severity alert: {alert['message']}")
        else:
            # Low/medium: log only
            logger.warning(f"{self.agent_id} safety alert: {alert['message']}")


class GovernanceEngine:
    """
    Main Governance Engine

    Orchestrates the complete multi-agent workflow:
    Φ-Architect → A2 → A1 → B1 → B2

    Maintains:
    - System state (RUN/HOLD/SAFE)
    - Proposal registry
    - Ledger
    - Audit trail
    """

    def __init__(self, token_system=None, ledger_path: Optional[Path] = None):
        """
        Initialize governance engine.

        Args:
            token_system: Optional HebrewTokenSystem instance
            ledger_path: Optional path to ledger file
        """
        self.token_system = token_system
        self.ledger_path = ledger_path

        # System state
        self.system_mode = SystemMode.RUN
        self.mode_history = []

        # Data structures
        self.proposals: List[Proposal] = []
        self.ledger: List[Dict] = []

        # Initialize agents
        self.phi_architect = PhiArchitect(self)
        self.agent_a2 = AgentA2(self)
        self.agent_a1 = AgentA1(self)
        self.b1_actuator = B1Actuator(self)
        self.b2_monitor = B2SafetyMonitor(self)

        logger.info("GovernanceEngine initialized")

    def process_request(self, request: Dict[str, Any]) -> Dict[str, Any]:
        """
        Process a request through the complete governance workflow.

        Workflow:
        1. Φ-Architect proposes
        2. A2 verifies (formal)
        3. A1 reviews (ethical)
        4. B1 executes
        5. B2 monitors

        Args:
            request: External request

        Returns:
            Complete result with audit trail
        """
        result = {
            "request": request,
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "proposal_id": None,
            "commitment_id": None,
            "audit_trail": [],
            "system_mode": self.system_mode.value
        }

        try:
            # Stage 1: Φ-Architect proposes
            logger.info("Stage 1: Φ-Architect proposing")
            proposal = self.phi_architect.propose(request)

            if not proposal:
                result["error"] = "Proposal creation failed"
                result["audit_trail"].append("Φ-Architect: Proposal creation failed")
                return result

            result["proposal_id"] = proposal.id
            result["audit_trail"].append(f"Φ-Architect: Created proposal {proposal.id}")

            # Stage 2: A2 verifies (before adding to proposals list to check for duplicates)
            logger.info(f"Stage 2: A2 verifying {proposal.id}")
            a2_verdict = self.agent_a2.verify(proposal)
            result["audit_trail"].append(
                f"A2: {'APPROVED' if a2_verdict['approved'] else 'REJECTED'}"
            )

            if not a2_verdict["approved"]:
                result["error"] = "A2 rejected"
                result["reasons"] = a2_verdict["violations"]
                result["audit_trail"].append(f"A2: Violations - {a2_verdict['violations']}")
                return result

            # Stage 3: A1 reviews
            logger.info(f"Stage 3: A1 reviewing {proposal.id}")
            a1_verdict = self.agent_a1.review(proposal)
            result["audit_trail"].append(
                f"A1: {'APPROVED' if a1_verdict['approved'] else 'REJECTED'}"
            )

            if not a1_verdict["approved"]:
                result["error"] = "A1 rejected"
                result["reasons"] = a1_verdict["violations"]
                result["audit_trail"].append(f"A1: Violations - {a1_verdict['violations']}")
                return result

            # Mark as ready for execution
            proposal.status = ProposalStatus.READY_FOR_EXECUTION
            result["audit_trail"].append("Proposal APPROVED by A2 and A1")

            # Now add to proposals list after all approvals
            self.proposals.append(proposal)

            # Stage 4: B1 executes
            logger.info(f"Stage 4: B1 executing {proposal.id}")
            execution_result = self.b1_actuator.execute(proposal)
            result["audit_trail"].append(
                f"B1: {'SUCCESS' if execution_result['success'] else 'FAILED'}"
            )

            if not execution_result["success"]:
                result["error"] = "Execution failed"
                result["execution_error"] = execution_result["error"]
                result["audit_trail"].append(f"B1: Error - {execution_result['error']}")
                return result

            result["commitment_id"] = execution_result["commitment_id"]
            result["audit_trail"].append(f"B1: Committed as {result['commitment_id']}")

            # Stage 5: B2 monitors
            logger.info(f"Stage 5: B2 monitoring {proposal.id}")
            monitor_result = self.b2_monitor.monitor(proposal, execution_result)
            result["audit_trail"].append(
                f"B2: Monitored - {len(monitor_result.get('alerts', []))} alerts"
            )

            if monitor_result.get("alerts"):
                result["safety_alerts"] = monitor_result["alerts"]

            # Success!
            result["success"] = True
            result["system_mode"] = self.system_mode.value

            logger.info(f"Request completed successfully: {result['commitment_id']}")

        except Exception as e:
            logger.error(f"Request processing failed: {e}")
            result["error"] = str(e)
            result["audit_trail"].append(f"ERROR: {e}")

            # Trigger safety response
            self._trigger_safe_mode(f"Unhandled exception: {e}")

        return result

    def _trigger_hold_mode(self, reason: str):
        """Transition to HOLD mode (T15 activated)"""
        if self.system_mode == SystemMode.HOLD:
            return

        previous_mode = self.system_mode
        self.system_mode = SystemMode.HOLD

        self.mode_history.append({
            "from": previous_mode.value,
            "to": SystemMode.HOLD.value,
            "reason": reason,
            "timestamp": datetime.now().isoformat()
        })

        # Activate T15
        if self.token_system:
            t15 = self.token_system.get_token("T15")
            if t15:
                # Would call t15.activate_emergency(reason)
                pass

        logger.critical(f"SYSTEM ENTERED HOLD MODE: {reason}")

    def _trigger_safe_mode(self, reason: str):
        """Transition to SAFE mode"""
        if self.system_mode in [SystemMode.HOLD, SystemMode.SAFE]:
            return

        previous_mode = self.system_mode
        self.system_mode = SystemMode.SAFE

        self.mode_history.append({
            "from": previous_mode.value,
            "to": SystemMode.SAFE.value,
            "reason": reason,
            "timestamp": datetime.now().isoformat()
        })

        logger.warning(f"SYSTEM ENTERED SAFE MODE: {reason}")

    def get_system_status(self) -> Dict[str, Any]:
        """Get complete system status"""
        return {
            "system_mode": self.system_mode.value,
            "proposals": {
                "total": len(self.proposals),
                "proposed": len([p for p in self.proposals if p.status == ProposalStatus.PROPOSED]),
                "approved": len([p for p in self.proposals if p.status in [ProposalStatus.A1_APPROVED, ProposalStatus.READY_FOR_EXECUTION]]),
                "committed": len([p for p in self.proposals if p.status == ProposalStatus.COMMITTED]),
                "rejected": len([p for p in self.proposals if p.status in [ProposalStatus.A1_REJECTED, ProposalStatus.A2_REJECTED]]),
                "failed": len([p for p in self.proposals if p.status == ProposalStatus.FAILED])
            },
            "ledger_size": len(self.ledger),
            "mode_history": len(self.mode_history),
            "safety_alerts": len(self.b2_monitor.alerts)
        }
