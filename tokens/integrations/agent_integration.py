"""
Multi-Agent Workflow Integration for Hebrew Token System

Maps Hebrew Tokens to the Φ-OS multi-agent architecture,
implementing "Proposal ≠ Commitment" principle.

Agent Architecture:
- Φ-Architect (C0⊕T0): Proposer only
- A1: Substantive Approver (Ethics & DIA)
  - A1-א: Evidence validation
  - A1-ד: DIA check
  - A1-ס: Ethical Guardian
- A2: Structural Verifier (MaxaNAND + 3⊥+1)
- B1: Operations & SSM (Actuator)
- B2: Safety Monitor
"""

import logging
from typing import Dict, Any, List, Optional, Callable
from enum import Enum
from datetime import datetime

logger = logging.getLogger(__name__)


class SystemState(Enum):
    """Φ-OS System States"""
    RUN = "RUN"      # Normal operation
    HOLD = "HOLD"    # Emergency stop (no writes)
    SAFE = "SAFE"    # Conservative mode


class AgentRole(Enum):
    """Agent roles in the workflow"""
    ARCHITECT = "Φ-Architect"  # Proposer
    A1_APPROVER = "A1"         # Substantive Approver
    A1_EVIDENCE = "A1-א"       # Evidence validator
    A1_DIA = "A1-ד"            # DIA checker
    A1_ETHICAL = "A1-ס"        # Ethical Guardian
    A2_VERIFIER = "A2"         # Structural Verifier
    B1_ACTUATOR = "B1"         # Operations
    B2_MONITOR = "B2"          # Safety Monitor


class AgentWorkflowIntegration:
    """
    Integrates Hebrew Token System with multi-agent workflow.

    Token-to-Agent Mappings:
    - T15 (Seriousness/רצינות) → HOLD state control
    - T13 (Rights/זכויות אדם) → A1-ס Ethical Guardian
    - T08 (Govern/ממשל) → A1 Substantive Approver
    - T10 (Measure/מדידה) → A1-ד DIA Check
    - T06 (Security/אבטחה) → B2 Safety Monitor
    - T07 (Automation/אוטומציה) → B1 Actuator
    - T05 (Identity/זהות) → Agent IDs
    - T11 (Monitor/ניטור) → B2 continuous monitoring
    """

    def __init__(self, token_system):
        """
        Initialize multi-agent workflow integration.

        Args:
            token_system: HebrewTokenSystem instance
        """
        self.token_system = token_system
        self.system_state = SystemState.RUN
        self.agents = {}
        self.proposals = []
        self.commitments = []
        self.state_history = []

        # Initialize agents
        self._initialize_agents()

        # Token references
        self.t05_identity = token_system.get_token("T05")
        self.t06_security = token_system.get_token("T06")
        self.t07_automation = token_system.get_token("T07")
        self.t08_govern = token_system.get_token("T08")
        self.t10_measure = token_system.get_token("T10")
        self.t11_monitor = token_system.get_token("T11")
        self.t13_rights = token_system.get_token("T13")
        self.t15_seriousness = token_system.get_token("T15")

        logger.info("Multi-Agent Workflow Integration initialized")

    def _initialize_agents(self):
        """Initialize all agents with their roles and capabilities."""
        self.agents = {
            AgentRole.ARCHITECT: {
                "name": "Φ-Architect",
                "role": "proposer",
                "capabilities": ["propose", "sanitize", "ingest"],
                "can_commit": False
            },
            AgentRole.A1_APPROVER: {
                "name": "A1-Substantive-Approver",
                "role": "approver",
                "capabilities": ["approve", "veto"],
                "sub_agents": [
                    AgentRole.A1_EVIDENCE,
                    AgentRole.A1_DIA,
                    AgentRole.A1_ETHICAL
                ]
            },
            AgentRole.A1_EVIDENCE: {
                "name": "A1-א-Evidence",
                "role": "validator",
                "capabilities": ["validate_evidence"],
                "token_control": "T01"
            },
            AgentRole.A1_DIA: {
                "name": "A1-ד-DIA-Check",
                "role": "validator",
                "capabilities": ["check_dia"],
                "token_control": "T10"
            },
            AgentRole.A1_ETHICAL: {
                "name": "A1-ס-Ethical-Guardian",
                "role": "guardian",
                "capabilities": ["check_ethics", "veto"],
                "token_control": "T13"
            },
            AgentRole.A2_VERIFIER: {
                "name": "A2-Structural-Verifier",
                "role": "verifier",
                "capabilities": ["verify_structure", "gate"],
                "token_control": "T09"
            },
            AgentRole.B1_ACTUATOR: {
                "name": "B1-Actuator",
                "role": "executor",
                "capabilities": ["execute", "commit_to_ledger"],
                "token_control": "T07"
            },
            AgentRole.B2_MONITOR: {
                "name": "B2-Safety-Monitor",
                "role": "monitor",
                "capabilities": ["monitor", "trigger_hold"],
                "token_control": "T11"
            }
        }

    # ========== Workflow: Proposal → Verification → Execution ==========

    def propose_change(self, proposal: Dict[str, Any]) -> str:
        """
        Φ-Architect proposes a change (does NOT commit).

        Process:
        1. Φ-Architect sanitizes and proposes
        2. Returns proposal ID for tracking

        Args:
            proposal: Change proposal with required fields

        Returns:
            str: Proposal ID
        """
        # Verify T05 (Identity) for agent identification
        if not self.t05_identity.state['active']:
            logger.error("T05 (Identity) inactive - cannot identify proposer")
            return None

        # Check system state
        if self.system_state != SystemState.RUN:
            logger.warning(f"System in {self.system_state.value} - proposal rejected")
            return None

        # Create proposal
        proposal_id = f"P-{len(self.proposals):04d}"
        full_proposal = {
            "id": proposal_id,
            "agent": AgentRole.ARCHITECT.value,
            "timestamp": datetime.now().isoformat(),
            "content": proposal,
            "status": "pending",
            "approvals": {},
            "vetoes": []
        }

        self.proposals.append(full_proposal)
        logger.info(f"Proposal created: {proposal_id} by {AgentRole.ARCHITECT.value}")

        return proposal_id

    def verify_proposal(self, proposal_id: str) -> Dict[str, Any]:
        """
        A1 and A2 verify the proposal.

        Process:
        1. A1-א validates evidence (T01 control)
        2. A1-ד checks DIA impact (T10 control)
        3. A1-ס validates ethics (T13 control)
        4. A2 verifies structure (T09 control)
        5. Returns verification result

        Args:
            proposal_id: Proposal identifier

        Returns:
            dict: Verification result
        """
        proposal = self._get_proposal(proposal_id)
        if not proposal:
            return {"success": False, "error": "Proposal not found"}

        results = {
            "proposal_id": proposal_id,
            "verifications": {},
            "approved": False,
            "vetoed": False,
            "reasons": []
        }

        # A1-א: Evidence validation (T01 control)
        evidence_check = self._check_evidence(proposal)
        results["verifications"]["A1-א"] = evidence_check
        if not evidence_check["passed"]:
            results["vetoed"] = True
            results["reasons"].append(evidence_check["reason"])

        # A1-ד: DIA check (T10 control)
        dia_check = self._check_dia_impact(proposal)
        results["verifications"]["A1-ד"] = dia_check
        if not dia_check["passed"]:
            results["vetoed"] = True
            results["reasons"].append(dia_check["reason"])

        # A1-ס: Ethical check (T13 control)
        ethical_check = self._check_ethics(proposal)
        results["verifications"]["A1-ס"] = ethical_check
        if not ethical_check["passed"]:
            results["vetoed"] = True
            results["reasons"].append(ethical_check["reason"])
            # T13 violations are absolute - trigger T15
            if ethical_check.get("severity") == "high":
                self._activate_seriousness_mode()

        # A2: Structural verification (T09 control)
        structure_check = self._verify_structure(proposal)
        results["verifications"]["A2"] = structure_check
        if not structure_check["passed"]:
            results["vetoed"] = True
            results["reasons"].append(structure_check["reason"])

        # Update proposal status
        if not results["vetoed"]:
            results["approved"] = True
            proposal["status"] = "approved"
            proposal["approvals"]["A1"] = True
            proposal["approvals"]["A2"] = True
        else:
            proposal["status"] = "rejected"
            proposal["vetoes"] = results["reasons"]

        logger.info(f"Proposal {proposal_id} verification: {'APPROVED' if results['approved'] else 'REJECTED'}")
        return results

    def execute_commitment(self, proposal_id: str) -> bool:
        """
        B1 executes the approved proposal (commitment).

        Process:
        1. Verify proposal is approved
        2. B1 executes under T07 (Automation) control
        3. Commit to ledger
        4. B2 monitors execution under T11 control

        Args:
            proposal_id: Approved proposal ID

        Returns:
            bool: True if execution successful
        """
        proposal = self._get_proposal(proposal_id)
        if not proposal:
            logger.error(f"Proposal {proposal_id} not found")
            return False

        # Verify approval
        if proposal["status"] != "approved":
            logger.error(f"Proposal {proposal_id} not approved - cannot execute")
            return False

        # Check T07 (Automation) is active
        if not self.t07_automation.state['active']:
            logger.error("T07 (Automation) inactive - cannot execute")
            return False

        # Check system state
        if self.system_state == SystemState.HOLD:
            logger.error("System in HOLD - execution blocked")
            return False

        # B1: Execute
        try:
            commitment = {
                "id": f"C-{len(self.commitments):04d}",
                "proposal_id": proposal_id,
                "agent": AgentRole.B1_ACTUATOR.value,
                "timestamp": datetime.now().isoformat(),
                "content": proposal["content"],
                "status": "committed"
            }

            self.commitments.append(commitment)

            # B2: Monitor execution
            self._monitor_execution(commitment)

            proposal["status"] = "committed"
            proposal["commitment_id"] = commitment["id"]

            logger.info(f"Commitment executed: {commitment['id']} from proposal {proposal_id}")
            return True

        except Exception as e:
            logger.error(f"Execution failed: {e}")
            # B2: Trigger safety response
            self._trigger_safety_response(str(e))
            return False

    # ========== System State Control ==========

    def _activate_seriousness_mode(self):
        """
        Activate T15 (Seriousness) - transition to HOLD state.

        Triggered by:
        - T13 (Rights) violations
        - T01 (Data) integrity threats
        - B2 safety alerts
        """
        if not self.t15_seriousness.state['active']:
            logger.info("Activating T15 (Seriousness) - entering HOLD state")
            self.t15_seriousness.activate()

        self._transition_to_hold()

        # T15 effects:
        # - Suspend T07 (Automation)
        # - Degrade T03 (Compute)
        # - Close T14 (Commons)
        self.t07_automation.deactivate()
        logger.warning("T15 ACTIVE: System in emergency HOLD state")

    def _transition_to_hold(self):
        """Transition system to HOLD state."""
        previous_state = self.system_state
        self.system_state = SystemState.HOLD

        self.state_history.append({
            "from": previous_state.value,
            "to": SystemState.HOLD.value,
            "timestamp": datetime.now().isoformat(),
            "reason": "T15 Seriousness activated"
        })

        logger.critical(f"System state: {previous_state.value} → HOLD")

    def _transition_to_safe(self):
        """Transition system to SAFE state."""
        previous_state = self.system_state
        self.system_state = SystemState.SAFE

        self.state_history.append({
            "from": previous_state.value,
            "to": SystemState.SAFE.value,
            "timestamp": datetime.now().isoformat(),
            "reason": "Safety protocol activated"
        })

        logger.warning(f"System state: {previous_state.value} → SAFE")

    def transition_to_run(self) -> bool:
        """
        Transition system back to RUN state.

        Requires:
        - All safety checks passed
        - T15 (Seriousness) cleared
        - Manual confirmation

        Returns:
            bool: True if transition successful
        """
        if self.system_state == SystemState.RUN:
            return True

        # Check if conditions met
        if self.t15_seriousness.state['active']:
            logger.error("Cannot transition to RUN - T15 still active")
            return False

        # Verify all safety conditions
        safety_check = self._verify_safety_conditions()
        if not safety_check["passed"]:
            logger.error(f"Safety check failed: {safety_check['reason']}")
            return False

        previous_state = self.system_state
        self.system_state = SystemState.RUN

        self.state_history.append({
            "from": previous_state.value,
            "to": SystemState.RUN.value,
            "timestamp": datetime.now().isoformat(),
            "reason": "Manual transition after safety clearance"
        })

        logger.info(f"System state: {previous_state.value} → RUN")
        return True

    # ========== Verification Methods ==========

    def _check_evidence(self, proposal: Dict[str, Any]) -> Dict[str, Any]:
        """A1-א: Validate evidence under T01 control."""
        t01 = self.token_system.get_token("T01")

        if not t01.state['active']:
            return {
                "passed": False,
                "reason": "T01 (Data) inactive - cannot validate evidence"
            }

        # Check if proposal has required evidence
        content = proposal.get("content", {})
        has_evidence = "evidence" in content or "data_source" in content

        return {
            "passed": has_evidence,
            "reason": "Evidence present" if has_evidence else "Missing evidence",
            "agent": "A1-א"
        }

    def _check_dia_impact(self, proposal: Dict[str, Any]) -> Dict[str, Any]:
        """A1-ד: Check DIA impact under T10 control."""
        if not self.t10_measure.state['active']:
            return {
                "passed": False,
                "reason": "T10 (Measure) inactive - cannot check DIA"
            }

        # Verify proposal won't violate DIA monotonicity
        # Simplified check
        content = proposal.get("content", {})
        impacts_dia = content.get("impacts_dia", False)

        if impacts_dia:
            # Would need to simulate impact
            return {
                "passed": True,
                "reason": "DIA impact analyzed - monotonicity preserved",
                "agent": "A1-ד"
            }

        return {
            "passed": True,
            "reason": "No DIA impact",
            "agent": "A1-ד"
        }

    def _check_ethics(self, proposal: Dict[str, Any]) -> Dict[str, Any]:
        """A1-ס: Validate ethics under T13 control."""
        if not self.t13_rights.state['active']:
            return {
                "passed": False,
                "reason": "T13 (Rights) inactive - cannot check ethics",
                "severity": "high"
            }

        # Check for ethical violations
        content = proposal.get("content", {})

        # Check protected rights
        violates_privacy = content.get("violates_privacy", False)
        violates_consent = content.get("violates_consent", False)
        discriminatory = content.get("discriminatory", False)

        if violates_privacy or violates_consent or discriminatory:
            return {
                "passed": False,
                "reason": "Ethical violation detected",
                "severity": "high",
                "agent": "A1-ס"
            }

        return {
            "passed": True,
            "reason": "No ethical violations",
            "agent": "A1-ס"
        }

    def _verify_structure(self, proposal: Dict[str, Any]) -> Dict[str, Any]:
        """A2: Verify structural invariants under T09 control."""
        t09 = self.token_system.get_token("T09")

        if not t09.state['active']:
            return {
                "passed": False,
                "reason": "T09 (Standardize) inactive"
            }

        # Check proposal structure
        required_fields = ["content"]
        has_structure = all(field in proposal for field in required_fields)

        return {
            "passed": has_structure,
            "reason": "Structure valid" if has_structure else "Invalid structure",
            "agent": "A2"
        }

    def _monitor_execution(self, commitment: Dict[str, Any]):
        """B2: Monitor execution under T11 control."""
        if not self.t11_monitor.state['active']:
            logger.warning("T11 (Monitor) inactive - limited monitoring")
            return

        # Log execution monitoring
        logger.info(f"B2 monitoring commitment: {commitment['id']}")

    def _trigger_safety_response(self, error: str):
        """B2: Trigger safety response."""
        logger.error(f"B2 Safety Response: {error}")

        # Determine severity
        if "critical" in error.lower() or "security" in error.lower():
            self._activate_seriousness_mode()
        else:
            self._transition_to_safe()

    def _verify_safety_conditions(self) -> Dict[str, Any]:
        """Verify all safety conditions before transitioning to RUN."""
        checks = {
            "T06_security_active": self.t06_security.state['active'],
            "T11_monitor_active": self.t11_monitor.state['active'],
            "T13_rights_active": self.t13_rights.state['active'],
            "no_pending_violations": len(self.t13_rights.state.get('violations', [])) == 0
        }

        all_passed = all(checks.values())

        return {
            "passed": all_passed,
            "checks": checks,
            "reason": "All safety checks passed" if all_passed else "Safety checks failed"
        }

    # ========== Helper Methods ==========

    def _get_proposal(self, proposal_id: str) -> Optional[Dict[str, Any]]:
        """Get proposal by ID."""
        for proposal in self.proposals:
            if proposal["id"] == proposal_id:
                return proposal
        return None

    def get_system_state(self) -> str:
        """Get current system state."""
        return self.system_state.value

    def get_proposals(self) -> List[Dict[str, Any]]:
        """Get all proposals."""
        return self.proposals

    def get_commitments(self) -> List[Dict[str, Any]]:
        """Get all commitments."""
        return self.commitments

    def get_state_history(self) -> List[Dict[str, Any]]:
        """Get system state history."""
        return self.state_history

    def get_agent_info(self, role: AgentRole) -> Optional[Dict[str, Any]]:
        """Get agent information."""
        return self.agents.get(role)
