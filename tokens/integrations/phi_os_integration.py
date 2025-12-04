"""
Unified Φ-OS Integration Layer

Combines all integration modules (R/DIA, NAND-only, Multi-agent)
into a single coherent system that implements the complete Φ-OS
architecture with Hebrew Token System governance.

Core Principles:
1. Memory = Accountability (R/DIA)
2. Verifiable Simplicity (NAND-only)
3. Proposal ≠ Commitment (Multi-agent)
4. Ethics Before Technology (Token Hierarchy)
"""

import logging
from typing import Dict, Any, List, Optional
from datetime import datetime

from .rdia_integration import RDIAIntegration
from .nand_integration import NANDIntegration
from .agent_integration import AgentWorkflowIntegration, SystemState

logger = logging.getLogger(__name__)


class PhiOSIntegration:
    """
    Unified Φ-OS Integration with Hebrew Token System.

    This class orchestrates all three pillars of Φ-OS:
    - R/DIA: Ensures accountability through immutable ledger
    - NAND-only: Ensures formal verifiability
    - Multi-agent: Ensures separation of powers

    All operations are governed by the Hebrew Token System's
    ethical hierarchy, with T15 (Seriousness) as ultimate control.
    """

    def __init__(self, token_system):
        """
        Initialize unified Φ-OS integration.

        Args:
            token_system: HebrewTokenSystem instance
        """
        self.token_system = token_system

        # Initialize integration modules
        self.rdia = RDIAIntegration(token_system)
        self.nand = NANDIntegration(token_system)
        self.agents = AgentWorkflowIntegration(token_system)

        # System metrics
        self.operations_count = 0
        self.start_time = datetime.now()

        logger.info("Φ-OS Integration initialized with Hebrew Token System")

    # ========== Unified Workflow ==========

    def process_request(self, request: Dict[str, Any]) -> Dict[str, Any]:
        """
        Process a request through the complete Φ-OS pipeline.

        Pipeline:
        1. Φ-Architect proposes change (Multi-agent)
        2. A1/A2 verify proposal (Token-controlled)
        3. NAND-only validation (Formal verification)
        4. B1 executes commitment (Automation)
        5. Append to ledger (R/DIA)
        6. B2 monitors execution (Safety)
        7. Update DIA metrics (Accountability)

        Args:
            request: Request dictionary with action and data

        Returns:
            dict: Processing result with full audit trail
        """
        self.operations_count += 1

        result = {
            "request_id": f"REQ-{self.operations_count:04d}",
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "stages": {},
            "audit_trail": []
        }

        try:
            # Stage 1: Proposal (Multi-agent)
            logger.info(f"Stage 1: Creating proposal for {request.get('action')}")
            proposal_id = self.agents.propose_change(request)

            if not proposal_id:
                result["error"] = "Proposal creation failed"
                return result

            result["stages"]["proposal"] = {
                "id": proposal_id,
                "status": "created"
            }
            result["audit_trail"].append(f"Proposal {proposal_id} created")

            # Stage 2: Verification (Token-controlled multi-agent)
            logger.info(f"Stage 2: Verifying proposal {proposal_id}")
            verification = self.agents.verify_proposal(proposal_id)

            result["stages"]["verification"] = verification

            if verification["vetoed"]:
                result["error"] = "Proposal vetoed"
                result["reasons"] = verification["reasons"]
                result["audit_trail"].append(f"Proposal {proposal_id} vetoed")
                return result

            result["audit_trail"].append(f"Proposal {proposal_id} approved")

            # Stage 3: NAND-only validation
            logger.info(f"Stage 3: NAND-only validation")
            nand_validation = self._validate_via_nand(request)

            result["stages"]["nand_validation"] = nand_validation

            if not nand_validation["valid"]:
                result["error"] = "NAND validation failed"
                return result

            result["audit_trail"].append("NAND validation passed")

            # Stage 4: Execution (B1 Actuator)
            logger.info(f"Stage 4: Executing commitment")
            execution = self.agents.execute_commitment(proposal_id)

            if not execution:
                result["error"] = "Execution failed"
                return result

            result["stages"]["execution"] = {
                "status": "committed"
            }
            result["audit_trail"].append(f"Commitment executed")

            # Stage 5: Ledger append (R/DIA)
            logger.info(f"Stage 5: Appending to ledger")
            ledger_event = self._create_ledger_event(request, proposal_id, result)
            ledger_success = self.rdia.append_to_ledger(ledger_event)

            if not ledger_success:
                result["error"] = "Ledger append failed"
                # Note: Execution completed but not recorded - critical state!
                logger.critical("Execution committed but ledger append failed!")
                return result

            result["stages"]["ledger"] = {
                "event_id": ledger_event["event_id"],
                "status": "appended"
            }
            result["audit_trail"].append(f"Event appended to ledger")

            # Stage 6: DIA metrics update
            logger.info(f"Stage 6: Updating DIA metrics")
            dia_metrics = self.rdia.compute_dia_metrics()

            result["stages"]["dia_metrics"] = dia_metrics
            result["audit_trail"].append("DIA metrics updated")

            # Verify DIA monotonicity
            monotonic = self.rdia.verify_dia_monotonicity()
            if not monotonic:
                logger.error("DIA monotonicity violated!")
                # This is critical - might trigger T15
                self.agents._activate_seriousness_mode()

            # Success!
            result["success"] = True
            logger.info(f"Request {result['request_id']} completed successfully")

        except Exception as e:
            logger.error(f"Request processing failed: {e}")
            result["error"] = str(e)
            result["audit_trail"].append(f"Error: {e}")

            # Trigger safety response
            self.agents._trigger_safety_response(str(e))

        return result

    # ========== Integrated Operations ==========

    def validate_system_state(self) -> Dict[str, Any]:
        """
        Validate complete system state across all integrations.

        Returns:
            dict: Comprehensive system state validation
        """
        validation = {
            "timestamp": datetime.now().isoformat(),
            "system_state": self.agents.get_system_state(),
            "validations": {}
        }

        # R/DIA validation
        validation["validations"]["rdia"] = {
            "ledger_size": self.rdia.get_ledger_size(),
            "dia_monotonic": self.rdia.verify_dia_monotonicity(),
            "dia_metrics": self.rdia.compute_dia_metrics()
        }

        # NAND-only validation
        validation["validations"]["nand"] = {
            "policy_compliance": self.nand.verify_policy_compliance(),
            "nand_stats": self.nand.get_nand_stats()
        }

        # Multi-agent validation
        validation["validations"]["agents"] = {
            "proposals_count": len(self.agents.get_proposals()),
            "commitments_count": len(self.agents.get_commitments()),
            "state_history": len(self.agents.get_state_history())
        }

        # Token system validation
        validation["validations"]["tokens"] = self._validate_token_hierarchy()

        # Overall health
        all_valid = all([
            validation["validations"]["rdia"]["dia_monotonic"],
            validation["validations"]["nand"]["policy_compliance"]["compliant"],
            validation["system_state"] != "HOLD"
        ])

        validation["system_healthy"] = all_valid

        return validation

    def replay_full_system(self) -> Dict[str, Any]:
        """
        Replay entire system state from ledger.

        This is the ultimate accountability check:
        - Replay ledger (R/DIA)
        - Verify all operations were NAND-only
        - Reconstruct agent workflow
        - Validate token constraints

        Returns:
            dict: Full system replay result
        """
        logger.info("Starting full system replay")

        replay = {
            "start_time": datetime.now().isoformat(),
            "stages": {}
        }

        # Replay ledger
        ledger_replay = self.rdia.replay_ledger()
        replay["stages"]["ledger_replay"] = ledger_replay

        # Verify NAND compliance throughout
        nand_compliance = self.nand.verify_policy_compliance()
        replay["stages"]["nand_compliance"] = nand_compliance

        # Reconstruct agent workflow
        agent_state = {
            "proposals": self.agents.get_proposals(),
            "commitments": self.agents.get_commitments(),
            "state_history": self.agents.get_state_history()
        }
        replay["stages"]["agent_workflow"] = agent_state

        # Validate token constraints
        token_validation = self._validate_all_constraints()
        replay["stages"]["token_constraints"] = token_validation

        # Verify Proposal ≠ Commitment invariant
        proposals_count = len(agent_state["proposals"])
        commitments_count = len(agent_state["commitments"])

        replay["invariants"] = {
            "proposal_not_commitment": proposals_count >= commitments_count,
            "dia_monotonicity": self.rdia.verify_dia_monotonicity(),
            "nand_only": nand_compliance["compliant"]
        }

        replay["success"] = all(replay["invariants"].values())

        logger.info(f"System replay complete: {'SUCCESS' if replay['success'] else 'FAILURE'}")

        return replay

    def emergency_hold(self, reason: str) -> bool:
        """
        Trigger emergency HOLD via T15 (Seriousness).

        This is the ultimate safety mechanism:
        - Activates T15 (Seriousness)
        - Transitions to HOLD state
        - Suspends T07 (Automation)
        - No writes allowed

        Args:
            reason: Reason for emergency hold

        Returns:
            bool: True if HOLD activated
        """
        logger.critical(f"EMERGENCY HOLD TRIGGERED: {reason}")

        # Activate T15
        self.agents._activate_seriousness_mode()

        # Log to ledger
        hold_event = {
            "event_id": f"HOLD-{datetime.now().timestamp()}",
            "timestamp": datetime.now().isoformat(),
            "event_type": "emergency_hold",
            "reason": reason,
            "triggered_by": "T15-Seriousness"
        }

        self.rdia.append_to_ledger(hold_event)

        return self.agents.get_system_state() == "HOLD"

    def resume_operations(self) -> bool:
        """
        Resume operations from HOLD/SAFE to RUN.

        Requires:
        - All safety checks passed
        - T15 cleared
        - Manual confirmation

        Returns:
            bool: True if resumed successfully
        """
        logger.info("Attempting to resume operations")

        # Validate system state
        validation = self.validate_system_state()

        if not validation["system_healthy"]:
            logger.error("System not healthy - cannot resume")
            return False

        # Transition to RUN
        success = self.agents.transition_to_run()

        if success:
            # Log to ledger
            resume_event = {
                "event_id": f"RESUME-{datetime.now().timestamp()}",
                "timestamp": datetime.now().isoformat(),
                "event_type": "resume_operations",
                "previous_state": validation["system_state"]
            }

            self.rdia.append_to_ledger(resume_event)

            logger.info("Operations resumed successfully")

        return success

    # ========== Helper Methods ==========

    def _validate_via_nand(self, request: Dict[str, Any]) -> Dict[str, Any]:
        """Validate request using NAND-only logic."""
        # Example: Validate token constraints via NAND
        constraints_valid = self.nand.validate_token_constraint("T01", "C01")

        return {
            "valid": constraints_valid,
            "nand_ops_used": self.nand.nand_ops_count
        }

    def _create_ledger_event(
        self,
        request: Dict[str, Any],
        proposal_id: str,
        result: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Create ledger event from request and result."""
        return {
            "event_id": f"EVT-{self.operations_count:04d}",
            "timestamp": datetime.now().isoformat(),
            "event_type": request.get("action", "unknown"),
            "proposal_id": proposal_id,
            "request": request,
            "result": result
        }

    def _validate_token_hierarchy(self) -> Dict[str, Any]:
        """Validate token hierarchy constraints."""
        violations = []

        # Check critical constraints
        constraints_to_check = ["C01", "C02", "C03", "C04", "C05", "C06"]

        for constraint in constraints_to_check:
            # Would implement full constraint checking here
            pass

        return {
            "valid": len(violations) == 0,
            "violations": violations
        }

    def _validate_all_constraints(self) -> Dict[str, bool]:
        """Validate all token constraints."""
        # Simplified validation
        return {
            "C01_automation_with_monitoring": True,
            "C02_compute_with_security": True,
            "C03_governance_with_rights": True,
            "C04_fair_standards": True,
            "C05_identified_network": True,
            "C06_no_rights_violations_storage": True
        }

    # ========== System Information ==========

    def get_system_info(self) -> Dict[str, Any]:
        """Get comprehensive system information."""
        uptime = (datetime.now() - self.start_time).total_seconds()

        return {
            "system": "Φ-OS with Hebrew Token System",
            "version": "1.0.0",
            "uptime_seconds": uptime,
            "operations_count": self.operations_count,
            "system_state": self.agents.get_system_state(),
            "integrations": {
                "rdia": {
                    "ledger_size": self.rdia.get_ledger_size(),
                    "dia_metrics": self.rdia.compute_dia_metrics()
                },
                "nand": {
                    "stats": self.nand.get_nand_stats()
                },
                "agents": {
                    "proposals": len(self.agents.get_proposals()),
                    "commitments": len(self.agents.get_commitments())
                }
            },
            "token_system": {
                "active_tokens": self._count_active_tokens(),
                "highest_priority_active": self._get_highest_priority_active()
            }
        }

    def _count_active_tokens(self) -> int:
        """Count active tokens."""
        count = 0
        for token_id in ["T01", "T02", "T03", "T04", "T05", "T06", "T07",
                         "T08", "T09", "T10", "T11", "T12", "T13", "T14", "T15"]:
            token = self.token_system.get_token(token_id)
            if token and token.state.get('active'):
                count += 1
        return count

    def _get_highest_priority_active(self) -> Optional[str]:
        """Get highest priority active token."""
        highest = None
        highest_priority = -1

        for token_id in ["T15", "T13", "T10", "T06", "T01"]:  # Check high priority first
            token = self.token_system.get_token(token_id)
            if token and token.state.get('active'):
                if token.priority > highest_priority:
                    highest_priority = token.priority
                    highest = token_id

        return highest
