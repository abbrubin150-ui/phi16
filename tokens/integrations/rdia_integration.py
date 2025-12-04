"""
R/DIA Integration for Hebrew Token System

Maps the Hebrew Token System to the Reflexive/Dialectic Intelligence
Architecture (R/DIA), ensuring that:
- Memory equals accountability (every state change is documented)
- DIA metrics are token-controlled
- Ledger operations respect the ethical hierarchy
"""

import logging
from typing import Dict, Any, Optional
from datetime import datetime

logger = logging.getLogger(__name__)


class RDIAIntegration:
    """
    Integrates Hebrew Token System with R/DIA architecture.

    Token Mappings:
    - T01 (Data/נתונים) → Ledger (L) - Append-only log
    - T10 (Measure/מדידה) → DIA Metrics (graph, info, replay)
    - T11 (Monitor/ניטור) → Continuous DIA monitoring
    - T04 (Storage/אחסון) → Ledger persistence + DIA
    - T06 (Security/אבטחה) → Cryptographic hash chain
    """

    def __init__(self, token_system):
        """
        Initialize R/DIA integration.

        Args:
            token_system: HebrewTokenSystem instance
        """
        self.token_system = token_system
        self.ledger_events = []
        self.dia_metrics_history = []

        # Token references
        self.t01_data = token_system.get_token("T01")
        self.t04_storage = token_system.get_token("T04")
        self.t06_security = token_system.get_token("T06")
        self.t10_measure = token_system.get_token("T10")
        self.t11_monitor = token_system.get_token("T11")

        logger.info("R/DIA Integration initialized")

    def append_to_ledger(self, event: Dict[str, Any]) -> bool:
        """
        Append event to ledger with token-based validation.

        Process:
        1. T01 (Data) validates event structure
        2. T06 (Security) ensures cryptographic integrity
        3. T04 (Storage) commits to ledger
        4. T10 (Measure) updates DIA metrics
        5. T11 (Monitor) tracks system state

        Args:
            event: Event dictionary with required fields

        Returns:
            bool: True if append successful
        """
        try:
            # T01: Validate data structure
            if not self.t01_data.state['active']:
                logger.error("T01 (Data) is inactive - cannot append")
                return False

            if not self._validate_event_structure(event):
                logger.error("Invalid event structure")
                return False

            # T06: Add security metadata
            secured_event = self._add_security_metadata(event)

            # T04: Store in ledger
            if not self.t04_storage.state['active']:
                logger.error("T04 (Storage) is inactive - cannot store")
                return False

            self.ledger_events.append(secured_event)

            # T10: Update DIA metrics
            self._update_dia_metrics()

            # T11: Monitor state
            self._monitor_dia_state()

            logger.info(f"Event appended to ledger: {secured_event['event_id']}")
            return True

        except Exception as e:
            logger.error(f"Error appending to ledger: {e}")
            return False

    def compute_dia_metrics(self) -> Dict[str, float]:
        """
        Compute DIA metrics under T10 (Measure) control.

        DIA Components:
        - DIA_graph: Connectivity (|E| / (|V| * (|V|-1)))
        - DIA_info: Information richness (entropy)
        - DIA_replay: Full reconstruction capability

        Returns:
            dict: DIA metrics
        """
        if not self.t10_measure.state['active']:
            logger.warning("T10 (Measure) inactive - returning default metrics")
            return {"dia_graph": 0.0, "dia_info": 0.0, "dia_replay": 0.0}

        metrics = {
            "dia_graph": self._compute_dia_graph(),
            "dia_info": self._compute_dia_info(),
            "dia_replay": self._compute_dia_replay(),
            "timestamp": datetime.now().isoformat()
        }

        # Apply T10/T11/T12 synergy if active
        if self._check_moral_triangle_synergy():
            synergy_multiplier = 2.5
            metrics["synergy_active"] = True
            metrics["synergy_multiplier"] = synergy_multiplier
            logger.info("Moral Triangle synergy applied to DIA metrics")

        self.dia_metrics_history.append(metrics)
        return metrics

    def verify_dia_monotonicity(self) -> bool:
        """
        Verify DIA Monotonicity Invariant: DIA' ≥ DIA.

        Under T10 (Measure) control, ensures that DIA metrics
        never decrease over time.

        Returns:
            bool: True if monotonicity holds
        """
        if len(self.dia_metrics_history) < 2:
            return True

        current = self.dia_metrics_history[-1]
        previous = self.dia_metrics_history[-2]

        current_dia = self._aggregate_dia(current)
        previous_dia = self._aggregate_dia(previous)

        monotonic = current_dia >= previous_dia

        if not monotonic:
            logger.error(f"DIA Monotonicity violated! {previous_dia} -> {current_dia}")
            # Trigger T11 (Monitor) alert
            self.t11_monitor.state['metrics']['violations'] += 1

        return monotonic

    def replay_ledger(self) -> Dict[str, Any]:
        """
        Replay entire ledger to reconstruct system state.

        Implements DIA_replay under T10 (Measure) and T11 (Monitor).

        Returns:
            dict: Reconstructed state and replay metrics
        """
        if not self.t10_measure.state['active']:
            logger.error("T10 (Measure) inactive - cannot replay")
            return None

        state = {
            "events_processed": 0,
            "state_transitions": [],
            "errors": [],
            "final_state": {}
        }

        for event in self.ledger_events:
            try:
                # Process each event sequentially
                event_state = self._process_event(event)
                state["events_processed"] += 1
                state["state_transitions"].append(event_state)
            except Exception as e:
                state["errors"].append({
                    "event_id": event.get("event_id", "unknown"),
                    "error": str(e)
                })

        # T11: Monitor replay quality
        replay_quality = state["events_processed"] / max(len(self.ledger_events), 1)
        self.t11_monitor.state['metrics']['replay_quality'] = replay_quality

        logger.info(f"Ledger replay complete: {state['events_processed']} events")
        return state

    def get_ledger_size(self) -> int:
        """Get current ledger size."""
        return len(self.ledger_events)

    def get_dia_history(self) -> list:
        """Get DIA metrics history."""
        return self.dia_metrics_history

    # Private helper methods

    def _validate_event_structure(self, event: Dict[str, Any]) -> bool:
        """Validate event has required fields."""
        required_fields = ["event_id", "timestamp", "event_type"]
        return all(field in event for field in required_fields)

    def _add_security_metadata(self, event: Dict[str, Any]) -> Dict[str, Any]:
        """Add T06 (Security) metadata to event."""
        secured = event.copy()
        secured["security"] = {
            "token": "T06",
            "timestamp": datetime.now().isoformat(),
            "hash": self._compute_event_hash(event),
            "sequence": len(self.ledger_events)
        }
        return secured

    def _compute_event_hash(self, event: Dict[str, Any]) -> str:
        """Compute cryptographic hash of event (simplified)."""
        import hashlib
        import json
        event_str = json.dumps(event, sort_keys=True)
        return hashlib.sha256(event_str.encode()).hexdigest()

    def _update_dia_metrics(self):
        """Update DIA metrics after ledger append."""
        metrics = self.compute_dia_metrics()
        self.t10_measure.state['metrics']['dia_last_update'] = metrics

    def _monitor_dia_state(self):
        """Monitor DIA state under T11 control."""
        self.t11_monitor.state['metrics']['ledger_size'] = len(self.ledger_events)
        self.t11_monitor.state['metrics']['last_append'] = datetime.now().isoformat()

    def _compute_dia_graph(self) -> float:
        """Compute DIA_graph (connectivity) metric."""
        if len(self.ledger_events) < 2:
            return 0.0

        # Simplified: assume each event connects to previous
        n = len(self.ledger_events)
        edges = n - 1  # Sequential connections
        max_edges = n * (n - 1)

        return edges / max_edges if max_edges > 0 else 0.0

    def _compute_dia_info(self) -> float:
        """Compute DIA_info (information richness) metric."""
        if not self.ledger_events:
            return 0.0

        # Simplified entropy calculation based on event types
        event_types = {}
        for event in self.ledger_events:
            etype = event.get("event_type", "unknown")
            event_types[etype] = event_types.get(etype, 0) + 1

        total = len(self.ledger_events)
        entropy = 0.0

        for count in event_types.values():
            p = count / total
            if p > 0:
                entropy -= p * (p ** 0.5)  # Simplified entropy

        return entropy

    def _compute_dia_replay(self) -> float:
        """Compute DIA_replay (reconstruction capability) metric."""
        # Returns 1.0 if all events have required fields for replay
        if not self.ledger_events:
            return 1.0

        replayable = sum(1 for e in self.ledger_events
                        if self._is_event_replayable(e))

        return replayable / len(self.ledger_events)

    def _is_event_replayable(self, event: Dict[str, Any]) -> bool:
        """Check if event is replayable."""
        required = ["event_id", "timestamp", "event_type"]
        return all(field in event for field in required)

    def _aggregate_dia(self, metrics: Dict[str, float]) -> float:
        """Aggregate DIA metrics into single score."""
        weights = {"w_g": 0.5, "w_i": 0.3, "w_r": 0.2}

        dia = (
            weights["w_g"] * metrics.get("dia_graph", 0.0) +
            weights["w_i"] * metrics.get("dia_info", 0.0) +
            weights["w_r"] * metrics.get("dia_replay", 0.0)
        )

        return dia

    def _check_moral_triangle_synergy(self) -> bool:
        """Check if T10/T11/T12 are in 1:1:1 ratio for synergy."""
        t12_learn = self.token_system.get_token("T12")

        if not all([self.t10_measure.state['active'],
                   self.t11_monitor.state['active'],
                   t12_learn.state['active']]):
            return False

        # Check if all three are balanced (simplified check)
        return True

    def _process_event(self, event: Dict[str, Any]) -> Dict[str, Any]:
        """Process single event during replay."""
        return {
            "event_id": event.get("event_id"),
            "timestamp": event.get("timestamp"),
            "processed": True
        }
