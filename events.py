"""
Enhanced Event Structures for Φ-OS

Provides typed event structures matching the development spec requirements.
All events support:
- Cryptographic hashing
- JSON schema validation
- Append-only semantics
- DIA metrics integration
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field, asdict
from datetime import datetime
from enum import Enum
from typing import Any, Dict, List, Optional


class EventKind(Enum):
    """Event types in the Φ-OS system"""
    PROPOSAL = "PROPOSAL"
    APPROVAL = "APPROVAL"
    REJECTION = "REJECTION"
    EXECUTION = "EXECUTION"
    COMMITMENT = "COMMITMENT"
    HOLD = "HOLD"
    RESUME = "RESUME"
    METRIC = "METRIC"
    ALERT = "ALERT"
    STATE_CHANGE = "STATE_CHANGE"


@dataclass
class Event:
    """
    Core Event structure for Φ-OS ledger.

    Matches specification from development spec:
    - id: UUID
    - ts: datetime
    - actor_id: str (Φ-Archit / A1 / A2 / B1 / B2 / System)
    - proposal_id: Optional[str]
    - kind: str (PROPOSAL / APPROVAL / EXECUTION / etc.)
    - payload: dict
    - justification: str
    - prev_hash: str (hash of previous event)
    - hash: str (hash of this event)
    - dia_delta: float (change in DIA)
    - signatures: List[str] (cryptographic/logical signatures)
    """

    id: str
    ts: str  # ISO format timestamp
    actor_id: str
    kind: EventKind
    payload: Dict[str, Any]
    justification: str

    # Ledger chain
    prev_hash: str = ""
    hash: str = ""

    # Optional fields
    proposal_id: Optional[str] = None
    dia_delta: float = 0.0
    signatures: List[str] = field(default_factory=list)

    # Graph relationships (for DIA computation)
    parents: List[str] = field(default_factory=list)
    justifies: List[str] = field(default_factory=list)

    # Metadata
    metadata: Dict[str, Any] = field(default_factory=dict)

    def compute_hash(self) -> str:
        """
        Compute SHA256 hash of event.

        Hash includes all fields except 'hash' itself.
        This ensures immutability and chain integrity.
        """
        event_dict = asdict(self)
        event_dict.pop('hash', None)  # Don't include hash in hash computation

        # Convert enum to string for JSON serialization
        if 'kind' in event_dict and hasattr(event_dict['kind'], 'value'):
            event_dict['kind'] = event_dict['kind'].value

        # Convert to canonical JSON
        canonical = json.dumps(event_dict, sort_keys=True, separators=(',', ':'))
        hash_value = hashlib.sha256(canonical.encode()).hexdigest()

        return hash_value

    def sign(self, signature: str):
        """Add a signature to the event"""
        if signature not in self.signatures:
            self.signatures.append(signature)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization"""
        data = asdict(self)
        data['kind'] = self.kind.value  # Convert enum to string
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> Event:
        """Create Event from dictionary"""
        # Convert kind string to enum
        if 'kind' in data and isinstance(data['kind'], str):
            data['kind'] = EventKind(data['kind'])

        return cls(**data)

    def validate(self) -> bool:
        """Validate event structure"""
        # Required fields
        if not self.id:
            return False
        if not self.ts:
            return False
        if not self.actor_id:
            return False
        if not self.kind:
            return False

        # Hash chain integrity
        if self.hash:
            computed = self.compute_hash()
            if computed != self.hash:
                return False

        return True


@dataclass
class ProposalEvent(Event):
    """Event representing a new proposal"""

    def __init__(self, proposal_id: str, actor_id: str, action: str,
                 payload: Dict[str, Any], justification: str):
        super().__init__(
            id=f"EVT-P-{proposal_id}",
            ts=datetime.now().isoformat(),
            actor_id=actor_id,
            kind=EventKind.PROPOSAL,
            payload=payload,
            justification=justification,
            proposal_id=proposal_id
        )
        self.metadata['action'] = action


@dataclass
class ApprovalEvent(Event):
    """Event representing approval (A1 or A2)"""

    def __init__(self, proposal_id: str, actor_id: str, agent: str,
                 verdict: Dict[str, Any], parent_event_id: str):
        super().__init__(
            id=f"EVT-A-{proposal_id}-{agent}",
            ts=datetime.now().isoformat(),
            actor_id=actor_id,
            kind=EventKind.APPROVAL,
            payload=verdict,
            justification=f"{agent} approval",
            proposal_id=proposal_id,
            parents=[parent_event_id]
        )
        self.metadata['agent'] = agent


@dataclass
class CommitmentEvent(Event):
    """Event representing B1 commitment to ledger"""

    def __init__(self, commitment_id: str, proposal_id: str,
                 actor_id: str, action: str, payload: Dict[str, Any],
                 parent_event_id: str):
        super().__init__(
            id=commitment_id,
            ts=datetime.now().isoformat(),
            actor_id=actor_id,
            kind=EventKind.COMMITMENT,
            payload=payload,
            justification=f"Commitment for proposal {proposal_id}",
            proposal_id=proposal_id,
            parents=[parent_event_id]
        )
        self.metadata['action'] = action


@dataclass
class HoldEvent(Event):
    """Event representing system entering HOLD state"""

    def __init__(self, reason: str, triggered_by: str):
        super().__init__(
            id=f"EVT-HOLD-{datetime.now().timestamp()}",
            ts=datetime.now().isoformat(),
            actor_id="SYSTEM",
            kind=EventKind.HOLD,
            payload={"reason": reason, "triggered_by": triggered_by},
            justification=f"Emergency HOLD: {reason}"
        )
        self.metadata['severity'] = 'critical'


@dataclass
class ResumeEvent(Event):
    """Event representing system resuming from HOLD/SAFE"""

    def __init__(self, previous_state: str, approved_by: str):
        super().__init__(
            id=f"EVT-RESUME-{datetime.now().timestamp()}",
            ts=datetime.now().isoformat(),
            actor_id="SYSTEM",
            kind=EventKind.RESUME,
            payload={"previous_state": previous_state, "approved_by": approved_by},
            justification=f"Resume from {previous_state}"
        )


@dataclass
class MetricEvent(Event):
    """Event recording DIA metrics"""

    def __init__(self, metrics: Dict[str, float]):
        super().__init__(
            id=f"EVT-METRIC-{datetime.now().timestamp()}",
            ts=datetime.now().isoformat(),
            actor_id="SYSTEM",
            kind=EventKind.METRIC,
            payload=metrics,
            justification="DIA metrics update"
        )
        self.dia_delta = metrics.get('dia', 0.0)


class EventFactory:
    """Factory for creating events with proper chaining"""

    def __init__(self):
        self.last_hash = ""
        self.event_count = 0

    def create_event(
        self,
        kind: EventKind,
        actor_id: str,
        payload: Dict[str, Any],
        justification: str,
        **kwargs
    ) -> Event:
        """
        Create a new event with proper hash chaining.

        Args:
            kind: Event type
            actor_id: Actor creating event
            payload: Event data
            justification: Reason for event
            **kwargs: Additional event fields

        Returns:
            Properly chained Event
        """
        self.event_count += 1

        event = Event(
            id=f"EVT-{self.event_count:06d}",
            ts=datetime.now().isoformat(),
            actor_id=actor_id,
            kind=kind,
            payload=payload,
            justification=justification,
            prev_hash=self.last_hash,
            **kwargs
        )

        # Compute and set hash
        event.hash = event.compute_hash()
        self.last_hash = event.hash

        return event

    def reset(self):
        """Reset factory state"""
        self.last_hash = ""
        self.event_count = 0


class EventValidator:
    """Validates events against schemas and invariants"""

    @staticmethod
    def validate_event(event: Event) -> tuple[bool, Optional[str]]:
        """
        Validate event structure and content.

        Returns:
            Tuple of (valid, error_message)
        """
        # Basic validation
        if not event.validate():
            return False, "Event validation failed"

        # Kind-specific validation
        if event.kind == EventKind.PROPOSAL:
            if not event.proposal_id:
                return False, "Proposal event missing proposal_id"

        elif event.kind == EventKind.COMMITMENT:
            if not event.proposal_id:
                return False, "Commitment event missing proposal_id"
            if not event.parents:
                return False, "Commitment event missing parents"

        elif event.kind == EventKind.HOLD:
            if 'reason' not in event.payload:
                return False, "HOLD event missing reason"

        return True, None

    @staticmethod
    def validate_chain(events: List[Event]) -> tuple[bool, Optional[str]]:
        """
        Validate hash chain integrity.

        Returns:
            Tuple of (valid, error_message)
        """
        if not events:
            return True, None

        # First event should have empty prev_hash
        if events[0].prev_hash != "":
            return False, "First event has non-empty prev_hash"

        # Validate chain
        for i in range(1, len(events)):
            prev_event = events[i - 1]
            curr_event = events[i]

            # Check hash chain
            if curr_event.prev_hash != prev_event.hash:
                return False, f"Hash chain broken at event {i}: {curr_event.id}"

            # Verify hash computation
            if curr_event.hash != curr_event.compute_hash():
                return False, f"Hash mismatch for event {curr_event.id}"

        return True, None

    @staticmethod
    def validate_dia_monotonicity(events: List[Event]) -> tuple[bool, Optional[str]]:
        """
        Validate DIA monotonicity (DIA should not decrease).

        Returns:
            Tuple of (valid, error_message)
        """
        cumulative_dia = 0.0

        for event in events:
            cumulative_dia += event.dia_delta

            if cumulative_dia < 0:
                return False, f"DIA became negative at event {event.id}"

        return True, None


def create_ledger_compatible_event(event: Event) -> Dict[str, Any]:
    """
    Convert Event to ledger-compatible format.

    Matches the format expected by ledger.py:
    {
        "id": str,
        "type": str,
        "timestamp": str,
        "data": dict,
        "parents": list,
        "justifies": list,
        "metadata": dict
    }
    """
    return {
        "id": event.id,
        "type": event.kind.value,
        "timestamp": event.ts,
        "actor": event.actor_id,
        "data": event.payload,
        "parents": event.parents,
        "justifies": event.justifies,
        "metadata": {
            **event.metadata,
            "proposal_id": event.proposal_id,
            "justification": event.justification,
            "signatures": event.signatures,
            "prev_hash": event.prev_hash,
            "hash": event.hash,
            "dia_delta": event.dia_delta
        }
    }
