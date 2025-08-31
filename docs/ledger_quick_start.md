# Ledger Quick Start

This guide shows how to create a Φ‑OS ledger, append events,
replay them, and inspect entropy metrics.

## Setup

Install dependencies:

```bash
pip install -r requirements.txt
```

## Appending events

Create a ledger file and append a stream of events.  The ledger
stores a hash‑chained history and tracks the DIA metric, which is
an entropy‑based measure of information density.

```python
from ledger import append_stream

CFG = {
    "N": 16,
    "EPS": 0,
    "tau": 0.2,
    "weights": {"w_g": 0.33, "w_i": 0.33, "w_r": 0.34},
    "states": ["RUN", "HOLD", "SAFE"],
    "invariants": [
        "AppendOnlyMonotone",
        "NoWriteInHold",
        "NoWriteInSAFE",
        "ProposalNotCommitment",
    ],
    "ports": ["tla", "sim"],
}

EVENTS = [
    {"id": "e1", "parents": [], "justifies": ["e2"], "type": "Init"},
    {"id": "e2", "parents": ["e1"], "justifies": [], "type": "ConfigChange"},
]

metrics = append_stream("ledger.json", EVENTS, CFG)
print("DIA:", metrics["dia"])
print("Mode:", metrics["mode"])
```

## Replaying

Replaying verifies the hash chain and recomputes the metrics.  The
result should match the values returned when events were appended.

```python
from ledger import replay_stream

replayed = replay_stream("ledger.json", CFG)
assert replayed == metrics
```

The `dia` value in the returned metrics represents the
normalised entropy of the event stream.

## Command‑line interface

The `ledger.py` module includes a small CLI.  Each command prints the
resulting metrics as JSON:

```bash
python ledger.py append-stream ledger.json examples/events.json cfg.json
python ledger.py replay-stream ledger.json cfg.json
```

The `append-batch` and `replay-batch` subcommands perform the same
operations but recompute metrics in batch mode.
