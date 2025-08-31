import json
import subprocess
import sys
from pathlib import Path


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


def run(cmd):
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return json.loads(result.stdout)


def test_cli_smoke(tmp_path):
    root = Path(__file__).resolve().parents[1]
    cfg_path = tmp_path / "cfg.json"
    events_path = tmp_path / "events.json"
    ledger_stream = tmp_path / "ledger_stream.json"
    ledger_batch = tmp_path / "ledger_batch.json"

    cfg_path.write_text(json.dumps(CFG))
    events_path.write_text(json.dumps({"events": EVENTS}))

    metrics_stream = run(
        [
            sys.executable,
            str(root / "ledger.py"),
            "append-stream",
            str(ledger_stream),
            str(events_path),
            str(cfg_path),
        ]
    )
    replayed_stream = run(
        [
            sys.executable,
            str(root / "ledger.py"),
            "replay-stream",
            str(ledger_stream),
            str(cfg_path),
        ]
    )
    assert replayed_stream == metrics_stream

    metrics_batch = run(
        [
            sys.executable,
            str(root / "ledger.py"),
            "append-batch",
            str(ledger_batch),
            str(events_path),
            str(cfg_path),
        ]
    )
    replayed_batch = run(
        [
            sys.executable,
            str(root / "ledger.py"),
            "replay-batch",
            str(ledger_batch),
            str(cfg_path),
        ]
    )
    assert replayed_batch == metrics_batch
