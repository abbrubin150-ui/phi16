import json
import sys
from pathlib import Path

import pytest

sys.path.append(str(Path(__file__).resolve().parents[1]))

from ledger import append_stream, replay_stream


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


def test_hash_chain_validation_failure(tmp_path):
    path = tmp_path / "ledger.json"
    events = [{"id": "0", "type": "A"}, {"id": "1", "type": "A"}]
    append_stream(path, events, CFG)
    data = json.loads(path.read_text())
    data["blocks"][1]["prev_hash"] = "bad"
    path.write_text(json.dumps(data))
    with pytest.raises(SystemExit):
        replay_stream(path, CFG)


def test_mode_transition_and_reject(tmp_path):
    path = tmp_path / "ledger.json"
    events_path = Path(__file__).resolve().parents[1] / "examples" / "events.json"
    events = json.loads(events_path.read_text())["events"]
    metrics = append_stream(path, events, CFG)
    assert metrics["mode"] == "SAFE"
    saved = json.loads(path.read_text())
    assert saved["header"]["mode"] == "SAFE"
    with pytest.raises(SystemExit):
        append_stream(path, [{"id": "x", "type": "A"}], CFG)


def test_replay_roundtrip(tmp_path):
    path = tmp_path / "ledger.json"
    events_path = Path(__file__).resolve().parents[1] / "examples" / "events.json"
    events = json.loads(events_path.read_text())["events"]
    metrics = append_stream(path, events, CFG)
    replayed = replay_stream(path, CFG)
    assert replayed == metrics
