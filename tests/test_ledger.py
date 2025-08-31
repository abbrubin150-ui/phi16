import json
import sys
from pathlib import Path

import pytest

sys.path.append(str(Path(__file__).resolve().parents[1]))

from ledger import (
    append_stream,
    replay_stream,
    append_batch,
    replay_batch,
)


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


@pytest.fixture
def ledger_path(tmp_path):
    path = tmp_path / "ledger.json"
    yield path
    if path.exists():
        path.unlink()


def test_hash_chain_validation_failure(ledger_path):
    events = [{"id": "0", "type": "A"}, {"id": "1", "type": "A"}]
    append_stream(ledger_path, events, CFG)
    data = json.loads(ledger_path.read_text())
    data["blocks"][1]["prev_hash"] = "bad"
    ledger_path.write_text(json.dumps(data))
    with pytest.raises(SystemExit):
        replay_stream(ledger_path, CFG)


def test_mode_transition_and_reject(ledger_path):
    events_path = Path(__file__).resolve().parents[1] / "examples" / "events.json"
    events = json.loads(events_path.read_text())["events"]
    metrics = append_stream(ledger_path, events, CFG)
    assert metrics["mode"] == "SAFE"
    saved = json.loads(ledger_path.read_text())
    assert saved["header"]["mode"] == "SAFE"
    with pytest.raises(SystemExit):
        append_stream(ledger_path, [{"id": "x", "type": "A"}], CFG)


def test_replay_roundtrip(ledger_path):
    events_path = Path(__file__).resolve().parents[1] / "examples" / "events.json"
    events = json.loads(events_path.read_text())["events"]
    metrics = append_stream(ledger_path, events, CFG)
    replayed = replay_stream(ledger_path, CFG)
    assert replayed == metrics


def test_batch_replay_roundtrip(ledger_path):
    events_path = Path(__file__).resolve().parents[1] / "examples" / "events.json"
    events = json.loads(events_path.read_text())["events"]
    metrics = append_batch(ledger_path, events, CFG)
    assert metrics["mode"] == "SAFE"
    replayed = replay_batch(ledger_path, CFG)
    assert replayed == metrics


def test_batch_hash_chain_validation_failure(ledger_path):
    events = [{"id": "0", "type": "A"}, {"id": "1", "type": "A"}]
    append_batch(ledger_path, events, CFG)
    data = json.loads(ledger_path.read_text())
    data["blocks"][1]["prev_hash"] = "bad"
    ledger_path.write_text(json.dumps(data))
    with pytest.raises(SystemExit):
        replay_batch(ledger_path, CFG)


@pytest.mark.parametrize("mode", ["HOLD", "SAFE"])
@pytest.mark.parametrize("append_fn", [append_stream, append_batch])
def test_append_reject_in_protected_modes(ledger_path, mode, append_fn):
    ledger_path.write_text(
        json.dumps({"header": {"last_hash": "", "last_dia": 1.0, "mode": mode}, "blocks": []})
    )
    with pytest.raises(SystemExit):
        append_fn(ledger_path, [{"id": "0", "type": "A"}], CFG)
