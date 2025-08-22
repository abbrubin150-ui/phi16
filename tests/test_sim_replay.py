import json
import shutil
import sys
from pathlib import Path

import pytest

# Ensure the project root is on the import path
sys.path.append(str(Path(__file__).resolve().parents[1]))

from sim_replay import (  # noqa: E402
    ReplayState,
    dia_graph,
    dia_replay,
    dia_info,
    replay_ok,
    main,
)


@pytest.fixture
def sample_state():
    events_path = (
        Path(__file__).resolve().parents[1] / "examples" / "events.json"
    )
    data = json.loads(events_path.read_text())
    events = data["events"]
    vertices = {e["id"] for e in events}
    edges = {
        (e["id"], j)
        for e in events
        for j in e.get("justifies", [])
        if j in vertices
    }
    state = ReplayState(events=events, vertices=vertices, edges=edges)
    yield state
    state.events.clear()
    state.vertices.clear()
    state.edges.clear()


@pytest.fixture
def cyclic_state(tmp_path):
    data = {
        "events": [
            {"id": 0, "justifies": [1]},
            {"id": 1, "justifies": [0]},
        ]
    }
    events_path = tmp_path / "events.json"
    events_path.write_text(json.dumps(data))
    events = data["events"]
    vertices = {e["id"] for e in events}
    edges = {
        (e["id"], j)
        for e in events
        for j in e.get("justifies", [])
        if j in vertices
    }
    state = ReplayState(events=events, vertices=vertices, edges=edges)
    yield state
    state.events.clear()
    state.vertices.clear()
    state.edges.clear()


def test_dia_graph(sample_state):
    assert dia_graph(sample_state) == pytest.approx(0.5)


def test_replay_ok(sample_state):
    assert replay_ok(sample_state) is True
    assert dia_replay(sample_state) == pytest.approx(1.0)


def test_dia_info(sample_state):
    assert dia_info(sample_state) == pytest.approx(0.5)


def test_replay_cycle(cyclic_state):
    assert replay_ok(cyclic_state) is False
    assert dia_replay(cyclic_state) == pytest.approx(0.0)


def test_weight_sum_validation(tmp_path):
    events_path = (
        Path(__file__).resolve().parents[1] / "examples" / "events.json"
    )
    cfg = {
        "N": 16,
        "EPS": 0,
        "tau": 0.0,
        "weights": {"w_g": 0.5, "w_i": 0.4, "w_r": 0.2},
        "states": ["RUN", "HOLD", "SAFE"],
        "invariants": [
            "AppendOnlyMonotone",
            "NoWriteInHold",
            "NoWriteInSAFE",
            "ProposalNotCommitment",
        ],
        "ports": ["tla", "sim"],
    }
    cfg_path = tmp_path / "cfg.json"
    cfg_path.write_text(json.dumps(cfg))
    schema_src = Path(__file__).resolve().parents[1] / "spec" / "ssot"
    for name in ["phi16.schema.json", "events.schema.json"]:
        shutil.copy(schema_src / name, tmp_path / name)
    state = ReplayState()
    with pytest.raises(SystemExit) as excinfo:
        main(str(events_path), str(cfg_path), state)
    assert "Weights must sum to 1" in str(excinfo.value)


def test_event_schema_validation(tmp_path, capsys):
    cfg_path = (
        Path(__file__).resolve().parents[1]
        / "spec"
        / "ssot"
        / "phi16.instance.json"
    )
    bad_events = {"events": [{"id": "e1"}]}
    events_path = tmp_path / "events.json"
    events_path.write_text(json.dumps(bad_events))
    state = ReplayState()
    with pytest.raises(SystemExit):
        main(str(events_path), str(cfg_path), state)
    captured = capsys.readouterr()
    assert "Event file error" in captured.out


def test_main_from_different_working_directory(tmp_path, monkeypatch):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    state = ReplayState()

    monkeypatch.chdir(tmp_path)
    main(str(events_path), str(cfg_path), state)
    assert state.events


def test_config_with_local_schemas(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    schema_src = repo_root / "spec" / "ssot"

    for name in ["phi16.instance.json", "phi16.schema.json", "events.schema.json"]:
        shutil.copy(schema_src / name, tmp_path / name)

    backup = schema_src.with_name("ssot.bak")
    schema_src.rename(backup)
    try:
        state = ReplayState()
        main(str(events_path), str(tmp_path / "phi16.instance.json"), state)
        assert state.events
    finally:
        backup.rename(schema_src)


def test_json_output(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    out_path = tmp_path / "out.json"
    state = ReplayState()
    main(str(events_path), str(cfg_path), state, json_out=str(out_path))
    data = json.loads(out_path.read_text())
    assert data["graph"] == pytest.approx(0.5)
    assert data["replay"] == pytest.approx(1.0)
    assert data["info"] == pytest.approx(0.5)
    assert data["dia"] == pytest.approx(0.6)
    assert data["mode"] == "SAFE"


def test_stdout_metrics(capsys):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    state = ReplayState()
    main(str(events_path), str(cfg_path), state)

    captured = capsys.readouterr()
    lines = [line.strip() for line in captured.out.strip().splitlines()]
    assert lines == [
        "DIA_graph = 0.5",
        "DIA_replay = 1.0",
        "DIA_info  = 0.5",
        "DIA       = 0.6",
        "mode = SAFE",
    ]
