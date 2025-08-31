import json
import shutil
import sys
from pathlib import Path

import pytest

# Ensure the project root is on the import path
sys.path.append(str(Path(__file__).resolve().parents[1]))

from sim_replay import (  # noqa: E402
    ReplayState,
    topo_order,
    dia_graph,
    dia_replay,
    dia_info,
    replay_ok,
    main,
    compute_metrics,
    entropy,
    StreamingReplay,
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
    parent_edges = {
        (p, e["id"])
        for e in events
        for p in e.get("parents", [])
        if p in vertices
    }
    state = ReplayState(
        events=events, vertices=vertices, edges=edges, parent_edges=parent_edges
    )
    yield state
    state.events.clear()
    state.vertices.clear()
    state.edges.clear()
    state.parent_edges.clear()


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
    parent_edges = {
        (p, e["id"])
        for e in events
        for p in e.get("parents", [])
        if p in vertices
    }
    state = ReplayState(
        events=events, vertices=vertices, edges=edges, parent_edges=parent_edges
    )
    yield state
    state.events.clear()
    state.vertices.clear()
    state.edges.clear()
    state.parent_edges.clear()


def test_topo_order_acyclic():
    state = ReplayState(
        events=[{"id": 0}, {"id": 1}, {"id": 2}],
        vertices={0, 1, 2},
        edges={(0, 1), (1, 2)},
    )
    order = topo_order(state)
    assert order is not None
    assert set(order) == state.vertices
    assert all(
        order.index(u) < order.index(v)
        for u, v in state.edges | state.parent_edges
    )


def test_topo_order_cyclic():
    state = ReplayState(
        events=[{"id": 0}, {"id": 1}],
        vertices={0, 1},
        edges={(0, 1), (1, 0)},
    )
    assert topo_order(state) is None


def test_dia_graph(sample_state):
    assert dia_graph(sample_state) == pytest.approx(0.5)


def test_dia_graph_empty_state():
    state = ReplayState()
    assert dia_graph(state) == pytest.approx(0.0)


def test_replay_ok(sample_state):
    assert replay_ok(sample_state) is True
    assert dia_replay(sample_state) == pytest.approx(1.0)


def test_dia_info(sample_state):
    assert dia_info(sample_state) == pytest.approx(0.5)


def test_replay_cycle(cyclic_state):
    assert replay_ok(cyclic_state) is False
    assert dia_replay(cyclic_state) == pytest.approx(0.0)


def test_replay_ok_self_loop():
    events = [{"id": 0, "justifies": [0]}]
    vertices = {0}
    edges = {(0, 0)}
    state = ReplayState(events=events, vertices=vertices, edges=edges)
    assert replay_ok(state) is False


def test_entropy_negative_probability():
    with pytest.raises(ValueError):
        entropy([0.5, -0.5])


def test_parent_edges_influence_metrics():
    events = [
        {"id": 0, "parents": [], "type": "A"},
        {"id": 1, "parents": [0], "type": "B"},
    ]
    vertices = {0, 1}
    edges: set = set()
    parent_edges = {(0, 1)}
    with_parents = ReplayState(
        events=events, vertices=vertices, edges=edges, parent_edges=parent_edges
    )
    without_parents = ReplayState(events=events, vertices=vertices, edges=edges)
    assert dia_graph(with_parents) == pytest.approx(0.5)
    assert dia_graph(without_parents) == pytest.approx(0.0)
    assert dia_info(with_parents) == pytest.approx(0.5)
    assert dia_info(without_parents) == pytest.approx(0.0)


def test_parent_edges_cycle_detection():
    events = [
        {"id": 0, "parents": [1]},
        {"id": 1, "parents": [0]},
    ]
    vertices = {0, 1}
    edges: set = set()
    parent_edges = {(1, 0), (0, 1)}
    state = ReplayState(
        events=events, vertices=vertices, edges=edges, parent_edges=parent_edges
    )
    assert replay_ok(state) is False
    assert dia_replay(state) == pytest.approx(0.0)


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
    with pytest.raises(SystemExit) as excinfo:
        main(str(events_path), str(cfg_path))
    assert "Weights must sum to 1" in str(excinfo.value)


def test_invalid_config_consistency():
    events = [{"id": "e1", "parents": [], "type": "X"}]
    cfg = {
        "N": 16,
        "EPS": 0,
        "tau": 0.0,
        "weights": {"w_g": 0.5, "w_i": 0.4, "w_r": 0.2},
        "states": ["RUN", "HOLD", "SAFE"],
        "invariants": ["AppendOnlyMonotone"],
        "ports": ["sim"],
    }

    with pytest.raises(SystemExit) as exc_batch:
        compute_metrics(events, cfg)

    sim = StreamingReplay(cfg)
    sim.add_event(events[0])
    with pytest.raises(SystemExit) as exc_stream:
        sim.metrics()

    assert str(exc_batch.value) == str(exc_stream.value)


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
    with pytest.raises(SystemExit):
        main(str(events_path), str(cfg_path))
    captured = capsys.readouterr()
    assert "Event file error" in captured.out


def test_streaming_add_event_validation(capsys):
    repo_root = Path(__file__).resolve().parents[1]
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    cfg = json.loads(cfg_path.read_text())
    sim = StreamingReplay(cfg)
    bad_event = {"id": 1, "type": "Init"}
    with pytest.raises(SystemExit) as excinfo:
        sim.add_event(bad_event)
    assert excinfo.value.code == 1
    captured = capsys.readouterr()
    assert "Event file error" in captured.out


def test_main_from_different_working_directory(tmp_path, monkeypatch):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"

    monkeypatch.chdir(tmp_path)
    result = main(str(events_path), str(cfg_path))
    assert result["dia"] == pytest.approx(0.6)


def test_config_with_local_schemas(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    schema_src = repo_root / "spec" / "ssot"

    for name in ["phi16.instance.json", "phi16.schema.json", "events.schema.json"]:
        shutil.copy(schema_src / name, tmp_path / name)

    backup = schema_src.with_name("ssot.bak")
    schema_src.rename(backup)
    try:
        result = main(str(events_path), str(tmp_path / "phi16.instance.json"))
        assert result["dia"] == pytest.approx(0.6)
    finally:
        backup.rename(schema_src)


def test_append_only_violation():
    events = [
        {"id": "e2", "parents": [], "type": "X"},
        {"id": "e1", "parents": [], "type": "X"},
    ]
    cfg = {
        "N": 16,
        "EPS": 0,
        "tau": 0.0,
        "weights": {"w_g": 0.5, "w_i": 0.3, "w_r": 0.2},
        "states": ["RUN", "HOLD", "SAFE"],
        "invariants": ["AppendOnlyMonotone"],
        "ports": ["sim"],
    }
    with pytest.raises(SystemExit) as excinfo:
        compute_metrics(events, cfg)
    assert "monotone increasing" in str(excinfo.value)


def test_numeric_ids_monotonic():
    events = [
        {"id": "1", "parents": [], "type": "X"},
        {"id": "2", "parents": [], "type": "X"},
        {"id": "10", "parents": [], "type": "X"},
    ]
    cfg = {
        "N": 16,
        "EPS": 0,
        "tau": 0.0,
        "weights": {"w_g": 0.5, "w_i": 0.3, "w_r": 0.2},
        "states": ["RUN", "HOLD", "SAFE"],
        "invariants": ["AppendOnlyMonotone"],
        "ports": ["sim"],
    }
    result = compute_metrics(events, cfg)
    assert result["replay"] == pytest.approx(1.0)

    sim = StreamingReplay(cfg)
    for ev in events:
        sim.add_event(ev)
    assert sim.metrics()["replay"] == pytest.approx(1.0)


def test_numeric_ids_violation():
    events = [
        {"id": "1", "parents": [], "type": "X"},
        {"id": "10", "parents": [], "type": "X"},
        {"id": "2", "parents": [], "type": "X"},
    ]
    cfg = {
        "N": 16,
        "EPS": 0,
        "tau": 0.0,
        "weights": {"w_g": 0.5, "w_i": 0.3, "w_r": 0.2},
        "states": ["RUN", "HOLD", "SAFE"],
        "invariants": ["AppendOnlyMonotone"],
        "ports": ["sim"],
    }
    with pytest.raises(SystemExit) as excinfo:
        compute_metrics(events, cfg)
    assert "monotone increasing" in str(excinfo.value)

    sim = StreamingReplay(cfg)
    sim.add_event(events[0])
    sim.add_event(events[1])
    with pytest.raises(SystemExit) as excinfo2:
        sim.add_event(events[2])
    assert "monotone increasing" in str(excinfo2.value)


def test_no_write_in_hold():
    events = [{"id": "e1", "parents": [], "type": "X"}]
    cfg = {
        "N": 16,
        "EPS": 0,
        "tau": 0.0,
        "weights": {"w_g": 0.5, "w_i": 0.3, "w_r": 0.2},
        "states": ["RUN", "HOLD", "SAFE"],
        "invariants": ["NoWriteInHold"],
        "ports": ["sim"],
    }
    with pytest.raises(SystemExit) as excinfo:
        compute_metrics(events, cfg, prev_mode="HOLD")
    assert "HOLD mode" in str(excinfo.value)


def test_streaming_replay_matches_batch():
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    events = json.loads(events_path.read_text())["events"]
    cfg = json.loads(cfg_path.read_text())

    sim = StreamingReplay(cfg)
    for ev in events:
        sim.add_event(ev)
    stream_res = sim.metrics()

    batch_res = compute_metrics(events, cfg)

    assert stream_res["dia"] == pytest.approx(batch_res["dia"])
    assert stream_res["mode"] == batch_res["mode"]


def test_json_output(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    out_path = tmp_path / "out.json"
    main(str(events_path), str(cfg_path), json_out=str(out_path))
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
    main(str(events_path), str(cfg_path))

    captured = capsys.readouterr()
    lines = [line.strip() for line in captured.out.strip().splitlines()]
    assert lines == [
        "DIA_graph = 0.5",
        "DIA_replay = 1.0",
        "DIA_info  = 0.5",
        "DIA       = 0.6",
        "mode = SAFE",
    ]


def test_duplicate_event_ids(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    events = {
        "events": [
            {"id": "e1", "type": "Init"},
            {"id": "e1", "type": "Init"},
        ]
    }
    events_path = tmp_path / "events.json"
    events_path.write_text(json.dumps(events))
    with pytest.raises(SystemExit) as excinfo:
        main(str(events_path), str(cfg_path))
    assert "Duplicate event IDs: ['e1']" in str(excinfo.value)


def test_unknown_justification(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    events = {"events": [{"id": "e0", "type": "Init", "justifies": ["e1"]}]}
    events_path = tmp_path / "events.json"
    events_path.write_text(json.dumps(events))
    with pytest.raises(SystemExit) as excinfo:
        main(str(events_path), str(cfg_path))
    assert "Event e0 justifies unknown event e1" in str(excinfo.value)


def test_unknown_justification_among_many(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"
    events = {
        "events": [
            {"id": "e0", "type": "Init", "justifies": ["e1", "e2"]},
            {"id": "e1", "type": "Init"},
        ]
    }
    events_path = tmp_path / "events.json"
    events_path.write_text(json.dumps(events))
    with pytest.raises(SystemExit) as excinfo:
        main(str(events_path), str(cfg_path))
    assert "Event e0 justifies unknown event e2" in str(excinfo.value)


def test_mode_prev_dia_below_threshold(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"

    # Determine threshold D - tau using a baseline computation
    baseline = main(
        str(events_path),
        str(cfg_path),
        json_out=str(tmp_path / "baseline.json"),
    )
    cfg = json.loads(cfg_path.read_text())
    threshold = baseline["dia"] - cfg["tau"]

    # Provide prev_dia just below threshold -> RUN
    result = main(
        str(events_path),
        str(cfg_path),
        prev_dia=threshold - 0.01,
        json_out=str(tmp_path / "below.json"),
    )
    assert result["mode"] == "RUN"


def test_mode_prev_dia_above_threshold(tmp_path):
    repo_root = Path(__file__).resolve().parents[1]
    events_path = repo_root / "examples" / "events.json"
    cfg_path = repo_root / "spec" / "ssot" / "phi16.instance.json"

    baseline = main(
        str(events_path),
        str(cfg_path),
        json_out=str(tmp_path / "baseline.json"),
    )
    cfg = json.loads(cfg_path.read_text())
    threshold = baseline["dia"] - cfg["tau"]

    # Provide prev_dia above threshold -> SAFE
    result = main(
        str(events_path),
        str(cfg_path),
        prev_dia=threshold + 0.01,
        json_out=str(tmp_path / "above.json"),
    )
    assert result["mode"] == "SAFE"


def test_compute_metrics_basic():
    events = [
        {"id": "e1", "parents": [], "justifies": ["e2"], "type": "Init"},
        {"id": "e2", "parents": ["e1"], "justifies": [], "type": "ConfigChange"},
    ]
    cfg = {
        "N": 16,
        "EPS": 0,
        "tau": 0.0,
        "weights": {"w_g": 0.5, "w_i": 0.3, "w_r": 0.2},
        "states": ["RUN", "HOLD", "SAFE"],
        "invariants": [
            "AppendOnlyMonotone",
            "NoWriteInHold",
            "NoWriteInSAFE",
            "ProposalNotCommitment",
        ],
        "ports": ["tla", "sim"],
    }
    result = compute_metrics(events, cfg)
    assert result["graph"] == pytest.approx(0.5)
    assert result["replay"] == pytest.approx(1.0)
    assert result["info"] == pytest.approx(0.5)
    assert result["dia"] == pytest.approx(0.6)
    assert result["mode"] == "SAFE"


def test_compute_metrics_duplicate_ids():
    events = [
        {"id": "e1", "type": "Init"},
        {"id": "e1", "type": "Config"},
    ]
    cfg = {
        "N": 16,
        "EPS": 0,
        "tau": 0.0,
        "weights": {"w_g": 0.5, "w_i": 0.3, "w_r": 0.2},
        "states": ["RUN", "HOLD", "SAFE"],
        "invariants": ["AppendOnlyMonotone"],
        "ports": ["tla"],
    }
    with pytest.raises(SystemExit) as excinfo:
        compute_metrics(events, cfg)
    assert "Duplicate event IDs: ['e1']" in str(excinfo.value)
