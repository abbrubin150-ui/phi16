import json
import sys
from pathlib import Path

import pytest

# Ensure the project root is on the import path
sys.path.append(str(Path(__file__).resolve().parents[1]))

from sim_replay import (
    ReplayState,
    dia_graph,
    dia_replay,
    dia_info,
    replay_ok,
)  # noqa: E402


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
    return ReplayState(events=events, vertices=vertices, edges=edges)


def test_dia_graph(sample_state):
    assert dia_graph(sample_state) == pytest.approx(0.5)


def test_replay_ok(sample_state):
    assert replay_ok(sample_state) is True
    assert dia_replay(sample_state) == pytest.approx(1.0)


def test_dia_info(sample_state):
    assert dia_info(sample_state) == pytest.approx(0.5)
