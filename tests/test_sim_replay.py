import json
import sys
from pathlib import Path

import pytest

# Ensure the project root is on the import path
sys.path.append(str(Path(__file__).resolve().parents[1]))

import sim_replay as sr  # noqa: E402
from sim_replay import dia_graph, dia_replay, dia_info, replay_ok  # noqa: E402


@pytest.fixture
def sample_events():
    events_path = (
        Path(__file__).resolve().parents[1] / "examples" / "events.json"
    )
    data = json.loads(events_path.read_text())

    sr.E = data["events"]
    sr.V = {e["id"] for e in sr.E}
    sr.E_edges = {
        (e["id"], j)
        for e in sr.E
        for j in e.get("justifies", [])
        if j in sr.V
    }
    yield
    sr.E = []
    sr.V = set()
    sr.E_edges = set()


def test_dia_graph(sample_events):
    assert dia_graph() == pytest.approx(0.5)


def test_replay_ok(sample_events):
    assert replay_ok() is True
    assert dia_replay() == pytest.approx(1.0)


def test_dia_info(sample_events):
    assert dia_info() == pytest.approx(0.5)
