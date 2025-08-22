import argparse
import json
from collections import defaultdict, deque
from dataclasses import dataclass, field
from math import log2
from pathlib import Path
from typing import Iterable, List, Optional

import jsonschema
from jsonschema import ValidationError


@dataclass
class ReplayState:
    """Holds data required for DIA computations."""

    events: list = field(default_factory=list)
    vertices: set = field(default_factory=set)
    edges: set = field(default_factory=set)
    parent_edges: set = field(default_factory=set)


def dia_graph(state: ReplayState) -> float:
    """Calculate edge density for the current replay state.

    Args:
        state: Replay state containing vertices and edges.

    Returns:
        Ratio of edges to vertices, defaulting to 0 when no vertices exist.
    """

    all_edges = state.edges | state.parent_edges
    return len(all_edges) / max(len(state.vertices), 1)


def topo_order(state: ReplayState) -> Optional[List[int]]:
    """Return a topological ordering of the event graph if possible.

    Args:
        state: Replay state containing the current graph.

    Returns:
        A list of event IDs in topological order, or ``None`` if cycles are
        detected.
    """

    indeg = defaultdict(int)
    adj = defaultdict(list)
    for u, v in state.edges | state.parent_edges:
        indeg[v] += 1
        adj[u].append(v)
    q = deque([v for v in state.vertices if indeg[v] == 0])
    order: List[int] = []
    while q:
        u = q.popleft()
        order.append(u)
        for w in adj[u]:
            indeg[w] -= 1
            if indeg[w] == 0:
                q.append(w)
    return order if len(order) == len(state.vertices) else None


def replay_ok(state: ReplayState) -> bool:
    """Check whether the event graph is acyclic.

    Args:
        state: Replay state containing the event graph.

    Returns:
        ``True`` if a topological order exists, ``False`` otherwise.
    """

    return topo_order(state) is not None


def dia_replay(state: ReplayState) -> float:
    """Score if the event graph can be replayed without cycles.

    Args:
        state: Replay state containing the event graph.

    Returns:
        ``1.0`` when the graph is acyclic, otherwise ``0.0``.
    """

    return 1.0 if replay_ok(state) else 0.0


def entropy(p: Iterable[float]) -> float:
    """Compute the Shannon entropy of a distribution.

    Args:
        p: Iterable of probability values.

    Returns:
        Entropy in bits.
    """

    return -sum(pi * log2(pi) for pi in p if pi > 0)


def dia_info(state: ReplayState) -> float:
    """Estimate information recovered by the event graph.

    Args:
        state: Replay state containing events and graph structure.

    Returns:
        Fraction of information captured by the graph relative to event
        diversity.
    """

    types = [e.get("type", "X") for e in state.events]
    from collections import Counter
    c = Counter(types)
    total = sum(c.values())
    p = [v / total for v in c.values()]
    H = entropy(p) if total > 0 else 0.0
    all_edges = state.edges | state.parent_edges
    recovered = min(H, len(all_edges) / max(len(state.vertices), 1))
    return 0.0 if H == 0 else recovered / H


def compute_metrics(
    events: list,
    cfg: dict,
    prev_dia: float = 1.0,
    schema_dir: str | Path | None = None,
) -> dict:
    """Validate and compute DIA metrics from in-memory data.

    Args:
        events: List of event dictionaries to analyse.
        cfg: Configuration dictionary.
        prev_dia: Previous DIA score for mode selection.
        schema_dir: Directory containing ``phi16.schema.json`` and
            ``events.schema.json``. Defaults to the repository's ``spec/ssot``
            directory.

    Returns:
        A dictionary containing individual metric components, the overall DIA
        value, and the selected mode.
    """

    state = ReplayState()

    schema_base = (
        Path(schema_dir)
        if schema_dir is not None
        else Path(__file__).resolve().parent / "spec" / "ssot"
    )
    with open(schema_base / "phi16.schema.json", "r") as f:
        schema = json.load(f)
    with open(schema_base / "events.schema.json", "r") as f:
        events_schema = json.load(f)

    try:
        jsonschema.validate(cfg, schema)
    except ValidationError as e:
        print(f"Configuration error: {e.message}")
        raise SystemExit(1)

    try:
        jsonschema.validate({"events": events}, events_schema)
    except ValidationError as e:
        print(f"Event file error: {e.message}")
        raise SystemExit(1)

    state.events = events
    ids = [e["id"] for e in state.events]
    if len(ids) != len(set(ids)):
        seen = set()
        duplicates = set()
        for _id in ids:
            if _id in seen:
                duplicates.add(_id)
            else:
                seen.add(_id)
        raise SystemExit(f"Duplicate event IDs: {sorted(duplicates)}")
    id2e = {e["id"]: e for e in state.events}

    state.vertices = set(id2e.keys())
    state.edges = set()
    state.parent_edges = set()
    for e in state.events:
        for j in e.get("justifies", []):
            if j not in state.vertices:
                msg = f"Event {e['id']} justifies unknown event {j}"
                raise SystemExit(msg)
            state.edges.add((e["id"], j))
        for p in e.get("parents", []):
            if p in state.vertices:
                state.parent_edges.add((p, e["id"]))

    weights = cfg["weights"]
    total = weights["w_g"] + weights["w_i"] + weights["w_r"]
    if abs(total - 1.0) > 1e-6:
        raise SystemExit(
            f"Weights must sum to 1 (w_g + w_i + w_r = {total})"
        )
    tau = cfg["tau"]

    G = dia_graph(state)
    R = dia_replay(state)
    info = dia_info(state)
    D = weights["w_g"] * G + weights["w_i"] * info + weights["w_r"] * R

    result = {"graph": G, "replay": R, "info": info, "dia": D}

    mode = "RUN"
    if not replay_ok(state):
        mode = "HOLD"
    else:
        if D < prev_dia - tau:
            mode = "SAFE"

    result["mode"] = mode

    return result


def main(
    events_path: str,
    cfg_path: str,
    prev_dia: float = 1.0,
    json_out: str | None = None,
) -> dict:
    """Compute DIA metrics from the given event and config files."""

    with open(events_path, "r") as f:
        data = json.load(f)
    with open(cfg_path, "r") as f:
        cfg = json.load(f)

    result = compute_metrics(
        data["events"],
        cfg,
        prev_dia=prev_dia,
        schema_dir=Path(cfg_path).resolve().parent,
    )

    if json_out:
        with open(json_out, "w") as f:
            json.dump(result, f)
    else:
        print("DIA_graph =", round(result["graph"], 4))
        print("DIA_replay =", round(result["replay"], 4))
        print("DIA_info  =", round(result["info"], 4))
        print("DIA       =", round(result["dia"], 4))
        print("mode =", result["mode"])

    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Compute DIA metrics")
    parser.add_argument("events_path", help="Path to events JSON file")
    parser.add_argument("cfg_path", help="Path to configuration JSON file")
    parser.add_argument(
        "--json-out", dest="json_out", help="Write metrics to JSON file"
    )
    parser.add_argument(
        "--prev-dia",
        dest="prev_dia",
        type=float,
        default=1.0,
        help="Previous DIA value used for mode selection",
    )
    args = parser.parse_args()
    main(
        args.events_path,
        args.cfg_path,
        prev_dia=args.prev_dia,
        json_out=args.json_out,
    )
