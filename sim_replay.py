import argparse
import json
import hashlib
from collections import defaultdict, deque
from dataclasses import dataclass, field
from math import log2, isclose
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

    Raises:
        ValueError: If probabilities are negative or do not sum to 1.
    """

    probabilities = list(p)
    if any(pi < 0 for pi in probabilities):
        raise ValueError("probabilities must be non-negative")
    total = sum(probabilities)
    if not isclose(total, 1.0):
        raise ValueError("probabilities must sum to 1.0")
    return -sum(pi * log2(pi) for pi in probabilities if pi > 0)


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


def block_hash(block: dict) -> str:
    """Return the SHA256 hash of ``block``."""

    payload = json.dumps(block, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def _as_int(eid: object) -> int | None:
    """Return ``int(eid)`` if ``eid`` is digit-only, else ``None``.

    The function accepts both integer and string identifiers. If the value is a
    string consisting solely of decimal digits, it is converted to ``int``.
    Non-numeric identifiers result in ``None`` so callers can fall back to
    lexicographic comparisons.
    """

    s = str(eid)
    return int(s) if s.isdigit() else None


def _load_schemas(schema_dir: str | Path | None) -> tuple[dict, dict]:
    """Return the configuration and events schemas."""

    schema_base = (
        Path(schema_dir)
        if schema_dir is not None
        else Path(__file__).resolve().parent / "spec" / "ssot"
    )
    with open(schema_base / "phi16.schema.json", "r") as f:
        schema = json.load(f)
    with open(schema_base / "events.schema.json", "r") as f:
        events_schema = json.load(f)
    return schema, events_schema


def _validate_and_prepare(
    events: list,
    cfg: dict,
    prev_mode: str,
    schema: dict | None = None,
    events_schema: dict | None = None,
    schema_dir: str | Path | None = None,
) -> tuple[ReplayState, dict, float]:
    """Return a prepared ``ReplayState`` after validating inputs.

    The helper consolidates common validation and graph construction logic used
    by both :func:`compute_metrics` and :meth:`StreamingReplay.metrics`.

    Args:
        events: Sequence of event dictionaries.
        cfg: Configuration dictionary.
        prev_mode: Previous operating mode.
        schema: Pre-loaded configuration schema.
        events_schema: Pre-loaded events schema.
        schema_dir: Directory from which to load schemas when not provided.

    Returns:
        A tuple ``(state, weights, tau)`` where ``state`` is a fully populated
        :class:`ReplayState`, ``weights`` is the validated weight mapping and
        ``tau`` the sensitivity threshold.
    """

    if schema is None or events_schema is None:
        schema, events_schema = _load_schemas(schema_dir)

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

    invariants = set(cfg.get("invariants", []))
    states = cfg.get("states", [])
    if prev_mode not in states:
        raise SystemExit(f"Unknown previous mode: {prev_mode}")
    if "NoWriteInHold" in invariants and prev_mode == "HOLD" and events:
        raise SystemExit("Writes not allowed while in HOLD mode")
    if "NoWriteInSAFE" in invariants and prev_mode == "SAFE" and events:
        raise SystemExit("Writes not allowed while in SAFE mode")

    state = ReplayState()
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

    prev_id: int | str | None = None
    for eid in ids:
        if prev_id is not None and "AppendOnlyMonotone" in invariants:
            prev_int = _as_int(prev_id)
            curr_int = _as_int(eid)
            if prev_int is not None and curr_int is not None:
                if curr_int <= prev_int:
                    raise SystemExit(
                        f"Event IDs must be monotone increasing: {eid} after {prev_id}"
                    )
            else:
                if str(eid) <= str(prev_id):
                    raise SystemExit(
                        f"Event IDs must be monotone increasing: {eid} after {prev_id}"
                    )
        prev_id = eid

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

    return state, weights, tau


class StreamingReplay:
    """Incrementally validate events and compute DIA metrics.

    The class enforces configured invariants on every appended event and can be
    used to process large ledgers without materialising the full history at
    once.
    """

    def __init__(
        self,
        cfg: dict,
        prev_dia: float = 1.0,
        prev_mode: str = "RUN",
        schema_dir: str | Path | None = None,
    ) -> None:
        self.state = ReplayState()
        self.cfg = cfg
        self.prev_dia = prev_dia
        self.prev_mode = prev_mode
        schema, events_schema = _load_schemas(schema_dir)

        try:
            jsonschema.validate(cfg, schema)
        except ValidationError as e:
            print(f"Configuration error: {e.message}")
            raise SystemExit(1)

        self.schema = schema
        self.events_schema = events_schema
        self.invariants = set(cfg.get("invariants", []))
        self.states = cfg.get("states", [])
        if prev_mode not in self.states:
            raise SystemExit(f"Unknown previous mode: {prev_mode}")

        self._last_id: int | str | None = None
        self._head_hash: str | None = None

    # ------------------------------------------------------------------
    def load(self, blocks: list, prev_hash: str | None = None) -> None:
        """Load ``blocks`` validating the hash chain."""

        last = None
        for blk in blocks:
            if last is not None and blk["prev_hash"] != last:
                raise SystemExit("Hash chain validation failed")
            self.add_event(blk["data"])
            last = block_hash(blk)
        self._head_hash = last
        if prev_hash not in (None, "") and prev_hash != last:
            raise SystemExit("Ledger head hash mismatch")

    # ------------------------------------------------------------------
    def add_event(self, event: dict) -> None:
        """Append ``event`` to the log enforcing configured invariants."""

        if "NoWriteInHold" in self.invariants and self.prev_mode == "HOLD":
            raise SystemExit("Writes not allowed while in HOLD mode")
        if "NoWriteInSAFE" in self.invariants and self.prev_mode == "SAFE":
            raise SystemExit("Writes not allowed while in SAFE mode")

        try:
            jsonschema.validate({"events": [event]}, self.events_schema)
        except ValidationError as e:
            print(f"Event file error: {e.message}")
            raise SystemExit(1)

        eid = event["id"]
        if self._last_id is not None and "AppendOnlyMonotone" in self.invariants:
            prev_int = _as_int(self._last_id)
            curr_int = _as_int(eid)
            if prev_int is not None and curr_int is not None:
                if curr_int <= prev_int:
                    raise SystemExit(
                        f"Event IDs must be monotone increasing: {eid} after {self._last_id}"
                    )
            else:
                if str(eid) <= str(self._last_id):
                    raise SystemExit(
                        f"Event IDs must be monotone increasing: {eid} after {self._last_id}"
                    )

        if eid in self.state.vertices:
            raise SystemExit(f"Duplicate event ID: {eid}")
        self._last_id = eid
        self.state.events.append(event)
        self.state.vertices.add(eid)

        for j in event.get("justifies", []):
            self.state.edges.add((eid, j))
        for p in event.get("parents", []):
            if p in self.state.vertices:
                self.state.parent_edges.add((p, eid))

    # ------------------------------------------------------------------
    def metrics(self) -> dict:
        """Return the DIA metrics for the current replay state."""

        state, weights, tau = _validate_and_prepare(
            self.state.events,
            self.cfg,
            self.prev_mode,
            schema=self.schema,
            events_schema=self.events_schema,
        )
        self.state = state

        G = dia_graph(state)
        R = dia_replay(state)
        info = dia_info(state)
        D = weights["w_g"] * G + weights["w_i"] * info + weights["w_r"] * R

        mode = "RUN"
        if not replay_ok(state):
            mode = "HOLD"
        elif D < self.prev_dia - tau:
            mode = "SAFE"

        return {"graph": G, "replay": R, "info": info, "dia": D, "mode": mode}


def compute_metrics(
    events: list,
    cfg: dict,
    prev_dia: float = 1.0,
    prev_mode: str = "RUN",
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
    state, weights, tau = _validate_and_prepare(
        events,
        cfg,
        prev_mode,
        schema_dir=schema_dir,
    )

    G = dia_graph(state)
    R = dia_replay(state)
    info = dia_info(state)
    D = weights["w_g"] * G + weights["w_i"] * info + weights["w_r"] * R

    result = {"graph": G, "replay": R, "info": info, "dia": D}

    mode = "RUN"
    if not replay_ok(state):
        mode = "HOLD"
    elif D < prev_dia - tau:
        mode = "SAFE"

    result["mode"] = mode

    return result


def main(
    events_path: str,
    cfg_path: str,
    prev_dia: float = 1.0,
    prev_mode: str = "RUN",
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
        prev_mode=prev_mode,
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
    parser.add_argument(
        "--prev-mode",
        dest="prev_mode",
        default="RUN",
        help="Previous mode used for invariant checks",
    )
    args = parser.parse_args()
    main(
        args.events_path,
        args.cfg_path,
        prev_dia=args.prev_dia,
        prev_mode=args.prev_mode,
        json_out=args.json_out,
    )
