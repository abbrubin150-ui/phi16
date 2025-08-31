"""Simple event ledger with hash-chain persistence."""

from __future__ import annotations

import json
import time
import hashlib
from pathlib import Path
from typing import Iterable

from sim_replay import StreamingReplay, compute_metrics


def hash_block(block: dict) -> str:
    """Return SHA256 hash of ``block``."""

    payload = json.dumps(block, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def load_ledger(path: str | Path) -> dict:
    p = Path(path)
    if p.exists():
        return json.loads(p.read_text())
    return {"header": {"last_hash": "", "last_dia": 1.0, "mode": "RUN"}, "blocks": []}


def save_ledger(ledger: dict, path: str | Path) -> None:
    Path(path).write_text(json.dumps(ledger))


def _check_writable(header: dict, cfg: dict) -> None:
    mode = header.get("mode", "RUN")
    invariants = set(cfg.get("invariants", []))
    if mode == "HOLD" and "NoWriteInHold" in invariants:
        raise SystemExit("Writes not allowed while in HOLD mode")
    if mode == "SAFE" and "NoWriteInSAFE" in invariants:
        raise SystemExit("Writes not allowed while in SAFE mode")


def append_stream(
    path: str | Path,
    events: Iterable[dict],
    cfg: dict,
    schema_dir: str | Path | None = None,
) -> dict:
    """Append ``events`` using :class:`StreamingReplay`."""

    ledger = load_ledger(path)
    _check_writable(ledger["header"], cfg)

    sr = StreamingReplay(cfg, schema_dir=schema_dir)
    sr.load(ledger["blocks"], prev_hash=ledger["header"]["last_hash"])
    sr.prev_dia = ledger["header"]["last_dia"]
    sr.prev_mode = ledger["header"]["mode"]
    last_hash = sr._head_hash or ""

    for ev in events:
        sr.add_event(ev)
        block = {"data": ev, "prev_hash": last_hash, "ts": time.time()}
        last_hash = hash_block(block)
        sr._head_hash = last_hash
        ledger["blocks"].append(block)

    metrics = sr.metrics()
    ledger["header"].update(
        {"last_hash": last_hash, "last_dia": metrics["dia"], "mode": metrics["mode"]}
    )
    save_ledger(ledger, path)
    return metrics


def append_batch(
    path: str | Path,
    events: Iterable[dict],
    cfg: dict,
    schema_dir: str | Path | None = None,
) -> dict:
    """Append ``events`` recomputing metrics in batch."""

    ledger = load_ledger(path)
    _check_writable(ledger["header"], cfg)

    existing = [b["data"] for b in ledger["blocks"]]
    all_events = existing + list(events)
    metrics = compute_metrics(
        all_events,
        cfg,
        prev_dia=ledger["header"]["last_dia"],
        prev_mode=ledger["header"]["mode"],
        schema_dir=schema_dir,
    )

    last_hash = ledger["header"]["last_hash"]
    for ev in events:
        block = {"data": ev, "prev_hash": last_hash, "ts": time.time()}
        last_hash = hash_block(block)
        ledger["blocks"].append(block)

    ledger["header"].update(
        {"last_hash": last_hash, "last_dia": metrics["dia"], "mode": metrics["mode"]}
    )
    save_ledger(ledger, path)
    return metrics


def replay_stream(
    path: str | Path,
    cfg: dict,
    schema_dir: str | Path | None = None,
) -> dict:
    """Replay ledger verifying hash chain using :class:`StreamingReplay`."""

    ledger = load_ledger(path)
    sr = StreamingReplay(cfg, schema_dir=schema_dir)
    sr.load(ledger["blocks"], prev_hash=ledger["header"]["last_hash"])
    return sr.metrics()


def replay_batch(
    path: str | Path,
    cfg: dict,
    schema_dir: str | Path | None = None,
) -> dict:
    """Replay ledger in batch verifying the hash chain."""

    ledger = load_ledger(path)
    last = None
    for blk in ledger["blocks"]:
        if last is not None and blk["prev_hash"] != last:
            raise SystemExit("Hash chain validation failed")
        last = hash_block(blk)
    if ledger["header"]["last_hash"] and last != ledger["header"]["last_hash"]:
        raise SystemExit("Ledger head hash mismatch")
    events = [b["data"] for b in ledger["blocks"]]
    return compute_metrics(events, cfg, schema_dir=schema_dir)

