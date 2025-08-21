# Φ-16: minimal, runnable scaffolding

This repo contains a minimal TLC-friendly TLA+ skeleton and engineering artifacts
for the Φ-16 architecture (R-invariant, AND-level 0+, 3⊥+1, Silence-Hold).

## Files
- `Phi16.tla` — core spec (finite, abstract).
- `Phi16.cfg` — small TLC config.
- `NAND_only_policy.yaml` — NAND-only lint/verification policy (HW + SW IR).
- `DIA_metrics.md` — quantitative DIA definitions and guards.
- `OpenDecision_SSM.md` — conservative decision pipeline (Holm/BH, N_guard).
- `phi16_ascii_arch.txt` — ASCII architecture/flow.
- `examples/events.json` — tiny sample ledger.
- `sim_replay.py` — reference script for DIA metrics.

## Run TLC
1. Open `Phi16.tla` with TLA+ Toolbox, load `Phi16.cfg`, run model checking.

## Run DIA toy script
```bash
python3 sim_replay.py
```
