# DIA Policy

`DIA` (Directed Integrity Attestation) measures the structural health of the
ledger's justification graph.  In this stage we employ a discrete metric based
on replayability and simply model it as the ledger length.  The model
parameter `Tau` bounds the allowed drop in this metric during validation.

* **Metric**: `DIA(L) == Len(L)` (placeholder for `DIA_replay`).
* **Threshold τ (`Tau`)**: maximum allowed decrease on append. `Tau = 0`
  prohibits any regression.

During the `Validate` step we only accept a proposal `prop` if
`DIA(L ⧺ <prop>) ≥ DIA(L) − Tau`.  This forms a concrete `DIAGuard` and
prevents commits that would regress the ledger's DIA score beyond the
threshold.
