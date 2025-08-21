# DIA — Density of Imputable (Audit) traces

Three computable definitions:

1) **DIA_graph** (causal justification density)  
Let G = (V, E) be the causal graph over events in L. Then:  
`DIA_graph = |E_justified| / max(|V|, 1)`  
Policy: Early-Stop if ΔDIA_graph < τ_graph over a rolling window.

2) **DIA_info** (recoverable information fraction)  
`DIA_info = (H(E) - H(E|S)) / max(H(E), ε)`

3) **DIA_replay** (empirical replay success)  
`DIA_replay = Pr[ replay(L_window) == S_window ]`

**DIAGuard** passes only if chosen DIA metric does not drop below threshold.
