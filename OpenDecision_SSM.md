# OpenDecision-SSM (conservative decision pipeline)

**Inputs:** Evidence_bundle, hypotheses H1..Hm, RISK ∈ {critical, high, medium, low}, N_guard.  
**Pre-register plan.** Run N_guard simulations; collect p-values.

**Correction:**  
- If RISK ∈ {critical, high}: **Holm** (FWER).  
- Else: **Benjamini–Hochberg** (FDR).

Permit only if effect size ≥ min threshold **AND** corrected tests support it.  
Emit full audit (seed, code hash, configs, results).  
Typical params: α=0.005 (critical), q=0.01 (low/medium), N_guard=1000.
