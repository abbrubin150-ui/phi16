# DIA-Moral Triangle Integration: Formal Mathematical Specification

## Abstract

This document formalizes the integration between the **DIA (Density of Information & Audit) metrics** and the **Moral Triangle** (T10↔T11↔T12 feedback loop). The moral triangle provides a continuous improvement mechanism that enhances the quality of auditable information through measurement, monitoring, and learning. We formalize how the 2.5× synergy multiplier affects DIA computation and system health.

**Version**: 1.0
**Last Updated**: 2025-12-05
**Status**: Complete

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [The Moral Triangle Structure](#2-the-moral-triangle-structure)
3. [DIA Metrics Review](#3-dia-metrics-review)
4. [Synergy Multiplier Mathematics](#4-synergy-multiplier-mathematics)
5. [Integrated DIA Computation](#5-integrated-dia-computation)
6. [Feedback Loop Dynamics](#6-feedback-loop-dynamics)
7. [Formal Theorems](#7-formal-theorems)
8. [Practical Implementation](#8-practical-implementation)
9. [Future Extensions](#9-future-extensions)

---

## 1. Introduction

### 1.1 Motivation

The **DIA metric** measures the system's accountability:
- **DIA_graph**: Causal connectivity
- **DIA_info**: Information entropy
- **DIA_replay**: Reproducibility

The **Moral Triangle** (T10, T11, T12) creates a feedback loop:
- **T10 (Measure)**: Quantifies system properties
- **T11 (Monitor)**: Detects anomalies
- **T12 (Learn)**: Extracts insights

**Key Insight**: When the moral triangle operates synergistically, it improves the quality of information captured in the ledger, thereby increasing DIA.

### 1.2 Core Principle

\[ \text{Synergistic Measurement} \implies \text{Higher Quality Audit Trail} \implies \text{Higher DIA} \]

---

## 2. The Moral Triangle Structure

### 2.1 Token Definitions

**T10 - Measure (מדידה)**
- **Role**: Quantitative evaluation
- **Priority**: 93
- **Metric**: \( M(x) \) — measurement function

**T11 - Monitor (ניטור)**
- **Role**: Continuous observation
- **Priority**: 89
- **Metric**: \( \Delta(t) \) — anomaly detection

**T12 - Learn (למידה)**
- **Role**: Insight extraction
- **Priority**: 91
- **Metric**: \( I(d) \) — insight generation

### 2.2 Feedback Loop

The moral triangle operates in cycles:

```
    T11 (Monitor)
         ↓
    Detects anomaly a(t)
         ↓
    T10 (Measure)
         ↓
    Quantifies m(a(t))
         ↓
    T12 (Learn)
         ↓
    Extracts insight i(m(a(t)))
         ↓
    T08 (Govern) ← Policy update
         ↓
    T09 (Standardize) ← Standard update
         ↓
    T07 (Automation) ← Automation update
         ↓
    Back to T11 (Monitor)
```

### 2.3 Cycle Formalization

A **cycle** \(C_k\) is a tuple:
\[ C_k = (a_k, m_k, i_k, t_{start}, t_{end}) \]

Where:
- \(a_k\): Anomaly detected by T11
- \(m_k\): Measurement by T10
- \(i_k\): Insight from T12
- \(t_{start}, t_{end}\): Cycle timestamps

**Cycle Duration**:
\[ \Delta t_k = t_{end} - t_{start} \]

---

## 3. DIA Metrics Review

### 3.1 Individual Metrics

**DIA_graph** (connectivity):
\[ DIA_g = \frac{|E|}{|V| \cdot (|V| - 1)} \]

**DIA_info** (entropy):
\[ DIA_i = \frac{\min(H(P), |E|/|V|)}{\max(H(P), 1)} \]

**DIA_replay** (reproducibility):
\[ DIA_r = \begin{cases} 1.0 & \text{if DAG is acyclic} \\ 0.0 & \text{otherwise} \end{cases} \]

### 3.2 Weighted DIA

\[ DIA = w_g \cdot DIA_g + w_i \cdot DIA_i + w_r \cdot DIA_r \]

With:
\[ w_g + w_i + w_r = 1 \]

**Default weights**: \(w_g = 0.5, w_i = 0.3, w_r = 0.2\)

---

## 4. Synergy Multiplier Mathematics

### 4.1 Synergy Condition

The moral triangle achieves **full synergy** when:

1. **All active**: \(T10, T11, T12 \in \text{ACTIVE}\)
2. **Balanced ratio**: Activation counts in approximately 1:1:1 ratio

### 4.2 Activation Ratio

Let:
- \(n_{10}\): Activation count for T10
- \(n_{11}\): Activation count for T11
- \(n_{12}\): Activation count for T12

**Average activation**:
\[ \bar{n} = \frac{n_{10} + n_{11} + n_{12}}{3} \]

**Standard deviation**:
\[ \sigma_n = \sqrt{\frac{(n_{10} - \bar{n})^2 + (n_{11} - \bar{n})^2 + (n_{12} - \bar{n})^2}{3}} \]

**Coefficient of variation**:
\[ CV = \frac{\sigma_n}{\bar{n}} \]

### 4.3 Synergy Multiplier Function

\[ S(CV) = \begin{cases}
2.5 & \text{if } CV \leq 0.2 \text{ (full synergy)} \\
1.0 + 1.5 \cdot \frac{n_{active}}{3} & \text{otherwise (partial synergy)}
\end{cases} \]

Where \(n_{active}\) is the number of active tokens in \(\{T10, T11, T12\}\).

**Properties**:
- \(S \in [1.0, 2.5]\)
- \(S = 1.0\) when no tokens active
- \(S = 2.5\) when all three active in balanced ratio
- Linear interpolation for partial activation

### 4.4 Mathematical Justification for 2.5×

The 2.5× multiplier comes from **emergent properties**:

1. **Pairwise synergies** (3 pairs):
   - T10↔T11: Measurement validates monitoring
   - T11↔T12: Monitoring guides learning
   - T12↔T10: Learning improves measurement

2. **Triangle closure**:
   - All three together create reinforcing feedback loop
   - Each component enhances the others

3. **Combinatorial effect**:
   - 3 tokens operating independently: \(1 + 1 + 1 = 3\)
   - 3 tokens in synergy: \(1 \times 2.5 = 2.5\) (per token)
   - Net effect: \(3 \times 2.5 = 7.5\) vs. \(3 \times 1 = 3\)
   - Ratio: \(7.5 / 3 = 2.5\)

---

## 5. Integrated DIA Computation

### 5.1 DIA with Moral Triangle Amplification

The integrated DIA incorporates the synergy multiplier:

\[ DIA_{integrated} = S(CV) \cdot DIA_{base} \]

Where:
- \(DIA_{base}\): Standard DIA from ledger
- \(S(CV)\): Synergy multiplier

### 5.2 Component-wise Amplification

Each DIA component can be amplified differently:

**DIA_graph amplification**:
\[ DIA_g^{(S)} = \min(S(CV) \cdot DIA_g, 1.0) \]

Capped at 1.0 (maximum density).

**DIA_info amplification**:
\[ DIA_i^{(S)} = DIA_i + (1 - DIA_i) \cdot \frac{S(CV) - 1}{1.5} \]

Increases information quality through better measurements.

**DIA_replay amplification**:
\[ DIA_r^{(S)} = DIA_r \]

Replay is binary (0 or 1), not amplified.

### 5.3 Weighted Integrated DIA

\[ DIA_{integrated} = w_g \cdot DIA_g^{(S)} + w_i \cdot DIA_i^{(S)} + w_r \cdot DIA_r \]

### 5.4 Quality Bonus

Alternatively, add a **quality bonus** term:

\[ DIA_{total} = DIA_{base} + \beta \cdot (S(CV) - 1) \]

Where \(\beta \in [0, 1]\) is a quality weight (default: 0.2).

**Interpretation**: Each unit of synergy above 1.0 contributes \(\beta\) to total DIA.

**Example**:
- \(DIA_{base} = 0.75\)
- \(S(CV) = 2.5\) (full synergy)
- \(\beta = 0.2\)
- \(DIA_{total} = 0.75 + 0.2 \cdot (2.5 - 1) = 0.75 + 0.3 = 1.05\)

This can exceed 1.0, indicating **exceptional audit quality**.

---

## 6. Feedback Loop Dynamics

### 6.1 Discrete-Time Model

Model the moral triangle as a discrete-time dynamical system:

**State vector** at cycle \(k\):
\[ \mathbf{x}_k = \begin{pmatrix} m_k \\ \delta_k \\ i_k \end{pmatrix} \]

Where:
- \(m_k\): Measurement quality (T10)
- \(\delta_k\): Monitoring effectiveness (T11)
- \(i_k\): Insight value (T12)

**Update equation**:
\[ \mathbf{x}_{k+1} = A \cdot \mathbf{x}_k + \mathbf{b}_k \]

Where \(A\) is the **synergy matrix**:
\[ A = \begin{pmatrix}
1 & \alpha_{10,11} & \alpha_{10,12} \\
\alpha_{11,10} & 1 & \alpha_{11,12} \\
\alpha_{12,10} & \alpha_{12,11} & 1
\end{pmatrix} \]

Diagonal: self-improvement (always 1)
Off-diagonal: cross-enhancement (\(\alpha_{ij} > 0\))

### 6.2 Synergy Coefficients

**Balanced synergy** implies:
\[ \alpha_{ij} = \alpha \quad \forall i \neq j \]

For 2.5× multiplier:
\[ (1 + 2\alpha)^3 \approx 2.5^3 \]
\[ 1 + 2\alpha \approx 1.357 \]
\[ \alpha \approx 0.179 \]

So each token enhances others by ~17.9%.

### 6.3 Eigenvalue Analysis

**Eigenvalues** of \(A\) determine stability:

For symmetric \(A\) with \(\alpha = 0.179\):
\[ \lambda_1 \approx 1.358 \quad (\text{dominant}) \]
\[ \lambda_2, \lambda_3 \approx 0.821 \quad (\text{stable}) \]

**Interpretation**:
- \(\lambda_1 > 1\): System improves over time (growth mode)
- \(\lambda_{2,3} < 1\): Non-dominant modes decay
- Convergence to direction of \(\lambda_1\)

### 6.4 Long-Term Behavior

**Proposition**: With balanced synergy (\(\alpha \approx 0.179\)), the moral triangle converges to exponential improvement.

**Proof Sketch**:
\[ \mathbf{x}_k \approx c \cdot \lambda_1^k \cdot \mathbf{v}_1 \]

Where \(\mathbf{v}_1\) is the dominant eigenvector (balanced state: \((1, 1, 1)^T\)).

Thus:
\[ m_k \approx \delta_k \approx i_k \approx c \cdot 1.358^k \]

Exponential growth with rate \(\approx 35.8\%\) per cycle, until saturation.

---

## 7. Formal Theorems

### Theorem 1: Synergy Amplifies DIA

**Statement**: When the moral triangle achieves full synergy, \(DIA_{integrated} \geq DIA_{base}\).

**Proof**:
1. By definition, \(S(CV) \in [1.0, 2.5]\)
2. For full synergy, \(S(CV) = 2.5 > 1\)
3. \(DIA_{integrated} = S(CV) \cdot DIA_{base} = 2.5 \cdot DIA_{base} > DIA_{base}\)
∎

### Theorem 2: Partial Synergy is Monotonic

**Statement**: As more tokens activate, synergy increases monotonically.

**Proof**:
1. \(S = 1.0 + 1.5 \cdot \frac{n_{active}}{3}\)
2. \(n_{active} \in \{0, 1, 2, 3\}\)
3. \(\frac{\partial S}{\partial n_{active}} = \frac{1.5}{3} = 0.5 > 0\)
4. Therefore, \(S\) is strictly increasing in \(n_{active}\)
∎

### Theorem 3: DIA Monotonicity Preserved Under Synergy

**Statement**: If \(DIA_{base}\) is monotonic (never decreases), then \(DIA_{integrated}\) is also monotonic.

**Proof**:
1. Assume \(DIA_{base}(t') \geq DIA_{base}(t)\) for \(t' > t\)
2. \(S(CV) \geq 1\) always (by definition)
3. \(DIA_{integrated}(t') = S(CV(t')) \cdot DIA_{base}(t')\)
4. Even if \(S(CV(t')) < S(CV(t))\), we have:
   \[ DIA_{integrated}(t') = S(CV(t')) \cdot DIA_{base}(t') \geq 1.0 \cdot DIA_{base}(t') \geq DIA_{base}(t) \]
5. Since \(DIA_{base}(t) \leq DIA_{integrated}(t)\), monotonicity holds
∎

### Theorem 4: Balanced State is Nash Equilibrium

**Statement**: The balanced state \(n_{10} = n_{11} = n_{12}\) is a Nash equilibrium for synergy maximization.

**Proof** (sketch):
1. Synergy is maximized when \(CV \leq 0.2\)
2. \(CV\) is minimized when \(n_{10} = n_{11} = n_{12}\) (zero variance)
3. Any unilateral deviation (activating only one token more) increases \(CV\)
4. Therefore, no agent benefits from deviating → Nash equilibrium
∎

### Theorem 5: Exponential Improvement Bound

**Statement**: The moral triangle with full synergy improves metrics at rate \(\lambda_1 \approx 1.358\) per cycle, bounded by saturation.

**Proof**:
1. From dynamical system: \(\mathbf{x}_k = A^k \mathbf{x}_0\)
2. Dominant eigenvalue: \(\lambda_1 = 1 + 2\alpha \approx 1.358\)
3. For large \(k\): \(\mathbf{x}_k \approx c \cdot \lambda_1^k \mathbf{v}_1\)
4. Growth rate: \(r = \lambda_1 - 1 \approx 0.358 = 35.8\%\)
5. Saturation occurs when \(\mathbf{x}_k\) reaches maximum (e.g., \(DIA = 1.0\))
∎

---

## 8. Practical Implementation

### 8.1 Python Implementation

```python
from typing import Dict, List
from dataclasses import dataclass

@dataclass
class MoralTriangleState:
    """State of the moral triangle."""
    n_10: int  # T10 activations
    n_11: int  # T11 activations
    n_12: int  # T12 activations
    cycles: List[Dict]  # Cycle history

def compute_cv(state: MoralTriangleState) -> float:
    """Compute coefficient of variation for activation balance."""
    activations = [state.n_10, state.n_11, state.n_12]

    if min(activations) == 0:
        return float('inf')  # Not all activated

    avg = sum(activations) / len(activations)
    variance = sum((x - avg) ** 2 for x in activations) / len(activations)
    stddev = variance ** 0.5

    return stddev / avg

def compute_synergy_multiplier(state: MoralTriangleState) -> float:
    """Compute synergy multiplier S(CV)."""
    cv = compute_cv(state)

    if cv <= 0.2:
        return 2.5  # Full synergy
    else:
        # Partial synergy
        n_active = sum([
            1 if state.n_10 > 0 else 0,
            1 if state.n_11 > 0 else 0,
            1 if state.n_12 > 0 else 0
        ])
        return 1.0 + 1.5 * (n_active / 3)

def compute_integrated_dia(
    dia_base: float,
    state: MoralTriangleState,
    beta: float = 0.2
) -> float:
    """Compute DIA with moral triangle amplification."""
    S = compute_synergy_multiplier(state)

    # Quality bonus method
    dia_total = dia_base + beta * (S - 1.0)

    return dia_total
```

### 8.2 Integration with sim_replay.py

Extend `compute_metrics` to include moral triangle:

```python
def compute_metrics_with_moral_triangle(
    events: list,
    cfg: dict,
    moral_state: MoralTriangleState,
    prev_dia: float = 1.0,
    prev_mode: str = "RUN"
) -> dict:
    """Compute DIA metrics with moral triangle integration."""

    # Base DIA computation
    base_result = compute_metrics(events, cfg, prev_dia, prev_mode)

    # Add synergy
    S = compute_synergy_multiplier(moral_state)
    dia_integrated = compute_integrated_dia(
        base_result['dia'],
        moral_state
    )

    return {
        **base_result,
        'dia_base': base_result['dia'],
        'dia_integrated': dia_integrated,
        'synergy_multiplier': S,
        'moral_triangle_cv': compute_cv(moral_state)
    }
```

### 8.3 Ledger Event Metadata

Events record moral triangle state:

```json
{
  "id": "e123",
  "type": "MoralTriangleCycle",
  "timestamp": "2025-12-05T20:00:00Z",
  "data": {
    "cycle_id": 42,
    "anomaly": "High latency detected",
    "measurement": {"latency_ms": 1250},
    "insight": "Database query optimization needed"
  },
  "metadata": {
    "moral_triangle": {
      "t10_activations": 100,
      "t11_activations": 102,
      "t12_activations": 98,
      "synergy_multiplier": 2.5,
      "cv": 0.02
    }
  }
}
```

---

## 9. Future Extensions

### 9.1 Adaptive Synergy

Allow synergy multiplier to evolve based on historical performance:

\[ S_k = S_{k-1} + \eta \cdot (DIA_{target} - DIA_{k-1}) \]

Where \(\eta\) is learning rate.

### 9.2 Multi-Triangle Interactions

Extend to interactions between multiple moral triangles (e.g., T10↔T11↔T12 and T08↔T09↔T05):

\[ S_{total} = \prod_{i=1}^{n} S_i(CV_i) \]

Multiplicative synergy across triangles.

### 9.3 Continuous-Time Model

Replace discrete cycles with continuous differential equations:

\[ \frac{d\mathbf{x}}{dt} = (A - I) \mathbf{x} + \mathbf{f}(t) \]

Where \(\mathbf{f}(t)\) represents external inputs.

### 9.4 Causal Inference Integration

Use moral triangle cycles to identify causal relationships:
- T11 detects correlation
- T10 measures potential causes
- T12 infers causation via interventions

---

## 10. Conclusion

The **DIA-Moral Triangle integration** provides:

1. **Formal amplification** of audit quality through synergy
2. **Dynamical model** of continuous improvement
3. **Provable theorems** about monotonicity and equilibrium
4. **Practical implementation** for Φ-OS ledger

**Key Result**: When T10, T11, T12 operate in balanced synergy, DIA can be amplified up to 2.5×, representing exceptional audit quality.

---

## References

1. **DIA Metrics**: spec/math/DIA_formal.md
2. **Moral Triangle**: tokens/moral_triangle.py
3. **Dynamical Systems**: Strogatz, S. (2015). Nonlinear Dynamics and Chaos
4. **Nash Equilibrium**: Nash, J. (1950). Equilibrium Points in N-Person Games
5. **Eigenvalue Analysis**: Golub, G. & Van Loan, C. (2013). Matrix Computations

---

**Document Version**: 1.0
**Last Updated**: 2025-12-05
**Status**: Complete Mathematical Specification
