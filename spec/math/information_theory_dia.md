# Information Theory Foundations for DIA Metrics

## Abstract

This document provides comprehensive **information-theoretic foundations** for the DIA (Density of Information & Audit) metrics. We extend Shannon's information theory to formalize audit quality, exploring entropy, mutual information, Kolmogorov complexity, and information-geometric perspectives on the append-only ledger.

**Version**: 1.0
**Last Updated**: 2025-12-05
**Status**: Complete

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [Shannon Entropy Foundations](#2-shannon-entropy-foundations)
3. [Mutual Information and Causality](#3-mutual-information-and-causality)
4. [Kolmogorov Complexity](#4-kolmogorov-complexity)
5. [Information Geometry](#5-information-geometry)
6. [DIA_info Metric Formalization](#6-dia_info-metric-formalization)
7. [Entropy Rate of Ledger Growth](#7-entropy-rate-of-ledger-growth)
8. [Fisher Information for Audit Quality](#8-fisher-information-for-audit-quality)
9. [Algorithmic Information Theory](#9-algorithmic-information-theory)
10. [Practical Computation](#10-practical-computation)

---

## 1. Introduction

### 1.1 Why Information Theory for Audit?

**Audit Quality** ≈ **Information Richness**

A high-quality audit trail:
- Captures **diverse** event types (high entropy)
- Reveals **causal structure** (high mutual information)
- Is **irreducible** (high Kolmogorov complexity)
- Enables **precise inference** (high Fisher information)

### 1.2 Core Questions

1. How much **information** does the ledger contain?
2. How much **redundancy** vs. **signal**?
3. Can we **compress** the ledger losslessly?
4. How **sensitive** is the ledger to parameter changes?

---

## 2. Shannon Entropy Foundations

### 2.1 Discrete Entropy

For discrete random variable \(X\) with probability mass function \(p(x)\):

\[ H(X) = -\sum_{x \in \mathcal{X}} p(x) \log_2 p(x) \]

**Units**: bits (base-2 logarithm)

**Interpretation**: Average number of bits needed to encode \(X\).

### 2.2 Properties of Entropy

**Non-negativity**:
\[ H(X) \geq 0 \]

**Maximum Entropy**:
\[ H(X) \leq \log_2 |\mathcal{X}| \]

Equality when \(X\) is uniform: \(p(x) = \frac{1}{|\mathcal{X}|}\)

**Additivity** (for independent variables):
\[ H(X, Y) = H(X) + H(Y) \quad \text{if } X \perp\!\!\!\perp Y \]

**Subadditivity** (general):
\[ H(X, Y) \leq H(X) + H(Y) \]

### 2.3 Conditional Entropy

\[ H(Y \mid X) = \sum_{x} p(x) H(Y \mid X = x) \]

\[ H(Y \mid X) = H(X, Y) - H(X) \]

**Interpretation**: Uncertainty in \(Y\) after observing \(X\).

### 2.4 Joint Entropy

\[ H(X, Y) = -\sum_{x, y} p(x, y) \log_2 p(x, y) \]

**Chain Rule**:
\[ H(X, Y) = H(X) + H(Y \mid X) = H(Y) + H(X \mid Y) \]

### 2.5 Relative Entropy (KL Divergence)

\[ D_{KL}(p \| q) = \sum_{x} p(x) \log_2 \frac{p(x)}{q(x)} \]

**Properties**:
- \(D_{KL}(p \| q) \geq 0\)
- \(D_{KL}(p \| q) = 0 \iff p = q\)
- **Not symmetric**: \(D_{KL}(p \| q) \neq D_{KL}(q \| p)\)

**Interpretation**: Information lost when approximating \(p\) by \(q\).

---

## 3. Mutual Information and Causality

### 3.1 Mutual Information

\[ I(X; Y) = H(X) + H(Y) - H(X, Y) \]

\[ I(X; Y) = \sum_{x, y} p(x, y) \log_2 \frac{p(x, y)}{p(x) p(y)} \]

**Interpretation**: Information shared between \(X\) and \(Y\).

**Properties**:
- \(I(X; Y) \geq 0\)
- \(I(X; Y) = 0 \iff X \perp\!\!\!\perp Y\)
- **Symmetric**: \(I(X; Y) = I(Y; X)\)

### 3.2 Conditional Mutual Information

\[ I(X; Y \mid Z) = H(X \mid Z) + H(Y \mid Z) - H(X, Y \mid Z) \]

**Interpretation**: Information shared between \(X\) and \(Y\) **given** \(Z\).

### 3.3 Transfer Entropy (Causality Measure)

\[ TE_{Y \to X} = I(X_t; Y_{t-1} \mid X_{t-1}) \]

**Interpretation**: Information flow from \(Y\) to \(X\) over time.

**Connection to Causality**:
- \(TE_{Y \to X} > 0\): \(Y\) causally influences \(X\)
- \(TE_{Y \to X} = 0\): No causal influence

### 3.4 Application to Ledger

For events \(e_i, e_j\) in ledger:
\[ I(e_i; e_j) = \text{mutual information between event types} \]

High \(I(e_i; e_j)\): Strong causal linkage (justification or parent relationship)

**DIA_graph Connection**:
\[ DIA_{graph} \propto \sum_{(i,j) \in E} I(e_i; e_j) \]

---

## 4. Kolmogorov Complexity

### 4.1 Definition

The **Kolmogorov complexity** \(K(x)\) of string \(x\) is:

\[ K(x) = \min\{ |p| : U(p) = x \} \]

Where:
- \(U\): Universal Turing machine
- \(p\): Program that outputs \(x\)
- \(|p|\): Length of program \(p\)

**Interpretation**: Shortest program that generates \(x\).

### 4.2 Properties

**Incomputability**:
\[ K(x) \text{ is not computable (Theorem: Chaitin)} \]

**Upper Bound**:
\[ K(x) \leq |x| + c \]

(Can always write program that outputs \(x\) verbatim, plus constant overhead)

**Randomness**:
\[ K(x) \approx |x| \iff x \text{ is random} \]

**Compressibility**:
\[ K(x) \ll |x| \iff x \text{ is compressible} \]

### 4.3 Conditional Kolmogorov Complexity

\[ K(x \mid y) = \min\{ |p| : U(p, y) = x \} \]

**Interpretation**: Complexity of \(x\) given \(y\).

### 4.4 Algorithmic Mutual Information

\[ I_K(x : y) = K(x) + K(y) - K(x, y) \]

**Analogy to Shannon**:
\[ I_K(x : y) \approx I(X; Y) \]

### 4.5 Application to Ledger

**Ledger Complexity**:
\[ K(L) = \text{Shortest program to generate ledger } L \]

**High \(K(L)\)**: Ledger is information-rich, not redundant
**Low \(K(L)\)**: Ledger is compressible, repetitive

**DIA_info Connection**:
\[ DIA_{info} \propto \frac{K(L)}{|L|} \]

Normalized complexity (information density).

---

## 5. Information Geometry

### 5.1 Statistical Manifold

The space of probability distributions \(\mathcal{P}\) forms a **Riemannian manifold**.

**Metric**: Fisher information matrix \(g_{ij}\)

\[ ds^2 = \sum_{i,j} g_{ij} d\theta_i d\theta_j \]

### 5.2 Fisher Information Matrix

\[ g_{ij} = \mathbb{E}\left[ \frac{\partial \log p(x \mid \theta)}{\partial \theta_i} \frac{\partial \log p(x \mid \theta)}{\partial \theta_j} \right] \]

**Interpretation**: Sensitivity of distribution \(p\) to parameter changes.

### 5.3 Geodesic Distance

The **shortest path** between distributions \(p\) and \(q\) on manifold:

\[ d_{geo}(p, q) = \int_{\gamma} \sqrt{g_{ij} \dot{\theta}^i \dot{\theta}^j} \, dt \]

### 5.4 KL Divergence as Squared Distance

For small perturbations:
\[ D_{KL}(p_{\theta} \| p_{\theta + d\theta}) \approx \frac{1}{2} \sum_{i,j} g_{ij} d\theta_i d\theta_j \]

### 5.5 Application to Ledger

Model ledger event distribution as parameterized family:
\[ p(e \mid \theta) \]

**Fisher Information**:
\[ \mathcal{I}(\theta) = \text{sensitivity of event distribution to parameters} \]

High \(\mathcal{I}\): Small parameter changes → large distribution changes → high audit precision

---

## 6. DIA_info Metric Formalization

### 6.1 Event Type Distribution

Given ledger \(L = \langle e_1, \ldots, e_n \rangle\), define event type distribution:

\[ P(T) = \{ p_1, \ldots, p_k \} \]

Where:
- \(k\): Number of distinct event types
- \(p_i = \frac{n_i}{n}\): Proportion of type \(i\)

### 6.2 DIA_info as Normalized Entropy

\[ DIA_{info}(L) = \frac{H(T)}{H_{max}(T)} \]

Where:
\[ H(T) = -\sum_{i=1}^{k} p_i \log_2 p_i \]

\[ H_{max}(T) = \log_2 k \]

**Properties**:
- \(DIA_{info} \in [0, 1]\)
- \(DIA_{info} = 1\): Uniform distribution (maximum diversity)
- \(DIA_{info} = 0\): Single event type (no diversity)

### 6.3 Alternative: Joint Entropy with Graph

Incorporate causal structure:

\[ DIA_{info}^{(joint)}(L) = \frac{H(T, G)}{H_{max}(T, G)} \]

Where:
- \(T\): Event types
- \(G\): Causal graph edges

\[ H(T, G) = H(T) + H(G \mid T) \]

### 6.4 Conditional Formulation

\[ DIA_{info}^{(cond)}(L) = \frac{H(T \mid G)}{H(T)} \]

**Interpretation**: How much event type information remains after knowing graph structure.

**Low value**: Event types are predictable from graph (redundant)
**High value**: Event types are independent of graph (diverse)

### 6.5 Mutual Information Formulation

\[ DIA_{info}^{(MI)}(L) = \frac{I(T; G)}{H(T)} \]

**Interpretation**: Fraction of event type information explained by graph structure.

### 6.6 Extended Definition (Used in Φ-OS)

Combining entropy and edge density:

\[ DIA_{info}(L) = \frac{\min(H(T), |E| / |V|)}{\max(H(T), 1)} \]

**Rationale**:
- Numerator: Lesser of entropy and edge density (conservative)
- Denominator: Normalization by maximum entropy
- Ensures \(DIA_{info} \in [0, 1]\)

---

## 7. Entropy Rate of Ledger Growth

### 7.1 Entropy Rate Definition

For stochastic process \(\{X_t\}\):

\[ H_{\infty} = \lim_{n \to \infty} \frac{1}{n} H(X_1, \ldots, X_n) \]

**Interpretation**: Average information per event in the limit.

### 7.2 Stationary Processes

For stationary ergodic process:

\[ H_{\infty} = \lim_{n \to \infty} H(X_n \mid X_1, \ldots, X_{n-1}) \]

\[ H_{\infty} = H(X_\infty \mid X_{-\infty}^{-1}) \]

### 7.3 Ledger Entropy Rate

Model ledger as stochastic process where each event is a random variable:

\[ H_{\infty}(L) = \lim_{n \to \infty} \frac{1}{n} H(e_1, \ldots, e_n) \]

**High \(H_{\infty}\)**: Ledger continuously adds new, unpredictable information
**Low \(H_{\infty}\)**: Ledger is repetitive, compressible

### 7.4 Excess Entropy

\[ E_{excess} = \sum_{n=0}^{\infty} [H(X_n \mid X_0) - H_{\infty}] \]

**Interpretation**: Total information in past that informs future beyond immediate predecessor.

### 7.5 Application: DIA Monotonicity

**Theorem**: If \(H_{\infty}(L) > 0\), then \(DIA_{info}\) is non-decreasing in expectation.

**Proof Sketch**:
1. \(H(T)\) increases with new event types
2. Even with repeated types, joint entropy \(H(T, G)\) increases
3. Normalization maintains \(DIA_{info} \in [0, 1]\)
4. Averaging over stochastic process: \(\mathbb{E}[DIA_{info}(L_{n+1})] \geq \mathbb{E}[DIA_{info}(L_n)]\)
∎

---

## 8. Fisher Information for Audit Quality

### 8.1 Fisher Information for Discrete Distributions

For parameterized distribution \(p(x \mid \theta)\):

\[ \mathcal{I}(\theta) = \mathbb{E}\left[ \left( \frac{\partial \log p(X \mid \theta)}{\partial \theta} \right)^2 \right] \]

\[ \mathcal{I}(\theta) = -\mathbb{E}\left[ \frac{\partial^2 \log p(X \mid \theta)}{\partial \theta^2} \right] \]

### 8.2 Cramér-Rao Bound

For unbiased estimator \(\hat{\theta}\) of parameter \(\theta\):

\[ \text{Var}(\hat{\theta}) \geq \frac{1}{\mathcal{I}(\theta)} \]

**Interpretation**: High Fisher information → low estimation variance → precise inference.

### 8.3 Application to Ledger

Model event distribution as:
\[ p(e \mid \theta) \]

Where \(\theta\) encodes:
- Event type probabilities
- Graph structure parameters
- Timestamp distributions

**Fisher Information**:
\[ \mathcal{I}_{ledger}(\theta) = \sum_{e \in L} \left( \frac{\partial \log p(e \mid \theta)}{\partial \theta} \right)^2 \]

### 8.4 DIA and Fisher Information

Hypothesis: High DIA correlates with high Fisher information.

\[ DIA_{info}(L) \propto \mathcal{I}_{ledger}(\theta) \]

**Reasoning**:
- Diverse events → high entropy → high \(DIA_{info}\)
- Diverse events → sensitive to parameter changes → high \(\mathcal{I}\)

### 8.5 Information-Geometric DIA

Define:
\[ DIA_{geo}(L) = \frac{\mathcal{I}_{ledger}(\theta)}{\mathcal{I}_{max}(\theta)} \]

**Interpretation**: Normalized sensitivity of ledger to parameter perturbations.

---

## 9. Algorithmic Information Theory

### 9.1 Normalized Information Distance (NID)

For strings \(x\) and \(y\):

\[ NID(x, y) = \frac{\max(K(x \mid y), K(y \mid x))}{\max(K(x), K(y))} \]

**Properties**:
- \(NID(x, y) \in [0, 1]\)
- \(NID(x, y) = 0\): \(x\) and \(y\) are algorithmically identical
- \(NID(x, y) = 1\): \(x\) and \(y\) are algorithmically independent

### 9.2 Normalized Compression Distance (NCD)

Approximation of NID using real compressors:

\[ NCD(x, y) = \frac{C(xy) - \min(C(x), C(y))}{\max(C(x), C(y))} \]

Where:
- \(C(x)\): Compressed size of \(x\)
- \(C(xy)\): Compressed size of concatenation

### 9.3 Application to Ledger Similarity

Compare two ledgers \(L_1\) and \(L_2\):

\[ NCD(L_1, L_2) = \text{ledger similarity} \]

**Use Cases**:
- Detect anomalous ledger states
- Compare ledger across replicas (should be NCD ≈ 0)
- Identify ledger forks or tampering

### 9.4 Minimum Description Length (MDL)

For model \(M\) and data \(D\):

\[ MDL(M, D) = L(M) + L(D \mid M) \]

Where:
- \(L(M)\): Description length of model
- \(L(D \mid M)\): Description length of data given model

**Principle**: Best model minimizes total description length.

### 9.5 Application to Ledger Compression

Find model \(M\) that compresses ledger \(L\):

\[ M^* = \arg\min_M [L(M) + L(L \mid M)] \]

**Example Models**:
- **Markov chains**: \(p(e_t \mid e_{t-1})\)
- **Grammars**: Context-free grammar generating events
- **Causal models**: SCM generating events

**DIA and MDL**:
\[ DIA_{MDL}(L) = \frac{L(L \mid M^*)}{|L|} \]

High \(DIA_{MDL}\): Ledger is incompressible (information-rich)

---

## 10. Practical Computation

### 10.1 Empirical Entropy Estimation

Given \(n\) events with type counts \(\{n_1, \ldots, n_k\}\):

\[ \hat{H}(T) = -\sum_{i=1}^{k} \frac{n_i}{n} \log_2 \frac{n_i}{n} \]

**Bias Correction** (Miller-Madow):
\[ \hat{H}_{corrected}(T) = \hat{H}(T) + \frac{k - 1}{2n} \]

### 10.2 Mutual Information Estimation

For joint counts \(\{n_{ij}\}\):

\[ \hat{I}(X; Y) = \sum_{i,j} \frac{n_{ij}}{n} \log_2 \frac{n_{ij} / n}{(n_{i \cdot} / n)(n_{\cdot j} / n)} \]

**Bias Correction**: Use jackknife or bootstrap.

### 10.3 Kolmogorov Complexity Approximation

Use compression algorithms (gzip, bzip2, lzma):

\[ K(x) \approx C_{gzip}(x) \]

**Note**: Approximation, not exact. Good for relative comparisons.

### 10.4 Python Implementation

```python
import math
from collections import Counter
import gzip

def compute_entropy(events):
    """Compute Shannon entropy of event types."""
    type_counts = Counter(e['type'] for e in events)
    n = len(events)

    entropy = 0.0
    for count in type_counts.values():
        p = count / n
        if p > 0:
            entropy -= p * math.log2(p)

    # Miller-Madow bias correction
    k = len(type_counts)
    entropy_corrected = entropy + (k - 1) / (2 * n)

    return entropy_corrected

def compute_mutual_information(events, var1, var2):
    """Compute mutual information between two variables."""
    from collections import defaultdict

    joint_counts = defaultdict(int)
    var1_counts = Counter()
    var2_counts = Counter()
    n = len(events)

    for e in events:
        v1 = e[var1]
        v2 = e[var2]
        joint_counts[(v1, v2)] += 1
        var1_counts[v1] += 1
        var2_counts[v2] += 1

    mi = 0.0
    for (v1, v2), count in joint_counts.items():
        p_joint = count / n
        p_v1 = var1_counts[v1] / n
        p_v2 = var2_counts[v2] / n

        if p_joint > 0:
            mi += p_joint * math.log2(p_joint / (p_v1 * p_v2))

    return mi

def compute_kolmogorov_complexity_approx(ledger_str):
    """Approximate Kolmogorov complexity using gzip."""
    compressed = gzip.compress(ledger_str.encode('utf-8'))
    return len(compressed)

def compute_dia_info_extended(events):
    """Compute extended DIA_info metric."""
    H_T = compute_entropy(events)

    # Compute graph edge density
    num_events = len(events)
    edges = set()
    for e in events:
        for parent in e.get('parents', []):
            edges.add((parent, e['id']))
        for justified in e.get('justifies', []):
            edges.add((e['id'], justified))

    edge_density = len(edges) / max(num_events, 1)

    # Extended formula
    numerator = min(H_T, edge_density)
    denominator = max(H_T, 1.0)

    dia_info = numerator / denominator

    return dia_info
```

### 10.5 Integration with sim_replay.py

Extend existing `dia_info` function:

```python
def dia_info_extended(state: ReplayState) -> float:
    """Extended DIA_info with bias correction and graph integration."""
    events = state.events

    # Compute entropy with bias correction
    H_T = compute_entropy(events)

    # Edge density
    all_edges = state.edges | state.parent_edges
    edge_density = len(all_edges) / max(len(state.vertices), 1)

    # Extended formula
    numerator = min(H_T, edge_density)
    denominator = max(H_T, 1.0)

    return numerator / denominator
```

---

## 11. Conclusion

### 11.1 Summary

We have formalized **DIA_info** using:
1. **Shannon entropy**: Diversity of event types
2. **Mutual information**: Causal linkage strength
3. **Kolmogorov complexity**: Incompressibility (information richness)
4. **Fisher information**: Inference precision
5. **Entropy rate**: Long-term information growth

### 11.2 Key Results

- **DIA_info measures audit quality** via information-theoretic principles
- **High DIA_info** → high entropy, high causal linkage, low redundancy
- **Monotonicity** guaranteed by positive entropy rate
- **Practical computation** via empirical estimation and compression

### 11.3 Future Work

- **Quantum information theory**: Extend to quantum ledgers
- **Topological data analysis**: Persistent homology of event graphs
- **Causal entropy**: Merge with causal inference framework

---

## References

1. **Shannon, C. E.** (1948). A Mathematical Theory of Communication. *Bell System Technical Journal*.
2. **Cover, T. M., & Thomas, J. A.** (2006). *Elements of Information Theory*. Wiley.
3. **Li, M., & Vitányi, P.** (2008). *An Introduction to Kolmogorov Complexity and Its Applications*. Springer.
4. **Amari, S., & Nagaoka, H.** (2000). *Methods of Information Geometry*. AMS.
5. **Grassberger, P.** (1986). Toward a Quantitative Theory of Self-Generated Complexity. *International Journal of Theoretical Physics*.

---

**Document Version**: 1.0
**Last Updated**: 2025-12-05
**Status**: Complete Mathematical Specification
