# Reversible Merge Monoid (3⊥+1)

The 3⊥+1 structure models an append-only ledger as a monoid. Elements support a merge operation (⊕) with an associated inverse enabling reversible merges. This spec sketches the algebraic laws that make the structure suitable for Φ-16, ensuring that history can be merged and audited without loss of information.

## 1. Algebraic Foundation

### 1.1 Monoid Definition

A **monoid** is an algebraic structure \((M, \oplus, e)\) satisfying:

1. **Closure**: \(\forall a, b \in M: a \oplus b \in M\)
2. **Associativity**: \(\forall a, b, c \in M: (a \oplus b) \oplus c = a \oplus (b \oplus c)\)
3. **Identity**: \(\exists e \in M: \forall a \in M: e \oplus a = a \oplus e = a\)

### 1.2 The 3⊥+1 Structure

For Φ-OS, we define the event ledger monoid:

```
M = Event*  (sequences of events)
⊕ = concatenation
e = ε (empty sequence)
```

**Key Properties**:
- **Append-only**: Events can only be added, never removed
- **Reversible in view**: We can "undo" by computing inverse views, not by deletion
- **Cryptographically chained**: Each event contains hash of previous

## 2. Event Structure

### 2.1 Event Definition

An event \(e_i\) is a tuple:

\[ e_i = (id, type, timestamp, data, parents, justifies, metadata, hash) \]

Where:
- \(id\): Unique monotonically increasing identifier
- \(type\): Event classification
- \(timestamp\): ISO 8601 timestamp
- \(data\): Event payload
- \(parents\): Set of parent event IDs (dependency edges)
- \(justifies\): Set of justified event IDs (causal edges)
- \(metadata\): Additional context (agent, approvals, etc.)
- \(hash\): SHA-256 hash of previous event

### 2.2 Hash Chain Property

\[ hash(e_i) = SHA256(e_{i-1}) \]

This creates an immutable chain:

\[ e_1 \xrightarrow{h_1} e_2 \xrightarrow{h_2} e_3 \xrightarrow{h_3} \cdots \xrightarrow{h_{n-1}} e_n \]

**Tamper Detection**: Any modification to \(e_k\) invalidates all hashes \(h_{k+1}, h_{k+2}, \ldots, h_n\)

## 3. Merge Operation (⊕)

### 3.1 Sequential Merge

For two ledgers \(L_1 = \langle e_1, \ldots, e_m \rangle\) and \(L_2 = \langle e_{m+1}, \ldots, e_n \rangle\):

\[ L_1 \oplus L_2 = \langle e_1, \ldots, e_m, e_{m+1}, \ldots, e_n \rangle \]

**Property**: Hash chain must be continuous:
\[ hash(e_{m+1}) = SHA256(e_m) \]

### 3.2 Parallel Merge (Branching)

When two agents create events concurrently from common ancestor:

```
        e_k
       /   \
     e_a   e_b  (parallel branches)
       \   /
        e_m     (merge event)
```

**Merge Event**: \(e_m\) has both \(e_a\) and \(e_b\) as parents:
\[ parents(e_m) = \{id(e_a), id(e_b)\} \]

### 3.3 3⊥+1 Terminology

**"3⊥"** refers to three bottom elements (⊥) representing:
1. **⊥_data**: Empty data event
2. **⊥_justify**: Event with no justification
3. **⊥_parent**: Event with no parent (genesis)

**"+1"** refers to the merge operation that combines these into a unified history.

## 4. Reversibility Without Deletion

### 4.1 Event Sourcing Principle

State is never stored directly but **derived from history**:

\[ S_n = f(f(f(\ldots f(S_0, e_1), e_2), \ldots), e_n) \]

Where:
- \(S_0\): Initial state
- \(f\): Deterministic state transition function
- \(e_i\): Events in order

### 4.2 Compensating Events

To "undo" event \(e_k\), create compensating event \(e_{k}^{-1}\):

\[ e_k \oplus e_k^{-1} \approx e \quad \text{(approximately identity in effect)} \]

**Example**:
- \(e_k\): "Add user_123"
- \(e_k^{-1}\): "Remove user_123"

The history preserves both actions:
\[ L = \langle \ldots, e_k, \ldots, e_k^{-1}, \ldots \rangle \]

### 4.3 View Functions (Projections)

Different views of history without modifying \(L\):

\[ V_{filter}(L) = \{ e_i \in L \mid P(e_i) \} \]

Where \(P\) is a predicate (e.g., "type = UserAction").

## 5. Formal Properties

### 5.1 Monotonicity

**Ledger Length Monotonicity**:
\[ \forall L, L': L \to L' \implies |L'| \geq |L| \]

**DIA Monotonicity** (with tolerance \(\tau\)):
\[ DIA(L') \geq DIA(L) - \tau \]

### 5.2 Causal Consistency

For events \(e_i, e_j\) where \(e_i\) causally precedes \(e_j\) (notation: \(e_i \prec e_j\)):

\[ e_i \prec e_j \iff (id(e_i) < id(e_j)) \land (id(e_i) \in ancestors(e_j)) \]

Where \(ancestors(e_j) = parents(e_j) \cup \bigcup_{p \in parents(e_j)} ancestors(p)\)

**Causal Consistency Requirement**:
\[ e_i \prec e_j \implies timestamp(e_i) \leq timestamp(e_j) \]

### 5.3 Conflict-Free Replicated Data Type (CRDT) Properties

The ledger forms a **Strong Eventually Consistent** CRDT:

1. **Eventual Consistency**: All replicas converge to the same state
2. **Strong Convergence**: Replicas that have seen the same events are in identical states
3. **Commutativity** (for parallel merges):
   \[ (L \oplus L_a) \oplus L_b = (L \oplus L_b) \oplus L_a \]
   when \(L_a\) and \(L_b\) branch from common \(L\)

## 6. Graph-Theoretic Representation

### 6.1 Event Graph

The ledger forms a **Directed Acyclic Graph (DAG)**:
\[ G = (V, E) \]

Where:
- \(V = \{ id(e_i) \mid e_i \in L \}\) (vertices = event IDs)
- \(E = E_{parent} \cup E_{justify}\) (edges from parents and justifications)

### 6.2 DAG Properties

1. **Acyclicity**: No cycles allowed
   \[ \nexists \text{ path } v_1 \to v_2 \to \cdots \to v_k \to v_1 \]

2. **Topological Order**: Events can be linearly ordered respecting causality
   \[ \exists \text{ ordering } \sigma: e_i \prec e_j \implies \sigma(i) < \sigma(j) \]

3. **Reachability**:
   \[ e_i \text{ causes } e_j \iff \exists \text{ path from } id(e_i) \text{ to } id(e_j) \]

### 6.3 DIA_graph Metric

Edge density measures causal richness:

\[ DIA_{graph}(G) = \frac{|E|}{|V| \cdot (|V| - 1)} \]

**Interpretation**:
- \(DIA_{graph} = 0\): No causal links (isolated events)
- \(DIA_{graph} = 1\): Fully connected DAG (maximum causality)

## 7. Information-Theoretic Properties

### 7.1 Shannon Entropy of Event Types

Given event type distribution \(P = \{p_1, \ldots, p_k\}\):

\[ H(P) = -\sum_{i=1}^{k} p_i \log_2 p_i \]

**Interpretation**:
- High \(H\): Diverse event types (rich information)
- Low \(H\): Homogeneous events (limited information)

### 7.2 DIA_info Metric

\[ DIA_{info}(L) = \frac{\min(H(P), |E|/|V|)}{\max(H(P), 1)} \]

Normalized to \([0, 1]\), combining:
- Entropy of event types
- Edge density (causal connections)

### 7.3 Information Preservation

**No Information Loss**:
\[ \forall L, L': L \subseteq L' \implies H(L) \leq H(L') \]

More events → more or equal entropy (cannot decrease by appending).

## 8. Cryptographic Properties

### 8.1 Hash Function Requirements

SHA-256 provides:
- **Pre-image resistance**: Hard to find \(e\) given \(h = SHA256(e)\)
- **Second pre-image resistance**: Hard to find \(e' \neq e\) with \(SHA256(e') = SHA256(e)\)
- **Collision resistance**: Hard to find any \(e_1 \neq e_2\) with \(SHA256(e_1) = SHA256(e_2)\)

### 8.2 Tamper Evidence

**Theorem**: Any modification to event \(e_k\) is detectable.

**Proof**:
1. Modify \(e_k \to e_k'\)
2. Hash chain breaks: \(hash(e_{k+1}) \neq SHA256(e_k')\)
3. Verification fails when checking: \(hash(e_{k+1}) \stackrel{?}{=} SHA256(e_k')\)
∎

### 8.3 Merkle Tree Extension

For efficient verification of large ledgers, organize events in Merkle tree:

```
         root_hash
        /         \
    h(AB)         h(CD)
    /   \         /   \
  h(A) h(B)    h(C) h(D)
   |     |      |     |
  e_A   e_B    e_C   e_D
```

**Property**: Verify membership of \(e_A\) with \(O(\log n)\) hashes instead of \(O(n)\).

## 9. Formal Verification (TLA+ Integration)

### 9.1 Invariants

**AppendOnlyMonotone**:
\[ Len(L') \geq Len(L) \]

**NoWriteInHold**:
\[ Mode = \text{"HOLD"} \implies \neg(append\_allowed) \]

**HashChainIntegrity**:
\[ \forall i \in 2..|L|: hash(L[i]) = SHA256(L[i-1]) \]

### 9.2 Liveness Properties

**Eventual Append**:
\[ \Diamond(\text{event submitted} \implies \Diamond(\text{event in } L)) \]

Eventually, submitted events appear in ledger (assuming RUN mode).

## 10. Practical Considerations

### 10.1 Storage Efficiency

**Problem**: Ledger grows unbounded.

**Solutions**:
1. **Snapshots**: Periodically save state \(S_n\), allow truncating \(L[1..n]\)
2. **Compression**: Use differential encoding for similar events
3. **Archival**: Move old events to slower storage

### 10.2 Query Efficiency

**Problem**: Replaying entire ledger for each query is slow.

**Solutions**:
1. **Materialized Views**: Cache computed states, update incrementally
2. **Indexing**: Build indices on event attributes (type, timestamp, etc.)
3. **Event Sourcing Snapshots**: Combine snapshots with delta logs

### 10.3 Distributed Ledger

For multi-node deployment:
1. **Consensus**: Use Raft or Paxos for total order
2. **Replication**: Each node maintains full ledger copy
3. **Synchronization**: Periodic hash chain verification across nodes

## 11. Connection to Φ-OS Architecture

### 11.1 R/DIA Doctrine

The reversible merge monoid **implements** the R/DIA doctrine:
- **R (Reproducibility)**: State is \(f(\ldots f(S_0, e_1), \ldots)\) — deterministic replay
- **DIA**: Metrics \(DIA_{graph}, DIA_{info}, DIA_{replay}\) computed from \(L\)

### 11.2 NAND-only Principle

The merge operation \(\oplus\) can be implemented in NAND-only logic:
- Concatenation: Sequential memory writes
- Hash computation: SHA-256 in NAND gates (existing designs)

### 11.3 Token System Integration

Events carry token constraints in metadata:
\[ metadata(e_i) = \{ \text{agent}, \text{approvals}, \text{token\_constraints}, \ldots \} \]

**Example**:
```json
{
  "id": "e42",
  "type": "UserAction",
  "metadata": {
    "agent": "B1",
    "approved_by": ["A1", "A2"],
    "token_constraints": {
      "T13": "active",  // Rights checked
      "T06": "active",  // Security verified
      "T11": "monitoring"  // Safety monitored
    }
  }
}
```

## 12. Mathematical Theorems

### Theorem 1: Monoid Closure
**Statement**: The ledger with concatenation forms a monoid.

**Proof**:
1. **Closure**: \(L_1 \oplus L_2\) is a valid ledger (by construction)
2. **Associativity**: \((L_1 \oplus L_2) \oplus L_3 = L_1 \oplus (L_2 \oplus L_3)\) (concatenation is associative)
3. **Identity**: \(\epsilon \oplus L = L \oplus \epsilon = L\) (empty ledger is identity)
∎

### Theorem 2: DIA Monotonicity (Weak Form)
**Statement**: With \(\tau = 0\), appending events cannot decrease DIA.

**Proof Sketch**:
1. \(DIA = w_g \cdot DIA_{graph} + w_i \cdot DIA_{info} + w_r \cdot DIA_{replay}\)
2. \(DIA_{graph}\) increases: more edges with each event (or stays same)
3. \(DIA_{info}\) increases: entropy non-decreasing with more events
4. \(DIA_{replay}\) maintains: 1.0 if DAG remains acyclic
5. Weighted sum cannot decrease if components don't decrease
∎

### Theorem 3: Tamper Detection
**Statement**: Any modification to the ledger is detectable in \(O(n)\) time.

**Proof**:
1. Compute expected hashes: \(h_i = SHA256(e_{i-1})\) for \(i = 2..n\)
2. Compare with stored hashes in each event
3. First mismatch indicates tamper point
4. Requires \(O(n)\) hash computations
∎

### Theorem 4: Causal Consistency
**Statement**: The DAG structure guarantees causal consistency.

**Proof**:
1. Events are totally ordered by ID: \(id(e_i) < id(e_j) \implies e_i\) comes before \(e_j\)
2. Parent edges enforce causality: \(e_i \in parents(e_j) \implies e_i \prec e_j\)
3. Transitive closure of parent edges = causal order
4. DAG property prevents cycles → causal consistency
∎

## 13. Future Extensions

### 13.1 Quantum-Resistant Hashing
Replace SHA-256 with post-quantum hash functions (e.g., SPHINCS+).

### 13.2 Zero-Knowledge Proofs
Allow verification of ledger properties without revealing event contents.

### 13.3 Smart Contracts
Embed executable code in events, creating programmable ledger.

### 13.4 Multi-Ledger Composition
Define homomorphisms between ledgers for cross-domain verification.

---

## References

1. **Event Sourcing**: Fowler, M. (2005). Event Sourcing. martinfowler.com
2. **CRDTs**: Shapiro, M., et al. (2011). Conflict-free Replicated Data Types. INRIA Research Report
3. **Merkle Trees**: Merkle, R. C. (1988). A Digital Signature Based on a Conventional Encryption Function. CRYPTO
4. **TLA+**: Lamport, L. (2002). Specifying Systems. Addison-Wesley
5. **Blockchain**: Nakamoto, S. (2008). Bitcoin: A Peer-to-Peer Electronic Cash System

---

**Document Version**: 1.0
**Last Updated**: 2025-12-05
**Status**: Complete Mathematical Specification
