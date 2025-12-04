# CLAUDE.md - AI Assistant Guide for Φ-OS (phi16)

**Last Updated:** 2025-12-04
**Repository:** phi16 - An AI-Based Operating System for Verifiable Knowledge
**Version:** 1.0

---

## Table of Contents

1. [Introduction](#introduction)
2. [Core Principles - The Inviolable Rules](#core-principles---the-inviolable-rules)
3. [Codebase Structure](#codebase-structure)
4. [Development Workflows](#development-workflows)
5. [Key Conventions](#key-conventions)
6. [Working with the Token System](#working-with-the-token-system)
7. [Common Tasks](#common-tasks)
8. [Testing Guidelines](#testing-guidelines)
9. [Critical Pitfalls to Avoid](#critical-pitfalls-to-avoid)
10. [Quick Reference](#quick-reference)

---

## Introduction

### What is Φ-OS?

Φ-OS (Phi-OS) is not a traditional operating system but an **epistemological engine** - a system designed for the creation, verification, and management of **verifiable knowledge** in complex, high-stakes environments. It is built on three fundamental pillars forming the **"Triad of Trust"**:

1. **Mathematical Trust** - Formal verification, provable logic, immutable data structures
2. **Statistical Trust** - Sophisticated analytics beyond correlation to causation-like investigation
3. **Ethical Trust** - Human partnership and epistemic justice embedded structurally

### Purpose of This Document

This document serves as a comprehensive guide for AI assistants (like Claude) working with the phi16 codebase. It explains:
- The architectural principles that MUST NOT be violated
- The codebase structure and organization
- Development workflows and conventions
- How to safely make changes while preserving system integrity

### Recent Major Development

The system recently integrated a complete **Hebrew Token System** providing ethical governance across all operations. This means:
- **15 tokens** organized in **6 hierarchical layers**
- **Ethics structurally prevails over efficiency**
- All operations are governed by token constraints
- Emergency controls via T15 (Seriousness) token

---

## Core Principles - The Inviolable Rules

These principles are **axiomatic** - they CANNOT be compromised under any circumstances. Violating these principles compromises the entire system's integrity.

### 1. The R/DIA Doctrine: Memory = Accountability

**Principle:** Every system state must be the direct and provable result of its history.

**Implementation:**
- All state changes recorded in an **append-only log** (L)
- Hash-chained for cryptographic immutability
- Any R/DIA violation triggers immediate **HOLD state**

**Critical Rules:**
- ✅ ALWAYS append to the ledger, NEVER modify it
- ✅ ALWAYS use `append_stream()` or `append_batch()`
- ❌ NEVER directly edit ledger data structures
- ❌ NEVER delete or modify historical events

**DIA Monotonicity Invariant:** `DIA′ ≥ DIA`
- The density of auditable information MUST NEVER decrease
- If DIA drops, system enters SAFE state
- This is the primary health metric

**Files:**
- `ledger.py` - Core ledger implementation
- `sim_replay.py` - DIA computation
- `spec/crypto/ledger_hash_chain.md` - Cryptographic model

### 2. The NAND-only Principle: Simplicity Enables Verification

**Principle:** ALL logic operations must decompose to NAND gates only.

**Rationale:**
- NAND is functionally complete (can implement any Boolean function)
- Single primitive makes formal verification tractable
- Reduces "attack surface" for proofs
- Eliminates entire classes of potential errors

**Implementation:**
- All software IR must use NAND-only primitives
- Hardware must use only NAND2 and FF (flip-flop)
- Formal equivalence checking required

**Critical Rules:**
- ✅ ALWAYS decompose logic to NAND primitives
- ✅ USE `nand_ir_semantics.md` as reference
- ❌ NEVER use OR, XOR, MUX directly
- ❌ NEVER skip verification steps

**Policy File:** `NAND_only_policy.yaml`

**Trade-off:** Correctness > Performance. This is a deliberate choice.

### 3. Separation of Proposal from Commitment

**Principle:** No single agent has unilateral control from proposal to execution.

**Multi-Agent Workflow:**
```
Φ-Architect → A2 (Formal) → A1 (Ethical) → B1 (Actuator) → B2 (Safety Monitor)
   Proposes     Verifies      Approves      Executes       Monitors
```

**Agent Roles:**
| Agent | Role | Can Propose | Can Approve | Can Execute | Can Veto |
|-------|------|-------------|-------------|-------------|----------|
| Φ-Architect | Proposer | ✅ | ❌ | ❌ | ❌ |
| A2 | Formal Approver | ❌ | ✅ (structure) | ❌ | ✅ |
| A1 | Substantive Approver | ❌ | ✅ (ethics) | ❌ | ✅ |
| B1 | Actuator | ❌ | ❌ | ✅ | ❌ |
| B2 | Safety Monitor | ❌ | ❌ | ❌ | ✅ (HOLD) |

**Critical Rules:**
- ✅ ALWAYS follow the complete workflow
- ✅ ALWAYS get approvals from both A1 and A2
- ❌ NEVER allow direct proposal-to-execution
- ❌ NEVER bypass safety checks

**Visual:** See `phi16_ascii_arch.txt`

### 4. Token Hierarchy: Ethics Before Technology

**Principle:** In any conflict, ethical values ALWAYS prevail over computational efficiency.

**Hierarchy (highest to lowest priority):**
```
Layer 1: T15 - Seriousness (Emergency Control)        Priority: 96
Layer 2: T13 - Rights (Supreme)                       Priority: 94
         T01 - Data                                   Priority: 95
         T06 - Security                               Priority: 92
Layer 3: T10 - Measure                                Priority: 93
         T11 - Monitor                                Priority: 89
         T12 - Learn                                  Priority: 91
Layer 4: T08 - Govern                                 Priority: 85
         T09 - Standardize                            Priority: 87
         T05 - Identity                               Priority: 88
Layer 5: T07 - Automation                             Priority: 86
         T03 - Compute                                Priority: 85
         T04 - Storage                                Priority: 85
Layer 6: T02 - Network                                Priority: 90
         T14 - Commons                                Priority: 85
```

**Critical Rules:**
- ✅ ALWAYS respect the hierarchy
- ✅ HIGHER layers control LOWER layers
- ❌ NEVER let efficiency override ethics (T13)
- ❌ NEVER bypass T15 in emergencies

**Constraints (Cannot be violated):**
- C01: No automation without monitoring (T07 ← T11)
- C02: No computation without security (T03 ← T06)
- C03: No governance without rights (T08 ← T13)
- C04: No unfair standards (T09 ← T10, T13)
- C05: No anonymous network (T02 ← T05, T06)
- C06: No storage of violations (T04 ← T13)

### 5. System States: RUN, HOLD, SAFE

**State Machine:**
```
RUN ──[Consensus Failure]──> HOLD
 │
 └──[Policy Violation]────> SAFE
```

**States:**
- **RUN**: Normal operation, all systems functional
- **HOLD**: Consensus failure (AND-0+ failed), no writes allowed
- **SAFE**: Policy violation (DIA drop, risk threshold), no writes allowed

**Recovery:**
- HOLD → RUN: Requires AND-0+ consensus restoration
- SAFE → RUN: Requires DIA restoration + explicit approval

**Critical Rules:**
- ✅ ALWAYS check system state before operations
- ✅ HALT immediately if entering HOLD or SAFE
- ❌ NEVER write during HOLD or SAFE states
- ❌ NEVER force recovery without proper conditions

---

## Codebase Structure

### Directory Layout

```
phi16/
├── README.md                    # Master plan and overview
├── LICENSE                      # MIT License
├── Makefile                     # Build targets (tla, sim, lint, test)
├── requirements.txt             # Python dependencies
│
├── Phi16.tla                    # Main TLA+ specification
├── Phi16.cfg                    # TLA+ model checker config
├── NAND_only_policy.yaml        # NAND verification policy
├── phi16_ascii_arch.txt         # Visual architecture diagram
│
├── ledger.py                    # Core ledger implementation (232 lines)
├── sim_replay.py                # DIA computation & replay (232+ lines)
│
├── docs/                        # Documentation (20 files)
│   ├── README.md                # Documentation index
│   ├── whitepaper_phi16.md      # Philosophy and rationale
│   ├── standard_phi16_v1.md     # Complete v1.0 standard (Hebrew)
│   ├── IMPLEMENTATION.md        # Token system implementation guide
│   ├── A2_invariants.md         # Invariant specifications
│   ├── B1_ops_manual.md         # Operations manual
│   ├── B2_playbook.md           # Safety playbook
│   ├── DIA_*.md                 # DIA documentation
│   ├── NAND_only_practical.md   # NAND guidelines
│   ├── ledger_quick_start.md    # Getting started
│   ├── hebrew_token_*.md        # Token system docs (5 files)
│   └── phi_os_token_integration.md  # Integration guide
│
├── spec/                        # Formal specifications
│   ├── tla/                     # TLA+ specs (3 files + configs)
│   ├── math/                    # Mathematical formalizations
│   ├── crypto/                  # Cryptographic specifications
│   ├── ir/                      # IR semantics
│   ├── stat/                    # Statistical decision models
│   └── ssot/                    # JSON schemas (4 files)
│
├── tokens/                      # Hebrew Token System (17 files)
│   ├── __init__.py              # Package exports
│   ├── base.py                  # Base Token class
│   ├── registry.py              # Token registry
│   ├── constraints.py           # Constraint enforcement
│   ├── hierarchy.py             # 6-layer hierarchy
│   ├── moral_triangle.py        # T10↔T11↔T12 feedback loop
│   ├── system.py                # System initialization (entry point)
│   ├── t15_seriousness.py       # Emergency control
│   ├── t05_identity.py          # Identity token
│   ├── layer2_absolute.py       # T13, T06, T01
│   ├── layer3_moral.py          # T10, T11, T12
│   ├── layer4_governance.py     # T08, T09
│   ├── layer5_execution.py      # T07, T03, T04
│   ├── layer6_infrastructure.py # T02, T14
│   └── integrations/            # Φ-OS integrations (4 files)
│       ├── rdia_integration.py
│       ├── nand_integration.py
│       ├── agent_integration.py
│       └── phi_os_integration.py
│
├── tests/                       # Test suite (6 files)
│   ├── run_tests.py             # Simple test runner (no pytest needed)
│   ├── test_hebrew_token_system.py  # Token tests (9 tests)
│   ├── test_ledger.py           # Ledger tests
│   ├── test_ledger_cli.py       # CLI tests
│   ├── test_sim_replay.py       # Simulation tests
│   └── test_entropy.py          # Entropy tests
│
├── examples/                    # Demonstration scripts (3 files)
│   ├── token_system_demo.py     # Token system demo (executable)
│   ├── phi_os_integration_demo.py  # Full integration demo
│   └── events.json              # Sample event data
│
└── generative/                  # Generative protocol (2 files)
    ├── protocol.py              # High-entropy concept generation
    └── entropy_tools.py         # Entropy utilities
```

### Key Statistics

- **Total Files:** ~80+ files
- **Python Code:** ~6,058 lines across 28 files
- **Documentation:** 26+ markdown files (Hebrew/English)
- **Specifications:** 3 TLA+ specs + 5+ formal spec documents
- **Test Coverage:** 9/9 tests passing (100%)
- **Languages:** Python 3.x, TLA+, Markdown, YAML, JSON

### Language & Style

- **Python Version:** 3.x with type hints (`from __future__ import annotations`)
- **Documentation:** Mix of Hebrew (philosophy, standards) and English (implementation)
- **Mathematical Notation:** LaTeX-style formulas in markdown
- **Diagrams:** ASCII art and Mermaid

---

## Development Workflows

### Git Workflow

**Branch Naming Convention:**
```
claude/[description]-[unique-id]
```

**Example:**
```
claude/implement-token-system-01R1FN7BXT5yNGXzXVqRPtYo
claude/integrate-token-phi-os-011x5dhA5eWsXeqQxd1dfJfE
```

**Workflow:**
1. Create feature branch from main
2. Implement changes with clear, descriptive commits
3. Ensure all tests pass
4. Create pull request
5. Maintainer reviews and merges

**Commit Style:**
```
[Type] Brief description

Detailed explanation if needed.
```

**Types:**
- `feat:` New feature
- `fix:` Bug fix
- `docs:` Documentation changes
- `test:` Test additions/modifications
- `refactor:` Code refactoring
- `style:` Code style changes
- `chore:` Maintenance tasks

**Example Commits:**
```
Implement complete Hebrew Token System
Integrate Hebrew Token System with Φ-OS architecture
Add comprehensive Hebrew Token System documentation
```

### Build & Verification Workflow

**Makefile Targets:**

```bash
make tla    # Model check TLA+ specification with TLC
make sim    # Replay trace using Python simulator
make lint   # Lint Python sources with flake8
make test   # Run Python unit tests with pytest
```

**Typical Development Flow:**

1. **Make Changes**
   ```bash
   # Edit code
   vim ledger.py
   ```

2. **Run Tests**
   ```bash
   python3 tests/run_tests.py  # Simple runner (no pytest needed)
   # OR
   make test                    # Full pytest suite
   ```

3. **Verify Formal Specs** (if changed)
   ```bash
   make tla
   ```

4. **Lint Code**
   ```bash
   make lint
   ```

5. **Test Simulation**
   ```bash
   make sim
   ```

6. **Commit & Push**
   ```bash
   git add .
   git commit -m "feat: Add new token constraint"
   git push -u origin claude/your-branch-name
   ```

### Testing Strategy

**Test Execution:**
```bash
# Simple runner (recommended for quick tests)
python3 tests/run_tests.py

# Full pytest suite
pytest

# Specific test file
pytest tests/test_ledger.py

# With coverage
pytest --cov=. tests/
```

**Test Organization:**
- `run_tests.py` - Simple runner, no external dependencies
- `test_hebrew_token_system.py` - Token system tests (9 tests)
- `test_ledger.py` - Ledger functionality
- `test_sim_replay.py` - Simulation and replay
- `test_entropy.py` - Entropy calculations
- `test_ledger_cli.py` - CLI interface

**Current Status:** ✅ 9/9 tests passing (100%)

---

## Key Conventions

### Python Conventions

**Code Style:**
- Python 3.x with type hints
- PEP 8 compliant (enforced by flake8)
- Use `from __future__ import annotations` for forward references
- Clear, descriptive variable names (prefer readability over brevity)

**Example:**
```python
from __future__ import annotations
from typing import Dict, List, Optional

def append_stream(
    ledger: Dict,
    event: Dict,
    validate: bool = True
) -> Optional[str]:
    """Append a single event to the ledger stream.

    Args:
        ledger: The ledger data structure
        event: Event to append
        validate: Whether to validate against schema

    Returns:
        Error message if validation fails, None otherwise
    """
    # Implementation
    pass
```

**Imports:**
- Standard library first
- Third-party packages second
- Local modules third
- Separated by blank lines

**Example:**
```python
import json
import hashlib
from typing import Dict, List

import jsonschema

from tokens.system import HebrewTokenSystem
```

### Naming Conventions

**Files:**
- Snake_case for Python: `sim_replay.py`, `ledger.py`
- PascalCase for TLA+: `Phi16.tla`
- lowercase for configs: `requirements.txt`, `Makefile`

**Variables:**
- Snake_case: `event_id`, `hash_chain`, `dia_metric`
- Constants: UPPER_SNAKE_CASE: `MAX_EVENTS`, `DEFAULT_EPSILON`

**Classes:**
- PascalCase: `HebrewTokenSystem`, `TokenRegistry`, `StreamingReplay`

**Functions/Methods:**
- Snake_case: `append_stream()`, `calculate_dia()`, `validate_constraints()`

### Documentation Conventions

**Docstrings:**
```python
def calculate_dia(
    ledger: Dict,
    weights: Optional[Dict] = None
) -> float:
    """Calculate the weighted DIA metric.

    DIA combines three metrics:
    - DIA_graph: Edge density of justification graph
    - DIA_info: Shannon entropy of metadata
    - DIA_replay: Replay success rate

    Args:
        ledger: Ledger data structure with events
        weights: Optional custom weights (w_g, w_i, w_r)
                Defaults to {w_g: 0.5, w_i: 0.3, w_r: 0.2}

    Returns:
        Weighted DIA score in [0, 1]

    Raises:
        ValueError: If weights don't sum to 1.0

    Example:
        >>> dia = calculate_dia(ledger)
        >>> print(f"DIA: {dia:.3f}")
        DIA: 0.847
    """
```

**Comments:**
- Use comments for "why", not "what"
- Reference formal specs when applicable
- Mark TODOs clearly: `# TODO: Add constraint C07`

**Example:**
```python
# Apply NAND-only constraint per spec/ir/nand_ir_semantics.md
# This ensures all operations are formally verifiable
result = nand(nand(a, b), nand(a, b))  # Implements AND via NAND
```

### JSON Schema Conventions

**Validation:**
- All external data MUST be validated against schemas in `spec/ssot/`
- Use `jsonschema.validate()` for validation
- Fail fast on schema violations

**Example:**
```python
import jsonschema

# Load schema
with open('spec/ssot/events.schema.json') as f:
    schema = json.load(f)

# Validate
try:
    jsonschema.validate(event, schema)
except jsonschema.ValidationError as e:
    print(f"Schema validation failed: {e.message}")
    return
```

### TLA+ Conventions

**Specifications:**
- One main spec: `Phi16.tla`
- Modular sub-specs in `spec/tla/`
- Config files alongside specs: `Phi16.cfg`

**Invariants:**
- Clearly named: `AppendOnlyMonotone`, `NoWriteInHold`, `DIAMonotonicity`
- Documented in both TLA+ and markdown
- Reference in code comments

**Model Checking:**
```bash
tlc -config Phi16.cfg Phi16.tla
```

---

## Working with the Token System

### Understanding the Token System

The Hebrew Token System is the **ethical governance layer** that ensures all operations respect ethical principles.

**Key Concepts:**
1. **15 Tokens** across **6 Layers**
2. **Strict Hierarchy** - higher layers control lower layers
3. **Constraints** - inviolable relationships between tokens
4. **Dependencies** - required relationships for activation
5. **Moral Triangle** - T10↔T11↔T12 feedback loop with 2.5× synergy

### Token System Entry Point

```python
from tokens.system import HebrewTokenSystem

# Initialize
system = HebrewTokenSystem()
system.initialize()

# Enable Φ-OS integration
system.enable_phi_os_integration()
```

### Checking Token Constraints

**Before any operation:**
```python
# Check if automation is allowed (C01: No automation without monitoring)
if not system.constraints.check_constraint('C01'):
    print("Cannot automate: Monitoring (T11) is not active")
    return

# Check if computation is allowed (C02: No computation without security)
if not system.constraints.check_constraint('C02'):
    print("Cannot compute: Security (T06) is not active")
    return
```

### Working with Emergency Mode (T15)

**Activating Emergency:**
```python
t15 = system.get_token('T15')

# Enter emergency mode (HOLD state)
t15.activate_emergency()
print(f"System state: {t15.state}")  # EMERGENCY

# Emergency automatically suspends lower-priority operations
# T07 (Automation) will be suspended
```

**Resolving Emergency:**
```python
# After resolving the issue
t15.resolve_emergency()
```

### Token → Φ-OS Mappings

When working with Φ-OS components, understand token mappings:

| Token | Φ-OS Component | Integration File |
|-------|----------------|------------------|
| T15 | HOLD State | `agent_integration.py` |
| T13 | VSD/FAT Ethical Principles | `agent_integration.py` |
| T06 | B2 Safety Monitor + Crypto | `rdia_integration.py` |
| T01 | Append-Only Log | `rdia_integration.py` |
| T10 | DIA Metrics + SSM | `rdia_integration.py` |
| T11 | B2 Safety Monitor | `agent_integration.py` |
| T12 | PPCD/QTPU-Φ Pipeline | (future) |
| T08 | A1 Substantive Approver | `agent_integration.py` |
| T09 | NAND-only Policy | `nand_integration.py` |
| T05 | Agent IDs | `agent_integration.py` |
| T07 | B1 Actuator | `agent_integration.py` |
| T03 | QTPU-Φ + PPCD | `nand_integration.py` |
| T04 | Ledger + DIA Monotonicity | `rdia_integration.py` |
| T02 | Communication Layer | (future) |
| T14 | Open Datasets | (future) |

### Example: Complete Request Processing

```python
from tokens.system import HebrewTokenSystem

# Initialize
system = HebrewTokenSystem()
system.initialize()
system.enable_phi_os_integration()

# Process request through complete pipeline
request = {
    "action": "add_user",
    "data": {"user_id": "123"},
    "evidence": "Registration form"
}

result = system.process_phi_os_request(request)

# Check results
print(f"Success: {result['success']}")
print(f"State: {result['state']}")
print(f"Audit Trail: {result['audit_trail']}")

# Audit trail shows:
# 1. Token validation (T05, T13)
# 2. Security checks (T06)
# 3. Agent workflow (Φ → A2 → A1 → B1 → B2)
# 4. Ledger append (T01, T04)
# 5. DIA verification (T10)
```

---

## Common Tasks

### Task 1: Adding a New Event to the Ledger

```python
import json
from ledger import append_stream, load_ledger, save_ledger

# Load existing ledger
ledger = load_ledger('data/ledger.json')

# Create new event
event = {
    "id": "e42",
    "type": "UserAction",
    "timestamp": "2025-12-04T20:00:00Z",
    "data": {"action": "login", "user_id": "user123"},
    "parents": ["e41"],  # Reference previous event
    "justifies": [],
    "metadata": {"agent": "A1", "approved_by": ["A2"]}
}

# Append with validation
error = append_stream(ledger, event, validate=True)
if error:
    print(f"Failed to append: {error}")
    # Handle error (likely enters HOLD state)
else:
    # Save updated ledger
    save_ledger(ledger, 'data/ledger.json')
    print("Event appended successfully")
```

### Task 2: Calculating DIA Metrics

```python
from sim_replay import dia_graph, dia_info, dia_replay

# Load ledger
with open('data/ledger.json') as f:
    ledger = json.load(f)

# Calculate individual metrics
dia_g = dia_graph(ledger['events'])
dia_i = dia_info(ledger['events'])
dia_r = dia_replay(ledger['events'])

print(f"DIA_graph: {dia_g:.3f}")
print(f"DIA_info: {dia_i:.3f}")
print(f"DIA_replay: {dia_r:.3f}")

# Calculate weighted DIA
weights = {'w_g': 0.5, 'w_i': 0.3, 'w_r': 0.2}
dia_total = (
    weights['w_g'] * dia_g +
    weights['w_i'] * dia_i +
    weights['w_r'] * dia_r
)

print(f"Total DIA: {dia_total:.3f}")

# Check monotonicity
if dia_total < previous_dia:
    print("WARNING: DIA decreased! Entering SAFE state.")
    # Trigger SAFE state
```

### Task 3: Adding a New Token Constraint

```python
# In tokens/constraints.py

class ConstraintEnforcer:
    def __init__(self, registry: 'TokenRegistry'):
        self.registry = registry
        self.constraints = {
            'C01': self._check_no_automation_without_monitoring,
            'C02': self._check_no_computation_without_security,
            # ... existing constraints ...
            'C07': self._check_your_new_constraint,  # Add here
        }

    def _check_your_new_constraint(self) -> bool:
        """C07: Description of your constraint.

        Example: No storage without encryption.
        T04 (Storage) requires T06 (Security) to be active.
        """
        t04 = self.registry.get_token('T04')
        t06 = self.registry.get_token('T06')

        if t04.state == TokenState.ACTIVE:
            if t06.state != TokenState.ACTIVE:
                return False

        return True
```

**Then update tests:**
```python
# In tests/test_hebrew_token_system.py

def test_your_new_constraint():
    """Test C07: No storage without encryption."""
    system = HebrewTokenSystem()
    system.initialize()

    # Activate storage
    t04 = system.get_token('T04')
    t04.activate()

    # Should fail constraint
    assert not system.constraints.check_constraint('C07')

    # Activate security
    t06 = system.get_token('T06')
    t06.activate()

    # Should pass now
    assert system.constraints.check_constraint('C07')
```

### Task 4: Implementing a New Agent Function

```python
# Following the multi-agent workflow

class PhiArchitect:
    """Φ-Architect: Proposes changes, cannot commit."""

    def __init__(self, token_system: HebrewTokenSystem):
        self.system = token_system
        self.agent_id = "Φ-Architect"

    def propose_change(self, change_request: Dict) -> Dict:
        """Propose a change (cannot execute directly).

        Returns proposal for A2/A1 review.
        """
        # Validate identity (T05)
        if not self.system.get_token('T05').state == TokenState.ACTIVE:
            return {"error": "Identity not validated"}

        # Create proposal
        proposal = {
            "proposer": self.agent_id,
            "type": "change_proposal",
            "request": change_request,
            "timestamp": datetime.now().isoformat(),
            "state": "PROPOSED"
        }

        # Pass to A2 for formal verification
        return self._send_to_a2(proposal)

class A2FormalApprover:
    """A2: Structural verification."""

    def verify_proposal(self, proposal: Dict) -> Dict:
        """Verify structural correctness."""
        # Check NAND-only compliance (T09)
        if not self._check_nand_only(proposal):
            return {"approved": False, "reason": "NAND-only violation"}

        # Check formal invariants
        if not self._check_invariants(proposal):
            return {"approved": False, "reason": "Invariant violation"}

        # Pass to A1 for ethical review
        proposal["a2_approved"] = True
        return proposal

class A1SubstantiveApprover:
    """A1: Ethical approval."""

    def approve_proposal(self, proposal: Dict) -> Dict:
        """Ethical and DIA review."""
        # Check rights (T13)
        if not self._check_rights(proposal):
            return {"approved": False, "reason": "Rights violation"}

        # Check DIA impact
        if not self._check_dia_preservation(proposal):
            return {"approved": False, "reason": "DIA would decrease"}

        # Approve
        proposal["a1_approved"] = True
        return proposal

class B1Actuator:
    """B1: Executes approved changes."""

    def execute(self, proposal: Dict) -> Dict:
        """Execute only if both A1 and A2 approved."""
        if not (proposal.get("a1_approved") and proposal.get("a2_approved")):
            return {"error": "Not approved by A1 and A2"}

        # Execute the change
        result = self._perform_execution(proposal)

        # Append to ledger
        self._append_to_ledger(proposal, result)

        return result
```

### Task 5: Writing Formal Specs for New Features

When adding new features, update TLA+ specifications:

```tla
---- MODULE Phi16Extended ----
EXTENDS Phi16

\* New state variable for your feature
VARIABLE FeatureState

\* Type invariant
TypeOK ==
  /\ FeatureState \in {"INACTIVE", "ACTIVE", "ERROR"}
  /\ \* existing type invariants

\* New invariant for your feature
YourNewInvariant ==
  \* Example: Feature can only be active if system is in RUN mode
  FeatureState = "ACTIVE" => Mode = "RUN"

\* Add to Spec
Spec == Init /\ [][Next]_vars /\ \* temporal properties

\* Verify your invariant
THEOREM Spec => []YourNewInvariant
====
```

Then verify:
```bash
tlc -config Phi16Extended.cfg Phi16Extended.tla
```

---

## Testing Guidelines

### Test Structure

**Test File Template:**
```python
"""
Test module for [feature name].

Tests:
1. test_basic_functionality - Basic operation
2. test_edge_cases - Boundary conditions
3. test_error_handling - Error scenarios
4. test_constraints - Token constraints
5. test_invariants - System invariants
"""

import sys
import os

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from tokens.system import HebrewTokenSystem
# ... other imports

def test_basic_functionality():
    """Test basic operation."""
    system = HebrewTokenSystem()
    system.initialize()

    # Test code
    assert system is not None
    assert len(system.registry.tokens) == 15

def test_edge_cases():
    """Test boundary conditions."""
    # Test empty input
    # Test maximum values
    # Test minimum values
    pass

def test_error_handling():
    """Test error scenarios."""
    # Test invalid input
    # Test constraint violations
    # Test state transition errors
    pass

def test_constraints():
    """Test token constraints."""
    # Test each relevant constraint
    pass

def test_invariants():
    """Test system invariants."""
    # Test DIA monotonicity
    # Test append-only
    # Test fail-closed
    pass
```

### Running Tests

**Quick Test (Simple Runner):**
```bash
cd /home/user/phi16
python3 tests/run_tests.py
```

**Full Test Suite:**
```bash
pytest tests/ -v
```

**Specific Test:**
```bash
pytest tests/test_ledger.py::test_hash_chain -v
```

**With Coverage:**
```bash
pytest --cov=. --cov-report=html tests/
open htmlcov/index.html
```

### Test Coverage Goals

Aim for:
- **Unit Tests:** Every function/method
- **Integration Tests:** Multi-component workflows
- **Invariant Tests:** All TLA+ invariants
- **Constraint Tests:** All token constraints
- **Edge Case Tests:** Boundary conditions
- **Error Tests:** All error paths

**Current Coverage:** 100% (9/9 tests passing)

### Writing Good Tests

**Good Test Characteristics:**
1. **Independent** - No dependencies on other tests
2. **Repeatable** - Same result every time
3. **Self-Checking** - Asserts success/failure
4. **Fast** - Runs in milliseconds
5. **Clear** - Obvious what is being tested

**Example:**
```python
def test_constraint_c01_no_automation_without_monitoring():
    """Test C01: Automation requires monitoring.

    Scenario:
    1. Activate T07 (Automation)
    2. T11 (Monitor) is not active
    3. Constraint C01 should fail
    4. Activate T11
    5. Constraint C01 should pass
    """
    system = HebrewTokenSystem()
    system.initialize()

    # Setup: Activate automation
    t07 = system.get_token('T07')
    t07.activate()

    # Test: Should fail without monitoring
    assert not system.constraints.check_constraint('C01'), \
        "C01 should fail: Automation active but monitoring inactive"

    # Setup: Activate monitoring
    t11 = system.get_token('T11')
    t11.activate()

    # Test: Should pass with monitoring
    assert system.constraints.check_constraint('C01'), \
        "C01 should pass: Both automation and monitoring active"
```

---

## Critical Pitfalls to Avoid

### 🚨 NEVER Do These

1. **NEVER Modify the Ledger Directly**
   ```python
   # ❌ WRONG
   ledger['events'].append(new_event)

   # ✅ CORRECT
   append_stream(ledger, new_event)
   ```

2. **NEVER Bypass Token Constraints**
   ```python
   # ❌ WRONG
   # Just execute without checking constraints
   execute_operation()

   # ✅ CORRECT
   if system.constraints.check_constraint('C01'):
       execute_operation()
   else:
       raise ConstraintViolation("C01 failed")
   ```

3. **NEVER Use Non-NAND Operations**
   ```python
   # ❌ WRONG
   result = a OR b

   # ✅ CORRECT
   result = nand(nand(a, a), nand(b, b))  # De-sugar to NAND
   ```

4. **NEVER Allow Direct Proposal-to-Execution**
   ```python
   # ❌ WRONG
   def propose_and_execute(change):
       proposal = create_proposal(change)
       execute(proposal)  # No review!

   # ✅ CORRECT
   def propose(change):
       proposal = create_proposal(change)
       return send_to_a2_for_review(proposal)
   ```

5. **NEVER Write During HOLD or SAFE States**
   ```python
   # ❌ WRONG
   append_stream(ledger, event)  # Ignores state

   # ✅ CORRECT
   if system_state == "RUN":
       append_stream(ledger, event)
   else:
       raise StateViolation(f"Cannot write in {system_state} state")
   ```

6. **NEVER Let Efficiency Override Ethics**
   ```python
   # ❌ WRONG
   if performance_critical:
       bypass_rights_check()  # Fast but unethical

   # ✅ CORRECT
   # ALWAYS check rights (T13), even if slow
   if not check_rights(request):
       reject(request)
   ```

7. **NEVER Skip Identity Validation**
   ```python
   # ❌ WRONG
   def process_request(data):
       # No identity check
       execute(data)

   # ✅ CORRECT
   def process_request(data, actor_id):
       if not validate_identity(actor_id):  # T05
           raise IdentityError("Unknown actor")
       execute(data)
   ```

8. **NEVER Delete Historical Events**
   ```python
   # ❌ WRONG
   del ledger['events'][old_event_index]

   # ✅ CORRECT
   # Events are immutable, create compensating event instead
   compensating_event = create_reversal(old_event)
   append_stream(ledger, compensating_event)
   ```

9. **NEVER Ignore DIA Drops**
   ```python
   # ❌ WRONG
   new_dia = calculate_dia(ledger)
   # Continue even if new_dia < old_dia

   # ✅ CORRECT
   new_dia = calculate_dia(ledger)
   if new_dia < old_dia:
       enter_safe_state()
       raise DIAViolation("DIA decreased")
   ```

10. **NEVER Force Recovery Without Conditions**
    ```python
    # ❌ WRONG
    if state == "HOLD":
        state = "RUN"  # Force recovery

    # ✅ CORRECT
    if state == "HOLD":
        if check_consensus_restored() and check_dia_restored():
            state = "RUN"
        else:
            raise RecoveryError("Conditions not met")
    ```

### ⚠️ Common Mistakes

1. **Forgetting to Initialize Token System**
   ```python
   # ❌ WRONG
   system = HebrewTokenSystem()
   # Use system without initializing

   # ✅ CORRECT
   system = HebrewTokenSystem()
   system.initialize()
   ```

2. **Not Checking Test Results**
   ```python
   # ❌ WRONG
   make test
   # Ignore failures and continue

   # ✅ CORRECT
   make test
   # If any test fails, stop and fix it
   ```

3. **Mixing Hebrew and English Inconsistently**
   ```python
   # ❌ INCONSISTENT
   # Use Hebrew token names in some places, English in others

   # ✅ CONSISTENT
   # Use T01-T15 consistently in code
   # Use full Hebrew names in documentation
   ```

4. **Not Updating Formal Specs**
   ```python
   # ❌ WRONG
   # Change code behavior without updating TLA+ specs

   # ✅ CORRECT
   # Update Phi16.tla whenever system behavior changes
   # Run make tla to verify
   ```

5. **Assuming Synchronous Operations**
   ```python
   # ⚠️ CAREFUL
   # Some operations may be asynchronous in future
   # Always handle async properly

   # ✅ CORRECT
   result = await process_request(request)
   # OR
   result = process_request(request)
   while not result.is_complete():
       wait()
   ```

---

## Quick Reference

### File Reference

**Need to...**
- Understand the system? → `README.md`
- Get started quickly? → `docs/ledger_quick_start.md`
- Understand tokens? → `docs/IMPLEMENTATION.md`
- See architecture? → `phi16_ascii_arch.txt`
- Check invariants? → `Phi16.tla`, `docs/A2_invariants.md`
- Modify ledger? → `ledger.py`
- Calculate DIA? → `sim_replay.py`
- Work with tokens? → `tokens/system.py`
- Add constraints? → `tokens/constraints.py`
- Test changes? → `tests/run_tests.py`
- See examples? → `examples/token_system_demo.py`

### Command Reference

```bash
# Testing
python3 tests/run_tests.py          # Quick test
make test                            # Full test suite
pytest tests/test_ledger.py -v      # Specific test

# Verification
make tla                             # Formal verification
make sim                             # Simulation test
make lint                            # Code style check

# Development
git checkout -b claude/your-feature-id  # New branch
git add .                            # Stage changes
git commit -m "feat: Description"   # Commit
git push -u origin claude/your-feature-id  # Push

# Examples
python3 examples/token_system_demo.py        # Token demo
python3 examples/phi_os_integration_demo.py  # Integration demo

# Ledger CLI
python3 ledger.py append event.json  # Append event
python3 ledger.py replay             # Replay ledger
python3 ledger.py validate           # Validate ledger
```

### API Reference

**Ledger Operations:**
```python
from ledger import append_stream, load_ledger, save_ledger, replay_stream

ledger = load_ledger('data/ledger.json')
error = append_stream(ledger, event, validate=True)
save_ledger(ledger, 'data/ledger.json')
errors = replay_stream(ledger)
```

**DIA Calculation:**
```python
from sim_replay import dia_graph, dia_info, dia_replay

dia_g = dia_graph(events)
dia_i = dia_info(events)
dia_r = dia_replay(events)
```

**Token System:**
```python
from tokens.system import HebrewTokenSystem

system = HebrewTokenSystem()
system.initialize()
system.enable_phi_os_integration()

token = system.get_token('T15')
is_valid = system.constraints.check_constraint('C01')
result = system.process_phi_os_request(request)
```

### Constraint Reference

```python
C01: No automation without monitoring    (T07 ← T11)
C02: No computation without security     (T03 ← T06)
C03: No governance without rights        (T08 ← T13)
C04: No unfair standards                 (T09 ← T10, T13)
C05: No anonymous network                (T02 ← T05, T06)
C06: No storage of violations            (T04 ← T13)
```

### Token Reference

```
T15 - Seriousness      (רצינות)        Priority: 96  [Emergency]
T13 - Rights           (זכויות אדם)     Priority: 94  [Supreme]
T01 - Data             (נתונים)         Priority: 95  [Foundation]
T06 - Security         (אבטחה)          Priority: 92  [Protection]
T10 - Measure          (מדידה)          Priority: 93  [Moral]
T11 - Monitor          (ניטור)          Priority: 89  [Moral]
T12 - Learn            (למידה)          Priority: 91  [Moral]
T08 - Govern           (ממשל)           Priority: 85  [Governance]
T09 - Standardize      (תקינה)          Priority: 87  [Governance]
T05 - Identity         (זהות)           Priority: 88  [Governance]
T07 - Automation       (אוטומציה)       Priority: 86  [Execution]
T03 - Compute          (חישוב)          Priority: 85  [Execution]
T04 - Storage          (אחסון)          Priority: 85  [Execution]
T02 - Network          (רשת)            Priority: 90  [Infrastructure]
T14 - Commons          (משאבים משותפים)  Priority: 85  [Infrastructure]
```

### State Machine Reference

```
States:
- RUN:  Normal operation
- HOLD: Consensus failure (AND-0+ failed), no writes
- SAFE: Policy violation (DIA drop), no writes

Transitions:
RUN → HOLD: Consensus failure
RUN → SAFE: DIA < threshold OR risk > threshold
HOLD → RUN: Consensus restored AND DIA restored
SAFE → RUN: DIA restored AND explicit approval
```

### Invariant Reference

```
AppendOnlyMonotone:    Len(L') >= Len(L)
NoWriteInHold:         Mode = "HOLD" => No appends
NoWriteInSafe:         Mode = "SAFE" => No appends
ProposalNotCommitment: Φ cannot commit directly
DIAMonotonicity:       DIA' >= DIA (when tau = 0)
```

---

## Getting Help

### Documentation Hierarchy

1. **This File (CLAUDE.md)** - AI assistant guide
2. **README.md** - System overview and master plan
3. **docs/standard_phi16_v1.md** - Complete v1.0 standard (Hebrew)
4. **docs/IMPLEMENTATION.md** - Token system implementation guide
5. **docs/whitepaper_phi16.md** - Philosophy and rationale
6. **spec/** - Formal specifications

### When You're Stuck

1. **Check the docs:** Most answers are in `docs/`
2. **Read the tests:** `tests/` shows expected behavior
3. **Check the examples:** `examples/` shows usage patterns
4. **Read the specs:** `spec/` has formal definitions
5. **Check git history:** Recent commits show patterns

### Debugging Tips

**Ledger Issues:**
```python
# Enable verbose output
import logging
logging.basicConfig(level=logging.DEBUG)

# Validate manually
import jsonschema
jsonschema.validate(event, schema)
```

**Token Issues:**
```python
# Print system state
system.print_system_state()

# Check specific constraint
result = system.constraints.check_constraint('C01')
print(f"C01: {result}")

# Check token state
token = system.get_token('T15')
print(f"T15 state: {token.state}")
```

**TLA+ Issues:**
```bash
# Run with verbose output
tlc -config Phi16.cfg -verbose Phi16.tla

# Check specific invariant
# Edit Phi16.cfg to specify invariant
```

---

## Changelog

### Version 1.0 (2025-12-04)

**Initial release covering:**
- Core principles and inviolable rules
- Complete codebase structure
- Development workflows
- Key conventions
- Token system guide
- Common tasks
- Testing guidelines
- Critical pitfalls
- Quick reference

**Recent System Changes:**
- Hebrew Token System integration (complete)
- Φ-OS integration layer (complete)
- 15 tokens across 6 layers (complete)
- 9/9 tests passing (100% coverage)

---

## License

This document is part of the phi16 project, licensed under MIT License.

See LICENSE file in repository root.

---

## Contributing

When contributing to phi16:

1. **Read this document thoroughly**
2. **Follow all core principles** (no exceptions)
3. **Write tests for all changes**
4. **Update documentation** (code + specs)
5. **Run full test suite** before committing
6. **Create descriptive pull requests**

**Remember:** Ethics before technology. Correctness before performance. Verification before deployment.

---

*End of CLAUDE.md*
