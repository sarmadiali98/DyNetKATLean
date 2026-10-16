# Architecture — DyNetKAT Lean Formalization

## Overview

Lean 4 is the trusted semantic core.  Python is an untrusted adapter for
auxiliary scripts and experiments only.

```
lean/
├── DyNetKAT.lean          -- library root (imports all modules)
├── DyNetKAT/
│   ├── Basic.lean         -- foundational types, Fintype setup
│   ├── NetKAT/
│   │   ├── AST.lean       -- NetKAT⁻ᵈᵘᵖ syntax
│   │   ├── Packet.lean    -- packet model, fields, values, complete test/assign
│   │   ├── Semantics.lean -- denotational semantics ⟦N⟧
│   │   ├── Axioms.lean    -- E_NK axiomatization
│   │   └── NormalForm.lean-- Lemma 5
│   ├── DyNetKAT/
│   │   ├── AST.lean       -- DyNetKAT syntax (extended, Eq. 6)
│   │   ├── Semantics.lean -- labeled SOS (Fig. 8)
│   │   ├── Config.lean    -- configurations (d, H, H′)
│   │   ├── Action.lean    -- labels γ
│   │   └── Operators.lean -- δ, π, rcfg, ⌊⌊, | |
│   ├── Bisimulation.lean  -- Definition 2, Lemma 3, Proposition 1
│   ├── Axioms.lean        -- A0–A15, AIP, A16 (Fig. 11)
│   ├── Derivability.lean  -- E_DNK ⊢ p ≡ q
│   ├── NormalForm.lean    -- Definition 6, Lemma 9
│   ├── Guardedness.lean   -- Definition 7, Lemma 8
│   ├── Soundness.lean     -- Lemma 10, 11; Theorem 1
│   ├── Completeness.lean  -- Theorem 1 (ground-completeness)
│   ├── Safety/
│   │   ├── AST.lean       -- Definitions 12, 13, 17
│   │   ├── Semantics.lean -- Definition 14 (⟦−⟧, Θ)
│   │   ├── Derivability.lean -- Definition 15, 16
│   │   └── Examples.lean  -- §IV-A examples
│   └── Examples/
│       ├── Firewall.lean
│       └── DistributedController.lean
├── lakefile.toml
└── lean-toolchain

python/
├── pyproject.toml
├── tests/
│   ├── conftest.py
│   └── test_*.py  -- golden tests, adapter tests
└── scripts/
    └── verify.sh
```

## Design decisions

### 1. Mathlib dependency

**Decision:** Use Mathlib4.  The formalization requires `Fintype`, `Finset`,
`Set`, and coinductive types that are much better supported in Mathlib than
in Lean 4 core.  The existing repo's pure-core approach avoided Mathlib,
but a faithful formalization of the paper's completeness and bisimulation
results will need richer library support.

**Rationale:** The paper's proofs rely on:
- Finite sets (complete tests, assignments, normal-form summands).
- Coinduction (bisimilarity).
- Set operations (denotations as relations).
Mathlib provides battle-tested definitions for all of these.

### 2. Self-contained NetKAT

**Decision:** Implement NetKAT⁻ᵈᵘᵖ from scratch, NOT wrapping DyNetiKAT,
Maude, KATch, or any external implementation.

**Rationale:** Per the task requirements.  The NetKAT model is the dup-free
fragment with denotational semantics ⟦N⟧ ⊆ Packet × Packet.

### 3. Coinductive bisimilarity

**Decision:** Use Lean 4's `coinductive` types (or manually coded greatest
fixed point) for bisimilarity.

**Rationale:** The paper defines bisimilarity as the largest bisimulation
(coinductive).  Lean 4 supports `coinductive` predicates.

### 4. Guarded recursion

**Decision:** Represent recursive DyNetKAT terms with explicit `recurse`
and `var` constructors, plus a separate guardedness check.

**Rationale:** The paper uses `X` with unique definition `X ≜ d`.  Guardedness
(Definition 7) ensures the recursion is well-behaved.

### 5. Configuration representation

**Decision:** Use exactly the paper's `(d, H, H′)` configuration structure:
```lean
structure Config where
  proc : DyNetKAT
  pending : List Packet    -- H  (cons notation in paper)
  handled : List Packet    -- H' (cons notation in paper)
```

**Rationale:** Faithful to the paper.  No `flowTable` field (that's a journal-
extension artifact).

### 6. Action/label type

**Decision:** Labels exactly as the paper specifies:
```lean
inductive Action where
  | packet (input output : Packet)   -- (σ, σ′)
  | recv (channel : Channel) (policy : NetKAT)    -- x?r
  | send (channel : Channel) (policy : NetKAT)    -- x!r
  | rcfg (channel : Channel) (policy : NetKAT)    -- rcfg(x, r)
```

**Rationale:** Faithful to §II-B, Fig. 8.

### 7. Parameterization

**Decision:** Parameterize the packet model over finite field types.
The paper does not fix specific fields, so we use:
```lean
variable [Fintype FieldType] [∀ f : FieldType, Fintype (Value f)]
```

**Rationale:** The paper says "we consider network packets with values in
finite domains" — parameterization respects this without fixing specifics.

### 8. Executable vs. proof

**Decision:** Separate the mathematical semantics (Prop-valued relations)
from any executable decision procedures.  The denotational semantics
`⟦N⟧` is a relation `Packet → Set Packet`, not an executable evaluator.

**Rationale:** Per the task: "Never confuse testing with mathematical proof."

## Semantic layering

The architecture mirrors the paper's structure:
1. **NetKAT** — finite packet domains, denotational semantics, E_NK.
2. **DyNetKAT syntax** — builds on NetKAT⁻ᵈᵘᵖ.
3. **Operational semantics** — SOS over (d, H, H′).
4. **Extensions** — δ, π, rcfg, ⌊⌊, | |.
5. **Bisimilarity** — coinductive, congruence.
6. **Axioms** — A0–A15, AIP, A16.
7. **Soundness & completeness** — Theorem 1.
8. **Safety** — Definitions 12–17.

## Python role

Python handles only:
- Golden-value tests for the NetKAT semantics (small examples).
- FatTree generation for potential experiments (future work).
- `scripts/verify.sh` orchestration.

Python does **not** implement or validate any DyNetKAT semantics.
