# Architecture — DyNetKAT Lean Formalization

## Symbolic native KAT

`KATLean.Native` decides the pure KAT equational theory using reduced ordered
Boolean decision trees and symbolic partial derivatives.
`decideEquiv_iff_equational` characterizes derivability from the KAT rules and
`decideEquiv_iff_algebraicallyEquivalent` characterizes equality in every
abstract KATLean model. `nativeSolver_derives` yields a NetKAT derivation
under any substitution of primitive actions and tests.

`netkatNativeEquiv` adds executable symbolic equivalence for the current
dup-free NetKAT AST. KATLean → native KAT → symbolic packet frontend →
NetKAT equivalence → E_NK → E_DNK is the resulting proof path.
`netkatNativeEquiv_correct` is independent of KATch, concrete packet
enumeration and Boolean valuation enumeration. The E_NK completeness proof
uses symbolic closure and the field-level partition axiom. The public
`netkatEquiv` and `netkatIsZero` APIs serve graph normalization and safety
through the symbolic checker. `legacyNetkatEquiv` is the regression oracle.

See the [symbolic frontend and dependency audit](NETKAT_AUDIT.md).

See [NATIVE_KAT.md](NATIVE_KAT.md) for the theorem chain and proof construction.

## Native solver boundary

The algebraic pipeline runs from KATLean and verified native KAT
through symbolic dup-free NetKAT equivalence and normalization, then E_NK,
DyNetKAT head normalization and E_DNK. Equivalence compares encoded
relations through native KAT. Normalization exports accepted packet pairs
from the same compiled diagram for Lemma 5 and the packet-prefix case of
Lemma 9. Its proof uses symbolic star elimination, KATLean-backed packet
laws and pair-sum extensionality. Source admission, reachable Residuals and
SOS remain unchanged.

`import KATLean.Native` is a separate Mathlib/KATLean-only surface, also exported
by `DyNetKAT`. It contains guarded-language syntax, finite partial derivatives,
subset-state search and a complete all-relational-model correctness theorem.
It does not import concrete packet evaluation or experimental backends.
The algebra-only `KATLean` import stays below it.

The packet frontend compiles syntax to a reduced ordered diagram for a binary
packet relation. Identity, tests and assignments impose one-hot field constraints.
Composition renames endpoints to a common middle bank and existentially projects
it out. Star reaches a canonical diagram fixed point using relational squaring.
The final diagram is embedded as a native KAT test on packet-pair encodings.
[Exact scope and audit](NETKAT_AUDIT.md).

## Graph normalization and concrete execution

The classical exact-table existence theorem uses the finite reachable
derivatives and the syntactic prefix labels of each source and its graph
definitions. Each packet label retains the policy of its originating SOS
prefix. The symbolic zero check determines feasibility without expanding
the relation into packet pairs. The checked-table renderer and safety
checker consume those policy labels.

Concrete execution starts with one supplied packet. Each star round unions
the previous outputs with their one-step successors and stops once those
sets agree. Executable fuel comes from field counts. The correctness proof
bounds strict growth using the cardinality of the packet type.

## Current architecture

The paper-facing core follows DyNetKAT source grammar, the `Program` /
reachable `Residual` semantic boundary, SOS semantics, KATLean, dup-free
NetKAT E_NK, DyNetKAT E_DNK and certified analysis. Mathlib provides the KA
classes; KATLean supplies Boolean tests, packet laws and the algebraic
interpretation connected to the current AST, evaluator and Derives.

| Import surface | Scope |
|---|---|
| `KATLean` | Algebra and packet model, with Mathlib dependencies |
| `DyNetKAT.NetKAT.KATLean` | Current NetKAT AST/evaluator/Derives bridge |
| `DyNetKAT` | Core formalization and admitted-program analysis |
| `DyNetKAT.NetKAT.Legacy` | Exhaustive concrete equivalence, normalization and partition proofs for regression and compatibility |
| `DyNetKAT.Experimental` | Core plus optional KATch comparison and candidate-checking modules |

The core import closure excludes the legacy exhaustive module, KATch, backend certificates, equational
certificates and JSON candidate formats. Python subprocess replay is an
optional experiment. KATch is an untrusted external comparison point and
possible future accelerator, with no release, completeness or theorem
prerequisite. The full NetKAT history/dup extension is outside current
DyNetKAT scope. Dup-free history correspondence remains supporting evidence
for the SOS packet rule.

See [KATLEAN.md](KATLEAN.md) for the axiom mapping and
[NETKAT_AUDIT.md](NETKAT_AUDIT.md#dependency-audit) for import evidence.

## Finite packet-schema foundation

NetKATLean's `PacketSchema` packages finite dependent field domains
and the existing KATLean `PacketModel` lookup and update laws over
total valuations. `PacketSchema.ofFields` uses dependent point
updates. `ctxSchema` retains the original four fields and four values
per field, with the original `Packet.update` operation.
The syntax types default to `ctxSchema`. Standalone expressions whose
context supplies no schema can use a type annotation, such as
`(.assign1 .port .v1 : NetKAT)`. Custom schemas use
`NetKAT.fieldTestFor` and `RecEnv.emptyFor`.

The same schema indexes the dup-free policy syntax and its packet
and history semantics. The supplied-packet evaluator compares fields
and visits only reachable output packets. Its star fuel is the product
of the finite field cardinalities, and its iteration stops at a fixed
point. KATLean's relational interpretation and native diagram frontend
are generic. Each of the three diagram banks has one bit per legal
field/value pair. `DiagramLayout` provides bit ordering for an existing
`PacketSchema`. `PacketSchema.diagramLayouts` constructs an executable
layout up to ordering by enumerating the fields and their disjoint
sum of value domains. `netkatNativeEquivFinite` eliminates that choice
using the proof that semantic equivalence is independent of layout.

DyNetKATLean uses that policy and packet boundary for process
and label syntax, `Step` and `Steps`, guarded declarations, admission,
and source traces. The generic history correspondence and
Proposition 1 retain syntactic communication payload matching.
`symbolicNormalFormFor` keeps the compact relation diagram.
`symbolicPairsFor` expands accepting paths for the explicit paper
syntax, which can itself be large for a dense relation. NetKATLean's
`Derives` uses field-local coverage for complete test expansion and
PA-MATCH-ALL. Its completeness proof uses only field partitions and
symbolic star closure. `Equations.packetHeads_bisimilar` gives the
source SOS meaning of the resulting choice of packet heads.
The letter and trace-safety specification layer is generic, including
the source translation and padded-word semantics. The full DyNetKATLean
head normalization proofs, graph compiler, projection renderer,
equational trace-safety results, and trace-safety checkers still use
`CtxPkt`.

## Future supported package boundaries

The deferred target has Mathlib below KATLean, NetKATLean above KATLean,
and DyNetKATLean consuming the two lower layers. Public umbrellas and
correctness theorems will support independent clients. Lake dependency
checks, transitive import checks, and external consumer projects will
verify the direction and accessibility of the interfaces. See the
[modularization plan](MODULARIZATION_PLAN.md) for the packaging,
verification, and migration sequence.

## Historical design sketch

The initial layout and design notes below predate the current module
organization. Use the import surfaces above and current proof ledger for
implementation and completion status.

```
lean/
├── DyNetKAT.lean          -- initial library-root sketch
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

`SourceTrace.lean` exposes the source `Steps` relation at the admitted
program boundary. Action words preserve packet observations and
communication labels. `TraceEquations.lean` extends the typed
equational theory with A16 and proves trace completeness using finite
word sums and AIP. `TraceSafety.lean` renders the translated specification
as an admitted program and proves Eq. (27). `TraceEnvironment.lean`
puts the specification and implementation in one declaration system
without changing either trace language.

`TraceSafetyCheck.lean` checks supplied words through certified
symbolic moves. The source theorem applies without a compiled graph.
`Reachability.lean` connects endpoint queries through
`SequentialReachability.lean` to feasible source traces. Each structural
tail segment ends at a selected reconfiguration and can precede another
tail segment. Graph paths use `GSteps` with canonical packet lists and
transport to source `Steps`. The bounded workflow renders an exact
projection and prunes impossible packet prefixes using symbolic zero.
The exact-row certificate provides a separate all-depth route.

`renderProjection_bisimilar` proves semantic exactness against the source
SOS. `ProjectionDerivation.lean` proves a separate E_DNK result for the
same output. Depth induction derives a ground process using closed head
normalization and the Π rules. Ground completeness then identifies its
bisimulation class with that of the rendered term. The admitted compiled
state API covers ordinary, total, and memoized rendering. The result
supplies finite-depth derivations that can be composed at each depth before
applying the existing all-depth rule `Derives.aip_guarded`.



## Python role

Python handles only:
- Golden-value tests for the NetKAT semantics (small examples).
- FatTree generation for potential experiments (future work).
- `scripts/verify.sh` orchestration.

Python does **not** implement or validate any DyNetKAT semantics.
