# PAPER_CONFORMANCE.md — DyNetKAT FoSSaCS Paper Conformance Map

**Paper version:** *DyNetKAT: An Algebra of Dynamic Networks*
arXiv:2102.10035v4 (22 May 2021).  FoSSaCS 2022.

**Scope:** The original DyNetKAT calculus only — its syntax, operational
semantics, equational theory, bisimilarity, normal forms, semantic results,
and safety framework.  The journal extension (log-based extraction, bounded
schedules, SDNRacer-specific causality) is deliberately out of scope.

---

## I. NetKAT Preliminaries

The DyNetKAT paper builds on NetKAT [Anderson et al., POPL 2014].  The
dup-free fragment, denoted **NetKAT⁻ᵈᵘᵖ**, is the foundation.

### 1. Packet model

**Paper location:** printed p. 5, §"Network packets" (within §I-A);
also §I-B "The NetKAT Language".

**Mathematical statement:**
A network packet is a function σ from a finite set of field names to a finite
set of values: `σ : Fields → Values`.  Complete tests α are predicates of the
form `f₁=v₁ · … · fₙ=vₙ`; complete assignments π are `f₁←v₁ · … · fₙ←vₙ`.
The sets **A** (all complete tests) and **Π** (all complete assignments) are
**finite** by the finite-domain assumption.

**Assumptions & side conditions:**
- Field names and value domains are finite.
- This finiteness makes **A** and **Π** finite.

**Required Lean representation:**
- A `FieldType` type (finite enumeration of field names).
- For each field, a finite value set; package as `FieldSpec : FieldType → Type`.
- `Packet := FieldType → Value` but since values are finite per field, use a
  structured record or finite-map representation.
- `CompleteTest` and `CompleteAssignment` as inductive types or finite
  products over `FieldType`.
- Lemmas that **A** and **Π** are finite (`Fintype` instances).

**Dependencies:** None (root of the model).

**Proof obligation:** Establish `Fintype Packet` (or equivalently finiteness
of **A** and **Π**) from the finite-domain assumption.

**Ambiguities / open questions:**
- The paper does not fix the specific field set; it is parameterized.
  **Recommendation:** parameterize over a `Fintype FieldType` and finite
  per-field value types.

**Implementation status:** Not started (new repo).

### 2. NetKAT syntax (dup-free)

**Paper location:** printed p. 6, §I-B.

**Mathematical statement:**
```
N ::= 0 | 1 | f=v | f←v | α | π | N + N | N;N | N*
```
where `α` ranges over complete tests, `π` over complete assignments, `0` = drop,
`1` = identity, `+` = choice, `;` = sequential composition, `*` = Kleene star.

(The full NetKAT also has `dup`; DyNetKAT uses **NetKAT⁻ᵈᵘᵖ**, i.e. without `dup`.)

**Assumptions & side conditions:**
- No `dup` operator in this fragment.

**Required Lean representation:**
```lean
inductive NetKAT
  | drop       -- 0
  | id         -- 1
  | test       -- α (complete test)
  | assign     -- π (complete assignment)
  | union      -- N + N
  | seq        -- N ; N
  | star       -- N *
```

**Dependencies:** Packet model (complete tests & assignments).

**Proof obligation:** None for syntax alone.

**Ambiguities / open questions:**
- Whether `test`/`assign` should be parameterized by concrete field=value or
  by the abstract `CompleteTest`/`CompleteAssignment` types.
  **Recommendation:** use abstract types; the concrete packet semantics unfolds
  them.

**Implementation status:** Not started.

### 3. NetKAT denotational semantics

**Paper location:** printed p. 6, §I-B / "Semantics".

**Mathematical statement:**
⟦N⟧ ⊆ Packet × Packet, defined compositionally:
- ⟦0⟧ = ∅
- ⟦1⟧ = {(σ,σ)}
- ⟦f=v⟧ = {(σ,σ) | σ(f) = v}
- ⟦f←v⟧ = {(σ,σ[f↦v])}
- ⟦α⟧ = product of field tests
- ⟦π⟧ = product of field assignments
- ⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧
- ⟦N₁;N₂⟧ = ⟦N₁⟧ ∘ ⟦N₂⟧
- ⟦N*⟧ = ⋃ₖ ⟦N⟧ᵏ  (reflexive-transitive closure over finite domain)

**Assumptions & side conditions:**
- Finite packet domain ⟹ the reflexive-transitive closure is itself finite.
- `⟦N*⟧ = id ∧ N` (Kleene star as iteration).

**Required Lean representation:**
- `⟦N⟧ : Packet → Set Packet` (or `Packet → List Packet` for executable form).
- Define union, composition, Kleene star (`rtc` of composition).
- Prove finite-domain finiteness of the star's iteration.

**Dependencies:** Packet model; NetKAT syntax.

**Proof obligation:**
- `⟦N*⟧` is well-defined (finite union terminates).
- Basic identities: `⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧`, etc.

**Ambiguities / open questions:** None significant.

**Implementation status:** Not started.

---

## II. DyNetKAT Syntax

### 4. Process syntax

**Paper location:** printed p. 8, §II, §II-A "Syntax".  Fig. 5.

**Mathematical statement:**
```
d ::= ⊥ | N;d | x?N;d | x!N;d | rcfg(x,r);d | d‖d | d⊕d | X
```
where `N ∈ NetKAT⁻ᵈᵘᵖ`, `x` ranges over channel names, `r` over NetKAT⁻ᵈᵘᵖ
(used in rcfg), `X` over a (countably infinite) set of recursive variables.

**Assumptions & side conditions:**
- `⊥` (deadlock) is the neutral element of `⊕`.
- `;` binds tighter than `⊕`, `‖`, `| |` — but precedence varies; use explicit
  grouping in Lean.
- Channels form a countably infinite set.
- Recursive variables are uniquely defined (`X ≜ d`).

**Required Lean representation:**
```lean
inductive DyNetKAT
  | deadlock           -- ⊥
  | nSeq               -- N ; d     (NetKAT policy then continuation)
  | recv               -- x?N;d     (receive NetKAT policy on channel x)
  | send               -- x!N;d     (send NetKAT policy on channel x)
  | rcfg               -- rcfg(x,N);d
  | parallel           -- d ‖ d
  | choice             -- d ⊕ d
  | var                -- X  (recursive variable, indexed by Nat or Symbol)
```
With a `Label` type for variables and a `Subst` relation for recursion.

**Dependencies:** NetKAT syntax (N).

**Proof obligation:** None for syntax.

**Ambiguities / open questions:**
- `rcfg(x,r)` — the paper uses `r` for a NetKAT⁻ᵈᵘᵖ term (same as `N`).
  The rcfg constant itself takes channel `x` and NetKAT term `r`.

**Implementation status:** Not started.

### 5. Multi-packet configurations

**Paper location:** printed p. 9, §II-B "Operational Semantics".

**Mathematical statement:**
Configuration: `(d, H, H′)`
- `d`: current DyNetKAT process term.
- `H`: pending packet list (front = newest packet to process).
- `H′`: handled (output) packet list (front = newest handled packet).

The paper writes `σ :: H` and `H′` using cons notation.

**Assumptions & side conditions:**
- Packet lists are finite.
- Per-packet consistency: each packet is processed by exactly one NetKAT
  policy throughout its flight (printed p. 9, §II-B).

**Required Lean representation:**
```lean
structure Config where
  proc : DyNetKAT
  pending : List Packet   -- H  (front = head)
  handled : List Packet   -- H' (front = head)
```

**Dependencies:** Packet model; DyNetKAT syntax.

**Proof obligation:** Per-packet consistency is a design property (assumption),
not a formal theorem.  The formal correctness result is semantic layering
(Proposition 1, §III).

**Ambiguities / open questions:**
- Whether `H` is a list or multiset.  **Paper evidence:** printed p. 9 uses
  cons notation `σ :: H`, and the configurations `(d, H, H′)` in the
  transition rules show ordered lists.  **Recommendation:** use `List Packet`
  with `σ :: H` semantics.

**Implementation status:** Not started.

### 6. Labels and actions

**Paper location:** printed p. 9, §II-B; Fig. 8.

**Mathematical statement:**
Labels (actions) γ are:
```
γ ::= (σ, σ′) | x?r | x!r | rcfg(x, r)
```
- `(σ, σ′)`: a packet-flow action — packet σ is transformed into σ′ by a
  NetKAT policy.
- `x?r`: receive action (NetKAT policy on channel x).
- `x!r`: send action (NetKAT policy on channel x).
- `rcfg(x, r)`: reconfiguration (synchronization of send/receive).

**Assumptions & side conditions:** None.

**Required Lean representation:**
```lean
inductive Action where
  | packet (input output : Packet)
  | recv (channel : Channel) (policy : NetKAT)
  | send (channel : Channel) (policy : NetKAT)
  | rcfg (channel : Channel) (policy : NetKAT)
```

**Dependencies:** Packet; NetKAT; Channel (countably infinite).

**Proof obligation:** None.

**Ambiguities / open questions:**
- `r` in `rcfg(x, r)` and `x?r`, `x!r` — is it NetKAT⁻ᵈᵘᵖ or full NetKAT?
  **Paper evidence:** printed p. 8, §II-A: "x?N", "x!N" use `N ∈ NetKAT⁻ᵈᵘᵖ`.
  The rcfg action carries the same.  **Recommendation:** use `NetKAT` (the
  dup-free fragment) throughout DyNetKAT.

**Implementation status:** Not started.

---

## III. Operational Semantics

### 7. Small-step labeled transition rules (Fig. 8)

**Paper location:** printed p. 9–10, §II-B, Fig. 8.

**Mathematical statement — transition relation:**
`(d, H, H′) →γ (d′, H′′, H′′)`

The paper's rules (Fig. 8).  The rule names below follow the appendix convention
`cpol_*` (seen in the ar5iv appendix output at printed p. 2550+).

**Rule (cpol_;✓) — packet flows through NetKAT policy:**
```
       σ′ ∈ ⟦N⟧(σ)
  (N;d, σ::H, H′) →(σ,σ′) (d, H, σ′::H′)
```
Condition: σ′ ∈ ⟦N⟧(σ), i.e., N maps packet σ to some output σ′.
The packet σ is removed from the head of `H` and σ′ is pushed to `H′`.

**Rule (cpol_;✗) — packet dropped by NetKAT policy:**
```
     ⟦N⟧(σ) = ∅
  (N;d, σ::H, H′) →(σ,⊥?) (d, H, H′)   [drop: packet consumed, no output]
```
**Ambiguity (pending figure verification):** the ar5iv extraction does not
show the exact label for the drop case.  The existing repo's `Semantics/Basic.lean`
uses `.drop input` / `Label.drop`.  **Recommendation:** define the drop
transition as consuming σ from `H` without producing output in `H′`; the
label should match Fig. 8 precisely.

**Rule (cpol_⊕) — choice left/right:**
```
  (p, H, H′) →γ (p′, H″, H‴)
  (p⊕q, H, H′) →γ (p′, H″, H‴)
```
(symmetrically for q, with `q′`)

**Rule (cpol_‖) — parallel component step (asynchronous):**
```
  (p, H, H′) →γ (p′, H″, H‴)
  (p‖q, H, H′) →γ (p′‖q, H″, H‴)
```
(symmetrically for right component `q → q′`)

**Rule (cpol_;_‖) — NetKAT policy in left of parallel:**
```
  (N;d, H, H′) →γ (d, H″, H‴)
  ((N;d)‖q, H, H′) →γ (d‖q, H″, H‴)
```
This is a specialization of `cpol_‖` for the `N;d` prefix.

**Rule (cpol_recv) — receive (asynchronous):**
```
  (x?N;d, H, H′) →(x?r) (d, H, H′)
```

**Rule (cpol_send) — send (asynchronous):**
```
  (x!N;d, H, H′) →(x!r) (d, H, H′)
```

**Rule (cpol_sync) — synchronization (synchronous):**
```
  (p, H, H′) →(x?r) (p′, H″, H‴)
  (q, H, H′) →(x!r) (q′, H″, H‴)
  (p‖q, H, H′) →(rcfg(x,r)) (p′‖q′, H″, H‴)
```
(symmetrically: left sends, right receives)

**Assumptions & side conditions:**
- Transitions preserve per-packet consistency.
- For synchronization, the send and receive must be on the same channel `x`
  with the same NetKAT policy `r`.

**Required Lean representation:**
```lean
inductive Step : Config → Action → Config → Prop
  | cpol_seq_ok ...
  | cpol_seq_bad ...
  | cpol_choice_l ...
  | cpol_choice_r ...
  | cpol_par_l ...
  | cpol_par_r ...
  | cpol_par_seq ...
  | cpol_recv ...
  | cpol_send ...
  | cpol_sync ...
```

**Dependencies:** DyNetKAT syntax; Action type; NetKAT denotational semantics;
Packet model; Config structure.

**Proof obligation:**
- Each rule is well-formed.
- The relation is the least relation closed under the rules.

**Ambiguities / open questions:**
- Exact handling of `H` / `H′` in synchronization.
- Exact label for the drop case.

**Implementation status:** Not started.  (Critical: all subsequent semantic
results depend on this.)

---

## IV. Extended DyNetKAT Operators

### 8. Restriction operator δ_ℒ(−)

**Paper location:** printed p. 12, §III; Eq. (2).

**Mathematical statement:**
For ℒ ⊆ {actions of shape `x?N`, `x!N`}, the restriction operator filters
transitions whose labels are in ℒ:
```
  (p, H, H′) →γ (p′, H″, H‴)    γ ∉ ℒ
  (δ_ℒ(p), H, H′) →γ (δ_ℒ(p′), H″, H‴)
```

**Assumptions & side conditions:**
- ℒ ranges over actions `x?N` and `x!N` only.

**Required Lean representation:**
```lean
def δ (L : Set Action) (d : DyNetKAT) : DyNetKAT  -- or as a Step rule
```

**Dependencies:** Step relation; Action type.

**Proof obligation:** δ is a congruence w.r.t. bisimilarity.

**Ambiguities / open questions:** None significant.

**Implementation status:** Not started.

### 9. Projection operator π_n(−)

**Paper location:** printed p. 12, §III; Eq. (3).

**Mathematical statement:**
π_n captures the first n steps of a DyNetKAT policy:
```
  (p, H, H′) →γ (p′, H″, H‴)
  (π_{n+1}(p), H, H′) →γ (π_n(p′), H″, H‴)
```

**Assumptions & side conditions:**
- n ∈ ℕ.

**Required Lean representation:**
```lean
def π (n : Nat) (d : DyNetKAT) : DyNetKAT
```
Plus the Step rule lifting.

**Dependencies:** Step relation.

**Proof obligation:** π_n is well-defined; AIP soundness proof uses π_n.

**Ambiguities / open questions:** None significant.

**Implementation status:** Not started.

### 10. rcfg constant (synchronization constant)

**Paper location:** printed p. 13, §III-A; Eq. (4).

**Mathematical statement:**
```
  (rcfg_{x,z};p, H, H′) →(rcfg(x,z)) (p, H, H′)
```
The constant `rcfg(x,r)` represents a synchronization step carrying
channel `x` and NetKAT policy `r`.

**Required Lean representation:**
```lean
-- rcfg(x, N) as a built-in constant in the DyNetKAT syntax
| rcfg : Channel → NetKAT → DyNetKAT → DyNetKAT
-- plus a Step rule:
| cpol_rcfg ...
```

**Dependencies:** DyNetKAT syntax; Step relation.

**Proof obligation:** The rcfg constant steps immediately to its continuation.

**Ambiguities / open questions:**
- The paper introduces rcfg as a syntactic constant `rcfg_{x,z}` and also
  as an action label `rcfg(x,r)`.  These must be distinguished: the constant
  is part of the syntax; the label is the transition action.
**Implementation status:** Not started.

### 11. Left-merge (⌊⌊) and communication-merge (| |)

**Paper location:** printed p. 13, §III-A; Eq. (5).

**Mathematical statement:**

**Left-merge rule (⌊⌊):**
```
  (p, H₀, H₁) →γ (p′, H₀′, H₁′)    γ ∈ {(σ,σ′), x!r, x?r, rcfg(x,r)}
  (p⌊⌊q, H₀, H₁) →γ (p′‖q, H₀′, H₁′)
```

**Communication-merge rule (| ?!):**
```
  (p, H, H′) →(x?r) (p′, H, H′)    (q, H, H′) →(x!r) (q′, H, H′)
  (p|q, H, H′) →(rcfg(x,r)) (p′‖q′, H, H′)
```

**Communication-merge rule (| !?):**
```
  (p, H, H′) →(x!r) (p′, H, H′)    (q, H, H′) →(x?r) (q′, H, H′)
  (p|q, H, H′) →(rcfg(x,r)) (p′‖q′, H, H′)
```

**Assumptions & side conditions:**
- Left-merge allows any action except the "otherwise" case.
- Communication-merge fires when one side sends and the other receives on the
  same channel with the same policy.

**Required Lean representation:**
Add `leftMerge` and `commMerge` constructors to DyNetKAT, plus Step rules.
```lean
inductive DyNetKAT
  | ...
  | leftMerge : DyNetKAT → DyNetKAT → DyNetKAT   -- p ⌊⌊ q
  | commMerge : DyNetKAT → DyNetKAT → DyNetKAT   -- p | q
```

**Dependencies:** DyNetKAT syntax; Step relation; Action type.

**Proof obligation:** Correctness of A8–A11 (left-merge) and A12–A15
(communication-merge) axioms.

**Ambiguities / open questions:**
- Whether `| |` and `⌊⌊` are syntactic sugar or primitive operators.
  **Paper evidence (printed p. 13):** they appear in the extended syntax
  (Eq. 6) as primitive constructors of D_e.
  **Recommendation:** treat them as primitive for the formalization.

**Implementation status:** Not started.

### 12. Full DyNetKAT syntax (extended form, Eq. 6)

**Paper location:** printed p. 14, §III-A; Eq. (6).

**Mathematical statement:**
```
N := NetKAT⁻ᵈᵘᵖ
D_e ::= ⊥ | N;D_e | x?N;D_e | x!N;D_e | rcfg_{x,N};D_e | D_e‖D_e | D_e⊕D_e
        | δ_ℒ(D_e) | π_n(D_e) | D_e⌊⌊D_e | D_e|D_e | X
```
where n ∈ ℕ, ℒ = {c | c ::= x?N | x!N}.

**Required Lean representation:** Combine all constructors above into one
`inductive DyNetKAT` type, with `Channel : Type := Nat` (or a custom type).

**Dependencies:** All prior sections.

**Proof obligation:** Syntax is well-defined; guardedness (Definition 7) is
decidable or at least definable.

**Ambiguities / open questions:**
- Recursion via `X` requires a `recurse` or `fix` construct with environment.

**Implementation status:** Not started.

---

## V. Equational Theory (Axioms A0–A15)

### 13. Axioms A0–A15 (Fig. 11)

**Paper location:** printed p. 11, §III-A; Fig. 11 (the full axiom system
`EDNK_E_DNK`).

**Mathematical statement — all 16 axioms:**

(A0) `⊥;(x!N;d) ≡ ⊥` — deadlock after send is deadlock.
Wait, let me re-read the exact axioms from the paper text (the ar5iv extraction
at line 549 showed the exact formulas).  The axioms are:

```
(A0)  ⊥;p ≡ ⊥                       (deadlock sequencing)
(A1)  (N₁+N₂);d ≡ N₁;d ⊕ N₂;d         (NetKAT sum to DyNetKAT choice)  [for N₁,N₂ ∈ NetKAT⁻ᵈᵘᵖ]
(A2)  p ⊕ q ≡ q ⊕ p                  (commutativity)
(A3)  (p ⊕ q) ⊕ r ≡ p ⊕ (q ⊕ r)        (associativity)
(A4)  p ⊕ p ≡ p                      (idempotence)
(A5)  p ⊕ ⊥ ≡ p                       (neutral element)
(A6)  p ‖ q ≡ q ‖ p                  (parallel commutativity)
(A7)  p ‖ ⊥ ≡ p                      (parallel deadlock = identity)
(A8)  p ‖ q ≡ p⌊⌊q ⊕ q⌊⌊p ⊕ p|q       (parallel expansion)
(A9)  ⊥⌊⌊p ≡ ⊥                        (left-merge with deadlock)
(A10) (a;p)⌊⌊q ≡ a;(p‖q)             (left-merge prefix)
        where a ::= (σ,σ′) | x!r | x?r | rcfg(x,r)
(A11) (p⊕q)⌊⌊r ≡ (p⌊⌊r) ⊕ (q⌊⌊r)      (left-merge distributes over ⊕)
(A12) (x?N;p) | (x!N;q) ≡ rcfg_{x,N};(p‖q)   (communication pin-points)
(A13) (p⊕q)|r ≡ (p|r) ⊕ (q|r)        (comm-merge distributes over ⊕)
(A14) p|q ≡ q|p                      (comm-merge commutativity)
(A15) p|q ≡ ⊥  [owise]               (communications that don't match yield ⊥)
```

**Assumptions & side conditions:**
- A1 requires `N₁, N₂ ∈ NetKAT⁻ᵈᵘᵖ` (the lhs is `z + y` where z,y are NetKAT⁻ᵈᵘᵖ).
- A10 requires the prefix `a` to be a "complete test or assignment or
  communication action" (`at ::= α·π | x?z | x!z | rcfg_{x,z}`).
- A12 requires matching channel and NetKAT policy.
- A15 has an `[owise]` (otherwise) condition: applies only when neither
  A12 nor commutativity of | applies.

**Required Lean representation:**
```lean
inductive AxEq : DyNetKAT → DyNetKAT → Prop
  | A0  : AxEq (.seq .deadlock p) .deadlock
  | A1  : ... -- for NetKAT⁻ᵈᵘᵖ sums
  | A2  : AxEq (a.union b) (b.union a)
  -- ... through A15
```
And a derivability relation `EDNK ⊢ p ≡ q` (refl/trans/symm/subst + the axioms).

**Dependencies:** DyNetKAT syntax (extended form); NetKAT denotational semantics
(for A1's correctness proof).

**Proof obligation:**
- All axioms are sound w.r.t. bisimilarity (Lemma 10).
- AIP is sound (Lemma 11).
- E_DNK is ground-complete (Theorem 1).

**Ambiguities / open questions:**
- A15's `[owise]` is an implicit side condition on the equation.
  In a formal derivation system, this typically means A15 only applies when
  the terms do NOT match the LHS pattern of A12 (or can't be reduced to it).
**Implementation status:** Not started.

### 14. NetKAT axiomatization E_NK

**Paper location:** printed p. 11, §III-A, "including `ENKE_NK`".

**Mathematical statement:**
The paper includes the NetKAT equational theory `E_NK` as part of `E_DNK`.
The paper does NOT reproduce E_NK internally (it references [2] / [8]).
The NetKAT axioms from Anderson et al. [2] are:
- `0 + p ≡ p`  (or `p + 0 ≡ p`)
- Associativity/commutativity of `+`
- `1 · p ≡ p · 1 ≡ p`
- `(p · q) · r ≡ p · (q · r)`
- `p* · (p · q) ≡ p* · q`  (left divisibility)
- `1 + p* · p ≡ p*`
- And Kleene algebra identities.

**Assumptions & side conditions:**
- E_NK is the standard NetKAT/NetKAT* Kleene algebra with tests.

**Required Lean representation:**
A separate `NetKAT/Axioms.lean` or include E_NK axioms in `AxEq`.

**Dependencies:** NetKAT syntax; denotational semantics.

**Proof obligation:**
- E_NK is sound and complete for NetKAT semantics.
- Lemma 5: every NetKAT⁻ᵈᵘᵖ term has a normal form `Σ α·π ∈ G`.

**Ambiguities / open questions:**
- The paper cites `[2]` (Anderson et al., POPL 2014) for the full NetKAT
  axiomatization.  We must reproduce E_NK from that source, not invent it.
  **Recommendation:** implement E_NK separately with its own soundness proof,
  and verify it against the NetKAT paper's axioms.
**Implementation status:** Not started.

### 15. Normal forms

**Paper location:** printed p. 13–14, §III-A; Definition 6 (DyNetKAT n.f.);
Lemma 5 (NetKAT⁻ᵈᵘᵖ n.f.); Lemma 9 (DyNetKAT normalization).

**Mathematical statement:**

**NetKAT⁻ᵈᵘᵖ normal form (Lemma 5):**
Every NetKAT⁻ᵈᵘᵖ term `p` has an n.f. `q = Σ_{α·π ∈ G} α·π` such that
`E_NK ⊢ p ≡ q`, where `G(p)` is the language model (printed p. 13).

**DyNetKAT normal form (Definition 6):**
A DyNetKAT policy is in n.f. if it is of shape:
```
⊕_{i∈I} (α_i·π_i);d_i  ⊕  ⊕_{j∈J} c_j;d_j  (⊕ ⊥)
```
where `d_i, d_j` range over DyNetKAT policies, and
`c_j ::= x?q | x!q | rcfg(x,q)` with `q ∈ NetKAT⁻ᵈᵘᵖ`.

**DyNetKAT normalization (Lemma 9):**
`E_DNK` is normalizing for DyNetKAT: for every guarded DyNetKAT policy `p`
there exists `q` in n.f. such that `E_DNK ⊢ p ≡ q`.

**Proof sketch (printed p. 14):** By Lemma 5 and A1, structural induction.
Base cases: `⊥`, `N;d`, `c;d`. Induction: `⊕`, `⌊⌊`, `| |`, `‖`, `δ_ℒ`, `π_n`.

**Assumptions & side conditions:**
- Guardedness (Definition 7) — unguarded recursion is excluded.

**Required Lean representation:**
```lean
def isNormalForm : DyNetKAT → Bool  -- or Prop
def normalize : DyNetAT → DyNetKAT   -- if implementing as algorithm
```

**Dependencies:** Axiom soundness; Axiom A1.

**Proof obligation:**
- Every guarded term has an n.f. (Lemma 9).
- n.f. is unique up to Σ ordering (for ground-completeness).

**Ambiguities / open questions:**
- The paper says "we assume DyNetKAT policies are guarded" (printed p. 14)
  for the normalization proof.
**Implementation status:** Not started.

### 16. Guardedness (Definition 7)

**Paper location:** printed p. 13, §III-A, Definition 7.

**Mathematical statement:**
A DyNetKAT policy `p` is guarded iff all occurrences of all variables `X` in `p`
are guarded.  An occurrence of `X` in `p` is guarded if and only if:
(i) `p` has a subterm `p′;t` such that either `p′` is variable-free, or all
occurrences of variables in `p′` are guarded, and `X` occurs in `t`; or
(ii) `p` is of shape `y?X;t`, `y!X;t`, or `rcfg(X,t)`.

**Required Lean representation:**
```lean
def IsGuarded : DyNetKAT → Prop
```
Decidable if the term is finite (no infinite recursion in syntax tree).

**Dependencies:** DyNetKAT syntax.

**Proof obligation:** Guarded terms are finitely branching (Lemma 8).

**Implementation status:** Not started.

### 17. Branching finiteness (Lemma 8)

**Paper location:** printed p. 13, §III-A, Lemma 8.

**Mathematical statement:**
All guarded DyNetKAT policies are finitely branching.

**Required Lean representation:**
```lean
theorem branching_finite : IsGuarded p → (∀ c s, { s' | Step c s s' } is finite)
```
The exact statement needs care — "finitely branching" means each
configuration has finitely many successors.

**Dependencies:** Guardedness; Step relation.

**Proof obligation:** Prove finiteness of successor set.

**Implementation status:** Not started.

### 18. Bisimilarity (Definition 2)

**Paper location:** printed p. 11, §III, Definition 2.

**Mathematical statement:**
A relation R over DyNetKAT policies is a bisimulation if for (p,q) ∈ R:
if `(p, H₀, H₁) →γ (p′, H₀′, H₁′)` then there exists q′ such that
`(q, H₀, H₁) →γ (q′, H₀′, H₁′)` and `(p′, q′) ∈ R`.

Bisimilarity `p ∼ q` is the largest bisimulation.

**Required Lean representation:**
```lean
def Bisimulation (R : DyNetKAT → DyNetKAT → Prop) : Prop := ...
def Bisimilar : DyNetKAT → DyNetKAT → Prop := ...
-- Coinductive definition, or greatest fixed point.
```

Lean 4 supports `coinductive` types.  Use coinduction.

**Dependencies:** Step relation (operational semantics).

**Proof obligation:**
- Bisimilarity is the greatest fixed point / coinductive relation.
- Bisimilarity is a congruence (Lemma 3).

**Ambiguities / open questions:**
- The bisimulation is defined over policies (DyNetKAT terms), but the
  transition rules operate on configurations `(p, H₀, H₁)`.
  So R ranges over `DyNetKAT → DyNetKAT → Prop`, and the simulation condition
  quantifies over all `H₀, H₁`.  This is standard.
**Implementation status:** Not started.

### 19. Semantic layering (Proposition 1)

**Paper location:** printed p. 11, §III-A, Proposition 1.

**Mathematical statement:**
For `p, q ∈ NetKAT⁻ᵈᵘᵖ` and any DyNetKAT `d`:
`⟦p⟧ = ⟦q⟧` iff `(p;d) ∼ (q;d)`.

**Required Lean representation:**
```lean
theorem semantic_layering :
  ∀ (p q : NetKAT⁻ᵈᵘᵖ) (d : DyNetKAT),
    ⟦p⟧ = ⟦q⟧ ↔ Step.* (p;d) ∼ Step.* (q;d)
```

**Dependencies:** NetKAT denotational semantics; DyNetKAT semantics; bisimilarity.

**Proof obligation:** Prove both directions.

**Implementation status:** Not started.

### 20. Soundness & ground-completeness (Theorem 1)

**Paper location:** printed p. 11, §III-A, Theorem 1; printed p. 15 §III-A1.

**Mathematical statement:**
`E_DNK` is sound and ground-complete for DyNetKAT bisimilarity.
- **Soundness:** if `E_DNK ⊢ p ≡ q` then `p ∼ q`.
- **Ground-completeness:** if `p ∼ q` then `E_DNK ⊢ p ≡ q`.

**Proof decomposition:**
1. Soundness of E_DNK \ {AIP} (Lemma 10).
2. Soundness of AIP (Lemma 11).
3. Completeness: via normalization (Lemma 9) and matching summands
   (printed p. 16).

**Required Lean representation:**
```lean
theorem soundness : E_DNK ⊢ p ≡ q → p ∼ q
theorem ground_completeness : p ∼ q → E_DNK ⊢ p ≡ q
```

**Dependencies:** Axioms A0-A15, AIP; normalization; bisimilarity;
NetKAT completeness (for E_NK).

**Proof obligation:** Full soundness and completeness proofs.

**Ambiguities / open questions:**
- "Ground-complete" means completeness for ground (variable-free) terms.
  With recursion, ground terms include those with `recurse` but no free variables.
**Implementation status:** Not started.

---

## VI. Safety Framework

### 21. Safety property syntax (Definition 12)

**Paper location:** printed p. 17, §IV, Definition 12.

**Mathematical statement:**
Let 𝒜 be an alphabet over letters of shape `α·π` and `rcfg(x,p)`.
```
act  ::= α·π | rcfg(x,p)       (where α·π, rcfg(x,p) ∈ 𝒜)
regexp ::= act | regexp + regexp | regexp · regexp
prop ::= [regexp]false
```

**Assumptions & side conditions:**
- `prop` states that the encoded behavior (regexp) cannot be observed.
- This is a "safety = something bad never happens" formulation.

**Required Lean representation:**
```lean
inductive Action (alphabet)  -- reuse from §6, but alphabet restricted to
                              -- α·π and rcfg(x,p) only
inductive Regexp
  | act : Action → Regexp
  | plus : Regexp → Regexp → Regexp
  | seq : Regexp → Regexp → Regexp
inductive Prop
  | unsafe : Regexp → Prop   -- [regexp]false
```

**Dependencies:** NetKAT (for α·π); DyNetKAT rcfg.

**Proof obligation:** The semantic map ⟦−⟧ is well-defined (Definition 14).

**Implementation status:** Not started.

### 22. Head normal form (Definition 13)

**Paper location:** printed p. 17–18, §IV, Definition 13.

**Mathematical statement:**
`hnf(r)` = sum of words obtained by distributing `·` over `+` in `r`:
```
hnf(a) = a                              (a ∈ 𝒜)
hnf(w) = w                              (w ∈ 𝒜*)
hnf(r₁ + r₂) = hnf(r₁) + hnf(r₂)
hnf(r₁·(r₂+r₃)) = hnf(r₁·r₂) + hnf(r₁·r₃)
hnf((r₁+r₂)·r₃) = hnf(r₁·r₃) + hnf(r₂·r₃)
hnf(r′·(r₁+r₂)·r″) = hnf(r′·r₁·r″) + hnf(r′·r₂·r″)
```

**Required Lean representation:**
```lean
def hnf : Regexp → Regexp  -- or to a list of words
```

**Dependencies:** Regexp type.

**Proof obligation:** hnf(r) ≡ r (semantic equivalence).

**Implementation status:** Not started.

### 23. Safety property semantics (Definition 14)

**Paper location:** printed p. 18–19, §IV, Definition 14.

**Mathematical statement:**
Let Θ encode all possible behaviors over 𝒜:
```
Θ ≜ ⊕_{α·π ∈ 𝒜} (α·π;⊥ ⊕ α·π;Θ) ⊕ ⊕_{rcfg(x,p) ∈ 𝒜} (rcfg(x,p);⊥ ⊕ rcfg(x,p);Θ)
```

Semantic map ⟦−⟧ : Prop → DyNetKAT:
```
(c1) ⟦[Σ_{i∈I} w_i]false⟧ ≜
     ⊕_{w ∈ 𝒜*, |w|<M, ∀i: w_i ⋠ w}  w̄;⊥
   ⊕ ⊕_{w ∈ 𝒜*, |w|=M, ∀i: w_i ⋠ w}  (w̄;⊥ ⊕ w̄;Θ)

(c2) ⟦[r]false⟧ ≜ ⟦[hnf(r)]false⟧   [otherwise]
```
where M = max |w_i|, and w̄ is the DyNetKAT term obtained from w by
separating all letters with `;`:
```
ā = a
a·w̄ = a;w̄
```

**Required Lean representation:**
- `Θ` as a DyNetKAT term (recursive).
- `w̄ : Word → DyNetKAT`.
- `⟦prop⟧ : Prop → DyNetKAT`.

**Dependencies:** DyNetKAT syntax (⊕, ;, ⊥, α·π, rcfg); Regexp semantics;
DyNetKAT normal forms.

**Proof obligation:** ⟦−⟧ is well-defined; Θ is well-defined (guarded recursion).

**Ambiguities / open questions:**
- Θ is defined via guarded recursion (`rcfg(x,p);Θ`).  Must ensure guardedness.
**Implementation status:** Not started.

### 24. Trace-equivalence axiomatization E^tr_DNK (Definition 15)

**Paper location:** printed p. 19, §IV, Definition 15.

**Mathematical statement:**
`E^tr_DNK` = the equational axioms in Fig. 11 (A0–A15, AIP) plus:
```
(A16)  p;(q ⊕ r) ≡ p;q ⊕ p;r    (left distributivity of ; over ⊕)
```

**Required Lean representation:**
Extend `AxEq` with A16, or define a separate trace-equivalence relation.

**Dependencies:** Axioms A0–A15, AIP.

**Proof obligation:** None beyond adding the axiom.

**Implementation status:** Not started.

### 25. Safe network systems (Definition 16)

**Paper location:** printed p. 19, §IV, Definition 16.

**Mathematical statement:**
Given safety spec `s` and network implementation `i`:
```
Network is safe  iff  E^tr_DNK ⊢ ⟦s⟧ ⊕ i ≡ ⟦s⟧
```
i.e., the trace behavior of `i` is included in that of `⟦s⟧`.

**Required Lean representation:**
```lean
def IsSafe (s : Prop) (i : DyNetKAT) : Prop :=
  E^tr_DNK ⊢ ⟦s⟧ ⊕ i ≡ ⟦s⟧
```

**Dependencies:** Safety semantics; trace-equivalence derivability.

**Proof obligation:** Soundness of safety checking.

**Implementation status:** Not started.

### 26. Extended safety sugars (Definition 17)

**Paper location:** printed p. 20, §IV-A, Definition 17.

**Mathematical statement:**
Extended actions: `act_e ::= α·π | rcfg(x,p) | ¬act_e`
Extended regexps: `regexp_e ::= true | act_e | regexp_e + regexp_e
                        | regexp_e · regexp_e | (regexp_e)^n  (n ≥ 1)`
Extended prop: `prop_e ::= [regexp_e]false`

Desugaring `ds : Regexp_e → Regexp`:
- `ds(true) = Σ_{a∈𝒜} a`
- `ds(¬(α·π)) = Σ_{α_i·π_i ∈ 𝒜, α_i≠α or π_i≠π} α_i·π_i`
- `ds(¬rcfg(x,p)) = Σ_{rcfg(y,q) ∈ 𝒜, rcfg(y,q)≠rcfg(x,p)} rcfg(y,q)`
- `ds(r^n) = ds(r · r · ... · r)` (n times)
- etc.

Semantic map: `⟦[r_e]false⟧ = ⟦[ds(r_e)]false⟧`.

**Required Lean representation:**
```lean
inductive RegexpExt
  | true
  | act
  | negAct
  | plus
  | seq
  | starN
def ds : RegexpExt → Regexp
```

**Dependencies:** All prior safety sections.

**Proof obligation:** `ds` preserves semantics: `ds(r_e) ≡ r_e` semantically.

**Implementation status:** Not started.

---

## VII. Examples and Theorems

### 27. Stateful firewall example (Fig. 1)

**Paper location:** printed p. 3 (Fig. 1), p. 5 (encoding, Fig. 5).

**Mathematical statement:**
The firewall initially drops packets at `ext`, until a secure connection
request triggers a reconfiguration.  Encoded as a DyNetKAT policy with
initial state, a `syn` trigger, and `rcfg` reconfiguration.

**Required Lean representation:** Concrete DyNetKAT terms encoding the example.

**Dependencies:** DyNetKAT syntax; NetKAT policies.

**Proof obligation:** Verify the safety property: packets at `port=ext` cannot
reach `port=int` before reconfiguration.

**Implementation status:** Not started.

### 28. Distributed controller example (Fig. 2)

**Paper location:** printed p. 4 (Fig. 2), p. 5 (encoding, Fig. 6).

**Mathematical statement:**
Two controllers `C1`, `C2` independently updating switches.  Interleaved
updates can cause cross-destination breaches.  Synchronization protocol
prevents this.

**Required Lean representation:** DyNetKAT terms for `C1`, `C2`, `SDN`.

**Dependencies:** All above.

**Proof obligation:** Verify safety with and without synchronization.

**Implementation status:** Not started.

### 29. Per-packet consistency (design property)

**Paper location:** printed p. 8–9, §I-B / §II-B.

**Mathematical statement:**
The semantics is designed so that each data-plane packet sees exactly one set
of flow tables throughout its flight.  This is the key design invariant.

**Paper evidence (existing RESEARCH_NOTES.md):**
> "The paper's design rationale explicitly says guarded recursion models new
> flow-table states; Figure 8 advances the process after synchronized
> rcfg(channel, policy). It does not put a mutable table mapping in (d,H,H')."

**Required Lean representation:** A theorem stating that the operational
semantics preserves the invariant that a single `d` (process term, encoding
the table state) governs each packet's processing.

**Dependencies:** Operational semantics; DyNetKAT syntax.

**Proof obligation:** Formalize and prove (or state as a design invariant).

**Ambiguities / open questions:**
- Per-packet consistency is stated as a design motivation, not a formal
  theorem with a proof. It emerges from the semantics structure.

**Implementation status:** Not started.

### 30. Restriction & projection equations (semantic)

**Paper location:** printed p. 12, §III; Eq. (2), (3).

**Mathematical statement:**
The restriction `δ_ℒ(−)` and projection `π_n(−)` are "defined in the standard
fashion, on top of DyNetKAT normal forms" (printed p. 12).  In process algebra
[Baeten & Weijland, ref 3], these are standard operators.

The projection equations are explicitly:
```
π_0(p) ≡ ⊥
π_n(⊥) ≡ ⊥
π_{n+1}(at;p) ≡ at;π_n(p)
π_n(p⊕q) ≡ π_n(p) ⊕ π_n(q)
```
The restriction equations are "standard" but not enumerated; the δ-rule is
Eq. (2) in §III.

**Required Lean representation:** Operators δ, π_n and their Step-lifting rules.

**Dependencies:** Restriction/projection operators; normal forms.

**Proof obligation:** δ and π axioms are sound (part of E_DNK, though the
paper says they're "defined in the standard fashion").

**Implementation status:** Not started.

### 31. Completeness of E_NK (external)

**Paper location:** printed p. 13, §III-A, proof of Lemma 5; references [2]
(Anderson et al., POPL 2014).

**Mathematical statement:**
E_NK is complete for NetKAT semantics: `⟦p⟧ = ⟦q⟧` iff `E_NK ⊢ p ≡ q`.
This is the standard NetKAT completeness result from [2].

**Required Lean representation:** The DyNetKAT completeness proof relies on
this through Lemma 5.

**Proof obligation:**
- Either cite/assume the NetKAT completeness from [2], or implement it.
**Recommendation:** Implement a minimal NetKAT completeness proof for the
dup-free fragment, as it is required for Lemma 5 and ground-completeness.

**Implementation status:** Not started.


