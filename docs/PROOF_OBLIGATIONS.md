# PROOF_OBLIGATIONS.md — Proof Roadmap

This document inventories every theorem and proof obligation required for a
faithful Lean 4 formalization of the original DyNetKAT paper
(arXiv:2102.10035v4 / FoSSaCS 2022).

Items are ordered by dependency.  Not all theorems can be proved immediately;
each entry notes its prerequisites and difficulty assessment.

---

## Tier 1 — NetKAT semantic core (foundational)

### T1.1 Finite-domain assumptions

**Statement:** Given a finite set of field names and finite value domains,
the set of complete tests **A** and complete assignments **Π** are finite.

**Prerequisites:** None.

**Difficulty:** Easy (standard `Fintype` instances in Lean).

**Status:** Done (machine-checked).
- `Packet.lean:158-161` — `instance : Fintype CtxPkt` via `Pi.instFintype` (domain `FieldName` and codomain `FieldValueEnum` both finite).
- `Packet.lean:198-200` — `instance : Fintype CompleteTest` (transferred from `CtxPkt` along `CompleteTest = CtxPkt`).
- `Packet.lean:258-260` — `instance : Fintype CompleteAssignmentValuation` (transferred from `CtxPkt`).
- Cardchecked: `|CtxPkt| = 256` (4⁴). Confirmed by `NETKAT_AUDIT.md §0.4` and `HANDOFF.md` (Task 2S, 2026-10-17).

### T1.2 NetKAT denotational semantics well-defined

**Statement:** ⟦N⟧ : Packet → Set Packet is well-defined for all N.
⟦N*⟧ = ⋃ₖ ⟦N⟧ᵏ is finite (terminates) due to finite packet domain.

**Prerequisites:** T1.1, NetKAT syntax.

**Difficulty:** Medium (Kleene star finiteness requires finite-domain proof).

**Status:** Semantics defined, identities proven; star-termination theorem missing.
- `Semantics.lean:51` — `StarClosure` inductive (reflexive-transitive closure).
- `Semantics.lean:61-71` — `Semantics : NetKAT → CtxPkt → CtxPkt → Prop` (8 clauses, total match).
- `Semantics.lean:74` — `eval` (set-of-outputs form).
- Basic identities proven: `drop_empty` (82), `id_diag` (91), `union_sem` (95),
  `seq_sem` (100), `fieldTest_sem` (156), `completeTest_sem` (252),
  `assign1_sem` (263), `assign1_seq_sem` (277), `assign_list_sem` (311),
  `completeAssignExpr_sem` (635), `star_refl` (140), `star_step` (144).
- Boolean algebra and packet algebra theorems in `Semantics.lean:498-588`.
- **Missing (star-termination, T1.2-STAR):** No theorem proves that
  `StarClosure (Semantics N)` stabilizes in ≤ |CtxPkt|² iterations on the
  finite packet domain. This blocks computable star traversal and normalization
  of `N*` terms. Cited as outstanding obligation in
  `UNIFIED_ARCHITECTURE_REQUIREMENTS.md:1678` and Risk R5 (line 823).
  **Do NOT assume the star bound without a proof.**

### T1.3 Basic NetKAT semantic identities

**Statement:** Standard Kleene algebra with tests identities:
- ⟦0⟧ = ∅, ⟦1⟧ = diagonal
- ⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧
- ⟦N₁;N₂⟧ = ⟦N₁⟧ ∘ ⟦N₂⟧
- etc.

**Prerequisites:** T1.2.

**Difficulty:** Easy.

**Status:** Done (machine-checked). All identities listed in §I-B and Figure 4
are implemented and proven with no `sorry`/`admit`/`axiom`. Key theorems:
- `drop_empty` (`Semantics.lean:82`), `id_diag` (`Semantics.lean:91`),
  `union_sem` (`Semantics.lean:95`), `seq_sem` (`Semantics.lean:100`).
- Boolean algebra (Figure 4 BA axioms): `pred_excluded_middle` (498),
  `pred_contra` (507), `pred_deMorgan_or` (523), `pred_deMorgan_and` (538).
- Packet algebra (Figure 4 PA axioms): `assign_overwrite` (558),
  `assign_comm_diff` (570), `assign_test_same_field` (577),
  `test_assign_same_field` (585).
- Star properties: `star_refl` (140), `star_step` (144).
- Total: 30+ semantic identity theorems, all machine-checked.

### T1.4 NetKAT normal forms (Lemma 5)

**Statement:** Every NetKAT⁻ᵈᵘᵖ term p has a normal form q = Σ_{α·π ∈ G} α·π
such that E_NK ⊢ p ≡ q.

**Prerequisites:** T1.2, T1.3; E_NK axiomatization; NetKAT completeness.

**Difficulty:** Hard (requires reproducing E_NK from Anderson et al. [2]
and proving the language-model decomposition ⟦p⟧ = ⋃_{x∈G(p)} ⟦x⟧).

**Status:** Representation + semantic-correspondence theorems implemented;
algorithm G and E_NK derivation relation missing. Lemma 5 itself is NOT proved.

  **Implemented (semantic correspondence, not equational derivability):**

  - Normal form *representation*:
    `NormalForm.lean:60` — `abbrev NormalForm := Finset (CompleteTest × CompleteAssignmentValuation)`.
    `NormalForm.lean:80` — `ofSummand` (computable): `(α,π) ↦ .seq (.completeTest α) (completeAssignExpr π)`.
    `NormalForm.lean:114` — `interpret` (noncomputable): union fold over summands; empty → `.drop`.
    `NormalForm.lean:371` — `idNF` (computable): diagonal embedding `{ (α,α) | α }`.
    `NormalForm.lean:400` — `testNF` (noncomputable).
    `NormalForm.lean:558` — `unionNF` (noncomputable): `a ∪ b`.
    `NormalForm.lean:592` — `assign1NF` (noncomputable).
    `NormalForm.lean:755` — `seqNF` (noncomputable): relational composition on Finsets.

  - Semantic correspondence *theorems* (all machine-checked, no proof holes):
    - `interpret_sem` (`NormalForm.lean:263`): `⟦interpret(nf)⟧(σ,τ) ↔ ∃ (α,π) ∈ nf, holdsComplete α σ ∧ τ = π`.
    - `ofSummand_sem` (`NormalForm.lean:138`): single-summand semantics.
    - `fold_sem` (`NormalForm.lean:199`): list-fold semantics.
    - `emptyNF_sem` (`NormalForm.lean:337`): `⟦interpret(∅)⟧ = ⟦0⟧`.
    - `idNF_sem` (`NormalForm.lean:417`): `⟦interpret(idNF)⟧ = ⟦NetKAT.id⟧`.
    - `testNF_sem` (`NormalForm.lean:478`): `⟦interpret(testNF Pr)⟧ = ⟦.test Pr⟧`.
    - `assign1NF_sem` (`NormalForm.lean:624`): `⟦interpret(assign1NF f v)⟧ = ⟦.assign1 f v⟧`.
    - `unionNF_sem` (`NormalForm.lean:686`): `⟦interpret(unionNF a b)⟧ = ⟦.union (interpret a) (interpret b)⟧`.
    - `mem_seqNF_iff` (`NormalForm.lean:802`): membership characterization for `seqNF`.
    - `seqNF_sem` (`NormalForm.lean:883`): relational composition semantics.

  **Missing (the actual Lemma 5 proof):**

  - **Algorithm G: `NetKAT → NormalForm`** — no function computes the normal form
    of an arbitrary NetKAT term. `NormalForm.interpret` is a *semantic* interpreter
    (Prop-valued, noncomputable); it does **not** produce a normal form from input.
  - **E_NK derivation relation** — no inductive relation `E_NK ⊢ p ≡ q` exists.
    Only semantic *theorems* (proofs about `⟦−⟧`) are present. Lemma 5 requires
    *equational derivability*: `E_NK ⊢ p ≡ q`, not semantic equivalence `⟦p⟧ = ⟦q⟧`.
    These are distinct notions (semantic equivalence ⊆ equational derivability).
  - **Lemma 5 proof** — `E_NK ⊢ p ≡ interpret(G(p))` is **NOT** proved. The
    representation and semantic-correspondence theorems are supporting
    infrastructure, not the normalization theorem itself.

  **Do NOT mark Lemma 5 complete.** The semantic correspondence theorems establish
  that `interpret` is *sound* with respect to the denotational semantics, but they
  do not establish that every NetKAT term has an equational normal form under
  `E_NK` (completeness of normalization). That requires the missing `G` algorithm
  and the `E_NK` derivation relation.

  **Distinction required (per task instructions):**
  - *Semantic proofs* (what exists): theorems of the form `⟦N₁⟧ = ⟦N₂⟧` established
    by machine-checked Lean proofs about `Semantics`.
  - *E_NK derivability* (what is missing): an inductive relation modeling
    axiom applications from Figure 4 / Anderson et al. [2], i.e. `E_NK ⊢ p ≡ q`.
  - Lemma 5 states equational derivability (`E_NK ⊢ p ≡ q`), **not** semantic
    equivalence (`⟦p⟧ = ⟦q⟧`). The existing theorems prove semantic equivalence,
    which is necessary but not sufficient for Lemma 5.

---

## Tier 2 — DyNetKAT syntax & operational semantics

### T2.1 DyNetKAT syntax well-formed

**Statement:** The extended DyNetKAT type (Eq. 6) is well-defined,
including recursion via uniquely defined variables.

**Prerequisites:** T1.1 (NetKAT⁻ᵈᵘᵖ as sub-syntax).

**Difficulty:** Easy.

**Status:** Not started.

### T2.2 Operational semantics is well-defined (Fig. 8)

**Statement:** The labeled transition system `(d, H, H′) →γ (d′, H″, H‴)`
is the least relation closed under the rules in Fig. 8.

**Prerequisites:** T2.1; T1.2 (NetKAT denotation for packet-flow rule).

**Difficulty:** Medium (inductive definition, verifying well-foundedness).

**Status:** Not started.

### T2.3 Per-packet consistency

**Statement:** Each packet is processed by exactly one process term
(encoding one flow-table configuration) throughout its flight.

**Prerequisites:** T2.2.

**Difficulty:** Medium (this is a design invariant — may be provable from
the structure of the transition rules, or may need to be stated as an
assumption).

**Status:** Not started.

---

## Tier 3 — Extended operators

### T3.1 Restriction semantics (Eq. 2)

**Statement:** δ_ℒ(−) filters transitions whose labels are in ℒ.

**Prerequisites:** T2.2.

**Difficulty:** Easy.

**Status:** Not started.

### T3.2 Projection semantics (Eq. 3)

**Statement:** π_n(−) captures first n steps.

**Prerequisites:** T2.2.

**Difficulty:** Easy.

**Status:** Not started.

### T3.3 rcfg constant (Eq. 4)

**Statement:** `rcfg_{x,r};p →(rcfg(x,r)) p`.

**Prerequisites:** T2.2.

**Difficulty:** Easy.

**Status:** Not started.

### T3.4 Left-merge & communication-merge (Eq. 5)

**Statement:** The rules for ⌊⌊ and | are well-defined.

**Prerequisites:** T2.2, T3.3.

**Difficulty:** Medium.

**Status:** Not started.

---

## Tier 4 — Bisimilarity

### T4.1 Bisimulation is well-defined (Definition 2)

**Statement:** The bisimulation relation R is coinductively defined;
bisimilarity ∼ is the largest bisimulation.

**Prerequisites:** T2.2 (or T3.4 if using extended syntax).

**Difficulty:** Medium (coinductive definition in Lean).

**Status:** Not started.

### T4.2 Bisimilarity is a congruence (Lemma 3)

**Statement:** ∼ is preserved by all DyNetKAT operators.

**Prerequisites:** T4.1.

**Difficulty:** Hard (standard but tedious; relies on congruence-format
conditions from [19] in the paper's proof).

**Status:** Not started.

### T4.3 Semantic layering (Proposition 1)

**Statement:** For p, q ∈ NetKAT⁻ᵈᵘᵖ: ⟦p⟧ = ⟦q⟧ iff (p;d) ∼ (q;d).

**Prerequisites:** T1.2, T1.3, T4.1.

**Difficulty:** Medium.

**Status:** Not started.

---

## Tier 5 — Axiom soundness

### T5.1 Soundness of A0–A15 without AIP (Lemma 10)

**Statement:** If E_DNK \ {AIP} ⊢ p ≡ q then p ∼ q.

**Prerequisites:** T4.1, T4.2; operational semantics (T2.2, T3.4).

**Difficulty:** Hard (case analysis on all 15 axioms; paper provides
proof sketches in Appendix A).

**Status:** Not started.

### T5.2 Soundness of AIP (Lemma 11)

**Statement:** The Approximation Induction Principle is sound for bisimilarity.

**Prerequisites:** T5.1, branching finiteness (T5.3).

**Difficulty:** Hard (uses sequence construction S_n, finite branching,
and a diagonalization argument).

**Status:** Not started.

### T5.3 Branching finiteness (Lemma 8)

**Statement:** All guarded DyNetKAT policies are finitely branching.

**Prerequisites:** T3.5 (guardedness), T2.2.

**Difficulty:** Medium.

**Status:** Not started.

### T5.4 Soundness of restriction & projection axioms

**Statement:** δ and π axioms are sound w.r.t. bisimilarity.

**Prerequisites:** T5.1 (for non-AIP axioms).

**Difficulty:** Medium.

**Status:** Not started.

---

## Tier 6 — Normal forms & AIP

### T6.1 DyNetKAT normal forms (Definition 6)

**Statement:** Definition of n.f. for DyNetKAT: sums of
`(α·π);d_i` and `c_j;d_j` (⊕ ⊥).

**Prerequisites:** T1.4 (NetKAT n.f.).

**Difficulty:** Easy (definition).

**Status:** Not started.

### T6.2 Guardedness (Definition 7)

**Statement:** Definition of guarded DyNetKAT policies.

**Prerequisites:** T2.1.

**Difficulty:** Easy (definition).

**Status:** Not started.

### T6.3 DyNetKAT normalization (Lemma 9)

**Statement:** E_DNK is normalizing for guarded DyNetKAT.

**Prerequisites:** T1.4, T6.1, T6.2, A1 soundness.

**Difficulty:** Medium (structural induction per paper's proof sketch).

**Status:** Not started.

---

## Tier 7 — Soundness & completeness

### T7.1 Soundness of E_DNK (Theorem 1, part 1)

**Statement:** E_DNK ⊢ p ≡ q ⟹ p ∼ q.

**Prerequisites:** T5.1, T5.2.

**Difficulty:** Follows from T5.1 and T5.2.

**Status:** Not started.

### T7.2 Ground-completeness of E_DNK (Theorem 1, part 2)

**Statement:** p ∼ q ⟹ E_DNK ⊢ p ≡ q (for ground terms).

**Prerequisites:** T6.3 (normalization), T7.1 (soundness),
T1.4 (NetKAT completeness).

**Difficulty:** Hard (matching summands of n.f.s by structural induction,
per paper's proof at printed p. 15-16).

**Status:** Not started.

---

## Tier 8 — Safety framework

### T8.1 Safety property syntax & semantics (Definitions 12-14)

**Statement:** ⟦−⟧ : Prop → DyNetKAT is well-defined; Θ is well-defined
(guarded recursion).

**Prerequisites:** T3.1-T3.4, T6.1.

**Difficulty:** Medium (Θ is recursive; need guardedness + fixed point).

**Status:** Not started.

### T8.2 Head normal forms (Definition 13)

**Statement:** hnf(r) is well-defined; hnf(r) ≡ r.

**Prerequisites:** T8.1.

**Difficulty:** Easy.

**Status:** Not started.

### T8.3 Trace-equivalence axioms (Definition 15)

**Statement:** E^tr_DNK = E_DNK ∪ {A16} where A16: p;(q⊕r) ≡ p;q ⊕ p;r.

**Prerequisites:** T7.1.

**Difficulty:** Easy (just adding an axiom).

**Status:** Not started.

### T8.4 Safe network systems (Definition 16)

**Statement:** Network i is safe w.r.t. spec s iff
E^tr_DNK ⊢ ⟦s⟧ ⊕ i ≡ ⟦s⟧.

**Prerequisites:** T8.1, T8.3.

**Difficulty:** Easy (definition).

**Status:** Not started.

### T8.5 Extended sugars (Definition 17)

**Statement:** ds : Regexp_e → Regexp is well-defined; ds(r_e) ≡ r_e.

**Prerequisites:** T8.1.

**Difficulty:** Medium (desugaring correctness).

**Status:** Not started.

---

## Tier 9 — Examples (verification)

### T9.1 Stateful firewall example

**Statement:** The paper's Fig. 1 firewall encoding satisfies its safety
property (packets at `port=ext` cannot reach `port=int` before
reconfiguration).

**Prerequisites:** T7.1, T8.4.

**Difficulty:** Medium.

**Status:** Not started.

### T9.2 Distributed controller example

**Statement:** Without synchronization, cross-destination breach is possible;
with synchronization, it is prevented.

**Prerequisites:** T7.1, T8.4.

**Difficulty:** Medium.

**Status:** Not started.

---

## Top unresolved mathematical issues

1. **Lean tool support for coinduction:** Lean 4's `coinductive` types
   may have limitations.  Need to verify that coinductive bisimilarity
   can be defined and reasoned about effectively.

2. **NetKAT completeness (T1.4 / Lemma 5):** Requires reproducing the full NetKAT
   axiomatization E_NK from Anderson et al. [2] as an inductive derivability
   relation `E_NK ⊢ p ≡ q`, plus the normalization algorithm `G : NetKAT → NormalForm`.
   This is the most substantial external dependency.  Decision: implement a minimal
   dup-free NetKAT completeness proof, citing [2] for the full theory.
   **Note (per T1.4 above):** Semantic-correspondence theorems for the NormalForm
   representation are already proven (machine-checked), but Lemma 5 itself
   (`E_NK ⊢ p ≡ interpret(G(p))`) is NOT proved — the `G` algorithm and `E_NK`
   derivation relation are both missing.

3. **A15 `[owise]` side condition:** The "otherwise" condition in axiom
   A15 needs careful formal treatment.  In a derivation system, it must
   be expressed as a negative premise or a contextual restriction.

4. **Θ guardedness:** The Θ term in the safety semantics (Def 14) uses
   guarded recursion.  Must verify this is well-defined constructively.

5. **Finite-domain finiteness of star:** ⟦N*⟧ = ⋃ₖ ⟦N⟧ᵏ terminates only
   because the packet domain is finite.  The `StarClosure` inductive is defined
   (`Semantics.lean:51`) and basic properties proven (`star_refl`, `star_step`),
   but **no proof bounds the number of iterations**.  This needs an explicit
   proof in Lean.  **Do not assume a star bound without proving it.**

6. **Mathlib dependency:** The project depends on Mathlib4 (v4.19.0) per
   `lakefile.toml`.  `Fintype`, `Finset`, `Pi.instFintype`, `funext_iff`,
   and `Classical` are already used.  No new dependency changes needed.
