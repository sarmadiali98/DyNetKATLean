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

**Status:** Not started.

### T1.2 NetKAT denotational semantics well-defined

**Statement:** ⟦N⟧ : Packet → Set Packet is well-defined for all N.
⟦N*⟧ = ⋃ₖ ⟦N⟧ᵏ is finite (terminates) due to finite packet domain.

**Prerequisites:** T1.1, NetKAT syntax.

**Difficulty:** Medium (Kleene star finiteness requires finite-domain proof).

**Status:** Not started.

### T1.3 Basic NetKAT semantic identities

**Statement:** Standard Kleene algebra with tests identities:
- ⟦0⟧ = ∅, ⟦1⟧ = diagonal
- ⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧
- ⟦N₁;N₂⟧ = ⟦N₁⟧ ∘ ⟦N₂⟧
- etc.

**Prerequisites:** T1.2.

**Difficulty:** Easy.

**Status:** Not started.

### T1.4 NetKAT normal forms (Lemma 5)

**Statement:** Every NetKAT⁻ᵈᵘᵖ term p has a normal form q = Σ_{α·π ∈ G} α·π
such that E_NK ⊢ p ≡ q.

**Prerequisites:** T1.2, T1.3; E_NK axiomatization; NetKAT completeness.

**Difficulty:** Hard (requires reproducing E_NK from Anderson et al. [2]
and proving the language-model decomposition ⟦p⟧ = ⋃_{x∈G(p)} ⟦x⟧).

**Status:** Not started.

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

2. **NetKAT completeness (T1.4):** Requires reproducing the full NetKAT
   axiomatization E_NK from Anderson et al. [2].  This is the most
   substantial external dependency.  Decision: implement a minimal
   dup-free NetKAT completeness proof, citing [2] for the full theory.

3. **A15 `[owise]` side condition:** The "otherwise" condition in axiom
   A15 needs careful formal treatment.  In a derivation system, it must
   be expressed as a negative premise or a contextual restriction.

4. **Θ guardedness:** The Θ term in the safety semantics (Def 14) uses
   guarded recursion.  Must verify this is well-defined constructively.

5. **Finite-domain finiteness of star:** ⟦N*⟧ = ⋃ₖ ⟦N⟧ᵏ terminates only
   because the packet domain is finite.  This needs an explicit proof in
   Lean.

6. **Mathlib dependency:** The existing repo uses no Mathlib.  The
   formalization will need `Fintype`, finite sets, etc.  Decision:
   consider whether to depend on Mathlib (for `Fintype`, `finset`, etc.)
   or implement minimal infrastructure.
