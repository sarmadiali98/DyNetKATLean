------------------------------------------------------------------------
-- History-based NetKAT denotational semantics (paper Figure 3, p. 5)
--
-- Per the DyNetKAT paper (arXiv:2102.10035v4), Figure 3 (p. 5) evaluates
-- NetKAT policies over packet histories via the semantic map
--   ⟦-⟧ : N → (H → P(H)):
--
--   ⟦1⟧(h) = {h}          ⟦0⟧(h) = {}
--   ⟦f=n⟧(σ::h) = {σ::h} if σ(f)=n, {} otherwise
--   ⟦¬a⟧(h) = {h} \ ⟦a⟧(h)
--   ⟦f←n⟧(σ::h) = {σ[f:=n]::h}
--   ⟦p+q⟧(h) = ⟦p⟧(h) ∪ ⟦q⟧(h)
--   ⟦p·q⟧(h) = (⟦p⟧ • ⟦q⟧)(h)                     (relational composition)
--   ⟦p*⟧(h) = ⋃_{i∈ℕ} Fⁱ(h), F⁰(h)={h}, Fⁱ⁺¹(h)=(⟦p⟧•Fⁱ)(h)
--   (f • g)(x) = ⋃ {g(y) | y ∈ f(x)}
--   ⟦dup⟧(σ::h) = {σ::(σ::h)}
--
-- This module defines the corresponding relation
--   HistorySemantics : NetKAT → History → History → Prop
-- (`HistorySemantics N h h'` reads: `h' ∈ ⟦N⟧(h)`) over the canonical
-- nonempty `History` type of `NetKAT/History.lean` (H1A).
--
-- The relation is an INDEPENDENT specification: it is defined directly
-- from the paper's Figure 3 clauses and is not a wrapper of the
-- packet-level `Semantics` of `NetKAT/Semantics.lean` — that module was
-- deliberately NOT imported at H1B time.  For the H3A correspondence
-- (packet/history equivalence on the star-free fragment) the packet-level
-- module IS imported below; the relation itself remains an independent
-- specification, and the equivalence is proved, not assumed.
--
-- The AST (`NetKAT/AST.lean`) is the dup-free fragment NetKAT⁻ᵈᵘᵖ
-- (Eq. 1, p. 6), so there is no `dup` clause; `dup` is out of scope for
-- DyNetKAT and must not be introduced.
--
-- Scope boundary (H1B): the basic clauses are checked below.  The
-- equivalence with the packet-level `Semantics` is NOT proved here, and
-- the evaluator is NOT proved correct against this relation.
------------------------------------------------------------------------

import Mathlib.Logic.Relation
import DyNetKAT.NetKAT.Packet
import DyNetKAT.NetKAT.AST
import DyNetKAT.NetKAT.History
import DyNetKAT.NetKAT.Semantics

namespace DyNetKAT.NetKAT

open Relation

/-! ## Predicate satisfaction on histories (Figure 3, test clauses) -/

/-- History-level satisfaction of a NetKAT predicate (Figure 3, p. 5).

    A predicate inspects only the current packet `h.head` of the history
    and never modifies the history: the paper's test clauses yield either
    `{h}` (the predicate holds) or `{}` (it does not).  Clause-by-clause:

    - `pFalse`      : never holds                          (`⟦0⟧(h) = {}`)
    - `pTrue`       : always holds                         (`⟦1⟧(h) = {h}`)
    - `pFieldEq fe` : holds iff `h.head fe.field = fe.value`
                                            (`⟦f=n⟧(σ::h) = {σ::h} if σ(f)=n`)
    - `pAnd p q`    : conjunction of satisfactions         (`Pr · Pr`)
    - `pOr p q`     : disjunction of satisfactions         (`Pr + Pr`)
    - `pNot p`      : satisfaction of `p` fails            (`⟦¬a⟧(h) = {h} \ ⟦a⟧(h)`)

    This is defined independently of the packet-level relational
    `Semantics`; it coincides with the existing packet evaluator
    `Predicate.eval` applied to the head packet
    (`satHistory_iff_eval` below). -/
def satHistory : Predicate → History → Prop
  | .pFalse,      _ => False
  | .pTrue,       _ => True
  | .pFieldEq fe, h => h.head fe.field = fe.value
  | .pAnd p q,    h => satHistory p h ∧ satHistory q h
  | .pOr p q,     h => satHistory p h ∨ satHistory q h
  | .pNot p,      h => ¬ satHistory p h

/-- History-level predicate satisfaction coincides with the existing
    packet-level `Predicate.eval` applied to the current packet. -/
theorem satHistory_iff_eval (Pr : Predicate) (h : History) :
    satHistory Pr h ↔ Predicate.eval Pr h.head = true := by
  induction Pr with
  | pFalse => simp [satHistory, Predicate.eval]
  | pTrue => simp [satHistory, Predicate.eval]
  | pFieldEq fe => simp [satHistory, Predicate.eval]
  | pAnd p q ihp ihq => simp [satHistory, Predicate.eval, ihp, ihq]
  | pOr p q ihp ihq => simp [satHistory, Predicate.eval, ihp, ihq]
  | pNot p ihp => simp [satHistory, Predicate.eval, ihp]

/-! ## The history semantics relation -/

/-- History-based NetKAT denotational semantics (paper Figure 3, p. 5),
    as a relation `HistorySemantics N h h'` — "policy `N` maps the input
    history `h` to the output history `h'`", i.e. `h' ∈ ⟦N⟧(h)`.

    Clauses for the eight constructors of the dup-free NetKAT AST:

    | constructor      | clause                                                  | paper                          |
    |-------------------|---------------------------------------------------------|--------------------------------|
    | `.drop`           | `False`                                                 | `⟦0⟧(h) = {}`                  |
    | `.id`             | `h = h'`                                                | `⟦1⟧(h) = {h}`                 |
    | `.test Pr`        | `h = h' ∧ satHistory Pr h`                              | test clauses of Figure 3       |
    | `.completeTest α` | `h = h' ∧ holdsComplete α h.head`                       | Def. 4 (p. 8), complete tests  |
    | `.assign1 f v`    | `h' = ⟨Packet.update h.head f v, h.tail⟩`               | `⟦f←n⟧(σ::h) = {σ[f:=n]::h}`   |
    | `.union p q`      | `HistorySemantics p h h' ∨ HistorySemantics q h h'`     | `⟦p+q⟧(h) = ⟦p⟧(h) ∪ ⟦q⟧(h)`    |
    | `.seq p q`        | `∃ k, HistorySemantics p h k ∧ HistorySemantics q k h'` | `⟦p·q⟧(h) = (⟦p⟧ • ⟦q⟧)(h)`     |
    | `.star p`         | `ReflTransGen (HistorySemantics p) h h'`                | `⟦p*⟧(h) = ⋃_{i∈ℕ} Fⁱ(h)`      |

    Kleene star uses Mathlib's `Relation.ReflTransGen` — the reflexive-
    transitive closure of the one-step history relation — which is exactly
    the paper's `⋃_{i∈ℕ} Fⁱ(h)`.  It is deliberately NOT the packet-level
    `StarClosure` of `NetKAT/Semantics.lean`. -/
def HistorySemantics (N : NetKAT) : History → History → Prop
  | h, h' =>
    match N with
    | .drop => False
    | .id => h = h'
    | .test Pr => h = h' ∧ satHistory Pr h
    | .completeTest α => h = h' ∧ holdsComplete α h.head
    | .assign1 f v => h' = ⟨Packet.update h.head f v, h.tail⟩
    | .union p q => HistorySemantics p h h' ∨ HistorySemantics q h h'
    | .seq p q => ∃ k, HistorySemantics p h k ∧ HistorySemantics q k h'
    | .star p => ReflTransGen (HistorySemantics p) h h'

/-! ## Basic semantic equations -/

/-- **Drop produces no history** — `⟦0⟧(h) = {}`. -/
theorem historySem_drop (h h' : History) :
    ¬ HistorySemantics .drop h h' := fun hc => hc

/-- **Identity preserves the entire history** — `⟦1⟧(h) = {h}`. -/
theorem historySem_id (h h' : History) :
    HistorySemantics .id h h' ↔ h = h' := by rfl

/-- Identity maps every history to itself. -/
theorem historySem_id_self (h : History) : HistorySemantics .id h h := rfl

/-- **Test clause** — a test preserves the history exactly when its
    predicate holds on the current packet. -/
theorem historySem_test (Pr : Predicate) (h h' : History) :
    HistorySemantics (.test Pr) h h' ↔ (h = h' ∧ satHistory Pr h) := by rfl

/-- **A true test preserves the entire history.** -/
theorem historySem_test_true (Pr : Predicate) (h : History)
    (hsat : satHistory Pr h) : HistorySemantics (.test Pr) h h :=
  ⟨rfl, hsat⟩

/-- **A false test produces no history.** -/
theorem historySem_test_false (Pr : Predicate) (h h' : History)
    (hsat : ¬ satHistory Pr h) : ¬ HistorySemantics (.test Pr) h h' :=
  fun hc => hsat ((historySem_test Pr h h').mp hc).2

/-- The predicate `0` never holds, so the test `0` produces no history. -/
theorem historySem_test_pFalse (h h' : History) :
    ¬ HistorySemantics (.test .pFalse) h h' :=
  historySem_test_false _ h h' (fun hf => hf.elim)

/-- **Complete-test clause** (Definition 4, p. 8) — the history is
    preserved exactly when its current packet matches the complete
    valuation. -/
theorem historySem_completeTest (α : CompleteTest) (h h' : History) :
    HistorySemantics (.completeTest α) h h' ↔
      (h = h' ∧ holdsComplete α h.head) := by rfl

/-- A complete test preserves the history iff the head packet equals the
    valuation itself (`holdsComplete_iff_eq`). -/
theorem historySem_completeTest_iff_head (α : CompleteTest) (h h' : History) :
    HistorySemantics (.completeTest α) h h' ↔ (h = h' ∧ h.head = α) := by
  rw [historySem_completeTest]
  exact and_congr_right fun _ => holdsComplete_iff_eq α h.head

/-- **Assignment clause** — `⟦f←n⟧(σ::h) = {σ[f:=n]::h}`: the head packet
    is updated, the history tail is preserved. -/
theorem historySem_assign1 (f : FieldName) (v : FieldValueEnum) (h h' : History) :
    HistorySemantics (.assign1 f v) h h' ↔
      h' = ⟨Packet.update h.head f v, h.tail⟩ := by rfl

/-- **Assignment preserves the original tail.** -/
theorem historySem_assign1_tail (f : FieldName) (v : FieldValueEnum) (h h' : History)
    (hc : HistorySemantics (.assign1 f v) h h') :
    h'.tail = h.tail := by
  rcases (historySem_assign1 f v h h').mp hc with heq
  subst heq
  rfl

/-- **Union corresponds to logical disjunction** —
    `⟦p+q⟧(h) = ⟦p⟧(h) ∪ ⟦q⟧(h)`. -/
theorem historySem_union (p q : NetKAT) (h h' : History) :
    HistorySemantics (.union p q) h h' ↔
      (HistorySemantics p h h' ∨ HistorySemantics q h h') := by rfl

/-- **Sequence corresponds to existence of an intermediate history** —
    `⟦p·q⟧(h) = (⟦p⟧ • ⟦q⟧)(h)` (relational composition). -/
theorem historySem_seq (p q : NetKAT) (h h' : History) :
    HistorySemantics (.seq p q) h h' ↔
      ∃ k, HistorySemantics p h k ∧ HistorySemantics q k h' := by rfl

/-- **Star is the reflexive-transitive closure** —
    `⟦p*⟧(h) = ⋃_{i∈ℕ} Fⁱ(h)`. -/
theorem historySem_star (p : NetKAT) (h h' : History) :
    HistorySemantics (.star p) h h' ↔
      ReflTransGen (HistorySemantics p) h h' := by rfl

/-- **Star includes zero iterations** — `F⁰(h) = {h}`, so `h ∈ ⟦p*⟧(h)`. -/
theorem historySem_star_refl (p : NetKAT) (h : History) :
    HistorySemantics (.star p) h h := ReflTransGen.refl

/-- Star is closed under one more iteration: if `p` maps `h` to `k` and
    `p*` maps `k` to `h'`, then `p*` maps `h` to `h'`
    (`Fⁱ⁺¹(h) = (⟦p⟧ • Fⁱ)(h)`). -/
theorem historySem_star_step (p : NetKAT) (h k h' : History)
    (hstep : HistorySemantics p h k)
    (hrest : HistorySemantics (.star p) k h') :
    HistorySemantics (.star p) h h' :=
  ReflTransGen.trans (ReflTransGen.single hstep) hrest

/-! ## Tail preservation (H2)

Every dup-free NetKAT policy preserves the tail of every nonempty packet
history.  This is the foundational invariant for the packet/history
semantic correspondence (H3): no clause of Figure 3 except `dup` touches
the history tail, and `dup` is not in the AST (`NetKAT/AST.lean`).

The theorem is unconditional and proved by structural induction on the
NetKAT AST, covering all eight constructors. -/

/-- **Kleene-star closure preserves the tail.**

    Induction over the actual `ReflTransGen` derivation — every finite
    closure derivation is covered, not a fixed number of iterations.

    Mathlib v4.19.0 orientation (checked against
    `Mathlib/Logic/Relation.lean`): `ReflTransGen` fixes the relation `r`
    and the start point `a` as parameters, and

    ```
    | tail {b c} : ReflTransGen r a b → r b c → ReflTransGen r a c
    ```

    appends one `r`-step *at the end* of a closure derivation (`head` is
    the derived prepend constructor).  So in the `tail` case the
    induction hypothesis covers the sub-derivation ending at `b`, and the
    remaining step `r b c` is handled by the one-step hypothesis. -/
private theorem reflTransGen_tail_preserved (p : NetKAT)
    (hstep : ∀ x y : History, HistorySemantics p x y → y.tail = x.tail)
    {h h' : History} (hr : ReflTransGen (HistorySemantics p) h h') :
    h'.tail = h.tail := by
  induction hr with
  | refl => rfl
  | tail _ hst ih => exact (hstep _ _ hst).trans ih

/-- **Tail preservation for all dup-free NetKAT policies** — the central
    H2 invariant: if `HistorySemantics p h h'` then `h'` has exactly the
    tail of `h`.

    Proof by structural induction on the NetKAT AST, all eight
    constructors:

    - `.drop`           : no output history exists (`⟦0⟧(h) = {}`).
    - `.id`             : `h = h'`, so the tails coincide.
    - `.test Pr`        : `h = h'` (test clauses never modify the history).
    - `.completeTest α` : `h = h'` likewise.
    - `.assign1 f v`    : `⟦f←n⟧(σ::h) = {σ[f:=n]::h}` — the tail is
      preserved verbatim (`historySem_assign1_tail`).
    - `.union p q`      : whichever branch fires preserves the tail (IHs).
    - `.seq p q`        : the intermediate history `k` has the original
      tail by the `p`-IH, and `h'` has the tail of `k` by the `q`-IH.
    - `.star p`         : induction over the `ReflTransGen` derivation
      (`reflTransGen_tail_preserved`), using the `p`-IH for each step. -/
theorem historySemantics_preserves_tail
    (p : NetKAT) (h h' : History)
    (hs : HistorySemantics p h h') :
    h'.tail = h.tail := by
  induction p generalizing h h' with
  | drop => exact absurd hs (historySem_drop h h')
  | id =>
    have heq : h = h' := (historySem_id h h').mp hs
    subst heq
    rfl
  | test Pr =>
    have heq : h = h' := ((historySem_test Pr h h').mp hs).1
    subst heq
    rfl
  | completeTest α =>
    have heq : h = h' := ((historySem_completeTest α h h').mp hs).1
    subst heq
    rfl
  | assign1 f v => exact historySem_assign1_tail f v h h' hs
  | union p q ihp ihq =>
    rcases (historySem_union p q h h').mp hs with hs | hs
    · exact ihp h h' hs
    · exact ihq h h' hs
  | seq p q ihp ihq =>
    rcases (historySem_seq p q h h').mp hs with ⟨k, hk1, hk2⟩
    exact (ihq k h' hk2).trans (ihp h k hk1)
  | star p ih =>
    exact reflTransGen_tail_preserved p ih ((historySem_star p h h').mp hs)

/-- Specialization of tail preservation to Kleene star. -/
theorem historySemantics_star_preserves_tail (p : NetKAT) (h h' : History)
    (hs : HistorySemantics (.star p) h h') :
    h'.tail = h.tail :=
  historySemantics_preserves_tail (.star p) h h' hs

/-- **Sequential composition: every intermediate history keeps the
    original tail.**  If `HistorySemantics (.seq p q) h h'` then there is
    an intermediate `k` with `HistorySemantics p h k`,
    `HistorySemantics q k h'`, and `k.tail = h.tail` (so all three of
    `h`, `k`, `h'` share one tail). -/
theorem historySemantics_seq_intermediate_tail (p q : NetKAT) (h h' : History)
    (hs : HistorySemantics (.seq p q) h h') :
    ∃ k, HistorySemantics p h k ∧ HistorySemantics q k h' ∧ k.tail = h.tail := by
  rcases (historySem_seq p q h h').mp hs with ⟨k, hk1, hk2⟩
  exact ⟨k, hk1, hk2, historySemantics_preserves_tail p h k hk1⟩

/-! ## H3A: packet/history correspondence on the star-free fragment

The two semantics of the dup-free fragment coincide on every policy built
without Kleene star (arbitrary nesting of primitives, union and sequence):

- the history relation never changes the history tail (H2), and
- the head-packet transformation is exactly the packet-level `Semantics`.

Formally, for `HistoryStarFree p`:

    HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics p σ τ

Kleene star is deliberately excluded (handled separately in H3B). -/

/-! ### Packet-level clause characterizations missing from `Semantics.lean` -/

/-- Packet-level test clause: `⟦Pr⟧ = {(σ,σ) | Pr holds on σ}`. -/
theorem packetSem_test (Pr : Predicate) (σ τ : CtxPkt) :
    Semantics (.test Pr) σ τ ↔ (Predicate.eval Pr σ = true ∧ σ = τ) := by rfl

/-- Packet-level complete-test clause: `⟦α⟧ = {(σ,σ) | α holds on σ}`. -/
theorem packetSem_completeTest (α : CompleteTest) (σ τ : CtxPkt) :
    Semantics (.completeTest α) σ τ ↔ (holdsComplete α σ ∧ σ = τ) := by rfl

/-! ### Concrete-history equality helpers -/

/-- An equality of concrete histories decomposes into head and tail
    equalities. -/
theorem history_mk_eq {σ τ : CtxPkt} {h h' : List CtxPkt}
    (hc : (⟨σ, h⟩ : History) = ⟨τ, h'⟩) : σ = τ ∧ h = h' := by
  injection hc with eσ eh
  exact ⟨eσ, eh⟩

/-- Concrete histories with equal heads and equal tails are equal. -/
theorem eq_history_mk {σ τ : CtxPkt} {h h' : List CtxPkt}
    (eσ : σ = τ) (eh : h = h') : (⟨σ, h⟩ : History) = ⟨τ, h'⟩ := by
  rw [eσ, eh]

/-! ### The star-free fragment -/

/-- The star-free fragment of the dup-free NetKAT AST: policies built from
    primitives (`drop`, `id`, tests, complete tests, primitive assignments)
    using only union and sequential composition, with **no Kleene star at
    any nesting depth** (there is no constructor for `.star`).

    This is the fragment on which the H3A packet/history correspondence is
    proved; Kleene star is handled separately in H3B. -/
inductive HistoryStarFree : NetKAT → Prop
  | drop : HistoryStarFree .drop
  | id : HistoryStarFree .id
  | test (Pr : Predicate) : HistoryStarFree (.test Pr)
  | completeTest (α : CompleteTest) : HistoryStarFree (.completeTest α)
  | assign1 (f : FieldName) (v : FieldValueEnum) : HistoryStarFree (.assign1 f v)
  | union (p q : NetKAT) (hp : HistoryStarFree p) (hq : HistoryStarFree q) :
      HistoryStarFree (.union p q)
  | seq (p q : NetKAT) (hp : HistoryStarFree p) (hq : HistoryStarFree q) :
      HistoryStarFree (.seq p q)

/-! ### The central lifting theorem -/

/-- **Packet/history correspondence for the star-free fragment (H3A).**

    For every star-free policy `p`, the history-based semantics and the
    packet-based semantics agree: `p` maps the history `⟨σ, h⟩` to `⟨τ, h'⟩`
    exactly when (1) the output history has the *same* packet list `h' = h`
    (no `dup`, so the tail never changes) and (2) the head packet is
    transformed according to the existing packet-level `Semantics p σ τ`.

    Proof by induction on the `HistoryStarFree` derivation, all seven
    constructors:

    - `.drop`           : neither semantics produces an output.
    - `.id`             : both preserve their input.
    - `.test Pr`        : `satHistory_iff_eval` + the packet-level test clause.
    - `.completeTest α` : both clauses share the conjunct `holdsComplete α σ`
      (the head of `⟨σ, h⟩` is σ definitionally; `holdsComplete_iff_eq`
      characterizes it further as `σ = α` but is not needed here).
    - `.assign1 f v`    : both use the exact `Packet.update` operation, and
      the tails agree.
    - `.union p q`      : `historySem_union` + the IHs + the packet-level
      union clause, both directions.
    - `.seq p q`        : the essential case.  Forward: the intermediate
      history `k` has the original tail by H2
      (`historySemantics_preserves_tail`), so `k = ⟨k.head, h⟩` and both
      induction hypotheses apply with the *original* tail; the packet-level
      intermediate witness is `k.head`.  Backward: given the packet-level
      intermediate `ρ`, the intermediate history is constructed as
      `⟨ρ, h⟩` — with the original tail — and both induction hypotheses
      apply directly. -/
theorem historySemantics_iff_packetSemantics_starFree
    (p : NetKAT) (hp : HistoryStarFree p) (σ τ : CtxPkt) (h h' : List CtxPkt) :
    HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics p σ τ := by
  induction hp generalizing σ τ h h' with
  | drop =>
    exact ⟨fun hc => hc.elim, fun hc => hc.2⟩
  | id =>
    constructor
    · intro hc
      have hc' : (⟨σ, h⟩ : History) = ⟨τ, h'⟩ := hc
      obtain ⟨eσ, eh⟩ := history_mk_eq hc'
      exact ⟨eh.symm, eσ⟩
    · intro hc
      have eσ : σ = τ := hc.2
      exact eq_history_mk eσ hc.1.symm
  | test Pr =>
    constructor
    · intro hc
      have hc' : (⟨σ, h⟩ : History) = ⟨τ, h'⟩ ∧ satHistory Pr ⟨σ, h⟩ := hc
      obtain ⟨heq, hsat⟩ := hc'
      obtain ⟨eσ, eh⟩ := history_mk_eq heq
      have heval : Predicate.eval Pr σ = true :=
        (satHistory_iff_eval Pr ⟨σ, h⟩).mp hsat
      exact ⟨eh.symm, ⟨heval, eσ⟩⟩
    · intro hc
      have hs : Predicate.eval Pr σ = true ∧ σ = τ := hc.2
      exact ⟨eq_history_mk hs.2 hc.1.symm,
        (satHistory_iff_eval Pr ⟨σ, h⟩).mpr hs.1⟩
  | completeTest α =>
    constructor
    · intro hc
      have hc' : (⟨σ, h⟩ : History) = ⟨τ, h'⟩ ∧ holdsComplete α σ := hc
      obtain ⟨heq, hholds⟩ := hc'
      obtain ⟨eσ, eh⟩ := history_mk_eq heq
      exact ⟨eh.symm, ⟨hholds, eσ⟩⟩
    · intro hc
      have hs : holdsComplete α σ ∧ σ = τ := hc.2
      exact ⟨eq_history_mk hs.2 hc.1.symm, hs.1⟩
  | assign1 f v =>
    constructor
    · intro hc
      have hc' : (⟨τ, h'⟩ : History) = ⟨Packet.update σ f v, h⟩ := hc
      obtain ⟨eτ, eh⟩ := history_mk_eq hc'.symm
      exact ⟨eh.symm, eτ.symm⟩
    · intro hc
      have eτ : τ = Packet.update σ f v := hc.2
      exact eq_history_mk eτ hc.1
  | union p q _ _ ihp ihq =>
    constructor
    · intro hc
      rcases (historySem_union p q ⟨σ, h⟩ ⟨τ, h'⟩).mp hc with hc | hc
      · obtain ⟨eh, hs⟩ := (ihp _ _ _ _).mp hc
        exact ⟨eh, (union_sem p q σ τ).mpr (Or.inl hs)⟩
      · obtain ⟨eh, hs⟩ := (ihq _ _ _ _).mp hc
        exact ⟨eh, (union_sem p q σ τ).mpr (Or.inr hs)⟩
    · intro hc
      obtain ⟨eh, hs⟩ := hc
      rcases (union_sem p q σ τ).mp hs with hs | hs
      · have hp' : HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ := (ihp _ _ _ _).mpr ⟨eh, hs⟩
        exact Or.inl hp'
      · have hq' : HistorySemantics q ⟨σ, h⟩ ⟨τ, h'⟩ := (ihq _ _ _ _).mpr ⟨eh, hs⟩
        exact Or.inr hq'
  | seq p q _ _ ihp ihq =>
    constructor
    · -- Forward: the intermediate history keeps the original tail (H2).
      intro hc
      obtain ⟨k, hk1, hk2⟩ := (historySem_seq p q ⟨σ, h⟩ ⟨τ, h'⟩).mp hc
      have hktail : k.tail = h := historySemantics_preserves_tail p ⟨σ, h⟩ k hk1
      obtain ⟨ρ, t⟩ := k
      have hkt' : t = h := hktail
      rw [hkt'] at hk1 hk2
      have hsp : Semantics p σ ρ := ((ihp _ _ _ _).mp hk1).2
      obtain ⟨eh, hsq⟩ := (ihq _ _ _ _).mp hk2
      exact ⟨eh, (seq_sem p q σ τ).mpr ⟨ρ, hsp, hsq⟩⟩
    · -- Backward: lift the packet-level intermediate with the original tail.
      intro hc
      obtain ⟨eh, hs⟩ := hc
      obtain ⟨ρ, hsp, hsq⟩ := (seq_sem p q σ τ).mp hs
      have hp' : HistorySemantics p ⟨σ, h⟩ ⟨ρ, h⟩ := (ihp _ _ _ _).mpr ⟨rfl, hsp⟩
      have hq' : HistorySemantics q ⟨ρ, h⟩ ⟨τ, h'⟩ := (ihq _ _ _ _).mpr ⟨eh, hsq⟩
      exact (historySem_seq p q ⟨σ, h⟩ ⟨τ, h'⟩).mpr ⟨⟨ρ, h⟩, hp', hq'⟩

/-! ### Consequences -/

/-- **Star-free policies preserve the whole packet list of a history.**

    Extracted from the H3A correspondence: if a star-free policy maps
    `⟨σ, h⟩` to `⟨τ, h'⟩`, then the output packet list is exactly `h`
    (stronger than the H2 tail equality `h'.tail = h.tail`, which holds for
    all policies including those with Kleene star). -/
theorem historySemantics_packetSemantics_starFree_tail
    (p : NetKAT) (hp : HistoryStarFree p) (σ τ : CtxPkt) (h h' : List CtxPkt)
    (hc : HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩) :
    h' = h :=
  ((historySemantics_iff_packetSemantics_starFree p hp σ τ h h').mp hc).1

/-! ## H3B: packet/history correspondence for Kleene star

The general closure correspondence: for an arbitrary NetKAT policy `p`
(star-free or not, nested stars included), the history semantics of
`.star p` corresponds to the packet-level semantics of `.star p` exactly
when the *one-step* semantics of `p` corresponds.  The theorem is
unconditional apart from that explicitly stated one-step hypothesis: no
termination, iteration-bound, or packet-domain-finiteness assumptions,
and every finite closure derivation on either side is covered by
induction over the actual derivation.

The two closure definitions have opposite step orientations (verified
against the current sources; neither definition is modified here):

- Mathlib `ReflTransGen` (`Mathlib/Logic/Relation.lean`, v4.19.0) fixes
  the relation `r` and the *start point* `a` as parameters and appends
  steps at the END:
  `tail : ReflTransGen r a b → r b c → ReflTransGen r a c`.
- The packet-level `StarClosure` (`NetKAT/Semantics.lean`) has both
  endpoints as indices and PREPENDS steps at the FRONT:
  `step : R a b → StarClosure R b c → StarClosure R a c`.

The orientation mismatch is bridged by `starClosure_snoc` below (append
one step at the END of a `StarClosure` derivation), proved by induction
over the actual `StarClosure` derivation. -/

/-- **Appending one step at the end of a packet-level closure derivation**
(the `snoc` orientation, matching Mathlib's `ReflTransGen.tail`).

`StarClosure.step` only *prepends* a step, so closing a derivation with
a final step requires this auxiliary induction over the actual
`StarClosure` derivation.  No fixed iteration bound: every finite
derivation is covered. -/
private theorem starClosure_snoc {α : Type} {R : α → α → Prop} {a b : α}
    (hsc : StarClosure R a b) :
    ∀ c, R b c → StarClosure R a c := by
  induction hsc with
  | refl a =>
    intro c hst
    exact StarClosure.step hst (StarClosure.refl c)
  | @step x y z h₁ h₂ ih =>
    intro c hst
    exact StarClosure.step h₁ (ih c hst)

/-- **Forward direction of the star correspondence** (induction core).

Induction over the actual `ReflTransGen` derivation of the history-level
star.  Mathlib's `ReflTransGen` fixes the start point as a *parameter*,
so the start `⟨σ, h⟩` stays fixed while the endpoint is generalized; the
motive is stated with the projections `x.tail` / `x.head` so that every
case is meaningful for an arbitrary endpoint.

- `refl` (zero iterations): the endpoint is the start itself, so the
  tail equality is trivial and the packet-level closure is reflexive.
- `tail` (one more iteration appended at the end): the intermediate
  history `b` has the original tail `h` by the induction hypothesis, and
  the appended step `HistorySemantics p b c` keeps the tail by H2
  (`historySemantics_preserves_tail`), so both `b` and `c` are concrete
  pairs with tail `h`; `hstep` turns the step into a packet-level
  `Semantics p` step on the heads, and `starClosure_snoc` appends it to
  the packet-level closure of the sub-derivation (appended-at-the-end
  history steps vs. prepended `StarClosure.step`). -/
private theorem historySemantics_star_fwd
    (p : NetKAT)
    (hstep :
      ∀ (σ τ : CtxPkt) (h h' : List CtxPkt),
        HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔
          h' = h ∧ Semantics p σ τ)
    (σ : CtxPkt) (h : List CtxPkt) (x : History)
    (hr : ReflTransGen (HistorySemantics p) ⟨σ, h⟩ x) :
    x.tail = h ∧ StarClosure (Semantics p) σ x.head := by
  induction hr with
  | refl => exact ⟨rfl, StarClosure.refl σ⟩
  | @tail b c _ hst ih =>
    obtain ⟨β, t⟩ := b
    obtain ⟨γ, u⟩ := c
    have hbt : t = h := ih.1
    have hcu : u = t := historySemantics_preserves_tail p ⟨β, t⟩ ⟨γ, u⟩ hst
    subst hbt
    subst hcu
    obtain ⟨-, hsem⟩ := (hstep β γ _ _).mp hst
    exact ⟨rfl, starClosure_snoc ih.2 _ hsem⟩

/-- **Reverse direction of the star correspondence** (induction core).

Induction over the actual `StarClosure` derivation of the packet-level
star.  Both endpoints of `StarClosure` are indices, so the start packet
is generalized; the motive reconstructs every history as `⟨s, h⟩` with
the ORIGINAL tail `h` — the reconstruction is by construction (the
induction builds the histories from the packet states), so no unproven
tail assumption on intermediate histories is needed.

- `refl` (zero iterations): `ReflTransGen.refl`.
- `step` (one more step prepended at the front): the reverse implication
  of `hstep` lifts `Semantics p a b` to `HistorySemantics p ⟨a, h⟩ ⟨b, h⟩`
  with the original tail, and Mathlib's `ReflTransGen.head` PREPENDS the
  history-level step — matching the prepending orientation of
  `StarClosure.step`. -/
private theorem packetSemantics_star_fwd
    (p : NetKAT)
    (hstep :
      ∀ (σ τ : CtxPkt) (h h' : List CtxPkt),
        HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔
          h' = h ∧ Semantics p σ τ)
    (h : List CtxPkt) (σ τ : CtxPkt)
    (hsc : StarClosure (Semantics p) σ τ) :
    HistorySemantics (.star p) ⟨σ, h⟩ ⟨τ, h⟩ := by
  induction hsc with
  | refl a => exact ReflTransGen.refl
  | @step a b c hst _ ih =>
    exact ReflTransGen.head ((hstep a b h h).mpr ⟨rfl, hst⟩) ih

/-- **H3B: the general Kleene-star packet/history correspondence.**

For an arbitrary NetKAT policy `p` — star-free or not, nested stars
included — the history semantics of `.star p` corresponds to the
packet-level semantics of `.star p` precisely when the ONE-STEP
semantics of `p` corresponds:

    HistorySemantics (.star p) ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics (.star p) σ τ

given the one-step hypothesis

    ∀ σ τ h h', HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics p σ τ.

The only assumption is the explicitly stated one-step correspondence;
there are no termination, iteration-bound, or packet-domain-finiteness
assumptions.  Both directions induct over the actual closure
derivations (`ReflTransGen` for the history level, `StarClosure` for
the packet level), so every finite derivation is covered.  The output
history keeps the original packet list `h`: in the forward direction
this follows from the one-step hypothesis plus H2 tail preservation
along the derivation; in the reverse direction every intermediate
history is reconstructed with the original tail by construction. -/
theorem historySemantics_star_iff_packetSemantics
    (p : NetKAT)
    (hstep :
      ∀ (σ τ : CtxPkt) (h h' : List CtxPkt),
        HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔
          h' = h ∧ Semantics p σ τ)
    (σ τ : CtxPkt) (h h' : List CtxPkt) :
    HistorySemantics (.star p) ⟨σ, h⟩ ⟨τ, h'⟩ ↔
      h' = h ∧ Semantics (.star p) σ τ := by
  constructor
  · -- Forward: induct over the ReflTransGen derivation of the
    -- history-level star (start point fixed by the parameter).
    intro hc
    obtain ⟨htail, hsc⟩ := historySemantics_star_fwd p hstep σ h ⟨τ, h'⟩ hc
    exact ⟨htail, hsc⟩
  · -- Reverse: rewrite the output tail to the original one and induct
    -- over the StarClosure derivation of the packet-level star.
    rintro ⟨htail, hstar⟩
    subst htail
    exact packetSemantics_star_fwd p hstep _ σ τ hstar

/-- **H3B corollary: star over a star-free body.**

Instantiating the general correspondence with the H3A one-step
correspondence (`historySemantics_iff_packetSemantics_starFree`): for a
star-free body `p`, the star correspondence holds unconditionally.
This reuses H3A rather than repeating its proof; the general theorem
itself remains independent of star-freeness. -/
theorem historySemantics_star_iff_packetSemantics_starFreeBody
    (p : NetKAT) (hp : HistoryStarFree p)
    (σ τ : CtxPkt) (h h' : List CtxPkt) :
    HistorySemantics (.star p) ⟨σ, h⟩ ⟨τ, h'⟩ ↔
      h' = h ∧ Semantics (.star p) σ τ :=
  historySemantics_star_iff_packetSemantics p
    (fun σ τ h h' => historySemantics_iff_packetSemantics_starFree p hp σ τ h h')
    σ τ h h'

/-! ## H3C: full packet/history correspondence (all dup-free NetKAT policies)

The two semantics coincide on the *entire* dup-free NetKAT fragment — all
eight constructors, arbitrarily nested Kleene stars included — with no side
conditions at all: no star-freeness, no termination, no iteration bounds,
no finite-history-domain or definedness/recursive-environment assumptions.

The proof is structural induction on the NetKAT AST.  The primitive, union
and sequence cases reuse the established H3A proof structure and its helper
lemmas; the star case reuses the H3B closure correspondence
(`historySemantics_star_iff_packetSemantics`) directly — its one-step
hypothesis is exactly the structural induction hypothesis of the star
body, so no closure argument is repeated and nested stars are covered. -/

/-- **Full packet/history correspondence (H3C).**

For every dup-free NetKAT policy `p` — unconditionally, with no
star-freeness, termination, iteration-bound, finite-history-domain, or
definedness assumptions — the history-based semantics and the packet-based
semantics agree:

    HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics p σ τ

i.e. `p` maps the history `⟨σ, h⟩` to `⟨τ, h'⟩` exactly when (1) the output
packet list is *unchanged* (`h' = h`) and (2) the head packet is transformed
according to the packet-level `Semantics p σ τ`.

Proof by structural induction on `p` (`induction p generalizing σ τ h h'`),
all eight constructors:

- `.drop`           : neither semantics produces an output.
- `.id`             : both preserve their input.
- `.test Pr`        : `satHistory_iff_eval` + the packet-level test clause.
- `.completeTest α` : both clauses share the conjunct `holdsComplete α σ`
  (the head of `⟨σ, h⟩` is σ definitionally).
- `.assign1 f v`    : both use the exact `Packet.update` operation, and the
  packet lists agree.
- `.union p q`      : `historySem_union` + the two induction hypotheses +
  `union_sem`, both directions.
- `.seq p q`        : the essential case.  Forward: the intermediate history
  `k` has the original tail by H2 (`historySemantics_preserves_tail`), so
  `k = ⟨k.head, h⟩` and both induction hypotheses apply with the *original*
  tail; the packet-level intermediate witness is `k.head`.  Backward: given
  the packet-level intermediate `ρ`, the intermediate history is
  constructed as `⟨ρ, h⟩` — with the original tail — and both induction
  hypotheses apply directly.
- `.star p`         : the structural induction hypothesis has exactly the
  one-step shape required by H3B,
  `∀ σ τ h h', HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics p σ τ`,
  so the case is `historySemantics_star_iff_packetSemantics` applied to it.
  The closure correspondence is reused, not reproved; the body `p` is
  arbitrary (it may itself contain stars), so nested stars such as
  `.star (.star q)` are covered. -/
theorem historySemantics_iff_packetSemantics
    (p : NetKAT) (σ τ : CtxPkt)
    (h h' : List CtxPkt) :
    HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔
      h' = h ∧ Semantics p σ τ := by
  induction p generalizing σ τ h h' with
  | drop =>
    exact ⟨fun hc => hc.elim, fun hc => hc.2⟩
  | id =>
    constructor
    · intro hc
      have hc' : (⟨σ, h⟩ : History) = ⟨τ, h'⟩ := hc
      obtain ⟨eσ, eh⟩ := history_mk_eq hc'
      exact ⟨eh.symm, eσ⟩
    · intro hc
      have eσ : σ = τ := hc.2
      exact eq_history_mk eσ hc.1.symm
  | test Pr =>
    constructor
    · intro hc
      have hc' : (⟨σ, h⟩ : History) = ⟨τ, h'⟩ ∧ satHistory Pr ⟨σ, h⟩ := hc
      obtain ⟨heq, hsat⟩ := hc'
      obtain ⟨eσ, eh⟩ := history_mk_eq heq
      have heval : Predicate.eval Pr σ = true :=
        (satHistory_iff_eval Pr ⟨σ, h⟩).mp hsat
      exact ⟨eh.symm, ⟨heval, eσ⟩⟩
    · intro hc
      have hs : Predicate.eval Pr σ = true ∧ σ = τ := hc.2
      exact ⟨eq_history_mk hs.2 hc.1.symm,
        (satHistory_iff_eval Pr ⟨σ, h⟩).mpr hs.1⟩
  | completeTest α =>
    constructor
    · intro hc
      have hc' : (⟨σ, h⟩ : History) = ⟨τ, h'⟩ ∧ holdsComplete α σ := hc
      obtain ⟨heq, hholds⟩ := hc'
      obtain ⟨eσ, eh⟩ := history_mk_eq heq
      exact ⟨eh.symm, ⟨hholds, eσ⟩⟩
    · intro hc
      have hs : holdsComplete α σ ∧ σ = τ := hc.2
      exact ⟨eq_history_mk hs.2 hc.1.symm, hs.1⟩
  | assign1 f v =>
    constructor
    · intro hc
      have hc' : (⟨τ, h'⟩ : History) = ⟨Packet.update σ f v, h⟩ := hc
      obtain ⟨eτ, eh⟩ := history_mk_eq hc'.symm
      exact ⟨eh.symm, eτ.symm⟩
    · intro hc
      have eτ : τ = Packet.update σ f v := hc.2
      exact eq_history_mk eτ hc.1
  | union p q ihp ihq =>
    constructor
    · intro hc
      rcases (historySem_union p q ⟨σ, h⟩ ⟨τ, h'⟩).mp hc with hc | hc
      · obtain ⟨eh, hs⟩ := (ihp _ _ _ _).mp hc
        exact ⟨eh, (union_sem p q σ τ).mpr (Or.inl hs)⟩
      · obtain ⟨eh, hs⟩ := (ihq _ _ _ _).mp hc
        exact ⟨eh, (union_sem p q σ τ).mpr (Or.inr hs)⟩
    · intro hc
      obtain ⟨eh, hs⟩ := hc
      rcases (union_sem p q σ τ).mp hs with hs | hs
      · exact (historySem_union p q ⟨σ, h⟩ ⟨τ, h'⟩).mpr
          (Or.inl ((ihp _ _ _ _).mpr ⟨eh, hs⟩))
      · exact (historySem_union p q ⟨σ, h⟩ ⟨τ, h'⟩).mpr
          (Or.inr ((ihq _ _ _ _).mpr ⟨eh, hs⟩))
  | seq p q ihp ihq =>
    constructor
    · -- Forward: the intermediate history keeps the original tail (H2).
      intro hc
      obtain ⟨k, hk1, hk2⟩ := (historySem_seq p q ⟨σ, h⟩ ⟨τ, h'⟩).mp hc
      have hktail : k.tail = h := historySemantics_preserves_tail p ⟨σ, h⟩ k hk1
      obtain ⟨ρ, t⟩ := k
      have hkt' : t = h := hktail
      rw [hkt'] at hk1 hk2
      have hsp : Semantics p σ ρ := ((ihp _ _ _ _).mp hk1).2
      obtain ⟨eh, hsq⟩ := (ihq _ _ _ _).mp hk2
      exact ⟨eh, (seq_sem p q σ τ).mpr ⟨ρ, hsp, hsq⟩⟩
    · -- Backward: lift the packet-level intermediate with the original tail.
      intro hc
      obtain ⟨eh, hs⟩ := hc
      obtain ⟨ρ, hsp, hsq⟩ := (seq_sem p q σ τ).mp hs
      have hp' : HistorySemantics p ⟨σ, h⟩ ⟨ρ, h⟩ := (ihp _ _ _ _).mpr ⟨rfl, hsp⟩
      have hq' : HistorySemantics q ⟨ρ, h⟩ ⟨τ, h'⟩ := (ihq _ _ _ _).mpr ⟨eh, hsq⟩
      exact (historySem_seq p q ⟨σ, h⟩ ⟨τ, h'⟩).mpr ⟨⟨ρ, h⟩, hp', hq'⟩
  | star p ih =>
    -- The structural induction hypothesis IS the one-step hypothesis of
    -- H3B; the closure correspondence is reused verbatim.
    exact historySemantics_star_iff_packetSemantics p ih σ τ h h'

/-- **H3C corollary: the whole packet list is preserved.**

    For every dup-free NetKAT policy (Kleene stars included, no side
    conditions), a history-level derivation `HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩`
    leaves the packet list `h` unchanged: `h' = h`.  In the canonical
    nonempty representation this strengthens the H2 tail equality
    `h'.tail = h.tail` (an equality of tail lists) to an equality of the
    entire packet list: the output history is exactly `⟨τ, h⟩` — same
    packet list, transformed head. -/
theorem historySemantics_preserves_packetList
    (p : NetKAT) (σ τ : CtxPkt) (h h' : List CtxPkt)
    (hc : HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩) :
    h' = h :=
  ((historySemantics_iff_packetSemantics p σ τ h h').mp hc).1

end DyNetKAT.NetKAT
