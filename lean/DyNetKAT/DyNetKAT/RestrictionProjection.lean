------------------------------------------------------------------------
-- Restriction δ_L and projection π_n (S4B)
--
-- Paper references (DyNetKAT paper, arXiv:2102.10035v4; page numbers are
-- PDF pages, matching the repo convention "Lemma 5 printed p. 13" = PDF
-- p. 11):
--
--   Eq. (2), PDF p. 8 — restriction operational rule:
--     (p, H0, H1) --γ--> (p0, H00, H10),  γ ∉ L
--     -------------------------------------------
--     (δL(p), H0, H1) --γ--> (δL(p0), H00, H10)
--
--   Eq. (3), PDF p. 9 — projection operational rule:
--     (p, H0, H1) --γ--> (p0, H00, H10)
--     -------------------------------------------
--     (π_{n+1}(p), H0, H1) --γ--> (π_n(p0), H00, H10)
--
--   Fig. 11, PDF p. 10 — axioms on DyNetKAT normal forms
--   (at ::= α·π | x?z | x!z | rcfg_{x,z};  L = {c | c ::= x?N | x!N}):
--     (δ⊥)  δL(⊥) ≡ ⊥
--     (δ;)  δL(at ; p) ≡ at ; δL(p)      if at ∉ L
--     (δ;⊥) δL(at ; p) ≡ ⊥              if at ∈ L
--     (δ⊕)  δL(p ⊕ q) ≡ δL(p) ⊕ δL(q)
--     (Π0)  π0(p) ≡ ⊥
--     (Π⊥)  πn(⊥) ≡ ⊥
--     (Π;)  π_{n+1}(at ; p) ≡ at ; π_n(p)
--     (Π⊕)  πn(p ⊕ q) ≡ πn(p) ⊕ πn(q)
--     (AIP) p ≡ q if ∀n ∈ N: πn(p) ≡ πn(q)
--
--   Lemma 11 + Proof 6, PDF p. 13 — soundness of AIP for DyNetKAT
--   bisimilarity (requires branching finiteness, Lemma 8).  NOT reproduced
--   here: the AIP direction "∀n, πn(p) ∼ πn(q) → p ∼ q" remains a
--   mathematical obligation (see the end of this file for what IS proved).
--
--   §V, PDF p. 14 — "we assume the input D to the operators head and tail
--   do not contain terms of shape x?q and x!q. This can be ensured by
--   always applying the restriction operator δ on D."
--
-- What this module establishes:
--   1. The existing `Step.cpol_restrict` / `Step.cpol_project` rules are
--      exactly Eqs. (2) and (3); this is captured by the iff
--      characterizations `restrict_step_iff` and `project_step_iff`.
--   2. The Fig. 11 axioms δ⊥, δ;, δ;⊥, δ⊕, Π0, Π⊥, Π;, Π⊕ hold for
--      environment-dependent `Bisimilar` (the paper proves them sound for
--      bisimilarity in appendix eqs. (105)–(115), (119), (125), (129)).
--      δ; is stated for all four prefix shapes; for `N;D` the paper states
--      it for atomic `α·π`, but the same operational proof (appendix
--      (105)) covers every N ∈ NetKAT⁻ᵈᵘᵖ, so the Lean theorem is stated
--      in that generality.
--   3. Restriction does NOT eliminate `.var` and projection does NOT
--      resolve variables (H6A): both operators re-apply underneath the
--      `cpol_var` rule; `recursiveVars` is preserved by restriction.
--   4. Concrete counterexamples: a fixed projection depth does NOT
--      establish unbounded bisimilarity, and π_n is not bisimilar to
--      π_{n+1} in general.
--   5. A computable preprocessing layer `preprocess` implementing the δ
--      axioms as rewrites on the δ-axiom fragment, sound for
--      `Bisimilar`, producing `HeadSupported` output (S4A integration).
--
-- Deliberately OUT of scope (mathematical obligations, not assumptions):
--   - Lemma 9 normalization to DyNetKAT normal forms,
--   - soundness of AIP (Lemma 11): needs branching finiteness (Lemma 8),
--   - the environment-free bisimulation architecture (post-S4B task).
--
-- Why a new module instead of extending `NetKAT/NormalForm.lean`: that
-- file formalizes the NetKAT⁻ᵈᵘᵖ normal forms of Lemma 5 (policies), a
-- layer that must not depend on process syntax; δ/π are process operators
-- (Eq. 6) and belong above `DyNetKAT/DyNetKAT/Semantics.lean`.
------------------------------------------------------------------------

import Mathlib.Data.Finset.Basic
import DyNetKAT.NetKAT.Packet
import DyNetKAT.NetKAT.Decision
import DyNetKAT.DyNetKAT.Bisimulation
import DyNetKAT.DyNetKAT.Definedness
import DyNetKAT.DyNetKAT.SafetyHead

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

variable {schema : PacketSchema}

------------------------------------------------------------------------
-- §0 Preliminaries
------------------------------------------------------------------------

/-- The `allowed` side condition of the `(δ)` rule (Eq. 2): a transition
    labeled `γ` may fire under `δL` exactly when `γ ∉ L`.  Since `L` ranges
    over communication actions only (Eq. 6: `L = {c | c ::= x?N | x!N}`),
    packet labels `(σ, σ')` and reconfiguration labels `rcfg(x, z)` are
    always allowed.  This definition mirrors the `allowed` field of
    `Step.cpol_restrict` definitionally. -/
def actionAllowed (L : Set (CommunicationAction schema)) (action : Action schema) : Prop :=
  match action with
  | .packet _ _ => True
  | .recv x r => CommunicationAction.recv x r ∉ L
  | .send x r => CommunicationAction.send x r ∉ L
  | .rcfg _ _ => True

/-- Two processes that admit no transitions at all (for every pending and
    handled list) are bisimilar: the relation consisting of the root pair
    and its swap is a bisimulation vacuously. -/
theorem bisimilar_of_no_steps (env : RecEnv) (p q : DyNetKAT)
    (hp : ∀ (pending handled : List CtxPkt) (action : Action) (dest : Config),
      ¬ Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action dest)
    (hq : ∀ (pending handled : List CtxPkt) (action : Action) (dest : Config),
      ¬ Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        action dest) :
    Bisimilar env p q := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = p ∧ b = q) ∨ (a = q ∧ b = p)
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · intro a b h pending handled action p' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd step (hp pending handled action _)
    · exact absurd step (hq pending handled action _)

------------------------------------------------------------------------
-- §0.1 Step inversion lemmas
--
-- These factor out the `cases`-based inversion of the Figure 8 rules into
-- lemmas with variable configurations, so that the bisimilarity proofs
-- below never manipulate transition derivations directly.
------------------------------------------------------------------------

/-- Inversion for a step of `N ; D` (`cpol_seq_ok` is the only rule). -/
theorem nSeq_step_inv (env : RecEnv schema) (N : NetKAT schema) (p : DyNetKAT schema)
    (pending handled : List schema.Packet) (action : Action schema)
    (p' : DyNetKAT schema) (pending' handled' : List schema.Packet)
    (h : Step env
      (show Config schema from { proc := .nSeq N p, pending := pending, handled := handled })
      action
      (show Config schema from { proc := p', pending := pending', handled := handled' })) :
    ∃ σ σ' : schema.Packet,
      action = Action.packet σ σ' ∧
      p' = p ∧
      HistorySemantics N (History.singleton σ) (History.singleton σ') ∧
      ∃ pT, pending = σ :: pT ∧ pending' = pT ∧ handled' = σ' :: handled := by
  cases h with
  | cpol_seq_ok _ _ σ σ' _ H ev => exact ⟨σ, σ', rfl, rfl, ev, pending', rfl, rfl, rfl⟩

/-- Inversion for a step of `x?z ; D`. -/
theorem recv_step_inv (env : RecEnv) (x : Channel) (z : NetKAT) (p : DyNetKAT)
    (pending handled : List CtxPkt) (action : Action)
    (p' : DyNetKAT) (pending' handled' : List CtxPkt)
    (h : Step env
      (show Config from { proc := .recv x z p, pending := pending, handled := handled })
      action
      (show Config from { proc := p', pending := pending', handled := handled' })) :
    action = Action.recv x z ∧ p' = p ∧ pending' = pending ∧ handled' = handled := by
  cases h with
  | cpol_recv _ _ _ _ _ => exact ⟨rfl, rfl, rfl, rfl⟩

/-- Inversion for a step of `x!z ; D`. -/
theorem send_step_inv (env : RecEnv) (x : Channel) (z : NetKAT) (p : DyNetKAT)
    (pending handled : List CtxPkt) (action : Action)
    (p' : DyNetKAT) (pending' handled' : List CtxPkt)
    (h : Step env
      (show Config from { proc := .send x z p, pending := pending, handled := handled })
      action
      (show Config from { proc := p', pending := pending', handled := handled' })) :
    action = Action.send x z ∧ p' = p ∧ pending' = pending ∧ handled' = handled := by
  cases h with
  | cpol_send _ _ _ _ _ => exact ⟨rfl, rfl, rfl, rfl⟩

/-- Inversion for a step of `rcfg_{x,z} ; D`. -/
theorem rcfgPrefix_step_inv (env : RecEnv) (x : Channel) (z : NetKAT) (p : DyNetKAT)
    (pending handled : List CtxPkt) (action : Action)
    (p' : DyNetKAT) (pending' handled' : List CtxPkt)
    (h : Step env
      (show Config from { proc := .rcfgPrefix x z p, pending := pending, handled := handled })
      action
      (show Config from { proc := p', pending := pending', handled := handled' })) :
    action = Action.rcfg x z ∧ p' = p ∧ pending' = pending ∧ handled' = handled := by
  cases h with
  | cpol_rcfg _ _ _ _ _ => exact ⟨rfl, rfl, rfl, rfl⟩

/-- Inversion for a step of `D ⊕ Q`. -/
theorem choice_step_inv (env : RecEnv schema) (p q : DyNetKAT schema)
    (pending handled : List schema.Packet) (action : Action schema)
    (p' : DyNetKAT schema) (pending' handled' : List schema.Packet)
    (h : Step env
      (show Config schema from { proc := .choice p q, pending := pending, handled := handled })
      action
      (show Config schema from { proc := p', pending := pending', handled := handled' })) :
    (Step env
      (show Config schema from { proc := p, pending := pending, handled := handled })
      action
      (show Config schema from { proc := p', pending := pending', handled := handled' })) ∨
    (Step env
      (show Config schema from { proc := q, pending := pending, handled := handled })
      action
      (show Config schema from { proc := p', pending := pending', handled := handled' })) := by
  cases h with
  | cpol_choice_l _ _ _ _ _ _ _ _ s => exact Or.inl s
  | cpol_choice_r _ _ _ _ _ _ _ _ s => exact Or.inr s

/-- Inversion for a step of `δL(p)` (Eq. 2): the label is allowed and the
    inner process performs the corresponding step; the successor applies
    `δL` again.  Pending and handled lists are preserved by restriction. -/
theorem restrict_step_inv (env : RecEnv) (L : Set CommunicationAction) (p : DyNetKAT)
    (pending handled : List CtxPkt) (action : Action)
    (p' : DyNetKAT) (pending' handled' : List CtxPkt)
    (h : Step env
      (show Config from { proc := .restrict L p, pending := pending, handled := handled })
      action
      (show Config from { proc := p', pending := pending', handled := handled' })) :
    ∃ p'', p' = .restrict L p'' ∧ actionAllowed L action ∧
      Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p'', pending := pending', handled := handled' }) := by
  cases h with
  | cpol_restrict _ _ q _ _ _ _ _ allowed inner => exact ⟨q, rfl, allowed, inner⟩

/-- Inversion for a step of `π_{n+1}(p)` (Eq. 3): the inner process performs
    the corresponding step and the budget decreases by one. -/
theorem project_step_inv (env : RecEnv schema) (n : Nat) (p : DyNetKAT schema)
    (pending handled : List schema.Packet) (action : Action schema)
    (p' : DyNetKAT schema) (pending' handled' : List schema.Packet)
    (h : Step env
      (show Config schema from { proc := .project (n + 1) p, pending := pending, handled := handled })
      action
      (show Config schema from { proc := p', pending := pending', handled := handled' })) :
    ∃ p'', p' = .project n p'' ∧
      Step env
        (show Config schema from { proc := p, pending := pending, handled := handled })
        action
        (show Config schema from { proc := p'', pending := pending', handled := handled' }) := by
  cases h with
  | cpol_project m q q2 _ _ _ _ _ inner => exact ⟨q2, rfl, inner⟩

/-- No step is possible from `⊥`. -/
theorem deadlock_no_step (env : RecEnv)
    (pending handled : List CtxPkt) (action : Action) (dest : Config) :
    ¬ Step env
      (show Config from { proc := .deadlock, pending := pending, handled := handled })
      action dest := by
  intro hstep
  cases hstep

------------------------------------------------------------------------
-- §1 Restriction δL (Eq. 2, PDF p. 8)
------------------------------------------------------------------------

/-- Operational characterization of restriction (Eq. 2): `δL(p)` affords
    exactly the transitions of `p` whose label is allowed (`γ ∉ L`), with
    `δL` re-applied to the successor.  This is the iff form of
    `Step.cpol_restrict`, which matches Eq. (2) verbatim. -/
theorem restrict_step_iff (env : RecEnv) (L : Set CommunicationAction) (p : DyNetKAT)
    (pending handled : List CtxPkt) (action : Action) (dest : Config) :
    Step env
      (show Config from { proc := .restrict L p, pending := pending, handled := handled })
      action dest ↔
    ∃ p' pending' handled',
      dest = (show Config from
        { proc := .restrict L p', pending := pending', handled := handled' }) ∧
      actionAllowed L action ∧
      Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' }) := by
  constructor
  · intro hstep
    cases hstep with
    | cpol_restrict _ _ q action pending pending' handled handled' allowed inner =>
      exact ⟨q, pending', handled', rfl, allowed, inner⟩
  · rintro ⟨q, pending', handled', rfl, hallowed, hstep⟩
    exact Step.cpol_restrict L p q action pending pending' handled handled' hallowed hstep

/-- `δL(⊥)` admits no transitions: the inner `⊥` admits none. -/
theorem restrict_deadlock_no_step (env : RecEnv) (L : Set CommunicationAction)
    (pending handled : List CtxPkt) (action : Action) (dest : Config) :
    ¬ Step env
      (show Config from
        { proc := .restrict L .deadlock, pending := pending, handled := handled })
      action dest := by
  intro hstep
  cases hstep with
  | cpol_restrict _ _ q _ _ _ _ _ _ inner => cases inner

/-- Axiom (δ⊥), Fig. 11: `δL(⊥) ≡ ⊥`. -/
theorem restrict_deadlock_bisim (env : RecEnv) (L : Set CommunicationAction) :
    Bisimilar env (.restrict L .deadlock) .deadlock :=
  bisimilar_of_no_steps env _ _
    (fun pending handled action dest => restrict_deadlock_no_step env L pending handled action dest)
    (fun pending handled action dest hstep => by cases hstep)

/-- Axiom (δ;), Fig. 11, packet-prefix case: `δL(N ; p) ≡ N ; δL(p)`.

    The paper states (δ;) for atomic `at ::= α·π`; the operational proof
    (appendix (105)) never uses atomicity, so the theorem is stated for
    every `N ∈ NetKAT⁻ᵈᵘᵖ`.  No side condition is needed: packet labels
    are never in `L` by type (Eq. 6). -/
theorem restrict_nSeq_bisim (env : RecEnv) (L : Set CommunicationAction)
    (N : NetKAT) (p : DyNetKAT) :
    Bisimilar env (.restrict L (.nSeq N p)) (.nSeq N (.restrict L p)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .restrict L (.nSeq N p) ∧ b = .nSeq N (.restrict L p)) ∨
    (a = .nSeq N (.restrict L p) ∧ b = .restrict L (.nSeq N p)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h pending handled action p' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · obtain ⟨p'', hp', _, inner⟩ :=
        restrict_step_inv env L (.nSeq N p) pending handled action p' pending' handled' step
      subst hp'
      obtain ⟨σ, σ', hact, heq, ev, pT, hpend, hpend', hhand⟩ :=
        nSeq_step_inv env N p pending handled action p'' pending' handled' inner
      subst hpend'
      subst hpend
      subst hhand
      subst hact
      refine ⟨.restrict L p, Step.cpol_seq_ok N (.restrict L p) σ σ' pending' handled ev, ?_⟩
      rw [heq]
      exact Or.inr (Or.inr rfl)
    · obtain ⟨σ, σ', hact, heq, ev, pT, hpend, hpend', hhand⟩ :=
        nSeq_step_inv env N (.restrict L p) pending handled action p' pending' handled' step
      subst hpend'
      subst hpend
      subst hhand
      subst hact
      subst heq
      exact ⟨.restrict L p,
        Step.cpol_restrict L (.nSeq N p) p (Action.packet σ σ')
          (σ :: pending') pending' handled (σ' :: handled) trivial
          (Step.cpol_seq_ok N p σ σ' pending' handled ev),
        Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

/-- Axiom (δ;), Fig. 11, receive case: `δL(x?z ; p) ≡ x?z ; δL(p)` when
    `x?z ∉ L`. -/
theorem restrict_recv_allowed_bisim (env : RecEnv) (L : Set CommunicationAction)
    (x : Channel) (z : NetKAT) (p : DyNetKAT)
    (h : CommunicationAction.recv x z ∉ L) :
    Bisimilar env (.restrict L (.recv x z p)) (.recv x z (.restrict L p)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .restrict L (.recv x z p) ∧ b = .recv x z (.restrict L p)) ∨
    (a = .recv x z (.restrict L p) ∧ b = .restrict L (.recv x z p)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h'
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h' pending handled action p' pending' handled' step
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · cases step with
      | cpol_restrict _ _ q _ _ _ _ _ _ inner =>
        cases inner with
        | cpol_recv x' z' cont pending handled =>
          exact ⟨.restrict L p, Step.cpol_recv x z (.restrict L p) pending handled,
            Or.inr (Or.inr rfl)⟩
    · cases step with
      | cpol_recv x' z' cont pending handled =>
        exact ⟨.restrict L p,
          Step.cpol_restrict L (.recv x z p) p (Action.recv x z)
            pending pending handled handled h
            (Step.cpol_recv x z p pending handled),
          Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

/-- Axiom (δ;), Fig. 11, send case: `δL(x!z ; p) ≡ x!z ; δL(p)` when
    `x!z ∉ L`. -/
theorem restrict_send_allowed_bisim (env : RecEnv) (L : Set CommunicationAction)
    (x : Channel) (z : NetKAT) (p : DyNetKAT)
    (h : CommunicationAction.send x z ∉ L) :
    Bisimilar env (.restrict L (.send x z p)) (.send x z (.restrict L p)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .restrict L (.send x z p) ∧ b = .send x z (.restrict L p)) ∨
    (a = .send x z (.restrict L p) ∧ b = .restrict L (.send x z p)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h'
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h' pending handled action p' pending' handled' step
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · cases step with
      | cpol_restrict _ _ q _ _ _ _ _ _ inner =>
        cases inner with
        | cpol_send x' z' cont pending handled =>
          exact ⟨.restrict L p, Step.cpol_send x z (.restrict L p) pending handled,
            Or.inr (Or.inr rfl)⟩
    · cases step with
      | cpol_send x' z' cont pending handled =>
        exact ⟨.restrict L p,
          Step.cpol_restrict L (.send x z p) p (Action.send x z)
            pending pending handled handled h
            (Step.cpol_send x z p pending handled),
          Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

/-- Axiom (δ;), Fig. 11, reconfiguration case: `δL(rcfg_{x,z} ; p) ≡
    rcfg_{x,z} ; δL(p)`.  No side condition: reconfiguration labels are
    never in `L` by type (Eq. 6). -/
theorem restrict_rcfgPrefix_bisim (env : RecEnv) (L : Set CommunicationAction)
    (x : Channel) (z : NetKAT) (p : DyNetKAT) :
    Bisimilar env (.restrict L (.rcfgPrefix x z p)) (.rcfgPrefix x z (.restrict L p)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .restrict L (.rcfgPrefix x z p) ∧ b = .rcfgPrefix x z (.restrict L p)) ∨
    (a = .rcfgPrefix x z (.restrict L p) ∧ b = .restrict L (.rcfgPrefix x z p)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h'
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h' pending handled action p' pending' handled' step
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · cases step with
      | cpol_restrict _ _ q _ _ _ _ _ _ inner =>
        cases inner with
        | cpol_rcfg x' z' cont pending handled =>
          exact ⟨.restrict L p, Step.cpol_rcfg x z (.restrict L p) pending handled,
            Or.inr (Or.inr rfl)⟩
    · cases step with
      | cpol_rcfg x' z' cont pending handled =>
        exact ⟨.restrict L p,
          Step.cpol_restrict L (.rcfgPrefix x z p) p (Action.rcfg x z)
            pending pending handled handled trivial
            (Step.cpol_rcfg x z p pending handled),
          Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

/-- Axiom (δ;⊥), Fig. 11, receive case: `δL(x?z ; p) ≡ ⊥` when `x?z ∈ L`:
    the restricted prefix admits no transitions at all. -/
theorem restrict_recv_blocked_bisim (env : RecEnv) (L : Set CommunicationAction)
    (x : Channel) (z : NetKAT) (p : DyNetKAT)
    (h : CommunicationAction.recv x z ∈ L) :
    Bisimilar env (.restrict L (.recv x z p)) .deadlock := by
  apply bisimilar_of_no_steps
  · intro pending handled action dest hstep
    cases hstep with
    | cpol_restrict _ _ q _ _ _ _ _ allowed inner =>
      cases inner with
      | cpol_recv x' z' cont pending handled =>
        have hnot : CommunicationAction.recv x z ∉ L := allowed
        exact hnot h
  · intro pending handled action dest hstep
    cases hstep

/-- Axiom (δ;⊥), Fig. 11, send case: `δL(x!z ; p) ≡ ⊥` when `x!z ∈ L`. -/
theorem restrict_send_blocked_bisim (env : RecEnv) (L : Set CommunicationAction)
    (x : Channel) (z : NetKAT) (p : DyNetKAT)
    (h : CommunicationAction.send x z ∈ L) :
    Bisimilar env (.restrict L (.send x z p)) .deadlock := by
  apply bisimilar_of_no_steps
  · intro pending handled action dest hstep
    cases hstep with
    | cpol_restrict _ _ q _ _ _ _ _ allowed inner =>
      cases inner with
      | cpol_send x' z' cont pending handled =>
        have hnot : CommunicationAction.send x z ∉ L := allowed
        exact hnot h
  · intro pending handled action dest hstep
    cases hstep

/-- Axiom (δ⊕), Fig. 11: `δL(p ⊕ q) ≡ δL(p) ⊕ δL(q)`. -/
theorem restrict_choice_bisim (env : RecEnv) (L : Set CommunicationAction) (p q : DyNetKAT) :
    Bisimilar env (.restrict L (.choice p q)) (.choice (.restrict L p) (.restrict L q)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .restrict L (.choice p q) ∧ b = .choice (.restrict L p) (.restrict L q)) ∨
    (a = .choice (.restrict L p) (.restrict L q) ∧ b = .restrict L (.choice p q)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h pending handled action p' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · obtain ⟨p'', hp', hallowed, inner⟩ :=
        restrict_step_inv env L (.choice p q) pending handled action p' pending' handled' step
      subst hp'
      rcases choice_step_inv env p q pending handled action p'' pending' handled' inner with
        hL | hR
      · exact ⟨.restrict L p'',
          Step.cpol_choice_l (.restrict L p) (.restrict L q) (.restrict L p'')
            action pending pending' handled handled'
            (Step.cpol_restrict L p p'' action pending pending' handled handled'
              hallowed hL),
          Or.inr (Or.inr rfl)⟩
      · exact ⟨.restrict L p'',
          Step.cpol_choice_r (.restrict L p) (.restrict L q) (.restrict L p'')
            action pending pending' handled handled'
            (Step.cpol_restrict L q p'' action pending pending' handled handled'
              hallowed hR),
          Or.inr (Or.inr rfl)⟩
    · rcases choice_step_inv env (.restrict L p) (.restrict L q) pending handled action p'
        pending' handled' step with hL | hR
      · obtain ⟨p'', hp', hallowed, inner⟩ :=
          restrict_step_inv env L p pending handled action p' pending' handled' hL
        subst hp'
        exact ⟨.restrict L p'',
          Step.cpol_restrict L (.choice p q) p'' action pending pending' handled handled'
            hallowed (Step.cpol_choice_l p q p'' action pending pending' handled handled' inner),
          Or.inr (Or.inr rfl)⟩
      · obtain ⟨p'', hp', hallowed, inner⟩ :=
          restrict_step_inv env L q pending handled action p' pending' handled' hR
        subst hp'
        exact ⟨.restrict L p'',
          Step.cpol_restrict L (.choice p q) p'' action pending pending' handled handled'
            hallowed (Step.cpol_choice_r p q p'' action pending pending' handled handled' inner),
          Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

------------------------------------------------------------------------
-- §1.1 Restriction does not eliminate recursive variables (H6A)
------------------------------------------------------------------------

/-- Restriction preserves the set of directly occurring recursive
    variables: `δL` is not a variable-eliminating operation. -/
theorem recursiveVars_restrict (L : Set CommunicationAction) (p : DyNetKAT) :
    recursiveVars (.restrict L p) = recursiveVars p := rfl

/-- Restriction does not unfold variables: `δL(X)` still steps through the
    `(cpolX)` rule whenever the body of `X` affords an allowed transition.
    Unfolding remains the business of `RecEnv`, exactly as in H6A. -/
theorem restrict_var_step (env : RecEnv) (L : Set CommunicationAction) (name : Var)
    (body body' : DyNetKAT) (action : Action)
    (pending pending' handled handled' : List CtxPkt)
    (allowed : actionAllowed L action)
    (definition : env.lookup name = some body)
    (step : Step env
      (show Config from { proc := body, pending := pending, handled := handled })
      action
      (show Config from { proc := body', pending := pending', handled := handled' })) :
    Step env
      (show Config from
        { proc := .restrict L (.var name), pending := pending, handled := handled })
      action
      (show Config from
        { proc := .restrict L body', pending := pending', handled := handled' }) :=
  Step.cpol_restrict L (.var name) body' action pending pending' handled handled'
    allowed
    (Step.cpol_var name body body' action pending pending' handled handled' definition step)

------------------------------------------------------------------------
-- §2 Projection πn (Eq. 3, PDF p. 9)
------------------------------------------------------------------------

/-- Zero-depth projection admits no transitions: `(π)` (Eq. 3) only
    concludes transitions for `π_{n+1}`, so `π0(p)` is inert for every `p`.
    This is the operational content of axiom (Π0) and the precise sense in
    which zero-depth projection differs from unrestricted execution. -/
theorem project_zero_no_step (env : (RecEnv schema)) (p : (DyNetKAT schema))
    (pending handled : List schema.Packet) (action : (Action schema)) (dest : (Config schema)) :
    ¬ Step env
      (show (Config schema) from { proc := .project 0 p, pending := pending, handled := handled })
      action dest := by
  intro hstep
  cases hstep

/-- `πn(⊥)` admits no transitions: the inner `⊥` admits none. -/
theorem project_deadlock_no_step (env : RecEnv) (n : Nat)
    (pending handled : List CtxPkt) (action : Action) (dest : Config) :
    ¬ Step env
      (show Config from
        { proc := .project n .deadlock, pending := pending, handled := handled })
      action dest := by
  intro hstep
  cases hstep with
  | cpol_project m q q2 _ _ _ _ _ inner => cases inner

/-- Axiom (Π0), Fig. 11: `π0(p) ≡ ⊥`. -/
theorem project_zero_bisim (env : RecEnv) (p : DyNetKAT) :
    Bisimilar env (.project 0 p) .deadlock :=
  bisimilar_of_no_steps env _ _
    (fun pending handled action dest => project_zero_no_step env p pending handled action dest)
    (fun pending handled action dest hstep => by cases hstep)

/-- Axiom (Π⊥), Fig. 11: `πn(⊥) ≡ ⊥`. -/
theorem project_deadlock_bisim (env : RecEnv) (n : Nat) :
    Bisimilar env (.project n .deadlock) .deadlock :=
  bisimilar_of_no_steps env _ _
    (fun pending handled action dest => project_deadlock_no_step env n pending handled action dest)
    (fun pending handled action dest hstep => by cases hstep)

/-- Operational characterization of projection at depth `n + 1` (Eq. 3):
    `π_{n+1}(p)` affords exactly the transitions of `p`, with the budget
    decreased by one in the successor.  This is the iff form of
    `Step.cpol_project`, which matches Eq. (3) verbatim. -/
theorem project_step_succ_iff (env : RecEnv) (n : Nat) (p : DyNetKAT)
    (pending handled : List CtxPkt) (action : Action) (dest : Config) :
    Step env
      (show Config from { proc := .project (n + 1) p, pending := pending, handled := handled })
      action dest ↔
    ∃ p' pending' handled',
      dest = (show Config from
        { proc := .project n p', pending := pending', handled := handled' }) ∧
      Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' }) := by
  constructor
  · intro hstep
    cases hstep with
    | cpol_project m q q2 action pending pending' handled handled' inner =>
      exact ⟨q2, pending', handled', rfl, inner⟩
  · rintro ⟨q, pending', handled', rfl, hstep⟩
    exact Step.cpol_project n p q action pending pending' handled handled' hstep

/-- Operational characterization of projection at arbitrary depth: `πn(p)`
    affords a transition iff `n = m + 1` for some `m` and `p` affords the
    transition, in which case the successor is `πm` of the successor of
    `p`.  At `n = 0` no transition is possible (`project_zero_no_step`). -/
theorem project_step_iff (env : RecEnv) (n : Nat) (p : DyNetKAT)
    (pending handled : List CtxPkt) (action : Action) (dest : Config) :
    Step env
      (show Config from { proc := .project n p, pending := pending, handled := handled })
      action dest ↔
    ∃ m p' pending' handled',
      n = m + 1 ∧
      dest = (show Config from
        { proc := .project m p', pending := pending', handled := handled' }) ∧
      Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' }) := by
  cases n with
  | zero =>
    constructor
    · intro hstep
      exact absurd hstep (project_zero_no_step env p pending handled action dest)
    · rintro ⟨m, p', pending', handled', hzero, _, _⟩
      exact absurd hzero (Nat.succ_ne_zero m).symm
  | succ k =>
    rw [project_step_succ_iff]
    constructor
    · rintro ⟨p', pending', handled', rfl, hstep⟩
      exact ⟨k, p', pending', handled', rfl, rfl, hstep⟩
    · rintro ⟨m, p', pending', handled', heq, rfl, hstep⟩
      simp only [Nat.add_eq, Nat.succ.injEq] at heq
      subst heq
      exact ⟨p', pending', handled', rfl, hstep⟩

/-- Axiom (Π;), Fig. 11, packet-prefix case: `π_{n+1}(N ; p) ≡ N ; πn(p)`.

    As for (δ;), the paper states (Π;) for atomic `at ::= α·π`; the
    operational proof (appendix (122)) covers every `N ∈ NetKAT⁻ᵈᵘᵖ`. -/
theorem project_nSeq_bisim (env : RecEnv) (n : Nat) (N : NetKAT) (p : DyNetKAT) :
    Bisimilar env (.project (n + 1) (.nSeq N p)) (.nSeq N (.project n p)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .project (n + 1) (.nSeq N p) ∧ b = .nSeq N (.project n p)) ∨
    (a = .nSeq N (.project n p) ∧ b = .project (n + 1) (.nSeq N p)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h pending handled action p' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · obtain ⟨p'', hp', inner⟩ :=
        project_step_inv env n (.nSeq N p) pending handled action p' pending' handled' step
      subst hp'
      obtain ⟨σ, σ', hact, heq, ev, pT, hpend, hpend', hhand⟩ :=
        nSeq_step_inv env N p pending handled action p'' pending' handled' inner
      subst hpend'
      subst hpend
      subst hhand
      subst hact
      refine ⟨.project n p, Step.cpol_seq_ok N (.project n p) σ σ' pending' handled ev, ?_⟩
      rw [heq]
      exact Or.inr (Or.inr rfl)
    · obtain ⟨σ, σ', hact, heq, ev, pT, hpend, hpend', hhand⟩ :=
        nSeq_step_inv env N (.project n p) pending handled action p' pending' handled' step
      subst hpend'
      subst hpend
      subst hhand
      subst hact
      subst heq
      exact ⟨.project n p,
        Step.cpol_project n (.nSeq N p) p (Action.packet σ σ')
          (σ :: pending') pending' handled (σ' :: handled)
          (Step.cpol_seq_ok N p σ σ' pending' handled ev),
        Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

/-- Axiom (Π;), Fig. 11, receive case: `π_{n+1}(x?z ; p) ≡ x?z ; πn(p)`. -/
theorem project_recv_bisim (env : RecEnv) (n : Nat) (x : Channel) (z : NetKAT) (p : DyNetKAT) :
    Bisimilar env (.project (n + 1) (.recv x z p)) (.recv x z (.project n p)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .project (n + 1) (.recv x z p) ∧ b = .recv x z (.project n p)) ∨
    (a = .recv x z (.project n p) ∧ b = .project (n + 1) (.recv x z p)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h pending handled action p' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · cases step with
      | cpol_project m q q2 _ _ _ _ _ inner =>
        cases inner with
        | cpol_recv x' z' cont pending handled =>
          exact ⟨.project n p, Step.cpol_recv x z (.project n p) pending handled,
            Or.inr (Or.inr rfl)⟩
    · cases step with
      | cpol_recv x' z' cont pending handled =>
        exact ⟨.project n p,
          Step.cpol_project n (.recv x z p) p (Action.recv x z)
            pending pending handled handled
            (Step.cpol_recv x z p pending handled),
          Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

/-- Axiom (Π;), Fig. 11, send case: `π_{n+1}(x!z ; p) ≡ x!z ; πn(p)`. -/
theorem project_send_bisim (env : RecEnv) (n : Nat) (x : Channel) (z : NetKAT) (p : DyNetKAT) :
    Bisimilar env (.project (n + 1) (.send x z p)) (.send x z (.project n p)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .project (n + 1) (.send x z p) ∧ b = .send x z (.project n p)) ∨
    (a = .send x z (.project n p) ∧ b = .project (n + 1) (.send x z p)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h pending handled action p' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · cases step with
      | cpol_project m q q2 _ _ _ _ _ inner =>
        cases inner with
        | cpol_send x' z' cont pending handled =>
          exact ⟨.project n p, Step.cpol_send x z (.project n p) pending handled,
            Or.inr (Or.inr rfl)⟩
    · cases step with
      | cpol_send x' z' cont pending handled =>
        exact ⟨.project n p,
          Step.cpol_project n (.send x z p) p (Action.send x z)
            pending pending handled handled
            (Step.cpol_send x z p pending handled),
          Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

/-- Axiom (Π;), Fig. 11, reconfiguration case:
    `π_{n+1}(rcfg_{x,z} ; p) ≡ rcfg_{x,z} ; πn(p)`. -/
theorem project_rcfgPrefix_bisim (env : RecEnv) (n : Nat) (x : Channel) (z : NetKAT)
    (p : DyNetKAT) :
    Bisimilar env (.project (n + 1) (.rcfgPrefix x z p))
      (.rcfgPrefix x z (.project n p)) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    (a = .project (n + 1) (.rcfgPrefix x z p) ∧ b = .rcfgPrefix x z (.project n p)) ∨
    (a = .rcfgPrefix x z (.project n p) ∧ b = .project (n + 1) (.rcfgPrefix x z p)) ∨
    a = b
  refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr rfl)
  · intro a b h pending handled action p' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · cases step with
      | cpol_project m q q2 _ _ _ _ _ inner =>
        cases inner with
        | cpol_rcfg x' z' cont pending handled =>
          exact ⟨.project n p, Step.cpol_rcfg x z (.project n p) pending handled,
            Or.inr (Or.inr rfl)⟩
    · cases step with
      | cpol_rcfg x' z' cont pending handled =>
        exact ⟨.project n p,
          Step.cpol_project n (.rcfgPrefix x z p) p (Action.rcfg x z)
            pending pending handled handled
            (Step.cpol_rcfg x z p pending handled),
          Or.inr (Or.inr rfl)⟩
    · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

/-- Axiom (Π⊕), Fig. 11: `πn(p ⊕ q) ≡ πn(p) ⊕ πn(q)`.

    At `n = 0` both sides are inert (appendix (126): "if n = 0, then both
    of the terms do not afford any transition"); at `n = m + 1` the budget
    of the inner projection steps decreases uniformly on both sides. -/
theorem project_choice_bisim (env : RecEnv) (n : Nat) (p q : DyNetKAT) :
    Bisimilar env (.project n (.choice p q)) (.choice (.project n p) (.project n q)) := by
  cases n with
  | zero =>
    apply bisimilar_of_no_steps
    · intro pending handled action dest hstep
      cases hstep
    · intro pending handled action dest hstep
      cases hstep with
      | cpol_choice_l _ _ r action pending pending' handled handled' rstep =>
        cases rstep
      | cpol_choice_r _ _ r action pending pending' handled handled' rstep =>
        cases rstep
  | succ n =>
    let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
      (a = .project (n + 1) (.choice p q) ∧
        b = .choice (.project (n + 1) p) (.project (n + 1) q)) ∨
      (a = .choice (.project (n + 1) p) (.project (n + 1) q) ∧
        b = .project (n + 1) (.choice p q)) ∨
      a = b
    refine ⟨R, ?_, Or.inl ⟨rfl, rfl⟩⟩
    constructor
    · intro a b h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr rfl)
    · intro a b h pending handled action p' pending' handled' step
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
      · obtain ⟨p'', hp', inner⟩ :=
          project_step_inv env n (.choice p q) pending handled action p' pending' handled' step
        subst hp'
        rcases choice_step_inv env p q pending handled action p'' pending' handled' inner with
          hL | hR
        · exact ⟨.project n p'',
            Step.cpol_choice_l (.project (n + 1) p) (.project (n + 1) q) (.project n p'')
              action pending pending' handled handled'
              (Step.cpol_project n p p'' action pending pending' handled handled' hL),
            Or.inr (Or.inr rfl)⟩
        · exact ⟨.project n p'',
            Step.cpol_choice_r (.project (n + 1) p) (.project (n + 1) q) (.project n p'')
              action pending pending' handled handled'
              (Step.cpol_project n q p'' action pending pending' handled handled' hR),
            Or.inr (Or.inr rfl)⟩
      · rcases choice_step_inv env (.project (n + 1) p) (.project (n + 1) q) pending handled
          action p' pending' handled' step with hL | hR
        · obtain ⟨p'', hp', inner⟩ :=
            project_step_inv env n p pending handled action p' pending' handled' hL
          subst hp'
          exact ⟨.project n p'',
            Step.cpol_project n (.choice p q) p'' action pending pending' handled handled'
              (Step.cpol_choice_l p q p'' action pending pending' handled handled' inner),
            Or.inr (Or.inr rfl)⟩
        · obtain ⟨p'', hp', inner⟩ :=
            project_step_inv env n q pending handled action p' pending' handled' hR
          subst hp'
          exact ⟨.project n p'',
            Step.cpol_project n (.choice p q) p'' action pending pending' handled handled'
              (Step.cpol_choice_r p q p'' action pending pending' handled handled' inner),
            Or.inr (Or.inr rfl)⟩
      · exact ⟨p', step, Or.inr (Or.inr rfl)⟩

------------------------------------------------------------------------
-- §2.1 Budget monotonicity and variables (H6A)
------------------------------------------------------------------------

/-- One-step budget monotonicity: every transition of `πn(p)` is matched
    by a transition of `π_{n+1}(p)` (with the budget shifted up by one).
    This is a one-step simulation only — it is NOT a bisimulation, see
    `not_bisimilar_project_depths` below. -/
theorem project_step_monotone (env : RecEnv) (n : Nat) (p : DyNetKAT)
    (pending handled : List CtxPkt) (action : Action) (dest : Config)
    (h : Step env
      (show Config from { proc := .project n p, pending := pending, handled := handled })
      action dest) :
    ∃ dest', Step env
      (show Config from
        { proc := .project (n + 1) p, pending := pending, handled := handled })
      action dest' := by
  obtain ⟨m, p', pending', handled', hn, _, hstep⟩ :=
    (project_step_iff env n p pending handled action dest).mp h
  subst hn
  exact ⟨(show Config from
    { proc := .project (m + 1) p', pending := pending', handled := handled' }),
    Step.cpol_project (m + 1) p p' action pending pending' handled handled' hstep⟩

/-- Bounded projection does not resolve variables: `π_{n+1}(X)` still steps
    through the `(cpolX)` rule whenever the body of `X` affords a
    transition.  Projection bounds the number of observed steps; it is not
    recursive resolution (H6A). -/
theorem project_var_step (env : RecEnv) (n : Nat) (name : Var)
    (body body' : DyNetKAT) (action : Action)
    (pending pending' handled handled' : List CtxPkt)
    (definition : env.lookup name = some body)
    (step : Step env
      (show Config from { proc := body, pending := pending, handled := handled })
      action
      (show Config from { proc := body', pending := pending', handled := handled' })) :
    Step env
      (show Config from
        { proc := .project (n + 1) (.var name), pending := pending, handled := handled })
      action
      (show Config from
        { proc := .project n body', pending := pending', handled := handled' }) :=
  Step.cpol_project n (.var name) body' action pending pending' handled handled'
    (Step.cpol_var name body body' action pending pending' handled handled' definition step)

/-- Bisimilarity is preserved by every projection depth: if `p ∼ q` then
    `πn(p) ∼ πn(q)` for all `n` (by `Bisimilar.project`).  This is the
    sound direction of the premise of AIP under bisimilarity; the converse
    (AIP itself, Lemma 11) remains an obligation. -/
theorem project_bisim_all_depths (env : RecEnv) {p q : DyNetKAT}
    (h : Bisimilar env p q) (n : Nat) :
    Bisimilar env (.project n p) (.project n q) :=
  Bisimilar.project env h

------------------------------------------------------------------------
-- §3 Interaction of restriction and projection
------------------------------------------------------------------------

/-- Restriction and projection commute up to bisimilarity:
    `δL(πn(p)) ∼ πn(δL(p))`.  Proof by induction on the budget `n`, in the
    style of the paper's appendix proofs: at each step both sides perform
    exactly the allowed transitions of `p` and land in `δL(π_{n-1}(p'))`
    resp. `π_{n-1}(δL(p'))`. -/
theorem restrict_project_commute (env : RecEnv) (L : Set CommunicationAction) (p : DyNetKAT)
    (n : Nat) :
    Bisimilar env (.restrict L (.project n p)) (.project n (.restrict L p)) := by
  induction n with
  | zero =>
    apply bisimilar_of_no_steps
    · intro pending handled action dest hstep
      cases hstep with
      | cpol_restrict _ _ q _ _ _ _ _ _ inner =>
        exact project_zero_no_step env p pending handled action _ inner
    · intro pending handled action dest hstep
      cases hstep
  | succ n ih =>
    let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
      (∃ k r, k ≤ n + 1 ∧ a = .restrict L (.project k r) ∧ b = .project k (.restrict L r)) ∨
      (∃ k r, k ≤ n + 1 ∧ a = .project k (.restrict L r) ∧ b = .restrict L (.project k r))
    refine ⟨R, ?_, Or.inl ⟨n + 1, p, Nat.le_refl _, rfl, rfl⟩⟩
    constructor
    · intro a b h
      rcases h with ⟨k, r, hk, rfl, rfl⟩ | ⟨k, r, hk, rfl, rfl⟩
      · exact Or.inr ⟨k, r, hk, rfl, rfl⟩
      · exact Or.inl ⟨k, r, hk, rfl, rfl⟩
    · intro a b h pending handled action p' pending' handled' step
      rcases h with ⟨k, r, hk, rfl, rfl⟩ | ⟨k, r, hk, rfl, rfl⟩
      · cases step with
        | cpol_restrict _ _ q _ _ _ _ _ allowed inner =>
          cases inner with
          | cpol_project m q2 q3 _ _ _ _ _ rstep =>
            exact ⟨.project m (.restrict L q3),
              Step.cpol_project m (.restrict L r) (.restrict L q3)
                action pending pending' handled handled'
                (Step.cpol_restrict L r q3 action pending pending' handled handled'
                  allowed rstep),
              Or.inl ⟨m, q3, Nat.le_trans (Nat.le_succ m) hk, rfl, rfl⟩⟩
      · cases step with
        | cpol_project m q q2 _ _ _ _ _ inner =>
          cases inner with
          | cpol_restrict _ _ q3 _ _ _ _ _ allowed rstep =>
            exact ⟨.restrict L (.project m q3),
              Step.cpol_restrict L (.project (m + 1) r) (.project m q3)
                action pending pending' handled handled'
                allowed
                (Step.cpol_project m r q3 action pending pending' handled handled' rstep),
              Or.inr ⟨m, q3, Nat.le_trans (Nat.le_succ m) hk, rfl, rfl⟩⟩

------------------------------------------------------------------------
-- §4 Counterexamples: bounded projection ≠ unbounded equivalence
------------------------------------------------------------------------

/-- A process performing two packet-processing steps (identity policy). -/
def twoStepProcess : DyNetKAT := .nSeq NetKAT.id (.nSeq NetKAT.id .deadlock)

/-- A process performing one packet-processing step (identity policy). -/
def oneStepProcess : DyNetKAT := .nSeq NetKAT.id .deadlock

/-- At depth 1 the two-step and one-step processes are bisimilar: both
    perform exactly one packet step and then become inert.  Together with
    `not_bisimilar_cutoff` this proves that agreement at a fixed projection
    depth does NOT establish unbounded bisimilarity (H6A). -/
theorem bisimilar_project_cutoff (env : RecEnv) :
    Bisimilar env (.project 1 twoStepProcess) (.project 1 oneStepProcess) := by
  let R : DyNetKAT → DyNetKAT → Prop := fun a b =>
    a = b ∨
    (a = .project 1 twoStepProcess ∧ b = .project 1 oneStepProcess) ∨
    (a = .project 1 oneStepProcess ∧ b = .project 1 twoStepProcess) ∨
    (a = .project 0 (.nSeq NetKAT.id .deadlock) ∧ b = .project 0 .deadlock) ∨
    (a = .project 0 .deadlock ∧ b = .project 0 (.nSeq NetKAT.id .deadlock))
  refine ⟨R, ?_, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  constructor
  · intro a b h
    rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · intro a b h pending handled action p' pending' handled' step
    rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨p', step, Or.inl rfl⟩
    · obtain ⟨p'', hp', inner⟩ :=
        project_step_inv env 0 twoStepProcess pending handled action p' pending' handled' step
      subst hp'
      obtain ⟨σ, σ', hact, heq, ev, pT, hpend, hpend', hhand⟩ :=
        nSeq_step_inv env NetKAT.id (.nSeq NetKAT.id .deadlock) pending handled action p''
          pending' handled' inner
      subst hpend'
      subst hpend
      subst hhand
      subst hact
      subst heq
      exact ⟨.project 0 .deadlock,
        Step.cpol_project 0 oneStepProcess .deadlock (Action.packet σ σ')
          (σ :: pending') pending' handled (σ' :: handled)
          (Step.cpol_seq_ok NetKAT.id .deadlock σ σ' pending' handled ev),
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    · obtain ⟨p'', hp', inner⟩ :=
        project_step_inv env 0 oneStepProcess pending handled action p' pending' handled' step
      subst hp'
      obtain ⟨σ, σ', hact, heq, ev, pT, hpend, hpend', hhand⟩ :=
        nSeq_step_inv env NetKAT.id .deadlock pending handled action p'' pending' handled' inner
      subst hpend'
      subst hpend
      subst hhand
      subst hact
      subst heq
      exact ⟨.project 0 (.nSeq NetKAT.id .deadlock),
        Step.cpol_project 0 twoStepProcess (.nSeq NetKAT.id .deadlock) (Action.packet σ σ')
          (σ :: pending') pending' handled (σ' :: handled)
          (Step.cpol_seq_ok NetKAT.id (.nSeq NetKAT.id .deadlock) σ σ' pending' handled ev),
        Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    · exact absurd step (project_zero_no_step env (.nSeq NetKAT.id .deadlock) pending
        handled action _)
    · exact absurd step (project_zero_no_step env .deadlock pending handled action _)

/-- The two-step and one-step processes are NOT bisimilar: after the first
    common packet step, the two-step process can perform a second step that
    the one-step process cannot match.  Hence the bisimilarity at depth 1
    in `bisimilar_project_cutoff` cannot be lifted to unbounded
    equivalence. -/
theorem not_bisimilar_cutoff (env : RecEnv) :
    ¬ Bisimilar env twoStepProcess oneStepProcess := by
  rintro ⟨R, hR, hpq⟩
  have step1 : Step env
      (show Config from
        { proc := twoStepProcess, pending := [examplePacket], handled := [] })
      (Action.packet examplePacket examplePacket)
      (show Config from
        { proc := oneStepProcess, pending := [], handled := [examplePacket] }) :=
    Step.cpol_seq_ok NetKAT.id (.nSeq NetKAT.id .deadlock) examplePacket examplePacket [] []
      (historySem_id_self (History.singleton examplePacket))
  obtain ⟨q, hq, hR1⟩ := hR.2 twoStepProcess oneStepProcess hpq [examplePacket] []
    (Action.packet examplePacket examplePacket) oneStepProcess [] [examplePacket] step1
  cases hq with
  | cpol_seq_ok _ _ sigma sigma' pendingTail handled evaluates =>
    have step2 : Step env
        (show Config from
          { proc := oneStepProcess, pending := [examplePacket], handled := [] })
        (Action.packet examplePacket examplePacket)
        (show Config from
          { proc := .deadlock, pending := [], handled := [examplePacket] }) :=
      Step.cpol_seq_ok NetKAT.id .deadlock examplePacket examplePacket [] []
        (historySem_id_self (History.singleton examplePacket))
    obtain ⟨q2, hq2, _⟩ := hR.2 oneStepProcess .deadlock hR1 [examplePacket] []
      (Action.packet examplePacket examplePacket) .deadlock [] [examplePacket] step2
    cases hq2

/-- Projection depths 1 and 2 of the same process are NOT bisimilar: the
    depth-2 projection performs a second packet step that the depth-1
    projection cannot match.  This is the precise sense in which the
    projection budget is meaningful (and in which zero-depth projection
    differs from unrestricted execution). -/
theorem not_bisimilar_project_depths (env : RecEnv) :
    ¬ Bisimilar env (.project 1 twoStepProcess) (.project 2 twoStepProcess) := by
  rintro ⟨R, hR, hpq⟩
  have hR21 : R (.project 2 twoStepProcess) (.project 1 twoStepProcess) := hR.1 _ _ hpq
  have step1 : Step env
      (show Config from
        { proc := .project 2 twoStepProcess, pending := [examplePacket], handled := [] })
      (Action.packet examplePacket examplePacket)
      (show Config from
        { proc := .project 1 (.nSeq NetKAT.id .deadlock), pending := [],
          handled := [examplePacket] }) :=
    Step.cpol_project 1 twoStepProcess (.nSeq NetKAT.id .deadlock)
      (Action.packet examplePacket examplePacket) [examplePacket] [] [] [examplePacket]
      (Step.cpol_seq_ok NetKAT.id (.nSeq NetKAT.id .deadlock) examplePacket examplePacket
        [] [] (historySem_id_self (History.singleton examplePacket)))
  obtain ⟨q, hq, hR1⟩ := hR.2 (.project 2 twoStepProcess) (.project 1 twoStepProcess) hR21
    [examplePacket] [] (Action.packet examplePacket examplePacket)
    (.project 1 (.nSeq NetKAT.id .deadlock)) [] [examplePacket] step1
  cases hq with
  | cpol_project m q0 q1 _ _ _ _ _ inner =>
    cases inner with
    | cpol_seq_ok _ _ sigma sigma' pendingTail handled evaluates =>
      have step2 : Step env
          (show Config from
            { proc := .project 1 (.nSeq NetKAT.id .deadlock),
              pending := [examplePacket], handled := [] })
          (Action.packet examplePacket examplePacket)
          (show Config from
            { proc := .project 0 .deadlock, pending := [], handled := [examplePacket] }) :=
        Step.cpol_project 0 (.nSeq NetKAT.id .deadlock) .deadlock
          (Action.packet examplePacket examplePacket) [examplePacket] [] [] [examplePacket]
          (Step.cpol_seq_ok NetKAT.id .deadlock examplePacket examplePacket [] []
            (historySem_id_self (History.singleton examplePacket)))
      obtain ⟨q2, hq2, _⟩ := hR.2 (.project 1 (.nSeq NetKAT.id .deadlock))
        (.project 0 (.nSeq NetKAT.id .deadlock)) hR1 [examplePacket] []
        (Action.packet examplePacket examplePacket) (.project 0 .deadlock) []
        [examplePacket] step2
      cases hq2

------------------------------------------------------------------------
-- §5 Computable preprocessing towards `head` (§V, PDF p. 14)
------------------------------------------------------------------------

deriving instance DecidableEq for CommunicationAction

/-- The communication actions syntactically occurring in a process
    (Eq. 6: `L = {c | c ::= x?N | x!N}`).  Restricting by this set blocks
    every communication prefix of the process, which is how the paper
    ensures the `head`/`tail` precondition of §V. -/
def commActions : DyNetKAT → Finset CommunicationAction
  | .deadlock => ∅
  | .nSeq _ D => commActions D
  | .recv x N D => {CommunicationAction.recv x N} ∪ commActions D
  | .send x N D => {CommunicationAction.send x N} ∪ commActions D
  | .rcfgPrefix _ _ D => commActions D
  | .parallel D Q => commActions D ∪ commActions Q
  | .choice D Q => commActions D ∪ commActions Q
  | .leftMerge D Q => commActions D ∪ commActions Q
  | .commMerge D Q => commActions D ∪ commActions Q
  | .restrict _ D => commActions D
  | .project _ D => commActions D
  | .var _ => ∅

@[simp] theorem commActions_nSeq (N : NetKAT) (D : DyNetKAT) :
    commActions (.nSeq N D) = commActions D := rfl

@[simp] theorem commActions_recv (x : Channel) (N : NetKAT) (D : DyNetKAT) :
    commActions (.recv x N D) = {CommunicationAction.recv x N} ∪ commActions D := rfl

@[simp] theorem commActions_send (x : Channel) (N : NetKAT) (D : DyNetKAT) :
    commActions (.send x N D) = {CommunicationAction.send x N} ∪ commActions D := rfl

@[simp] theorem commActions_rcfgPrefix (x : Channel) (N : NetKAT) (D : DyNetKAT) :
    commActions (.rcfgPrefix x N D) = commActions D := rfl

@[simp] theorem commActions_choice (D Q : DyNetKAT) :
    commActions (.choice D Q) = commActions D ∪ commActions Q := rfl

/-- The fragment on which the Fig. 11 axioms δ⊥, δ;, δ;⊥, δ⊕ determine
    restriction completely: processes built from `⊥`, prefixes `at ; D`
    (all four prefix shapes), and `⊕`.  The paper's axioms are stated on
    normal forms, which live in exactly this fragment; parallel
    composition, merges, nested restriction, projection, and recursive
    variables are outside it (the latter are never resolved by
    preprocessing — H6A). -/
inductive PreprocessFragment : DyNetKAT → Prop
  | deadlock : PreprocessFragment .deadlock
  | nSeq : ∀ (N : NetKAT) (D : DyNetKAT),
      PreprocessFragment D → PreprocessFragment (.nSeq N D)
  | recv : ∀ (x : Channel) (N : NetKAT) (D : DyNetKAT),
      PreprocessFragment D → PreprocessFragment (.recv x N D)
  | send : ∀ (x : Channel) (N : NetKAT) (D : DyNetKAT),
      PreprocessFragment D → PreprocessFragment (.send x N D)
  | rcfgPrefix : ∀ (x : Channel) (N : NetKAT) (D : DyNetKAT),
      PreprocessFragment D → PreprocessFragment (.rcfgPrefix x N D)
  | choice : ∀ (D Q : DyNetKAT),
      PreprocessFragment D → PreprocessFragment Q → PreprocessFragment (.choice D Q)

/-- The paper's §V precondition for `head`/`tail`: the process contains no
    terms of shape `x?N` or `x!N`. -/
def CommFree : DyNetKAT → Prop
  | .deadlock => True
  | .nSeq _ D => CommFree D
  | .recv _ _ _ => False
  | .send _ _ _ => False
  | .rcfgPrefix _ _ D => CommFree D
  | .parallel D Q => CommFree D ∧ CommFree Q
  | .choice D Q => CommFree D ∧ CommFree Q
  | .leftMerge D Q => CommFree D ∧ CommFree Q
  | .commMerge D Q => CommFree D ∧ CommFree Q
  | .restrict _ D => CommFree D
  | .project _ D => CommFree D
  | .var _ => True

/-- The restriction operator `δL` of the paper, as a computable function on
    the δ-axiom fragment: each step is an instance of a Fig. 11 axiom
    (δ⊥, δ;, δ;⊥, δ⊕).  Unsupported shapes fail explicitly with `none` —
    in particular recursive variables are NOT unfolded (H6A) and nested
    restriction/projection are not eliminated (no paper axiom covers
    them). -/
def restrictElim (L : Finset CommunicationAction) : DyNetKAT → Option DyNetKAT
  | .deadlock => some .deadlock
  | .nSeq N D => (restrictElim L D).map (.nSeq N)
  | .recv x N D =>
      if CommunicationAction.recv x N ∈ L then some .deadlock
      else (restrictElim L D).map (.recv x N)
  | .send x N D =>
      if CommunicationAction.send x N ∈ L then some .deadlock
      else (restrictElim L D).map (.send x N)
  | .rcfgPrefix x N D => (restrictElim L D).map (.rcfgPrefix x N)
  | .choice D Q =>
      (restrictElim L D).bind (fun D' => (restrictElim L Q).map (fun Q' => .choice D' Q'))
  | .parallel _ _ => none
  | .leftMerge _ _ => none
  | .commMerge _ _ => none
  | .restrict _ _ => none
  | .project _ _ => none
  | .var _ => none

/-- Equational rewrites for `restrictElim`, one per constructor, so that
    proofs can unfold exactly one layer at a time. -/
theorem restrictElim_deadlock (L : Finset CommunicationAction) :
    restrictElim L .deadlock = some .deadlock := rfl

theorem restrictElim_nSeq (L : Finset CommunicationAction) (N : NetKAT) (D : DyNetKAT) :
    restrictElim L (.nSeq N D) = (restrictElim L D).map (.nSeq N) := rfl

theorem restrictElim_recv (L : Finset CommunicationAction) (x : Channel) (N : NetKAT)
    (D : DyNetKAT) :
    restrictElim L (.recv x N D) =
      if CommunicationAction.recv x N ∈ L then some .deadlock
      else (restrictElim L D).map (.recv x N) := rfl

theorem restrictElim_send (L : Finset CommunicationAction) (x : Channel) (N : NetKAT)
    (D : DyNetKAT) :
    restrictElim L (.send x N D) =
      if CommunicationAction.send x N ∈ L then some .deadlock
      else (restrictElim L D).map (.send x N) := rfl

theorem restrictElim_rcfgPrefix (L : Finset CommunicationAction) (x : Channel) (N : NetKAT)
    (D : DyNetKAT) :
    restrictElim L (.rcfgPrefix x N D) = (restrictElim L D).map (.rcfgPrefix x N) := rfl

theorem restrictElim_choice (L : Finset CommunicationAction) (D Q : DyNetKAT) :
    restrictElim L (.choice D Q) =
      (restrictElim L D).bind (fun D' => (restrictElim L Q).map (fun Q' => .choice D' Q')) :=
  rfl

theorem restrictElim_parallel (L : Finset CommunicationAction) (D Q : DyNetKAT) :
    restrictElim L (.parallel D Q) = none := rfl

theorem restrictElim_leftMerge (L : Finset CommunicationAction) (D Q : DyNetKAT) :
    restrictElim L (.leftMerge D Q) = none := rfl

theorem restrictElim_commMerge (L : Finset CommunicationAction) (D Q : DyNetKAT) :
    restrictElim L (.commMerge D Q) = none := rfl

theorem restrictElim_restrict (L : Finset CommunicationAction) (M : Set CommunicationAction)
    (D : DyNetKAT) :
    restrictElim L (.restrict M D) = none := rfl

theorem restrictElim_project (L : Finset CommunicationAction) (n : Nat) (D : DyNetKAT) :
    restrictElim L (.project n D) = none := rfl

theorem restrictElim_var (L : Finset CommunicationAction) (name : Var) :
    restrictElim L (.var name) = none := rfl

set_option linter.unusedVariables false in
/-- The paper's preprocessing step (§V): restrict the process by the set of
    communication actions it contains, so that no `x?N`/`x!N` prefix can
    ever fire.  Recursive variables are deliberately not resolved.  The
    environment argument is carried for uniformity with the integration
    theorems (the δ-axiom fragment contains no recursive variables, so the
    transformation itself is environment-free). -/
def preprocess (env : RecEnv) (p : DyNetKAT) : Option DyNetKAT :=
  restrictElim (commActions p) p

/-- Preprocessing conditions for the S4A integration theorem: the process
    lies in the δ-axiom fragment, and every directly occurring recursive
    variable is defined (which is vacuous on this fragment — see
    `PreprocessFragment.defined` — but kept to mirror the target theorem
    shape and the H6A environment discipline). -/
def PreprocessingConditions (env : RecEnv) (p : DyNetKAT) : Prop :=
  PreprocessFragment p ∧ Defined env p

/-- Every process in the δ-axiom fragment has no recursive variables, so
    the `Defined` side condition of `PreprocessingConditions` is vacuous
    there. -/
theorem PreprocessFragment.defined (env : RecEnv) (p : DyNetKAT) (hf : PreprocessFragment p) :
    Defined env p := by
  induction hf with
  | deadlock => intro name hmem; exact absurd hmem (Finset.not_mem_empty name)
  | nSeq N D _ ih =>
      intro name hmem
      simp only [recursiveVars] at hmem
      exact ih name hmem
  | recv x N D _ ih =>
      intro name hmem
      simp only [recursiveVars] at hmem
      exact ih name hmem
  | send x N D _ ih =>
      intro name hmem
      simp only [recursiveVars] at hmem
      exact ih name hmem
  | rcfgPrefix x N D _ ih =>
      intro name hmem
      simp only [recursiveVars] at hmem
      exact ih name hmem
  | choice D Q _ _ ihD ihQ =>
      intro name hmem
      simp only [recursiveVars, Finset.mem_union] at hmem
      rcases hmem with h | h
      · exact ihD name h
      · exact ihQ name h

/-- `restrictElim` succeeds on the whole δ-axiom fragment. -/
theorem restrictElim_defined (L : Finset CommunicationAction) (p : DyNetKAT) :
    PreprocessFragment p → ∃ q, restrictElim L p = some q := by
  intro hf
  induction hf with
  | deadlock => exact ⟨.deadlock, restrictElim_deadlock L⟩
  | nSeq N D _ ih =>
      obtain ⟨D', hD⟩ := ih
      exact ⟨.nSeq N D', by rw [restrictElim_nSeq, hD]; rfl⟩
  | recv x N D _ ih =>
      obtain ⟨D', hD⟩ := ih
      by_cases hmem : CommunicationAction.recv x N ∈ L
      · exact ⟨.deadlock, by rw [restrictElim_recv, if_pos hmem]⟩
      · exact ⟨.recv x N D', by rw [restrictElim_recv, if_neg hmem, hD]; rfl⟩
  | send x N D _ ih =>
      obtain ⟨D', hD⟩ := ih
      by_cases hmem : CommunicationAction.send x N ∈ L
      · exact ⟨.deadlock, by rw [restrictElim_send, if_pos hmem]⟩
      · exact ⟨.send x N D', by rw [restrictElim_send, if_neg hmem, hD]; rfl⟩
  | rcfgPrefix x N D _ ih =>
      obtain ⟨D', hD⟩ := ih
      exact ⟨.rcfgPrefix x N D', by rw [restrictElim_rcfgPrefix, hD]; rfl⟩
  | choice D Q _ _ ihD ihQ =>
      obtain ⟨D', hD⟩ := ihD
      obtain ⟨Q', hQ⟩ := ihQ
      exact ⟨.choice D' Q', by rw [restrictElim_choice, hD, hQ]; rfl⟩

/-- Soundness of `restrictElim`: each elimination step is an instance of a
    Fig. 11 restriction axiom, so `δL(p)` is bisimilar to the eliminated
    process. -/
theorem restrictElim_sound (env : RecEnv) (L : Finset CommunicationAction) (p : DyNetKAT) :
    ∀ q, restrictElim L p = some q →
      Bisimilar env (.restrict (↑L : Set CommunicationAction) p) q := by
  induction p with
  | deadlock =>
      intro q h
      rw [restrictElim_deadlock, Option.some.injEq] at h
      subst h
      exact restrict_deadlock_bisim env _
  | nSeq N D ih =>
      intro q h
      rw [restrictElim_nSeq, Option.map_eq_some'] at h
      obtain ⟨D', hD', rfl⟩ := h
      exact Bisimilar.trans env (restrict_nSeq_bisim env _ N D)
        (Bisimilar.nSeq_left env (ih D' hD'))
  | recv x N D ih =>
      intro q h
      rw [restrictElim_recv] at h
      split at h
      · rename_i hmem
        have hq : .deadlock = q := Option.some.inj h
        subst hq
        exact restrict_recv_blocked_bisim env _ x N D
          (show CommunicationAction.recv x N ∈ (↑L : Set CommunicationAction) from hmem)
      · rename_i hmem
        obtain ⟨D', hD', rfl⟩ := Option.map_eq_some.mp h
        have hnotmem : CommunicationAction.recv x N ∉ (↑L : Set CommunicationAction) :=
          fun hmem' => hmem hmem'
        exact Bisimilar.trans env (restrict_recv_allowed_bisim env _ x N D hnotmem)
          (Bisimilar.recv_left env (ih D' hD'))
  | send x N D ih =>
      intro q h
      rw [restrictElim_send] at h
      split at h
      · rename_i hmem
        have hq : .deadlock = q := Option.some.inj h
        subst hq
        exact restrict_send_blocked_bisim env _ x N D
          (show CommunicationAction.send x N ∈ (↑L : Set CommunicationAction) from hmem)
      · rename_i hmem
        obtain ⟨D', hD', rfl⟩ := Option.map_eq_some.mp h
        have hnotmem : CommunicationAction.send x N ∉ (↑L : Set CommunicationAction) :=
          fun hmem' => hmem hmem'
        exact Bisimilar.trans env (restrict_send_allowed_bisim env _ x N D hnotmem)
          (Bisimilar.send_left env (ih D' hD'))
  | rcfgPrefix x N D ih =>
      intro q h
      rw [restrictElim_rcfgPrefix, Option.map_eq_some'] at h
      obtain ⟨D', hD', rfl⟩ := h
      exact Bisimilar.trans env (restrict_rcfgPrefix_bisim env _ x N D)
        (Bisimilar.rcfgPrefix_left env (ih D' hD'))
  | choice D Q ihD ihQ =>
      intro q h
      rw [restrictElim_choice] at h
      simp only [Option.bind_eq_some, Option.map_eq_some'] at h
      obtain ⟨D', hD, Q', hQ, rfl⟩ := h
      exact Bisimilar.trans env (restrict_choice_bisim env _ D Q)
        (Bisimilar.trans env (Bisimilar.choice_left env (ihD D' hD))
          (Bisimilar.choice_right env (ihQ Q' hQ)))
  | parallel D Q _ _ => intro q h; rw [restrictElim_parallel] at h; simp at h
  | leftMerge D Q _ _ => intro q h; rw [restrictElim_leftMerge] at h; simp at h
  | commMerge D Q _ _ => intro q h; rw [restrictElim_commMerge] at h; simp at h
  | restrict M D _ => intro q h; rw [restrictElim_restrict] at h; simp at h
  | project n D _ => intro q h; rw [restrictElim_project] at h; simp at h
  | var name => intro q h; rw [restrictElim_var] at h; simp at h

/-- Combined effect of `restrictElim` on the δ-axiom fragment when every
    communication action of the process is forbidden: the result contains
    no `x?N`/`x!N` terms (the §V precondition for `head`/`tail`) and lies
    in the S4A `HeadSupported` fragment. -/
theorem restrictElim_effect (L : Finset CommunicationAction) (p : DyNetKAT) :
    PreprocessFragment p → (∀ a ∈ commActions p, a ∈ L) →
    ∀ q, restrictElim L p = some q → CommFree q ∧ HeadSupported q := by
  intro hf
  induction hf with
  | deadlock =>
      intro hsub q h
      rw [restrictElim_deadlock, Option.some.injEq] at h
      subst h
      exact ⟨trivial, HeadSupported.deadlock⟩
  | nSeq N D _ ih =>
      intro hsub q h
      rw [restrictElim_nSeq, Option.map_eq_some'] at h
      obtain ⟨D', hD', rfl⟩ := h
      obtain ⟨hcf, hhs⟩ := ih (fun a ha => hsub a ha) D' hD'
      exact ⟨hcf, HeadSupported.nSeq N D' hhs⟩
  | recv x N D _ ih =>
      intro hsub q h
      rw [restrictElim_recv] at h
      split at h
      · rename_i hmem
        have hq : .deadlock = q := Option.some.inj h
        subst hq
        exact ⟨trivial, HeadSupported.deadlock⟩
      · rename_i hmem
        exact absurd (hsub _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl))) hmem
  | send x N D _ ih =>
      intro hsub q h
      rw [restrictElim_send] at h
      split at h
      · rename_i hmem
        have hq : .deadlock = q := Option.some.inj h
        subst hq
        exact ⟨trivial, HeadSupported.deadlock⟩
      · rename_i hmem
        exact absurd (hsub _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl))) hmem
  | rcfgPrefix x N D _ ih =>
      intro hsub q h
      rw [restrictElim_rcfgPrefix, Option.map_eq_some'] at h
      obtain ⟨D', hD', rfl⟩ := h
      obtain ⟨hcf, hhs⟩ := ih (fun a ha => hsub a ha) D' hD'
      exact ⟨hcf, HeadSupported.rcfgPrefix x N D'⟩
  | choice D Q _ _ ihD ihQ =>
      intro hsub q h
      rw [restrictElim_choice] at h
      simp only [Option.bind_eq_some, Option.map_eq_some'] at h
      obtain ⟨D', hD, Q', hQ, rfl⟩ := h
      obtain ⟨hcfD, hhsD⟩ := ihD (fun a ha => hsub a (Finset.subset_union_left ha)) D' hD
      obtain ⟨hcfQ, hhsQ⟩ := ihQ (fun a ha => hsub a (Finset.subset_union_right ha)) Q' hQ
      exact ⟨⟨hcfD, hcfQ⟩, HeadSupported.choice D' Q' hhsD hhsQ⟩

/-- S4A's `HeadSupported` does not by itself imply the paper's §V
    precondition: a reconfiguration prefix may hide communication prefixes
    in its continuation.  This is why preprocessing (restriction δ) is
    required before `head`, exactly as the paper says. -/
theorem headSupported_not_commFree :
    HeadSupported (.rcfgPrefix "c" NetKAT.id (.recv "d" NetKAT.id .deadlock)) ∧
      ¬ CommFree (.rcfgPrefix "c" NetKAT.id (.recv "d" NetKAT.id .deadlock)) := by
  constructor
  · exact HeadSupported.rcfgPrefix "c" NetKAT.id _
  · intro h
    exact h

/-- Main S4B integration theorem (derived form of the target statement):
    under the preprocessing conditions, `preprocess` succeeds and its
    result lies in the S4A `HeadSupported` fragment.  The target form
    `HeadSupported (preprocess env process)` is not valid as stated because
    preprocessing can fail (explicit `none`) on processes outside the
    δ-axiom fragment — in particular on processes with recursive variables,
    which restriction must not resolve (H6A). -/
theorem preprocess_head_supported (env : RecEnv) (p : DyNetKAT)
    (h : PreprocessingConditions env p) :
    ∃ q, preprocess env p = some q ∧ HeadSupported q := by
  obtain ⟨q, hq⟩ := restrictElim_defined (commActions p) p h.1
  obtain ⟨_, hsup⟩ := restrictElim_effect (commActions p) p h.1 (fun _ ha => ha) q hq
  exact ⟨q, hq, hsup⟩

/-- The §V precondition (no `x?N`/`x!N` terms) is established by
    preprocessing. -/
theorem preprocess_commFree (env : RecEnv) (p : DyNetKAT)
    (h : PreprocessingConditions env p) :
    ∃ q, preprocess env p = some q ∧ CommFree q := by
  obtain ⟨q, hq⟩ := restrictElim_defined (commActions p) p h.1
  obtain ⟨hcf, _⟩ := restrictElim_effect (commActions p) p h.1 (fun _ ha => ha) q hq
  exact ⟨q, hq, hcf⟩

/-- Preprocessing is sound: the result is bisimilar to the restricted
    process `δ_{commActions(p)}(p)` of the paper. -/
theorem preprocess_bisimilar (env : RecEnv) (p : DyNetKAT)
    (h : PreprocessingConditions env p) :
    ∃ q, preprocess env p = some q ∧
      Bisimilar env (.restrict (↑(commActions p) : Set CommunicationAction) p) q := by
  obtain ⟨q, hq⟩ := restrictElim_defined (commActions p) p h.1
  exact ⟨q, hq, restrictElim_sound env (commActions p) p q hq⟩

/-- Full S4A integration: preprocessing yields a `HeadSupported` process on
    which S4A's `head` extraction succeeds. -/
theorem preprocess_head_some (env : RecEnv) (p : DyNetKAT)
    (h : PreprocessingConditions env p) :
    ∃ q H, preprocess env p = some q ∧ HeadSupported q ∧ head q = some H := by
  obtain ⟨q, hq, hsup⟩ := preprocess_head_supported env p h
  obtain ⟨H, hH⟩ := head_supported_some q hsup
  exact ⟨q, H, hq, hsup, hH⟩

end DyNetKAT.DyNetKAT
