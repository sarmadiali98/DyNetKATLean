import DyNetKAT.DyNetKAT.SequentialReachability
------------------------------------------------------------------------
-- S5B: Formal safety-checking criterion (paper §V, Eqs. (34)–(35))
--
-- Paper interpretation (arXiv:2102.10035v4, §V "Implementation", the
-- stateful firewall example, verified against the paper text and the
-- original tool's verdict generation, cf. docs/SAFETY_WORKFLOW_AUDIT.md):
--
--   `in` and `out` are NetKAT *predicates* (tests), embedded as NetKAT
--   policies: for the firewall example the paper sets
--   `in := port = ext`, `out := port = int`, `R = {rcfg_{secConReq,1}}`.
--   The original tool takes paired `in_packets`/`out_packets` predicates
--   from its JSON input and compiles them into NetKAT test terms.
--
--   (34)  `in · head(Init) · out ≡ 0`
--         expresses that packets at port `ext` are NOT able to reach
--         port `int` in the initial configuration (initial isolation).
--
--   (35)  `in · head(tail(Init, R)) · out ≢ 0`
--         expresses that the configuration after the synchronization on
--         the channel `secConReq` (the reconfiguration events in `R`)
--         DOES allow this flow (post-reconfiguration reachability).
--
--   The conjunction of (34) and (35) establishes the paper's combined
--   claim: "the packets at port ext can arrive at port int only after a
--   proper reconfiguration on the channel secConReq".  It is NOT a bare
--   safety verdict: (34) is an isolation property, (35) is a reachability
--   witness demonstrating that the reconfiguration in `R` is exactly
--   what enables the flow.  The two conditions are therefore reported
--   separately here (see `SafetyCheckResult`), never collapsed into one
--   Boolean without the explicit `bothHold` conjunction.
--
--   Original tool (`hcantunc/DyNetiKAT`, commit 1c6bd42): for a
--   reachability property `r` it reduces the extracted NetKAT term to a
--   string and calls the external decision procedure as
--   `equiv (in · net · out) zero`; the property is *satisfied* iff the
--   answer is `false` for the expected `!0` shape (term ≢ 0) and `true`
--   for the expected `=0` shape (term ≡ 0).  No counterexamples are
--   generated; a failing property is reported as the bare word
--   "violated".  Paper and tool agree on the shape `in · H · out` (no
--   star: `head`/`tail` already extract the full forwarding policy);
--   the tool additionally supports waypointing (`w`) properties, which
--   are outside the scope of this milestone.
--
-- This module provides:
--   §1  an existential characterization of the symbolic zero check;
--   §2  the property policy `in · H · out` (`reachabilityPolicy`) with
--       its composition characterization (via `seq_sem`);
--   §3  the two independent checkers `checkCondition34`/`checkCondition35`
--       with machine-checked semantic correctness theorems, including
--       the relational-transition characterizations via `head_spec` and
--       `tail_head_spec`;
--   §4  the result type `SafetyCheckResult` preserving preprocessing
--       failure, head-extraction failure, tail-extraction failure, and
--       the two successful condition evaluations as distinct outcomes;
--   §5  the end-to-end pipeline `Internal.safetyCheck` with its correctness
--       theorem on the supported preprocessing fragment.
--
-- Scope boundary: this is a verified checker for the currently supported
-- preprocessing fragment (the δ-axiom fragment of S4B, feeding S4A `head`
-- and S5A `tail`).  It does NOT implement recursive-variable unfolding,
-- full Lemma 9 normalization, AIP soundness, environment-free
-- bisimulation, a graph-based recursive checker, or E_NK derivability,
-- and it is NOT a claim of equivalence with the complete original
-- DyNetiKAT tool.
------------------------------------------------------------------------

import DyNetKAT.NetKAT.Decision
import DyNetKAT.DyNetKAT.SafetyHead
import DyNetKAT.DyNetKAT.TailExtraction
import DyNetKAT.DyNetKAT.GraphTail
import DyNetKAT.DyNetKAT.GraphRestriction

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

open DyNetKAT.NetKAT

------------------------------------------------------------------------
-- §1 Existential characterization of the symbolic zero check
------------------------------------------------------------------------

/-- Packet-level existence probe: the input packet `σ` reaches a nonempty
    output set under `p`.  Defined by matching on the verified evaluator's
    result, keeping `unsupported` distinct from a supported empty set. -/
def netkatNonemptyAt (p : NetKAT schema) (σ : schema.Packet) : Prop :=
  match execute p σ with
  | .supported B => B ≠ ∅
  | .unsupported => False

/-- Decidability of the probe, by matching on the evaluator's result. -/
instance instDecidableNetkatNonemptyAt (p : NetKAT schema) (σ : schema.Packet) :
    Decidable (netkatNonemptyAt p σ) := by
  letI := schema.packetEq
  unfold netkatNonemptyAt
  cases h : execute p σ with
  | supported B => exact inferInstanceAs (Decidable (B ≠ ∅))
  | unsupported => exact inferInstanceAs (Decidable False)

/-- The probe on supported executions is exactly nonemptiness of the
    computed output set. -/
theorem netkatNonemptyAt_iff (p : NetKAT schema) (σ : schema.Packet) (B : Finset schema.Packet)
    (hB : execute p σ = .supported B) : netkatNonemptyAt p σ ↔ B ≠ ∅ := by
  simp only [netkatNonemptyAt, hB]

/-- Rejection of equality with drop gives a related packet pair. -/
theorem netkatIsZero_false_iff_exists (p : NetKAT schema) :
    netkatIsZero p = false ↔ ∃ σ τ : schema.Packet, Semantics p σ τ := by
  classical
  refine Bool.eq_false_iff.trans ((not_congr (netkatIsZero_correct p)).trans ?_)
  push_neg
  rfl

/-- Symbolic nonemptiness probe for the packet relation. -/
def netkatExistsNonempty (p : NetKAT schema) : Bool := !netkatIsZero p

theorem netkatExistsNonempty_sound (p : NetKAT schema)
    (h : netkatExistsNonempty p = true) : ∃ σ τ : schema.Packet, Semantics p σ τ :=
  (netkatIsZero_false_iff_exists p).mp (by simpa [netkatExistsNonempty] using h)

theorem netkatExistsNonempty_complete (p : NetKAT schema)
    (h : ∃ σ τ : schema.Packet, Semantics p σ τ) : netkatExistsNonempty p = true :=
  by simpa [netkatExistsNonempty] using (netkatIsZero_false_iff_exists p).mpr h

------------------------------------------------------------------------
-- §2 The property policy `in · H · out`
------------------------------------------------------------------------

/-- The paper's property policy `in · H · out` (§V, Eqs. (34)–(35)):
    the sequential composition of the ingress predicate, the extracted
    NetKAT policy `H`, and the egress predicate.  `in` and `out` are
    NetKAT policies (predicates are tests, and tests are policies), so
    no new semantic relation is introduced: the composition is the
    existing `NetKAT.seq`. -/
def reachabilityPolicy (ingress core egress : NetKAT schema) : NetKAT schema :=
  NetKAT.seq ingress (NetKAT.seq core egress)

/-- Composition characterization of the property policy: a packet pair
    `(σ, τ)` lies in `⟦in · H · out⟧` exactly when there are intermediate
    packets `ρ, κ` with `σ` reaching `ρ` through the ingress predicate,
    `ρ` reaching `κ` through the core policy, and `κ` reaching `τ`
    through the egress predicate.  Proved from the existing `seq_sem`. -/
theorem reachabilityPolicy_sem (ingress core egress : NetKAT schema) (σ τ : schema.Packet) :
    Semantics (reachabilityPolicy ingress core egress) σ τ ↔
      ∃ ρ κ : schema.Packet,
        Semantics ingress σ ρ ∧ Semantics core ρ κ ∧ Semantics egress κ τ := by
  rw [reachabilityPolicy, seq_sem]
  constructor
  · rintro ⟨ρ, h₁, h₂⟩
    rw [seq_sem] at h₂
    obtain ⟨κ, h₂, h₃⟩ := h₂
    exact ⟨ρ, κ, h₁, h₂, h₃⟩
  · rintro ⟨ρ, κ, h₁, h₂, h₃⟩
    exact ⟨ρ, h₁, κ, h₂, h₃⟩

/-- Zero characterization of the property policy: `in · H · out ≡ 0`
    exactly when no triple of packet pairs composes an ingress step, a
    core step, and an egress step. -/
theorem netkatIsZero_reachabilityPolicy_true_iff (ingress core egress : NetKAT schema) :
    netkatIsZero (reachabilityPolicy ingress core egress) = true ↔
      ∀ σ ρ κ τ : schema.Packet,
        ¬ (Semantics ingress σ ρ ∧ Semantics core ρ κ ∧ Semantics egress κ τ) := by
  rw [netkatIsZero_correct]
  constructor
  · intro h σ ρ κ τ htrio
    exact h σ τ ((reachabilityPolicy_sem ingress core egress σ τ).mpr ⟨ρ, κ, htrio⟩)
  · intro h σ τ hsem
    obtain ⟨ρ, κ, h₁, h₂, h₃⟩ := (reachabilityPolicy_sem ingress core egress σ τ).mp hsem
    refine h σ ρ κ τ ?_
    exact ⟨h₁, h₂, h₃⟩

/-- Nonzero characterization of the property policy: `in · H · out ≢ 0`
    exactly when at least one triple of packet pairs composes an ingress
    step, a core step, and an egress step (finite-domain existential,
    via `netkatIsZero_false_iff_exists`). -/
theorem netkatIsZero_reachabilityPolicy_false_iff (ingress core egress : NetKAT schema) :
    netkatIsZero (reachabilityPolicy ingress core egress) = false ↔
      ∃ σ ρ κ τ : schema.Packet,
        Semantics ingress σ ρ ∧ Semantics core ρ κ ∧ Semantics egress κ τ := by
  rw [netkatIsZero_false_iff_exists]
  constructor
  · rintro ⟨σ, τ, hsem⟩
    obtain ⟨ρ, κ, h₁, h₂, h₃⟩ := (reachabilityPolicy_sem ingress core egress σ τ).mp hsem
    exact ⟨σ, ρ, κ, τ, h₁, h₂, h₃⟩
  · rintro ⟨σ, ρ, κ, τ, h₁, h₂, h₃⟩
    exact ⟨σ, τ, (reachabilityPolicy_sem ingress core egress σ τ).mpr ⟨ρ, κ, h₁, h₂, h₃⟩⟩

/-- Predicate tests denote the test relation (definitional). -/
theorem sem_test_iff (Pr : Predicate schema) (σ τ : schema.Packet) :
    Semantics (.test Pr) σ τ ↔ (Pr.holds σ ∧ σ = τ) := by
  simp only [Semantics]

/-- Test form of the zero characterization: with `in` and `out` NetKAT
    predicates, `in · H · out ≡ 0` exactly when no relational transition
    `(σ, κ)` of `H` leads from a packet satisfying `in` to a packet
    satisfying `out`.  This is the paper's reading of (34): packets at
    `ext` are not able to reach `int` under the extracted configuration. -/
theorem netkatIsZero_reachabilityPolicy_tests_true_iff (core : NetKAT schema)
    (Pin Pout : Predicate schema) :
    netkatIsZero (reachabilityPolicy (.test Pin) core (.test Pout)) = true ↔
      ∀ σ κ : schema.Packet, Semantics core σ κ → ¬ (Pin.holds σ ∧ Pout.holds κ) := by
  rw [netkatIsZero_reachabilityPolicy_true_iff]
  constructor
  · intro h σ κ hH hpair
    apply h σ σ κ κ
    exact ⟨⟨hpair.1, rfl⟩, hH, ⟨hpair.2, rfl⟩⟩
  · intro h σ ρ κ τ htrio
    obtain ⟨hPin, hρ⟩ := (sem_test_iff Pin σ ρ).mp htrio.1
    obtain ⟨hPout, hτ⟩ := (sem_test_iff Pout κ τ).mp htrio.2.2
    subst hρ
    subst hτ
    apply h σ κ htrio.2.1
    exact ⟨hPin, hPout⟩

/-- Test form of the nonzero characterization: with `in` and `out` NetKAT
    predicates, `in · H · out ≢ 0` exactly when some relational transition
    `(σ, κ)` of `H` leads from a packet satisfying `in` to a packet
    satisfying `out`.  This is the paper's reading of (35): the
    configuration after the reconfiguration allows the flow. -/
theorem netkatIsZero_reachabilityPolicy_tests_false_iff (core : NetKAT schema)
    (Pin Pout : Predicate schema) :
    netkatIsZero (reachabilityPolicy (.test Pin) core (.test Pout)) = false ↔
      ∃ σ κ : schema.Packet, Semantics core σ κ ∧ Pin.holds σ ∧ Pout.holds κ := by
  rw [netkatIsZero_reachabilityPolicy_false_iff]
  constructor
  · rintro ⟨σ, ρ, κ, τ, hPin, hCore, hPout⟩
    obtain ⟨hPin', hρ⟩ := (sem_test_iff Pin σ ρ).mp hPin
    obtain ⟨hPout', hτ⟩ := (sem_test_iff Pout κ τ).mp hPout
    subst hρ
    subst hτ
    exact ⟨σ, κ, hCore, hPin', hPout'⟩
  · rintro ⟨σ, κ, hCore, hPin, hPout⟩
    exact ⟨σ, σ, κ, κ, ⟨hPin, rfl⟩, hCore, ⟨hPout, rfl⟩⟩

------------------------------------------------------------------------
-- §3 The two independent checkers
------------------------------------------------------------------------

/-- Condition (34) checker: `in · head(Init) · out ≡ 0`.

    Returns `some true` when the composed property policy is zero (the
    condition holds), `some false` when it is nonzero (the condition
    fails), and `none` when `head` extraction fails.  A failed extraction
    is NEVER interpreted as a zero policy: `none` is not `some true`. -/
def checkCondition34 (ingress egress : NetKAT schema) (init : DyNetKAT schema) : Option Bool :=
  match head init with
  | some H => some (netkatIsZero (reachabilityPolicy ingress H egress))
  | none => none

/-- Condition (35) checker: `in · head(tail(Init, R)) · out ≢ 0`.

    Returns `some true` when the composed property policy is nonzero (the
    condition holds), `some false` when it is zero (the condition fails),
    and `none` when `tail` extraction or the subsequent `head` extraction
    fails.  A failed extraction is NEVER interpreted as a zero policy:
    `none` is not `some false`. -/
def checkCondition35 (ingress egress : NetKAT schema) (R : ReconfigSet schema) (init : DyNetKAT schema) :
    Option Bool :=
  match tail R init with
  | none => none
  | some Q =>
      match head Q with
      | none => none
      | some H => some (!netkatIsZero (reachabilityPolicy ingress H egress))

/-- Behavior of `checkCondition34` on failed head extraction. -/
theorem checkCondition34_none (ingress egress : NetKAT schema) (D : DyNetKAT schema)
    (h : head D = none) : checkCondition34 ingress egress D = none := by
  simp only [checkCondition34, h]

/-- Behavior of `checkCondition34` on successful head extraction: the
    returned Boolean is exactly the verified zero checker applied to
    `in · H · out`. -/
theorem checkCondition34_some (ingress egress : NetKAT schema) (D : DyNetKAT schema) (H : NetKAT schema)
    (h : head D = some H) :
    checkCondition34 ingress egress D =
      some (netkatIsZero (reachabilityPolicy ingress H egress)) := by
  simp only [checkCondition34, h]

/-- Behavior of `checkCondition35` on failed tail extraction. -/
theorem checkCondition35_none_tail (ingress egress : NetKAT schema) (R : ReconfigSet schema)
    (D : DyNetKAT schema) (h : tail R D = none) :
    checkCondition35 ingress egress R D = none := by
  simp only [checkCondition35, h]

/-- Behavior of `checkCondition35` on a successful tail extraction whose
    head extraction fails. -/
theorem checkCondition35_none_head (ingress egress : NetKAT schema) (R : ReconfigSet schema)
    (D Q : DyNetKAT schema) (hQ : tail R D = some Q) (hH : head Q = none) :
    checkCondition35 ingress egress R D = none := by
  simp only [checkCondition35, hQ, hH]

/-- Behavior of `checkCondition35` on fully successful extraction: the
    returned Boolean is exactly the negation of the verified zero checker
    applied to `in · H · out` (the paper's `≢ 0`). -/
theorem checkCondition35_some (ingress egress : NetKAT schema) (R : ReconfigSet schema)
    (D Q : DyNetKAT schema) (H : NetKAT schema) (hQ : tail R D = some Q) (hH : head Q = some H) :
    checkCondition35 ingress egress R D =
      some (!netkatIsZero (reachabilityPolicy ingress H egress)) := by
  simp only [checkCondition35, hQ, hH]

/-- Semantic correctness of the condition-(34) checker: on successful
    head extraction with policy `H`, the checker result is `true` exactly
    when the property policy `in · H · out` denotes the empty relation. -/
theorem checkCondition34_correct (ingress egress : NetKAT schema) (D : DyNetKAT schema) (H : NetKAT schema)
    (hH : head D = some H) (b : Bool) (h : checkCondition34 ingress egress D = some b) :
    b = true ↔ ∀ σ τ : schema.Packet, ¬ Semantics (reachabilityPolicy ingress H egress) σ τ := by
  rw [checkCondition34_some ingress egress D H hH] at h
  have hb : b = netkatIsZero (reachabilityPolicy ingress H egress) :=
    (Option.some.inj h).symm
  subst hb
  exact netkatIsZero_correct _

/-- Semantic correctness of the condition-(34) checker, in the
    relational-transition form: on supported input, the checker result is
    `true` exactly when there is NO packet pair `(ρ, κ)` contributed by
    the head configuration (`HeadSpec D`) that composes with an ingress
    step before it and an egress step after it.  This is the absence of
    all corresponding relational transitions of the initial
    configuration. -/
theorem checkCondition34_headSpec (ingress egress : NetKAT schema) (D : DyNetKAT schema)
    (hsup : HeadSupported D) (H : NetKAT schema) (hH : head D = some H) (b : Bool)
    (h : checkCondition34 ingress egress D = some b) :
    b = true ↔ ∀ σ ρ κ τ : schema.Packet,
      ¬ (Semantics ingress σ ρ ∧ HeadSpec D ρ κ ∧ Semantics egress κ τ) := by
  rw [checkCondition34_correct ingress egress D H hH b h]
  constructor
  · intro hall σ ρ κ τ htrio
    refine hall σ τ ?_
    exact (reachabilityPolicy_sem ingress H egress σ τ).mpr
      ⟨ρ, κ, htrio.1, (head_spec D hsup ρ κ H hH).mpr htrio.2.1, htrio.2.2⟩
  · intro hex σ τ hsem
    obtain ⟨ρ, κ, h₁, h₂, h₃⟩ := (reachabilityPolicy_sem ingress H egress σ τ).mp hsem
    refine hex σ ρ κ τ ?_
    exact ⟨h₁, (head_spec D hsup ρ κ H hH).mp h₂, h₃⟩

/-- Semantic correctness of the condition-(35) checker: on fully
    successful extraction with policy `H`, the checker result is `true`
    exactly when the property policy `in · H · out` denotes a nonempty
    relation (finite-domain existential, via
    `netkatIsZero_false_iff_exists`). -/
theorem checkCondition35_correct (ingress egress : NetKAT schema) (R : ReconfigSet schema)
    (D Q : DyNetKAT schema) (H : NetKAT schema) (hQ : tail R D = some Q) (hH : head Q = some H)
    (b : Bool) (h : checkCondition35 ingress egress R D = some b) :
    b = true ↔ ∃ σ τ : schema.Packet, Semantics (reachabilityPolicy ingress H egress) σ τ := by
  rw [checkCondition35_some ingress egress R D Q H hQ hH] at h
  have hb : b = !netkatIsZero (reachabilityPolicy ingress H egress) :=
    (Option.some.inj h).symm
  subst hb
  constructor
  · intro hbtrue
    have hz : netkatIsZero (reachabilityPolicy ingress H egress) = false := by
      cases hd : netkatIsZero (reachabilityPolicy ingress H egress) with
      | false => rfl
      | true => rw [hd] at hbtrue; simp at hbtrue
    exact (netkatIsZero_false_iff_exists _).mp hz
  · rintro ⟨σ, τ, hsem⟩
    cases hd : netkatIsZero (reachabilityPolicy ingress H egress) with
    | false => rfl
    | true => exact absurd hsem (((netkatIsZero_correct _).mp hd) σ τ)

/-- Semantic correctness of the condition-(35) checker, in the
    relational-transition form: on supported input, the checker result is
    `true` exactly when there EXISTS a packet pair `(ρ, κ)` contributed by
    the post-reconfiguration configuration (`TailHeadSpec R D`) that
    composes with an ingress step before it and an egress step after it.
    This is the existence of at least one corresponding relational
    transition of the post-reconfiguration configuration. -/
theorem checkCondition35_tailHeadSpec (ingress egress : NetKAT schema) (R : ReconfigSet schema)
    (D : DyNetKAT schema) (hsup : TailSupported D) (Q : DyNetKAT schema) (H : NetKAT schema)
    (hQ : tail R D = some Q) (hH : head Q = some H) (b : Bool)
    (h : checkCondition35 ingress egress R D = some b) :
    b = true ↔ ∃ σ ρ κ τ : schema.Packet,
      Semantics ingress σ ρ ∧ TailHeadSpec R D ρ κ ∧ Semantics egress κ τ := by
  rw [checkCondition35_correct ingress egress R D Q H hQ hH b h]
  constructor
  · rintro ⟨σ, τ, hsem⟩
    obtain ⟨ρ, κ, h₁, h₂, h₃⟩ := (reachabilityPolicy_sem ingress H egress σ τ).mp hsem
    exact ⟨σ, ρ, κ, τ, h₁, (tail_head_spec R D hsup Q H hQ hH ρ κ).mp h₂, h₃⟩
  · rintro ⟨σ, ρ, κ, τ, h₁, h₂, h₃⟩
    exact ⟨σ, τ, (reachabilityPolicy_sem ingress H egress σ τ).mpr
      ⟨ρ, κ, h₁, (tail_head_spec R D hsup Q H hQ hH ρ κ).mpr h₂, h₃⟩⟩

------------------------------------------------------------------------
-- §4 The result type and the composed checking procedure
------------------------------------------------------------------------

/-- Result of the condition-(34) evaluation (initial isolation:
    `in · head(Init) · out ≡ 0`).

    The three outcomes are deliberately distinct:
    - `preprocessFailure`: preprocessing failed, so no condition of the
      pipeline was evaluated;
    - `headFailure`: preprocessing succeeded but `head(Init)` failed —
      the condition is not evaluable, and this is NOT the verdict
      "condition holds";
    - `isZero b`: the condition was successfully evaluated; it holds
      exactly when `b = true`. -/
inductive Cond34Result where
  | preprocessFailure : Cond34Result
  | headFailure : Cond34Result
  | isZero (b : Bool) : Cond34Result
  deriving DecidableEq, BEq, Repr

/-- Result of the condition-(35) evaluation (post-reconfiguration
    reachability: `in · head(tail(Init, R)) · out ≢ 0`).

    The four outcomes are deliberately distinct:
    - `preprocessFailure`: preprocessing failed;
    - `tailFailure`: preprocessing succeeded but `tail(Init, R)` failed —
      NOT the verdict "condition holds";
    - `tailHeadFailure`: `tail(Init, R)` succeeded but `head` of the
      extracted process failed — NOT the verdict "condition holds";
    - `nonzero b`: the condition was successfully evaluated; it holds
      exactly when `b = true`. -/
inductive Cond35Result where
  | preprocessFailure : Cond35Result
  | tailFailure : Cond35Result
  | tailHeadFailure : Cond35Result
  | nonzero (b : Bool) : Cond35Result
  deriving DecidableEq, BEq, Repr

/-- The formal checking result.  Conditions (34) and (35) are different
    properties — initial isolation versus post-reconfiguration
    reachability — and are preserved as separate results, exactly as the
    original tool reports each property separately.  Extraction failures
    are kept distinguishable from each other and from a successfully
    checked policy whose semantics is empty. -/
structure SafetyCheckResult where
  initialCondition : Cond34Result
  postReconfigurationCondition : Cond35Result
  deriving DecidableEq, BEq, Repr

/-- The paper's combined claim — "the packets at port ext can arrive at
    port int only after a proper reconfiguration on the channel
    secConReq" — as a derived conjunction of the two separately reported
    conditions.  This is a convenience accessor, not a replacement for
    the structured result: any extraction failure yields `false`, and
    the individual outcomes remain available in `SafetyCheckResult`. -/
def SafetyCheckResult.bothHold (r : SafetyCheckResult) : Bool :=
  decide (r.initialCondition = Cond34Result.isZero true ∧
    r.postReconfigurationCondition = Cond35Result.nonzero true)

/-- Characterization of the combined claim. -/
theorem bothHold_true_iff (r : SafetyCheckResult) :
    r.bothHold = true ↔
      (r.initialCondition = Cond34Result.isZero true ∧
        r.postReconfigurationCondition = Cond35Result.nonzero true) :=
  decide_eq_true_iff

/-- The composed checking procedure (S5B pipeline).

    Stage 1: preprocessing (S4B `preprocess` = restriction δ by the
    process's own communication actions).  Failure yields
    `preprocessFailure` on both conditions — never a zero verdict.

    Stage 2a: `head(q)` extraction for condition (34).  Failure yields
    `headFailure` — never a zero verdict.

    Stage 2b: `tail(R, q)` extraction followed by `head` of the extracted
    process for condition (35).  Failures at the two stages are
    distinguished (`tailFailure` vs `tailHeadFailure`) — never zero
    verdicts.

    Stage 3: the verified zero checker `netkatIsZero` decides both
    property policies. -/
def Internal.safetyCheck (env : RecEnv schema) (p : DyNetKAT schema) (R : ReconfigSet schema)
    (ingress egress : NetKAT schema) : SafetyCheckResult :=
  match preprocess env p with
  | none => ⟨.preprocessFailure, .preprocessFailure⟩
  | some q =>
      ⟨match checkCondition34 ingress egress q with
         | none => .headFailure
         | some b => .isZero b,
       match tail R q with
       | none => .tailFailure
       | some Q =>
           match head Q with
           | none => .tailHeadFailure
           | some H => .nonzero (!netkatIsZero (reachabilityPolicy ingress H egress))⟩

/-- Preprocessing failure yields the explicit failure result on both
    conditions. -/
theorem safetyCheck_preprocessFailure (env : RecEnv schema) (p : DyNetKAT schema) (R : ReconfigSet schema)
    (ingress egress : NetKAT schema) (h : preprocess env p = none) :
    Internal.safetyCheck env p R ingress egress =
      ⟨Cond34Result.preprocessFailure, Cond35Result.preprocessFailure⟩ := by
  simp only [Internal.safetyCheck, h]

------------------------------------------------------------------------
-- §5 End-to-end correctness on the supported fragment
------------------------------------------------------------------------

/-- End-to-end pipeline theorem (extraction level): under the S4B
    preprocessing conditions, preprocessing succeeds, both extractions
    succeed, and the composed procedure evaluates exactly the two
    verified zero checks of Eqs. (34)–(35) on the extracted policies. -/
theorem safetyCheck_supported (env : RecEnv schema) (p : DyNetKAT schema) (R : ReconfigSet schema)
    (ingress egress : NetKAT schema) (h : PreprocessingConditions env p) :
    ∃ q Q H₁ H₂,
      preprocess env p = some q ∧ head q = some H₁ ∧
      tail R q = some Q ∧ head Q = some H₂ ∧
      Internal.safetyCheck env p R ingress egress =
        ⟨Cond34Result.isZero (netkatIsZero (reachabilityPolicy ingress H₁ egress)),
         Cond35Result.nonzero
           (!netkatIsZero (reachabilityPolicy ingress H₂ egress))⟩ := by
  obtain ⟨q, Q, H₂, hq, hsupH, hsupT, hQ, hH₂⟩ := preprocess_head_tail_some env p R h
  obtain ⟨H₁, hH₁⟩ := head_supported_some q hsupH
  refine ⟨q, Q, H₁, H₂, hq, hH₁, hQ, hH₂, ?_⟩
  simp only [Internal.safetyCheck, hq, checkCondition34_some ingress egress q H₁ hH₁, hQ, hH₂]

/-- Constructor injectivity for the condition-(34) verdict. -/
theorem cond34Result_isZero_eq_true_iff {b : Bool} :
    Cond34Result.isZero b = Cond34Result.isZero true ↔ b = true := by
  cases b <;> simp

/-- Constructor injectivity for the condition-(35) verdict. -/
theorem cond35Result_nonzero_eq_true_iff {b : Bool} :
    Cond35Result.nonzero b = Cond35Result.nonzero true ↔ b = true := by
  cases b <;> simp

/-- End-to-end pipeline theorem (semantic level): under the S4B
    preprocessing conditions, the composed procedure succeeds, and its
    two verdicts carry exactly the semantic conditions established for
    Eqs. (34)–(35):

    - the initial-condition verdict is `true` exactly when NO packet
      pair `(ρ, κ)` of the initial configuration (`HeadSpec q`) composes
      with an ingress step before it and an egress step after it
      (absence of all corresponding relational transitions);

    - the post-reconfiguration verdict is `true` exactly when SOME packet
      pair `(ρ, κ)` of the post-reconfiguration configuration
      (`TailHeadSpec R q`) composes with an ingress step before it and an
      egress step after it (existence of at least one corresponding
      relational transition).

    This is a verified checker for the supported preprocessing fragment
    (δ-axiom fragment, S4B), not a claim of equivalence with the complete
    original DyNetiKAT tool. -/
theorem safetyCheck_pipeline_semantic (env : RecEnv schema) (p : DyNetKAT schema) (R : ReconfigSet schema)
    (ingress egress : NetKAT schema) (h : PreprocessingConditions env p) :
    ∃ q Q H₁ H₂,
      preprocess env p = some q ∧ head q = some H₁ ∧
      tail R q = some Q ∧ head Q = some H₂ ∧
      ((Internal.safetyCheck env p R ingress egress).initialCondition =
         Cond34Result.isZero true ↔
         ∀ σ ρ κ τ : schema.Packet,
           ¬ (Semantics ingress σ ρ ∧ HeadSpec q ρ κ ∧ Semantics egress κ τ)) ∧
      ((Internal.safetyCheck env p R ingress egress).postReconfigurationCondition =
         Cond35Result.nonzero true ↔
         ∃ σ ρ κ τ : schema.Packet,
           Semantics ingress σ ρ ∧ TailHeadSpec R q ρ κ ∧ Semantics egress κ τ) := by
  obtain ⟨q, Q, H₁, H₂, hq, hH₁, hQ, hH₂, hres⟩ :=
    safetyCheck_supported env p R ingress egress h
  obtain ⟨_, hsupT⟩ := preprocess_tail_supported env p q hq
  have hsupH : HeadSupported q := TailSupported.headSupported q hsupT
  refine ⟨q, Q, H₁, H₂, hq, hH₁, hQ, hH₂, ?_, ?_⟩
  · simp only [hres, cond34Result_isZero_eq_true_iff]
    exact checkCondition34_headSpec ingress egress q hsupH H₁ hH₁ _
      (checkCondition34_some ingress egress q H₁ hH₁)
  · simp only [hres, cond35Result_nonzero_eq_true_iff]
    exact checkCondition35_tailHeadSpec ingress egress R q hsupT Q H₂ hQ hH₂ _
      (checkCondition35_some ingress egress R q Q H₂ hQ hH₂)

/-! ## Verification on closed graphs in the head/tail fragment -/

/-- Check equations (34) and (35) on the graph supplied to the paper's
    head and tail operators. Each failed extraction has its own result. -/
def Internal.safetyCheckGraph (G : ProcessGraph schema) (R : ReconfigSet schema)
    (ingress egress : NetKAT schema) : SafetyCheckResult :=
  ⟨match graphHead G with
   | none => .headFailure
   | some H => .isZero (netkatIsZero (reachabilityPolicy ingress H egress)),
   match graphTail G R with
   | none => .tailFailure
   | some T =>
       match graphHead T with
       | none => .tailHeadFailure
       | some H => .nonzero (!netkatIsZero (reachabilityPolicy ingress H egress))⟩

/-- A packet flow through the selected graph configuration, from ingress
    through a head or tail contribution to egress. -/
def flowVia {schema : PacketSchema} (ingress egress : NetKAT schema)
    (config : schema.Packet → schema.Packet → Prop) : Prop :=
  ∃ σ ρ κ τ, Semantics ingress σ ρ ∧ config ρ κ ∧ Semantics egress κ τ

private theorem flowVia_semantics (ingress H egress : NetKAT schema) :
    flowVia ingress egress (Semantics H) ↔
      ∃ σ τ, Semantics (reachabilityPolicy ingress H egress) σ τ := by
  constructor
  · rintro ⟨σ, ρ, κ, τ, hIn, hCore, hOut⟩
    exact ⟨σ, τ, (reachabilityPolicy_sem ingress H egress σ τ).mpr
      ⟨ρ, κ, hIn, hCore, hOut⟩⟩
  · rintro ⟨σ, τ, h⟩
    obtain ⟨ρ, κ, hIn, hCore, hOut⟩ := (reachabilityPolicy_sem ingress H egress σ τ).mp h
    exact ⟨σ, ρ, κ, τ, hIn, hCore, hOut⟩

/-- Condition (34) is exact whenever initial-head extraction succeeds. -/
theorem safetyCheckGraph_initial_correct {G : ProcessGraph schema} {R : ReconfigSet schema}
    {ingress egress H : NetKAT schema} (hHead : graphHead G = some H) :
    (Internal.safetyCheckGraph G R ingress egress).initialCondition = .isZero true ↔
      ¬ flowVia ingress egress (GraphHeadSpec G G.root) := by
  have hSem : Semantics H = GraphHeadSpec G G.root := by
    funext σ τ
    exact propext ⟨graphHead_sound G H hHead σ τ, graphHead_complete G H hHead σ τ⟩
  simp only [Internal.safetyCheckGraph, hHead, Cond34Result.isZero.injEq, netkatIsZero_correct,
    ← hSem, flowVia_semantics, not_exists]

/-- Condition (35) is exact whenever tail and head-of-tail extraction succeed. -/
theorem safetyCheckGraph_post_correct {G T : ProcessGraph schema} {R : ReconfigSet schema}
    {ingress egress H : NetKAT schema} (hTail : graphTail G R = some T)
    (hHead : graphHead T = some H) :
    (Internal.safetyCheckGraph G R ingress egress).postReconfigurationCondition = .nonzero true ↔
      flowVia ingress egress (GraphTailSpec G R G.root) := by
  have hSem : Semantics H = GraphTailSpec G R G.root := by
    funext σ τ
    exact propext ⟨graphTail_sound hTail hHead, graphTail_complete hTail hHead⟩
  simp only [Internal.safetyCheckGraph, hTail, hHead, Cond35Result.nonzero.injEq,
    Bool.not_eq_true', netkatIsZero_reachabilityPolicy_false_iff, ← hSem, flowVia]

/-- On the supported domain the graph checker evaluates both conditions.
    The relational specifications give their exact truth values. -/
theorem safetyCheckGraph_correct (G : ProcessGraph schema) (R : ReconfigSet schema)
    (ingress egress : NetKAT schema) (hHead : GraphHeadSupported G) (hTail : GraphTailDomain G R) :
    ∃ H₁ T H₂, graphHead G = some H₁ ∧ graphTail G R = some T ∧ graphHead T = some H₂ ∧
      ((Internal.safetyCheckGraph G R ingress egress).initialCondition = .isZero true ↔
        ¬ flowVia ingress egress (GraphHeadSpec G G.root)) ∧
      ((Internal.safetyCheckGraph G R ingress egress).postReconfigurationCondition = .nonzero true ↔
        flowVia ingress egress (GraphTailSpec G R G.root)) := by
  obtain ⟨H₁, h₁⟩ := graphHead_supported_some G hHead
  obtain ⟨T, hT⟩ := graphTail_domain_some hTail
  obtain ⟨H₂, h₂⟩ := graphTail_head_some hT
  exact ⟨H₁, T, H₂, h₁, hT, h₂, safetyCheckGraph_initial_correct h₁,
    safetyCheckGraph_post_correct hT h₂⟩

/-- Frontend checks that must succeed before a closed graph is available. -/
inductive GraphInputError where
  | invalidGraph
  | compilationFailed
  deriving DecidableEq, BEq, Repr

/-- Validate closure when the graph arrives as raw nodes and labels. -/
def validateProcessGraph (nodes : Finset NodeId) (root : GProc schema) (label : NodeId → GProc schema) :
    Except GraphInputError (ProcessGraph schema) :=
  if hRoot : gprocRefs root ⊆ nodes then
    if hLabels : ∀ i ∈ nodes, gprocRefs (label i) ⊆ nodes then
      .ok ⟨nodes, root, label, hRoot, hLabels⟩
    else .error .invalidGraph
  else .error .invalidGraph

theorem validateProcessGraph_invalid_iff (nodes : Finset NodeId) (root : GProc schema)
    (label : NodeId → GProc schema) :
    validateProcessGraph nodes root label = .error .invalidGraph ↔
      ¬ (gprocRefs root ⊆ nodes ∧ ∀ i ∈ nodes, gprocRefs (label i) ⊆ nodes) := by
  unfold validateProcessGraph
  split
  · split <;> simp_all
  · simp_all

theorem preprocessGraph_supported {G Q : ProcessGraph schema} (h : preprocessGraph G = some Q) :
    GraphHeadSupported Q ∧ GraphTailSupported Q :=
  let ready := preprocessGraph_traceReady h
  graphSupported_of_shapes ready.root.shape (fun i hi => (ready.label i hi).shape)

/-- Check the graph under restriction of all communication actions. If
    restriction cannot be eliminated in the sequential fragment, both
    conditions report preprocessing failure. -/
def Internal.safetyCheckRestrictedGraph (G : ProcessGraph schema) (R : ReconfigSet schema)
    (ingress egress : NetKAT schema) : SafetyCheckResult :=
  match preprocessGraph G with
  | none => ⟨.preprocessFailure, .preprocessFailure⟩
  | some Q => Internal.safetyCheckGraph Q R ingress egress

theorem safetyCheckRestrictedGraph_correct {G Q : ProcessGraph schema} {R : ReconfigSet schema}
    {ingress egress : NetKAT schema} (h : preprocessGraph G = some Q) :
    ∃ H₁ T H₂, graphHead Q = some H₁ ∧ graphTail Q R = some T ∧ graphHead T = some H₂ ∧
      ((Internal.safetyCheckRestrictedGraph G R ingress egress).initialCondition = .isZero true ↔
        ¬ flowVia ingress egress (GraphHeadSpec Q Q.root)) ∧
      ((Internal.safetyCheckRestrictedGraph G R ingress egress).postReconfigurationCondition =
        .nonzero true ↔ flowVia ingress egress (GraphTailSpec Q R Q.root)) := by
  obtain ⟨hHead, hTail⟩ := preprocessGraph_supported h
  simpa only [Internal.safetyCheckRestrictedGraph, h] using
    safetyCheckGraph_correct Q R ingress egress hHead (graphTailSupported_implies_domain hTail)

/-- Resolve recursion once, then restrict and verify the closed graph. -/
def Internal.compileAndSafetyCheckGraph (env : RecEnv schema) (p : DyNetKAT schema) (support : Finset Var)
    (R : ReconfigSet schema) (ingress egress : NetKAT schema) : Except GraphInputError SafetyCheckResult :=
  match compileGraph env p support with
  | none => .error .compilationFailed
  | some G => .ok (Internal.safetyCheckRestrictedGraph G R ingress egress)

/-- Successful frontend compilation relates the root to the original SOS.
    After restriction elimination the result decides (34) and (35). -/
theorem Internal.compileAndSafetyCheckGraph_correct {env : RecEnv schema} {p : DyNetKAT schema}
    {support : Finset Var} {G Q : ProcessGraph schema} (hCompile : compileGraph env p support = some G)
    {R : ReconfigSet schema} {ingress egress : NetKAT schema}
    (hPrep : preprocessGraph G = some Q) :
    Corr G env p G.root ∧
      ∃ result, Internal.compileAndSafetyCheckGraph env p support R ingress egress = .ok result ∧
        (result.initialCondition = .isZero true ↔
          ¬ flowVia ingress egress (GraphHeadSpec Q Q.root)) ∧
        (result.postReconfigurationCondition = .nonzero true ↔
          flowVia ingress egress (GraphTailSpec Q R Q.root)) := by
  obtain ⟨_, _, _, _, _, _, hInitial, hPost⟩ :=
    safetyCheckRestrictedGraph_correct (R := R) (ingress := ingress) (egress := egress) hPrep
  exact ⟨compileGraph_corr hCompile, Internal.safetyCheckRestrictedGraph G R ingress egress,
    by simp only [Internal.compileAndSafetyCheckGraph, hCompile], hInitial, hPost⟩

end DyNetKAT.DyNetKAT
