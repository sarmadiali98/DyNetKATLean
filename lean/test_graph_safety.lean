import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.GraphSafetyTests

open DyNetKAT.NetKAT

private def enter := NetKAT.fieldTest .port .v0
private def leave := NetKAT.fieldTest .port .v1
private def allow := NetKAT.seq enter (.assign1 .port .v1)
private def reverse := NetKAT.seq leave (.assign1 .port .v0)

-- Restricted normal-form representation of the firewall in the paper:
-- the two graph nodes represent its closed and open controller states.
private def closedBody : DyNetKAT :=
  .choice (.nSeq reverse (.var "closed")) (.rcfgPrefix "secConReq" .id (.var "open"))

private def openBody : DyNetKAT :=
  .choice (.nSeq allow (.var "open")) (.rcfgPrefix "secConEnd" .id (.var "closed"))

private def firewall : RecEnv :=
  (RecEnv.empty.define "closed" closedBody).define "open" openBody

private def support : Finset Var := {"closed", "open"}
private def req : ReconfigSet := {("secConReq", .id)}
private def wrong : ReconfigSet := {("secConReq", .drop)}

private def check (R : ReconfigSet) (S : Finset Var) :=
  compileAndSafetyCheckGraph firewall (.var "closed") S R enter leave

#guard match check req support with
  | .ok result => result.bothHold
  | .error _ => false

#guard match check wrong support with
  | .ok ⟨.isZero true, .nonzero false⟩ => true
  | _ => false

#guard match check req {"closed"} with
  | .error .compilationFailed => true
  | _ => false

#guard (compileGraph RecEnv.empty (.var "missing") {"missing"}).isNone
#guard (compileGraph infEnv (.var "X") {"X", "X0"}).isNone

#guard match validateProcessGraph ∅ (.ref (varNode "missing")) (fun _ => .deadlock) with
  | .error .invalidGraph => true
  | _ => false

#guard match validateProcessGraph {varNode "X"} (.ref (varNode "X"))
    (fun _ => .ref (varNode "missing")) with
  | .error .invalidGraph => true
  | _ => false

private def unsupported : DyNetKAT := .parallel .deadlock .deadlock

#guard match compileAndSafetyCheckGraph RecEnv.empty unsupported ∅ req enter leave with
  | .ok ⟨.preprocessFailure, .preprocessFailure⟩ => true
  | _ => false

#guard match compileGraph RecEnv.empty unsupported ∅ with
  | some G =>
      safetyCheckGraph G req enter leave == ⟨.headFailure, .tailFailure⟩
  | _ => false

-- A solo send is blocked under δ, including one in a recursive label.
private def sendingBody : DyNetKAT :=
  .choice (.send "ctrl" .id (.nSeq allow (.var "S")))
    (.rcfgPrefix "secConReq" .id (.nSeq allow (.var "S")))

#guard match compileAndSafetyCheckGraph (RecEnv.empty.define "S" sendingBody)
    (.var "S") {"S"} req enter leave with
  | .ok ⟨.isZero true, .nonzero true⟩ => true
  | _ => false

private def loop : DyNetKAT :=
  .choice (.nSeq allow (.var "X")) (.rcfgPrefix "a" .id (.var "X"))

-- The same recursive label contributes the initial and post-event policies.
#guard match compileAndSafetyCheckGraph (RecEnv.empty.define "X" loop)
    (.var "X") {"X"} {("a", .id)} enter leave with
  | .ok ⟨.isZero false, .nonzero true⟩ => true
  | _ => false

private def cycle : DyNetKAT :=
  .rcfgPrefix "a" .id
    (.nSeq allow (.rcfgPrefix "b" .id (.nSeq reverse (.var "X"))))

private def tailPolicies (R : ReconfigSet) (expected : NetKAT) : Bool :=
  match (compileGraph (RecEnv.empty.define "X" cycle) (.var "X") {"X"}).bind
      (fun G => (graphTail G R).bind graphHead) with
  | some H => netkatEquiv H expected
  | none => false

#guard tailPolicies {("a", .id), ("b", .id)} (.union allow reverse)
#guard tailPolicies {("a", .id)} allow
#guard tailPolicies {("b", .id)} .drop

#guard match (graphTail exUnguardedGraph ∅).bind graphHead with
  | some H => netkatIsZero H
  | none => false

-- Figure 5 before restriction and normalization.
private def rawHost : DyNetKAT :=
  .choice (.send "secConReq" .id (.var "Host")) (.send "secConEnd" .id (.var "Host"))

private def rawClosed : DyNetKAT :=
  .choice (.nSeq reverse (.var "Switch"))
    (.choice (.nSeq (.seq enter .drop) (.var "Switch"))
      (.recv "secConReq" .id (.var "SwitchOpen")))

private def rawOpen : DyNetKAT :=
  .choice (.nSeq reverse (.var "SwitchOpen"))
    (.choice (.nSeq allow (.var "SwitchOpen")) (.recv "secConEnd" .id (.var "Switch")))

private def rawFirewall : RecEnv :=
  ((RecEnv.empty.define "Host" rawHost).define "Switch" rawClosed).define "SwitchOpen" rawOpen

private def rawInit : DyNetKAT := .parallel (.var "Host") (.var "Switch")
private def rawSupport : Finset Var := {"Host", "Switch", "SwitchOpen"}

private def rawFirewallCandidate : NormalizationCandidate 1 where
  referenceOrder := [varNode "Host", varNode "Switch", varNode "SwitchOpen"]
  state i := .parallel (.ref (varNode "Host"))
    (.ref (varNode (if i = 0 then "Switch" else "SwitchOpen")))
  moves i := if i = 0 then
    [(.packet reverse, 0), (.rcfg "secConReq" .id, 1)]
    else [(.packet reverse, 1), (.packet allow, 1), (.rcfg "secConEnd" .id, 0)]

private theorem rawSupported : FiniteSupport rawFirewall rawInit rawSupport := by
  refine ⟨by simp [rawInit, rawSupport, recursiveVars, Finset.union_subset_iff], ?_⟩
  intro x hx
  simp only [rawSupport, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;>
    simp [rawFirewall, RecEnv.lookup, RecEnv.define, rawHost, rawClosed, rawOpen,
      rawSupport, recursiveVars, Finset.union_subset_iff]

private def rawGraph := toGraph rawFirewall rawInit rawSupport rawSupported

private theorem finTwo (i : Fin 2) : i = 0 ∨ i = 1 := by
  by_cases h : i = 0
  · exact Or.inl h
  · exact Or.inr (Fin.eq_one_of_ne_zero i h)

private theorem forward_nonzero (f g : FieldValueEnum) :
    netkatIsZero (.seq (.fieldTest .port f) (.assign1 .port g)) = false := by
  apply (netkatIsZero_false_iff_exists _).mpr
  let σ : CtxPkt := fun _ => f
  exact ⟨σ, Packet.update σ .port g, σ, (fieldTest_sem ..).mpr ⟨rfl, rfl⟩,
    (assign1_sem ..).mpr rfl⟩

private theorem drop_zero : netkatIsZero (.seq enter .drop) = true :=
  (netkatIsZero_correct _).mpr (seq_drop_right enter)

private def closedState : GProc := rawFirewallCandidate.state 0
private def openState : GProc := rawFirewallCandidate.state 1

private def closedRow : List SymbolicMove :=
  [(.send "secConReq" .id, closedState), (.send "secConEnd" .id, closedState),
   (.visible (.packet reverse), closedState), (.visible (.packet (.seq enter .drop)), closedState),
   (.recv "secConReq" .id, openState), (.visible (.rcfg "secConReq" .id), openState)]

private def openRow : List SymbolicMove :=
  [(.send "secConReq" .id, openState), (.send "secConEnd" .id, openState),
   (.visible (.packet reverse), openState), (.visible (.packet allow), openState),
   (.recv "secConEnd" .id, closedState), (.visible (.rcfg "secConEnd" .id), closedState)]

private def rawRows : ReferenceRows :=
  [(varNode "SwitchOpen", [(.visible (.packet reverse), .ref (varNode "SwitchOpen")),
      (.visible (.packet allow), .ref (varNode "SwitchOpen")),
      (.recv "secConEnd" .id, .ref (varNode "Switch"))]),
   (varNode "Switch", [(.visible (.packet reverse), .ref (varNode "Switch")),
      (.visible (.packet (.seq enter .drop)), .ref (varNode "Switch")),
      (.recv "secConReq" .id, .ref (varNode "SwitchOpen"))]),
   (varNode "Host", [(.send "secConReq" .id, .ref (varNode "Host")),
      (.send "secConEnd" .id, .ref (varNode "Host"))])]

private theorem rawRowsBuilt :
    buildReferenceRows rawGraph rawFirewallCandidate.referenceOrder [] = some rawRows := by
  simp [rawGraph, rawFirewallCandidate, rawRows, buildReferenceRows, localMoves,
    rawSupport, rawFirewall, RecEnv.lookup, RecEnv.define, rawHost, rawClosed, rawOpen, toGProc]

private theorem rawRefExact (i : NodeId) (row : List SymbolicMove)
    (h : referenceMoves rawRows i = some row) : MovesExact rawGraph (.ref i) row :=
  buildReferenceRows_exact rawRowsBuilt (by simp [referenceMoves]) i row h

private theorem closedRowExact : MovesExact rawGraph closedState closedRow :=
  localMoves_exact rawRefExact rfl

private theorem openRowExact : MovesExact rawGraph openState openRow :=
  localMoves_exact rawRefExact rfl

-- The one-step oracle preserves the firewall handshake under the outer block
-- without consulting a derivative certificate.
example : guardedMoves rawGraph (.restrict Set.univ rawGraph.root)
    (some (fun _ _ => true)) (fun _ => some (fun _ _ => false)) =
    some [(.visible (.packet reverse), .restrict Set.univ closedState),
      (.visible (.packet (.seq enter .drop)), .restrict Set.univ closedState),
      (.visible (.rcfg "secConReq" .id), .restrict Set.univ openState)] := by
  rw [show rawGraph.root = toGProc rawInit from rfl]
  have hh : rawGraph.label (varNode "Host") = toGProc rawHost := by
    rw [rawGraph, toGraph_label_varNode rawSupported (by simp [rawSupport])]
    rfl
  have hs : rawGraph.label (varNode "Switch") = toGProc rawClosed := by
    rw [rawGraph, toGraph_label_varNode rawSupported (by simp [rawSupport])]
    rfl
  simp only [guardedMoves, localMoves, rawInit, toGProc, hh, hs,
    rawHost, rawClosed, Option.some_bind]
  rfl

private def firewallChecks : RestrictionChecks := fun _ _ => false

private theorem firewallProjectionBodies (x : Var) (hx : ReachableVar rawFirewall rawInit x) :
    ∃ b, rawFirewall.lookup x = some b ∧ GuardedOccurrences b ∧
      AllRestrictionChecksCorrect (toGProc b) firewallChecks := by
  have hm := reachableVars_subset_of_finiteSupport rawFirewall rawInit rawSupport rawSupported x hx
  simp only [rawSupport, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact ⟨rawHost, rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  · exact ⟨rawClosed, rfl, ⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩
  · exact ⟨rawOpen, rfl, ⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩

private theorem firewallProjectionWellFormed : WellFormed rawFirewall rawInit := by
  constructor
  · intro x hx
    obtain ⟨b, he, _, _⟩ := firewallProjectionBodies x hx
    simp [he]
  · intro x hx
    obtain ⟨b, he, hg, _⟩ := firewallProjectionBodies x hx
    exact ⟨b, he, hg⟩

private def firewallDependencies :=
  DependencyGraph.build rawFirewall rawInit rawSupport rawSupported

#guard firewallDependencies.nodes.card == 3
#guard firewallDependencies.entries == {"Host", "Switch"}
#guard firewallDependencies.edges == {("Host", "Host"), ("Switch", "Switch"),
  ("Switch", "SwitchOpen"), ("SwitchOpen", "Switch"), ("SwitchOpen", "SwitchOpen")}
#guard firewallDependencies.sccs == {{"Host"}, {"Switch", "SwitchOpen"}}
#guard firewallDependencies.cyclicSccs == firewallDependencies.sccs
#guard firewallDependencies.condensationEdges == ∅

example {C : Finset Var} (hC : C ∈ firewallDependencies.sccs) {x : Var} (hx : x ∈ C) :
    ∃ b, rawFirewall.lookup x = some b ∧ TypedPaperGuarded b := by
  unfold firewallDependencies at hC
  exact DependencyGraph.guarded_scc (env := rawFirewall) (root := rawInit) (S := rawSupport)
    (C := C) (x := x) rawSupported firewallProjectionWellFormed hC hx

private theorem firewall_typed_guarded_bodies :
    WellFormed rawFirewall rawInit ∧ TypedPaperGuarded rawHost ∧
      TypedPaperGuarded rawClosed ∧ ¬ TypedPaperGuarded rawInit := by
  have typed := (wellFormed_iff_closedDefined_and_typedPaperGuarded ..).mp
    firewallProjectionWellFormed
  exact ⟨firewallProjectionWellFormed,
    typed.2 "Host" rawHost (.direct (by simp [rawInit, recursiveVars])) rfl,
    typed.2 "Switch" rawClosed (.direct (by simp [rawInit, recursiveVars])) rfl,
    fun h => h "Host" (.parallelLeft .here)⟩

#print axioms firewall_typed_guarded_bodies

-- The original Figure 5 process has a derivable head form with a
-- secConReq branch even though its outer restriction blocks every send/receive.
example : ∃ xs : HeadNormalForm,
    DerivesNoAIP rawFirewall (.restrict Set.univ rawInit) xs.render ∧
      ∃ b ∈ xs, b.label.Realizes [] [] (.rcfg "secConReq" .id) [] [] := by
  have reach (x : Var) (h : ReachableVar rawFirewall (.restrict Set.univ rawInit) x) :
      ReachableVar rawFirewall rawInit x := by
    induction h with
    | direct h => exact .direct h
    | throughDefinition _ he hm ih => exact .throughDefinition ih he hm
  have wf : WellFormed rawFirewall (.restrict Set.univ rawInit) :=
    ⟨fun x hx => firewallProjectionWellFormed.1 x (reach x hx),
     fun x hx => firewallProjectionWellFormed.2 x (reach x hx)⟩
  obtain ⟨xs, eqn⟩ := wf.exists_headNormalForm
  refine ⟨xs, eqn, ?_⟩
  have source : Step rawFirewall ⟨.restrict Set.univ rawInit, [], []⟩
      (.rcfg "secConReq" .id)
      ⟨.restrict Set.univ (.parallel (.var "Host") (.var "SwitchOpen")), [], []⟩ := by
    refine .cpol_restrict _ _ _ _ _ _ _ _ trivial ?_
    refine .cpol_sync_send_recv _ _ _ _ _ _ _ _ ?_ ?_
    · exact .cpol_var _ rawHost _ _ _ _ _ _ rfl
        (.cpol_choice_l _ _ _ _ _ _ _ _ (.cpol_send _ _ _ _ _))
    · exact .cpol_var _ rawClosed _ _ _ _ _ _ rfl
        (.cpol_choice_r _ _ _ _ _ _ _ _ (.cpol_choice_r _ _ _ _ _ _ _ _
          (.cpol_recv _ _ _ _ _)))
  obtain ⟨R, hR, hr⟩ := eqn.sound
  obtain ⟨q, hs, _⟩ := hR.2 _ _ hr _ _ _ _ _ _ source
  obtain ⟨b, hb, _, realizes⟩ := (HeadNormalForm.step_iff rawFirewall xs ..).mp hs
  exact ⟨b, hb, realizes⟩

private def firewallProjectionState : CheckedResidual :=
  (CheckedResidual.mk rawGraph.root firewallChecks).restrict Set.univ (fun _ => true)

theorem firewall_projection (n : Nat) : ∃ q,
    renderProjection rawGraph (fun _ => firewallChecks) n firewallProjectionState = some q ∧
      Bisimilar rawFirewall q (.restrict Set.univ (.project n rawInit)) := by
  apply renderProjection_restricted rawSupported firewallProjectionWellFormed firewallChecks
    (fun _ => firewallChecks) ⟨trivial, trivial⟩ _ Set.univ (fun _ => true) (by simp)
  intro x b hx he
  obtain ⟨b', he', _, hc⟩ := firewallProjectionBodies x hx
  rw [he] at he'
  cases he'
  exact hc

theorem firewall_memo_projection (n : Nat) : ∃ q stats,
    renderProjectionMemo rawGraph (fun _ => firewallChecks) n firewallProjectionState =
      some (q, stats) ∧ Bisimilar rawFirewall q (.restrict Set.univ (.project n rawInit)) := by
  obtain ⟨q, he, bis⟩ := firewall_projection n
  rw [← renderProjectionMemo_eq] at he
  obtain ⟨⟨_, stats⟩, hm, rfl⟩ := Option.map_eq_some'.mp he
  exact ⟨_, stats, hm, bis⟩

private def firewallMemo (n : Nat) :=
  renderProjectionMemo rawGraph (fun _ => firewallChecks) n firewallProjectionState

#guard (firewallMemo 1).map Prod.snd == some ⟨0, 4, 0⟩
#guard (firewallMemo 2).map Prod.snd == some ⟨0, 13, 0⟩

-- The original firewall's first handshake survives at the cutoff.
private theorem firewall_cutoff :
    renderProjection rawGraph (fun _ => firewallChecks) 1 firewallProjectionState =
    some (choiceOf [.nSeq reverse .deadlock, .nSeq (.seq enter .drop) .deadlock,
      .rcfgPrefix "secConReq" .id .deadlock]) := by
  have hh : rawGraph.label (varNode "Host") = toGProc rawHost := by
    rw [rawGraph, toGraph_label_varNode rawSupported (by simp [rawSupport])]
    rfl
  have hs : rawGraph.label (varNode "Switch") = toGProc rawClosed := by
    rw [rawGraph, toGraph_label_varNode rawSupported (by simp [rawSupport])]
    rfl
  simp only [renderProjection, checkedMoves, firewallProjectionState, CheckedResidual.restrict,
    show rawGraph.root = toGProc rawInit from rfl, rawInit, toGProc, localCheckedMoves,
    hh, hs, rawHost, rawClosed]
  rfl

example : (firewallMemo 1).map Prod.fst =
    some (choiceOf [.nSeq reverse .deadlock, .nSeq (.seq enter .drop) .deadlock,
      .rcfgPrefix "secConReq" .id .deadlock]) := by
  rw [firewallMemo, renderProjectionMemo_eq]
  exact firewall_cutoff

#guard (renderProjection rawGraph (fun _ => firewallChecks) 2 firewallProjectionState).isSome

-- Even the unrestricted process has exactly these two derivatives. The
-- extra send/receive steps return to one of the same states.
private theorem rawUnrestrictedStepClosed {c d : GConfig} {a : Action}
    (h : GStep rawGraph c a d) :
    (c.proc = closedState ∨ c.proc = openState) →
      d.proc = closedState ∨ d.proc = openState := by
  rcases c with ⟨p, pt, hl⟩
  rcases d with ⟨q, pt', hl'⟩
  rintro (rfl | rfl)
  · obtain ⟨l, hm, _⟩ := (closedRowExact ..).mp h
    simp only [closedRow, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      first | exact Or.inl rfl | exact Or.inr rfl
  · obtain ⟨l, hm, _⟩ := (openRowExact ..).mp h
    simp only [openRow, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      first | exact Or.inl rfl | exact Or.inr rfl

theorem rawFirewall_unrestricted_derivatives (p : GProc) :
    (∃ pt hl acts pt' hl', GSteps rawGraph ⟨rawGraph.root, pt, hl⟩ acts ⟨p, pt', hl'⟩) ↔
      p = closedState ∨ p = openState := by
  constructor
  · rintro ⟨pt, hl, acts, pt', hl', ht⟩
    have inv {c d : GConfig} {acts} (h : GSteps rawGraph c acts d) :
        (c.proc = closedState ∨ c.proc = openState) →
          d.proc = closedState ∨ d.proc = openState := by
      induction h with
      | nil => exact id
      | cons _ _ _ _ _ hs _ ih => exact fun h => ih (rawUnrestrictedStepClosed hs h)
    exact inv ht (Or.inl rfl)
  · rintro (rfl | rfl)
    · exact ⟨[], [], [], [], [], .nil _⟩
    · refine ⟨[], [], [.rcfg "secConReq" .id], [], [], .cons _ _ _ _ _ ?_ (.nil _)⟩
      exact (closedRowExact [] [] (.rcfg "secConReq" .id) openState [] []).mpr
        ⟨_, by simp [closedRow], .rcfg⟩

private theorem rawCertificateAccepted : checkNormalization rawGraph rawFirewallCandidate = true := by
  apply checkNormalization_of_rows (refs := rawRows)
  · exact rawRowsBuilt
  · rfl
  · intro i
    rcases finTwo i with rfl | rfl <;> rfl
  · intro i
    rcases finTwo i with rfl | rfl
    · refine ⟨closedRow, rfl, ?_⟩
      simp [closedRow, observableMove, SequentialLabel.enabled, drop_zero, reverse, leave,
        forward_nonzero, rawFirewallCandidate, closedState, openState]
    · refine ⟨openRow, rfl, ?_⟩
      simp [openRow, observableMove, SequentialLabel.enabled, reverse, leave, allow, enter,
        forward_nonzero, rawFirewallCandidate, closedState, openState]
  · intro i
    rcases finTwo i with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨0, .rcfg "secConReq" .id, by decide, by simp [rawFirewallCandidate]⟩

#guard checkNormalization rawGraph rawFirewallCandidate

example : HasFiniteDerivatives rawGraph := checkNormalization_finite rawCertificateAccepted

example (p : GProc) :
    ReachableDerivative rawGraph p ↔
      p = rawFirewallCandidate.state 0 ∨ p = rawFirewallCandidate.state 1 := by
  have h := (checkNormalization_sound rawCertificateAccepted).derivativeClosure.mem_iff p
  rw [← h]
  constructor
  · rintro ⟨i, rfl⟩
    rcases finTwo i with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

example (i : Fin 2) :
    ∃ pt acts hl, GSteps rawGraph ⟨.restrict Set.univ rawGraph.root, pt, []⟩ acts
      ⟨.restrict Set.univ (rawFirewallCandidate.state i), [], hl⟩ :=
  (checkNormalization_sound rawCertificateAccepted).reachesTrace i

private def rawCheck (R : ReconfigSet) :=
  compileNormalizeAndSafetyCheckGraph rawFirewall rawInit rawSupport rawFirewallCandidate R enter leave

private def verdictsAgree (R : ReconfigSet) : Bool :=
  match rawCheck R, check R support with
  | .ok a, .ok b => a == b
  | _, _ => false

#guard verdictsAgree req
#guard verdictsAgree wrong
#guard match rawCheck req with
  | .ok ⟨.isZero true, .nonzero true⟩ => true
  | _ => false

-- Missing, fabricated and redirected transitions each invalidate a row.
private def missingSync : NormalizationCandidate 1 :=
  { rawFirewallCandidate with moves := fun i => if i = 0 then [(.packet reverse, 0)]
      else rawFirewallCandidate.moves i }

private def fabricatedSync : NormalizationCandidate 1 :=
  { rawFirewallCandidate with moves := fun i =>
      (.rcfg "unmatched" .id, i) :: rawFirewallCandidate.moves i }

private def redirectedSync : NormalizationCandidate 1 :=
  { rawFirewallCandidate with moves := fun i => if i = 0 then
      [(.packet reverse, 0), (.rcfg "secConReq" .id, 0)] else rawFirewallCandidate.moves i }

#guard match normalizeGraph rawGraph missingSync with
  | .error .invalidCertificate => true
  | _ => false
#guard !(checkNormalization rawGraph fabricatedSync)
#guard !(checkNormalization rawGraph redirectedSync)
#guard !(checkNormalization rawGraph { rawFirewallCandidate with referenceOrder := [] })

-- A closed table with two identical deadlocks would have an unreachable index.
private def duplicateDeadlocks : NormalizationCandidate 1 := ⟨[], fun _ => .deadlock, fun _ => []⟩
#guard !(checkNormalization (toGraph RecEnv.empty .deadlock ∅ (by decide)) duplicateDeadlocks)

-- Both interleavings retain the other operand until it takes its step.
private def packetParallel : DyNetKAT :=
  .parallel (.nSeq .id .deadlock) (.nSeq allow .deadlock)

private def packetParallelGraph : ProcessGraph :=
  toGraph RecEnv.empty packetParallel ∅ (by simp [FiniteSupport, packetParallel, recursiveVars])

private def packetParallelCandidate : NormalizationCandidate 3 where
  referenceOrder := []
  state i := match i.val with
    | 0 => toGProc packetParallel
    | 1 => .parallel .deadlock (.nSeq allow .deadlock)
    | 2 => .parallel (.nSeq .id .deadlock) .deadlock
    | _ => .parallel .deadlock .deadlock
  moves i := match i.val with
    | 0 => [(.packet .id, 1), (.packet allow, 2)]
    | 1 => [(.packet allow, 3)]
    | 2 => [(.packet .id, 3)]
    | _ => []

#guard checkNormalization packetParallelGraph packetParallelCandidate
#guard !(checkNormalization packetParallelGraph
  { packetParallelCandidate with moves := fun i =>
      if i = 1 then [] else packetParallelCandidate.moves i })

#print axioms localMoves_exact
#print axioms buildReferenceRows_exact
#print axioms reachableDerivative_iff_trace
#print axioms hasFiniteDerivatives_iff
#print axioms rawFirewall_unrestricted_derivatives
#print axioms rawCertificateAccepted
#print axioms checkNormalization_sound
#print axioms checkNormalization_finite
#print axioms NormalizationExact.reachesTrace
#print axioms normalizeGraph_correct
#print axioms normalizeAndSafetyCheckGraph_correct
#print axioms compileNormalizeAndSafetyCheckGraph_correct
#print axioms GraphMatches.traces
#print axioms graphBisimilarBetween_same

#print axioms compileGraph_eq_some_iff
#print axioms compileGraph_eq_none_iff
#print axioms compileGraph_corr
#print axioms GStep.closed
#print axioms graph_step_iff
#print axioms gbisimilar_isGBisimulation
#print axioms GBisimilar.trans
#print axioms gbisimilar_iff_bisimilar
#print axioms compileGraph_bisimilar_iff
#print axioms graphHeadSpec_agree
#print axioms graphTail_bridge
#print axioms graphTail_sound
#print axioms graphTail_complete
#print axioms graphTail_spec_iff
#print axioms safetyCheckGraph_initial_correct
#print axioms safetyCheckGraph_post_correct
#print axioms safetyCheckGraph_correct
#print axioms validateProcessGraph_invalid_iff
#print axioms preprocessGraph_eq_some
#print axioms preprocessGraph_bisimulation
#print axioms preprocessGraph_supported
#print axioms safetyCheckRestrictedGraph_correct
#print axioms compileAndSafetyCheckGraph_correct
#print axioms execute_correct
#print axioms ctxPkt_card
#print axioms eval_correct
#print axioms execute_star_correct
#print axioms execute_star_eq_boundedStar
#print axioms netkatIsZero_correct
#print axioms netkatEquiv_correct
#print axioms execute_history_correct
#print axioms netkatEquiv_history_correct
#print axioms netkatIsZero_history_correct
#print axioms completeTestExpr_correct
#print axioms katchSemantics_encode
#print axioms katchPacket_range_iff
#print axioms netkatEquiv_katch_restricted
#print axioms netkatIsZero_katch_restricted

end DyNetKAT.DyNetKAT.GraphSafetyTests
