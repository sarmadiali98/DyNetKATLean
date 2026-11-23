import DyNetKATLean.Core.FiniteClosure

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

open DyNetKAT.NetKAT

abbrev BisimCandidate (G : ProcessGraph schema) := List (ConcreteRow G × ConcreteRow G)

def BisimCandidate.Relates {G : ProcessGraph schema} (pairs : BisimCandidate G) (p q : GProc schema) :
    Prop := ∃ r ∈ pairs, r.1.proc = p ∧ r.2.proc = q

def BisimCandidate.contains {G : ProcessGraph schema} (pairs : BisimCandidate G)
    (id : ConcreteIdentity schema) (p q : GProc schema) : Bool :=
  pairs.any fun (l, r) => id.same p l.proc && id.same q r.proc

theorem BisimCandidate.contains_sound {G : ProcessGraph schema} {pairs : BisimCandidate G}
    {id : ConcreteIdentity schema} {p q : GProc schema} (h : pairs.contains id p q = true) :
    pairs.Relates p q := by
  obtain ⟨r, hr, he⟩ := List.any_eq_true.mp h
  obtain ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp he
  exact ⟨r, hr, (id.sound hp).symm, (id.sound hq).symm⟩

private def matchRows {G : ProcessGraph schema} (id : ConcreteIdentity schema) (pairs : BisimCandidate G)
    (l r : ConcreteRow G) : Bool :=
  l.moves.all fun m => r.moves.any fun n =>
    decide (m.1 = n.1) && pairs.contains id m.2 n.2

def checkBisimulation {G : ProcessGraph schema} (id : ConcreteIdentity schema) (p q : GProc schema)
    (pairs : BisimCandidate G) : Bool :=
  pairs.contains id p q && pairs.all fun (l, r) =>
    pairs.contains id r.proc l.proc && matchRows id pairs l r

structure ValidBisimCertificate {schema : NetKAT.PacketSchema} {G : ProcessGraph schema} (p q : GProc schema)
    (pairs : BisimCandidate G) : Prop where
  roots : pairs.Relates p q
  bisimulation : IsGBisimulation G pairs.Relates

theorem checkBisimulation_sound {G : ProcessGraph schema} {id : ConcreteIdentity schema} {p q : GProc schema}
    {pairs : BisimCandidate G} (h : checkBisimulation id p q pairs = true) :
    ValidBisimCertificate p q pairs := by
  obtain ⟨hroot, hall⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨BisimCandidate.contains_sound hroot, ⟨?_, ?_⟩⟩
  · rintro _ _ ⟨r, hm, rfl, rfl⟩
    exact BisimCandidate.contains_sound (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp hall r hm)).1
  · rintro _ _ ⟨r, hm, rfl, rfl⟩ pt hl a p' pt' hl' hs
    obtain ⟨l, hm', hreal⟩ := (r.1.exactRow pt hl a p' pt' hl').mp hs
    have hmatch := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hall r hm)).2
    obtain ⟨⟨k, q'⟩, hk, h⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp hmatch (l, p') hm')
    obtain ⟨he, hnext⟩ := Bool.and_eq_true_iff.mp h
    have hEq : l = k := of_decide_eq_true he
    exact ⟨q', (r.2.exactRow pt hl a q' pt' hl').mpr ⟨k, hk, hEq ▸ hreal⟩,
      BisimCandidate.contains_sound hnext⟩

theorem ValidBisimCertificate.bisimilar {G : ProcessGraph schema} {env : RecEnv schema}
    {p q : DyNetKAT schema} {gp gq : GProc schema} {pairs : BisimCandidate G}
    (h : ValidBisimCertificate gp gq pairs) (hp : Corr G env p gp) (hq : Corr G env q gq) :
    Bisimilar env p q :=
  (gbisimilar_iff_bisimilar G env hp hq).mp ⟨_, h.bisimulation, h.roots⟩

/-- A one-step distinguishing witness for an unmatched reconfiguration.
The observation includes the channel and the carried policy. -/
def checkReconfigurationMismatch {G : ProcessGraph schema} (left right : ConcreteRow G)
    (channel : Channel) (policy : NetKAT schema) : Bool :=
  let label := MoveLabel.visible (.rcfg channel policy)
  left.moves.any (fun m => decide (m.1 = label)) &&
    !right.moves.any (fun m => decide (m.1 = label))

theorem checkReconfigurationMismatch_sound {G : ProcessGraph schema} {left right : ConcreteRow G}
    {channel policy} (h : checkReconfigurationMismatch left right channel policy = true) :
    ¬ GBisimilar G left.proc right.proc := by
  obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨⟨l, p'⟩, hm, he⟩ := List.any_eq_true.mp hl
  have he : l = .visible (.rcfg channel policy) := of_decide_eq_true he
  subst l
  rintro ⟨R, bisim, related⟩
  have step := (left.exactRow [] [] (.rcfg channel policy) p' [] []).mpr ⟨_, hm, .rcfg⟩
  obtain ⟨q', hstep, _⟩ := bisim.2 _ _ related [] [] _ _ [] [] step
  obtain ⟨k, hk, hreal⟩ := (right.exactRow [] [] (.rcfg channel policy) q' [] []).mp hstep
  cases hreal
  have present : right.moves.any (fun m => decide (m.1 = .visible (.rcfg channel policy))) = true :=
    List.any_eq_true.mpr ⟨_, hk, by simp⟩
  simp [present] at hr

private def refinePairs {G : ProcessGraph schema} (id : ConcreteIdentity schema) :
    Nat → BisimCandidate G → BisimCandidate G
  | 0, pairs => pairs
  | fuel + 1, pairs =>
    let next := pairs.filter fun (l, r) => matchRows id pairs l r && matchRows id pairs r l
    if next.length = pairs.length then next else refinePairs id fuel next

/-- Try every same-label successor match in the current relation. Iterative
pruning can remove pairs whose only witnesses depended on a removed pair. -/
def discoverBisimulation {G : ProcessGraph schema} (id : ConcreteIdentity schema) (maxPairs rounds : Nat)
    (p q : GProc schema) (left right : ClosureCandidate G) :
    Except DiscoveryFailure (BisimCandidate G) :=
  if 2 * left.length * right.length > maxPairs then .error .resourceLimit
  else
    let cross := left.flatMap fun l => right.map fun r => (l, r)
    let pairs := refinePairs id rounds (cross ++ cross.map Prod.swap)
    if checkBisimulation id p q pairs then .ok pairs else .error .unknown

theorem discoverBisimulation_sound {G : ProcessGraph schema} {id : ConcreteIdentity schema}
    {maxPairs rounds p q left right pairs}
    (h : discoverBisimulation (G := G) id maxPairs rounds p q left right = .ok pairs) :
    ValidBisimCertificate p q pairs := by
  unfold discoverBisimulation at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · rename_i hc
    exact checkBisimulation_sound (by simpa only [Except.ok.inj h] using hc)
  · simp_all

/-- Discover both concrete closures with the given per-root limits, then
attempt to certify bisimilarity within the pair and refinement limits. -/
def discoverResidualBisimulation {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}
    {live : NodeId → Prop} (support : ProjectionSupport G bodyChecks live)
    (id : ConcreteIdentity schema) (limits : ClosureLimits) (maxPairs rounds : Nat)
    (p q : CheckedResidual schema) (hp : p.Valid live) (hq : q.Valid live) :
    Except DiscoveryFailure (BisimCandidate G) := do
  let left ← discoverClosure support id limits p hp
  let right ← discoverClosure support id limits q hq
  discoverBisimulation id maxPairs rounds p.proc q.proc left right

theorem discoverResidualBisimulation_sound {G : ProcessGraph schema}
    {bodyChecks : NodeId → RestrictionChecks schema} {live : NodeId → Prop}
    {support : ProjectionSupport G bodyChecks live} {id limits maxPairs rounds p q hp hq pairs}
    (h : discoverResidualBisimulation support id limits maxPairs rounds p q hp hq = .ok pairs) :
    ValidBisimCertificate p.proc q.proc pairs := by
  unfold discoverResidualBisimulation at h
  cases hl : discoverClosure support id limits p hp with
  | error e => simp [hl, Bind.bind, Except.bind] at h
  | ok left =>
    cases hr : discoverClosure support id limits q hq with
    | error e => simp [hl, hr, Bind.bind, Except.bind] at h
    | ok right =>
      exact discoverBisimulation_sound (by simpa [hl, hr, Bind.bind, Except.bind] using h)

end DyNetKAT.DyNetKAT
