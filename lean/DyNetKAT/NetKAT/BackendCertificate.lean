import DyNetKAT.NetKAT.Normalization
import DyNetKAT.NetKAT.KATch
import Lean.Data.Json

namespace DyNetKAT.NetKAT

/-- Sparse relation rows. Repeated entries have set semantics. -/
abbrev BackendRelation := CtxPkt → Finset CtxPkt

def checkBackendRelation (p : NetKAT) (rows : BackendRelation) : Bool :=
  decide (∀ σ : CtxPkt, execute p σ = .supported (rows σ))

theorem checkBackendRelation_sound {p : NetKAT} {rows : BackendRelation}
    (h : checkBackendRelation p rows = true) :
    ∀ σ τ, τ ∈ rows σ ↔ Semantics p σ τ := by
  have checked : ∀ σ : CtxPkt, execute p σ = .supported (rows σ) := of_decide_eq_true h
  intro σ τ
  obtain ⟨B, hb, hs⟩ := execute_correct p σ
  rw [EvalResult.supported.inj (hb.symm.trans (checked σ))] at hs
  exact (hs τ).symm

theorem checkBackendRelation_normalize {p : NetKAT} {rows : BackendRelation}
    (h : checkBackendRelation p rows = true) (σ τ : CtxPkt) :
    τ ∈ rows σ ↔ Semantics (normalize p) σ τ :=
  (checkBackendRelation_sound h σ τ).trans (normalize_correct p σ τ).symm

theorem checkBackendRelation_normalForm {p : NetKAT} {rows : BackendRelation}
    (h : checkBackendRelation p rows = true) (σ τ : CtxPkt) :
    τ ∈ rows σ ↔ (σ, τ) ∈ netkatNormalForm p :=
  (checkBackendRelation_sound h σ τ).trans (netkatNormalForm_mem p σ τ).symm

def checkBackendEquivalent (p q : NetKAT) (rows : BackendRelation) : Bool :=
  checkBackendRelation p rows && checkBackendRelation q rows

theorem checkBackendEquivalent_sound {p q : NetKAT} {rows : BackendRelation}
    (h : checkBackendEquivalent p q rows = true) : netkatEquiv p q = true := by
  obtain ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp h
  exact (netkatEquiv_correct p q).mpr fun σ τ =>
    (checkBackendRelation_sound hp σ τ).symm.trans (checkBackendRelation_sound hq σ τ)

/-- A distinguishing input suffices. The checked evaluator compares all its outputs. -/
def checkBackendCounterexample (p q : NetKAT) (input : CtxPkt) : Bool :=
  !netkatEquivAt p q input

theorem checkBackendCounterexample_sound {p q : NetKAT} {input : CtxPkt}
    (h : checkBackendCounterexample p q input = true) : netkatEquiv p q = false := by
  apply Bool.eq_false_iff.mpr
  intro eq
  have same := netkatEquivAt_complete p q input ((netkatEquiv_correct p q).mp eq input)
  simp [checkBackendCounterexample, same] at h

inductive BackendCandidate where
  | commonRelation (rows : BackendRelation)
  | counterexample (input : CtxPkt)

inductive BackendMethod where
  | checkedRelation
  | checkedCounterexample
  | exactFallback
  deriving DecidableEq, Repr

structure BackendDecision (p q : NetKAT) where
  equivalent : Bool
  method : BackendMethod
  correct : equivalent = netkatEquiv p q

/-- An absent candidate covers unavailable, unsupported, and failed backend runs. -/
def decideWithBackend (p q : NetKAT) (candidate : Option BackendCandidate) :
    BackendDecision p q :=
  let fallback := ⟨netkatEquiv p q, .exactFallback, rfl⟩
  match candidate with
  | some (.commonRelation rows) =>
      if h : checkBackendEquivalent p q rows then
        ⟨true, .checkedRelation, (checkBackendEquivalent_sound h).symm⟩
      else fallback
  | some (.counterexample input) =>
      if h : checkBackendCounterexample p q input then
        ⟨false, .checkedCounterexample, (checkBackendCounterexample_sound h).symm⟩
      else fallback
  | none => fallback

theorem decideWithBackend_correct (p q : NetKAT) (candidate : Option BackendCandidate) :
    (decideWithBackend p q candidate).equivalent = true ↔
      ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ := by
  rw [(decideWithBackend p q candidate).correct, netkatEquiv_correct]

/-- Packet-prefix consumers can use the existing history semantics bridge. -/
theorem decideWithBackend_history (p q : NetKAT) (candidate : Option BackendCandidate) :
    (decideWithBackend p q candidate).equivalent = true ↔
      ∀ h h', HistorySemantics p h h' ↔ HistorySemantics q h h' := by
  rw [(decideWithBackend p q candidate).correct, netkatEquiv_history_correct]

/-- The checked decision can feed existing packet-prefix equational reasoning. -/
theorem decideWithBackend_derives {p q : NetKAT} {candidate : Option BackendCandidate}
    (h : (decideWithBackend p q candidate).equivalent = true) : Derives p q := by
  apply (normalize_derives p).trans
  apply Derives.trans _ (normalize_derives q).symm
  exact IsPairSum.derives_of_equiv (normalize_pairSum p) (normalize_pairSum q) fun σ τ =>
    (normalize_correct p σ τ).trans
      (((decideWithBackend_correct p q candidate).mp h σ τ).trans
        (normalize_correct q σ τ).symm)

/-- Decode fields in the existing enumeration order: src, dst, sw, port. -/
def decodeBackendPacket : List Int → Option CtxPkt
  | [src, dst, sw, port] => do
    let s ← value src
    let d ← value dst
    let w ← value sw
    let p ← value port
    return fun
      | .tpSrc => s
      | .tpDst => d
      | .swId => w
      | .port => p
  | _ => none
where
  value : Int → Option FieldValueEnum
    | 0 => some .v0
    | 1 => some .v1
    | 8 => some .v8
    | 9 => some .v9
    | _ => none

theorem decodeBackendPacket_encode (p : CtxPkt) :
    decodeBackendPacket (NetKAT.fieldEnum.map (katchPacket p)) = some p := by
  have hv (v : FieldValueEnum) : decodeBackendPacket.value (katchValue v) = some v := by
    cases v <;> rfl
  simp only [NetKAT.fieldEnum, List.map_cons, List.map_nil, decodeBackendPacket, katchPacket,
    Function.Embedding.coeFn_mk, hv, Option.bind_some]
  change some (fun f => match f with
    | .tpSrc => p .tpSrc | .tpDst => p .tpDst | .swId => p .swId | .port => p .port) = some p
  congr
  funext f
  cases f <;> rfl

/-- Untrusted numeric relation pairs are decoded before any semantic check. -/
def decodeBackendRelation (entries : List (List Int × List Int)) : Option BackendRelation := do
  let pairs ← entries.mapM fun (input, output) => do
    let σ ← decodeBackendPacket input
    let τ ← decodeBackendPacket output
    return (σ, τ)
  return fun σ => ((pairs.filter fun pair => pair.1 == σ).map Prod.snd).toFinset

/-- Portable transport for adapters. The tag is explicit so that an empty
relation is distinct from a missing or malformed response. -/
def decodeBackendCandidate (text : String) : Option BackendCandidate := do
  let json ← (Lean.Json.parse text).toOption
  let kind ← (json.getObjValAs? String "kind").toOption
  match kind with
  | "relation" =>
    let pairs ← (json.getObjValAs? (List (List Int × List Int)) "pairs").toOption
    return .commonRelation (← decodeBackendRelation pairs)
  | "counterexample" =>
    let input ← (json.getObjValAs? (List Int) "input").toOption
    return .counterexample (← decodeBackendPacket input)
  | _ => none

end DyNetKAT.NetKAT
