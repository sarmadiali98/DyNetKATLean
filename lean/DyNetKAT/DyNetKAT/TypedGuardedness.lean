import DyNetKAT.DyNetKAT.Definedness
import Mathlib.Logic.ExistsUnique

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

variable {schema : PacketSchema}

/-- A path to a process-variable occurrence. The Boolean records whether
the path crosses an action-prefix continuation edge. -/
inductive ProcessVarOccurrence {schema : PacketSchema} : DyNetKAT schema → Var → Bool → Prop
  | here : ProcessVarOccurrence (.var x) x false
  | packet : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.nSeq z p) x true
  | recv : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.recv c z p) x true
  | send : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.send c z p) x true
  | rcfg : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.rcfgPrefix c z p) x true
  | choiceLeft : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.choice p q) x crossed
  | choiceRight : ProcessVarOccurrence q x crossed → ProcessVarOccurrence (.choice p q) x crossed
  | parallelLeft : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.parallel p q) x crossed
  | parallelRight : ProcessVarOccurrence q x crossed → ProcessVarOccurrence (.parallel p q) x crossed
  | leftMergeLeft : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.leftMerge p q) x crossed
  | leftMergeRight : ProcessVarOccurrence q x crossed → ProcessVarOccurrence (.leftMerge p q) x crossed
  | commMergeLeft : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.commMerge p q) x crossed
  | commMergeRight : ProcessVarOccurrence q x crossed → ProcessVarOccurrence (.commMerge p q) x crossed
  | restrict : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.restrict L p) x crossed
  | project : ProcessVarOccurrence p x crossed → ProcessVarOccurrence (.project n p) x crossed

/-- Typed reading of Definition 7. Every path to a process variable crosses
at least one action-prefix continuation edge. This is a syntactic property. -/
def TypedPaperGuarded (p : DyNetKAT schema) : Prop :=
  ∀ x, ¬ ProcessVarOccurrence p x false

theorem typedPaperGuarded_iff_guardedOccurrences (p : DyNetKAT schema) :
    TypedPaperGuarded p ↔ GuardedOccurrences p := by
  induction p <;> simp only [TypedPaperGuarded, GuardedOccurrences] at *
  case deadlock | nSeq | recv | send | rcfgPrefix =>
    exact ⟨fun _ => trivial, fun _ _ h => by cases h⟩
  case var x =>
    exact ⟨fun h => h x .here, False.elim⟩
  case parallel p q ihp ihq | choice p q ihp ihq |
      leftMerge p q ihp ihq | commMerge p q ihp ihq =>
    rw [← ihp, ← ihq]
    constructor
    · intro h
      constructor <;> intro x hx <;>
        first
        | exact h x (.parallelLeft hx)
        | exact h x (.parallelRight hx)
        | exact h x (.choiceLeft hx)
        | exact h x (.choiceRight hx)
        | exact h x (.leftMergeLeft hx)
        | exact h x (.leftMergeRight hx)
        | exact h x (.commMergeLeft hx)
        | exact h x (.commMergeRight hx)
    · rintro ⟨hp, hq⟩ x hx
      cases hx <;> first | exact hp x (by assumption) | exact hq x (by assumption)
  case restrict L p ih | project n p ih =>
    rw [← ih]
    constructor
    · intro h x hx
      first | exact h x (.restrict hx) | exact h x (.project hx)
    · intro h x hx
      cases hx
      exact h x (by assumption)

theorem RecEnv.lookup_unique {env : (RecEnv schema)} {x : Var} {p q : (DyNetKAT schema)}
    (hp : env.lookup x = some p) (hq : env.lookup x = some q) : p = q :=
  Option.some.inj (hp.symm.trans hq)

/-- Closure makes the partial environment total on the reachable names. -/
theorem ClosedDefined.existsUnique_lookup {env : (RecEnv schema)} {root : (DyNetKAT schema)}
    (h : ClosedDefined env root) {x : Var} (hx : ReachableVar env root x) :
    ∃! body, env.lookup x = some body := by
  have defined := h x hx
  cases he : env.lookup x with
  | none => simp [he] at defined
  | some body =>
    exact ⟨body, rfl, fun _ other => Option.some.inj other.symm⟩

/-- Every reachable defining equation has a guarded body in the typed reading. -/
theorem wellFormed_iff_closedDefined_and_typedPaperGuarded (env : RecEnv schema) (root : DyNetKAT schema) :
    WellFormed env root ↔ ClosedDefined env root ∧
      ∀ x body, ReachableVar env root x → env.lookup x = some body → TypedPaperGuarded body := by
  constructor
  · intro h
    exact ⟨h.1, fun x body hx hb => (typedPaperGuarded_iff_guardedOccurrences body).mpr
      (h.reachable_guarded env root x body hx hb)⟩
  · rintro ⟨closed, guarded⟩
    refine ⟨closed, fun x hx => ?_⟩
    obtain ⟨body, hb, _⟩ := closed.existsUnique_lookup hx
    exact ⟨body, hb, (typedPaperGuarded_iff_guardedOccurrences body).mp (guarded x body hx hb)⟩

end DyNetKAT.DyNetKAT
