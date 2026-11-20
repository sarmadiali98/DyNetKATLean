import DyNetKAT.DyNetKAT.Definedness
import DyNetKAT.DyNetKAT.Semantics

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

/-- A ground process has no process-variable occurrences, even behind prefixes. -/
def Ground (p : DyNetKAT schema) : Prop := recursiveVars p = ∅

theorem Ground.guarded {p : DyNetKAT schema} (h : Ground p) : GuardedOccurrences p := by
  induction p <;> simp_all [Ground, recursiveVars, GuardedOccurrences, Finset.union_eq_empty]

/-- Count process prefixes, ignoring packet syntax and projection indices. -/
def prefixCount : DyNetKAT schema → Nat
  | .deadlock | .var _ => 0
  | .nSeq _ p | .recv _ _ p | .send _ _ p | .rcfgPrefix _ _ p => prefixCount p + 1
  | .choice p q | .parallel p q | .leftMerge p q | .commMerge p q =>
      prefixCount p + prefixCount q
  | .restrict _ p | .project _ p => prefixCount p

/-- A ground transition preserves groundness and consumes at least one prefix. -/
theorem Step.ground_decreases {env : RecEnv schema} {s t : Config schema} {a : Action schema}
    (h : Step env s a t) (hg : Ground s.proc) :
    Ground t.proc ∧ prefixCount t.proc < prefixCount s.proc := by
  induction h <;> simp only [Ground, recursiveVars, Finset.union_eq_empty, prefixCount] at *
  all_goals try solve | simp_all
  case cpol_choice_l =>
    rename_i ih
    obtain ⟨g, lt⟩ := ih hg.1
    exact ⟨g, by omega⟩
  case cpol_choice_r =>
    rename_i ih
    obtain ⟨g, lt⟩ := ih hg.2
    exact ⟨g, by omega⟩
  all_goals
    rename_i ih₁ ih₂
    obtain ⟨g₁, lt₁⟩ := ih₁ hg.1
    obtain ⟨g₂, lt₂⟩ := ih₂ hg.2
    exact ⟨⟨g₁, g₂⟩, Nat.add_lt_add lt₁ lt₂⟩

end DyNetKAT.DyNetKAT
