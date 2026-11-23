import DyNetKATLean.Core.Equations
import DyNetKATLean.Core.SemanticBranching

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

/-- The typed equational system with infinitary AIP. Image finiteness is
a semantic side condition at each use of AIP. The guarded source domain
discharges it via `WellFormed.imageFiniteFrom`. -/
inductive Derives {schema : NetKAT.PacketSchema} (env : RecEnv schema) : DyNetKAT schema → DyNetKAT schema → Prop
  | ofNoAIP : DerivesNoAIP env p q → Derives env p q
  | symm : Derives env p q → Derives env q p
  | trans : Derives env p q → Derives env q r → Derives env p r
  | prefixCongr (l : MoveLabel schema) : Derives env p q → Derives env (l.prefix p) (l.prefix q)
  | choiceCongr : Derives env p p' → Derives env q q' → Derives env (.choice p q) (.choice p' q')
  | parallelCongr : Derives env p p' → Derives env q q' →
      Derives env (.parallel p q) (.parallel p' q')
  | leftMergeCongr : Derives env p p' → Derives env q q' →
      Derives env (.leftMerge p q) (.leftMerge p' q')
  | commMergeCongr : Derives env p p' → Derives env q q' →
      Derives env (.commMerge p q) (.commMerge p' q')
  | restrictCongr (L : Set (CommunicationAction schema)) : Derives env p q →
      Derives env (.restrict L p) (.restrict L q)
  | projectCongr (n : Nat) : Derives env p q → Derives env (.project n p) (.project n q)
  | aip : ImageFiniteFrom env p → ImageFiniteFrom env q →
      (∀ n : Nat, Derives env (.project n p) (.project n q)) → Derives env p q

theorem Derives.refl (env : RecEnv schema) (p : DyNetKAT schema) : Derives env p p :=
  .ofNoAIP (.refl p)

theorem Derives.aip_guarded {env : RecEnv schema} {p q : DyNetKAT schema}
    (hp : WellFormed env p) (hq : WellFormed env q)
    (premises : ∀ n, Derives env (.project n p) (.project n q)) : Derives env p q :=
  .aip hp.imageFiniteFrom hq.imageFiniteFrom premises

/-- Soundness by induction on the full derivation, including all AIP premises. -/
theorem Derives.sound {env : RecEnv schema} {p q : DyNetKAT schema}
    (h : Derives env p q) : Bisimilar env p q := by
  induction h with
  | ofNoAIP h => exact h.sound
  | symm _ ih => exact Bisimilar.symm env ih
  | trans _ _ ih₁ ih₂ => exact Bisimilar.trans env ih₁ ih₂
  | prefixCongr l _ ih => exact Equations.prefix_congr env l ih
  | choiceCongr _ _ ih₁ ih₂ =>
    exact Bisimilar.trans env (Bisimilar.choice_left env ih₁) (Bisimilar.choice_right env ih₂)
  | parallelCongr _ _ ih₁ ih₂ =>
    exact Bisimilar.trans env (Bisimilar.parallel_right env ih₁) (Bisimilar.parallel_left env ih₂)
  | leftMergeCongr _ _ ih₁ ih₂ =>
    exact Bisimilar.trans env (Bisimilar.leftMerge_left env ih₁) (Bisimilar.leftMerge_right env ih₂)
  | commMergeCongr _ _ ih₁ ih₂ =>
    exact Bisimilar.trans env (Bisimilar.commMerge_right env ih₁) (Bisimilar.commMerge_left env ih₂)
  | restrictCongr _ _ ih => exact Bisimilar.restrict env ih
  | projectCongr _ _ ih => exact Bisimilar.project env ih
  | aip hp hq _ ih => exact approximation_induction hp hq ih

theorem Derives.aip_guarded_sound {env : RecEnv schema} {p q : DyNetKAT schema}
    (hp : WellFormed env p) (hq : WellFormed env q)
    (premises : ∀ n, Derives env (.project n p) (.project n q)) : Bisimilar env p q :=
  (Derives.aip_guarded hp hq premises).sound

/-- The soundness direction of Theorem 1 for the typed equational system. -/
theorem derivability_sound {env : RecEnv schema} {p q : DyNetKAT schema}
    (h : Derives env p q) : Bisimilar env p q :=
  h.sound

end DyNetKAT.DyNetKAT
