import DyNetKATLean

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.HeadNormalFormTests

open DyNetKAT.NetKAT
open HeadNormalForm

variable (env : RecEnv) (p q : DyNetKAT)

example : DerivesNoAIP env .deadlock (render []) := .refl _
example : DerivesNoAIP env (.nSeq .drop p) (render []) := .a0 _

-- Two distinct input valuations both give head branches of the identity policy.
example (σ τ : CtxPkt) (different : σ ≠ τ) :
    ∃ a b : HeadSummand, a ∈ packetHeads .id p ∧ b ∈ packetHeads .id p ∧ a ≠ b := by
  refine ⟨.packet σ σ p, .packet τ τ p, ?_, ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨(σ, σ), (mem_symbolicPairs ..).mpr rfl, rfl⟩
  · apply List.mem_map.mpr
    exact ⟨(τ, τ), (mem_symbolicPairs ..).mpr rfl, rfl⟩
  · intro h
    have eq := congrArg HeadSummand.label h
    cases eq
    exact different rfl

example : DerivesNoAIP env (.nSeq .id p) (render (packetHeads .id p)) :=
  packetHeads_correct env _ _

private def s (p : DyNetKAT) := HeadSummand.send "x" .id p
private def r (p : DyNetKAT) := HeadSummand.recv "x" .id p
private def c (p : DyNetKAT) := HeadSummand.rcfg "x" .id p

example : DerivesNoAIP env (s p).render (render [s p]) := (render_singleton env _).symm
example : DerivesNoAIP env (r p).render (render [r p]) := (render_singleton env _).symm
example : DerivesNoAIP env (c p).render (render [c p]) := (render_singleton env _).symm
example : DerivesNoAIP env (.choice (render [s p]) (render [r q])) (render [s p, r q]) :=
  render_append env [s p] [r q]
example : DerivesNoAIP env (render [r q, s p, r q]) (render [s p, r q]) :=
  render_derives_of_mem_iff env (by intro b; simp [or_left_comm, or_comm])

example : DerivesNoAIP env (.leftMerge (render [s p]) q) (render [s (.parallel p q)]) :=
  leftMerge_correct env [s p] q

example : DerivesNoAIP env (.commMerge (render [r p]) (render [s q]))
    (render [c (.parallel p q)]) := commMerge_correct env [r p] [s q]

example : DerivesNoAIP env (.commMerge (render [s p]) (render [r q]))
    (render [c (.parallel p q)]) := commMerge_correct env [s p] [r q]

example : DerivesNoAIP env (.commMerge (render [r p]) (render [.send "other" .id q]))
    (render []) := commMerge_correct env [r p] [.send "other" .id q]

example : DerivesNoAIP env (.commMerge (render [r p]) (render [.send "x" (.union .id .drop) q]))
    (render []) := commMerge_correct env [r p] [.send "x" (.union .id .drop) q]

private abbrev joints (p q : DyNetKAT) : HeadNormalForm :=
  [s (.parallel p (r q).render), r (.parallel q (s p).render), c (.parallel p q)]

private theorem parallelDerivation : DerivesNoAIP env (.parallel (s p).render (r q).render)
    (render (joints p q)) :=
  parallel_correct env (render_singleton env (s p)).symm (render_singleton env (r q)).symm

example (pt hl : List CtxPkt) :
    Step env ⟨render (joints p q), pt, hl⟩ (.rcfg "x" .id) ⟨.parallel p q, pt, hl⟩ :=
  (HeadNormalForm.step_iff ..).mpr ⟨c (.parallel p q), by simp [joints], rfl, .rcfg⟩

example : DerivesNoAIP env (.restrict Set.univ (render [s p])) (render []) := by
  simpa [HeadNormalForm.restrict, s, HeadSummand.send, Equations.PrefixBlocked] using
    restrict_correct env Set.univ [s p]

example : DerivesNoAIP env (.restrict ∅ (render [r p])) (render [r (.restrict ∅ p)]) := by
  simpa [HeadNormalForm.restrict, r, HeadSummand.recv, HeadSummand.withContinuation,
    Equations.PrefixBlocked] using restrict_correct env ∅ [r p]

example : DerivesNoAIP env (.restrict Set.univ (.parallel (s p).render (r q).render))
    (render [c (.restrict Set.univ (.parallel p q))]) := by
  apply DerivesNoAIP.trans (.restrictCongr _ (parallelDerivation env p q))
  simpa [HeadNormalForm.restrict, joints, s, r, c, HeadSummand.send, HeadSummand.recv,
    HeadSummand.rcfg, HeadSummand.withContinuation, Equations.PrefixBlocked] using
    restrict_correct env Set.univ (joints p q)

example : DerivesNoAIP env (.project 0 (render [s p])) (render []) :=
  project_correct env 0 [s p]

example : DerivesNoAIP env (.project 1 (render [s p])) (render [s (.project 0 p)]) :=
  project_correct env 1 [s p]

example : DerivesNoAIP env (.project 1 (.project 2 (render [s p])))
    (render [s (.project 0 (.project 1 p))]) :=
  .trans (.projectCongr 1 (project_correct env 2 [s p])) (project_correct env 1 _)

#print axioms exists_headNormalForm_of_guarded
#print axioms HeadNormalForm.packetHeads_correct
#print axioms HeadNormalForm.parallel_correct
#print axioms HeadNormalForm.commMerge_correct
#print axioms HeadNormalForm.restrict_correct
#print axioms HeadNormalForm.project_correct
#print axioms HeadNormalForm.step_iff
#print axioms guarded_normalizes
#print axioms WellFormed.exists_headNormalForm
#print axioms WellFormed.normalizes

end DyNetKAT.DyNetKAT.HeadNormalFormTests
