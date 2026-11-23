import DyNetKATLean

open DyNetKAT.NetKAT DyNetKAT.DyNetKAT

private theorem deadlockAdmissible : BaseAdmissible (schema := ctxSchema) RecEnv.empty .deadlock :=
  (baseAdmissible_iff _ _).2 ⟨trivial, fun x hx => by
    have impossible : x ∈ (∅ : Finset Var) := by
      cases hx with
      | direct occurs => exact occurs
      | throughDefinition _ lookup _ => simp only [RecEnv.lookup_empty, reduceCtorEq] at lookup
    exact False.elim (Finset.not_mem_empty x impossible)⟩

private def halt : Program (schema := ctxSchema) false RecEnv.empty :=
  ⟨.deadlock, deadlockAdmissible⟩

private def forward := halt.packetPrefix trivial .id
private def packet : CtxPkt := fun _ => .v0

private theorem forwardStep :
    Step RecEnv.empty ⟨forward.term, [packet], []⟩ (.packet packet packet)
      ⟨.deadlock, [], [packet]⟩ :=
  Step.cpol_seq_ok .id .deadlock packet packet [] [] (historySem_id_self _)

private def residual : forward.Residual := forward.initial.advance forwardStep

example : residual.term = .deadlock := rfl

example : PaperAdmissible false RecEnv.empty residual.term := residual.admissible

example : {q | ProcessStep RecEnv.empty residual.term q}.Finite := residual.finite_targets

example : ∃ q, IsDNKNormalForm q ∧ DerivesNoAIP RecEnv.empty forward.term q :=
  forward.normalizes
