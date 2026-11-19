import DyNetKAT.DyNetKAT.TraceSafety

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.TraceSafety

open DyNetKAT.NetKAT

private def matchesLetter : MoveLabel → Letter → Bool
  | .visible (.packet p), .packet i o =>
      match execute p i with
      | .supported outputs => decide (o ∈ outputs)
      | .unsupported => false
  | .visible (.rcfg x p), .rcfg y q => decide (x = y ∧ p = q)
  | _, _ => false

private theorem matchesLetter_iff (l : MoveLabel) (letter : Letter) :
    matchesLetter l letter = true ↔
      l.Realizes (letter.action.pendingFor []) [] letter.action [] (letter.action.handledAfter []) := by
  cases letter with
  | packet i o =>
      cases l with
      | visible v =>
          cases v with
          | packet p =>
              obtain ⟨outputs, eval, exactOutput⟩ := execute_correct p i
              simp only [matchesLetter, eval, decide_eq_true_eq]
              constructor
              · intro mem
                exact .packet ((historySemantics_singleton_iff_packetSemantics ..).mpr
                  ((exactOutput o).mpr mem))
              · intro step
                cases step with
                | packet history =>
                    exact (exactOutput o).mp
                      ((historySemantics_singleton_iff_packetSemantics ..).mp history)
          | rcfg => exact ⟨Bool.noConfusion, fun h => by cases h⟩
      | recv | send => exact ⟨Bool.noConfusion, fun h => by cases h⟩
  | rcfg x p =>
      cases l with
      | visible v =>
          cases v with
          | packet => exact ⟨Bool.noConfusion, fun h => by cases h⟩
          | rcfg y q =>
              simp only [matchesLetter, decide_eq_true_eq]
              constructor
              · rintro ⟨rfl, rfl⟩; exact .rcfg
              · intro step; cases step; exact ⟨rfl, rfl⟩
      | recv | send => exact ⟨Bool.noConfusion, fun h => by cases h⟩

private def checkedRow {G : ProcessGraph} {bodyChecks live}
    (support : ProjectionSupport G bodyChecks live) (state : CheckedResidual)
    (valid : state.Valid live) :
    { row : List CheckedMove // MovesExact G state.proc (row.map CheckedMove.erase) ∧
      ∀ move ∈ row, move.2.Valid live } :=
  match checked : checkedMoves G bodyChecks state with
  | some row => ⟨row, checkedMoves_spec support valid checked⟩
  | none => False.elim (by
    obtain ⟨row, existsRow⟩ := checkedMoves_exists support valid
    rw [checked] at existsRow
    cases existsRow)

private def acceptsWord {G : ProcessGraph} {bodyChecks live}
    (support : ProjectionSupport G bodyChecks live) (state : CheckedResidual)
    (valid : state.Valid live) : Word → Bool
  | [] => true
  | a :: rest =>
      let row := checkedRow support state valid
      row.val.attach.any fun move =>
        matchesLetter move.val.1 a &&
          acceptsWord support move.val.2 (row.property.2 _ move.property) rest

private theorem acceptsWord_iff {G : ProcessGraph} {bodyChecks live}
    (support : ProjectionSupport G bodyChecks live) {env : RecEnv} {p : DyNetKAT}
    {state : CheckedResidual} (valid : state.Valid live) (corr : Corr G env p state.proc)
    (w : Word) :
    acceptsWord support state valid w = true ↔ SourceTrace env p (w.map Letter.action) := by
  induction w generalizing p state with
  | nil => exact ⟨fun _ => sourceTrace_nil .., fun _ => rfl⟩
  | cons a w ih =>
      let row := checkedRow support state valid
      have source := row.property.1.source_steps corr (a.action.pendingFor []) [] a.action []
        (a.action.handledAfter [])
      unfold acceptsWord
      simp only [List.any_eq_true, Bool.and_eq_true, List.map_cons,
        sourceTrace_cons_actionStep]
      constructor
      · rintro ⟨⟨m, mem⟩, _, realized, accepts⟩
        obtain ⟨q, step, corresponds⟩ := source.1 m.1 m.2.proc
          (List.mem_map.mpr ⟨m, mem, rfl⟩) ((matchesLetter_iff ..).mp realized)
        exact ⟨q, step, (ih _ corresponds).mp accepts⟩
      · rintro ⟨q, step, run⟩
        obtain ⟨l, target, mem, realized, corresponds⟩ := source.2 q step
        obtain ⟨m, member, eq⟩ := List.mem_map.mp mem
        cases m with
        | mk label next =>
          cases eq
          exact ⟨⟨(label, next), member⟩, by simp, (matchesLetter_iff ..).mpr realized,
            (ih _ corresponds).mpr run⟩

/-- Check the supplied forbidden words using exact symbolic moves and the
supplied-packet evaluator. Search depth is the length of the current word.
No finite derivative closure or exhaustively generated alphabet is needed. -/
def check {extended : Bool} {env : RecEnv} {p : Program extended env}
    (compiled : p.Compiled) (rootChecks : RestrictionChecks)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : (compiled.initial rootChecks).checked.Valid live)
    (forbidden : List Word) : Bool :=
  forbidden.all fun w => !acceptsWord support (compiled.initial rootChecks).checked valid w

theorem check_correct {extended : Bool} {env : RecEnv} {p : Program extended env}
    (compiled : p.Compiled) (rootChecks : RestrictionChecks)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : (compiled.initial rootChecks).checked.Valid live)
    (forbidden : List Word) :
    check compiled rootChecks support valid forbidden = true ↔ Safe p forbidden := by
  simp only [check, List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Safe]
  apply forall_congr'
  intro w
  exact imp_congr_right fun _ => not_congr (acceptsWord_iff support valid compiled.corr w)

theorem check_iff_equationalSafety {extended : Bool} {env : RecEnv} {p : Program extended env}
    (compiled : p.Compiled) (rootChecks : RestrictionChecks)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : (compiled.initial rootChecks).checked.Valid live)
    (A : Alphabet) (forbidden : List Word) (nonemptyWords : [] ∉ forbidden)
    (alphabet : UsesAlphabet p A) :
    check compiled rootChecks support valid forbidden = true ↔ EquationalSafety p A forbidden :=
  (check_correct compiled rootChecks support valid forbidden).trans
    (equationalSafety_iff_safe p A forbidden nonemptyWords alphabet).symm

end DyNetKAT.DyNetKAT.TraceSafety
