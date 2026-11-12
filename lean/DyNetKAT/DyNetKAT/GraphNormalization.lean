import DyNetKAT.DyNetKAT.GraphMoves
import DyNetKAT.DyNetKAT.SafetyCheck
import DyNetKAT.NetKAT.NormalForm
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finite.Prod

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- The process projection of one SOS transition under the outer
    restriction used by the safety analysis. The lists are quantified
    here and retained in the bisimulation theorem. -/
def RestrictedDerivativeStep (G : ProcessGraph) (p q : GProc) : Prop :=
  ∃ pt hl a pt' hl', actionAllowed Set.univ a ∧
    GStep G ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩

def ReachableDerivative (G : ProcessGraph) : GProc → Prop :=
  Relation.ReflTransGen (RestrictedDerivativeStep G) G.root

/-- A candidate contains the initial process, is closed under all
    restricted SOS steps, and contains only reachable derivatives. -/
structure DerivativeClosure (G : ProcessGraph) (states : Set GProc) : Prop where
  root_mem : G.root ∈ states
  closed : ∀ ⦃p q⦄, p ∈ states → RestrictedDerivativeStep G p q → q ∈ states
  reachable : ∀ ⦃p⦄, p ∈ states → ReachableDerivative G p

def HasFiniteDerivatives (G : ProcessGraph) : Prop :=
  ∃ states : Set GProc, states.Finite ∧ DerivativeClosure G states

theorem DerivativeClosure.mem_iff {G : ProcessGraph} {states : Set GProc}
    (h : DerivativeClosure G states) (p : GProc) : p ∈ states ↔ ReachableDerivative G p := by
  refine ⟨fun hm => h.reachable hm, ?_⟩
  intro hr
  induction hr with
  | refl => exact h.root_mem
  | tail _ hs ih => exact h.closed ih hs

theorem hasFiniteDerivatives_iff {G : ProcessGraph} :
    HasFiniteDerivatives G ↔ {p | ReachableDerivative G p}.Finite := by
  constructor
  · rintro ⟨S, hFin, hClosure⟩
    exact hFin.subset (fun p hp => (hClosure.mem_iff p).mpr hp)
  · intro h
    exact ⟨_, h, ⟨.refl, fun _ _ hp hs => hp.tail hs, fun _ hp => hp⟩⟩

/-- The certificate supplies derivative syntax, a transition table, and
    an order for computing the active reference rows. Index zero denotes
    the initial process. Each other index must have an incoming edge
    from an earlier index. -/
structure NormalizationCandidate (n : Nat) where
  referenceOrder : List NodeId
  state : Fin (n + 1) → GProc
  moves : Fin (n + 1) → List (SequentialLabel × Fin (n + 1))

/-- Compare syntax for certificate validation. An arbitrary set in a
    restriction has no executable equality test, so such a comparison
    cannot certify equality. -/
def sameProcess : GProc → GProc → Bool
  | .deadlock, .deadlock => true
  | .ref i, .ref j => decide (i = j)
  | .nSeq p u, .nSeq q v => decide (p = q) && sameProcess u v
  | .rcfgPrefix x p u, .rcfgPrefix y q v
  | .recv x p u, .recv y q v
  | .send x p u, .send y q v => decide (x = y) && decide (p = q) && sameProcess u v
  | .choice u v, .choice w z
  | .parallel u v, .parallel w z
  | .leftMerge u v, .leftMerge w z
  | .commMerge u v, .commMerge w z => sameProcess u w && sameProcess v z
  | .project i u, .project j v => decide (i = j) && sameProcess u v
  | _, _ => false

theorem sameProcess_sound {p q : GProc} (h : sameProcess p q = true) : p = q := by
  induction p generalizing q <;> cases q <;>
    simp_all [sameProcess] <;> aesop

/-- Restriction constructors in a derivative's own syntax prevent
    structural comparison. Reference bodies are checked separately. -/
def restrictionFree : GProc → Prop
  | .restrict _ _ => False
  | .nSeq _ p | .recv _ _ p | .send _ _ p | .rcfgPrefix _ _ p | .project _ p =>
      restrictionFree p
  | .choice p q | .parallel p q | .leftMerge p q | .commMerge p q =>
      restrictionFree p ∧ restrictionFree q
  | .deadlock | .ref _ => True

theorem sameProcess_self_iff (p : GProc) : sameProcess p p = true ↔ restrictionFree p := by
  induction p <;> simp_all [sameProcess, restrictionFree]

def SequentialLabel.enabled : SequentialLabel → Bool
  | .packet p => !netkatIsZero p
  | .rcfg _ _ => true

/-- Keep the actions admitted by the outer restriction that have an SOS witness. -/
def observableMove (e : SymbolicMove) : Option (SequentialLabel × GProc) :=
  match e with
  | (.visible l, p) => if l.enabled then some (l, p) else none
  | (.recv .., _) | (.send .., _) => none

private theorem mem_observable {row : List SymbolicMove} {l : SequentialLabel} {p : GProc} :
    (l, p) ∈ row.filterMap observableMove ↔ (.visible l, p) ∈ row ∧ l.enabled = true := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨k, q⟩, hm, he⟩
    cases k with
    | visible k =>
        simp only [observableMove, Option.ite_none_right_eq_some, Option.some.injEq,
          Prod.mk.injEq] at he
        obtain ⟨hen, rfl, rfl⟩ := he
        exact ⟨hm, hen⟩
    | recv | send => cases he
  · rintro ⟨hm, he⟩
    exact ⟨_, hm, by simp [observableMove, he]⟩

private theorem realizes_allowed {l : SequentialLabel} {pt hl pt' hl' : List CtxPkt}
    {a : Action} (h : MoveLabel.Realizes (.visible l) pt hl a pt' hl') :
    actionAllowed Set.univ a := by
  cases h <;> trivial

theorem realizes_enabled {l : SequentialLabel} {pt hl pt' hl' : List CtxPkt}
    {a : Action} (h : MoveLabel.Realizes (.visible l) pt hl a pt' hl') :
    l.enabled = true := by
  cases h with
  | rcfg => rfl
  | packet h =>
      have hSem := (historySemantics_iff_packetSemantics _ _ _ [] []).mp h
      have hZero := (netkatIsZero_false_iff_exists _).mpr ⟨_, _, hSem.2⟩
      simp [SequentialLabel.enabled, hZero]

private theorem realizes_visible {l : MoveLabel} {pt hl pt' hl' : List CtxPkt}
    {a : Action} (h : MoveLabel.Realizes l pt hl a pt' hl')
    (ha : actionAllowed Set.univ a) : ∃ k, l = .visible k := by
  cases h
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · simp [actionAllowed] at ha
  · simp [actionAllowed] at ha

private def agrees {n : Nat} (C : NormalizationCandidate n) (actual : SequentialLabel × GProc)
    (edge : SequentialLabel × Fin (n + 1)) : Bool :=
  decide (actual.1 = edge.1) && sameProcess actual.2 (C.state edge.2)

private def rowMatches {n : Nat} (C : NormalizationCandidate n) (i : Fin (n + 1))
    (row : List SymbolicMove) : Bool :=
  let actual := row.filterMap observableMove
  actual.all (fun m => (C.moves i).any (agrees C m)) &&
    (C.moves i).all (fun e => actual.any fun m => agrees C m e)

private theorem rowMatches_exact {n : Nat} {C : NormalizationCandidate n} {i : Fin (n + 1)}
    {row : List SymbolicMove} (h : rowMatches C i row = true)
    (l : SequentialLabel) (p : GProc) :
    (l, p) ∈ row.filterMap observableMove ↔ ∃ j, (l, j) ∈ C.moves i ∧ p = C.state j := by
  simp only [rowMatches, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, agrees,
    decide_eq_true_eq] at h
  constructor
  · intro hm
    obtain ⟨⟨k, j⟩, he, rfl, hp⟩ := h.1 _ hm
    exact ⟨j, he, sameProcess_sound hp⟩
  · rintro ⟨j, he, rfl⟩
    obtain ⟨⟨k, q⟩, hm, rfl, hp⟩ := h.2 _ he
    exact sameProcess_sound hp ▸ hm

private def checkRow {n : Nat} (C : NormalizationCandidate n) (rows : ReferenceRows)
    (i : Fin (n + 1)) : Bool :=
  match localMoves (referenceMoves rows) (C.state i) with
  | none => false
  | some row => rowMatches C i row

/-- Executable validation checks initial-state identity, exact rows and
    an incoming edge witnessing reachability of every non-initial index. -/
def checkNormalization {n : Nat} (G : ProcessGraph) (C : NormalizationCandidate n) : Bool :=
  match buildReferenceRows G C.referenceOrder [] with
  | none => false
  | some rows =>
      sameProcess G.root (C.state 0) &&
      decide (∀ i, checkRow C rows i = true) &&
      decide (∀ i, i = 0 ∨ ∃ j, j < i ∧
        (C.moves j).any (fun edge => decide (edge.2 = i)) = true)

/-- A convenient sufficient condition for proving acceptance of an explicit
    table without reducing the packet evaluator in the kernel. -/
theorem checkNormalization_of_rows {n : Nat} {G : ProcessGraph}
    {C : NormalizationCandidate n} {refs : ReferenceRows}
    (hRefs : buildReferenceRows G C.referenceOrder [] = some refs)
    (hRoot : sameProcess G.root (C.state 0) = true)
    (hComparable : ∀ i, sameProcess (C.state i) (C.state i) = true)
    (hRows : ∀ i, ∃ row, localMoves (referenceMoves refs) (C.state i) = some row ∧
      row.filterMap observableMove = (C.moves i).map (fun e => (e.1, C.state e.2)))
    (hOrder : ∀ i, i = 0 ∨ ∃ j l, j < i ∧ (l, i) ∈ C.moves j) :
    checkNormalization G C = true := by
  unfold checkNormalization
  rw [hRefs]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hRoot, ?_⟩, ?_⟩
  · intro i
    obtain ⟨row, hLocal, hRow⟩ := hRows i
    simp only [checkRow, hLocal, rowMatches, hRow, Bool.and_eq_true,
      List.all_eq_true, List.any_eq_true, agrees, decide_eq_true_eq]
    constructor
    · intro m hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      exact ⟨e, he, rfl, hComparable _⟩
    · intro e he
      exact ⟨_, List.mem_map.mpr ⟨e, he, rfl⟩, rfl, hComparable _⟩
  · intro i
    rcases hOrder i with hi | ⟨j, l, hlt, he⟩
    · exact Or.inl hi
    · exact Or.inr ⟨j, hlt, List.any_eq_true.mpr ⟨(l, i), he, by simp⟩⟩

/-- The validated table is exact for all histories and each of its
    transitions can occur for some packet lists. -/
structure NormalizationExact {n : Nat} (G : ProcessGraph)
    (C : NormalizationCandidate n) : Prop where
  root : G.root = C.state 0
  step (i : Fin (n + 1)) (pt hl : List CtxPkt) (a : Action) (q : GProc) (pt' hl' : List CtxPkt) :
    (actionAllowed Set.univ a ∧ GStep G ⟨C.state i, pt, hl⟩ a ⟨q, pt', hl'⟩) ↔
      ∃ l j, (l, j) ∈ C.moves i ∧ q = C.state j ∧
        MoveLabel.Realizes (.visible l) pt hl a pt' hl'
  enabled {i j : Fin (n + 1)} {l : SequentialLabel} :
    (l, j) ∈ C.moves i → l.enabled = true
  connected (i : Fin (n + 1)) :
    i = 0 ∨ ∃ j l, j < i ∧ (l, i) ∈ C.moves j

theorem checkNormalization_sound {n : Nat} {G : ProcessGraph} {C : NormalizationCandidate n}
    (h : checkNormalization G C = true) : NormalizationExact G C := by
  unfold checkNormalization at h
  split at h
  · contradiction
  rename_i rows hRows
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hRoot, hChecked⟩, hOrder⟩ := h
  have exactRows := buildReferenceRows_exact hRows (by simp [referenceMoves])
  have rowAt (i : Fin (n + 1)) :
      ∃ row, MovesExact G (C.state i) row ∧ rowMatches C i row = true := by
    have hi := hChecked i
    unfold checkRow at hi
    split at hi
    · contradiction
    · rename_i row hRow
      exact ⟨row, localMoves_exact exactRows hRow, hi⟩
  refine ⟨sameProcess_sound hRoot, ?_, ?_, ?_⟩
  · intro i pt hl a q pt' hl'
    obtain ⟨row, he, hm⟩ := rowAt i
    constructor
    · rintro ⟨ha, hs⟩
      obtain ⟨l, hMem, hr⟩ := (he ..).mp hs
      obtain ⟨k, rfl⟩ := realizes_visible hr ha
      obtain ⟨j, hj, hq⟩ := (rowMatches_exact hm k q).mp
        (mem_observable.mpr ⟨hMem, realizes_enabled hr⟩)
      exact ⟨k, j, hj, hq, hr⟩
    · rintro ⟨l, j, hj, rfl, hr⟩
      have hMem := (rowMatches_exact hm l (C.state j)).mpr ⟨j, hj, rfl⟩
      exact ⟨realizes_allowed hr, (he ..).mpr ⟨_, (mem_observable.mp hMem).1, hr⟩⟩
  · intro i j l hj
    obtain ⟨row, _, hm⟩ := rowAt i
    exact (mem_observable.mp ((rowMatches_exact hm l (C.state j)).mpr ⟨j, hj, rfl⟩)).2
  · intro i
    rcases hOrder i with hi | ⟨j, hlt, hEdge⟩
    · exact Or.inl hi
    · obtain ⟨⟨l, k⟩, hk, he⟩ := List.any_eq_true.mp hEdge
      have heq : k = i := of_decide_eq_true he
      subst k
      exact Or.inr ⟨j, l, hlt, hk⟩

private theorem NormalizationExact.edgeStep {n : Nat} {G : ProcessGraph}
    {C : NormalizationCandidate n} (h : NormalizationExact G C)
    {i j : Fin (n + 1)} {l : SequentialLabel} (he : (l, j) ∈ C.moves i) :
    RestrictedDerivativeStep G (C.state i) (C.state j) := by
  cases l with
  | rcfg x p =>
      obtain ⟨ha, hs⟩ := (h.step i [] [] (.rcfg x p) (C.state j) [] []).mpr
        ⟨_, j, he, rfl, .rcfg⟩
      exact ⟨[], [], _, [], [], ha, hs⟩
  | packet p =>
      have hNonzero : netkatIsZero p = false := by
        simpa [SequentialLabel.enabled] using (h.enabled he)
      obtain ⟨σ, τ, hSem⟩ := (netkatIsZero_false_iff_exists p).mp hNonzero
      have hHist := (historySemantics_iff_packetSemantics p σ τ [] []).mpr ⟨rfl, hSem⟩
      obtain ⟨ha, hs⟩ := (h.step i [σ] [] (.packet σ τ) (C.state j) [] [τ]).mpr
        ⟨_, j, he, rfl, .packet hHist⟩
      exact ⟨[σ], [], _, [], [τ], ha, hs⟩

theorem NormalizationExact.derivativeClosure {n : Nat} {G : ProcessGraph}
    {C : NormalizationCandidate n} (h : NormalizationExact G C) :
    DerivativeClosure G (Set.range C.state) := by
  constructor
  · exact ⟨0, h.root.symm⟩
  · rintro _ q ⟨i, rfl⟩ ⟨pt, hl, a, pt', hl', ha, hs⟩
    obtain ⟨l, j, _, hq, _⟩ := (h.step i pt hl a q pt' hl').mp ⟨ha, hs⟩
    exact ⟨j, hq.symm⟩
  · rintro _ ⟨i, rfl⟩
    induction i using (measure (fun i : Fin (n + 1) => i.val)).wf.induction with
    | h i ih =>
        rcases h.connected i with rfl | ⟨j, l, hlt, he⟩
        · rw [← h.root]
          exact .refl
        · exact (ih j hlt).tail (h.edgeStep he)

private theorem appendPending_step {G : ProcessGraph} {c d : GConfig} {a : Action}
    (h : GStep G c a d) (suffix : List CtxPkt) :
    GStep G { c with pending := c.pending ++ suffix } a
      { d with pending := d.pending ++ suffix } := by
  induction h with
  | seq_ok N p σ τ pt hl h => exact .seq_ok N p σ τ (pt ++ suffix) hl h
  | recv => exact .recv _ _ _ _ _
  | send => exact .send _ _ _ _ _
  | rcfg => exact .rcfg _ _ _ _ _
  | choice_l _ _ _ _ _ _ _ _ _ ih => exact .choice_l _ _ _ _ _ _ _ _ ih
  | choice_r _ _ _ _ _ _ _ _ _ ih => exact .choice_r _ _ _ _ _ _ _ _ ih
  | par_l _ _ _ _ _ _ _ _ _ ih => exact .par_l _ _ _ _ _ _ _ _ ih
  | par_r _ _ _ _ _ _ _ _ _ ih => exact .par_r _ _ _ _ _ _ _ _ ih
  | left_merge _ _ _ _ _ _ _ _ _ ih => exact .left_merge _ _ _ _ _ _ _ _ ih
  | comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_recv_send _ _ _ _ _ _ _ _ ih₁ ih₂
  | comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_send_recv _ _ _ _ _ _ _ _ ih₁ ih₂
  | sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .sync_recv_send _ _ _ _ _ _ _ _ ih₁ ih₂
  | sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .sync_send_recv _ _ _ _ _ _ _ _ ih₁ ih₂
  | var _ _ _ _ _ _ _ _ ih => exact .var _ _ _ _ _ _ _ ih
  | project _ _ _ _ _ _ _ _ _ ih => exact .project _ _ _ _ _ _ _ _ ih
  | restrict _ _ _ _ _ _ _ _ ha _ ih => exact .restrict _ _ _ _ _ _ _ _ ha ih

private theorem appendPending_steps {G : ProcessGraph} {c d : GConfig} {acts : List Action}
    (h : GSteps G c acts d) (suffix : List CtxPkt) :
    GSteps G { c with pending := c.pending ++ suffix } acts
      { d with pending := d.pending ++ suffix } := by
  induction h with
  | nil => exact .nil _
  | cons _ _ _ _ _ hs _ ih => exact .cons _ _ _ _ _ (appendPending_step hs suffix) ih

private theorem appendStep {G : ProcessGraph} {c d e : GConfig} {acts : List Action} {a : Action}
    (h : GSteps G c acts d) (hs : GStep G d a e) :
    GSteps G c (acts ++ [a]) e := by
  induction h with
  | nil => exact .cons _ _ _ _ _ hs (.nil _)
  | cons _ _ _ _ _ hf _ ih => exact .cons _ _ _ _ _ hf (ih hs)

private def pendingFor (a : Action) (pt : List CtxPkt) : List CtxPkt :=
  match a with
  | .packet σ _ => σ :: pt
  | _ => pt

private def handledAfter (a : Action) (hl : List CtxPkt) : List CtxPkt :=
  match a with
  | .packet _ τ => τ :: hl
  | _ => hl

private theorem rebaseStep {G : ProcessGraph} {c d : GConfig} {a : Action}
    (h : GStep G c a d) (pt hl : List CtxPkt) :
    GStep G ⟨c.proc, pendingFor a pt, hl⟩ a ⟨d.proc, pt, handledAfter a hl⟩ := by
  induction h with
  | seq_ok N p σ τ _ _ h => exact .seq_ok N p σ τ pt hl h
  | recv => exact .recv _ _ _ pt hl
  | send => exact .send _ _ _ pt hl
  | rcfg => exact .rcfg _ _ _ pt hl
  | choice_l _ _ _ _ _ _ _ _ _ ih => exact .choice_l _ _ _ _ _ _ _ _ ih
  | choice_r _ _ _ _ _ _ _ _ _ ih => exact .choice_r _ _ _ _ _ _ _ _ ih
  | par_l _ _ _ _ _ _ _ _ _ ih => exact .par_l _ _ _ _ _ _ _ _ ih
  | par_r _ _ _ _ _ _ _ _ _ ih => exact .par_r _ _ _ _ _ _ _ _ ih
  | left_merge _ _ _ _ _ _ _ _ _ ih => exact .left_merge _ _ _ _ _ _ _ _ ih
  | comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_recv_send _ _ _ _ _ _ pt hl ih₁ ih₂
  | comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_send_recv _ _ _ _ _ _ pt hl ih₁ ih₂
  | sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .sync_recv_send _ _ _ _ _ _ pt hl ih₁ ih₂
  | sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .sync_send_recv _ _ _ _ _ _ pt hl ih₁ ih₂
  | var _ _ _ _ _ _ _ _ ih => exact .var _ _ _ _ _ _ _ ih
  | project _ _ _ _ _ _ _ _ _ ih => exact .project _ _ _ _ _ _ _ _ ih
  | restrict _ _ _ _ _ _ _ _ ha _ ih => exact .restrict _ _ _ _ _ _ _ _ ha ih

private theorem restrictedTrace_derivative {G : ProcessGraph} {c d : GConfig}
    {acts : List Action} (h : GSteps G c acts d) :
    ∀ p, c.proc = .restrict Set.univ p →
      ∃ q, d.proc = .restrict Set.univ q ∧ Relation.ReflTransGen (RestrictedDerivativeStep G) p q := by
  induction h with
  | nil c => exact fun p hp => ⟨p, hp, .refl⟩
  | cons c c' d a acts hs ht ih =>
      intro p hp
      cases c with
      | mk u pt hl =>
        cases c' with
        | mk v pt' hl' =>
          change u = .restrict Set.univ p at hp
          subst u
          cases hs with
          | restrict _ _ v _ _ _ _ _ ha hs =>
            obtain ⟨q, hq, hPath⟩ := ih v rfl
            exact ⟨q, hq, hPath.head ⟨pt, hl, a, pt', hl', ha, hs⟩⟩

/-- Projected reachability is exact. Every path can run with one initial
    pending list and an empty handled list. Each packet step consumes its
    next input, and all other steps leave both lists intact. -/
theorem reachableDerivative_iff_trace {G : ProcessGraph} {p : GProc} :
    ReachableDerivative G p ↔
      ∃ pt acts hl, GSteps G ⟨.restrict Set.univ G.root, pt, []⟩ acts
        ⟨.restrict Set.univ p, [], hl⟩ := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], [], [], .nil _⟩
    | @tail q r hPath hStep ih =>
        obtain ⟨pt, acts, hl, hTrace⟩ := ih
        obtain ⟨_, _, a, _, _, ha, hs⟩ := hStep
        let next := pendingFor a []
        have extended : GSteps G ⟨.restrict Set.univ G.root, pt ++ next, []⟩ acts
            ⟨.restrict Set.univ q, next, hl⟩ := appendPending_steps hTrace next
        have nextStep : GStep G ⟨.restrict Set.univ q, next, hl⟩ a
            ⟨.restrict Set.univ r, [], handledAfter a hl⟩ :=
          .restrict Set.univ q r a next [] hl (handledAfter a hl) ha (rebaseStep hs [] hl)
        exact ⟨_, _, _, appendStep extended nextStep⟩
  · rintro ⟨pt, acts, hl, h⟩
    obtain ⟨q, hq, hr⟩ := restrictedTrace_derivative h G.root rfl
    cases hq
    exact hr

/-- Each certified state is reached by an actual restricted SOS trace. -/
theorem NormalizationExact.reachesTrace {n : Nat} {G : ProcessGraph}
    {C : NormalizationCandidate n} (h : NormalizationExact G C) (i : Fin (n + 1)) :
    ∃ pt acts hl, GSteps G ⟨.restrict Set.univ G.root, pt, []⟩ acts
      ⟨.restrict Set.univ (C.state i), [], hl⟩ :=
  reachableDerivative_iff_trace.mp (h.derivativeClosure.reachable ⟨i, rfl⟩)

theorem checkNormalization_finite {n : Nat} {G : ProcessGraph} {C : NormalizationCandidate n}
    (h : checkNormalization G C = true) : HasFiniteDerivatives G :=
  ⟨Set.range C.state, Set.finite_range _, (checkNormalization_sound h).derivativeClosure⟩

/-- The exact extra obligations of the Boolean validator. Each reachable
    derivative must admit a structural comparison and a symbolic row
    from one checked reference order. -/
def NormalizationAdmissible (G : ProcessGraph) : Prop :=
  (∀ p, ReachableDerivative G p → sameProcess p p = true) ∧
  ∃ order refs, buildReferenceRows G order [] = some refs ∧
    ∀ p, ReachableDerivative G p → ∃ row, localMoves (referenceMoves refs) p = some row

/-- The Boolean checker's domain, expressed without running its row
    computation. Only the reachable terms and the reference bodies
    demanded by the selected order need satisfy these conditions. -/
theorem normalizationAdmissible_iff (G : ProcessGraph) :
    NormalizationAdmissible G ↔
      (∀ p, ReachableDerivative G p → restrictionFree p) ∧
      ∃ order, ReferenceOrderAdmissible G ∅ order ∧
        ∀ p, ReachableDerivative G p → MoveAdmissible (· ∈ order.toFinset) p := by
  have rowsFor {order : List NodeId} {refs : ReferenceRows}
      (h : buildReferenceRows G order [] = some refs) (p : GProc) :
      (∃ row, localMoves (referenceMoves refs) p = some row) ↔
        MoveAdmissible (· ∈ order.toFinset) p := by
    apply (localMoves_exists_iff ..).trans
    apply MoveAdmissible.congr
    intro i
    rw [referenceMoves_exists_iff, buildReferenceRows_keys h]
    simp
  constructor
  · rintro ⟨hc, order, refs, hRefs, hLocal⟩
    refine ⟨fun p hp => (sameProcess_self_iff p).mp (hc p hp), order, ?_,
      fun p hp => (rowsFor hRefs p).mp (hLocal p hp)⟩
    simpa using (buildReferenceRows_exists_iff G order []).mp ⟨refs, hRefs⟩
  · rintro ⟨hc, order, hOrder, hLocal⟩
    obtain ⟨refs, hRefs⟩ := (buildReferenceRows_exists_iff G order []).mpr (by simpa using hOrder)
    exact ⟨fun p hp => (sameProcess_self_iff p).mpr (hc p hp), order, refs, hRefs,
      fun p hp => (rowsFor hRefs p).mpr (hLocal p hp)⟩

private theorem checkNormalization_admissible {n : Nat} {G : ProcessGraph}
    {C : NormalizationCandidate n} (h : checkNormalization G C = true) :
    NormalizationAdmissible G := by
  have he := checkNormalization_sound h
  have inRange (p : GProc) := (he.derivativeClosure.mem_iff p).mpr
  unfold checkNormalization at h
  split at h
  · contradiction
  rename_i refs hRefs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hRoot, hRows⟩, _⟩ := h
  have rows (i : Fin (n + 1)) :
      ∃ row, localMoves (referenceMoves refs) (C.state i) = some row ∧ rowMatches C i row = true := by
    have hi := hRows i
    unfold checkRow at hi
    split at hi
    · contradiction
    · exact ⟨_, by assumption, hi⟩
  constructor
  · intro p hp
    obtain ⟨i, rfl⟩ := inRange p hp
    rcases he.connected i with rfl | ⟨j, l, _, hj⟩
    · simpa only [he.root] using hRoot
    · obtain ⟨row, _, hm⟩ := rows j
      simp only [rowMatches, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, agrees] at hm
      obtain ⟨m, _, _, hSame⟩ := hm.2 (l, i) hj
      simpa only [sameProcess_sound hSame] using hSame
  · refine ⟨_, refs, hRefs, ?_⟩
    intro p hp
    obtain ⟨i, rfl⟩ := inRange p hp
    obtain ⟨row, hRow, _⟩ := rows i
    exact ⟨row, hRow⟩

private theorem MovesExact.observableStep {G : ProcessGraph} {p q : GProc}
    {row : List SymbolicMove} (h : MovesExact G p row) :
    RestrictedDerivativeStep G p q ↔ ∃ l, (l, q) ∈ row.filterMap observableMove := by
  constructor
  · rintro ⟨pt, hl, a, pt', hl', ha, hs⟩
    obtain ⟨l, hm, hr⟩ := (h ..).mp hs
    obtain ⟨k, rfl⟩ := realizes_visible hr ha
    exact ⟨k, mem_observable.mpr ⟨hm, realizes_enabled hr⟩⟩
  · rintro ⟨l, hm⟩
    obtain ⟨hm, hen⟩ := mem_observable.mp hm
    cases l with
    | rcfg x p =>
        exact ⟨[], [], .rcfg x p, [], [], trivial, (h ..).mpr ⟨_, hm, .rcfg⟩⟩
    | packet p =>
        have hz : netkatIsZero p = false := by simpa [SequentialLabel.enabled] using hen
        obtain ⟨σ, τ, hsem⟩ := (netkatIsZero_false_iff_exists p).mp hz
        have hh := (historySemantics_iff_packetSemantics p σ τ [] []).mpr ⟨rfl, hsem⟩
        exact ⟨[σ], [], .packet σ τ, [], [τ], trivial, (h ..).mpr ⟨_, hm, .packet hh⟩⟩

private structure OrderedDerivatives (G : ProcessGraph) {n : Nat}
    (state : Fin (n + 1) → GProc) : Prop where
  root : state 0 = G.root
  injective : Function.Injective state
  reachable : ∀ i, ReachableDerivative G (state i)
  parent : ∀ i, i = 0 ∨ ∃ j, j < i ∧ RestrictedDerivativeStep G (state j) (state i)

private theorem includeDerivative {G : ProcessGraph} {p : GProc} (hp : ReachableDerivative G p) :
    ∀ {n : Nat} {state : Fin (n + 1) → GProc}, OrderedDerivatives G state →
      ∃ (m : Nat) (next : Fin (m + 1) → GProc), OrderedDerivatives G next ∧
        Set.range state ⊆ Set.range next ∧ p ∈ Set.range next := by
  classical
  induction hp with
  | refl =>
      intro n state h
      exact ⟨n, state, h, fun _ hx => hx, 0, h.root⟩
  | @tail q p hq hqp ih =>
      intro n state h
      obtain ⟨m, old, ho, hSub, j, rfl⟩ := ih h
      by_cases hp : p ∈ Set.range old
      · exact ⟨m, old, ho, hSub, hp⟩
      let next : Fin (m + 2) → GProc := Fin.lastCases p old
      have hOld (i : Fin (m + 1)) : next i.castSucc = old i := Fin.lastCases_castSucc ..
      have hLast : next (Fin.last (m + 1)) = p := Fin.lastCases_last ..
      have hZero : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := rfl
      refine ⟨m + 1, next, ⟨?_, ?_, ?_, ?_⟩, ?_, Fin.last (m + 1), hLast⟩
      · rw [← hZero, hOld, ho.root]
      · intro i k
        induction i using Fin.lastCases <;> induction k using Fin.lastCases
        · intro _; rfl
        · intro he
          rw [hLast, hOld] at he
          exact (hp ⟨_, he.symm⟩).elim
        · intro he
          rw [hOld, hLast] at he
          exact (hp ⟨_, he⟩).elim
        · intro he
          rw [hOld, hOld] at he
          exact congrArg Fin.castSucc (ho.injective he)
      · intro i
        induction i using Fin.lastCases with
        | last => rw [hLast]; exact hq.tail hqp
        | cast i => rw [hOld]; exact ho.reachable i
      · intro i
        induction i using Fin.lastCases with
        | last =>
            exact Or.inr ⟨j.castSucc, Fin.castSucc_lt_last _, by simpa only [hOld, hLast] using hqp⟩
        | cast i =>
            rcases ho.parent i with rfl | ⟨k, hki, hk⟩
            · exact Or.inl hZero
            · exact Or.inr ⟨k.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hki,
                by simpa only [hOld] using hk⟩
      · intro p hp
        obtain ⟨i, hi⟩ := hSub hp
        exact ⟨i.castSucc, (hOld i).trans hi⟩

private theorem orderedDerivatives_cover {G : ProcessGraph} (h : HasFiniteDerivatives G) :
    ∃ (n : Nat) (state : Fin (n + 1) → GProc), OrderedDerivatives G state ∧
      ∀ p, ReachableDerivative G p → p ∈ Set.range state := by
  classical
  obtain ⟨S, hf, hc⟩ := h
  have build (s : Finset GProc) (hs : ∀ p ∈ s, ReachableDerivative G p) :
      ∃ (n : Nat) (state : Fin (n + 1) → GProc), OrderedDerivatives G state ∧
        ∀ p ∈ s, p ∈ Set.range state := by
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨0, fun _ => G.root, ⟨rfl, ?_, fun _ => .refl, ?_⟩, by simp⟩
        · intro i j _
          have hi := i.isLt
          have hj := j.isLt
          exact Fin.ext (by omega)
        · intro i
          have hi := i.isLt
          exact Or.inl (Fin.ext (by change i.val = 0; omega))
    | @insert p s _ ih =>
        obtain ⟨n, state, hState, hCover⟩ := ih
          (fun q hq => hs q (Finset.mem_insert_of_mem hq))
        obtain ⟨m, next, hNext, hSub, hNew⟩ :=
          includeDerivative (hs p (Finset.mem_insert_self _ _)) hState
        refine ⟨m, next, hNext, ?_⟩
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hNew
        · exact hSub (hCover q hq)
  obtain ⟨n, state, hState, cover⟩ := build hf.toFinset
    (fun p hp => hc.reachable (hf.mem_toFinset.mp hp))
  exact ⟨n, state, hState, fun p hp => cover p (hf.mem_toFinset.mpr ((hc.mem_iff p).mpr hp))⟩

/-- Completeness of Boolean validation on its exact admissible domain.
    The proof orders the finite derivatives by discovery and uses the
    computed symbolic rows to construct the certificate. -/
theorem exists_checkedNormalization_iff (G : ProcessGraph) :
    (∃ (n : Nat) (C : NormalizationCandidate n), checkNormalization G C = true) ↔
      HasFiniteDerivatives G ∧ NormalizationAdmissible G := by
  classical
  constructor
  · rintro ⟨n, C, h⟩
    exact ⟨checkNormalization_finite h, checkNormalization_admissible h⟩
  · rintro ⟨hf, comparable, order, refs, hRefs, available⟩
    obtain ⟨n, state, hState, cover⟩ := orderedDerivatives_cover hf
    have hAvailable (i) := available (state i) (hState.reachable i)
    let rows (i : Fin (n + 1)) := Classical.choose (hAvailable i)
    have hRow (i) : localMoves (referenceMoves refs) (state i) = some (rows i) :=
      Classical.choose_spec (hAvailable i)
    have hExact (i) : MovesExact G (state i) (rows i) :=
      localMoves_exact (buildReferenceRows_exact hRefs (by simp [referenceMoves])) (hRow i)
    let target (p : GProc) : Fin (n + 1) :=
      if h : p ∈ Set.range state then Classical.choose h else 0
    have hTarget {i : Fin (n + 1)} {e : SequentialLabel × GProc}
        (hm : e ∈ (rows i).filterMap observableMove) : state (target e.2) = e.2 := by
      have hs := (hExact i).observableStep.mpr ⟨e.1, hm⟩
      have hIn := cover e.2 ((hState.reachable i).tail hs)
      rw [show target e.2 = Classical.choose hIn from dif_pos hIn]
      exact Classical.choose_spec hIn
    let C : NormalizationCandidate n :=
      ⟨order, state, fun i => ((rows i).filterMap observableMove).map fun e => (e.1, target e.2)⟩
    refine ⟨n, C, checkNormalization_of_rows hRefs ?_ (fun i => comparable _ (hState.reachable i)) ?_ ?_⟩
    · change sameProcess G.root (state 0) = true
      rw [hState.root]
      exact comparable _ .refl
    · intro i
      refine ⟨rows i, hRow i, ?_⟩
      change _ = (((rows i).filterMap observableMove).map _).map _
      rw [List.map_map]
      trans ((rows i).filterMap observableMove).map id
      · simp
      apply List.map_congr_left
      intro e he
      exact Prod.ext rfl (hTarget he).symm
    · intro i
      rcases hState.parent i with hi | ⟨j, hji, hStep⟩
      · exact Or.inl hi
      obtain ⟨l, hl⟩ := (hExact j).observableStep.mp hStep
      have he : target (state i) = i := hState.injective (hTarget hl)
      exact Or.inr ⟨j, l, hji, List.mem_map.mpr ⟨(l, state i), hl, by simp [he]⟩⟩

-- A finite derivative set also admits a semantic certificate. The finite
-- packet universe and the control labels in the syntax bound its alphabet.
private def eventLabels : GProc → Finset (Channel × NetKAT)
  | .recv x p q | .send x p q | .rcfgPrefix x p q => insert (x, p) (eventLabels q)
  | .nSeq _ q | .project _ q | .restrict _ q => eventLabels q
  | .choice p q | .parallel p q | .leftMerge p q | .commMerge p q =>
      eventLabels p ∪ eventLabels q
  | .ref _ | .deadlock => ∅

private def actionEvent : Action → Option (Channel × NetKAT)
  | .recv x p | .send x p | .rcfg x p => some (x, p)
  | .packet _ _ => none

private theorem stepEvent_mem {G : ProcessGraph} {src dst : GConfig} {a : Action}
    (hs : GStep G src a dst) {e : Channel × NetKAT} :
    gprocRefs src.proc ⊆ G.nodes → actionEvent a = some e →
      e ∈ eventLabels src.proc ∨ ∃ i ∈ G.nodes, e ∈ eventLabels (G.label i) := by
  induction hs with
  | seq_ok => intro _ h; cases h
  | recv | send | rcfg =>
      intro _ h
      cases h
      exact Or.inl (Finset.mem_insert_self _ _)
  | choice_l _ _ _ _ _ _ _ _ _ ih | par_l _ _ _ _ _ _ _ _ _ ih |
    left_merge _ _ _ _ _ _ _ _ _ ih =>
      intro hc he
      exact (ih (Finset.union_subset_iff.mp hc).1 he).imp (Finset.mem_union_left _) id
  | choice_r _ _ _ _ _ _ _ _ _ ih | par_r _ _ _ _ _ _ _ _ _ ih =>
      intro hc he
      exact (ih (Finset.union_subset_iff.mp hc).2 he).imp (Finset.mem_union_right _) id
  | sync_recv_send _ _ _ _ _ _ _ _ _ _ ih _ |
    sync_send_recv _ _ _ _ _ _ _ _ _ _ ih _ |
    comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih _ |
    comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih _ =>
      intro hc he
      exact (ih (Finset.union_subset_iff.mp hc).1 he).imp (Finset.mem_union_left _) id
  | project _ _ _ _ _ _ _ _ _ ih | restrict _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | var i _ _ _ _ _ _ _ ih =>
      intro hc he
      have hi := hc (Finset.mem_singleton_self i)
      rcases ih (G.closed i hi) he with hm | hm
      · exact Or.inr ⟨i, hi, hm⟩
      · exact Or.inr hm

private theorem reachable_closed {G : ProcessGraph} {p : GProc}
    (h : ReachableDerivative G p) : gprocRefs p ⊆ G.nodes := by
  induction h with
  | refl => exact G.root_closed
  | tail _ hs ih =>
      obtain ⟨_, _, _, _, _, _, hs⟩ := hs
      exact hs.closed ih

private theorem stepHistory {G : ProcessGraph} {c d : GConfig} {a : Action}
    (hs : GStep G c a d) :
    c.pending = pendingFor a d.pending ∧ d.handled = handledAfter a c.handled := by
  induction hs <;> first | exact ⟨rfl, rfl⟩ | assumption

private abbrev GroundMove := (CtxPkt × CtxPkt) ⊕ (Channel × NetKAT)

private def groundAction : GroundMove → Action
  | .inl (σ, τ) => .packet σ τ
  | .inr (x, p) => .rcfg x p

private def groundLabel : GroundMove → SequentialLabel
  | .inl (σ, τ) => .packet (NormalForm.ofSummand (σ, τ))
  | .inr (x, p) => .rcfg x p

private theorem groundRealizes (b : GroundMove) (pt hl : List CtxPkt) (a : Action)
    (pt' hl' : List CtxPkt) :
    MoveLabel.Realizes (.visible (groundLabel b)) pt hl a pt' hl' ↔
      a = groundAction b ∧ pt = pendingFor a pt' ∧ hl' = handledAfter a hl := by
  rcases b with ⟨σ, τ⟩ | ⟨x, p⟩
  · constructor
    · intro h
      cases h with
      | packet hh =>
          have hsem := (historySemantics_iff_packetSemantics _ _ _ [] []).mp hh
          obtain ⟨hσ, hτ⟩ := (ofSummand_sem σ τ _ _).mp hsem.2
          cases (holdsComplete_iff_eq _ _).mp hσ
          cases hτ
          exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      apply MoveLabel.Realizes.packet
      apply (historySemantics_iff_packetSemantics _ _ _ [] []).mpr
      exact ⟨rfl, (ofSummand_sem σ τ σ τ).mpr ⟨(holdsComplete_iff_eq ..).mpr rfl, rfl⟩⟩
  · constructor
    · intro h
      cases h
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact .rcfg

private theorem groundAllowed (b : GroundMove) : actionAllowed Set.univ (groundAction b) := by
  cases b <;> exact trivial

private def alphabet (G : ProcessGraph) (p : GProc) : Set GroundMove :=
  Set.range (Sum.inl : CtxPkt × CtxPkt → GroundMove) ∪
    Sum.inr '' ↑(eventLabels p ∪ G.nodes.biUnion (eventLabels ∘ G.label))

private theorem alphabet_finite (G : ProcessGraph) (p : GProc) : (alphabet G p).Finite :=
  (Set.finite_range _).union ((Finset.finite_toSet _).image _)

private theorem alphabet_complete {G : ProcessGraph} {src dst : GConfig} {a : Action}
    (hs : GStep G src a dst) (hc : gprocRefs src.proc ⊆ G.nodes)
    (ha : actionAllowed Set.univ a) :
    ∃ b ∈ alphabet G src.proc, a = groundAction b := by
  cases a with
  | packet σ τ =>
      exact ⟨.inl (σ, τ), Or.inl ⟨(σ, τ), rfl⟩, rfl⟩
  | send | recv => simp [actionAllowed] at ha
  | rcfg x p =>
      refine ⟨.inr (x, p), Or.inr ⟨(x, p), ?_, rfl⟩, rfl⟩
      rcases stepEvent_mem hs hc (show actionEvent (.rcfg x p) = some (x, p) from rfl) with
        hm | ⟨i, hi, hm⟩
      · exact Finset.mem_union_left _ hm
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hm⟩)

/-- Every finite restricted derivative system admits a proof-checked
    certificate. This is a classical existence result. It enumerates
    ground packet actions and syntactically available reconfigurations,
    then retains the actual SOS transitions. -/
theorem exists_exactNormalization_iff (G : ProcessGraph) :
    (∃ (n : Nat) (C : NormalizationCandidate n), NormalizationExact G C) ↔
      HasFiniteDerivatives G := by
  classical
  constructor
  · rintro ⟨n, C, h⟩
    exact ⟨_, Set.finite_range C.state, h.derivativeClosure⟩
  · intro hf
    obtain ⟨n, state, hState, cover⟩ := orderedDerivatives_cover hf
    let runs (i j : Fin (n + 1)) (b : GroundMove) :=
      ∃ pt hl pt' hl', GStep G ⟨state i, pt, hl⟩ (groundAction b) ⟨state j, pt', hl'⟩
    let table (i : Fin (n + 1)) :=
      ((alphabet_finite G (state i)).toFinset.product (Finset.univ : Finset (Fin (n + 1)))).filter
        (fun e => runs i e.2 e.1)
    have tableMem (i j : Fin (n + 1)) (b : GroundMove) :
        (b, j) ∈ table i ↔ runs i j b := by
      simp only [table, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      refine ⟨And.right, fun h => ⟨?_, h⟩⟩
      obtain ⟨pt, hl, pt', hl', hs⟩ := h
      obtain ⟨b', hm, he⟩ := alphabet_complete hs (reachable_closed (hState.reachable i)) (groundAllowed b)
      have hEq : b = b' := by
        rcases b with ⟨σ, τ⟩ | ⟨x, p⟩ <;> rcases b' with ⟨ν, ρ⟩ | ⟨y, q⟩ <;>
          cases he <;> rfl
      exact Finset.mem_product.mpr
        ⟨(alphabet_finite G (state i)).mem_toFinset.mpr (hEq ▸ hm), Finset.mem_univ _⟩
    let C : NormalizationCandidate n :=
      ⟨[], state, fun i => (table i).toList.map fun e => (groundLabel e.1, e.2)⟩
    have moveMem (i j : Fin (n + 1)) (l : SequentialLabel) :
        (l, j) ∈ C.moves i ↔ ∃ b, runs i j b ∧ groundLabel b = l := by
      change (l, j) ∈ List.map _ (table i).toList ↔ _
      simp only [List.mem_map, Finset.mem_toList]
      constructor
      · rintro ⟨⟨b, k⟩, hm, he⟩
        cases he
        exact ⟨b, (tableMem ..).mp hm, rfl⟩
      · rintro ⟨b, hr, rfl⟩
        exact ⟨(b, j), (tableMem ..).mpr hr, rfl⟩
    refine ⟨n, C, ⟨hState.root.symm, ?_, ?_, ?_⟩⟩
    · intro i pt hl a q pt' hl'
      constructor
      · rintro ⟨ha, hs⟩
        have hReach := (hState.reachable i).tail ⟨pt, hl, a, pt', hl', ha, hs⟩
        obtain ⟨j, rfl⟩ := cover q hReach
        obtain ⟨b, _, rfl⟩ := alphabet_complete hs (reachable_closed (hState.reachable i)) ha
        obtain ⟨hp, hh⟩ := stepHistory hs
        exact ⟨groundLabel b, j, (moveMem ..).mpr ⟨b, ⟨pt, hl, pt', hl', hs⟩, rfl⟩, rfl,
          (groundRealizes ..).mpr ⟨rfl, hp, hh⟩⟩
      · rintro ⟨l, j, hm, rfl, hr⟩
        obtain ⟨b, ⟨_, _, _, _, hs⟩, rfl⟩ := (moveMem ..).mp hm
        obtain ⟨rfl, rfl, rfl⟩ := (groundRealizes ..).mp hr
        exact ⟨groundAllowed b, rebaseStep hs pt' hl⟩
    · intro i j l hm
      obtain ⟨b, _, rfl⟩ := (moveMem ..).mp hm
      exact realizes_enabled ((groundRealizes b (pendingFor (groundAction b) []) []
        (groundAction b) [] (handledAfter (groundAction b) [])).mpr ⟨rfl, rfl, rfl⟩)
    · intro i
      rcases hState.parent i with hi | ⟨j, hji, pt, hl, a, pt', hl', ha, hs⟩
      · exact Or.inl hi
      obtain ⟨b, _, rfl⟩ := alphabet_complete hs (reachable_closed (hState.reachable j)) ha
      exact Or.inr ⟨j, groundLabel b, hji, (moveMem ..).mpr ⟨b, ⟨pt, hl, pt', hl', hs⟩, rfl⟩⟩

private def stateNode {n : Nat} (i : Fin (n + 1)) : NodeId := auxNode i.val

private def edgePrefix (l : SequentialLabel) (q : GProc) : GProc :=
  match l with
  | .packet p => .nSeq p q
  | .rcfg x p => .rcfgPrefix x p q

private def renderRow {n : Nat} : List (SequentialLabel × Fin (n + 1)) → GProc
  | [] => .deadlock
  | (l, j) :: rest => .choice (edgePrefix l (.ref (stateNode j))) (renderRow rest)

private def stateNodes (n : Nat) : Finset NodeId :=
  (Finset.univ : Finset (Fin (n + 1))).image stateNode

private theorem stateNode_mem {n : Nat} (i : Fin (n + 1)) : stateNode i ∈ stateNodes n :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem renderRow_closed {n : Nat} (row : List (SequentialLabel × Fin (n + 1))) :
    gprocRefs (renderRow row) ⊆ stateNodes n := by
  induction row with
  | nil => simp [renderRow, gprocRefs]
  | cons edge rest ih =>
      obtain ⟨l, j⟩ := edge
      cases l <;>
        simpa only [renderRow, edgePrefix, gprocRefs, Finset.union_subset_iff,
          Finset.singleton_subset_iff] using And.intro (stateNode_mem j) ih

private def sequentialLabel {n : Nat} (C : NormalizationCandidate n) : NodeId → GProc
  | .inl _ => .deadlock
  | .inr k =>
      if hk : k < n + 1 then renderRow (C.moves ⟨k, hk⟩) else .deadlock

private theorem sequentialLabel_stateNode {n : Nat} (C : NormalizationCandidate n)
    (i : Fin (n + 1)) :
    sequentialLabel C (stateNode i) = renderRow (C.moves i) := by
  simp [sequentialLabel, stateNode, auxNode, i.isLt]

private def sequentialGraph {n : Nat} (C : NormalizationCandidate n) : ProcessGraph where
  nodes := stateNodes n
  root := .ref (stateNode (0 : Fin (n + 1)))
  label := sequentialLabel C
  root_closed := Finset.singleton_subset_iff.mpr (stateNode_mem _)
  closed := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    rw [sequentialLabel_stateNode]
    exact renderRow_closed _

private theorem sequentialGraph_supported {n : Nat} (C : NormalizationCandidate n) :
    GraphHeadSupported (sequentialGraph C) ∧ GraphTailSupported (sequentialGraph C) := by
  have shape (row : List (SequentialLabel × Fin (n + 1))) :
      TailShapeOk (sequentialGraph C) (renderRow row) := by
    induction row with
    | nil => exact .deadlock
    | cons edge rest ih =>
        obtain ⟨l, j⟩ := edge
        have href : TailShapeOk (sequentialGraph C) (.ref (stateNode j)) := .ref (stateNode_mem j)
        cases l
        · exact .choice (.nSeq href) ih
        · exact .choice (.rcfgPrefix href) ih
  apply graphSupported_of_shapes (.ref (stateNode_mem _))
  intro k hk
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
  change TailShapeOk (sequentialGraph C) (sequentialLabel C (stateNode i))
  rw [sequentialLabel_stateNode]
  exact shape _

private theorem localMoves_renderRow {n : Nat} (row : List (SequentialLabel × Fin (n + 1))) :
    localMoves (fun _ => none) (renderRow row) =
      some (row.map fun (l, j) => (.visible l, .ref (stateNode j))) := by
  induction row with
  | nil => rfl
  | cons edge rest ih =>
      obtain ⟨l, j⟩ := edge
      cases l <;> simp [renderRow, edgePrefix, localMoves, ih]

private theorem sequentialGraph_step {n : Nat} (C : NormalizationCandidate n)
    (i : Fin (n + 1)) (pt hl : List CtxPkt) (a : Action) (q : GProc) (pt' hl' : List CtxPkt) :
    GStep (sequentialGraph C) ⟨.ref (stateNode i), pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
      ∃ l j, (l, j) ∈ C.moves i ∧ q = .ref (stateNode j) ∧
        MoveLabel.Realizes (.visible l) pt hl a pt' hl' := by
  have href : GStep (sequentialGraph C) ⟨.ref (stateNode i), pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
      GStep (sequentialGraph C) ⟨renderRow (C.moves i), pt, hl⟩ a ⟨q, pt', hl'⟩ := by
    have label : (sequentialGraph C).label (stateNode i) = renderRow (C.moves i) :=
      sequentialLabel_stateNode C i
    exact ⟨fun h => label ▸ gstep_ref_inv h,
      fun h => .var _ _ _ _ _ _ _ (label.symm ▸ h)⟩
  have hExact := localMoves_exact (G := sequentialGraph C) (by simp) (localMoves_renderRow (C.moves i))
  rw [href, hExact]
  constructor
  · rintro ⟨l, hm, hr⟩
    obtain ⟨⟨k, j⟩, he, hEq⟩ := List.mem_map.mp hm
    cases hEq
    exact ⟨k, j, he, rfl, hr⟩
  · rintro ⟨l, j, hm, rfl, hr⟩
    exact ⟨_, List.mem_map.mpr ⟨(l, j), hm, rfl⟩, hr⟩

/-- The two-graph form of the SOS step matching used by `IsGBisimulation`. -/
def GraphMatches (G Q : ProcessGraph) (R : GProc → GProc → Prop) : Prop :=
  ∀ p q, R p q →
    ∀ (pt hl : List CtxPkt) (a : Action) (p' : GProc) (pt' hl' : List CtxPkt),
      GStep G ⟨p, pt, hl⟩ a ⟨p', pt', hl'⟩ →
      ∃ q', GStep Q ⟨q, pt, hl⟩ a ⟨q', pt', hl'⟩ ∧ R p' q'

theorem GraphMatches.traces {G Q : ProcessGraph} {R : GProc → GProc → Prop}
    (h : GraphMatches G Q R) {c d : GConfig} {acts : List Action} (hs : GSteps G c acts d) :
    ∀ q, R c.proc q → ∃ q', GSteps Q ⟨q, c.pending, c.handled⟩ acts
      ⟨q', d.pending, d.handled⟩ ∧ R d.proc q' := by
  induction hs with
  | nil c => exact fun q hq => ⟨q, .nil _, hq⟩
  | cons c c' d a acts hs _ ih =>
      intro q hq
      obtain ⟨v, hv, hRv⟩ := h c.proc q hq c.pending c.handled a c'.proc c'.pending c'.handled
        (by cases c; cases c'; exact hs)
      obtain ⟨q', hq', hR⟩ := ih v hRv
      exact ⟨q', .cons _ _ _ _ _ hv hq', hR⟩

def GraphBisimilarBetween (G Q : ProcessGraph) (p q : GProc) : Prop :=
  ∃ R, R p q ∧ GraphMatches G Q R ∧ GraphMatches Q G (fun v u => R u v)

theorem graphBisimilarBetween_same {G : ProcessGraph} {p q : GProc} :
    GraphBisimilarBetween G G p q ↔ GBisimilar G p q := by
  constructor
  · rintro ⟨R, hpq, hf, hb⟩
    refine ⟨fun u v => R u v ∨ R v u, ⟨?_, ?_⟩, Or.inl hpq⟩
    · exact fun _ _ h => h.symm
    · rintro u v (h | h) pt hl a u' pt' hl' hs
      · obtain ⟨v', hv, hr⟩ := hf u v h pt hl a u' pt' hl' hs
        exact ⟨v', hv, Or.inl hr⟩
      · obtain ⟨v', hv, hr⟩ := hb u v h pt hl a u' pt' hl' hs
        exact ⟨v', hv, Or.inr hr⟩
  · rintro ⟨R, ⟨hSym, hStep⟩, hpq⟩
    refine ⟨R, hpq, hStep, ?_⟩
    intro u v h pt hl a u' pt' hl' hs
    obtain ⟨v', hv, hr⟩ := hStep u v (hSym _ _ h) pt hl a u' pt' hl' hs
    exact ⟨v', hv, hSym _ _ hr⟩

private theorem NormalizationExact.bisimilar {n : Nat} {G : ProcessGraph}
    {C : NormalizationCandidate n} (h : NormalizationExact G C) :
    GraphBisimilarBetween G (sequentialGraph C) (.restrict Set.univ G.root)
      (sequentialGraph C).root := by
  let R : GProc → GProc → Prop := fun p q =>
    ∃ i : Fin (n + 1), p = .restrict Set.univ (C.state i) ∧ q = .ref (stateNode i)
  refine ⟨R, ⟨0, congrArg (GProc.restrict Set.univ) h.root, rfl⟩, ?_, ?_⟩
  · rintro p q ⟨i, rfl, rfl⟩ pt hl a p' pt' hl' hs
    cases hs with
    | restrict _ _ u _ _ _ _ _ ha hs =>
        obtain ⟨l, j, hm, rfl, hr⟩ := (h.step i pt hl a u pt' hl').mp ⟨ha, hs⟩
        exact ⟨_, (sequentialGraph_step C i pt hl a _ pt' hl').mpr
          ⟨l, j, hm, rfl, hr⟩, j, rfl, rfl⟩
  · rintro q p ⟨i, rfl, rfl⟩ pt hl a q' pt' hl' hs
    obtain ⟨l, j, hm, rfl, hr⟩ := (sequentialGraph_step C i pt hl a q' pt' hl').mp hs
    obtain ⟨ha, hs⟩ := (h.step i pt hl a (C.state j) pt' hl').mpr ⟨l, j, hm, rfl, hr⟩
    exact ⟨_, .restrict Set.univ _ _ a pt pt' hl hl' ha hs, j, rfl, rfl⟩

/-- Render a table whose exactness is checked by Lean. This entry point
    allows proofs about the SOS in place of Boolean row validation. -/
def normalizeCertifiedGraph {n : Nat} {G : ProcessGraph}
    (C : NormalizationCandidate n) (_ : NormalizationExact G C) : ProcessGraph :=
  sequentialGraph C

theorem normalizeCertifiedGraph_correct {n : Nat} {G : ProcessGraph}
    {C : NormalizationCandidate n} (h : NormalizationExact G C) :
    let Q := normalizeCertifiedGraph C h
    DerivativeClosure G (Set.range C.state) ∧
      GraphBisimilarBetween G Q (.restrict Set.univ G.root) Q.root ∧
      GraphHeadSupported Q ∧ GraphTailSupported Q :=
  ⟨h.derivativeClosure, h.bisimilar, sequentialGraph_supported C⟩

/-- Run the existing safety checker on a proof-checked table. -/
def safetyCheckCertifiedGraph {n : Nat} {G : ProcessGraph}
    (C : NormalizationCandidate n) (h : NormalizationExact G C)
    (R : ReconfigSet) (ingress egress : NetKAT) : SafetyCheckResult :=
  safetyCheckGraph (normalizeCertifiedGraph C h) R ingress egress

theorem safetyCheckCertifiedGraph_correct {n : Nat} {G : ProcessGraph}
    {C : NormalizationCandidate n} (h : NormalizationExact G C)
    (R : ReconfigSet) (ingress egress : NetKAT) :
    let Q := normalizeCertifiedGraph C h
    let result := safetyCheckCertifiedGraph C h R ingress egress
    GraphBisimilarBetween G Q (.restrict Set.univ G.root) Q.root ∧
      (result.initialCondition = .isZero true ↔
        ¬ flowVia ingress egress (GraphHeadSpec Q Q.root)) ∧
      (result.postReconfigurationCondition = .nonzero true ↔
        flowVia ingress egress (GraphTailSpec Q R Q.root)) := by
  obtain ⟨_, hBisim, hHead, hTail⟩ := normalizeCertifiedGraph_correct h
  obtain ⟨_, _, _, _, _, _, hInitial, hPost⟩ :=
    safetyCheckGraph_correct (normalizeCertifiedGraph C h) R ingress egress hHead
      (graphTailSupported_implies_domain hTail)
  exact ⟨hBisim, hInitial, hPost⟩

inductive NormalizationError where
  | compilationFailed
  | invalidCertificate
  deriving DecidableEq, BEq, Repr

/-- Normalize a closed graph using a checked finite derivative table. -/
def normalizeGraph {n : Nat} (G : ProcessGraph) (C : NormalizationCandidate n) :
    Except NormalizationError ProcessGraph :=
  if checkNormalization G C then .ok (sequentialGraph C) else .error .invalidCertificate

theorem normalizeGraph_invalid_iff {n : Nat} (G : ProcessGraph) (C : NormalizationCandidate n) :
    normalizeGraph G C = .error .invalidCertificate ↔ checkNormalization G C = false := by
  unfold normalizeGraph
  split <;> simp_all

theorem normalizeGraph_correct {n : Nat} {G Q : ProcessGraph} {C : NormalizationCandidate n}
    (h : normalizeGraph G C = .ok Q) :
    DerivativeClosure G (Set.range C.state) ∧
      GraphBisimilarBetween G Q (.restrict Set.univ G.root) Q.root ∧
      GraphHeadSupported Q ∧ GraphTailSupported Q := by
  unfold normalizeGraph at h
  split at h
  · rename_i hc
    obtain rfl := Except.ok.inj h
    exact normalizeCertifiedGraph_correct (checkNormalization_sound hc)
  · contradiction

/-- Normalize and check (34) and (35) using the environment-free graph checker. -/
def normalizeAndSafetyCheckGraph {n : Nat} (G : ProcessGraph) (C : NormalizationCandidate n)
    (R : ReconfigSet) (ingress egress : NetKAT) : Except NormalizationError SafetyCheckResult :=
  (normalizeGraph G C).map fun Q => safetyCheckGraph Q R ingress egress

theorem normalizeAndSafetyCheckGraph_correct {n : Nat} {G Q : ProcessGraph}
    {C : NormalizationCandidate n} (h : normalizeGraph G C = .ok Q)
    (R : ReconfigSet) (ingress egress : NetKAT) :
    GraphBisimilarBetween G Q (.restrict Set.univ G.root) Q.root ∧
      ∃ result, normalizeAndSafetyCheckGraph G C R ingress egress = .ok result ∧
        (result.initialCondition = .isZero true ↔
          ¬ flowVia ingress egress (GraphHeadSpec Q Q.root)) ∧
        (result.postReconfigurationCondition = .nonzero true ↔
          flowVia ingress egress (GraphTailSpec Q R Q.root)) := by
  obtain ⟨_, hBisim, hHead, hTail⟩ := normalizeGraph_correct h
  obtain ⟨_, _, _, _, _, _, hInitial, hPost⟩ :=
    safetyCheckGraph_correct Q R ingress egress hHead (graphTailSupported_implies_domain hTail)
  exact ⟨hBisim, _, by simp [normalizeAndSafetyCheckGraph, h, Except.map], hInitial, hPost⟩

/-- Frontend for raw terms. The certificate describes derivatives of
    the compiled graph with its canonical reference identifiers. -/
def compileNormalizeAndSafetyCheckGraph {n : Nat} (env : RecEnv) (p : DyNetKAT)
    (support : Finset Var) (C : NormalizationCandidate n) (R : ReconfigSet)
    (ingress egress : NetKAT) : Except NormalizationError SafetyCheckResult :=
  match compileGraph env p support with
  | none => .error .compilationFailed
  | some G => normalizeAndSafetyCheckGraph G C R ingress egress

theorem compileNormalizeAndSafetyCheckGraph_correct {n : Nat} {env : RecEnv}
    {p : DyNetKAT} {support : Finset Var} {G Q : ProcessGraph}
    {C : NormalizationCandidate n} (hCompile : compileGraph env p support = some G)
    (hNormalize : normalizeGraph G C = .ok Q) (R : ReconfigSet) (ingress egress : NetKAT) :
    Corr G env p G.root ∧ GraphBisimilarBetween G Q (.restrict Set.univ G.root) Q.root ∧
      ∃ result, compileNormalizeAndSafetyCheckGraph env p support C R ingress egress = .ok result ∧
        (result.initialCondition = .isZero true ↔
          ¬ flowVia ingress egress (GraphHeadSpec Q Q.root)) ∧
        (result.postReconfigurationCondition = .nonzero true ↔
          flowVia ingress egress (GraphTailSpec Q R Q.root)) := by
  obtain ⟨hBisim, result, hResult, hInitial, hPost⟩ :=
    normalizeAndSafetyCheckGraph_correct hNormalize R ingress egress
  exact ⟨compileGraph_corr hCompile, hBisim, result,
    by simpa only [compileNormalizeAndSafetyCheckGraph, hCompile] using hResult, hInitial, hPost⟩

end DyNetKAT.DyNetKAT
