import KATLean.NetKAT.Guard
import KATLean.NetKAT.Packet

/-! A symbolic relation uses one-hot field bits in two banks. Composition
temporarily uses a third bank and projects it out of the diagram. -/

namespace KATLean.NetKAT.Symbolic

open Native.Boolean

variable {F V : Type}

/-- Executable enumeration of individual fields and individual values, and
an ordering for the bit variables. No enumeration of packets is required. -/
structure Schema (F V : Type) where
  fields : List F
  values : List V
  fields_complete : ∀ f, f ∈ fields
  values_complete : ∀ a, a ∈ values
  width : Nat
  index : ((F × V) × Fin 3) ≃ Fin width

namespace Schema

variable (s : Schema F V) [DecidableEq V]

abbrev Bits := Fin s.width → Bool
abbrev DiagramGuard := Guard s.width

private def bit (b : Fin 3) (f : F) (a : V) : Fin s.width := s.index ((f, a), b)

/-- A bank represents one packet when its bits are the exactly-one encoding
of each field's value. -/
def Matches (b : Fin 3) (v : s.Bits) (p : F → V) : Prop :=
  ∀ f a, v (s.bit b f a) = decide (p f = a)

theorem matches_unique {b : Fin 3} {v : s.Bits} {p q : F → V}
    (hp : s.Matches b v p) (hq : s.Matches b v q) : p = q := by
  funext f
  have h := (hp f (q f)).symm.trans (hq f (q f))
  simpa using h

/-- Encode selected packets into the three banks. This operation describes
a single valuation, for use in proofs relating diagrams to packets. -/
def encode (p : Fin 3 → F → V) : s.Bits := fun i =>
  let x := s.index.symm i
  decide (p x.2 x.1.1 = x.1.2)

theorem matches_encode (p : Fin 3 → F → V) (b : Fin 3) :
    s.Matches b (s.encode p) (p b) := by
  intro f a
  simp [encode, bit]

/-- A binary diagram accepts exactly the encodings of related packet pairs. -/
def Represents (g : s.DiagramGuard) (r : Rel (F → V)) : Prop :=
  ∀ v : s.Bits, eval g.1 v = true ↔
    ∃ p q, s.Matches 0 v p ∧ s.Matches 1 v q ∧ r.holds p q

private def decodeField (fallback : V) (b : Fin 3) (v : s.Bits) : F → V :=
  fun f => (s.values.find? (fun a => v (s.bit b f a))).getD fallback

private theorem decodeField_correct {b : Fin 3} {v : s.Bits} {p : F → V}
    (fallback : V) (h : s.Matches b v p) : s.decodeField fallback b v = p := by
  funext f
  unfold decodeField
  cases he : s.values.find? (fun a => v (s.bit b f a)) with
  | none =>
    have hn := List.find?_eq_none.mp he (p f) (s.values_complete (p f))
    exact False.elim (hn (by simp [h f (p f)]))
  | some a =>
    have ht : v (s.bit b f a) = true := List.find?_some (p := fun a => v (s.bit b f a)) he
    rw [h f a, decide_eq_true_eq] at ht
    exact ht.symm

private theorem matches_of_true_subset {b : Fin 3} {v w : s.Bits} {p q : F → V}
    (hp : s.Matches b v p) (hq : s.Matches b w q)
    (sub : ∀ i, w i = true → v i = true) : p = q := by
  funext f
  have h : v (s.bit b f (q f)) = true := sub _ (by simp [hq f (q f)])
  rwa [hp f (q f), decide_eq_true_eq] at h

section

variable [DecidableEq F]

/-- Cache the decoded fields once. Packet expressions can then read the
same packet repeatedly without following the decision path again. -/
private def decodeBank (fallback : V) (b : Fin 3) (v : s.Bits) : F → V :=
  let fields := s.fields.map fun f => (f, s.decodeField fallback b v f)
  fun f => (fields.lookup f).getD fallback

omit [DecidableEq V] in
private theorem lookup_fields (fields : List F) (p : F → V) (f : F) (h : f ∈ fields) :
    (fields.map fun g => (g, p g)).lookup f = some (p f) := by
  induction fields with
  | nil => simp at h
  | cons g gs ih =>
    by_cases e : f = g
    · subst g
      simp
    · have hm : f ∈ gs := by simpa [e] using h
      simp [List.lookup_cons, beq_false_of_ne e, ih hm]

private theorem decodeBank_correct {b : Fin 3} {v : s.Bits} {p : F → V}
    (fallback : V) (h : s.Matches b v p) : s.decodeBank fallback b v = p := by
  funext f
  simp only [decodeBank, s.decodeField_correct fallback h,
    lookup_fields _ _ _ (s.fields_complete f), Option.getD_some]

/-- Materialize only the packet pairs on accepting diagram paths.
The fallback is unreachable for represented relations. -/
def acceptedPairs (fallback : V) (g : s.DiagramGuard) : List ((F → V) × (F → V)) :=
  (Guard.acceptingReps g.1).map fun v =>
    (s.decodeBank fallback 0 v, s.decodeBank fallback 1 v)

theorem mem_acceptedPairs (fallback : V) {g : s.DiagramGuard} {r : Rel (F → V)}
    (h : s.Represents g r) (p q : F → V) :
    (p, q) ∈ s.acceptedPairs fallback g ↔ r.holds p q := by
  constructor
  · intro hm
    obtain ⟨w, hw, eq⟩ := List.mem_map.mp hm
    obtain ⟨a, b, ha, hb, step⟩ := (h w).mp (Guard.acceptingReps_sound hw)
    rw [s.decodeBank_correct fallback ha, s.decodeBank_correct fallback hb] at eq
    cases eq
    exact step
  · intro step
    let banks : Fin 3 → F → V := fun b => if b = 0 then p else q
    let v := s.encode banks
    have hp : s.Matches 0 v p := by simpa [v, banks] using s.matches_encode banks 0
    have hq : s.Matches 1 v q := by simpa [v, banks] using s.matches_encode banks 1
    obtain ⟨w, hw, sub⟩ := Guard.acceptingReps_complete v ((h v).mpr ⟨p, q, hp, hq, step⟩)
    obtain ⟨a, b, ha, hb, _⟩ := (h w).mp (Guard.acceptingReps_sound hw)
    exact List.mem_map.mpr ⟨w, hw, Prod.ext
      ((s.decodeBank_correct fallback ha).trans (s.matches_of_true_subset hp ha sub).symm)
      ((s.decodeBank_correct fallback hb).trans (s.matches_of_true_subset hq hb sub).symm)⟩

end

private def every (xs : List X) (f : X → Guard n) : Guard n :=
  xs.foldr (fun x acc => conj (f x) acc) truth

private def some (xs : List X) (f : X → Guard n) : Guard n :=
  xs.foldr (fun x acc => disj (f x) acc) falsity

private theorem eval_every (xs : List X) (f : X → Guard n) (v : Fin n → Bool) :
    eval (every xs f).1 v = true ↔ ∀ x ∈ xs, eval (f x).1 v = true := by
  induction xs with
  | nil => simp [every]
  | cons x xs ih =>
    change eval (conj (f x) (every xs f)).1 v = true ↔ _
    simp only [eval_conj, Bool.and_eq_true, ih, List.forall_mem_cons]

private theorem eval_some (xs : List X) (f : X → Guard n) (v : Fin n → Bool) :
    eval (some xs f).1 v = true ↔ ∃ x ∈ xs, eval (f x).1 v = true := by
  induction xs with
  | nil => simp [some]
  | cons x xs ih =>
    change eval (disj (f x) (some xs f)).1 v = true ↔ _
    simp only [eval_disj, Bool.or_eq_true, ih, List.mem_cons]
    aesop

/-- A symbolic field equality. The primitive relation constructors below
restrict these bits to the one-hot encodings. -/
def fieldTest (b : Fin 3) (f : F) (a : V) : s.DiagramGuard :=
  atom s.width (s.bit b f a)

omit [DecidableEq V] in
@[simp] theorem eval_fieldTest (b : Fin 3) (f : F) (a : V) (v : s.Bits) :
    eval (s.fieldTest b f a).1 v = v (s.bit b f a) := atom_correct _ _ _

theorem fieldTest_correct {v : s.Bits} {p : F → V} {b : Fin 3} (h : s.Matches b v p)
    (f : F) (a : V) :
    eval (s.fieldTest b f a).1 v = decide (p f = a) := by
  rw [eval_fieldTest, h]

private def fieldCode (b : Fin 3) (f : F) (a : V) : s.DiagramGuard :=
  every s.values (fun w => if a = w then s.fieldTest b f w else neg (s.fieldTest b f w))

private theorem fieldCode_correct (b : Fin 3) (f : F) (a : V) (v : s.Bits) :
    eval (s.fieldCode b f a).1 v = true ↔ ∀ w, v (s.bit b f w) = decide (a = w) := by
  rw [fieldCode, eval_every]
  constructor
  · intro h w
    specialize h w (s.values_complete w)
    by_cases hEq : a = w <;> simpa [hEq] using h
  · intro h w _
    by_cases hEq : a = w <;> simp [hEq, h]

private def fieldRelation (f : F) (allowed : V → V → Bool) : s.DiagramGuard :=
  some s.values (fun a =>
    conj (s.fieldCode 0 f a)
      (some s.values (fun b => if allowed a b then s.fieldCode 1 f b else falsity)))

private theorem fieldRelation_correct (f : F) (allowed : V → V → Bool) (v : s.Bits) :
    eval (s.fieldRelation f allowed).1 v = true ↔
      ∃ a b, (∀ w, v (s.bit 0 f w) = decide (a = w)) ∧
        (∀ w, v (s.bit 1 f w) = decide (b = w)) ∧ allowed a b = true := by
  simp only [fieldRelation, eval_some, eval_conj, Bool.and_eq_true, fieldCode_correct]
  constructor
  · rintro ⟨a, _, ha, b, _, h⟩
    cases he : allowed a b
    · simp [he] at h
    · exact ⟨a, b, ha, by simpa [he, fieldCode_correct] using h, he⟩
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨a, s.values_complete a, ha, b, s.values_complete b,
      by simpa [h, fieldCode_correct] using hb⟩

/-- Independent field transfers compose to a primitive packet relation.
Only the two values of one field are considered at a time. -/
def primitive (allowed : F → V → V → Bool) : s.DiagramGuard :=
  every s.fields (fun f => s.fieldRelation f (allowed f))

theorem primitive_correct (allowed : F → V → V → Bool) :
    s.Represents (s.primitive allowed) ⟨fun p q => ∀ f, allowed f (p f) (q f) = true⟩ := by
  intro v
  rw [primitive, eval_every]
  simp only [fieldRelation_correct]
  constructor
  · intro h
    classical
    have hall (f : F) := h f (s.fields_complete f)
    choose p q hp hq hrel using hall
    exact ⟨p, q, hp, hq, hrel⟩
  · rintro ⟨p, q, hp, hq, h⟩ f _
    exact ⟨p f, q f, hp f, hq f, h f⟩

def skip : s.DiagramGuard := s.primitive (fun _ a b => decide (a = b))

theorem skip_correct : s.Represents s.skip (1 : Rel (F → V)) := by
  intro v
  rw [skip, s.primitive_correct]
  simp only [Rel.one_holds, decide_eq_true_eq]
  exact ⟨fun ⟨p, q, hp, hq, h⟩ => ⟨p, q, hp, hq, funext h⟩,
    fun ⟨p, q, hp, hq, h⟩ => ⟨p, q, hp, hq, congrFun h⟩⟩

theorem drop_correct : s.Represents falsity (0 : Rel (F → V)) := by
  intro v
  simp

/-- Symbolic single-field update. Unwritten fields retain their values. -/
def assign [DecidableEq F] (f : F) (a : V) : s.DiagramGuard :=
  s.primitive (fun g x y => if f = g then decide (a = y) else decide (x = y))

theorem assign_correct [DecidableEq F] (model : PacketModel F (fun _ => V) (F → V))
    (lookup : ∀ f p, model.lookup f p = p f) (f : F) (a : V) :
    s.Represents (s.assign f a) (model.assign f a) := by
  intro v
  rw [assign, s.primitive_correct]
  simp only [PacketModel.assign_holds]
  have upd (p : F → V) (g : F) : model.update f a p g = if f = g then a else p g := by
    rw [← lookup g (model.update f a p)]
    split
    · next h => subst g; exact model.lookup_update f a p
    · next h => rw [model.lookup_update_other f g a p h, lookup]
  have equiv (p q : F → V) :
      (∀ g, (if f = g then decide (a = q g) else decide (p g = q g)) = true) ↔
        q = model.update f a p := by
    constructor
    · intro h
      funext g
      rw [upd]
      specialize h g
      by_cases he : f = g <;> simpa [he, eq_comm (a := q g)] using h
    · rintro rfl g
      rw [upd]
      by_cases h : f = g <;> simp [h]
  simp only [equiv]

theorem filter_correct {test : s.DiagramGuard} {pred : Set (F → V)}
    (h : ∀ v p, s.Matches 0 v p → (eval test.1 v = true ↔ p ∈ pred)) :
    s.Represents (conj s.skip test) (Rel.test pred) := by
  intro v
  simp only [eval_conj, Bool.and_eq_true, s.skip_correct v, Rel.one_holds, Rel.test]
  constructor
  · rintro ⟨⟨p, q, hp, hq, he⟩, ht⟩
    exact ⟨p, q, hp, hq, (h v p hp).mp ht, he⟩
  · rintro ⟨p, q, hp, hq, ht, he⟩
    exact ⟨⟨p, q, hp, hq, he⟩, (h v p hp).mpr ht⟩

theorem union_correct {g h : s.DiagramGuard} {r t : Rel (F → V)}
    (hg : s.Represents g r) (hh : s.Represents h t) :
    s.Represents (disj g h) (r + t) := by
  intro v
  simp only [eval_disj, Bool.or_eq_true, hg v, hh v, Rel.add_holds]
  aesop

/-- Conjunction of a single complete test's field equalities. -/
def completeTest (p : F → V) : s.DiagramGuard :=
  every s.fields (fun f => s.fieldTest 0 f (p f))

theorem completeTest_correct {v : s.Bits} {p q : F → V} (h : s.Matches 0 v p) :
    eval (s.completeTest q).1 v = true ↔ p = q := by
  rw [completeTest, eval_every]
  simp only [s.fieldTest_correct h, decide_eq_true_eq]
  exact ⟨fun h => funext (fun f => h f (s.fields_complete f)),
    fun e f _ => congrFun e f⟩

private def leftBank (b : Fin 3) : Fin 3 := if b = 1 then 2 else b
private def rightBank (b : Fin 3) : Fin 3 := if b = 0 then 2 else b

private def move (f : Fin 3 → Fin 3) (i : Fin s.width) : Fin s.width :=
  let x := s.index.symm i
  s.index (x.1, f x.2)

private theorem matches_move (f : Fin 3 → Fin 3) (b : Fin 3) (v : s.Bits) (p : F → V) :
    s.Matches b (v ∘ s.move f) p ↔ s.Matches (f b) v p := by
  simp [Matches, move, bit, Function.comp_def]

private def middle (i : Fin s.width) : Bool := decide ((s.index.symm i).2 = 2)

omit [DecidableEq V] in
private theorem middle_bit (b : Fin 3) (f : F) (a : V) :
    s.middle (s.bit b f a) = decide (b = 2) := by
  simp [middle, bit]

private def setMiddle (v : s.Bits) (p : F → V) : s.Bits := fun i =>
  if s.middle i then decide (p (s.index.symm i).1.1 = (s.index.symm i).1.2) else v i

private theorem matches_setMiddle (v : s.Bits) (p : F → V) :
    s.Matches 2 (s.setMiddle v p) p := by
  intro f a
  simp [setMiddle, middle, bit]

/-- Relational composition by joining at the middle bank and projecting
that bank out. Projection walks the symbolic diagram. -/
def seq (g h : s.DiagramGuard) : s.DiagramGuard :=
  let join := conj (Guard.rename g.1 (s.move leftBank)) (Guard.rename h.1 (s.move rightBank))
  Guard.project join.1 s.middle

theorem seq_correct {g h : s.DiagramGuard} {r t : Rel (F → V)}
    (hg : s.Represents g r) (hh : s.Represents h t) :
    s.Represents (s.seq g h) (r * t) := by
  simp only [Represents] at hg hh
  intro v
  rw [seq, Guard.eval_project]
  simp only [eval_conj, Bool.and_eq_true, Guard.eval_rename, hg, hh, s.matches_move,
    show leftBank 0 = 0 by rfl, show leftBank 1 = 2 by rfl,
    show rightBank 0 = 2 by rfl, show rightBank 1 = 1 by rfl, Rel.mul_holds]
  constructor
  · rintro ⟨w, hstay, ⟨p, m, hp, hm, hpm⟩, ⟨m', q, hm', hq, hmq⟩⟩
    have heq := s.matches_unique hm hm'
    subst m'
    refine ⟨p, q, ?_, ?_, m, hpm, hmq⟩
    · intro f a
      rw [← hstay (s.bit 0 f a) (by rw [s.middle_bit]; rfl), hp f a]
    · intro f a
      rw [← hstay (s.bit 1 f a) (by rw [s.middle_bit]; rfl), hq f a]
  · rintro ⟨p, q, hp, hq, m, hpm, hmq⟩
    let w := s.setMiddle v m
    have hstay : ∀ i, s.middle i = false → w i = v i := by
      intro i hi
      simp [w, setMiddle, hi]
    have hp' : s.Matches 0 w p := fun f a =>
      (hstay (s.bit 0 f a) (by rw [s.middle_bit]; rfl)).trans (hp f a)
    have hq' : s.Matches 1 w q := fun f a =>
      (hstay (s.bit 1 f a) (by rw [s.middle_bit]; rfl)).trans (hq f a)
    exact ⟨w, hstay, ⟨p, m, hp', s.matches_setMiddle v m, hpm⟩,
      ⟨m, q, s.matches_setMiddle v m, hq', hmq⟩⟩

end Schema
end KATLean.NetKAT.Symbolic
