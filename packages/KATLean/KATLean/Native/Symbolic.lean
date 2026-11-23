import KATLean.Native.Boolean
import KATLean.Native.Automaton
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Finset.Sort
import KATLean.Native.Ordering

namespace KATLean.Native

open Boolean


variable {T A S R U : Type} [BooleanAlphabet T]

abbrev Regions (T : Type) [BooleanAlphabet T] (S : Type) := List (Guard T × S)

def Covers (regions : Regions T S) (f : Atom T → S) : Prop :=
  (∀ g s, (g, s) ∈ regions → ∀ v, eval g.1 (encodeAtom v) = true → s = f v) ∧
  ∀ v, ∃ g, (g, f v) ∈ regions ∧ eval g.1 (encodeAtom v) = true

def constant (s : S) : Regions T S := [(truth, s)]

theorem covers_constant (s : S) : Covers (constant s : Regions T S) (fun _ => s) := by
  constructor
  · intro g t member v accepted
    have eq := List.mem_singleton.mp member
    exact congrArg Prod.snd eq
  · intro v; exact ⟨truth, by simp [constant], rfl⟩

def combine (op : S → R → U) (p : Regions T S) (q : Regions T R) : Regions T U :=
  ((p ×ˢ q).filter (fun pair => sat (conj pair.1.1 pair.2.1).1)).map
    (fun pair => (conj pair.1.1 pair.2.1, op pair.1.2 pair.2.2))

theorem mem_combine (op : S → R → U) (p : Regions T S) (q : Regions T R) (g : Guard T) (u : U) :
    (g, u) ∈ combine op p q ↔ ∃ a s b r, (a, s) ∈ p ∧ (b, r) ∈ q ∧
      sat (conj a b).1 = true ∧ g = conj a b ∧ u = op s r := by
  simp only [combine, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨⟨a, s⟩, ⟨b, r⟩⟩, ⟨hpq, hs⟩, eq⟩
    obtain ⟨hp, hq⟩ := List.mem_product.mp hpq
    exact ⟨a, s, b, r, hp, hq, hs, (congrArg Prod.fst eq).symm, (congrArg Prod.snd eq).symm⟩
  · rintro ⟨a, s, b, r, hp, hq, hs, rfl, rfl⟩
    exact ⟨((a, s), (b, r)), ⟨List.mem_product.mpr ⟨hp, hq⟩, hs⟩, rfl⟩

theorem covers_combine (op : S → R → U) {p : Regions T S} {q : Regions T R}
    {f : Atom T → S} {h : Atom T → R} (hp : Covers p f) (hq : Covers q h) :
    Covers (combine op p q) (fun v => op (f v) (h v)) := by
  constructor
  · intro g u member v accepted
    obtain ⟨a, s, b, r, has, hbr, _, rfl, rfl⟩ := (mem_combine op p q g u).mp member
    obtain ⟨ha, hb⟩ := (show eval a.1 (encodeAtom v) = true ∧ eval b.1 (encodeAtom v) = true by simpa using accepted)
    rw [hp.1 a s has v ha, hq.1 b r hbr v hb]
  · intro v
    obtain ⟨a, has, ha⟩ := hp.2 v
    obtain ⟨b, hbr, hb⟩ := hq.2 v
    have hab : eval (conj a b).1 (encodeAtom v) = true := by simp [ha, hb]
    exact ⟨conj a b, (mem_combine _ _ _ _ _).mpr
      ⟨a, f v, b, h v, has, hbr, (sat_correct _).mpr ⟨encodeAtom v, hab⟩, rfl, rfl⟩, hab⟩

def mapRegions (op : S → R) (p : Regions T S) : Regions T R := p.map (fun x => (x.1, op x.2))

theorem covers_map (op : S → R) {p : Regions T S} {f : Atom T → S} (hp : Covers p f) :
    Covers (mapRegions op p) (fun v => op (f v)) := by
  constructor
  · intro g r member v accepted
    obtain ⟨⟨a, s⟩, hm, eq⟩ := List.mem_map.mp member
    cases eq
    exact congrArg op (hp.1 a s hm v accepted)
  · intro v
    obtain ⟨g, hg, hv⟩ := hp.2 v
    exact ⟨g, List.mem_map.mpr ⟨(g, f v), hg, rfl⟩, hv⟩

def splitGuard (g : Guard T) : Regions T Bool := [(g, true), (neg g, false)]

theorem covers_split (g : Guard T) :
    Covers (splitGuard g) (fun v => eval g.1 (encodeAtom v)) := by
  constructor
  · intro h b member v accepted
    simp only [splitGuard, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with eq | eq
    · cases eq; exact accepted.symm
    · cases eq
      have h : !eval g.1 (encodeAtom v) = true := by simpa using accepted
      cases value : eval g.1 (encodeAtom v) <;> simp_all
  · intro v
    cases value : eval g.1 (encodeAtom v)
    · exact ⟨neg g, by simp [splitGuard, value], by simp [value]⟩
    · exact ⟨g, by simp [splitGuard, value], value⟩

variable [DecidableEq T] [DecidableEq A]

/-- Guarded symbolic derivative partition. Unsatisfiable intersections are
removed by diagram traversal, without generating Boolean assignments. -/
def derivativeRegions : Expr T A → A → Regions T (State T A)
  | .zero, _ | .one, _ | .test _, _ => constant ∅
  | .action name, a => constant (if name = a then {.one} else ∅)
  | .plus p q, a => combine (· ∪ ·) (derivativeRegions p a) (derivativeRegions q a)
  | .seq p q, a => combine (· ∪ ·)
      (mapRegions (fun state => state.image (fun e => .seq e q)) (derivativeRegions p a))
      (combine (fun enabled state => if enabled then state else ∅)
        (splitGuard (nullable p).guard) (derivativeRegions q a))
  | .star p, a => mapRegions (fun state => state.image (fun e => .seq e (.star p))) (derivativeRegions p a)

theorem derivativeRegions_correct (e : Expr T A) (a : A) :
    Covers (derivativeRegions e a) (fun v => derivative e v a) := by
  induction e with
  | zero | one | test | action => exact covers_constant _
  | plus p q ihp ihq => exact covers_combine _ ihp ihq
  | seq p q ihp ihq =>
    have hp := covers_map (fun state : State T A => state.image (fun e => Expr.seq e q)) ihp
    have hq := covers_combine (fun enabled state => if enabled then state else ∅)
      (covers_split (nullable p).guard) ihq
    simpa only [Test.guard_correct] using covers_combine (· ∪ ·) hp hq
  | star p ih => exact covers_map _ ih

def transitionList (a : A) : List (Expr T A) → Regions T (State T A)
  | [] => constant ∅
  | e :: rest => combine (· ∪ ·) (derivativeRegions e a) (transitionList a rest)

theorem transitionList_correct (a : A) (es : List (Expr T A)) :
    Covers (transitionList a es) (fun v => es.foldr (fun e acc => derivative e v a ∪ acc) ∅) := by
  induction es with
  | nil => exact covers_constant _
  | cons e rest ih => exact covers_combine _ (derivativeRegions_correct e a) ih

variable [Encodable T] [Encodable A]

/-- Structural insertion sort keeps proof-producing `by decide` reduction
available, unlike the well-founded merge sort used by `Finset.sort`. -/
def sortedValues {E : Type} [LinearOrder E] (s : Multiset E) : List E :=
  Quot.liftOn s (fun xs => xs.insertionSort (· ≤ ·)) (fun xs ys perm =>
    List.eq_of_perm_of_sorted
      ((List.perm_insertionSort _ xs).trans (perm.trans (List.perm_insertionSort _ ys).symm))
      (List.sorted_insertionSort _ xs) (List.sorted_insertionSort _ ys))

omit [BooleanAlphabet T] [DecidableEq T] [DecidableEq A] [Encodable T] [Encodable A] in
@[simp] theorem mem_sortedValues {E : Type} [LinearOrder E] (s : Multiset E) (e : E) :
    e ∈ sortedValues s ↔ e ∈ s := by
  induction s using Quot.inductionOn with
  | h xs => simp [sortedValues]

def stateList (state : State T A) : List (Expr T A) :=
  letI : LinearOrder (Expr T A) := LinearOrder.lift' Expr.orderCode Expr.orderCode_injective
  sortedValues state.val

omit [BooleanAlphabet T] [DecidableEq T] [DecidableEq A] in
@[simp] theorem mem_stateList (state : State T A) (e : Expr T A) : e ∈ stateList state ↔ e ∈ state := by
  letI : LinearOrder (Expr T A) := LinearOrder.lift' Expr.orderCode Expr.orderCode_injective
  exact mem_sortedValues _ _

def transitionRegions (state : State T A) (a : A) : Regions T (State T A) :=
  transitionList a (stateList state)

theorem transitionRegions_correct (state : State T A) (a : A) :
    Covers (transitionRegions state a) (fun v => transition state v a) := by
  have eq : ∀ v, (stateList state).foldr (fun e acc => derivative e v a ∪ acc) ∅ = transition state v a := by
    intro v
    ext e
    simp only [transition, Finset.mem_biUnion]
    have fold : ∀ es : List (Expr T A), e ∈ es.foldr (fun x acc => derivative x v a ∪ acc) ∅ ↔
        ∃ x ∈ es, e ∈ derivative x v a := by
      intro es
      induction es with
      | nil => simp
      | cons x xs ih => simp [ih, or_and_right, exists_or]
    simpa using fold (stateList state)
  simpa only [eq] using transitionList_correct a (stateList state)

def outputList : List (Expr T A) → Guard T
  | [] => falsity
  | e :: rest => disj (nullable e).guard (outputList rest)

omit [DecidableEq T] [DecidableEq A] [Encodable T] [Encodable A] in
theorem outputList_correct (es : List (Expr T A)) (v : Atom T) :
    eval (outputList es).1 (encodeAtom v) = true ↔ ∃ e ∈ es, Accept e v [] := by
  induction es with
  | nil => simp [outputList]
  | cons e rest ih => simp [outputList, Test.guard_correct, Bool.or_eq_true, nullable_correct, ih]

def outputGuard (state : State T A) : Guard T := outputList (stateList state)

omit [DecidableEq T] [DecidableEq A] in
theorem outputGuard_correct (state : State T A) (v : Atom T) :
    eval (outputGuard state).1 (encodeAtom v) = output state v := by
  apply Bool.eq_iff_iff.mpr
  rw [output_correct]
  simpa [outputGuard, StateAccept] using outputList_correct (stateList state) v

end KATLean.Native
