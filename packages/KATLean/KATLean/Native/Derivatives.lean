import KATLean.Native.Language
import Mathlib.Data.Finset.Image

namespace KATLean.Native

variable {T A : Type} [DecidableEq T] [DecidableEq A]

/-- Antimirov partial derivatives. Tests retain their guarding atom, and
nullable prefixes determine whether the right operand can consume an action. -/
def derivative : Expr T A → Atom T → A → Finset (Expr T A)
  | .zero, _, _ | .one, _, _ | .test _, _, _ => ∅
  | .action name, _, action => if name = action then {.one} else ∅
  | .plus p q, atom, action => derivative p atom action ∪ derivative q atom action
  | .seq p q, atom, action =>
      (derivative p atom action).image (fun rest => .seq rest q) ∪
        if (nullable p).eval atom then derivative q atom action else ∅
  | .star p, atom, action => (derivative p atom action).image (fun rest => .seq rest (.star p))

/-- Consuming an action under its current atom is exactly the union of
the partial-derivative languages. The next atom guards the residual. -/
theorem derivative_correct (e : Expr T A) (atom : Atom T) (action : A)
    (next : Atom T) (word : Word T A) :
    Accept e atom ((action, next) :: word) ↔
      ∃ rest ∈ derivative e atom action, Accept rest next word := by
  induction e generalizing atom action next word with
  | zero | one | test =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨_, impossible, _⟩
      cases impossible
  | action name =>
    constructor
    · intro accepted
      cases accepted
      exact ⟨.one, by simp [derivative], .one _⟩
    · rintro ⟨rest, member, accepted⟩
      by_cases equal : name = action
      · simp [derivative, equal] at member
        subst rest
        cases accepted
        subst action
        exact .action _ _ _
      · simp [derivative, equal] at member
  | plus p q ihp ihq =>
    constructor
    · intro accepted
      cases accepted with
      | plusLeft hp =>
        obtain ⟨rest, hr, accepted⟩ := (ihp atom action next word).mp hp
        exact ⟨rest, Finset.mem_union_left _ hr, accepted⟩
      | plusRight hq =>
        obtain ⟨rest, hr, accepted⟩ := (ihq atom action next word).mp hq
        exact ⟨rest, Finset.mem_union_right _ hr, accepted⟩
    · rintro ⟨rest, member, accepted⟩
      rcases Finset.mem_union.mp member with hp | hq
      · exact .plusLeft ((ihp atom action next word).mpr ⟨rest, hp, accepted⟩)
      · exact .plusRight ((ihq atom action next word).mpr ⟨rest, hq, accepted⟩)
  | seq p q ihp ihq =>
    constructor
    · intro accepted
      obtain ⟨u, v, eq, hp, hq⟩ := accept_seq_iff.mp accepted
      cases u with
      | nil =>
        simp only [List.nil_append] at eq
        subst v
        obtain ⟨rest, member, accepted⟩ := (ihq atom action next word).mp hq
        have hn := (nullable_correct p atom).mpr hp
        exact ⟨rest, Finset.mem_union_right _ (by simpa [hn] using member), accepted⟩
      | cons first tail =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj eq
        obtain ⟨rest, member, accepted⟩ := (ihp atom action next tail).mp hp
        exact ⟨.seq rest q, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨rest, member, rfl⟩),
          .seq accepted hq⟩
    · rintro ⟨rest, member, accepted⟩
      rcases Finset.mem_union.mp member with left | right
      · obtain ⟨base, baseMember, rfl⟩ := Finset.mem_image.mp left
        obtain ⟨u, v, rfl, hu, hv⟩ := accept_seq_iff.mp accepted
        exact .seq ((ihp atom action next u).mpr ⟨base, baseMember, hu⟩) hv
      · by_cases hn : (nullable p).eval atom = true
        · have member : rest ∈ derivative q atom action := by simpa [hn] using right
          exact .seq ((nullable_correct p atom).mp hn)
            ((ihq atom action next word).mpr ⟨rest, member, accepted⟩)
        · simp [hn] at right
  | star p ih =>
    constructor
    · intro accepted
      obtain ⟨u, v, nonempty, eq, hp, hrest⟩ := accepted.star_nonempty p rfl (by simp)
      cases u with
      | nil => exact (nonempty rfl).elim
      | cons first tail =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj eq
        obtain ⟨rest, member, accepted⟩ := (ih atom action next tail).mp hp
        exact ⟨.seq rest (.star p), Finset.mem_image.mpr ⟨rest, member, rfl⟩,
          .seq accepted hrest⟩
    · rintro ⟨rest, member, accepted⟩
      obtain ⟨base, baseMember, rfl⟩ := Finset.mem_image.mp member
      obtain ⟨u, v, rfl, hu, hv⟩ := accept_seq_iff.mp accepted
      exact .starCons ((ih atom action next u).mpr ⟨base, baseMember, hu⟩) hv

/-- A syntax-computed finite overapproximation of all partial derivatives.
It depends on the expression, with no packet universe or exploration cutoff. -/
def continuations : Expr T A → Finset (Expr T A)
  | .zero | .one | .test _ => ∅
  | .action _ => {.one}
  | .plus p q => continuations p ∪ continuations q
  | .seq p q => (continuations p).image (fun rest => .seq rest q) ∪ continuations q
  | .star p => (continuations p).image (fun rest => .seq rest (.star p))

theorem derivative_subset (e : Expr T A) (atom : Atom T) (action : A) :
    derivative e atom action ⊆ continuations e := by
  induction e with
  | zero | one | test => exact Finset.empty_subset _
  | action name => simp only [derivative, continuations]; split <;> simp
  | plus p q ihp ihq => exact Finset.union_subset_union ihp ihq
  | seq p q ihp ihq =>
    apply Finset.union_subset_union (Finset.image_subset_image ihp)
    split <;> first | exact ihq | exact Finset.empty_subset _
  | star p ih => exact Finset.image_subset_image ih

theorem continuations_closed (e : Expr T A) :
    ∀ rest ∈ continuations e, ∀ atom action, derivative rest atom action ⊆ continuations e := by
  induction e with
  | zero | one | test => simp [continuations]
  | action name =>
    intro rest member atom action
    have eq : rest = .one := Finset.mem_singleton.mp member
    subst rest
    exact Finset.empty_subset _
  | plus p q ihp ihq =>
    intro rest member atom action target step
    rcases Finset.mem_union.mp member with hp | hq
    · exact Finset.mem_union_left _ (ihp rest hp atom action step)
    · exact Finset.mem_union_right _ (ihq rest hq atom action step)
  | seq p q ihp ihq =>
    intro rest member atom action
    rcases Finset.mem_union.mp member with hp | hq
    · obtain ⟨base, hb, rfl⟩ := Finset.mem_image.mp hp
      apply Finset.union_subset_union
      · exact Finset.image_subset_image (ihp base hb atom action)
      · split
        · exact derivative_subset q atom action
        · exact Finset.empty_subset _
    · exact (ihq rest hq atom action).trans Finset.subset_union_right
  | star p ih =>
    intro rest member atom action
    obtain ⟨base, hb, rfl⟩ := Finset.mem_image.mp member
    apply Finset.union_subset
    · exact Finset.image_subset_image (ih base hb atom action)
    · split
      · exact derivative_subset (.star p) atom action
      · exact Finset.empty_subset _

/-- Every finite derivative execution stays inside one finite syntactic set. -/
def support (e : Expr T A) : Finset (Expr T A) := insert e (continuations e)

theorem support_closed (e : Expr T A) {rest : Expr T A} (member : rest ∈ support e)
    (atom : Atom T) (action : A) : derivative rest atom action ⊆ support e := by
  rcases Finset.mem_insert.mp member with equal | member
  · subst rest
    exact (derivative_subset e atom action).trans (Finset.subset_insert _ _)
  · exact (continuations_closed e rest member atom action).trans (Finset.subset_insert _ _)

end KATLean.Native
