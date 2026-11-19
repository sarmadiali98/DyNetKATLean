import DyNetKAT.NetKAT.Symbolic
import DyNetKAT.NetKAT.Normalization

/-! The proof-only bridge to E_NK. Symbolic closure supplies the star
certificates. The star-free comparison uses the existing field partition
and pair-sum laws. -/

namespace DyNetKAT.NetKAT

open scoped Computability
open KATLean.Native.Boolean

local infixl:65 " ∔ " => NetKAT.union
local infixl:70 " ⨟ " => NetKAT.seq

/-- Exact symbolic closure gives a star-free derivation representative.
The invariant tracks a syntactic unfolding below star for each reached
diagram. Star induction certifies the final fixed point. -/
theorem exists_derives_starFree_symbolic (p : NetKAT) :
    ∃ r, StarFree r ∧ Derives p r := by
  induction p with
  | drop | id | test | completeTest | assign1 => exact ⟨_, by trivial, .refl _⟩
  | union p q ihp ihq =>
    obtain ⟨r, hrf, hr⟩ := ihp
    obtain ⟨t, htf, ht⟩ := ihq
    exact ⟨r ∔ t, ⟨hrf, htf⟩, .unionCongr hr ht⟩
  | seq p q ihp ihq =>
    obtain ⟨r, hrf, hr⟩ := ihp
    obtain ⟨t, htf, ht⟩ := ihq
    exact ⟨r ⨟ t, ⟨hrf, htf⟩, .seqCongr hr ht⟩
  | star p ih =>
    obtain ⟨body, hfree, hbody⟩ := ih
    let Inv (g : symbolicSchema.DiagramGuard) := ∃ r,
      StarFree r ∧ symbolicSchema.Represents g (katInterp r) ∧
        Derives (r ∔ .star p) (.star p)
    have base : Inv (disj symbolicSchema.skip (compileSymbolic p)) := by
      have hrep := compileSymbolic_correct p
      rw [hbody.katSound] at hrep
      exact ⟨.id ∔ body, ⟨trivial, hfree⟩,
        symbolicSchema.union_correct symbolicSchema.skip_correct hrep,
        Derives.trans (.unionCongr (.unionCongr (.refl _) hbody.symm) (.refl _)) (star_seed_below p)⟩
    have step (g) (h : Inv g) : Inv (disj g (symbolicSchema.seq g g)) := by
      obtain ⟨r, hf, hr, hu⟩ := h
      exact ⟨r ∔ (r ⨟ r), ⟨hf, hf, hf⟩,
        symbolicSchema.union_correct hr (symbolicSchema.seq_correct hr hr), star_square_below hu⟩
    obtain ⟨r, hf, hr, hu⟩ := symbolicSchema.star_induction base step
    have heq : katInterp r = katInterp (.star p) :=
      symbolicSchema.represents_unique hr (compileSymbolic_correct (.star p))
    have hfixed : Derives (.id ∔ (r ⨟ body)) r := by
      apply derives_of_equiv_starFree (p := .id ∔ (r ⨟ body)) ⟨trivial, hf, hfree⟩ hf
      apply katInterp_eq_iff.mp
      rw [katInterp_union, katInterp_seq, ← hbody.katSound, heq, katInterp_star]
      exact KATLean.star_unfold_right _
    have hfixed' : Derives (.id ∔ (r ⨟ p)) r :=
      Derives.trans (.unionCongr (.refl _) (.seqCongr (.refl _) hbody)) hfixed
    exact ⟨r, hf, derives_star_of_fixed hu hfixed'⟩

/-- Packet-specific completeness through symbolic star closure and the
star-free field-partition laws. -/
theorem netkatNativeEquiv_iff_derives (p q : NetKAT) :
    netkatNativeEquiv p q = true ↔ Derives p q := by
  rw [netkatNativeEquiv_correct]
  constructor
  · intro h
    obtain ⟨r, hf, hr⟩ := exists_derives_starFree_symbolic p
    obtain ⟨t, hg, ht⟩ := exists_derives_starFree_symbolic q
    exact hr.trans ((derives_of_equiv_starFree hf hg (fun σ τ =>
      (hr.sound σ τ).symm.trans ((h σ τ).trans (ht.sound σ τ)))).trans ht.symm)
  · exact Derives.sound

theorem netkatNativeEquiv_false_not_derives {p q : NetKAT}
    (h : netkatNativeEquiv p q = false) : ¬ Derives p q := by
  intro d
  have htrue := netkatNativeEquiv_complete d.sound
  rw [h] at htrue
  contradiction

end DyNetKAT.NetKAT
