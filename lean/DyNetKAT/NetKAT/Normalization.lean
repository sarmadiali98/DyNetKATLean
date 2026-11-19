import DyNetKAT.NetKAT.NormalForm
import DyNetKAT.NetKAT.Axioms
import DyNetKAT.NetKAT.Symbolic

namespace DyNetKAT.NetKAT

local instance : DecidableEq CompleteTest := (inferInstance : DecidableEq CtxPkt)
local instance : DecidableEq CompleteAssignmentValuation := (inferInstance : DecidableEq CtxPkt)

/-- The complete test succeeds exactly on its own valuation and preserves it. -/
theorem completeTest_singleton (α : CompleteTest) (σ τ : CtxPkt) :
    Semantics (.completeTest α) σ τ ↔ σ = α ∧ σ = τ := by
  rw [← NetKAT.completeTestEmbed, completeTest_sem, holdsComplete_iff_eq]

/-- A complete branch denotes exactly one ordered packet pair. -/
theorem ofSummand_singleton (α : CompleteTest) (π : CompleteAssignmentValuation)
    (σ τ : CtxPkt) :
    Semantics (NormalForm.ofSummand (α, π)) σ τ ↔ σ = α ∧ τ = π := by
  rw [ofSummand_sem, holdsComplete_iff_eq]

/-- The finite-set interpretation denotes precisely its members. -/
theorem NormalForm.interpret_iff_mem (nf : NormalForm) (σ τ : CtxPkt) :
    Semantics (nf.interpret) σ τ ↔ (σ, τ) ∈ nf := by
  rw [interpret_sem]
  constructor
  · rintro ⟨α, π, hm, hσ, hτ⟩
    rw [holdsComplete_iff_eq] at hσ
    simpa [hσ, hτ] using hm
  · intro hm
    exact ⟨σ, τ, hm, (holdsComplete_iff_eq σ σ).mpr rfl, rfl⟩

private def values : List FieldValueEnum := [.v0, .v1, .v8, .v9]

private def enumerateFields : List FieldName → List CtxPkt
  | [] => [fun _ => .v0]
  | f :: fs => (enumerateFields fs).flatMap fun p =>
      values.map fun v => Packet.update p f v

private theorem enumerateFields_covers (fs : List FieldName) (σ : CtxPkt) :
    ∃ p ∈ enumerateFields fs, ∀ f ∈ fs, p f = σ f := by
  induction fs with
  | nil => exact ⟨_, List.mem_cons_self, by simp⟩
  | cons f fs ih =>
    obtain ⟨p, hp, he⟩ := ih
    refine ⟨Packet.update p f (σ f), List.mem_flatMap.mpr ⟨p, hp, ?_⟩, ?_⟩
    · exact List.mem_map.mpr ⟨σ f, by cases σ f <;> simp [values], rfl⟩
    · intro g hg
      by_cases h : g = f
      · subst g
        simp [Packet.update]
      · have hm := (List.mem_cons.mp hg).resolve_left h
        simpa [Packet.update, h, Ne.symm h] using he g hm

/-- A fixed order for rendering. Its completeness follows from field enumeration. -/
def packetList : List CtxPkt := enumerateFields NetKAT.fieldEnum

theorem mem_packetList (σ : CtxPkt) : σ ∈ packetList := by
  obtain ⟨p, hp, he⟩ := enumerateFields_covers NetKAT.fieldEnum σ
  have h : p = σ := funext fun f => he f (NetKAT.fieldEnum_complete f)
  exact h ▸ hp

/-- The finite relation computed by the existing exact evaluator. -/
def legacyNetkatNormalForm (p : NetKAT) : NormalForm :=
  (Finset.univ : Finset CtxPkt).biUnion fun σ =>
    ((execute p σ).outputs.getD ∅).image fun τ => (σ, τ)

theorem legacyNetkatNormalForm_mem (p : NetKAT) (σ τ : CtxPkt) :
    (σ, τ) ∈ legacyNetkatNormalForm p ↔ Semantics p σ τ := by
  unfold legacyNetkatNormalForm
  constructor
  · intro h
    obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp h
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hs
    cases he
    obtain ⟨B, hB, hSem⟩ := execute_correct p σ
    exact (hSem τ).mpr (by simpa [hB, EvalResult.outputs] using ht)
  · intro h
    obtain ⟨B, hB, hSem⟩ := execute_correct p σ
    exact Finset.mem_biUnion.mpr ⟨σ, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨τ, by simpa [hB, EvalResult.outputs] using (hSem τ).mp h, rfl⟩⟩

/-- The compact normal form is the reduced packet relation diagram.
Only the paper's explicit pair syntax and heads require materialization. -/
def symbolicNormalForm (p : NetKAT) : symbolicSchema.DiagramGuard :=
  compileSymbolic p

theorem symbolicNormalForm_correct (p : NetKAT) :
    symbolicSchema.Represents (symbolicNormalForm p) (katInterp p) :=
  compileSymbolic_correct p

/-- Materialize the exact paper branches from accepting paths only. -/
def symbolicPairs (p : NetKAT) : List (CompleteTest × CompleteAssignmentValuation) :=
  symbolicSchema.acceptedPairs .v0 (symbolicNormalForm p)

theorem mem_symbolicPairs (p : NetKAT) (σ τ : CtxPkt) :
    (σ, τ) ∈ symbolicPairs p ↔ Semantics p σ τ :=
  (symbolicSchema.mem_acceptedPairs .v0 (symbolicNormalForm_correct p) σ τ).trans
    (katInterp_correct p σ τ)

/-- Finite-set compatibility view of the symbolic normal form. -/
def netkatNormalForm (p : NetKAT) : NormalForm :=
  (symbolicPairs p).toFinset

theorem netkatNormalForm_mem (p : NetKAT) (σ τ : CtxPkt) :
    (σ, τ) ∈ netkatNormalForm p ↔ Semantics p σ τ :=
  List.mem_toFinset.trans (mem_symbolicPairs p σ τ)

theorem netkatNormalForm_correct (p : NetKAT) (σ τ : CtxPkt) :
    Semantics (netkatNormalForm p).interpret σ τ ↔ Semantics p σ τ :=
  (NormalForm.interpret_iff_mem _ _ _).trans (netkatNormalForm_mem p σ τ)

theorem netkatNormalForm_eq_iff (p q : NetKAT) :
    netkatNormalForm p = netkatNormalForm q ↔
      ∀ σ τ : CtxPkt, Semantics p σ τ ↔ Semantics q σ τ := by
  constructor
  · intro he σ τ
    rw [← netkatNormalForm_mem p σ τ, ← netkatNormalForm_mem q σ τ, he]
  · intro he
    ext pair
    obtain ⟨σ, τ⟩ := pair
    rw [netkatNormalForm_mem, netkatNormalForm_mem]
    exact he σ τ

/-- Ordered syntax for a finite sum of complete branches. -/
def pairSum (xs : List (CompleteTest × CompleteAssignmentValuation)) : NetKAT :=
  xs.foldr (fun pair acc => .union (NormalForm.ofSummand pair) acc) .drop

theorem pairSum_sem (xs : List (CompleteTest × CompleteAssignmentValuation)) (σ τ : CtxPkt) :
    Semantics (pairSum xs) σ τ ↔ (σ, τ) ∈ xs := by
  unfold pairSum
  rw [fold_sem]
  simp only [holdsComplete_iff_eq]
  constructor
  · rintro ⟨α, π, hm, rfl, rfl⟩
    exact hm
  · intro h
    exact ⟨σ, τ, h, rfl, rfl⟩

/-- A syntax-level witness for a sum of complete branches. The empty sum is drop. -/
def IsPairSum (p : NetKAT) : Prop :=
  ∃ xs : List (CompleteTest × CompleteAssignmentValuation),
    p = pairSum xs

/-- Legacy Cartesian-product renderer for the concrete regression oracle. -/
def NormalForm.orderedPairs (nf : NormalForm) :
    List (CompleteTest × CompleteAssignmentValuation) :=
  (packetList.flatMap fun σ => packetList.map fun τ => (σ, τ)).filter (fun pair => decide (pair ∈ nf))

theorem NormalForm.mem_orderedPairs (nf : NormalForm)
    (pair : CompleteTest × CompleteAssignmentValuation) :
    pair ∈ nf.orderedPairs ↔ pair ∈ nf := by
  rcases pair with ⟨σ, τ⟩
  rw [orderedPairs, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨List.mem_flatMap.mpr ⟨σ, mem_packetList σ,
    List.mem_map.mpr ⟨τ, mem_packetList τ, rfl⟩⟩, h⟩⟩

/-- The original exhaustive normalizer, retained for regression. -/
def legacyNormalize (p : NetKAT) : NetKAT :=
  pairSum (legacyNetkatNormalForm p).orderedPairs

theorem legacyNormalize_correct (p : NetKAT) (σ τ : CtxPkt) :
    Semantics (legacyNormalize p) σ τ ↔ Semantics p σ τ :=
  (pairSum_sem _ σ τ).trans
    ((NormalForm.mem_orderedPairs _ _).trans (legacyNetkatNormalForm_mem p σ τ))

/-- Exact finite sum of complete tests followed by complete assignments. -/
def symbolicNormalize (p : NetKAT) : NetKAT :=
  pairSum (symbolicPairs p)

abbrev normalize := symbolicNormalize

theorem symbolic_normalize_pairSum (p : NetKAT) : IsPairSum (symbolicNormalize p) :=
  ⟨symbolicPairs p, rfl⟩

theorem normalize_pairSum (p : NetKAT) : IsPairSum (normalize p) :=
  symbolic_normalize_pairSum p

theorem normalize_correct (p : NetKAT) (σ τ : CtxPkt) :
    Semantics (normalize p) σ τ ↔ Semantics p σ τ :=
  (pairSum_sem _ σ τ).trans (mem_symbolicPairs p σ τ)

theorem normalize_history_correct (p : NetKAT) (h h' : History) :
    HistorySemantics (normalize p) h h' ↔ HistorySemantics p h h' :=
  (netkatEquiv_history_correct (normalize p) p).mp
    ((netkatEquiv_correct (normalize p) p).mpr (normalize_correct p)) h h'

/-- Star-free is a strict subfragment of the dup-free NetKAT AST. -/
def StarFree : NetKAT → Prop
  | .union p q | .seq p q => StarFree p ∧ StarFree q
  | .star _ => False
  | _ => True

private theorem completeAssignExpr_starFree (π : CompleteAssignmentValuation) :
    StarFree (NetKAT.completeAssignExpr π) := by
  unfold NetKAT.completeAssignExpr
  split
  · trivial
  · rename_i f fs he
    refine ⟨trivial, ?_⟩
    clear he
    induction fs with
    | nil => trivial
    | cons g fs ih => exact ⟨trivial, ih⟩

theorem IsPairSum.starFree {p : NetKAT} (hp : IsPairSum p) : StarFree p := by
  obtain ⟨xs, rfl⟩ := hp
  induction xs with
  | nil => trivial
  | cons pair xs ih => exact ⟨⟨trivial, completeAssignExpr_starFree pair.2⟩, ih⟩

theorem normalize_starFree (p : NetKAT) : StarFree (normalize p) :=
  (normalize_pairSum p).starFree

local infixl:65 " ⊕ " => NetKAT.union
local infixl:70 " ⨟ " => NetKAT.seq

private def Below (p q : NetKAT) : Prop := Derives (p ⊕ q) q

private theorem below_trans {a b c : NetKAT} (h : Below a b) (k : Below b c) : Below a c :=
  .trans (.unionCongr (.refl _) k.symm)
    (.trans (.plusAssoc _ _ _) (.trans (.unionCongr h (.refl _)) k))

private theorem below_left (a b : NetKAT) : Below a (a ⊕ b) :=
  .trans (.plusAssoc _ _ _) (.unionCongr (.plusIdem _) (.refl _))

private theorem below_right (a b : NetKAT) : Below b (a ⊕ b) :=
  .trans (.unionCongr (.refl _) (.plusComm _ _))
    (.trans (below_left _ _) (.plusComm _ _))

private theorem below_of_derives {a b : NetKAT} (h : Derives a b) : Below a b :=
  .trans (.unionCongr h (.refl _)) (.plusIdem _)

private theorem below_union {a b c : NetKAT} (h : Below a c) (k : Below b c) : Below (a ⊕ b) c :=
  .trans (.symm (.plusAssoc _ _ _)) (.trans (.unionCongr (.refl _) k) h)

private theorem below_seq_right {a b : NetKAT} (h : Below a b) (p : NetKAT) :
    Below (a ⨟ p) (b ⨟ p) :=
  .trans (.symm (.seqDistR _ _ _)) (.seqCongr h (.refl _))

private theorem derives_of_below {a b : NetKAT} (h : Below a b) (k : Below b a) : Derives a b :=
  .trans k.symm (.trans (.plusComm _ _) h)

private theorem summand_below_sum {a : CompleteTest × CompleteAssignmentValuation}
    {xs : List (CompleteTest × CompleteAssignmentValuation)} (h : a ∈ xs) :
    Below (NormalForm.ofSummand a) (pairSum xs) := by
  induction xs with
  | nil => cases h
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact below_left _ _
    · exact below_trans (ih h) (below_right _ _)

private theorem pairSum_below {xs ys : List (CompleteTest × CompleteAssignmentValuation)}
    (h : ∀ a ∈ xs, a ∈ ys) : Below (pairSum xs) (pairSum ys) := by
  induction xs with
  | nil => exact .trans (.plusComm _ _) (.plusZero _)
  | cons a xs ih =>
    exact below_union (summand_below_sum (h a List.mem_cons_self))
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- Finite sums with the same pairs are derivably equal, regardless of order
or duplicate branches. -/
theorem pairSum_derives {xs ys : List (CompleteTest × CompleteAssignmentValuation)}
    (h : ∀ a, a ∈ xs ↔ a ∈ ys) : Derives (pairSum xs) (pairSum ys) :=
  derives_of_below (pairSum_below (fun a => (h a).mp)) (pairSum_below (fun a => (h a).mpr))

theorem IsPairSum.derives_of_equiv {p q : NetKAT} (hp : IsPairSum p) (hq : IsPairSum q)
    (h : ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ) : Derives p q := by
  obtain ⟨xs, rfl⟩ := hp
  obtain ⟨ys, rfl⟩ := hq
  apply pairSum_derives
  rintro ⟨σ, τ⟩
  exact (pairSum_sem xs σ τ).symm.trans ((h σ τ).trans (pairSum_sem ys σ τ))

theorem IsPairSum.derives_normalize {p : NetKAT} (hp : IsPairSum p) :
    Derives p (normalize p) :=
  hp.derives_of_equiv (normalize_pairSum p) (fun σ τ => (normalize_correct p σ τ).symm)

theorem normalize_derives_drop : Derives .drop (normalize .drop) :=
  IsPairSum.derives_normalize ⟨[], rfl⟩

theorem normalize_derives_summand (α : CompleteTest) (π : CompleteAssignmentValuation) :
    Derives (NormalForm.ofSummand (α, π)) (normalize (NormalForm.ofSummand (α, π))) := by
  let p := NormalForm.ofSummand (α, π)
  have hd : Derives p (pairSum [(α, π)]) := .symm (.plusZero p)
  have hs : IsPairSum (pairSum [(α, π)]) := ⟨_, rfl⟩
  exact .trans hd (hs.derives_of_equiv (normalize_pairSum p) (fun σ τ =>
    (hd.sound σ τ).symm.trans (normalize_correct p σ τ).symm))

private theorem pairSum_append (xs ys : List (CompleteTest × CompleteAssignmentValuation)) :
    Derives (pairSum xs ⊕ pairSum ys) (pairSum (xs ++ ys)) := by
  induction xs with
  | nil => exact .trans (.plusComm _ _) (.plusZero _)
  | cons a xs ih => exact .trans (.symm (.plusAssoc _ _ _)) (.unionCongr (.refl _) ih)

theorem normalize_derives_union {p q : NetKAT} (hp : Derives p (normalize p))
    (hq : Derives q (normalize q)) : Derives (p ⊕ q) (normalize (p ⊕ q)) := by
  let xs := symbolicPairs p
  let ys := symbolicPairs q
  have hd : Derives (p ⊕ q) (pairSum (xs ++ ys)) :=
    .trans (.unionCongr hp hq) (pairSum_append xs ys)
  have hshape : IsPairSum (pairSum (xs ++ ys)) := ⟨_, rfl⟩
  exact .trans hd (hshape.derives_of_equiv (normalize_pairSum _) (fun σ τ =>
    (hd.sound σ τ).symm.trans (normalize_correct _ σ τ).symm))

/-- Finite unrolling with zero iterations represented by identity. -/
def boundedPolicy (p : NetKAT) : Nat → NetKAT
  | 0 => .id
  | n + 1 => let q := boundedPolicy p n; q ⊕ (q ⨟ p)

theorem boundedPolicy_sem (p : NetKAT) (n : Nat) (σ τ : CtxPkt) :
    Semantics (boundedPolicy p n) σ τ ↔ ReachableWithin p n σ τ := by
  induction n generalizing τ with
  | zero => exact eq_comm
  | succ n ih => simp only [boundedPolicy, union_sem, seq_sem, reachableWithin_succ_iff, ih]

theorem boundedPolicy_starFree {p : NetKAT} (hp : StarFree p) (n : Nat) :
    StarFree (boundedPolicy p n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih, ih, hp⟩

private theorem boundedPolicy_below_star (p : NetKAT) (n : Nat) :
    Below (boundedPolicy p n) (.star p) := by
  have hu := below_of_derives (Derives.unrollR p)
  induction n with
  | zero => exact below_trans (below_left _ _) hu
  | succ n ih =>
    exact below_union ih (below_trans (below_seq_right ih p) (below_trans (below_right _ _) hu))

private theorem id_below_boundedPolicy (p : NetKAT) (n : Nat) :
    Below .id (boundedPolicy p n) := by
  induction n with
  | zero => exact .plusIdem _
  | succ n ih => exact below_trans ih (below_left _ _)

/-- An equational stabilization certificate gives an actual star derivation
via the existing right least-fixpoint rule. -/
theorem derives_star_boundedPolicy {p : NetKAT} {n : Nat}
    (h : Derives (boundedPolicy p (n + 1)) (boundedPolicy p n)) :
    Derives (.star p) (boundedPolicy p n) := by
  let q := boundedPolicy p n
  have step : Below (q ⨟ p) q := below_trans (below_right _ _) (below_of_derives h)
  have upper : Below (.id ⨟ .star p) q := Derives.lfpR (below_union (id_below_boundedPolicy p n) step)
  exact derives_of_below
    (.trans (.unionCongr (.symm (.oneSeq _)) (.refl _)) upper)
    (boundedPolicy_below_star p n)

/-- Equational completeness restricted to star-free policies. -/
def StarFreeComplete : Prop :=
  ∀ {p q : NetKAT}, StarFree p → StarFree q →
    (∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ) → Derives p q

set_option maxRecDepth 10000 in
/-- Legacy packet-cardinality proof of star elimination kept for compatibility.
The normalization theorem uses symbolic fixed-point iteration instead. -/
theorem derives_starFree_of_complete (complete : StarFreeComplete) (p : NetKAT) :
    ∃ q, StarFree q ∧ Derives p q := by
  induction p with
  | drop | id | test | completeTest | assign1 =>
    refine ⟨_, ?_, .refl _⟩
    trivial
  | union p q ihp ihq | seq p q ihp ihq =>
    obtain ⟨p', hp', hdp⟩ := ihp
    obtain ⟨q', hq', hdq⟩ := ihq
    first
    | exact ⟨.union p' q', ⟨hp', hq'⟩, .unionCongr hdp hdq⟩
    | exact ⟨.seq p' q', ⟨hp', hq'⟩, .seqCongr hdp hdq⟩
  | star p ih =>
    obtain ⟨q, hq, hd⟩ := ih
    let n := Fintype.card CtxPkt
    have stable : Derives (boundedPolicy q (n + 1)) (boundedPolicy q n) :=
      complete (boundedPolicy_starFree hq _) (boundedPolicy_starFree hq _) (fun σ τ =>
        (boundedPolicy_sem q _ σ τ).trans
          ((reachableWithin_stable_at_card q σ τ).trans (boundedPolicy_sem q _ σ τ).symm))
    exact ⟨_, boundedPolicy_starFree hq _, .trans (.starCongr hd) (derives_star_boundedPolicy (n := n) stable)⟩

/-- Pair-sum extensionality upgrades star-free normalization to star-free
semantic completeness. -/
theorem starFreeComplete_iff_normalize :
    StarFreeComplete ↔ ∀ p, StarFree p → Derives p (normalize p) := by
  constructor
  · intro complete p hp
    exact complete hp (normalize_starFree p) (fun σ τ => (normalize_correct p σ τ).symm)
  · intro normalizeProof p q hp hq he
    have hn : Derives (normalize p) (normalize q) :=
      (normalize_pairSum p).derives_of_equiv (normalize_pairSum q) (fun σ τ =>
        (normalize_correct p σ τ).trans ((he σ τ).trans (normalize_correct q σ τ).symm))
    exact .trans (normalizeProof p hp) (.trans hn (.symm (normalizeProof q hq)))

private def word (f : FieldName → NetKAT) (xs : List FieldName) : NetKAT :=
  xs.foldr (fun x acc => f x ⨟ acc) .id

private def reads (σ : CtxPkt) (f : FieldName) := NetKAT.fieldTest f (σ f)
private def writes (σ : CtxPkt) (f : FieldName) := NetKAT.assign1 f (σ f)

private theorem word_congr {f g : FieldName → NetKAT} {xs : List FieldName}
    (h : ∀ x ∈ xs, Derives (f x) (g x)) : Derives (word f xs) (word g xs) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    exact .seqCongr (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem word_commute (a : NetKAT) (f : FieldName → NetKAT) (xs : List FieldName)
    (h : ∀ x ∈ xs, Derives (a ⨟ f x) (f x ⨟ a)) :
    Derives (a ⨟ word f xs) (word f xs ⨟ a) := by
  induction xs with
  | nil => exact .trans (.seqOne _) (.symm (.oneSeq _))
  | cons x xs ih =>
    exact .trans (.seqAssoc _ _ _) (.trans (.seqCongr (h x List.mem_cons_self) (.refl _))
      (.trans (.symm (.seqAssoc _ _ _))
        (.trans (.seqCongr (.refl _) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))))
          (.seqAssoc _ _ _))))

private theorem word_append_at {f g : FieldName → NetKAT} {xs : List FieldName}
    {k : FieldName} {a : NetKAT} (hn : xs.Nodup) (hk : k ∈ xs)
    (hit : Derives (f k ⨟ a) (g k)) (keep : ∀ x, x ≠ k → f x = g x)
    (comm : ∀ x, x ≠ k → Derives (a ⨟ f x) (f x ⨟ a)) :
    Derives (word f xs ⨟ a) (word g xs) := by
  induction xs with
  | nil => cases hk
  | cons x xs ih =>
    obtain ⟨hnot, hn'⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hk with rfl | hmem
    · have hc := word_commute a f xs (fun y hy => comm y (fun he => hnot (he ▸ hy)))
      have hg := word_congr (xs := xs) (fun y hy =>
        show Derives (f y) (g y) from keep y (fun he => hnot (he ▸ hy)) ▸ Derives.refl (f y))
      exact .trans (.symm (.seqAssoc _ _ _)) (.trans (.seqCongr (.refl _) (.symm hc))
        (.trans (.seqAssoc _ _ _) (.seqCongr hit hg)))
    · have he := keep x (fun he => hnot (he.symm ▸ hmem))
      exact .trans (.symm (.seqAssoc _ _ _)) (.seqCongr (he ▸ Derives.refl (f x)) (ih hn' hmem))

private theorem word_append_reject {f : FieldName → NetKAT} {xs : List FieldName}
    {k : FieldName} {a : NetKAT} (hn : xs.Nodup) (hk : k ∈ xs)
    (hit : Derives (f k ⨟ a) .drop)
    (comm : ∀ x, x ≠ k → Derives (a ⨟ f x) (f x ⨟ a)) :
    Derives (word f xs ⨟ a) .drop := by
  induction xs with
  | nil => cases hk
  | cons x xs ih =>
    obtain ⟨hnot, hn'⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hk with rfl | hmem
    · have hc := word_commute a f xs (fun y hy => comm y (fun he => hnot (he ▸ hy)))
      exact .trans (.symm (.seqAssoc _ _ _)) (.trans (.seqCongr (.refl _) (.symm hc))
        (.trans (.seqAssoc _ _ _) (.trans (.seqCongr hit (.refl _)) (.zeroSeq _))))
    · exact .trans (.symm (.seqAssoc _ _ _))
        (.trans (.seqCongr (.refl _) (ih hn' hmem)) (.seqZero _))

private theorem word_prepend_absorb {f : FieldName → NetKAT} {xs : List FieldName}
    {k : FieldName} {a : NetKAT} (hk : k ∈ xs)
    (hit : Derives (a ⨟ f k) (f k))
    (comm : ∀ x, x ≠ k → Derives (a ⨟ f x) (f x ⨟ a)) :
    Derives (a ⨟ word f xs) (word f xs) := by
  induction xs with
  | nil => cases hk
  | cons x xs ih =>
    by_cases h : x = k
    · subst x
      exact .trans (.seqAssoc _ _ _) (.seqCongr hit (.refl _))
    · exact .trans (.seqAssoc _ _ _) (.trans (.seqCongr (comm x h) (.refl _))
        (.trans (.symm (.seqAssoc _ _ _)) (.seqCongr (.refl _) (ih ((List.mem_cons.mp hk).resolve_left (Ne.symm h))))))

private theorem word_fields_prepend {f : FieldName → NetKAT} (xs : List FieldName) (q : NetKAT)
    (h : ∀ x ∈ xs, Derives (f x ⨟ q) q) : Derives (word f xs ⨟ q) q := by
  induction xs with
  | nil => exact .oneSeq _
  | cons x xs ih =>
    exact .trans (.symm (.seqAssoc _ _ _))
      (.trans (.seqCongr (.refl _) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))))
        (h x List.mem_cons_self))

private theorem word_fields_append (q : NetKAT) {f : FieldName → NetKAT} (xs : List FieldName)
    (h : ∀ x ∈ xs, Derives (q ⨟ f x) q) : Derives (q ⨟ word f xs) q := by
  induction xs with
  | nil => exact .seqOne _
  | cons x xs ih =>
    exact .trans (.seqAssoc _ _ _) (.trans (.seqCongr (h x List.mem_cons_self) (.refl _))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))))

private theorem read_eq (σ : CtxPkt) :
    Derives (.completeTest σ) (word (reads σ) NetKAT.fieldEnum) :=
  .completeTestExpand σ

private theorem read_write_self (σ : CtxPkt) :
    Derives (.completeTest σ ⨟ NetKAT.completeAssignExpr σ) (.completeTest σ) := by
  refine .trans (.seqCongr (read_eq σ) (.refl _)) (.trans ?_ (.symm (read_eq σ)))
  change Derives (word (reads σ) NetKAT.fieldEnum ⨟ word (writes σ) NetKAT.fieldEnum) _
  apply word_fields_append
  intro f _
  apply word_append_at NetKAT.fieldEnum_nodup (NetKAT.fieldEnum_complete f)
  · exact .paFilterMod f (σ f)
  · intro _ _
    rfl
  · intro g hg
    exact .paModFilterComm f g _ _ (Ne.symm hg)

private theorem write_write (β δ : CtxPkt) :
    Derives (NetKAT.completeAssignExpr β ⨟ NetKAT.completeAssignExpr δ)
      (NetKAT.completeAssignExpr δ) := by
  change Derives (word (writes β) NetKAT.fieldEnum ⨟ word (writes δ) NetKAT.fieldEnum) _
  apply word_fields_prepend
  intro f _
  exact word_prepend_absorb (NetKAT.fieldEnum_complete f) (.paModMod f (β f) (δ f))
    (fun g hg => .paModModComm f g _ _ (Ne.symm hg))

private theorem write_fieldTest (β : CtxPkt) (f : FieldName) (v : FieldValueEnum) :
    Derives (NetKAT.completeAssignExpr β ⨟ NetKAT.fieldTest f v)
      (if β f = v then NetKAT.completeAssignExpr β else .drop) := by
  change Derives (word (writes β) NetKAT.fieldEnum ⨟ _) (if β f = v then word (writes β) NetKAT.fieldEnum else .drop)
  split
  · rename_i h
    subst v
    apply word_append_at NetKAT.fieldEnum_nodup (NetKAT.fieldEnum_complete f)
    · exact .paModFilter f (β f)
    · intro _ _
      rfl
    · intro g hg
      exact .symm (.paModFilterComm g f _ _ hg)
  · rename_i h
    have hit : Derives (NetKAT.assign1 f (β f) ⨟ NetKAT.fieldTest f v) .drop :=
      .trans (.seqCongr (.symm (.paModFilter f (β f))) (.refl _))
        (.trans (.symm (.seqAssoc _ _ _)) (.trans (.seqCongr (.refl _) (.paContra f _ _ h)) (.seqZero _)))
    exact word_append_reject NetKAT.fieldEnum_nodup (NetKAT.fieldEnum_complete f) hit
      (fun g hg => .symm (.paModFilterComm g f _ _ hg))

private theorem write_assign (β : CtxPkt) (f : FieldName) (v : FieldValueEnum) :
    Derives (NetKAT.completeAssignExpr β ⨟ .assign1 f v)
      (NetKAT.completeAssignExpr (Packet.update β f v)) := by
  change Derives (word (writes β) NetKAT.fieldEnum ⨟ _) (word (writes (Packet.update β f v)) NetKAT.fieldEnum)
  apply word_append_at NetKAT.fieldEnum_nodup (NetKAT.fieldEnum_complete f)
  · simpa [writes, Packet.update] using Derives.paModMod f (β f) v
  · intro g hg
    simp [writes, Packet.update, hg, Ne.symm hg]
  · intro g hg
    exact .paModModComm f g _ _ (Ne.symm hg)


/-- A finite union of policies, with drop as the empty sum. -/
def sumOn {α : Type} (xs : List α) (f : α → NetKAT) : NetKAT :=
  xs.foldr (fun x acc => f x ⊕ acc) .drop

private theorem sumOn_map {α β : Type} (xs : List α) (f : α → β) (g : β → NetKAT) :
    sumOn (xs.map f) g = sumOn xs (fun x => g (f x)) := by
  simp [sumOn, List.foldr_map]

private theorem sumOn_congr {α : Type} {xs : List α} {f g : α → NetKAT}
    (h : ∀ x ∈ xs, Derives (f x) (g x)) : Derives (sumOn xs f) (sumOn xs g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    exact .unionCongr (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem sumOn_append {α : Type} (xs ys : List α) (f : α → NetKAT) :
    Derives (sumOn (xs ++ ys) f) (sumOn xs f ⊕ sumOn ys f) := by
  induction xs with
  | nil => exact .symm (.trans (.plusComm _ _) (.plusZero _))
  | cons x xs ih => exact .trans (.unionCongr (.refl _) ih) (.plusAssoc _ _ _)

private theorem sumOn_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → NetKAT) :
    Derives (sumOn (xs.flatMap f) g) (sumOn xs (fun x => sumOn (f x) g)) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => exact .trans (sumOn_append _ _ _) (.unionCongr (.refl _) ih)

private theorem sumOn_seq_right {α : Type} (xs : List α) (f : α → NetKAT) (p : NetKAT) :
    Derives (sumOn xs f ⨟ p) (sumOn xs (fun x => f x ⨟ p)) := by
  induction xs with
  | nil => exact .zeroSeq _
  | cons x xs ih => exact .trans (.seqDistR _ _ _) (.unionCongr (.refl _) ih)

private theorem sumOn_seq_left {α : Type} (p : NetKAT) (xs : List α) (f : α → NetKAT) :
    Derives (p ⨟ sumOn xs f) (sumOn xs (fun x => p ⨟ f x)) := by
  induction xs with
  | nil => exact .seqZero _
  | cons x xs ih => exact .trans (.seqDistL _ _ _) (.unionCongr (.refl _) ih)

private theorem field_partition (xs : List FieldName) (hn : xs.Nodup) :
    Derives (sumOn (enumerateFields xs) (fun σ => word (reads σ) xs)) .id := by
  induction xs with
  | nil => exact .plusZero _
  | cons f fs ih =>
    obtain ⟨hnot, hn'⟩ := List.nodup_cons.mp hn
    refine .trans (sumOn_flatMap _ _ _) (.trans (sumOn_congr ?_) (ih hn'))
    intro σ _
    change Derives
      (sumOn (values.map (fun v => Packet.update σ f v)) (fun p => word (reads p) (f :: fs)))
      (word (reads σ) fs)
    have hp : Derives
        (sumOn values (fun v => word (reads (Packet.update σ f v)) (f :: fs)))
        (sumOn values (fun v => NetKAT.fieldTest f v ⨟ word (reads σ) fs)) := by
      apply sumOn_congr
      intro v _
      apply Derives.seqCongr
      · simp [reads, Packet.update]
        exact .refl _
      · apply word_congr
        intro g hg
        have hgf : g ≠ f := fun h => hnot (h ▸ hg)
        simp [reads, Packet.update, hgf, Ne.symm hgf]
        exact .refl _
    change Derives
      (sumOn values (fun v => word (reads (Packet.update σ f v)) (f :: fs)))
      (word (reads σ) fs)
    exact .trans hp (.trans (.symm (sumOn_seq_right values (NetKAT.fieldTest f) _))
      (.trans (.seqCongr (.paMatchAll f) (.refl _)) (.oneSeq _)))

/-- The complete tests partition identity by the packet-field axioms. -/
theorem completeTest_partition :
    Derives .id (sumOn packetList (fun σ => .completeTest σ)) :=
  .symm (.trans (sumOn_congr (fun σ _ => read_eq σ))
    (field_partition NetKAT.fieldEnum NetKAT.fieldEnum_nodup))

theorem derives_id_diagonal : Derives .id (pairSum (packetList.map fun σ => (σ, σ))) := by
  apply Derives.trans completeTest_partition
  change Derives (sumOn packetList (fun σ => .completeTest σ))
    (sumOn (packetList.map fun σ => (σ, σ)) NormalForm.ofSummand)
  rw [sumOn_map]
  exact sumOn_congr (fun σ _ => .symm (read_write_self σ))

private theorem derives_to_normalize {p : NetKAT} {xs : List (CompleteTest × CompleteAssignmentValuation)}
    (h : Derives p (pairSum xs)) : Derives p (normalize p) :=
  .trans h ((show IsPairSum (pairSum xs) from ⟨xs, rfl⟩).derives_of_equiv (normalize_pairSum p)
    (fun σ τ => (h.sound σ τ).symm.trans (normalize_correct p σ τ).symm))

private def TestResult (a p : NetKAT) : Prop :=
  Derives (a ⨟ p) a ∨ Derives (a ⨟ p) .drop

private theorem testResult_seq {a p q : NetKAT} (hp : TestResult a p) (hq : TestResult a q) :
    TestResult a (p ⨟ q) := by
  rcases hp with hp | hp
  · have h := Derives.trans (.seqAssoc a p q) (.seqCongr hp (.refl q))
    exact hq.imp (fun k => .trans h k) (fun k => .trans h k)
  · exact .inr (.trans (.seqAssoc _ _ _) (.trans (.seqCongr hp (.refl _)) (.zeroSeq _)))

private theorem testResult_union {a p q : NetKAT} (hp : TestResult a p) (hq : TestResult a q) :
    TestResult a (p ⊕ q) := by
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact .inl (.trans (.seqDistL _ _ _) (.trans (.unionCongr hp hq) (.plusIdem _)))
  · exact .inl (.trans (.seqDistL _ _ _) (.trans (.unionCongr hp hq) (.plusZero _)))
  · exact .inl (.trans (.seqDistL _ _ _) (.trans (.unionCongr hp hq)
      (.trans (.plusComm _ _) (.plusZero _))))
  · exact .inr (.trans (.seqDistL _ _ _) (.trans (.unionCongr hp hq) (.plusZero _)))

private theorem write_testResult (β : CtxPkt) (p : Predicate) :
    TestResult (NetKAT.completeAssignExpr β) (.test p) := by
  let a := NetKAT.completeAssignExpr β
  induction p with
  | pFalse => exact .inr (.trans (.seqCongr (.refl _) .testFalse) (.seqZero _))
  | pTrue => exact .inl (.trans (.seqCongr (.refl _) .testTrue) (.seqOne _))
  | pFieldEq e =>
    obtain ⟨f, v⟩ := e
    have h := write_fieldTest β f v
    by_cases he : β f = v
    · exact .inl (by simpa only [if_pos he] using h)
    · exact .inr (by simpa only [if_neg he] using h)
  | pAnd p q ihp ihq =>
    have h : Derives (a ⨟ .test (.pAnd p q)) (a ⨟ (.test p ⨟ .test q)) :=
      .seqCongr (.refl _) (.testAnd _ _)
    exact (testResult_seq ihp ihq).imp (fun k => .trans h k) (fun k => .trans h k)
  | pOr p q ihp ihq =>
    have h : Derives (a ⨟ .test (.pOr p q)) (a ⨟ (.test p ⊕ .test q)) :=
      .seqCongr (.refl _) (.testOr _ _)
    exact (testResult_union ihp ihq).imp (fun k => .trans h k) (fun k => .trans h k)
  | pNot p ih =>
    rcases ih with h | h
    · exact .inr (.trans (.seqCongr (.symm h) (.refl _))
        (.trans (.symm (.seqAssoc _ _ _))
          (.trans (.seqCongr (.refl _) (.baContra p)) (.seqZero _))))
    · have he : Derives (a ⨟ (.test p ⊕ .test (.pNot p))) a :=
        .trans (.seqCongr (.refl _) (.baExclMid p)) (.seqOne _)
      have hu : Derives (a ⨟ (.test p ⊕ .test (.pNot p))) (a ⨟ .test (.pNot p)) :=
        .trans (.seqDistL _ _ _) (.trans (.unionCongr h (.refl _))
          (.trans (.plusComm _ _) (.plusZero _)))
      exact .inl (.trans (.symm hu) he)

private theorem write_completeTest_result (β γ : CtxPkt) :
    TestResult (NetKAT.completeAssignExpr β) (.completeTest γ) := by
  have h (xs : List FieldName) :
      TestResult (NetKAT.completeAssignExpr β) (word (reads γ) xs) := by
    induction xs with
    | nil => exact .inl (.seqOne _)
    | cons f fs ih =>
      have hd := write_fieldTest β f (γ f)
      by_cases he : β f = γ f
      · exact testResult_seq (p := reads γ f) (.inl (by simpa only [if_pos he] using hd)) ih
      · exact testResult_seq (p := reads γ f) (.inr (by simpa only [if_neg he] using hd)) ih
  have hd : Derives (NetKAT.completeAssignExpr β ⨟ .completeTest γ)
      (NetKAT.completeAssignExpr β ⨟ word (reads γ) NetKAT.fieldEnum) :=
    .seqCongr (.refl _) (read_eq γ)
  exact (h NetKAT.fieldEnum).imp (fun k => .trans hd k) (fun k => .trans hd k)

private theorem write_completeTest (β γ : CtxPkt) :
    Derives (NetKAT.completeAssignExpr β ⨟ .completeTest γ)
      (if β = γ then NetKAT.completeAssignExpr β else .drop) := by
  classical
  have output : Semantics (NetKAT.completeAssignExpr β) β β :=
    (completeAssignExpr_sem β β β).mpr rfl
  rcases write_completeTest_result β γ with h | h
  · obtain ⟨ρ, hρ, htest⟩ := (h.sound β β).mpr output
    have hρ' := (completeAssignExpr_sem β β ρ).mp hρ
    subst ρ
    have he := ((completeTest_singleton γ β β).mp htest).1
    simpa only [if_pos he] using h
  · by_cases he : β = γ
    · subst γ
      exact False.elim ((h.sound β β).mp ⟨β, output, (completeTest_singleton β β β).mpr ⟨rfl, rfl⟩⟩)
    · simpa only [if_neg he] using h

theorem branch_seq_match (α β δ : CtxPkt) :
    Derives (NormalForm.ofSummand (α, β) ⨟ NormalForm.ofSummand (β, δ))
      (NormalForm.ofSummand (α, δ)) := by
  have h := write_completeTest β β
  simp only [if_pos rfl] at h
  change Derives ((.completeTest α ⨟ NetKAT.completeAssignExpr β) ⨟
    (.completeTest β ⨟ NetKAT.completeAssignExpr δ)) _
  exact .trans (.symm (.seqAssoc _ _ _))
    (.seqCongr (.refl _) (.trans (.seqAssoc _ _ _)
      (.trans (.seqCongr h (.refl _)) (write_write β δ))))

theorem branch_seq_mismatch (α β γ δ : CtxPkt) (h : β ≠ γ) :
    Derives (NormalForm.ofSummand (α, β) ⨟ NormalForm.ofSummand (γ, δ)) .drop := by
  have hd := write_completeTest β γ
  simp only [if_neg h] at hd
  change Derives ((.completeTest α ⨟ NetKAT.completeAssignExpr β) ⨟
    (.completeTest γ ⨟ NetKAT.completeAssignExpr δ)) _
  exact .trans (.symm (.seqAssoc _ _ _))
    (.trans (.seqCongr (.refl _) (.trans (.seqAssoc _ _ _)
      (.trans (.seqCongr hd (.refl _)) (.zeroSeq _)))) (.seqZero _))

private theorem sumOn_to_pairs {α : Type} {xs : List α} {f : α → NetKAT}
    (h : ∀ x ∈ xs, ∃ ys, Derives (f x) (pairSum ys)) :
    ∃ ys, Derives (sumOn xs f) (pairSum ys) := by
  induction xs with
  | nil => exact ⟨[], .refl _⟩
  | cons x xs ih =>
    obtain ⟨ys, hy⟩ := h x List.mem_cons_self
    obtain ⟨zs, hz⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact ⟨ys ++ zs, .trans (.unionCongr hy hz) (pairSum_append ys zs)⟩

private theorem branch_post_test (α β : CtxPkt) (t : NetKAT)
    (ht : TestResult (NetKAT.completeAssignExpr β) t) :
    ∃ xs, Derives (NormalForm.ofSummand (α, β) ⨟ t) (pairSum xs) := by
  rcases ht with ht | ht
  · exact ⟨[(α, β)], .trans (.symm (.seqAssoc _ _ _))
      (.trans (.seqCongr (.refl _) ht) (.symm (.plusZero _)))⟩
  · exact ⟨[], .trans (.symm (.seqAssoc _ _ _)) (.trans (.seqCongr (.refl _) ht) (.seqZero _))⟩

theorem derives_assign1_pairs (f : FieldName) (v : FieldValueEnum) :
    Derives (.assign1 f v) (pairSum (packetList.map fun σ => (σ, Packet.update σ f v))) := by
  let xs : List (CompleteTest × CompleteAssignmentValuation) := packetList.map fun σ => (σ, σ)
  have hd : Derives (.assign1 f v)
      (sumOn xs (fun b => NormalForm.ofSummand b ⨟ .assign1 f v)) :=
    .trans (.symm (.oneSeq _))
      (.trans (.seqCongr derives_id_diagonal (.refl _)) (sumOn_seq_right xs NormalForm.ofSummand _))
  refine .trans hd ?_
  change Derives (sumOn (packetList.map fun σ => (σ, σ)) (fun b => NormalForm.ofSummand b ⨟ .assign1 f v))
    (sumOn (packetList.map fun σ => (σ, Packet.update σ f v)) NormalForm.ofSummand)
  rw [sumOn_map, sumOn_map]
  exact sumOn_congr (fun σ _ =>
    .trans (.symm (.seqAssoc _ _ _)) (.seqCongr (.refl _) (write_assign σ f v)))

theorem pairSum_seq (xs ys : List (CompleteTest × CompleteAssignmentValuation)) :
    ∃ zs, Derives (pairSum xs ⨟ pairSum ys) (pairSum zs) := by
  have hd := sumOn_seq_right xs NormalForm.ofSummand (pairSum ys)
  obtain ⟨zs, hz⟩ := sumOn_to_pairs (xs := xs)
    (f := fun b => NormalForm.ofSummand b ⨟ pairSum ys) (by
      rintro ⟨α, β⟩ _
      have hleft := sumOn_seq_left (NormalForm.ofSummand (α, β)) ys NormalForm.ofSummand
      obtain ⟨bs, hb⟩ := sumOn_to_pairs (xs := ys)
        (f := fun b => NormalForm.ofSummand (α, β) ⨟ NormalForm.ofSummand b) (by
          rintro ⟨γ, δ⟩ _
          classical
          by_cases he : β = γ
          · subst γ
            exact ⟨[(α, δ)], .trans (branch_seq_match α β δ) (.symm (.plusZero _))⟩
          · exact ⟨[], branch_seq_mismatch α β γ δ he⟩)
      exact ⟨bs, .trans hleft hb⟩)
  exact ⟨zs, .trans hd hz⟩

theorem normalize_derives_seq {p q : NetKAT} (hp : Derives p (normalize p))
    (hq : Derives q (normalize q)) : Derives (p ⨟ q) (normalize (p ⨟ q)) := by
  obtain ⟨zs, hz⟩ := pairSum_seq (symbolicPairs p) (symbolicPairs q)
  exact derives_to_normalize (.trans (.seqCongr hp hq) hz)

/-- Reduce a star-free policy starting from one known packet. The
resulting branches arise from the policy's syntax and assignments. -/
private theorem branch_derives_pairSum (p : NetKAT) (free : StarFree p)
    (α β : CtxPkt) :
    ∃ xs, Derives (NormalForm.ofSummand (α, β) ⨟ p) (pairSum xs) := by
  induction p generalizing α β with
  | drop => exact ⟨[], .seqZero _⟩
  | id => exact ⟨[(α, β)], .trans (.seqOne _) (.symm (.plusZero _))⟩
  | test p => exact branch_post_test α β _ (write_testResult β p)
  | completeTest γ => exact branch_post_test α β _ (write_completeTest_result β γ)
  | assign1 f v =>
    exact ⟨[(α, Packet.update β f v)], .trans (.symm (.seqAssoc _ _ _))
      (.trans (.seqCongr (.refl _) (write_assign β f v)) (.symm (.plusZero _)))⟩
  | union p q ihp ihq =>
    obtain ⟨xs, hx⟩ := ihp free.1 α β
    obtain ⟨ys, hy⟩ := ihq free.2 α β
    exact ⟨xs ++ ys, .trans (.seqDistL _ _ _) (.trans (.unionCongr hx hy) (pairSum_append xs ys))⟩
  | seq p q ihp ihq =>
    obtain ⟨xs, hx⟩ := ihp free.1 α β
    obtain ⟨ys, hy⟩ := sumOn_to_pairs (xs := xs)
      (f := fun a => NormalForm.ofSummand a ⨟ q)
      (fun (a, b) _ => ihq free.2 a b)
    exact ⟨ys, .trans (.seqAssoc _ _ _) (.trans (.seqCongr hx (.refl _))
      (.trans (sumOn_seq_right xs NormalForm.ofSummand q) hy))⟩
  | star => exact False.elim free

private theorem word_snoc (f : FieldName → NetKAT) (fs : List FieldName) (g : FieldName) :
    Derives (word f (fs ++ [g])) (word f fs ⨟ f g) := by
  induction fs with
  | nil => exact .trans (.seqOne _) (.symm (.oneSeq _))
  | cons x xs ih => exact .trans (.seqCongr (.refl _) ih) (.seqAssoc _ _ _)

private theorem lift_field_agreement (readPart p q : NetKAT) (f : FieldName)
    (h : ∀ v, Derives ((readPart ⨟ NetKAT.fieldTest f v) ⨟ p)
      ((readPart ⨟ NetKAT.fieldTest f v) ⨟ q)) :
    Derives (readPart ⨟ p) (readPart ⨟ q) := by
  have reduce (t : NetKAT) :
      Derives (sumOn values (fun v => (readPart ⨟ NetKAT.fieldTest f v) ⨟ t)) (readPart ⨟ t) :=
    .trans (.symm (sumOn_seq_right _ _ _))
      (.seqCongr (.trans (.symm (sumOn_seq_left _ _ _))
        (.trans (.seqCongr (.refl _) (.paMatchAll f)) (.seqOne _))) (.refl _))
  exact (reduce p).symm.trans ((sumOn_congr (fun v _ => h v)).trans (reduce q))

/-- Discharge observations one field at a time using PA-MATCH-ALL.
The induction ranges over fields and the local value list only. -/
private theorem lift_read_agreement {p q : NetKAT} (fs gs : List FieldName) (σ : CtxPkt)
    (distinct : (fs ++ gs).Nodup)
    (h : ∀ τ, (∀ f ∈ fs, τ f = σ f) →
      Derives (word (reads τ) (fs ++ gs) ⨟ p) (word (reads τ) (fs ++ gs) ⨟ q)) :
    Derives (word (reads σ) fs ⨟ p) (word (reads σ) fs ⨟ q) := by
  induction gs generalizing fs σ with
  | nil => simpa using h σ (fun _ _ => rfl)
  | cons g gs ih =>
    apply lift_field_agreement _ p q g
    intro v
    let τ := Packet.update σ g v
    have hdistinct : (fs ++ [g] ++ gs).Nodup := by simpa [List.append_assoc] using distinct
    have hg : g ∉ fs := by
      have hn := (List.nodup_append.mp distinct).2.2
      exact fun hm => hn hm (by simp)
    have agree (f : FieldName) (hf : f ∈ fs) : τ f = σ f :=
      Packet.get_update_diff σ g f v (fun eq => hg (eq ▸ hf))
    have more := ih (fs ++ [g]) τ hdistinct (by
      intro ρ hρ
      have hh := h ρ (fun f hf => (hρ f (List.mem_append_left _ hf)).trans (agree f hf))
      simpa [List.append_assoc] using hh)
    have tail : Derives (word (reads τ) (fs ++ [g]))
        (word (reads σ) fs ⨟ NetKAT.fieldTest g v) := by
      refine (word_snoc _ fs g).trans (.seqCongr (word_congr ?_) ?_)
      · intro f hf
        rw [reads, reads, agree f hf]
        exact .refl _
      · rw [reads, show τ g = v from Packet.get_update_same σ g v]
        exact .refl _
    exact (.seqCongr tail.symm (.refl p) : Derives _ _).trans
      (more.trans (.seqCongr tail (.refl q)))

/-- Packet-specific completeness for star-free syntax. Compare branches
under one input observation, then discharge those observations using only
the field-level partition axiom. -/
theorem derives_of_equiv_starFree {p q : NetKAT} (hp : StarFree p) (hq : StarFree q)
    (h : ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ) : Derives p q := by
  have prefixed (σ : CtxPkt) :
      Derives (.completeTest σ ⨟ p) (.completeTest σ ⨟ q) := by
    obtain ⟨xs, hx⟩ := branch_derives_pairSum p hp σ σ
    obtain ⟨ys, hy⟩ := branch_derives_pairSum q hq σ σ
    have hs : IsPairSum (pairSum xs) := ⟨xs, rfl⟩
    have ht : IsPairSum (pairSum ys) := ⟨ys, rfl⟩
    have eq : Derives (pairSum xs) (pairSum ys) :=
      hs.derives_of_equiv ht (fun x y => (hx.sound x y).symm.trans
        ((seq_sem _ _ x y).trans ((exists_congr fun z => and_congr_right' (h z y)).trans
          ((seq_sem _ _ x y).symm.trans (hy.sound x y)))))
    exact (.seqCongr (read_write_self σ).symm (.refl p) : Derives _ _).trans
      (hx.trans (eq.trans (hy.symm.trans (.seqCongr (read_write_self σ) (.refl q)))))
  have lifted := lift_read_agreement (p := p) (q := q) [] NetKAT.fieldEnum examplePacket
    (by simpa using NetKAT.fieldEnum_nodup) (by
      intro σ _
      exact (.seqCongr (read_eq σ).symm (.refl p) : Derives _ _).trans
        ((prefixed σ).trans (.seqCongr (read_eq σ) (.refl q))))
  exact (Derives.oneSeq p).symm.trans (lifted.trans (.oneSeq q))

private theorem below_seq_left (p : NetKAT) {a b : NetKAT} (h : Below a b) :
    Below (p ⨟ a) (p ⨟ b) :=
  .trans (.symm (.seqDistL _ _ _)) (.seqCongr (.refl _) h)

/-- The first symbolic star approximation lies below the original star. -/
theorem star_seed_below (p : NetKAT) : Derives ((.id ⊕ p) ⊕ .star p) (.star p) := by
  have unfoldLeft := below_of_derives (Derives.unrollL p)
  have hid := below_trans (below_left _ _) unfoldLeft
  have hp : Below p (.star p) :=
    below_trans (below_of_derives (.symm (.seqOne p)))
      (below_trans (below_seq_left p hid) (below_trans (below_right _ _) unfoldLeft))
  exact below_union hid hp

/-- A symbolic squaring round preserves the algebraic upper bound by star. -/
theorem star_square_below {p r : NetKAT} (h : Derives (r ⊕ .star p) (.star p)) :
    Derives ((r ⊕ (r ⨟ r)) ⊕ .star p) (.star p) := by
  have hright := below_trans (below_right _ _) (below_of_derives (Derives.unrollR p))
  have hstar : Below (.star p ⨟ .star p) (.star p) :=
    Derives.lfpR (below_union (.plusIdem _) hright)
  exact below_union h (below_trans (below_seq_right h r)
    (below_trans (below_seq_left (.star p) h) hstar))

/-- A right-star fixed point below star is derivably equal to star. -/
theorem derives_star_of_fixed {p r : NetKAT}
    (lower : Derives (r ⊕ .star p) (.star p)) (fixed : Derives (.id ⊕ (r ⨟ p)) r) :
    Derives (.star p) r := by
  have upper : Below (.id ⨟ .star p) r := Derives.lfpR (below_of_derives fixed)
  exact derives_of_below
    (.trans (.unionCongr (.symm (.oneSeq _)) (.refl _)) upper) lower

open scoped Computability in
open KATLean.Native.Boolean in
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
    exact ⟨r ⊕ t, ⟨hrf, htf⟩, .unionCongr hr ht⟩
  | seq p q ihp ihq =>
    obtain ⟨r, hrf, hr⟩ := ihp
    obtain ⟨t, htf, ht⟩ := ihq
    exact ⟨r ⨟ t, ⟨hrf, htf⟩, .seqCongr hr ht⟩
  | star p ih =>
    obtain ⟨body, hfree, hbody⟩ := ih
    let Inv (g : symbolicSchema.DiagramGuard) := ∃ r,
      StarFree r ∧ symbolicSchema.Represents g (katInterp r) ∧
        Derives (r ⊕ .star p) (.star p)
    have base : Inv (disj symbolicSchema.skip (compileSymbolic p)) := by
      have hrep := compileSymbolic_correct p
      rw [hbody.katSound] at hrep
      exact ⟨.id ⊕ body, ⟨trivial, hfree⟩,
        symbolicSchema.union_correct symbolicSchema.skip_correct hrep,
        Derives.trans (.unionCongr (.unionCongr (.refl _) hbody.symm) (.refl _)) (star_seed_below p)⟩
    have step (g) (h : Inv g) : Inv (disj g (symbolicSchema.seq g g)) := by
      obtain ⟨r, hf, hr, hu⟩ := h
      exact ⟨r ⊕ (r ⨟ r), ⟨hf, hf, hf⟩,
        symbolicSchema.union_correct hr (symbolicSchema.seq_correct hr hr), star_square_below hu⟩
    obtain ⟨r, hf, hr, hu⟩ := symbolicSchema.star_induction base step
    have heq : katInterp r = katInterp (.star p) :=
      symbolicSchema.represents_unique hr (compileSymbolic_correct (.star p))
    have hfixed : Derives (.id ⊕ (r ⨟ body)) r := by
      apply derives_of_equiv_starFree (p := .id ⊕ (r ⨟ body)) ⟨trivial, hf, hfree⟩ hf
      apply katInterp_eq_iff.mp
      rw [katInterp_union, katInterp_seq, ← hbody.katSound, heq, katInterp_star]
      exact KATLean.star_unfold_right _
    have hfixed' : Derives (.id ⊕ (r ⨟ p)) r :=
      Derives.trans (.unionCongr (.refl _) (.seqCongr (.refl _) hbody)) hfixed
    exact ⟨r, hf, derives_star_of_fixed hu hfixed'⟩

/-- Lift star-free completeness to normalization using exact symbolic closure. -/
theorem normalize_derives_of_starFree_complete (complete : StarFreeComplete) (p : NetKAT) :
    Derives p (normalize p) := by
  obtain ⟨r, hf, hr⟩ := exists_derives_starFree_symbolic p
  exact hr.trans (complete hf (normalize_starFree p)
    (fun σ τ => (hr.sound σ τ).symm.trans (normalize_correct p σ τ).symm))

theorem symbolic_normalize_correct (p : NetKAT) : Derives p (symbolicNormalize p) :=
  normalize_derives_of_starFree_complete (@derives_of_equiv_starFree) p

theorem normalize_derives (p : NetKAT) : Derives p (normalize p) :=
  symbolic_normalize_correct p

theorem normalize_derives_starFree (p : NetKAT) (h : StarFree p) : Derives p (normalize p) :=
  derives_of_equiv_starFree h (normalize_starFree p) (fun σ τ => (normalize_correct p σ τ).symm)

theorem starFree_complete : StarFreeComplete := @derives_of_equiv_starFree

theorem normalize_derives_id : Derives .id (normalize .id) := normalize_derives .id

theorem normalize_derives_test (p : Predicate) : Derives (.test p) (normalize (.test p)) :=
  normalize_derives (.test p)

theorem normalize_derives_completeTest (γ : CtxPkt) :
    Derives (.completeTest γ) (normalize (.completeTest γ)) :=
  normalize_derives (.completeTest γ)

theorem normalize_derives_assign1 (f : FieldName) (v : FieldValueEnum) :
    Derives (.assign1 f v) (normalize (.assign1 f v)) :=
  normalize_derives (.assign1 f v)

-- Compatibility with the concrete diagonal partition.
/-- A predicate derives to the diagonal branches for precisely its satisfying packets. -/
theorem derives_test_pairs (p : Predicate) :
    Derives (.test p) (pairSum ((packetList.filter p.eval).map fun σ => (σ, σ))) := by
  let xs := (packetList.filter p.eval).map (fun σ => (σ, σ))
  have h : ∀ σ τ, Semantics (.test p) σ τ ↔ Semantics (pairSum xs) σ τ := by
    intro σ τ
    rw [pairSum_sem]
    change (p.holds σ ∧ σ = τ) ↔ (σ, τ) ∈ xs
    constructor
    · rintro ⟨hp, rfl⟩
      exact List.mem_map.mpr ⟨σ, List.mem_filter.mpr ⟨mem_packetList σ, hp⟩, rfl⟩
    · intro hm
      obtain ⟨ρ, hρ, he⟩ := List.mem_map.mp hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨(List.mem_filter.mp hρ).2, rfl⟩
  exact .trans (normalize_derives_test p)
    ((normalize_pairSum (.test p)).derives_of_equiv ⟨xs, rfl⟩
      (fun σ τ => (normalize_correct _ σ τ).trans (h σ τ)))

/-- DyNetKAT v4 Lemma 5 with the original complete-pair syntax. -/
theorem exists_derives_pairSum (p : NetKAT) : ∃ q, IsPairSum q ∧ Derives p q :=
  ⟨normalize p, normalize_pairSum p, normalize_derives p⟩

end DyNetKAT.NetKAT
