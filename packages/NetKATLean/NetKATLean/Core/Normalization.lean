import NetKATLean.Core.NormalForm
import NetKATLean.Core.Axioms
import NetKATLean.Core.Symbolic

namespace DyNetKAT.NetKAT

local instance : DecidableEq CompleteTest := (inferInstance : DecidableEq CtxPkt)
local instance : DecidableEq CompleteAssignmentValuation := (inferInstance : DecidableEq CtxPkt)

/-- The complete test succeeds exactly on its own valuation and preserves it. -/
theorem completeTest_singleton {schema : PacketSchema} (α σ τ : schema.Packet) :
    Semantics (.completeTest α) σ τ ↔ σ = α ∧ σ = τ := by
  change (holdsComplete α σ ∧ σ = τ) ↔ _
  rw [holdsComplete_iff_eq]

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

section FiniteSchema

variable {schema : PacketSchema} [diagram : DiagramLayout schema]

local instance (f : schema.Field) : DecidableEq (schema.Value f) := schema.valueEq f

/-- The symbolic normal form stores a reduced relation diagram. -/
def symbolicNormalFormFor (p : NetKAT schema) : diagram.layout.DiagramGuard :=
  compileSymbolic p

theorem symbolicNormalFormFor_correct (p : NetKAT schema) :
    diagram.layout.Represents (symbolicNormalFormFor p) (katInterp p) :=
  compileSymbolic_correct p

/-- Expand a symbolic normal form when concrete paper summands are requested. -/
def symbolicPairsFor (p : NetKAT schema) : List (schema.Packet × schema.Packet) :=
  diagram.layout.pairs (symbolicNormalFormFor p)

theorem mem_symbolicPairsFor (p : NetKAT schema) (input output : schema.Packet) :
    (input, output) ∈ symbolicPairsFor p ↔ Semantics p input output :=
  (diagram.layout.mem_pairs (symbolicNormalFormFor_correct p) input output).trans
    (katInterp_correct p input output)

private def assignFields (fields : List schema.Field) (target : schema.Packet) : NetKAT schema :=
  fields.foldr (fun f rest => .seq (.assign1 f (target f)) rest) .id

omit diagram in
private theorem assignFields_sem (fields : List schema.Field) (target input output : schema.Packet) :
    Semantics (assignFields fields target) input output ↔
      output = fields.foldl (fun p f => schema.model.update f (target f) p) input := by
  induction fields generalizing input with
  | nil => exact eq_comm
  | cons f tail ih =>
    change (∃ mid, mid = schema.model.update f (target f) input ∧
      Semantics (assignFields tail target) mid output) ↔ _
    simp [ih]

omit diagram in
private theorem fold_update_apply (fields : List schema.Field) (target input : schema.Packet)
    (f : schema.Field) (h : f ∈ fields) :
    (fields.foldl (fun p g => schema.model.update g (target g) p) input) f = target f := by
  have untouched (xs : List schema.Field) (p : schema.Packet) (absent : f ∉ xs) :
      (xs.foldl (fun p g => schema.model.update g (target g) p) p) f = p f := by
    induction xs generalizing p with
    | nil => rfl
    | cons g xs ih =>
      have differ : g ≠ f := fun e => absent (e ▸ List.mem_cons_self)
      rw [List.foldl_cons, ih _ (fun mem => absent (List.mem_cons_of_mem _ mem))]
      exact (schema.lookup_eq f _).symm.trans
        ((schema.model.lookup_update_other g f (target g) p differ).trans (schema.lookup_eq f p))
  induction fields generalizing input with
  | nil => cases h
  | cons g xs ih =>
    rw [List.foldl_cons]
    by_cases later : f ∈ xs
    · exact ih _ later
    · have equal := (List.mem_cons.mp h).resolve_right later
      subst g
      rw [untouched _ _ later]
      exact (schema.lookup_eq f _).symm.trans (schema.model.lookup_update f (target f) input)

/-- Write all fields of one specified packet. -/
def assignPacket (target : schema.Packet) : NetKAT schema :=
  assignFields diagram.layout.fields target

theorem assignPacket_sem (target input output : schema.Packet) :
    Semantics (assignPacket target) input output ↔ output = target := by
  have update : diagram.layout.fields.foldl
      (fun p f => schema.model.update f (target f) p) input = target :=
    funext fun f => fold_update_apply _ _ _ f (diagram.layout.fields_complete f)
  rw [assignPacket, assignFields_sem, update]

/-- One complete-test/assignment branch of the paper's normal form. -/
def packetSummand (pair : schema.Packet × schema.Packet) : NetKAT schema :=
  .seq (.completeTest pair.1) (assignPacket pair.2)

theorem packetSummand_sem (input output : schema.Packet) (pair : schema.Packet × schema.Packet) :
    Semantics (packetSummand pair) input output ↔ (input, output) = pair := by
  rcases pair with ⟨i, o⟩
  change (∃ mid, Semantics (.completeTest i) input mid ∧
    Semantics (assignPacket o) mid output) ↔ _
  simp [completeTest_singleton, assignPacket_sem, Prod.mk.injEq]

/-- Paper-form syntax for an explicitly supplied list of packet pairs. -/
def pairSumFor (pairs : List (schema.Packet × schema.Packet)) : NetKAT schema :=
  pairs.foldr (fun pair rest => .union (packetSummand pair) rest) .drop

theorem pairSumFor_sem (pairs : List (schema.Packet × schema.Packet)) (input output : schema.Packet) :
    Semantics (pairSumFor pairs) input output ↔ (input, output) ∈ pairs := by
  induction pairs with
  | nil => simp [pairSumFor, Semantics]
  | cons pair rest ih =>
    obtain ⟨a, b⟩ := pair
    change ((∃ mid, (holdsComplete a input ∧ input = mid) ∧
      Semantics (assignPacket b) mid output) ∨ Semantics (pairSumFor rest) input output) ↔ _
    simp [assignPacket_sem, holdsComplete_iff_eq, ih]

theorem symbolicPairsFor_sum_correct (p : NetKAT schema) (input output : schema.Packet) :
    Semantics (pairSumFor (symbolicPairsFor p)) input output ↔ Semantics p input output :=
  (pairSumFor_sem _ _ _).trans (mem_symbolicPairsFor _ _ _)

theorem symbolicPairsFor_history_correct (p : NetKAT schema) (input output : History schema.Packet) :
    HistorySemantics (pairSumFor (symbolicPairsFor p)) input output ↔
      HistorySemantics p input output := by
  obtain ⟨i, it⟩ := input
  obtain ⟨o, ot⟩ := output
  rw [historySemantics_iff_packetSemantics, historySemantics_iff_packetSemantics]
  exact and_congr_right (fun _ => symbolicPairsFor_sum_correct p i o)

end FiniteSchema

/-- The compact normal form is the reduced packet relation diagram.
Only the paper's explicit pair syntax and heads require materialization. -/
def symbolicNormalForm (p : NetKAT) : symbolicSchema.DiagramGuard :=
  symbolicNormalFormFor p

theorem symbolicNormalForm_correct (p : NetKAT) :
    symbolicSchema.Represents (symbolicNormalForm p) (katInterp p) :=
  symbolicNormalFormFor_correct p

/-- Materialize the exact paper branches from accepting paths only. -/
def symbolicPairs (p : NetKAT) : List (CompleteTest × CompleteAssignmentValuation) :=
  symbolicPairsFor p

theorem mem_symbolicPairs (p : NetKAT) (σ τ : CtxPkt) :
    (σ, τ) ∈ symbolicPairs p ↔ Semantics p σ τ :=
  mem_symbolicPairsFor p σ τ

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

section FiniteAlgebra

variable {schema : PacketSchema} [diagram : DiagramLayout schema]

local instance (f : schema.Field) : DecidableEq (schema.Value f) := schema.valueEq f
local instance : DecidableEq schema.Field := schema.fieldEq
local instance : DecidableEq schema.Packet := schema.packetEq

/-- Ordered syntax for a finite sum of complete branches. -/
def pairSum (xs : List (schema.Packet × schema.Packet)) : NetKAT schema :=
  pairSumFor xs

theorem pairSum_sem (xs : List (schema.Packet × schema.Packet)) (σ τ : schema.Packet) :
    Semantics (pairSum xs) σ τ ↔ (σ, τ) ∈ xs :=
  pairSumFor_sem xs σ τ

/-- A syntax-level witness for a sum of complete branches. The empty sum is drop. -/
def IsPairSum (p : NetKAT schema) : Prop :=
  ∃ xs : List (schema.Packet × schema.Packet),
    p = pairSum xs

/-- Exact finite sum of complete tests followed by complete assignments. -/
def symbolicNormalize (p : NetKAT schema) : NetKAT schema :=
  pairSum (symbolicPairsFor p)

abbrev normalize (p : NetKAT schema) := symbolicNormalize p

theorem symbolic_normalize_pairSum (p : NetKAT schema) : IsPairSum (symbolicNormalize p) :=
  ⟨symbolicPairsFor p, rfl⟩

theorem normalize_pairSum (p : NetKAT schema) : IsPairSum (normalize p) :=
  symbolic_normalize_pairSum p

theorem normalize_correct (p : NetKAT schema) (σ τ : schema.Packet) :
    Semantics (normalize p) σ τ ↔ Semantics p σ τ :=
  (pairSum_sem _ σ τ).trans (mem_symbolicPairsFor p σ τ)

theorem normalize_history_correct (p : NetKAT schema) (h h' : History schema.Packet) :
    HistorySemantics (normalize p) h h' ↔ HistorySemantics p h h' :=
  symbolicPairsFor_history_correct p h h'

/-- Star-free is a strict subfragment of the dup-free NetKAT schema AST. -/
def StarFree : NetKAT schema → Prop
  | .union p q | .seq p q => StarFree p ∧ StarFree q
  | .star _ => False
  | _ => True

private theorem completeAssignExpr_starFree (π : schema.Packet) :
    StarFree (assignPacket π) := by
  unfold assignPacket
  generalize diagram.layout.fields = fields
  induction fields with
  | nil => trivial
  | cons g fs ih => exact ⟨trivial, ih⟩

theorem IsPairSum.starFree {p : NetKAT schema} (hp : IsPairSum p) : StarFree p := by
  obtain ⟨xs, rfl⟩ := hp
  induction xs with
  | nil => trivial
  | cons pair xs ih => exact ⟨⟨trivial, completeAssignExpr_starFree pair.2⟩, ih⟩

theorem normalize_starFree (p : NetKAT schema) : StarFree (normalize p) :=
  (normalize_pairSum p).starFree

local infixl:65 " ⊕ " => NetKAT.union
local infixl:70 " ⨟ " => NetKAT.seq

private def Below (p q : NetKAT schema) : Prop := Derives (p ⊕ q) q

omit diagram in
private theorem below_trans {a b c : NetKAT schema} (h : Below a b) (k : Below b c) : Below a c :=
  .trans (.unionCongr (.refl _) k.symm)
    (.trans (.plusAssoc _ _ _) (.trans (.unionCongr h (.refl _)) k))

omit diagram in
private theorem below_left (a b : NetKAT schema) : Below a (a ⊕ b) :=
  .trans (.plusAssoc _ _ _) (.unionCongr (.plusIdem _) (.refl _))

private theorem below_right (a b : NetKAT schema) : Below b (a ⊕ b) :=
  .trans (.unionCongr (.refl _) (.plusComm _ _))
    (.trans (below_left _ _) (.plusComm _ _))

omit diagram in
private theorem below_of_derives {a b : NetKAT schema} (h : Derives a b) : Below a b :=
  .trans (.unionCongr h (.refl _)) (.plusIdem _)

omit diagram in
private theorem below_union {a b c : NetKAT schema} (h : Below a c) (k : Below b c) : Below (a ⊕ b) c :=
  .trans (.symm (.plusAssoc _ _ _)) (.trans (.unionCongr (.refl _) k) h)

omit diagram in
private theorem below_seq_right {a b : NetKAT schema} (h : Below a b) (p : NetKAT schema) :
    Below (a ⨟ p) (b ⨟ p) :=
  .trans (.symm (.seqDistR _ _ _)) (.seqCongr h (.refl _))

omit diagram in
private theorem derives_of_below {a b : NetKAT schema} (h : Below a b) (k : Below b a) : Derives a b :=
  .trans k.symm (.trans (.plusComm _ _) h)

private theorem summand_below_sum {a : schema.Packet × schema.Packet}
    {xs : List (schema.Packet × schema.Packet)} (h : a ∈ xs) :
    Below (packetSummand a) (pairSum xs) := by
  induction xs with
  | nil => cases h
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact below_left _ _
    · exact below_trans (ih h) (below_right _ _)

private theorem pairSum_below {xs ys : List (schema.Packet × schema.Packet)}
    (h : ∀ a ∈ xs, a ∈ ys) : Below (pairSum xs) (pairSum ys) := by
  induction xs with
  | nil => exact .trans (.plusComm _ _) (.plusZero _)
  | cons a xs ih =>
    exact below_union (summand_below_sum (h a List.mem_cons_self))
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- Finite sums with the same pairs are derivably equal, regardless of order
or duplicate branches. -/
theorem pairSum_derives {xs ys : List (schema.Packet × schema.Packet)}
    (h : ∀ a, a ∈ xs ↔ a ∈ ys) : Derives (pairSum xs) (pairSum ys) :=
  derives_of_below (pairSum_below (fun a => (h a).mp)) (pairSum_below (fun a => (h a).mpr))

theorem IsPairSum.derives_of_equiv {p q : NetKAT schema} (hp : IsPairSum p) (hq : IsPairSum q)
    (h : ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ) : Derives p q := by
  obtain ⟨xs, rfl⟩ := hp
  obtain ⟨ys, rfl⟩ := hq
  apply pairSum_derives
  rintro ⟨σ, τ⟩
  exact (pairSum_sem xs σ τ).symm.trans ((h σ τ).trans (pairSum_sem ys σ τ))

theorem IsPairSum.derives_normalize {p : NetKAT schema} (hp : IsPairSum p) :
    Derives p (normalize p) :=
  hp.derives_of_equiv (normalize_pairSum p) (fun σ τ => (normalize_correct p σ τ).symm)

theorem normalize_derives_drop : Derives (schema := schema) .drop (normalize .drop) :=
  IsPairSum.derives_normalize ⟨[], rfl⟩

theorem normalize_derives_summand (α : schema.Packet) (π : schema.Packet) :
    Derives (packetSummand (α, π)) (normalize (packetSummand (α, π))) := by
  let p := packetSummand (α, π)
  have hd : Derives p (pairSum [(α, π)]) := .symm (.plusZero p)
  have hs : IsPairSum (pairSum [(α, π)]) := ⟨_, rfl⟩
  exact .trans hd (hs.derives_of_equiv (normalize_pairSum p) (fun σ τ =>
    (hd.sound σ τ).symm.trans (normalize_correct p σ τ).symm))

private theorem pairSum_append (xs ys : List (schema.Packet × schema.Packet)) :
    Derives (pairSum xs ⊕ pairSum ys) (pairSum (xs ++ ys)) := by
  induction xs with
  | nil => exact .trans (.plusComm _ _) (.plusZero _)
  | cons a xs ih => exact .trans (.symm (.plusAssoc _ _ _)) (.unionCongr (.refl _) ih)

theorem normalize_derives_union {p q : NetKAT schema} (hp : Derives p (normalize p))
    (hq : Derives q (normalize q)) : Derives (p ⊕ q) (normalize (p ⊕ q)) := by
  let xs := symbolicPairsFor p
  let ys := symbolicPairsFor q
  have hd : Derives (p ⊕ q) (pairSum (xs ++ ys)) :=
    .trans (.unionCongr hp hq) (pairSum_append xs ys)
  have hshape : IsPairSum (pairSum (xs ++ ys)) := ⟨_, rfl⟩
  exact .trans hd (hshape.derives_of_equiv (normalize_pairSum _) (fun σ τ =>
    (hd.sound σ τ).symm.trans (normalize_correct _ σ τ).symm))

/-- Finite unrolling with zero iterations represented by identity. -/
def boundedPolicy (p : NetKAT schema) : Nat → NetKAT schema
  | 0 => .id
  | n + 1 => let q := boundedPolicy p n; q ⊕ (q ⨟ p)

omit diagram in
theorem boundedPolicy_sem (p : NetKAT schema) (n : Nat) (σ τ : schema.Packet) :
    Semantics (boundedPolicy p n) σ τ ↔ ReachableWithin p n σ τ := by
  induction n generalizing τ with
  | zero => exact eq_comm
  | succ n ih => simp only [boundedPolicy, union_sem, seq_sem, reachableWithin_succ_iff, ih]

omit diagram in
theorem boundedPolicy_starFree {p : NetKAT schema} (hp : StarFree p) (n : Nat) :
    StarFree (boundedPolicy p n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih, ih, hp⟩

private theorem boundedPolicy_below_star (p : NetKAT schema) (n : Nat) :
    Below (boundedPolicy p n) (.star p) := by
  have hu := below_of_derives (Derives.unrollR p)
  induction n with
  | zero => exact below_trans (below_left _ _) hu
  | succ n ih =>
    exact below_union ih (below_trans (below_seq_right ih p) (below_trans (below_right _ _) hu))

private theorem id_below_boundedPolicy (p : NetKAT schema) (n : Nat) :
    Below .id (boundedPolicy p n) := by
  induction n with
  | zero => exact .plusIdem _
  | succ n ih => exact below_trans ih (below_left _ _)

/-- An equational stabilization certificate gives an actual star derivation
via the existing right least-fixpoint rule. -/
theorem derives_star_boundedPolicy {p : NetKAT schema} {n : Nat}
    (h : Derives (boundedPolicy p (n + 1)) (boundedPolicy p n)) :
    Derives (.star p) (boundedPolicy p n) := by
  let q := boundedPolicy p n
  have step : Below (q ⨟ p) q := below_trans (below_right _ _) (below_of_derives h)
  have upper : Below (.id ⨟ .star p) q := Derives.lfpR (below_union (id_below_boundedPolicy p n) step)
  exact derives_of_below
    (.trans (.unionCongr (.symm (.oneSeq _)) (.refl _)) upper)
    (boundedPolicy_below_star p n)

/-- Equational completeness restricted to star-free policies. -/
def StarFreeComplete (schema : PacketSchema := ctxSchema) : Prop :=
  ∀ {p q : NetKAT schema}, StarFree p → StarFree q →
    (∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ) → Derives p q

/-- Pair-sum extensionality upgrades star-free normalization to star-free
semantic completeness. -/
theorem starFreeComplete_iff_normalize :
    StarFreeComplete schema ↔ ∀ p : NetKAT schema, StarFree p → Derives p (normalize p) := by
  constructor
  · intro complete p hp
    exact complete hp (normalize_starFree p) (fun σ τ => (normalize_correct p σ τ).symm)
  · intro normalizeProof p q hp hq he
    have hn : Derives (normalize p) (normalize q) :=
      (normalize_pairSum p).derives_of_equiv (normalize_pairSum q) (fun σ τ =>
        (normalize_correct p σ τ).trans ((he σ τ).trans (normalize_correct q σ τ).symm))
    exact .trans (normalizeProof p hp) (.trans hn (.symm (normalizeProof q hq)))

private def word (f : schema.Field → NetKAT schema) (xs : List schema.Field) : NetKAT schema :=
  xs.foldr (fun x acc => f x ⨟ acc) .id

private def reads (σ : schema.Packet) (f : schema.Field) : NetKAT schema := NetKAT.fieldTestFor f (σ f)
private def writes (σ : schema.Packet) (f : schema.Field) : NetKAT schema := NetKAT.assign1 f (σ f)

omit diagram in
private theorem word_congr {f g : schema.Field → NetKAT schema} {xs : List schema.Field}
    (h : ∀ x ∈ xs, Derives (f x) (g x)) : Derives (word f xs) (word g xs) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    exact .seqCongr (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

omit diagram in
private theorem word_commute (a : NetKAT schema) (f : schema.Field → NetKAT schema) (xs : List schema.Field)
    (h : ∀ x ∈ xs, Derives (a ⨟ f x) (f x ⨟ a)) :
    Derives (a ⨟ word f xs) (word f xs ⨟ a) := by
  induction xs with
  | nil => exact .trans (.seqOne _) (.symm (.oneSeq _))
  | cons x xs ih =>
    exact .trans (.seqAssoc _ _ _) (.trans (.seqCongr (h x List.mem_cons_self) (.refl _))
      (.trans (.symm (.seqAssoc _ _ _))
        (.trans (.seqCongr (.refl _) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))))
          (.seqAssoc _ _ _))))

private theorem word_append_at {f g : schema.Field → NetKAT schema} {xs : List schema.Field}
    {k : schema.Field} {a : NetKAT schema} (hn : xs.Nodup) (hk : k ∈ xs)
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

private theorem word_append_reject {f : schema.Field → NetKAT schema} {xs : List schema.Field}
    {k : schema.Field} {a : NetKAT schema} (hn : xs.Nodup) (hk : k ∈ xs)
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

omit diagram in
private theorem word_prepend_absorb {f : schema.Field → NetKAT schema} {xs : List schema.Field}
    {k : schema.Field} {a : NetKAT schema} (hk : k ∈ xs)
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

omit diagram in
private theorem word_fields_prepend {f : schema.Field → NetKAT schema} (xs : List schema.Field) (q : NetKAT schema)
    (h : ∀ x ∈ xs, Derives (f x ⨟ q) q) : Derives (word f xs ⨟ q) q := by
  induction xs with
  | nil => exact .oneSeq _
  | cons x xs ih =>
    exact .trans (.symm (.seqAssoc _ _ _))
      (.trans (.seqCongr (.refl _) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))))
        (h x List.mem_cons_self))

omit diagram in
private theorem word_fields_append (q : NetKAT schema) {f : schema.Field → NetKAT schema} (xs : List schema.Field)
    (h : ∀ x ∈ xs, Derives (q ⨟ f x) q) : Derives (q ⨟ word f xs) q := by
  induction xs with
  | nil => exact .seqOne _
  | cons x xs ih =>
    exact .trans (.seqAssoc _ _ _) (.trans (.seqCongr (h x List.mem_cons_self) (.refl _))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))))

private theorem read_eq (σ : schema.Packet) :
    Derives (.completeTest σ) (word (reads σ) diagram.layout.fields) :=
  .completeTestExpandFor σ diagram.layout.fields diagram.layout.fields_complete

private theorem read_write_self (σ : schema.Packet) :
    Derives (.completeTest σ ⨟ assignPacket σ) (.completeTest σ) := by
  refine .trans (.seqCongr (read_eq σ) (.refl _)) (.trans ?_ (.symm (read_eq σ)))
  change Derives (word (reads σ) diagram.layout.fields ⨟ word (writes σ) diagram.layout.fields) _
  apply word_fields_append
  intro f _
  apply word_append_at diagram.fields_nodup (diagram.layout.fields_complete f)
  · exact .paFilterMod f (σ f)
  · intro _ _
    rfl
  · intro g hg
    exact .paModFilterComm f g _ _ (Ne.symm hg)

private theorem write_write (β δ : schema.Packet) :
    Derives (assignPacket β ⨟ assignPacket δ)
      (assignPacket δ) := by
  change Derives (word (writes β) diagram.layout.fields ⨟ word (writes δ) diagram.layout.fields) _
  apply word_fields_prepend
  intro f _
  exact word_prepend_absorb (diagram.layout.fields_complete f) (.paModMod f (β f) (δ f))
    (fun g hg => .paModModComm f g _ _ (Ne.symm hg))

private theorem write_fieldTest (β : schema.Packet) (f : schema.Field) (v : schema.Value f) :
    Derives (assignPacket β ⨟ NetKAT.fieldTestFor f v)
      (if β f = v then assignPacket β else .drop) := by
  change Derives (word (writes β) diagram.layout.fields ⨟ _) (if β f = v then word (writes β) diagram.layout.fields else .drop)
  split
  · rename_i h
    subst v
    apply word_append_at diagram.fields_nodup (diagram.layout.fields_complete f)
    · exact .paModFilter f (β f)
    · intro _ _
      rfl
    · intro g hg
      exact .symm (.paModFilterComm g f _ _ hg)
  · rename_i h
    have hit : Derives (NetKAT.assign1 f (β f) ⨟ NetKAT.fieldTestFor f v) .drop :=
      .trans (.seqCongr (.symm (.paModFilter f (β f))) (.refl _))
        (.trans (.symm (.seqAssoc _ _ _)) (.trans (.seqCongr (.refl _) (.paContra f _ _ h)) (.seqZero _)))
    exact word_append_reject diagram.fields_nodup (diagram.layout.fields_complete f) hit
      (fun g hg => .symm (.paModFilterComm g f _ _ hg))

omit diagram in
private theorem updateAt (f : schema.Field) (v : schema.Value f) (p : schema.Packet) :
    schema.model.update f v p f = v :=
  (schema.lookup_eq f _).symm.trans (schema.model.lookup_update f v p)

omit diagram in
private theorem updateAtOther (f g : schema.Field) (v : schema.Value f) (p : schema.Packet)
    (different : f ≠ g) : schema.model.update f v p g = p g :=
  (schema.lookup_eq g _).symm.trans
    ((schema.model.lookup_update_other f g v p different).trans (schema.lookup_eq g p))

private theorem write_assign (β : schema.Packet) (f : schema.Field) (v : schema.Value f) :
    Derives (assignPacket β ⨟ .assign1 f v)
      (assignPacket (schema.model.update f v β)) := by
  change Derives (word (writes β) diagram.layout.fields ⨟ _) (word (writes (schema.model.update f v β)) diagram.layout.fields)
  apply word_append_at diagram.fields_nodup (diagram.layout.fields_complete f)
  · simpa [writes, updateAt] using Derives.paModMod f (β f) v
  · intro g hg
    simp [writes, updateAtOther _ _ _ _ (Ne.symm hg)]
  · intro g hg
    exact .paModModComm f g _ _ (Ne.symm hg)


/-- A finite union of policies, with drop as the empty sum. -/
def sumOn {α : Type} (xs : List α) (f : α → NetKAT schema) : NetKAT schema :=
  xs.foldr (fun x acc => f x ⊕ acc) .drop

omit diagram in
private theorem sumOn_congr {α : Type} {xs : List α} {f g : α → NetKAT schema}
    (h : ∀ x ∈ xs, Derives (f x) (g x)) : Derives (sumOn xs f) (sumOn xs g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    exact .unionCongr (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

omit diagram in
private theorem sumOn_seq_right {α : Type} (xs : List α) (f : α → NetKAT schema) (p : NetKAT schema) :
    Derives (sumOn xs f ⨟ p) (sumOn xs (fun x => f x ⨟ p)) := by
  induction xs with
  | nil => exact .zeroSeq _
  | cons x xs ih => exact .trans (.seqDistR _ _ _) (.unionCongr (.refl _) ih)

omit diagram in
private theorem sumOn_seq_left {α : Type} (p : NetKAT schema) (xs : List α) (f : α → NetKAT schema) :
    Derives (p ⨟ sumOn xs f) (sumOn xs (fun x => p ⨟ f x)) := by
  induction xs with
  | nil => exact .seqZero _
  | cons x xs ih => exact .trans (.seqDistL _ _ _) (.unionCongr (.refl _) ih)

private theorem derives_to_normalize {p : NetKAT schema} {xs : List (schema.Packet × schema.Packet)}
    (h : Derives p (pairSum xs)) : Derives p (normalize p) :=
  .trans h ((show IsPairSum (pairSum xs) from ⟨xs, rfl⟩).derives_of_equiv (normalize_pairSum p)
    (fun σ τ => (h.sound σ τ).symm.trans (normalize_correct p σ τ).symm))

private def TestResult (a p : NetKAT schema) : Prop :=
  Derives (a ⨟ p) a ∨ Derives (a ⨟ p) .drop

omit diagram in
private theorem testResult_seq {a p q : NetKAT schema} (hp : TestResult a p) (hq : TestResult a q) :
    TestResult a (p ⨟ q) := by
  rcases hp with hp | hp
  · have h := Derives.trans (.seqAssoc a p q) (.seqCongr hp (.refl q))
    exact hq.imp (fun k => .trans h k) (fun k => .trans h k)
  · exact .inr (.trans (.seqAssoc _ _ _) (.trans (.seqCongr hp (.refl _)) (.zeroSeq _)))

omit diagram in
private theorem testResult_union {a p q : NetKAT schema} (hp : TestResult a p) (hq : TestResult a q) :
    TestResult a (p ⊕ q) := by
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact .inl (.trans (.seqDistL _ _ _) (.trans (.unionCongr hp hq) (.plusIdem _)))
  · exact .inl (.trans (.seqDistL _ _ _) (.trans (.unionCongr hp hq) (.plusZero _)))
  · exact .inl (.trans (.seqDistL _ _ _) (.trans (.unionCongr hp hq)
      (.trans (.plusComm _ _) (.plusZero _))))
  · exact .inr (.trans (.seqDistL _ _ _) (.trans (.unionCongr hp hq) (.plusZero _)))

private theorem write_testResult (β : schema.Packet) (p : Predicate schema) :
    TestResult (assignPacket β) (.test p) := by
  let a := assignPacket β
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

private theorem write_completeTest_result (β γ : schema.Packet) :
    TestResult (assignPacket β) (.completeTest γ) := by
  have h (xs : List schema.Field) :
      TestResult (assignPacket β) (word (reads γ) xs) := by
    induction xs with
    | nil => exact .inl (.seqOne _)
    | cons f fs ih =>
      have hd := write_fieldTest β f (γ f)
      by_cases he : β f = γ f
      · exact testResult_seq (p := reads γ f) (.inl (by simpa only [if_pos he] using hd)) ih
      · exact testResult_seq (p := reads γ f) (.inr (by simpa only [if_neg he] using hd)) ih
  have hd : Derives (assignPacket β ⨟ .completeTest γ)
      (assignPacket β ⨟ word (reads γ) diagram.layout.fields) :=
    .seqCongr (.refl _) (read_eq γ)
  exact (h diagram.layout.fields).imp (fun k => .trans hd k) (fun k => .trans hd k)

private theorem write_completeTest (β γ : schema.Packet) :
    Derives (assignPacket β ⨟ .completeTest γ)
      (if β = γ then assignPacket β else .drop) := by
  classical
  have output : Semantics (assignPacket β) β β :=
    (assignPacket_sem β β β).mpr rfl
  rcases write_completeTest_result β γ with h | h
  · obtain ⟨ρ, hρ, htest⟩ := (h.sound β β).mpr output
    have hρ' := (assignPacket_sem β β ρ).mp hρ
    subst ρ
    have he := ((completeTest_singleton γ β β).mp htest).1
    simpa only [if_pos he] using h
  · by_cases he : β = γ
    · subst γ
      exact False.elim ((h.sound β β).mp ⟨β, output, (completeTest_singleton β β β).mpr ⟨rfl, rfl⟩⟩)
    · simpa only [if_neg he] using h

theorem branch_seq_match (α β δ : schema.Packet) :
    Derives (packetSummand (α, β) ⨟ packetSummand (β, δ))
      (packetSummand (α, δ)) := by
  have h := write_completeTest β β
  simp only [if_pos rfl] at h
  change Derives ((.completeTest α ⨟ assignPacket β) ⨟
    (.completeTest β ⨟ assignPacket δ)) _
  exact .trans (.symm (.seqAssoc _ _ _))
    (.seqCongr (.refl _) (.trans (.seqAssoc _ _ _)
      (.trans (.seqCongr h (.refl _)) (write_write β δ))))

theorem branch_seq_mismatch (α β γ δ : schema.Packet) (h : β ≠ γ) :
    Derives (packetSummand (α, β) ⨟ packetSummand (γ, δ)) .drop := by
  have hd := write_completeTest β γ
  simp only [if_neg h] at hd
  change Derives ((.completeTest α ⨟ assignPacket β) ⨟
    (.completeTest γ ⨟ assignPacket δ)) _
  exact .trans (.symm (.seqAssoc _ _ _))
    (.trans (.seqCongr (.refl _) (.trans (.seqAssoc _ _ _)
      (.trans (.seqCongr hd (.refl _)) (.zeroSeq _)))) (.seqZero _))

private theorem sumOn_to_pairs {α : Type} {xs : List α} {f : α → NetKAT schema}
    (h : ∀ x ∈ xs, ∃ ys, Derives (f x) (pairSum ys)) :
    ∃ ys, Derives (sumOn xs f) (pairSum ys) := by
  induction xs with
  | nil => exact ⟨[], .refl _⟩
  | cons x xs ih =>
    obtain ⟨ys, hy⟩ := h x List.mem_cons_self
    obtain ⟨zs, hz⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact ⟨ys ++ zs, .trans (.unionCongr hy hz) (pairSum_append ys zs)⟩

private theorem branch_post_test (α β : schema.Packet) (t : NetKAT schema)
    (ht : TestResult (assignPacket β) t) :
    ∃ xs, Derives (packetSummand (α, β) ⨟ t) (pairSum xs) := by
  rcases ht with ht | ht
  · exact ⟨[(α, β)], .trans (.symm (.seqAssoc _ _ _))
      (.trans (.seqCongr (.refl _) ht) (.symm (.plusZero _)))⟩
  · exact ⟨[], .trans (.symm (.seqAssoc _ _ _)) (.trans (.seqCongr (.refl _) ht) (.seqZero _))⟩

theorem pairSum_seq (xs ys : List (schema.Packet × schema.Packet)) :
    ∃ zs, Derives (pairSum xs ⨟ pairSum ys) (pairSum zs) := by
  have hd := sumOn_seq_right xs packetSummand (pairSum ys)
  obtain ⟨zs, hz⟩ := sumOn_to_pairs (xs := xs)
    (f := fun b => packetSummand b ⨟ pairSum ys) (by
      rintro ⟨α, β⟩ _
      have hleft := sumOn_seq_left (packetSummand (α, β)) ys packetSummand
      obtain ⟨bs, hb⟩ := sumOn_to_pairs (xs := ys)
        (f := fun b => packetSummand (α, β) ⨟ packetSummand b) (by
          rintro ⟨γ, δ⟩ _
          classical
          by_cases he : β = γ
          · subst γ
            exact ⟨[(α, δ)], .trans (branch_seq_match α β δ) (.symm (.plusZero _))⟩
          · exact ⟨[], branch_seq_mismatch α β γ δ he⟩)
      exact ⟨bs, .trans hleft hb⟩)
  exact ⟨zs, .trans hd hz⟩

theorem normalize_derives_seq {p q : NetKAT schema} (hp : Derives p (normalize p))
    (hq : Derives q (normalize q)) : Derives (p ⨟ q) (normalize (p ⨟ q)) := by
  obtain ⟨zs, hz⟩ := pairSum_seq (symbolicPairsFor p) (symbolicPairsFor q)
  exact derives_to_normalize (.trans (.seqCongr hp hq) hz)

/-- Reduce a star-free policy starting from one known packet. The
resulting branches arise from the policy's syntax and assignments. -/
private theorem branch_derives_pairSum (p : NetKAT schema) (free : StarFree p)
    (α β : schema.Packet) :
    ∃ xs, Derives (packetSummand (α, β) ⨟ p) (pairSum xs) := by
  induction p generalizing α β with
  | drop => exact ⟨[], .seqZero _⟩
  | id => exact ⟨[(α, β)], .trans (.seqOne _) (.symm (.plusZero _))⟩
  | test p => exact branch_post_test α β _ (write_testResult β p)
  | completeTest γ => exact branch_post_test α β _ (write_completeTest_result β γ)
  | assign1 f v =>
    exact ⟨[(α, schema.model.update f v β)], .trans (.symm (.seqAssoc _ _ _))
      (.trans (.seqCongr (.refl _) (write_assign β f v)) (.symm (.plusZero _)))⟩
  | union p q ihp ihq =>
    obtain ⟨xs, hx⟩ := ihp free.1 α β
    obtain ⟨ys, hy⟩ := ihq free.2 α β
    exact ⟨xs ++ ys, .trans (.seqDistL _ _ _) (.trans (.unionCongr hx hy) (pairSum_append xs ys))⟩
  | seq p q ihp ihq =>
    obtain ⟨xs, hx⟩ := ihp free.1 α β
    obtain ⟨ys, hy⟩ := sumOn_to_pairs (xs := xs)
      (f := fun a => packetSummand a ⨟ q)
      (fun (a, b) _ => ihq free.2 a b)
    exact ⟨ys, .trans (.seqAssoc _ _ _) (.trans (.seqCongr hx (.refl _))
      (.trans (sumOn_seq_right xs packetSummand q) hy))⟩
  | star => exact False.elim free

omit diagram in
private theorem word_snoc (f : schema.Field → NetKAT schema) (fs : List schema.Field) (g : schema.Field) :
    Derives (word f (fs ++ [g])) (word f fs ⨟ f g) := by
  induction fs with
  | nil => exact .trans (.seqOne _) (.symm (.oneSeq _))
  | cons x xs ih => exact .trans (.seqCongr (.refl _) ih) (.seqAssoc _ _ _)

private theorem lift_field_agreement (readPart p q : NetKAT schema) (f : schema.Field)
    (h : ∀ v, Derives ((readPart ⨟ NetKAT.fieldTestFor f v) ⨟ p)
      ((readPart ⨟ NetKAT.fieldTestFor f v) ⨟ q)) :
    Derives (readPart ⨟ p) (readPart ⨟ q) := by
  have reduce (t : NetKAT schema) :
      Derives (sumOn (diagram.layout.values f) (fun v => (readPart ⨟ NetKAT.fieldTestFor f v) ⨟ t)) (readPart ⨟ t) :=
    .trans (.symm (sumOn_seq_right _ _ _))
      (.seqCongr (.trans (.symm (sumOn_seq_left _ _ _))
        (.trans (.seqCongr (.refl _) (.paMatchAllFor f _ (diagram.layout.values_complete f))) (.seqOne _))) (.refl _))
  exact (reduce p).symm.trans ((sumOn_congr (fun v _ => h v)).trans (reduce q))

/-- Discharge observations one field at a time using PA-MATCH-ALL.
The induction ranges over fields and the local value list only. -/
private theorem lift_read_agreement {p q : NetKAT schema} (fs gs : List schema.Field) (σ : schema.Packet)
    (distinct : (fs ++ gs).Nodup)
    (h : ∀ τ, (∀ f ∈ fs, τ f = σ f) →
      Derives (word (reads τ) (fs ++ gs) ⨟ p) (word (reads τ) (fs ++ gs) ⨟ q)) :
    Derives (word (reads σ) fs ⨟ p) (word (reads σ) fs ⨟ q) := by
  induction gs generalizing fs σ with
  | nil => simpa using h σ (fun _ _ => rfl)
  | cons g gs ih =>
    apply lift_field_agreement _ p q g
    intro v
    let τ := schema.model.update g v σ
    have hdistinct : (fs ++ [g] ++ gs).Nodup := by simpa [List.append_assoc] using distinct
    have hg : g ∉ fs := by
      have hn := (List.nodup_append.mp distinct).2.2
      exact fun hm => hn hm (by simp)
    have agree (f : schema.Field) (hf : f ∈ fs) : τ f = σ f :=
      updateAtOther g f v σ (fun eq => hg (eq ▸ hf))
    have more := ih (fs ++ [g]) τ hdistinct (by
      intro ρ hρ
      have hh := h ρ (fun f hf => (hρ f (List.mem_append_left _ hf)).trans (agree f hf))
      simpa [List.append_assoc] using hh)
    have tail : Derives (word (reads τ) (fs ++ [g]))
        (word (reads σ) fs ⨟ NetKAT.fieldTestFor g v) := by
      refine (word_snoc _ fs g).trans (.seqCongr (word_congr ?_) ?_)
      · intro f hf
        rw [reads, reads, agree f hf]
        exact .refl _
      · rw [reads, show τ g = v from updateAt g v σ]
        exact .refl _
    exact (.seqCongr tail.symm (.refl p) : Derives _ _).trans
      (more.trans (.seqCongr tail (.refl q)))

/-- Packet-specific completeness for star-free syntax. Compare branches
under one input observation, then discharge those observations using only
the field-level partition axiom. -/
theorem derives_of_equiv_starFree {p q : NetKAT schema} (hp : StarFree p) (hq : StarFree q)
    (h : ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ) : Derives p q := by
  have prefixed (σ : schema.Packet) :
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
  classical
  by_cases inhabited : Nonempty schema.Packet
  · obtain ⟨packet⟩ := inhabited
    have lifted := lift_read_agreement (p := p) (q := q) [] diagram.layout.fields packet
      (by simpa using diagram.fields_nodup) (by
        intro σ _
        exact (.seqCongr (read_eq σ).symm (.refl p) : Derives _ _).trans
          ((prefixed σ).trans (.seqCongr (read_eq σ) (.refl q))))
    exact (Derives.oneSeq p).symm.trans (lifted.trans (.oneSeq q))
  · have emptyDomain : ∃ f, diagram.layout.values f = [] := by
      by_contra anyEmpty
      push_neg at anyEmpty
      apply inhabited
      exact ⟨fun f => (diagram.layout.values f).head (anyEmpty f)⟩
    obtain ⟨f, empty⟩ := emptyDomain
    have all : Derives (matchAllFor f (diagram.layout.values f)) .id :=
      .paMatchAllFor f _ (diagram.layout.values_complete f)
    have collapse : Derives (schema := schema) .drop .id := by
      simpa [empty, matchAllFor] using all
    have zero (s : NetKAT schema) : Derives s .drop :=
      (Derives.oneSeq s).symm.trans ((Derives.seqCongr collapse.symm (.refl s)).trans (.zeroSeq s))
    exact (zero p).trans (zero q).symm

omit diagram in
private theorem below_seq_left (p : NetKAT schema) {a b : NetKAT schema} (h : Below a b) :
    Below (p ⨟ a) (p ⨟ b) :=
  .trans (.symm (.seqDistL _ _ _)) (.seqCongr (.refl _) h)

/-- The first symbolic star approximation lies below the original star. -/
theorem star_seed_below (p : NetKAT schema) : Derives ((.id ⊕ p) ⊕ .star p) (.star p) := by
  have unfoldLeft := below_of_derives (Derives.unrollL p)
  have hid := below_trans (below_left _ _) unfoldLeft
  have hp : Below p (.star p) :=
    below_trans (below_of_derives (.symm (.seqOne p)))
      (below_trans (below_seq_left p hid) (below_trans (below_right _ _) unfoldLeft))
  exact below_union hid hp

/-- A symbolic squaring round preserves the algebraic upper bound by star. -/
theorem star_square_below {p r : NetKAT schema} (h : Derives (r ⊕ .star p) (.star p)) :
    Derives ((r ⊕ (r ⨟ r)) ⊕ .star p) (.star p) := by
  have hright := below_trans (below_right _ _) (below_of_derives (Derives.unrollR p))
  have hstar : Below (.star p ⨟ .star p) (.star p) :=
    Derives.lfpR (below_union (.plusIdem _) hright)
  exact below_union h (below_trans (below_seq_right h r)
    (below_trans (below_seq_left (.star p) h) hstar))

/-- A right-star fixed point below star is derivably equal to star. -/
theorem derives_star_of_fixed {p r : NetKAT schema}
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
theorem exists_derives_starFree_symbolic (p : NetKAT schema) :
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
    let Inv (g : diagram.layout.DiagramGuard) := ∃ r,
      StarFree r ∧ diagram.layout.Represents g (katInterp r) ∧
        Derives (r ⊕ .star p) (.star p)
    have base : Inv (disj diagram.layout.skip (compileSymbolic p)) := by
      have hrep := compileSymbolic_correct p
      rw [hbody.katSound] at hrep
      exact ⟨.id ⊕ body, ⟨trivial, hfree⟩,
        diagram.layout.union_correct diagram.layout.skip_correct hrep,
        Derives.trans (.unionCongr (.unionCongr (.refl _) hbody.symm) (.refl _)) (star_seed_below p)⟩
    have step (g) (h : Inv g) : Inv (disj g (diagram.layout.seq g g)) := by
      obtain ⟨r, hf, hr, hu⟩ := h
      exact ⟨r ⊕ (r ⨟ r), ⟨hf, hf, hf⟩,
        diagram.layout.union_correct hr (diagram.layout.seq_correct hr hr), star_square_below hu⟩
    obtain ⟨r, hf, hr, hu⟩ := diagram.layout.star_induction base step
    have heq : katInterp r = katInterp (.star p) :=
      diagram.layout.represents_unique hr (compileSymbolic_correct (.star p))
    have hfixed : Derives (.id ⊕ (r ⨟ body)) r := by
      apply derives_of_equiv_starFree (p := .id ⊕ (r ⨟ body)) ⟨trivial, hf, hfree⟩ hf
      have eq : katInterp (.id ⊕ (r ⨟ body)) = katInterp r := by
        change 1 + katInterp r * katInterp body = katInterp r
        rw [← hbody.katSound, heq]
        exact KATLean.star_unfold_right _
      intro i o
      rw [← katInterp_correct, ← katInterp_correct, eq]
    have hfixed' : Derives (.id ⊕ (r ⨟ p)) r :=
      Derives.trans (.unionCongr (.refl _) (.seqCongr (.refl _) hbody)) hfixed
    exact ⟨r, hf, derives_star_of_fixed hu hfixed'⟩

/-- Lift star-free completeness to normalization using exact symbolic closure. -/
theorem normalize_derives_of_starFree_complete (complete : StarFreeComplete schema) (p : NetKAT schema) :
    Derives p (normalize p) := by
  obtain ⟨r, hf, hr⟩ := exists_derives_starFree_symbolic p
  exact hr.trans (complete hf (normalize_starFree p)
    (fun σ τ => (hr.sound σ τ).symm.trans (normalize_correct p σ τ).symm))

theorem symbolic_normalize_correct (p : NetKAT schema) : Derives p (symbolicNormalize p) :=
  normalize_derives_of_starFree_complete (fun hp hq eq => derives_of_equiv_starFree hp hq eq) p

theorem normalize_derives (p : NetKAT schema) : Derives p (normalize p) :=
  symbolic_normalize_correct p

theorem normalize_derives_starFree (p : NetKAT schema) (h : StarFree p) : Derives p (normalize p) :=
  derives_of_equiv_starFree h (normalize_starFree p) (fun σ τ => (normalize_correct p σ τ).symm)

theorem starFree_complete : StarFreeComplete schema := fun hp hq eq => derives_of_equiv_starFree hp hq eq

theorem normalize_derives_id : Derives (schema := schema) .id (normalize .id) := normalize_derives .id

theorem normalize_derives_test (p : Predicate schema) : Derives (.test p) (normalize (.test p)) :=
  normalize_derives (.test p)

theorem normalize_derives_completeTest (γ : schema.Packet) :
    Derives (.completeTest γ) (normalize (.completeTest γ)) :=
  normalize_derives (.completeTest γ)

theorem normalize_derives_assign1 (f : schema.Field) (v : schema.Value f) :
    Derives (.assign1 f v) (normalize (.assign1 f v)) :=
  normalize_derives (.assign1 f v)

/-- DyNetKAT v4 Lemma 5 with the original complete-pair syntax. -/
theorem exists_derives_pairSum (p : NetKAT schema) : ∃ q, IsPairSum q ∧ Derives p q :=
  ⟨normalize p, normalize_pairSum p, normalize_derives p⟩

end FiniteAlgebra

end DyNetKAT.NetKAT
