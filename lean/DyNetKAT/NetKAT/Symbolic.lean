import KATLean.NetKAT.Closure
import KATLean.Native
import DyNetKAT.NetKAT.Denotation
import Mathlib.Logic.Equiv.Fin.Basic

/-! The dup-free packet frontend for the native KAT solver. -/

namespace DyNetKAT.NetKAT

open KATLean
open KATLean.NetKAT.Symbolic
open KATLean.Native.Boolean

private def fieldNumber : FieldName ≃ Fin 4 where
  toFun
    | .tpSrc => 0
    | .tpDst => 1
    | .swId => 2
    | .port => 3
  invFun i := match i.val with
    | 0 => .tpSrc
    | 1 => .tpDst
    | 2 => .swId
    | _ => .port
  left_inv := by intro f; cases f <;> rfl
  right_inv := by decide

private def valueNumber : FieldValueEnum ≃ Fin 4 where
  toFun
    | .v0 => 0
    | .v1 => 1
    | .v8 => 2
    | .v9 => 3
  invFun i := match i.val with
    | 0 => .v0
    | 1 => .v1
    | 2 => .v8
    | _ => .v9
  left_inv := by intro a; cases a <;> rfl
  right_inv := by decide

/-- Interleave the three banks for each field/value bit. -/
def symbolicSchema : Schema FieldName FieldValueEnum where
  fields := NetKAT.fieldEnum
  values := [.v0, .v1, .v8, .v9]
  fields_complete := NetKAT.fieldEnum_complete
  values_complete := by intro a; cases a <;> decide
  width := 4 * 4 * 3
  index := (Equiv.prodCongr (((Equiv.prodCongr fieldNumber valueNumber).trans finProdFinEquiv))
    (Equiv.refl (Fin 3))).trans finProdFinEquiv

/-- Boolean guards refer only to the input bank. -/
def compilePredicate : Predicate → symbolicSchema.DiagramGuard
  | .pFalse => falsity
  | .pTrue => truth
  | .pFieldEq fe => symbolicSchema.fieldTest 0 fe.field fe.value
  | .pAnd p q => conj (compilePredicate p) (compilePredicate q)
  | .pOr p q => disj (compilePredicate p) (compilePredicate q)
  | .pNot p => neg (compilePredicate p)

theorem compilePredicate_correct (p : Predicate) (v : symbolicSchema.Bits) (σ : CtxPkt)
    (h : symbolicSchema.Matches 0 v σ) :
    Native.Boolean.eval (compilePredicate p).1 v = p.eval σ := by
  induction p <;> simp [compilePredicate, Predicate.eval, *, symbolicSchema.fieldTest_correct h]

private def identityDiagram : symbolicSchema.DiagramGuard := symbolicSchema.skip

/-- Avoid joining a diagram with the empty or identity relation. A guard
can become empty or identity after compiling a composite policy. -/
private def composeDiagrams (g h : symbolicSchema.DiagramGuard) : symbolicSchema.DiagramGuard :=
  if g = falsity ∨ h = falsity then falsity
  else if g = identityDiagram then h
  else if h = identityDiagram then g
  else symbolicSchema.seq g h

private theorem composeDiagrams_correct {g h : symbolicSchema.DiagramGuard}
    {r t : Rel CtxPkt} (hg : symbolicSchema.Represents g r)
    (hh : symbolicSchema.Represents h t) :
    symbolicSchema.Represents (composeDiagrams g h) (r * t) := by
  unfold composeDiagrams
  split
  · rename_i empty
    rcases empty with rfl | rfl
    · rw [symbolicSchema.represents_unique hg symbolicSchema.drop_correct, zero_mul]
      exact symbolicSchema.drop_correct
    · rw [symbolicSchema.represents_unique hh symbolicSchema.drop_correct, mul_zero]
      exact symbolicSchema.drop_correct
  · split
    · rename_i hid
      have he := symbolicSchema.represents_unique (hid ▸ hg)
        (show symbolicSchema.Represents identityDiagram 1 from symbolicSchema.skip_correct)
      simpa [he] using hh
    · split
      · rename_i hid
        have he := symbolicSchema.represents_unique (hid ▸ hh)
          (show symbolicSchema.Represents identityDiagram 1 from symbolicSchema.skip_correct)
        simpa [he] using hg
      · exact symbolicSchema.seq_correct hg hh

/-- NetKAT compilation computes one symbolic binary relation. Star closes
the diagram under composition using a proved fixed point. -/
def compileSymbolic : NetKAT → symbolicSchema.DiagramGuard
  | .drop => falsity
  | .id => identityDiagram
  | .test p => conj identityDiagram (compilePredicate p)
  | .completeTest α => conj identityDiagram (symbolicSchema.completeTest α)
  | .assign1 f a => symbolicSchema.assign f a
  | .union p q => disj (compileSymbolic p) (compileSymbolic q)
  | .seq p q => composeDiagrams (compileSymbolic p) (compileSymbolic q)
  | .star p => symbolicSchema.star (compileSymbolic p)

theorem compile_test_correct (p : Predicate) :
    symbolicSchema.Represents (compileSymbolic (.test p)) (katInterp (.test p)) :=
  symbolicSchema.filter_correct (fun v σ h => by
    rw [compilePredicate_correct p v σ h, predicateInterp_correct]
    rfl)

theorem compile_assign_correct (f : FieldName) (a : FieldValueEnum) :
    symbolicSchema.Represents (compileSymbolic (.assign1 f a)) (katInterp (schema := ctxSchema) (.assign1 f a)) :=
  symbolicSchema.assign_correct ctxPacketModel (fun _ _ => rfl) f a

theorem compile_completeTest_correct (α : CompleteTest) :
    symbolicSchema.Represents (compileSymbolic (.completeTest α)) (katInterp (schema := ctxSchema) (.completeTest α)) :=
  symbolicSchema.filter_correct (fun v σ h => by
    rw [symbolicSchema.completeTest_correct h]
    exact ⟨fun e f => (congrFun e f).symm, fun e => funext (fun f => (e f).symm)⟩)

theorem compileSymbolic_correct (p : NetKAT) :
    symbolicSchema.Represents (compileSymbolic p) (katInterp p) := by
  induction p with
  | drop => exact symbolicSchema.drop_correct
  | id => exact symbolicSchema.skip_correct
  | test p => exact compile_test_correct p
  | completeTest α => exact compile_completeTest_correct α
  | assign1 f a => exact compile_assign_correct f a
  | union p q hp hq => exact symbolicSchema.union_correct hp hq
  | seq p q hp hq => exact composeDiagrams_correct hp hq
  | star p hp => exact symbolicSchema.star_correct hp

/-- A pair encoding is accepted precisely when the original policy
relates its input and output packets. -/
theorem compileSymbolic_semantics (p : NetKAT) (σ τ : CtxPkt) :
    Native.Boolean.eval (compileSymbolic p).1 (symbolicSchema.encodePair σ τ) = true ↔ Semantics p σ τ :=
  (symbolicSchema.eval_pair (compileSymbolic_correct p) σ τ).trans (katInterp_correct p σ τ)

/-- Embed the symbolic relation as a native test over pair encodings.
Packet updates have already been interpreted before this embedding. -/
def compileNative (p : NetKAT) : Native.Expr (Fin symbolicSchema.width) Empty :=
  .test ((compileSymbolic p).1.toTest id)

theorem compileNative_accept (p : NetKAT) (v : symbolicSchema.Bits) :
    Native.Accept (compileNative p) v [] ↔ Native.Boolean.eval (compileSymbolic p).1 v = true := by
  rw [← Native.nullable_correct, compileNative, Native.nullable, Diagram.toTest_correct]
  rfl

theorem compileNative_correct (p : NetKAT) (σ τ : CtxPkt) :
    Native.Accept (compileNative p) (symbolicSchema.encodePair σ τ) [] ↔ Semantics p σ τ :=
  (compileNative_accept p _).trans (compileSymbolic_semantics p σ τ)

/-- The native solver's action-free case compares the already compiled
output guards directly. -/
def netkatNativeEquiv (p q : NetKAT) : Bool :=
  Native.compareOutputGuards (compileSymbolic p) (compileSymbolic q)

/-- The specialized executable entry point returns the full native solver's
answer on the compiled policies. -/
theorem netkatNativeEquiv_eq_solver (p q : NetKAT) :
    netkatNativeEquiv p q = Native.decideEquiv (compileNative p) (compileNative q) := by
  rw [Bool.eq_iff_iff, netkatNativeEquiv, Native.compareOutputGuards, decide_eq_true_eq,
    Native.decideEquiv_correct, Native.relational_iff_language]
  rw [guard_ext]
  constructor
  · intro same v word
    cases word with
    | nil => rw [compileNative_accept, compileNative_accept, same v]
    | cons first _ => exact first.1.elim
  · intro equivalent v
    apply Bool.eq_iff_iff.mpr
    rw [← compileNative_accept, ← compileNative_accept]
    exact equivalent v []

theorem netkatNativeEquiv_sound {p q : NetKAT} (h : netkatNativeEquiv p q = true) :
    ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ := by
  rw [netkatNativeEquiv_eq_solver] at h
  have langs := (Native.relational_iff_language _ _).mp (Native.decideEquiv_sound _ _ h)
  intro σ τ
  exact (compileNative_correct p σ τ).symm.trans
    ((langs (symbolicSchema.encodePair σ τ) []).trans (compileNative_correct q σ τ))

theorem netkatNativeEquiv_complete {p q : NetKAT} (h : ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ) :
    netkatNativeEquiv p q = true := by
  rw [netkatNativeEquiv_eq_solver]
  apply Native.decideEquiv_complete
  apply (Native.relational_iff_language _ _).mpr
  intro v word
  cases word with
  | nil =>
    rw [compileNative_accept, compileNative_accept, compileSymbolic_correct p v,
      compileSymbolic_correct q v]
    simp only [katInterp_correct, h]
  | cons head _ => exact head.1.elim

theorem netkatNativeEquiv_correct (p q : NetKAT) :
    netkatNativeEquiv p q = true ↔ ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ :=
  ⟨netkatNativeEquiv_sound, netkatNativeEquiv_complete⟩

theorem netkatNativeEquiv_false_iff (p q : NetKAT) :
    netkatNativeEquiv p q = false ↔ ∃ σ τ, ¬ (Semantics p σ τ ↔ Semantics q σ τ) := by
  classical
  rw [← Bool.not_eq_true, netkatNativeEquiv_correct]
  push_neg
  rfl

/-- Symbolic constraints describing exactly the input/output pairs on which
the policies disagree. Invalid one-hot encodings satisfy neither operand. -/
def distinguishingGuard (p q : NetKAT) : symbolicSchema.DiagramGuard :=
  binary (· != ·) (compileSymbolic p) (compileSymbolic q)

theorem distinguishingGuard_correct (p q : NetKAT) (v : symbolicSchema.Bits) :
    Native.Boolean.eval (distinguishingGuard p q).1 v = true ↔
      ∃ σ τ : CtxPkt, symbolicSchema.Matches 0 v σ ∧ symbolicSchema.Matches 1 v τ ∧
        ¬ (Semantics p σ τ ↔ Semantics q σ τ) := by
  rw [distinguishingGuard, binary, apply_correct]
  have hp := compileSymbolic_correct p
  have hq := compileSymbolic_correct q
  have same (σ τ : CtxPkt) (hs : symbolicSchema.Matches 0 v σ)
      (ht : symbolicSchema.Matches 1 v τ) :
      Native.Boolean.eval (compileSymbolic p).1 v =
        Native.Boolean.eval (compileSymbolic q).1 v ↔
        (Semantics p σ τ ↔ Semantics q σ τ) := by
    rw [Bool.eq_iff_iff, symbolicSchema.eval_matched hp hs ht,
      symbolicSchema.eval_matched hq hs ht, katInterp_correct, katInterp_correct]
  constructor
  · intro h
    have someGuard :
        Native.Boolean.eval (compileSymbolic p).1 v = true ∨
        Native.Boolean.eval (compileSymbolic q).1 v = true := by
      cases he : Native.Boolean.eval (compileSymbolic p).1 v <;> simp_all
    rcases someGuard with hP | hQ
    · obtain ⟨σ, τ, hs, ht, _⟩ := (hp v).mp hP
      exact ⟨σ, τ, hs, ht, fun hx => by simp [(same σ τ hs ht).mpr hx] at h⟩
    · obtain ⟨σ, τ, hs, ht, _⟩ := (hq v).mp hQ
      exact ⟨σ, τ, hs, ht, fun hx => by simp [(same σ τ hs ht).mpr hx] at h⟩
  · rintro ⟨σ, τ, hs, ht, h⟩
    have ne := mt (same σ τ hs ht).mp h
    simpa using ne

theorem distinguishingGuard_sat (p q : NetKAT) :
    sat (distinguishingGuard p q).1 = true ↔ netkatNativeEquiv p q = false := by
  rw [sat_correct, netkatNativeEquiv_false_iff]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨σ, τ, _, _, hd⟩ := (distinguishingGuard_correct p q v).mp hv
    exact ⟨σ, τ, hd⟩
  · rintro ⟨σ, τ, hd⟩
    refine ⟨symbolicSchema.encodePair σ τ, (distinguishingGuard_correct p q _).mpr ?_⟩
    refine ⟨σ, τ, ?_, ?_, hd⟩
    · simpa [KATLean.NetKAT.Symbolic.Schema.encodePair] using
        symbolicSchema.matches_encode (fun b => if b = 0 then σ else τ) 0
    · simpa [KATLean.NetKAT.Symbolic.Schema.encodePair] using
        symbolicSchema.matches_encode (fun b => if b = 0 then σ else τ) 1

end DyNetKAT.NetKAT
