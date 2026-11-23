import NetKATLean.PacketAdapter.Closure
import KATLean.Native
import DyNetKAT.NetKAT.Denotation
import Mathlib.Data.Fintype.Sigma
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
def symbolicSchema : Schema FieldName (fun _ => FieldValueEnum) where
  fields := NetKAT.fieldEnum
  values := fun _ => [.v0, .v1, .v8, .v9]
  fields_complete := NetKAT.fieldEnum_complete
  values_complete := by intro _ a; cases a <;> decide
  width := 4 * 4 * 3
  index := (Equiv.prodCongr (((Equiv.sigmaEquivProd FieldName FieldValueEnum).trans
    (Equiv.prodCongr fieldNumber valueNumber)).trans finProdFinEquiv)
    (Equiv.refl (Fin 3))).trans finProdFinEquiv

/-- A choice of field orders and diagram bit indices for an existing packet schema.
The packet values and semantics are supplied by the schema itself. -/
class DiagramLayout (schema : PacketSchema) where
  layout : Schema schema.Field schema.Value
  fields_nodup : layout.fields.Nodup

instance : DiagramLayout ctxSchema := ⟨symbolicSchema, NetKAT.fieldEnum_nodup⟩

/-- The bit indices range over the disjoint sum of local field domains. -/
def DiagramLayout.ofIndices (schema : PacketSchema) {n m : Nat}
    (fields : schema.Field ≃ Fin n) (atoms : Sigma schema.Value ≃ Fin m) :
    DiagramLayout schema := by
  letI := schema.fieldEq
  let values (f : schema.Field) :=
    (List.finRange m).filterMap fun i =>
      let a := atoms.symm i
      if h : a.1 = f then some (h ▸ a.2) else none
  exact ⟨{
    fields := (List.finRange n).map fields.symm
    fields_complete := fun f => List.mem_map.mpr
      ⟨fields f, List.mem_finRange _, fields.symm_apply_apply f⟩
    values := values
    values_complete := by
      intro f v
      apply List.mem_filterMap.mpr
      refine ⟨atoms ⟨f, v⟩, List.mem_finRange _, ?_⟩
      rw [atoms.symm_apply_apply]
      simp
    width := m * 3
    index := (Equiv.prodCongr atoms (Equiv.refl (Fin 3))).trans finProdFinEquiv
  }, (List.nodup_finRange n).map fields.symm.injective⟩

/-- Finite enumeration gives an executable layout up to a choice of ordering.
Order-independent computations can consume the truncation directly. -/
def PacketSchema.diagramLayouts (schema : PacketSchema) : Trunc (DiagramLayout schema) := by
  letI := schema.fieldEq
  letI := schema.valueEq
  letI := schema.fieldFinite
  letI := schema.valueFinite
  exact do
    let fields ← Fintype.truncEquivFin schema.Field
    let atoms ← Fintype.truncEquivFin (Sigma schema.Value)
    pure (DiagramLayout.ofIndices schema fields atoms)

section

variable {schema : PacketSchema} [diagram : DiagramLayout schema]

local instance (f : schema.Field) : DecidableEq (schema.Value f) := schema.valueEq f
local instance : DecidableEq schema.Field := schema.fieldEq


/-- Boolean guards refer only to the input bank. -/
def compilePredicate : Predicate schema → (diagram.layout).DiagramGuard
  | .pFalse => falsity
  | .pTrue => truth
  | .pFieldEq fe => (diagram.layout).fieldTest 0 fe.field fe.value
  | .pAnd p q => conj (compilePredicate p) (compilePredicate q)
  | .pOr p q => disj (compilePredicate p) (compilePredicate q)
  | .pNot p => neg (compilePredicate p)

theorem compilePredicate_correct (p : Predicate schema) (v : (diagram.layout).Bits) (σ : schema.Packet)
    (h : (diagram.layout).Matches 0 v σ) :
    Native.Boolean.eval (compilePredicate p).1 v = p.eval σ := by
  induction p <;> simp [compilePredicate, Predicate.eval, *, (diagram.layout).fieldTest_correct h]

private def identityDiagram : (diagram.layout).DiagramGuard := (diagram.layout).skip

/-- Avoid joining a diagram with the empty or identity relation. A guard
can become empty or identity after compiling a composite policy. -/
private def composeDiagrams (g h : (diagram.layout).DiagramGuard) : (diagram.layout).DiagramGuard :=
  if g = falsity ∨ h = falsity then falsity
  else if g = identityDiagram then h
  else if h = identityDiagram then g
  else (diagram.layout).seq g h

private theorem composeDiagrams_correct {g h : (diagram.layout).DiagramGuard}
    {r t : Rel schema.Packet} (hg : (diagram.layout).Represents g r)
    (hh : (diagram.layout).Represents h t) :
    (diagram.layout).Represents (composeDiagrams g h) (r * t) := by
  unfold composeDiagrams
  split
  · rename_i empty
    rcases empty with rfl | rfl
    · rw [(diagram.layout).represents_unique hg (diagram.layout).drop_correct, zero_mul]
      exact (diagram.layout).drop_correct
    · rw [(diagram.layout).represents_unique hh (diagram.layout).drop_correct, mul_zero]
      exact (diagram.layout).drop_correct
  · split
    · rename_i hid
      have he := (diagram.layout).represents_unique (hid ▸ hg)
        (show (diagram.layout).Represents identityDiagram 1 from (diagram.layout).skip_correct)
      simpa [he] using hh
    · split
      · rename_i hid
        have he := (diagram.layout).represents_unique (hid ▸ hh)
          (show (diagram.layout).Represents identityDiagram 1 from (diagram.layout).skip_correct)
        simpa [he] using hg
      · exact (diagram.layout).seq_correct hg hh

/-- NetKAT compilation computes one symbolic binary relation. Star closes
the diagram under composition using a proved fixed point. -/
def compileSymbolic : NetKAT schema → (diagram.layout).DiagramGuard
  | .drop => falsity
  | .id => identityDiagram
  | .test p => conj identityDiagram (compilePredicate p)
  | .completeTest α => conj identityDiagram ((diagram.layout).completeTest α)
  | .assign1 f a => (diagram.layout).assign f a
  | .union p q => disj (compileSymbolic p) (compileSymbolic q)
  | .seq p q => composeDiagrams (compileSymbolic p) (compileSymbolic q)
  | .star p => (diagram.layout).star (compileSymbolic p)

theorem compile_test_correct (p : Predicate schema) :
    (diagram.layout).Represents (compileSymbolic (.test p)) (katInterp (.test p)) :=
  (diagram.layout).filter_correct (fun v σ h => by
    rw [compilePredicate_correct p v σ h, predicateInterp_correct]
    rfl)

theorem compile_assign_correct (f : schema.Field) (a : schema.Value f) :
    (diagram.layout).Represents (compileSymbolic (.assign1 f a)) (katInterp (schema := schema) (.assign1 f a)) :=
  (diagram.layout).assign_correct schema.model schema.lookup_eq f a

theorem compile_completeTest_correct (α : schema.Packet) :
    (diagram.layout).Represents (compileSymbolic (.completeTest α)) (katInterp (schema := schema) (.completeTest α)) :=
  (diagram.layout).filter_correct (fun v σ h => by
    rw [(diagram.layout).completeTest_correct h]
    exact ⟨fun e f => (congrFun e f).symm, fun e => funext (fun f => (e f).symm)⟩)

theorem compileSymbolic_correct (p : NetKAT schema) :
    (diagram.layout).Represents (compileSymbolic p) (katInterp p) := by
  induction p with
  | drop => exact (diagram.layout).drop_correct
  | id => exact (diagram.layout).skip_correct
  | test p => exact compile_test_correct p
  | completeTest α => exact compile_completeTest_correct α
  | assign1 f a => exact compile_assign_correct f a
  | union p q hp hq => exact (diagram.layout).union_correct hp hq
  | seq p q hp hq => exact composeDiagrams_correct hp hq
  | star p hp => exact (diagram.layout).star_correct hp

/-- A pair encoding is accepted precisely when the original policy
relates its input and output packets. -/
theorem compileSymbolic_semantics (p : NetKAT schema) (σ τ : schema.Packet) :
    Native.Boolean.eval (compileSymbolic p).1 ((diagram.layout).encodePair σ τ) = true ↔ Semantics p σ τ :=
  ((diagram.layout).eval_pair (compileSymbolic_correct p) σ τ).trans (katInterp_correct p σ τ)

/-- Embed the symbolic relation as a native test over pair encodings.
Packet updates have already been interpreted before this embedding. -/
def compileNative (p : NetKAT schema) : Native.Expr (Fin (diagram.layout).width) Empty :=
  .test ((compileSymbolic p).1.toTest id)

theorem compileNative_accept (p : NetKAT schema) (v : (diagram.layout).Bits) :
    Native.Accept (compileNative p) v [] ↔ Native.Boolean.eval (compileSymbolic p).1 v = true := by
  rw [← Native.nullable_correct, compileNative, Native.nullable, Diagram.toTest_correct]
  rfl

theorem compileNative_correct (p : NetKAT schema) (σ τ : schema.Packet) :
    Native.Accept (compileNative p) ((diagram.layout).encodePair σ τ) [] ↔ Semantics p σ τ :=
  (compileNative_accept p _).trans (compileSymbolic_semantics p σ τ)

/-- The native solver's action-free case compares the already compiled
output guards directly. -/
def netkatNativeEquiv (p q : NetKAT schema) : Bool :=
  Native.compareOutputGuards (compileSymbolic p) (compileSymbolic q)

/-- The specialized executable entry point returns the full native solver's
answer on the compiled policies. -/
theorem netkatNativeEquiv_eq_solver (p q : NetKAT schema) :
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

theorem netkatNativeEquiv_sound {p q : NetKAT schema} (h : netkatNativeEquiv p q = true) :
    ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ := by
  rw [netkatNativeEquiv_eq_solver] at h
  have langs := (Native.relational_iff_language _ _).mp (Native.decideEquiv_sound _ _ h)
  intro σ τ
  exact (compileNative_correct p σ τ).symm.trans
    ((langs ((diagram.layout).encodePair σ τ) []).trans (compileNative_correct q σ τ))

theorem netkatNativeEquiv_complete {p q : NetKAT schema} (h : ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ) :
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

theorem netkatNativeEquiv_correct (p q : NetKAT schema) :
    netkatNativeEquiv p q = true ↔ ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ :=
  ⟨netkatNativeEquiv_sound, netkatNativeEquiv_complete⟩

theorem netkatNativeEquiv_false_iff (p q : NetKAT schema) :
    netkatNativeEquiv p q = false ↔ ∃ σ τ, ¬ (Semantics p σ τ ↔ Semantics q σ τ) := by
  classical
  rw [← Bool.not_eq_true, netkatNativeEquiv_correct]
  push_neg
  rfl

/-- Symbolic constraints describing exactly the input/output pairs on which
the policies disagree. Invalid one-hot encodings satisfy neither operand. -/
def distinguishingGuard (p q : NetKAT schema) : (diagram.layout).DiagramGuard :=
  binary (· != ·) (compileSymbolic p) (compileSymbolic q)

theorem distinguishingGuard_correct (p q : NetKAT schema) (v : (diagram.layout).Bits) :
    Native.Boolean.eval (distinguishingGuard p q).1 v = true ↔
      ∃ σ τ : schema.Packet, (diagram.layout).Matches 0 v σ ∧ (diagram.layout).Matches 1 v τ ∧
        ¬ (Semantics p σ τ ↔ Semantics q σ τ) := by
  rw [distinguishingGuard, binary, apply_correct]
  have hp := compileSymbolic_correct p
  have hq := compileSymbolic_correct q
  have same (σ τ : schema.Packet) (hs : (diagram.layout).Matches 0 v σ)
      (ht : (diagram.layout).Matches 1 v τ) :
      Native.Boolean.eval (compileSymbolic p).1 v =
        Native.Boolean.eval (compileSymbolic q).1 v ↔
        (Semantics p σ τ ↔ Semantics q σ τ) := by
    rw [Bool.eq_iff_iff, (diagram.layout).eval_matched hp hs ht,
      (diagram.layout).eval_matched hq hs ht, katInterp_correct, katInterp_correct]
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

theorem distinguishingGuard_sat (p q : NetKAT schema) :
    sat (distinguishingGuard p q).1 = true ↔ netkatNativeEquiv p q = false := by
  rw [sat_correct, netkatNativeEquiv_false_iff]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨σ, τ, _, _, hd⟩ := (distinguishingGuard_correct p q v).mp hv
    exact ⟨σ, τ, hd⟩
  · rintro ⟨σ, τ, hd⟩
    refine ⟨(diagram.layout).encodePair σ τ, (distinguishingGuard_correct p q _).mpr ?_⟩
    refine ⟨σ, τ, ?_, ?_, hd⟩
    · simpa [KATLean.NetKAT.Symbolic.Schema.encodePair] using
        (diagram.layout).matches_encode (fun b => if b = 0 then σ else τ) 0
    · simpa [KATLean.NetKAT.Symbolic.Schema.encodePair] using
        (diagram.layout).matches_encode (fun b => if b = 0 then σ else τ) 1

end

/-- Decide equivalence using only the finite packet schema. The order of
field values can change the diagrams but cannot change the answer. -/
def netkatNativeEquivFinite {schema : PacketSchema} (p q : NetKAT schema) : Bool :=
  schema.diagramLayouts.liftOn (fun d => @netkatNativeEquiv schema d p q) (by
    intro first second
    apply Bool.eq_iff_iff.mpr
    exact (@netkatNativeEquiv_correct schema first p q).trans
      (@netkatNativeEquiv_correct schema second p q).symm)

theorem netkatNativeEquivFinite_correct {schema : PacketSchema} (p q : NetKAT schema) :
    netkatNativeEquivFinite p q = true ↔ ∀ i o, Semantics p i o ↔ Semantics q i o := by
  unfold netkatNativeEquivFinite
  generalize schema.diagramLayouts = layouts
  induction layouts using Trunc.induction_on with
  | _ d => exact @netkatNativeEquiv_correct schema d p q

end DyNetKAT.NetKAT
