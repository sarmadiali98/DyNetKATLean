import KATLean.Native.Syntax
import Mathlib.Data.Fin.Basic

namespace KATLean.Native.Boolean

/-- Ordered decision trees. The type index fixes the variable order;
`skip` omits the current variable without duplicating the subtree. -/
inductive Diagram : Nat → Type
  | leaf (value : Bool) : Diagram n
  | skip (child : Diagram n) : Diagram (n + 1)
  | node (low high : Diagram n) : Diagram (n + 1)
  deriving DecidableEq, Repr

def eval : Diagram n → (Fin n → Bool) → Bool
  | .leaf b, _ => b
  | .skip child, valuation => eval child (fun i => valuation i.succ)
  | .node low high, valuation =>
      if valuation 0 then eval high (fun i => valuation i.succ)
      else eval low (fun i => valuation i.succ)

def Reduced : Diagram n → Prop
  | .leaf _ => True
  | .skip child => Reduced child ∧ ∀ b, child ≠ .leaf b
  | .node low high => Reduced low ∧ Reduced high ∧ low ≠ high

def lift : Diagram n → Diagram (n + 1)
  | .leaf b => .leaf b
  | child => .skip child

def mk (low high : Diagram n) : Diagram (n + 1) :=
  if low = high then lift low else .node low high

@[simp] theorem eval_lift (d : Diagram n) (v : Fin (n + 1) → Bool) :
    eval (lift d) v = eval d (fun i => v i.succ) := by
  cases d <;> rfl

theorem reduced_lift (d : Diagram n) (h : Reduced d) : Reduced (lift d) := by
  cases d <;> simp_all [lift, Reduced]

@[simp] theorem eval_mk (low high : Diagram n) (v : Fin (n + 1) → Bool) :
    eval (mk low high) v =
      if v 0 then eval high (fun i => v i.succ) else eval low (fun i => v i.succ) := by
  unfold mk
  split
  · rename_i same
    simp [same]
  · rfl

theorem reduced_mk (low high : Diagram n) (hl : Reduced low) (hh : Reduced high) :
    Reduced (mk low high) := by
  unfold mk
  split
  · exact reduced_lift low hl
  · exact ⟨hl, hh, by assumption⟩

def low : Diagram (n + 1) → Diagram n
  | .leaf b => .leaf b
  | .skip d => d
  | .node l _ => l

def high : Diagram (n + 1) → Diagram n
  | .leaf b => .leaf b
  | .skip d => d
  | .node _ h => h

theorem reduced_low (d : Diagram (n + 1)) (h : Reduced d) : Reduced (low d) := by
  cases d <;> simp_all [low, Reduced]

theorem reduced_high (d : Diagram (n + 1)) (h : Reduced d) : Reduced (high d) := by
  cases d <;> simp_all [high, Reduced]

theorem eval_low (d : Diagram (n + 1)) (v : Fin n → Bool) :
    eval (low d) v = eval d (Fin.cases false v) := by
  cases d <;> simp [low, eval]

theorem eval_high (d : Diagram (n + 1)) (v : Fin n → Bool) :
    eval (high d) v = eval d (Fin.cases true v) := by
  cases d <;> simp [high, eval]

theorem reconstruct (d : Diagram (n + 1)) (h : Reduced d) : mk (low d) (high d) = d := by
  cases d with
  | leaf b => simp [low, high, mk, lift]
  | skip child =>
    simp only [low, high, mk, ↓reduceIte]
    cases child with
    | leaf b => exact (h.2 b rfl).elim
    | skip d => rfl
    | node l r => rfl
  | node l r => simp [low, high, mk, h.2.2]

/-- Ordered, reduced trees are canonical for Boolean functions. -/
theorem canonical (p q : Diagram n) (hp : Reduced p) (hq : Reduced q)
    (same : ∀ v, eval p v = eval q v) : p = q := by
  induction n with
  | zero =>
    cases p with
    | leaf b =>
      cases q with
      | leaf c => exact congrArg Diagram.leaf (same Fin.elim0)
  | succ n ih =>
    have l := ih (low p) (low q) (reduced_low p hp) (reduced_low q hq)
      (fun v => by rw [eval_low, eval_low]; exact same _)
    have r := ih (high p) (high q) (reduced_high p hp) (reduced_high q hq)
      (fun v => by rw [eval_high, eval_high]; exact same _)
    rw [← reconstruct p hp, ← reconstruct q hq, l, r]

/-- Symbolic satisfiability traverses the diagram, never a valuation table. -/
def sat : Diagram n → Bool
  | .leaf b => b
  | .skip child => sat child
  | .node l r => sat l || sat r

theorem sat_correct (d : Diagram n) : sat d = true ↔ ∃ v, eval d v = true := by
  induction d with
  | leaf b =>
    simp only [sat, eval]
    exact ⟨fun h => ⟨fun _ => false, h⟩, fun ⟨_, h⟩ => h⟩
  | skip child ih =>
    rw [sat, ih]
    constructor
    · rintro ⟨v, h⟩; exact ⟨Fin.cases false v, by simpa [eval] using h⟩
    · rintro ⟨v, h⟩; exact ⟨fun i => v i.succ, h⟩
  | node l r ihl ihr =>
    rw [sat, Bool.or_eq_true, ihl, ihr]
    constructor
    · rintro (⟨v, h⟩ | ⟨v, h⟩)
      · exact ⟨Fin.cases false v, by simpa [eval] using h⟩
      · exact ⟨Fin.cases true v, by simpa [eval] using h⟩
    · rintro ⟨v, h⟩
      cases value : v 0
      · exact Or.inl ⟨fun i => v i.succ, by simpa [eval, value] using h⟩
      · exact Or.inr ⟨fun i => v i.succ, by simpa [eval, value] using h⟩

/-- Negation preserves sharing of skipped levels and reduces every node. -/
def negate : Diagram n → Diagram n
  | .leaf b => .leaf (!b)
  | .skip d => lift (negate d)
  | .node l r => mk (negate l) (negate r)

@[simp] theorem negate_correct (d : Diagram n) (v : Fin n → Bool) :
    eval (negate d) v = !eval d v := by
  induction d with
  | leaf b => rfl
  | skip d ih => simpa [negate, eval] using ih (fun i => v i.succ)
  | node l r ihl ihr =>
    simp only [negate, eval_mk, eval, ihl, ihr]
    cases v 0 <;> rfl

theorem reduced_negate (d : Diagram n) (h : Reduced d) : Reduced (negate d) := by
  induction d with
  | leaf b => trivial
  | skip d ih => exact reduced_lift _ (ih h.1)
  | node l r ihl ihr => exact reduced_mk _ _ (ihl h.1) (ihr h.2.1)

def unary (op : Bool → Bool) (d : Diagram n) : Diagram n :=
  if op false = op true then .leaf (op false)
  else if op false then negate d else d

@[simp] theorem unary_correct (op : Bool → Bool) (d : Diagram n) (v : Fin n → Bool) :
    eval (unary op d) v = op (eval d v) := by
  cases a : op false <;> cases b : op true <;> cases c : eval d v <;>
    simp [unary, a, b, c, eval]

theorem reduced_unary (op : Bool → Bool) (d : Diagram n) (h : Reduced d) : Reduced (unary op d) := by
  unfold unary
  split
  · trivial
  · split
    · exact reduced_negate d h
    · exact h

/-- Boolean apply skips a level jointly unused by both operands. -/
@[noinline] def apply (op : Bool → Bool → Bool) : (n : Nat) → Diagram n → Diagram n → Diagram n
  | 0, .leaf a, .leaf b => .leaf (op a b)
  | n + 1, p, q =>
      match p, q with
      | .leaf a, q => unary (op a) q
      | p, .leaf b => unary (fun a => op a b) p
      | p, q =>
        if low p = high p ∧ low q = high q then
          lift (apply op n (low p) (low q))
        else mk (apply op n (low p) (low q)) (apply op n (high p) (high q))

theorem apply_succ (op : Bool → Bool → Bool) (n : Nat) (p q : Diagram (n + 1)) :
    apply op (n + 1) p q = match p, q with
      | .leaf a, q => unary (op a) q
      | p, .leaf b => unary (fun a => op a b) p
      | p, q => if low p = high p ∧ low q = high q then lift (apply op n (low p) (low q))
          else mk (apply op n (low p) (low q)) (apply op n (high p) (high q)) := rfl

theorem eval_branches (d : Diagram (n + 1)) (v : Fin (n + 1) → Bool) :
    eval d v = if v 0 then eval (high d) (fun i => v i.succ)
      else eval (low d) (fun i => v i.succ) := by
  cases d <;> simp [eval, low, high]

theorem apply_correct (op : Bool → Bool → Bool) (n : Nat) (p q : Diagram n) (v : Fin n → Bool) :
    eval (apply op n p q) v = op (eval p v) (eval q v) := by
  induction n with
  | zero => cases p; cases q; rfl
  | succ n ih =>
    cases p <;> cases q <;> simp only [apply_succ]
    all_goals try (solve | simp only [unary_correct, eval])
    all_goals split
    all_goals cases value : v 0 <;> simp_all [eval_lift, eval_mk, eval, low, high]

theorem reduced_apply (op : Bool → Bool → Bool) (n : Nat) (p q : Diagram n)
    (hp : Reduced p) (hq : Reduced q) : Reduced (apply op n p q) := by
  induction n with
  | zero => cases p; cases q; trivial
  | succ n ih =>
    cases p <;> cases q <;> simp only [apply_succ]
    all_goals first | exact reduced_unary _ _ hq | exact reduced_unary _ _ hp | skip
    all_goals split
    all_goals first
      | exact reduced_lift _ (ih _ _ (reduced_low _ hp) (reduced_low _ hq))
      | exact reduced_mk _ _ (ih _ _ (reduced_low _ hp) (reduced_low _ hq))
          (ih _ _ (reduced_high _ hp) (reduced_high _ hq))

abbrev Guard (n : Nat) := { d : Diagram n // Reduced d }

def falsity : Guard n := ⟨.leaf false, trivial⟩
def truth : Guard n := ⟨.leaf true, trivial⟩
def binary (op : Bool → Bool → Bool) (p q : Guard n) : Guard n :=
  ⟨apply op n p.1 q.1, reduced_apply op n p.1 q.1 p.2 q.2⟩
def neg (p : Guard n) : Guard n := binary (fun a _ => !a) p truth
def conj (p q : Guard n) : Guard n := binary (· && ·) p q
def disj (p q : Guard n) : Guard n := binary (· || ·) p q

@[noinline] def atom : (n : Nat) → Fin n → Guard n
  | 0, i => i.elim0
  | _ + 1, ⟨0, _⟩ => ⟨mk (.leaf false) (.leaf true), reduced_mk _ _ trivial trivial⟩
  | n + 1, ⟨j + 1, h⟩ =>
      ⟨lift (atom n ⟨j, Nat.lt_of_succ_lt_succ h⟩).1,
        reduced_lift _ (atom n ⟨j, Nat.lt_of_succ_lt_succ h⟩).2⟩

theorem atom_correct (n : Nat) (i : Fin n) (v : Fin n → Bool) : eval (atom n i).1 v = v i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change eval (mk (.leaf false) (.leaf true)) v = v 0
      simp [eval_mk, eval]
    · change eval (lift (atom n j).1) v = v j.succ
      rw [eval_lift, ih]

def compile : Test (Fin n) → Guard n
  | .bot => falsity
  | .top => truth
  | .atom i => atom n i
  | .neg p => neg (compile p)
  | .conj p q => conj (compile p) (compile q)
  | .disj p q => disj (compile p) (compile q)

theorem compile_correct (p : Test (Fin n)) (v : Fin n → Bool) :
    eval (compile p).1 v = p.eval v := by
  induction p <;> simp_all [compile, falsity, truth, neg, conj, disj, binary,
    apply_correct, eval, Test.eval, atom_correct]

theorem guard_ext (p q : Guard n) : p = q ↔ ∀ v, eval p.1 v = eval q.1 v := by
  constructor
  · rintro rfl; exact fun _ => rfl
  · intro h; exact Subtype.ext (canonical p.1 q.1 p.2 q.2 h)

end KATLean.Native.Boolean

namespace KATLean.Native.Boolean

@[simp] theorem eval_conj (p q : Guard n) (v : Fin n → Bool) :
    eval (conj p q).1 v = (eval p.1 v && eval q.1 v) :=
  apply_correct _ _ _ _ _
@[simp] theorem eval_disj (p q : Guard n) (v : Fin n → Bool) :
    eval (disj p q).1 v = (eval p.1 v || eval q.1 v) :=
  apply_correct _ _ _ _ _
@[simp] theorem eval_neg (p : Guard n) (v : Fin n → Bool) :
    eval (neg p).1 v = !eval p.1 v := apply_correct _ _ _ _ _
@[simp] theorem eval_truth (v : Fin n → Bool) : eval (truth : Guard n).1 v = true := rfl
@[simp] theorem eval_falsity (v : Fin n → Bool) : eval (falsity : Guard n).1 v = false := rfl

def nodes : Diagram n → Nat
  | .leaf _ => 1
  | .skip d => 1 + nodes d
  | .node l r => 1 + nodes l + nodes r

end KATLean.Native.Boolean

namespace KATLean.Native

/-- An executable numbering, provided as data rather than chosen noncomputably.
This need not enumerate any Boolean assignments. -/
class BooleanAlphabet (T : Type) where
  width : Nat
  numbering : T ≃ Fin width

instance (n : Nat) : BooleanAlphabet (Fin n) := ⟨n, Equiv.refl _⟩

abbrev Guard (T : Type) [BooleanAlphabet T] := Boolean.Guard (BooleanAlphabet.width T)

def encodeAtom {T : Type} [BooleanAlphabet T] (v : T → Bool) :
    Fin (BooleanAlphabet.width T) → Bool := fun i => v ((BooleanAlphabet.numbering (T := T)).symm i)

def decodeAtom {T : Type} [BooleanAlphabet T] (v : Fin (BooleanAlphabet.width T) → Bool) :
    T → Bool := fun i => v (BooleanAlphabet.numbering (T := T) i)

@[simp] theorem encode_decode {T : Type} [BooleanAlphabet T]
    (v : Fin (BooleanAlphabet.width T) → Bool) : encodeAtom (decodeAtom v) = v := by
  funext i
  simp [encodeAtom, decodeAtom]

def Test.renumber {T : Type} [BooleanAlphabet T] : Test T → Test (Fin (BooleanAlphabet.width T))
  | .bot => .bot
  | .top => .top
  | .atom i => .atom (BooleanAlphabet.numbering (T := T) i)
  | .neg p => .neg p.renumber
  | .conj p q => .conj p.renumber q.renumber
  | .disj p q => .disj p.renumber q.renumber

def Test.guard {T : Type} [BooleanAlphabet T] (p : Test T) : Guard T := Boolean.compile p.renumber

theorem Test.guard_correct {T : Type} [BooleanAlphabet T] (p : Test T) (v : T → Bool) :
    Boolean.eval p.guard.1 (encodeAtom v) = p.eval v := by
  rw [Test.guard, Boolean.compile_correct]
  induction p <;> simp_all [Test.renumber, Test.eval, encodeAtom]

end KATLean.Native
