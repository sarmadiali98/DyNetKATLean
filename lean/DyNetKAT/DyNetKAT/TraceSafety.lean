import DyNetKAT.DyNetKAT.TraceEquations
import DyNetKAT.DyNetKAT.TraceEnvironment
import Mathlib.Data.Nat.Bits

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.TraceSafety

open DyNetKAT.NetKAT

/-- Definition 12. A complete packet transform or a syntactic reconfiguration label. -/
inductive Letter
  | packet (input output : CtxPkt)
  | rcfg (channel : Channel) (payload : NetKAT)
  deriving DecidableEq

def Letter.action : Letter → Action
  | .packet i o => .packet i o
  | .rcfg x p => .rcfg x p

theorem Letter.action_injective : Function.Injective Letter.action := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

def Letter.label (l : Letter) : MoveLabel := l.action.atomicLabel

def Letter.sameKind : Letter → Letter → Bool
  | .packet .., .packet .. | .rcfg .., .rcfg .. => true
  | _, _ => false

abbrev Word := List Letter
abbrev Alphabet := List Letter

inductive Regexp
  | letter (a : Letter)
  | union (p q : Regexp)
  | concat (p q : Regexp)

def Regexp.Matches : Regexp → Word → Prop
  | .letter a, w => w = [a]
  | .union p q, w => p.Matches w ∨ q.Matches w
  | .concat p q, w => ∃ u v, u ++ v = w ∧ p.Matches u ∧ q.Matches v

private def wordProduct (p q : List Word) : List Word :=
  p.flatMap fun u => q.map (u ++ ·)

private theorem mem_wordProduct {p q : List Word} {w : Word} :
    w ∈ wordProduct p q ↔ ∃ u v, u ++ v = w ∧ u ∈ p ∧ v ∈ q := by
  simp only [wordProduct, List.mem_flatMap, List.mem_map]
  aesop

/-- Definition 13, distributing concatenation over both operands of a sum. -/
def Regexp.hnf : Regexp → List Word
  | .letter a => [[a]]
  | .union p q => p.hnf ++ q.hnf
  | .concat p q => wordProduct p.hnf q.hnf

theorem Regexp.mem_hnf (r : Regexp) (w : Word) : w ∈ r.hnf ↔ r.Matches w := by
  induction r generalizing w with
  | letter => simp [Regexp.hnf, Regexp.Matches]
  | union _ _ ih₁ ih₂ => simp [Regexp.hnf, Regexp.Matches, ih₁, ih₂]
  | concat _ _ ih₁ ih₂ => simp [Regexp.hnf, Regexp.Matches, mem_wordProduct, ih₁, ih₂]

theorem Regexp.hnf_nonempty_word {r : Regexp} {w : Word} (h : w ∈ r.hnf) : w ≠ [] := by
  induction r generalizing w with
  | letter a => simp [Regexp.hnf] at h; simp [h]
  | union _ _ ih₁ ih₂ => exact (List.mem_append.mp h).elim ih₁ ih₂
  | concat _ _ ih₁ _ =>
      obtain ⟨u, v, rfl, hu, _⟩ := mem_wordProduct.mp h
      intro h
      exact ih₁ hu (List.append_eq_nil_iff.mp h).1

/-- Definition 17's stated desugaring clauses. Negation is of a literal and
ranges over its own kind. The printed desugaring gives no nested-negation rule. -/
inductive ExtendedRegexp
  | letter (a : Letter)
  | any
  | except (a : Letter)
  | union (p q : ExtendedRegexp)
  | concat (p q : ExtendedRegexp)
  | repeat (p : ExtendedRegexp) (extra : Nat)

/-- The action grammar as printed, including nested negation. -/
inductive PrintedAction
  | literal (a : Letter)
  | neg (a : PrintedAction)

def PrintedAction.elaborate : PrintedAction → Option ExtendedRegexp
  | .literal a => some (.letter a)
  | .neg (.literal a) => some (.except a)
  | .neg (.neg _) => none

/-- The surface grammar of Definition 17. A repetition count is one plus
the stored count, as in the supported extended grammar. -/
inductive PrintedRegexp
  | action (a : PrintedAction)
  | any
  | union (p q : PrintedRegexp)
  | concat (p q : PrintedRegexp)
  | repeat (p : PrintedRegexp) (extra : Nat)

/-- Elaboration is defined exactly where the paper supplies a clause for
each action. Alphabet membership is checked separately by `ExtendedRegexp.Over`. -/
def PrintedRegexp.elaborate : PrintedRegexp → Option ExtendedRegexp
  | .action a => a.elaborate
  | .any => some .any
  | .union p q => ExtendedRegexp.union <$> p.elaborate <*> q.elaborate
  | .concat p q => ExtendedRegexp.concat <$> p.elaborate <*> q.elaborate
  | .repeat p n => (·.repeat n) <$> p.elaborate

private def wordPower (p : List Word) : Nat → List Word
  | 0 => [[]]
  | n + 1 => wordProduct p (wordPower p n)

/-- A finite sum is represented by its summands, so empty sums are meaningful. -/
def ExtendedRegexp.desugar (A : Alphabet) : ExtendedRegexp → List Word
  | .letter a => [[a]]
  | .any => A.map fun a => [a]
  | .except a => (A.filter fun b => a.sameKind b && decide (b ≠ a)).map fun b => [b]
  | .union p q => p.desugar A ++ q.desugar A
  | .concat p q => wordProduct (p.desugar A) (q.desugar A)
  | .repeat p n => wordPower (p.desugar A) (n + 1)

def InAlphabet (A : Alphabet) (w : Word) : Prop := ∀ a ∈ w, a ∈ A

def Avoids (forbidden : List Word) (w : Word) : Prop :=
  ∀ bad ∈ forbidden, ¬ bad <+: w

def avoids (forbidden : List Word) (w : Word) : Bool :=
  !forbidden.any (·.isPrefixOf w)

theorem avoids_iff (forbidden : List Word) (w : Word) :
    avoids forbidden w = true ↔ Avoids forbidden w := by
  simp [avoids, Avoids, List.any_eq_true, List.isPrefixOf_iff_prefix]

theorem Avoids.prefix {forbidden : List Word} {w v : Word} (h : Avoids forbidden w)
    (pre : v <+: w) : Avoids forbidden v :=
  fun bad mem occurs => h bad mem (occurs.trans pre)

def maxLength (forbidden : List Word) : Nat :=
  forbidden.foldr (fun w n => max w.length n) 0

theorem le_maxLength {forbidden : List Word} {w : Word} (mem : w ∈ forbidden) :
    w.length ≤ maxLength forbidden := by
  induction forbidden with
  | nil => simp at mem
  | cons head tail ih =>
      simp only [maxLength, List.foldr_cons]
      rcases List.mem_cons.mp mem with rfl | mem
      · exact Nat.le_max_left ..
      · exact (ih mem).trans (Nat.le_max_right ..)

theorem Avoids.append_of_maxLength {forbidden : List Word} {u : Word}
    (h : Avoids forbidden u) (length : maxLength forbidden ≤ u.length) (v : Word) :
    Avoids forbidden (u ++ v) := by
  intro bad mem pre
  exact h bad mem (List.prefix_of_prefix_length_le pre (List.prefix_append ..)
    ((le_maxLength mem).trans length))

private theorem trace_prefix_cons {env : RecEnv} {l : Letter} {p : DyNetKAT}
    {a : Action} {word : List Action} :
    SourceTrace env (l.label.prefix p) (a :: word) ↔
      a = l.action ∧ SourceTrace env p word := by
  simp only [Letter.label, sourceTrace_atomicPrefix_iff]

private theorem trace_choiceOf_cons {env : RecEnv} {ps : List DyNetKAT} {a : Action}
    {word : List Action} :
    SourceTrace env (choiceOf ps) (a :: word) ↔ ∃ p ∈ ps, SourceTrace env p (a :: word) := by
  simp only [sourceTrace_cons_iff]
  constructor
  · rintro ⟨⟨_, pt, hl⟩, ⟨q, pt', hl'⟩, rfl, step, rest⟩
    obtain ⟨p, hp, step⟩ := (choiceOf_step_iff ..).mp step
    exact ⟨p, hp, ⟨p, pt, hl⟩, ⟨q, pt', hl'⟩, rfl, step, rest⟩
  · rintro ⟨p, hp, ⟨b, pt, hl⟩, ⟨q, pt', hl'⟩, eq, step, rest⟩
    change b = p at eq
    subst b
    exact ⟨⟨choiceOf ps, pt, hl⟩, ⟨q, pt', hl'⟩, rfl,
      (choiceOf_step_iff ..).mpr ⟨p, hp, step⟩, rest⟩

private theorem trace_var_iff {env : RecEnv} {x : Var} {body : DyNetKAT}
    (lookup : env.lookup x = some body) {word : List Action} :
    SourceTrace env (.var x) word ↔ SourceTrace env body word := by
  cases word with
  | nil => exact ⟨fun _ => sourceTrace_nil .., fun _ => sourceTrace_nil ..⟩
  | cons a w =>
      simp only [sourceTrace_cons_iff]
      constructor
      · rintro ⟨⟨_, pt, hl⟩, d, rfl, step, rest⟩
        cases step with
        | cpol_var _ _ _ _ _ _ _ _ h hs =>
            have eq := RecEnv.lookup_unique h lookup
            subst_vars
            exact ⟨⟨_, pt, hl⟩, _, rfl, hs, rest⟩
      · rintro ⟨⟨_, pt, hl⟩, ⟨q, pt', hl'⟩, rfl, step, rest⟩
        exact ⟨⟨.var x, pt, hl⟩, ⟨q, pt', hl'⟩, rfl,
          .cpol_var x _ q a pt pt' hl hl' lookup step, rest⟩


/-- Index the supplied alphabet. Word enumeration ranges only over these indices. -/
private abbrev Index (A : Alphabet) := Fin A.length
private abbrev Node (A : Alphabet) := Option (Index A × List (Index A) × Bool)

private def wordOf (A : Alphabet) (w : List (Index A)) : Word := w.map A.get

private theorem inAlphabet_wordOf (A : Alphabet) (w : List (Index A)) :
    InAlphabet A (wordOf A w) := by
  intro a mem
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
  exact List.mem_iff_get.mpr ⟨i, rfl⟩

private theorem exists_wordOf {A : Alphabet} {w : Word} (mem : InAlphabet A w) :
    ∃ is, wordOf A is = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp (mem a (by simp))
      obtain ⟨is, his⟩ := ih (fun b hb => mem b (List.mem_cons_of_mem _ hb))
      exact ⟨i :: is, congrArg₂ List.cons hi his⟩

private def wordsAt (A : Alphabet) : Nat → List (List (Index A))
  | 0 => [[]]
  | n + 1 => (List.finRange A.length).flatMap fun i => (wordsAt A n).map (i :: ·)

private theorem mem_wordsAt (A : Alphabet) (n : Nat) (w : List (Index A)) :
    w ∈ wordsAt A n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsAt]
  | succ n ih =>
      cases w <;> simp [wordsAt, ih, List.mem_finRange, List.mem_flatMap, List.mem_map]

/-- The two word sums in Definition 14. The boolean marks the summand ending
in Θ. The deadlock summand is included at every permitted depth. -/
def branches (A : Alphabet) (forbidden : List Word) : List (List (Index A) × Bool) :=
  let M := maxLength forbidden
  let words n := (wordsAt A n).filter fun w => avoids forbidden (wordOf A w)
  ((List.range (M + 1)).flatMap words).map (·, false) ++ (words M).map (·, true)

private theorem mem_branches {A : Alphabet} {forbidden : List Word}
    {w : List (Index A)} {loop : Bool} :
    (w, loop) ∈ branches A forbidden ↔
      Avoids forbidden (wordOf A w) ∧ w.length ≤ maxLength forbidden ∧
        (loop = true → w.length = maxLength forbidden) := by
  cases loop with
  | false =>
      simp [branches, List.mem_flatMap, List.mem_map, mem_wordsAt, avoids_iff,
        and_comm, Nat.lt_succ_iff]
  | true =>
      simp [branches, List.mem_flatMap, List.mem_map, mem_wordsAt, avoids_iff]
      exact ⟨fun ⟨eq, safe⟩ => ⟨safe, eq.le, eq⟩, fun ⟨safe, _, eq⟩ => ⟨eq, safe⟩⟩

private theorem fold_bits (n : Nat) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | z => simp
  | f b n valid ih =>
      rw [Nat.bits_append_bit _ _ valid, List.foldr_cons, ih]

private def nodeName {A : Alphabet} (node : Node A) : Var :=
  String.mk ((Encodable.encode node).bits.map fun b => if b then '1' else '0')

private def nameCode (name : Var) : Nat :=
  (name.data.map (· == '1')).foldr Nat.bit 0

private theorem nameCode_nodeName {A : Alphabet} (node : Node A) :
    nameCode (nodeName node) = Encodable.encode node := by
  simp only [nameCode, nodeName, List.map_map]
  rw [show ((· == '1') ∘ (fun b : Bool => if b then '1' else '0')) = id by
    funext b; cases b <;> rfl]
  rw [List.map_id, fold_bits]

private def ref {A : Alphabet} (node : Node A) : DyNetKAT := .var (nodeName node)

private def continuation (A : Alphabet) (w : List (Index A)) (loop : Bool) : DyNetKAT :=
  match w with
  | [] => if loop then ref (A := A) none else .deadlock
  | i :: rest => ref (A := A) (some (i, rest, loop))

private def branch (A : Alphabet) (w : List (Index A)) (loop : Bool) : DyNetKAT :=
  match w with
  | [] => continuation A [] loop
  | i :: rest => (A.get i).label.prefix (continuation A rest loop)

private def theta (A : Alphabet) : DyNetKAT :=
  choiceOf ((List.finRange A.length).flatMap fun i => [branch A [i] false, branch A [i] true])

private def body (A : Alphabet) : Node A → DyNetKAT
  | none => theta A
  | some (i, rest, loop) => branch A (i :: rest) loop

def translationEnv (A : Alphabet) : RecEnv := fun name =>
  (Encodable.decode (α := Node A) (nameCode name)).map (body A)

private theorem lookup_node (A : Alphabet) (node : Node A) :
    (translationEnv A).lookup (nodeName node) = some (body A node) := by
  simp [RecEnv.lookup, translationEnv, nameCode_nodeName, Encodable.encodek]

private def translatedTerm (A : Alphabet) (forbidden : List Word) : DyNetKAT :=
  choiceOf ((branches A forbidden).map fun (w, loop) => branch A w loop)

private def ReferencesDefined (A : Alphabet) (p : DyNetKAT) : Prop :=
  ∀ x ∈ recursiveVars p, ∃ node : Node A, x = nodeName node

private theorem continuation_facts (A : Alphabet) (w : List (Index A)) (loop : Bool) :
    BaseSyntax (continuation A w loop) ∧ ReferencesDefined A (continuation A w loop) := by
  cases w <;> cases loop <;>
    simp [continuation, PaperSyntax, ReferencesDefined, recursiveVars, ref]

private theorem prefix_facts (A : Alphabet) (l : Letter) (p : DyNetKAT)
    (base : BaseSyntax p) (refs : ReferencesDefined A p) :
    PaperSyntax true (l.label.prefix p) ∧ ReferencesDefined A (l.label.prefix p) ∧
      GuardedOccurrences (l.label.prefix p) := by
  cases l with
  | packet i o => exact ⟨base, refs, trivial⟩
  | rcfg x q => exact ⟨⟨rfl, base.of_base⟩, refs, trivial⟩

private theorem choiceOf_facts {A : Alphabet} {ps : List DyNetKAT}
    (h : ∀ p ∈ ps, PaperSyntax true p ∧ ReferencesDefined A p) :
    PaperSyntax true (choiceOf ps) ∧ ReferencesDefined A (choiceOf ps) := by
  induction ps with
  | nil => simp [choiceOf, PaperSyntax, ReferencesDefined, recursiveVars]
  | cons p ps ih =>
      obtain ⟨head, refs⟩ := h p (by simp)
      obtain ⟨tail, refs'⟩ := ih (fun q mem => h q (List.mem_cons_of_mem _ mem))
      exact ⟨⟨head, tail⟩, fun x mem => (Finset.mem_union.mp mem).elim (refs x) (refs' x)⟩

private theorem branch_facts (A : Alphabet) (w : List (Index A)) (loop : Bool) :
    PaperSyntax true (branch A w loop) ∧ ReferencesDefined A (branch A w loop) := by
  cases w with
  | nil =>
      obtain ⟨sort, refs⟩ := continuation_facts A [] loop
      exact ⟨sort.of_base, refs⟩
  | cons i w =>
      obtain ⟨base, refs⟩ := continuation_facts A w loop
      exact ⟨(prefix_facts A _ _ base refs).1, (prefix_facts A _ _ base refs).2.1⟩

private theorem body_facts (A : Alphabet) (node : Node A) :
    PaperSyntax true (body A node) ∧ ReferencesDefined A (body A node) ∧
      GuardedOccurrences (body A node) := by
  cases node with
  | some node =>
      obtain ⟨i, rest, loop⟩ := node
      obtain ⟨base, refs⟩ := continuation_facts A rest loop
      exact prefix_facts A _ _ base refs
  | none =>
      let ps := (List.finRange A.length).flatMap fun i => [branch A [i] false, branch A [i] true]
      change PaperSyntax true (choiceOf ps) ∧ ReferencesDefined A (choiceOf ps) ∧
        GuardedOccurrences (choiceOf ps)
      have heads (p : DyNetKAT) (mem : p ∈ ps) :
          PaperSyntax true p ∧ ReferencesDefined A p ∧ GuardedOccurrences p := by
        obtain ⟨i, _, mem⟩ := List.mem_flatMap.mp mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · exact prefix_facts A _ _ trivial (continuation_facts ..).2
        · exact prefix_facts A _ _ trivial (continuation_facts ..).2
      obtain ⟨sort, refs⟩ := choiceOf_facts (fun p mem => ⟨(heads p mem).1, (heads p mem).2.1⟩)
      refine ⟨sort, refs, ?_⟩
      have guarded (qs : List DyNetKAT) (h : ∀ q ∈ qs, GuardedOccurrences q) :
          GuardedOccurrences (choiceOf qs) := by
        induction qs with
        | nil => trivial
        | cons q qs ih =>
            exact ⟨h q (by simp), ih (fun r mem => h r (List.mem_cons_of_mem _ mem))⟩
      exact guarded ps (fun p mem => (heads p mem).2.2)

/-- Definition 14 rendered in the printed extended grammar. Named guarded
tails put a base-sorted variable immediately below a packet prefix. -/
def translate (A : Alphabet) (forbidden : List Word) : Program true (translationEnv A) := by
  have root := choiceOf_facts (ps := (branches A forbidden).map fun (w, loop) => branch A w loop)
    (fun p mem => by
      obtain ⟨⟨w, loop⟩, _, rfl⟩ := List.mem_map.mp mem
      exact branch_facts A w loop)
  refine ⟨translatedTerm A forbidden, (paperAdmissible_iff ..).mpr ⟨root.1, ?_⟩⟩
  intro x reachable
  have named : ∃ node : Node A, x = nodeName node := by
    induction reachable with
    | direct mem => exact root.2 _ mem
    | throughDefinition _ lookup mem ih =>
        obtain ⟨node, rfl⟩ := ih
        have eq := RecEnv.lookup_unique lookup (lookup_node A node)
        subst_vars
        exact (body_facts A node).2.1 _ mem
  obtain ⟨node, rfl⟩ := named
  have facts := body_facts A node
  exact ⟨body A node, ⟨lookup_node A node, facts.1,
    (typedPaperGuarded_iff_guardedOccurrences _).mpr facts.2.2⟩,
    fun q proof => RecEnv.lookup_unique proof.1 (lookup_node A node)⟩


private theorem trace_deadlock_iff {env : RecEnv} {t : List Action} :
    SourceTrace env .deadlock t ↔ t = [] := by
  cases t with
  | nil => exact ⟨fun _ => rfl, fun _ => sourceTrace_nil ..⟩
  | cons a t =>
      rw [sourceTrace_cons_iff]
      constructor
      · rintro ⟨⟨_, pt, hl⟩, d, rfl, step, _⟩
        exact (deadlock_no_step _ _ _ _ _ step).elim
      · simp

private theorem trace_theta (A : Alphabet) (t : List Action) :
    SourceTrace (translationEnv A) (ref (A := A) none) t ↔
      ∃ w, InAlphabet A w ∧ w.map Letter.action = t := by
  induction t with
  | nil => exact ⟨fun _ => ⟨[], by simp [InAlphabet], rfl⟩, fun _ => sourceTrace_nil ..⟩
  | cons a t ih =>
      rw [ref, trace_var_iff (lookup_node A none)]
      change SourceTrace (translationEnv A) (theta A) (a :: t) ↔ _
      simp only [theta, trace_choiceOf_cons, List.mem_flatMap]
      constructor
      · rintro ⟨_, ⟨i, _, mem⟩, hs⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · obtain ⟨rfl, rest⟩ := trace_prefix_cons.mp hs
          obtain rfl := trace_deadlock_iff.mp rest
          exact ⟨[A.get i], inAlphabet_wordOf A [i], rfl⟩
        · obtain ⟨rfl, rest⟩ := trace_prefix_cons.mp hs
          obtain ⟨w, inA, rfl⟩ := ih.mp rest
          exact ⟨A.get i :: w, fun b hb => (List.mem_cons.mp hb).elim
            (fun e => e ▸ List.mem_iff_get.mpr ⟨i, rfl⟩) (inA b), rfl⟩
      · rintro ⟨w, inA, eq⟩
        cases w with
        | nil => cases eq
        | cons b w =>
          simp only [List.map_cons, List.cons.injEq] at eq
          obtain ⟨rfl, rfl⟩ := eq
          obtain ⟨i, hi⟩ := List.mem_iff_get.mp (inA b (by simp))
          refine ⟨branch A [i] true, ⟨i, List.mem_finRange i, by simp⟩, ?_⟩
          exact trace_prefix_cons.mpr ⟨congrArg Letter.action hi.symm,
            ih.mpr ⟨w, fun c hc => inA c (List.mem_cons_of_mem _ hc), rfl⟩⟩

private theorem trace_branch (A : Alphabet) (w : List (Index A)) (loop : Bool)
    (t : List Action) :
    SourceTrace (translationEnv A) (branch A w loop) t ↔
      ∃ v, InAlphabet A v ∧ (loop = false → v = []) ∧
        t <+: (wordOf A w ++ v).map Letter.action := by
  induction w generalizing t with
  | nil =>
      cases loop with
      | false =>
          rw [show branch A [] false = .deadlock from rfl, trace_deadlock_iff]
          simp [wordOf, InAlphabet]
      | true =>
          rw [show branch A [] true = ref (A := A) none from rfl, trace_theta]
          simp only [Bool.true_eq_false, false_implies, true_and, wordOf, List.map_nil, List.nil_append]
          constructor
          · rintro ⟨v, hv, rfl⟩
            exact ⟨v, hv, ⟨[], by simp⟩⟩
          · rintro ⟨v, hv, pre⟩
            refine ⟨v.take t.length, fun a mem => hv a (List.mem_of_mem_take mem), ?_⟩
            rw [List.map_take, ← List.prefix_iff_eq_take.mp pre]
  | cons i w ih =>
      cases t with
      | nil =>
          exact ⟨fun _ => ⟨[], by simp [InAlphabet], fun _ => rfl, List.nil_prefix⟩,
            fun _ => sourceTrace_nil ..⟩
      | cons a t =>
          change SourceTrace _ ((A.get i).label.prefix (continuation A w loop)) _ ↔ _
          rw [trace_prefix_cons]
          have cont : SourceTrace (translationEnv A) (continuation A w loop) t ↔
              SourceTrace (translationEnv A) (branch A w loop) t := by
            cases w with
            | nil => rfl
            | cons j rest => exact trace_var_iff (lookup_node A (some (j, rest, loop)))
          rw [cont, ih]
          change (_ ∧ _) ↔ ∃ v, _ ∧ _ ∧
            a :: t <+: (A.get i).action :: (wordOf A w ++ v).map Letter.action
          simp only [List.cons_prefix_cons]
          aesop


private theorem map_prefix {α β : Type} (f : α → β) {u v : List α}
    (h : u <+: v) : u.map f <+: v.map f := by
  obtain ⟨w, rfl⟩ := h
  rw [List.map_append]
  exact List.prefix_append ..

private theorem prefix_of_map_prefix {u v : Word}
    (h : u.map Letter.action <+: v.map Letter.action) : u <+: v := by
  apply List.prefix_iff_eq_take.mpr
  apply List.map_injective_iff.mpr Letter.action_injective
  simpa only [List.map_take, List.length_map] using List.prefix_iff_eq_take.mp h

private theorem inAlphabet_append {A : Alphabet} {u v : Word}
    (hu : InAlphabet A u) (hv : InAlphabet A v) : InAlphabet A (u ++ v) :=
  fun a mem => (List.mem_append.mp mem).elim (hu a) (hv a)

private theorem inAlphabet_prefix {A : Alphabet} {u v : Word}
    (hv : InAlphabet A v) (h : u <+: v) : InAlphabet A u := by
  obtain ⟨w, rfl⟩ := h
  exact fun a mem => hv a (List.mem_append_left _ mem)

/-- The SOS traces of the Definition 14 term are exactly the alphabet words
that have no forbidden prefix. Every occurrence keeps the full SOS action. -/
theorem translate_trace_iff (A : Alphabet) (forbidden : List Word)
    (nonemptyWords : [] ∉ forbidden) (t : List Action) :
    (translate A forbidden).Trace t ↔
      ∃ w, w.map Letter.action = t ∧ InAlphabet A w ∧ Avoids forbidden w := by
  cases t with
  | nil =>
      refine ⟨fun _ => ⟨[], rfl, by simp [InAlphabet], ?_⟩, fun _ => sourceTrace_nil ..⟩
      intro bad mem pre
      have eq : bad = [] := by simpa using List.prefix_iff_eq_take.mp pre
      exact nonemptyWords (eq ▸ mem)
  | cons a t =>
      change SourceTrace (translationEnv A) (translatedTerm A forbidden) (a :: t) ↔ _
      rw [translatedTerm, trace_choiceOf_cons]
      constructor
      · rintro ⟨p, hp, run⟩
        obtain ⟨⟨w, loop⟩, hw, rfl⟩ := List.mem_map.mp hp
        obtain ⟨safe, _, atMax⟩ := mem_branches.mp hw
        obtain ⟨v, hv, suffix, pre⟩ := (trace_branch ..).mp run
        have whole : Avoids forbidden (wordOf A w ++ v) := by
          cases loop with
          | false => simpa [suffix rfl] using safe
          | true => exact safe.append_of_maxLength (by simp [wordOf, atMax rfl]) v
        let u := (wordOf A w ++ v).take (a :: t).length
        have preWord : u <+: wordOf A w ++ v :=
          ⟨(wordOf A w ++ v).drop (a :: t).length, List.take_append_drop ..⟩
        refine ⟨u, ?_, inAlphabet_prefix (inAlphabet_append (inAlphabet_wordOf A w) hv) preWord,
          whole.prefix preWord⟩
        change List.map Letter.action (List.take _ _) = _
        rw [List.map_take, ← List.prefix_iff_eq_take.mp pre]
      · rintro ⟨w, eq, inA, safe⟩
        let M := maxLength forbidden
        let u := w.take M
        let v := w.drop M
        have split : u ++ v = w := List.take_append_drop ..
        have preWord : u <+: w := ⟨v, split⟩
        obtain ⟨is, his⟩ := exists_wordOf (inAlphabet_prefix inA preWord)
        have len : is.length = min M w.length := by
          simpa [wordOf, u] using congrArg List.length his
        by_cases short : w.length ≤ M
        · have takeAll : u = w := List.take_of_length_le short
          have mem : (is, false) ∈ branches A forbidden :=
            mem_branches.mpr ⟨his ▸ safe.prefix preWord, by omega, by simp⟩
          refine ⟨branch A is false, List.mem_map.mpr ⟨(is, false), mem, rfl⟩,
            (trace_branch ..).mpr ⟨[], by simp [InAlphabet], fun _ => rfl, ?_⟩⟩
          rw [his, takeAll, List.append_nil, eq]
        · have mem : (is, true) ∈ branches A forbidden :=
            mem_branches.mpr ⟨his ▸ safe.prefix preWord, by omega, fun _ => by omega⟩
          refine ⟨branch A is true, List.mem_map.mpr ⟨(is, true), mem, rfl⟩,
            (trace_branch ..).mpr ⟨v, ?_, by simp, ?_⟩⟩
          · intro l mem
            apply inA l
            rw [← split]
            exact List.mem_append_right _ mem
          · rw [his, split, eq]


private theorem repeat_nonempty {p : List Word} (h : [] ∉ p) (n : Nat) :
    [] ∉ wordPower p (n + 1) := by
  intro mem
  obtain ⟨u, _, eq, hu, _⟩ := mem_wordProduct.mp mem
  exact h ((List.append_eq_nil_iff.mp eq).1 ▸ hu)

theorem ExtendedRegexp.desugar_nonempty_word (A : Alphabet) (r : ExtendedRegexp) :
    [] ∉ r.desugar A := by
  induction r with
  | letter => simp [ExtendedRegexp.desugar]
  | any => simp [ExtendedRegexp.desugar]
  | except => simp [ExtendedRegexp.desugar]
  | union _ _ ih₁ ih₂ => simp [ExtendedRegexp.desugar, ih₁, ih₂]
  | concat _ _ ih₁ _ =>
      intro mem
      obtain ⟨u, _, eq, hu, _⟩ := mem_wordProduct.mp mem
      exact ih₁ ((List.append_eq_nil_iff.mp eq).1 ▸ hu)
  | «repeat» _ n ih => exact repeat_nonempty ih n

/-- A formula `[r]false` forbids feasible initial occurrences of its words.
The quantification over source input lists is in `Program.Trace`. -/
def Safe {extended : Bool} {env : RecEnv} (p : Program extended env)
    (forbidden : List Word) : Prop :=
  ∀ bad ∈ forbidden, ¬ p.Trace (bad.map Letter.action)

def UsesAlphabet {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) : Prop :=
  ∀ t, p.Trace t → ∃ w, w.map Letter.action = t ∧ InAlphabet A w

/-- All-depth safety is equivalent to avoiding bad prefixes on every trace. -/
theorem safe_iff_avoids_traces {extended : Bool} {env : RecEnv} (p : Program extended env)
    (forbidden : List Word) :
    Safe p forbidden ↔ ∀ w, p.Trace (w.map Letter.action) → Avoids forbidden w := by
  constructor
  · intro safe w trace bad mem pre
    obtain ⟨_, _, _, run⟩ := trace
    obtain ⟨suffix, split⟩ := pre
    exact safe bad mem (sourceTrace_prefix_of_append run (by rw [←List.map_append, split]))
  · intro avoidsAll bad mem trace
    exact avoidsAll bad trace bad mem ⟨[], by simp⟩

/-- Semantic trace inclusion in the translated safety program. The alphabet
hypothesis is precisely what licenses comparison with all source traces. -/
theorem safe_iff_trace_inclusion {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) (forbidden : List Word) (nonemptyWords : [] ∉ forbidden)
    (alphabet : UsesAlphabet p A) :
    Safe p forbidden ↔ ∀ t, p.Trace t → (translate A forbidden).Trace t := by
  constructor
  · intro safe t run
    obtain ⟨w, rfl, inA⟩ := alphabet t run
    exact (translate_trace_iff A forbidden nonemptyWords _).mpr
      ⟨w, rfl, inA, (safe_iff_avoids_traces p forbidden).mp safe w run⟩
  · intro included
    apply (safe_iff_avoids_traces p forbidden).mpr
    intro w run
    obtain ⟨v, eq, _, allowed⟩ := (translate_trace_iff A forbidden nonemptyWords _).mp (included _ run)
    obtain rfl := List.map_injective_iff.mpr Letter.action_injective eq
    exact allowed

/-- The semantic absorption equation underlying Eq. (27). The two programs
may have separate defining equations. The union is over trace languages. -/
theorem safe_iff_trace_absorption {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) (forbidden : List Word) (nonemptyWords : [] ∉ forbidden)
    (alphabet : UsesAlphabet p A) :
    Safe p forbidden ↔ ∀ t,
      ((translate A forbidden).Trace t ∨ p.Trace t) ↔ (translate A forbidden).Trace t := by
  rw [safe_iff_trace_inclusion p A forbidden nonemptyWords alphabet]
  constructor
  · intro included t
    exact ⟨fun h => h.elim id (included t), Or.inl⟩
  · intro absorbs t h
    exact (absorbs t).mp (.inr h)

/-- A single formula has a completeness bound fixed by its longest bad word.
This compares a property-specific projection with the unprojected source. -/
theorem safe_iff_project_maxLength {extended : Bool} {env : RecEnv} (p : Program extended env)
    (forbidden : List Word) :
    Safe p forbidden ↔
      ∀ bad ∈ forbidden, ¬ SourceTrace env (.project (maxLength forbidden) p.term)
        (bad.map Letter.action) := by
  unfold Safe
  simp only [sourceTrace_project_iff, List.length_map]
  constructor
  · intro safe bad mem run
    exact safe bad mem run.1
  · intro safe bad mem run
    exact safe bad mem ⟨run, le_maxLength mem⟩

theorem safe_iff_all_projections {extended : Bool} {env : RecEnv} (p : Program extended env)
    (forbidden : List Word) :
    Safe p forbidden ↔
      ∀ n bad, bad ∈ forbidden → ¬ SourceTrace env (.project n p.term) (bad.map Letter.action) := by
  constructor
  · intro safe n bad mem trace
    exact safe bad mem (sourceTrace_project_iff.mp trace).1
  · intro all
    exact (safe_iff_project_maxLength p forbidden).mpr (all _)

/-- Exact conditional transfer to a compiled graph. A graph is needed only
for this representation theorem. -/
theorem safe_iff_compiled {extended : Bool} {env : RecEnv} (p : Program extended env)
    (compiled : p.Compiled) (forbidden : List Word) :
    Safe p forbidden ↔ ∀ bad ∈ forbidden, ¬ ∃ pt hl d,
      GSteps compiled.graph ⟨compiled.graph.root, pt, hl⟩ (bad.map Letter.action) d := by
  unfold Safe
  simp only [Program.Compiled.trace_iff p compiled]


/-- Definition 16, Eq. (27), in one declaration system. The translated
specification and the network have disjoint recursive names in that system. -/
def EquationalSafety {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) (forbidden : List Word) : Prop :=
  let specification := (translate A forbidden).inLeft env
  let network := p.inRight (translationEnv A)
  TraceDerives ((translationEnv A).disjoint env) (specification.choice network).term specification.term

theorem equationalSafety_iff_safe {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) (forbidden : List Word) (nonemptyWords : [] ∉ forbidden)
    (alphabet : UsesAlphabet p A) :
    EquationalSafety p A forbidden ↔ Safe p forbidden := by
  unfold EquationalSafety
  dsimp only
  rw [TraceDerives.iff_traces (Program.admissible _).1 (Program.admissible _).1]
  change (∀ t, ((translate A forbidden).inLeft env |>.choice (p.inRight (translationEnv A))).Trace t
    ↔ ((translate A forbidden).inLeft env).Trace t) ↔ Safe p forbidden
  simp only [Program.choice_trace, Program.inLeft_trace, Program.inRight_trace]
  exact (safe_iff_trace_absorption p A forbidden nonemptyWords alphabet).symm

/-- Admissible expressions in the alphabet of Definition 12. -/
def Regexp.Over (A : Alphabet) : Regexp → Prop
  | .letter a => a ∈ A
  | .union p q | .concat p q => p.Over A ∧ q.Over A

abbrev Formula (A : Alphabet) := {r : Regexp // r.Over A}

theorem Regexp.hnf_inAlphabet {A : Alphabet} {r : Regexp} (valid : r.Over A)
    {w : Word} (mem : w ∈ r.hnf) : InAlphabet A w := by
  induction r generalizing w with
  | letter a =>
      simp [Regexp.hnf] at mem
      subst w
      simpa [InAlphabet] using valid
  | union p q ih₁ ih₂ =>
      exact (List.mem_append.mp mem).elim (fun h => ih₁ valid.1 h) (fun h => ih₂ valid.2 h)
  | concat p q ih₁ ih₂ =>
      obtain ⟨u, v, rfl, first, second⟩ := mem_wordProduct.mp mem
      exact inAlphabet_append (ih₁ valid.1 first) (ih₂ valid.2 second)

theorem ExtendedRegexp.mem_desugar_except {A : Alphabet} {a : Letter} {w : Word} :
    w ∈ (ExtendedRegexp.except a).desugar A ↔
      ∃ b ∈ A, a.sameKind b = true ∧ b ≠ a ∧ w = [b] := by
  simp only [ExtendedRegexp.desugar, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]
  aesop

private theorem mem_wordPower {p : List Word} {n : Nat} {w : Word} :
    w ∈ wordPower p n ↔
      ∃ ws : List Word, ws.length = n ∧ (∀ u ∈ ws, u ∈ p) ∧ ws.flatten = w := by
  induction n generalizing w with
  | zero =>
      constructor
      · intro mem
        have eq : w = [] := by simpa [wordPower] using mem
        exact ⟨[], rfl, by simp, eq.symm⟩
      · rintro ⟨ws, len, _, rfl⟩
        simp only [List.length_eq_zero_iff] at len
        simp [len, wordPower]
  | succ n ih =>
      simp only [wordPower, mem_wordProduct, ih]
      constructor
      · rintro ⟨u, _, rfl, hu, ws, len, mem, rfl⟩
        exact ⟨u :: ws, by simp [len], fun v hv => (List.mem_cons.mp hv).elim
          (fun h => h ▸ hu) (mem v), rfl⟩
      · rintro ⟨ws, len, mem, rfl⟩
        cases ws with
        | nil => simp at len
        | cons u ws =>
            exact ⟨u, ws.flatten, rfl, mem u (by simp), ws, by simpa using len,
              fun v hv => mem v (List.mem_cons_of_mem u hv), rfl⟩

theorem ExtendedRegexp.mem_desugar_repeat {A : Alphabet} {r : ExtendedRegexp}
    {n : Nat} {w : Word} :
    w ∈ (r.repeat n).desugar A ↔
      ∃ ws : List Word, ws.length = n + 1 ∧ (∀ u ∈ ws, u ∈ r.desugar A) ∧ ws.flatten = w :=
  mem_wordPower

/-- Paper-facing Eq. (27) for a core formula `[r]false`. -/
theorem Formula.equational_iff {extended : Bool} {env : RecEnv} {A : Alphabet}
    (r : Formula A) (p : Program extended env) (alphabet : UsesAlphabet p A) :
    EquationalSafety p A r.val.hnf ↔
      ∀ w, r.val.Matches w → ¬ p.Trace (w.map Letter.action) := by
  rw [equationalSafety_iff_safe p A _ (fun h => Regexp.hnf_nonempty_word h rfl) alphabet]
  simp only [Safe, Regexp.mem_hnf]

theorem ExtendedRegexp.equational_iff {extended : Bool} {env : RecEnv}
    (r : ExtendedRegexp) (p : Program extended env) (A : Alphabet) (alphabet : UsesAlphabet p A) :
    EquationalSafety p A (r.desugar A) ↔ Safe p (r.desugar A) :=
  equationalSafety_iff_safe p A _ (r.desugar_nonempty_word A) alphabet


def ExtendedRegexp.Over (A : Alphabet) : ExtendedRegexp → Prop
  | .letter a | .except a => a ∈ A
  | .any => True
  | .union p q | .concat p q => p.Over A ∧ q.Over A
  | .repeat p _ => p.Over A

/-- Word semantics of the supported Definition 17 fragment. A repetition
matches a concatenation of exactly the indicated number of matching words. -/
def ExtendedRegexp.Matches (A : Alphabet) : ExtendedRegexp → Word → Prop
  | .letter a, w => w = [a]
  | .any, w => ∃ a ∈ A, w = [a]
  | .except a, w => ∃ b ∈ A, a.sameKind b = true ∧ b ≠ a ∧ w = [b]
  | .union p q, w => p.Matches A w ∨ q.Matches A w
  | .concat p q, w => ∃ u v, u ++ v = w ∧ p.Matches A u ∧ q.Matches A v
  | .repeat p n, w =>
      ∃ ws : List Word, ws.length = n + 1 ∧ (∀ u ∈ ws, p.Matches A u) ∧ ws.flatten = w

theorem ExtendedRegexp.desugar_correct (A : Alphabet) (r : ExtendedRegexp) (w : Word) :
    w ∈ r.desugar A ↔ r.Matches A w := by
  induction r generalizing w with
  | letter => simp [desugar, Matches]
  | any => simp [desugar, Matches, eq_comm]
  | except => exact mem_desugar_except
  | union _ _ ih₁ ih₂ => simp [desugar, Matches, ih₁, ih₂]
  | concat _ _ ih₁ ih₂ => simp [desugar, Matches, mem_wordProduct, ih₁, ih₂]
  | «repeat» _ _ ih => simp [Matches, mem_desugar_repeat, ih]

/-- Concatenation of a core expression with itself a positive number of times.
The argument is the number of copies after the first. -/
def Regexp.repeatPositive (r : Regexp) : Nat → Regexp
  | 0 => r
  | n + 1 => .concat r (r.repeatPositive n)

private theorem Regexp.hnf_repeatPositive (r : Regexp) (n : Nat) :
    (r.repeatPositive n).hnf = wordPower r.hnf (n + 1) := by
  induction n with
  | zero => simp [repeatPositive, wordPower, wordProduct]
  | succ n ih => simp only [repeatPositive, hnf, wordPower, ih]

theorem Regexp.matches_repeatPositive (r : Regexp) (n : Nat) (w : Word) :
    (r.repeatPositive n).Matches w ↔
      ∃ ws : List Word, ws.length = n + 1 ∧ (∀ u ∈ ws, r.Matches u) ∧ ws.flatten = w := by
  simp only [← Regexp.mem_hnf, hnf_repeatPositive, mem_wordPower]

theorem ExtendedRegexp.equational_iff_matches {extended : Bool} {env : RecEnv}
    (r : ExtendedRegexp) (p : Program extended env) (A : Alphabet) (alphabet : UsesAlphabet p A) :
    EquationalSafety p A (r.desugar A) ↔ ∀ w, r.Matches A w → ¬ p.Trace (w.map Letter.action) := by
  rw [r.equational_iff p A alphabet]
  simp only [Safe, desugar_correct]

/-- The Eq. (28) expression. At zero the empty prefix contributes no action,
so the formula is the ordinary forbidden literal. -/
def padded (a : Letter) : Nat → ExtendedRegexp
  | 0 => .letter a
  | n + 1 => .concat (.repeat .any n) (.letter a)

theorem padded_over {A : Alphabet} {a : Letter} (ha : a ∈ A) (n : Nat) :
    (padded a n).Over A := by
  cases n
  · exact ha
  · exact ⟨trivial, ha⟩

private theorem wordPower_any {A : Alphabet} {n : Nat} {u : Word} :
    u ∈ wordPower (A.map fun a => [a]) n ↔ u.length = n ∧ InAlphabet A u := by
  induction n generalizing u with
  | zero =>
      cases u <;> simp [wordPower, InAlphabet]
  | succ n ih =>
      simp only [wordPower, mem_wordProduct, List.mem_map, ih]
      constructor
      · rintro ⟨_, v, rfl, ⟨a, ha, rfl⟩, hv, letters⟩
        exact ⟨by simp [hv], fun b hb => (List.mem_cons.mp hb).elim (fun eq => eq ▸ ha) (letters b)⟩
      · rintro ⟨len, letters⟩
        cases u with
        | nil => simp at len
        | cons a v =>
            exact ⟨[a], v, rfl, ⟨a, letters a (by simp), rfl⟩, by simpa using len,
              fun b hb => letters b (List.mem_cons_of_mem _ hb)⟩

theorem mem_padded {A : Alphabet} {a : Letter} {n : Nat} {w : Word} :
    w ∈ (padded a n).desugar A ↔
      ∃ u, u.length = n ∧ InAlphabet A u ∧ w = u ++ [a] := by
  cases n with
  | zero => simp [padded, ExtendedRegexp.desugar, InAlphabet]
  | succ n =>
      simp only [padded, ExtendedRegexp.desugar, mem_wordProduct, wordPower_any,
        List.mem_singleton]
      constructor
      · rintro ⟨u, _, rfl, ⟨len, letters⟩, rfl⟩
        exact ⟨u, len, letters, rfl⟩
      · rintro ⟨u, len, letters, rfl⟩
        exact ⟨u, [a], rfl, ⟨len, letters⟩, rfl⟩

theorem padded_matches {A : Alphabet} {a : Letter} {n : Nat} {w : Word} :
    (padded a n).Matches A w ↔ ∃ u, u.length = n ∧ InAlphabet A u ∧ w = u ++ [a] :=
  (ExtendedRegexp.desugar_correct ..).symm.trans mem_padded

@[simp] theorem padded_zero (A : Alphabet) (a : Letter) :
    (padded a 0).desugar A = [[a]] := rfl

theorem safe_padded_iff {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) (a : Letter) (n : Nat) :
    Safe p ((padded a n).desugar A) ↔
      ∀ u, u.length = n → InAlphabet A u → ¬ p.Trace ((u ++ [a]).map Letter.action) := by
  constructor
  · intro safe u len letters
    exact safe _ (mem_padded.mpr ⟨u, len, letters, rfl⟩)
  · intro rejects w mem
    obtain ⟨u, len, letters, rfl⟩ := mem_padded.mp mem
    exact rejects u len letters

/-- For one member of Eq. (28), depth `n + 1` completely decides trace
feasibility for that member's words. -/
theorem safe_padded_iff_project {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) (a : Letter) (n : Nat) :
    Safe p ((padded a n).desugar A) ↔
      ∀ w ∈ (padded a n).desugar A, ¬ SourceTrace env (.project (n + 1) p.term)
        (w.map Letter.action) := by
  constructor
  · intro safe w mem run
    exact safe w mem (sourceTrace_project_iff.mp run).1
  · intro projected w mem run
    have len : w.length = n + 1 := by
      obtain ⟨u, len, _, rfl⟩ := mem_padded.mp mem
      simp [len]
    exact projected w mem (sourceTrace_project_iff.mpr ⟨run, by simp [len]⟩)

theorem padded_equational_iff {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) (alphabet : UsesAlphabet p A) (a : Letter) (n : Nat) :
    EquationalSafety p A ((padded a n).desugar A) ↔
      ∀ u, u.length = n → InAlphabet A u → ¬ p.Trace ((u ++ [a]).map Letter.action) :=
  ((padded a n).equational_iff p A alphabet).trans (safe_padded_iff p A a n)

/-- Eq. (28) over all prefix lengths. The alphabet covers the complete
traces of the network, including the prefix before a candidate violation. -/
theorem eq28_iff_no_occurrence {extended : Bool} {env : RecEnv} (p : Program extended env)
    (A : Alphabet) (alphabet : UsesAlphabet p A) (a : Letter) :
    (∀ n, EquationalSafety p A ((padded a n).desugar A)) ↔
      ∀ t, p.Trace t → a.action ∉ t := by
  constructor
  · intro all t trace occurrence
    obtain ⟨w, rfl, letters⟩ := alphabet t trace
    obtain ⟨b, mem, eq⟩ := List.mem_map.mp occurrence
    obtain rfl := Letter.action_injective eq
    obtain ⟨u, v, rfl⟩ := List.append_of_mem mem
    have prefixLetters : InAlphabet A u :=
      fun k hk => letters k (List.mem_append_left _ hk)
    have observed : p.Trace ((u ++ [b]).map Letter.action) := by
      obtain ⟨_, _, _, run⟩ := trace
      apply sourceTrace_prefix_of_append run (v := v.map Letter.action)
      simp [List.map_append, List.append_assoc]
    exact (padded_equational_iff p A alphabet b u.length).mp (all _) _ rfl prefixLetters observed
  · intro never n
    apply (padded_equational_iff p A alphabet a n).mpr
    intro u _ _ run
    exact never _ run (by simp)


theorem ExtendedRegexp.desugar_inAlphabet {A : Alphabet} {r : ExtendedRegexp}
    (valid : r.Over A) {w : Word} (mem : w ∈ r.desugar A) : InAlphabet A w := by
  replace mem := (r.desugar_correct A w).mp mem
  induction r generalizing w with
  | letter a =>
      change w = [a] at mem
      subst w
      simpa [InAlphabet] using valid
  | any =>
      obtain ⟨a, ha, rfl⟩ := mem
      simpa [InAlphabet] using ha
  | except a =>
      obtain ⟨b, hb, _, _, rfl⟩ := mem
      simpa [InAlphabet] using hb
  | union _ _ ih₁ ih₂ =>
      exact mem.elim (ih₁ valid.1) (ih₂ valid.2)
  | concat _ _ ih₁ ih₂ =>
      obtain ⟨u, v, rfl, left, right⟩ := mem
      exact inAlphabet_append (ih₁ valid.1 left) (ih₂ valid.2 right)
  | «repeat» _ _ ih =>
      obtain ⟨ws, _, wordMatches, rfl⟩ := mem
      intro a occurs
      obtain ⟨u, hu, letter⟩ := List.mem_flatten.mp occurs
      exact ih valid (wordMatches u hu) a letter

private theorem formula_of_word {A : Alphabet} {a : Letter} {w : Word}
    (letters : InAlphabet A (a :: w)) :
    ∃ f : Formula A, ∀ u, f.val.Matches u ↔ u = a :: w := by
  induction w generalizing a with
  | nil => exact ⟨⟨.letter a, letters a (by simp)⟩, fun _ => Iff.rfl⟩
  | cons b rest ih =>
      obtain ⟨f, wordMatches⟩ := ih (fun c hc => letters c (List.mem_cons_of_mem _ hc))
      refine ⟨⟨.concat (.letter a) f.val, letters a (by simp), f.property⟩, ?_⟩
      intro u
      simp [Regexp.Matches, wordMatches, eq_comm]

private theorem formula_of_words {A : Alphabet} {words : List Word}
    (hasWord : words ≠ []) (noEmpty : [] ∉ words)
    (letters : ∀ w ∈ words, InAlphabet A w) :
    ∃ f : Formula A, ∀ w, f.val.Matches w ↔ w ∈ words := by
  induction words with
  | nil => exact (hasWord rfl).elim
  | cons w ws ih =>
      cases w with
      | nil => exact (noEmpty (by simp)).elim
      | cons a w =>
          obtain ⟨head, matchesHead⟩ := formula_of_word (a := a) (w := w) (letters _ (by simp))
          by_cases empty : ws = []
          · exact ⟨head, fun w => by simp [empty, matchesHead]⟩
          · obtain ⟨tail, matchesTail⟩ := ih empty
              (fun mem => noEmpty (List.mem_cons_of_mem _ mem))
              (fun w mem => letters w (List.mem_cons_of_mem _ mem))
            exact ⟨⟨.union head.val tail.val, head.property, tail.property⟩,
              fun w => by simp [Regexp.Matches, matchesHead, matchesTail]⟩

/-- A nonempty desugared sum is represented by an ordinary formula. An
empty sum has no representation in the literal/union/concatenation grammar
and is already handled by the word-sum form of Eq. (27). -/
theorem ExtendedRegexp.exists_coreFormula {A : Alphabet} {r : ExtendedRegexp}
    (valid : r.Over A) (hasWord : r.desugar A ≠ []) :
    ∃ f : Formula A, ∀ w, f.val.Matches w ↔ r.Matches A w := by
  obtain ⟨f, exactWords⟩ := formula_of_words hasWord (r.desugar_nonempty_word A)
    (fun _ mem => desugar_inAlphabet valid mem)
  exact ⟨f, fun w => (exactWords w).trans (r.desugar_correct A w)⟩

theorem ExtendedRegexp.equational_iff_core {extended : Bool} {env : RecEnv}
    (r : ExtendedRegexp) (p : Program extended env) (A : Alphabet) (alphabet : UsesAlphabet p A)
    (valid : r.Over A) (hasWord : r.desugar A ≠ []) :
    ∃ f : Formula A, (∀ w, f.val.Matches w ↔ r.Matches A w) ∧
      (EquationalSafety p A (r.desugar A) ↔ EquationalSafety p A f.val.hnf) := by
  obtain ⟨f, wordMatches⟩ := exists_coreFormula valid hasWord
  refine ⟨f, wordMatches, ?_⟩
  rw [r.equational_iff_matches p A alphabet, f.equational_iff p alphabet]
  simp only [wordMatches]

/-- Every member of the paper's padding family has a core formula when
the forbidden action belongs to the alphabet. -/
theorem padded_exists_coreFormula {A : Alphabet} {a : Letter} (ha : a ∈ A) (n : Nat) :
    ∃ f : Formula A, ∀ w, f.val.Matches w ↔
      ∃ u, u.length = n ∧ InAlphabet A u ∧ w = u ++ [a] := by
  have mem : List.replicate n a ++ [a] ∈ (padded a n).desugar A :=
    mem_padded.mpr ⟨List.replicate n a, by simp, fun b hb => by
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hb
      exact ha, rfl⟩
  have hasWord : (padded a n).desugar A ≠ [] := by
    intro empty
    simp [empty] at mem
  obtain ⟨f, wordMatches⟩ := ExtendedRegexp.exists_coreFormula (padded_over ha n) hasWord
  exact ⟨f, fun w => (wordMatches w).trans padded_matches⟩

end DyNetKAT.DyNetKAT.TraceSafety
