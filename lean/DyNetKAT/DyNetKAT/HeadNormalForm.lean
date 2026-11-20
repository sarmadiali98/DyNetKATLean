import DyNetKAT.DyNetKAT.Equations
import DyNetKAT.DyNetKAT.Ground
import DyNetKAT.NetKAT.Normalization

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT
open Equations

variable [DiagramLayout schema]

theorem choiceOf_append (env : RecEnv schema) (xs ys : List (DyNetKAT schema)) :
    DerivesNoAIP env (.choice (choiceOf xs) (choiceOf ys)) (choiceOf (xs ++ ys)) := by
  induction xs with
  | nil => exact .trans (.a2 _ _) (.a5 _)
  | cons b xs ih =>
    exact .trans (.a3 _ _ _) (.choiceCongr (.refl _) ih)

/-- The rendered choice depends equationally only on summand membership. -/
theorem choiceOf_derives_of_mem_iff (env : RecEnv schema) {xs ys : List (DyNetKAT schema)}
    (h : ∀ b, b ∈ xs ↔ b ∈ ys) : DerivesNoAIP env (choiceOf xs) (choiceOf ys) := by
  have absorb (b : DyNetKAT schema) (zs : List (DyNetKAT schema)) (hb : b ∈ zs) :
      DerivesNoAIP env (.choice b (choiceOf zs)) (choiceOf zs) := by
    induction zs with
    | nil => simp at hb
    | cons c zs ih =>
      rcases List.mem_cons.mp hb with rfl | ht
      · exact .trans (.symm (.a3 _ _ _)) (.choiceCongr (.a4 _) (.refl _))
      · exact .trans (.symm (.a3 _ _ _)) (.trans (.choiceCongr (.a2 _ _) (.refl _))
          (.trans (.a3 _ _ _) (.choiceCongr (.refl _) (ih ht))))
  have absorbList (us vs : List (DyNetKAT schema)) (sub : ∀ b ∈ us, b ∈ vs) :
      DerivesNoAIP env (.choice (choiceOf us) (choiceOf vs)) (choiceOf vs) := by
    induction us with
    | nil => exact .trans (.a2 _ _) (.a5 _)
    | cons b us ih =>
      exact .trans (.a3 _ _ _) (.trans
        (.choiceCongr (.refl _) (ih (fun c hc => sub c (List.mem_cons_of_mem _ hc))))
        (absorb b vs (sub b List.mem_cons_self)))
  exact .trans (.symm (absorbList ys xs (fun b => (h b).mpr)))
    (.trans (.a2 _ _) (absorbList xs ys (fun b => (h b).mp)))

/-- Definition 6's head sort, with an unrestricted process continuation. -/
structure HeadSummand (schema : PacketSchema := ctxSchema) [DiagramLayout schema] where
  label : MoveLabel schema
  atomic : AtomicPrefix label
  continuation : DyNetKAT schema

namespace HeadSummand

def render (b : HeadSummand schema) : DyNetKAT schema := b.label.prefix b.continuation

def withContinuation (b : HeadSummand schema) (p : DyNetKAT schema) : HeadSummand schema :=
  { b with continuation := p }

def packet (α π : schema.Packet) (p : DyNetKAT schema) :
    (HeadSummand schema) :=
  ⟨.visible (.packet (packetSummand (α, π))), .packet α π, p⟩

def recv (x : Channel) (z : NetKAT schema) (p : DyNetKAT schema) : HeadSummand schema :=
  ⟨.recv x z, .recv x z, p⟩

def send (x : Channel) (z : NetKAT schema) (p : DyNetKAT schema) : HeadSummand schema :=
  ⟨.send x z, .send x z, p⟩

def rcfg (x : Channel) (z : NetKAT schema) (p : DyNetKAT schema) : HeadSummand schema :=
  ⟨.visible (.rcfg x z), .rcfg x z, p⟩

end HeadSummand

/-- A finite choice of heads, with deadlock as the empty choice and trailing unit. -/
abbrev HeadNormalForm (schema : PacketSchema := ctxSchema) [DiagramLayout schema] := List (HeadSummand schema)

namespace HeadNormalForm

def render (xs : HeadNormalForm schema) : DyNetKAT schema :=
  choiceOf (xs.map HeadSummand.render)

@[simp] theorem render_nil : render (schema := schema) [] = .deadlock := rfl

@[simp] theorem render_cons (b : HeadSummand schema) (xs : HeadNormalForm schema) :
    render (b :: xs) = .choice b.render (render xs) := rfl

/-- Invert a rendered step to a head and its exact continuation. -/
theorem step_iff (env : RecEnv schema) (xs : HeadNormalForm schema) (pt hl : List schema.Packet)
    (a : Action schema) (q : DyNetKAT schema) (pt' hl' : List schema.Packet) :
    Step env ⟨render xs, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
      ∃ b ∈ xs, q = b.continuation ∧ b.label.Realizes pt hl a pt' hl' := by
  simp only [render, choiceOf_step_iff, List.mem_map]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, hs⟩
    exact ⟨b, hb, (b.label.prefix_step_iff env ..).mp hs⟩
  · rintro ⟨b, hb, hs⟩
    exact ⟨b.render, ⟨b, hb, rfl⟩, (b.label.prefix_step_iff env ..).mpr hs⟩

theorem render_singleton (env : RecEnv schema) (b : HeadSummand schema) :
    DerivesNoAIP env (render [b]) b.render := .a5 _

theorem render_append (env : RecEnv schema) (xs ys : HeadNormalForm schema) :
    DerivesNoAIP env (.choice (render xs) (render ys)) (render (xs ++ ys)) := by
  simpa only [render, List.map_append] using choiceOf_append env
    (xs.map HeadSummand.render) (ys.map HeadSummand.render)

theorem render_derives_of_mem_iff (env : RecEnv schema) {xs ys : HeadNormalForm schema}
    (h : ∀ b, b ∈ xs ↔ b ∈ ys) : DerivesNoAIP env (render xs) (render ys) := by
  apply choiceOf_derives_of_mem_iff
  intro q
  simp only [List.mem_map, h]

private theorem distribute (env : RecEnv schema) (f : DyNetKAT schema → DyNetKAT schema)
    (branches : HeadSummand schema → HeadNormalForm schema)
    (empty : DerivesNoAIP env (f .deadlock) .deadlock)
    (choice : ∀ p q, DerivesNoAIP env (f (.choice p q)) (.choice (f p) (f q)))
    (head : ∀ b, DerivesNoAIP env (f b.render) (render (branches b)))
    (xs : HeadNormalForm schema) :
    DerivesNoAIP env (f (render xs)) (render (xs.flatMap branches)) := by
  induction xs with
  | nil => exact empty
  | cons b xs ih =>
    exact .trans (choice _ _) (.trans (.choiceCongr (head b) ih) (render_append ..))

def packetHeads (z : NetKAT schema) (p : DyNetKAT schema) : HeadNormalForm schema :=
  (symbolicPairsFor z).map fun (α, π) => .packet α π p

private theorem pairSum_prefix (env : RecEnv schema) (p : DyNetKAT schema)
    (xs : List (schema.Packet × schema.Packet)) :
    DerivesNoAIP env (.nSeq (pairSum xs) p) (render (xs.map fun (α, π) => .packet α π p)) := by
  induction xs with
  | nil => exact .a0 _
  | cons b xs ih => exact .trans (.a1 _ _ _) (.choiceCongr (.refl _) ih)

theorem packetHeads_correct (env : RecEnv schema) (z : NetKAT schema) (p : DyNetKAT schema) :
    DerivesNoAIP env (.nSeq z p) (render (packetHeads z p)) :=
  .trans (.netkat p (NetKAT.normalize_derives z)) (pairSum_prefix ..)

def leftMerge (xs : HeadNormalForm schema) (q : DyNetKAT schema) : HeadNormalForm schema :=
  xs.flatMap fun b => [b.withContinuation (.parallel b.continuation q)]

theorem leftMerge_correct (env : RecEnv schema) (xs : HeadNormalForm schema) (q : DyNetKAT schema) :
    DerivesNoAIP env (.leftMerge (render xs) q) (render (leftMerge xs q)) :=
  distribute env (fun p => .leftMerge p q) _ (.a9 _) (fun _ _ => .a11 _ _ _)
    (fun b => .trans (.a10 b.label _ _) (.symm (.a5 _))) xs

def synchronize (a b : HeadSummand schema) : HeadNormalForm schema :=
  match a.label, b.label with
  | .recv x z, .send y w | .send x z, .recv y w =>
    if x = y ∧ z = w then [.rcfg x z (.parallel a.continuation b.continuation)] else []
  | _, _ => []

theorem synchronize_correct (env : RecEnv schema) (a b : HeadSummand schema) :
    DerivesNoAIP env (.commMerge a.render b.render) (render (synchronize a b)) := by
  rcases a with ⟨_, ha, p⟩
  rcases b with ⟨_, hb, q⟩
  cases ha <;> cases hb <;>
    first
    | exact .a15 .packet
    | exact .a15 .rcfg
    | exact .a15 .recvRecv
    | exact .a15 .sendSend
    | exact .trans (.a14 _ _) (.a15 .packet)
    | exact .trans (.a14 _ _) (.a15 .rcfg)
    | skip
  · rename_i x z y w
    by_cases h : x = y ∧ z = w
    · obtain ⟨rfl, rfl⟩ := h
      simp only [synchronize, if_pos (And.intro rfl rfl)]
      exact .trans (.a12 _ _ _ _) (.symm (.a5 _))
    · simp only [synchronize, if_neg h]
      exact .a15 (.recvSend (not_and_or.mp h))
  · rename_i x z y w
    by_cases h : x = y ∧ z = w
    · obtain ⟨rfl, rfl⟩ := h
      simp only [synchronize, if_pos (And.intro rfl rfl)]
      exact .trans (DerivesNoAIP.a12_reverse env _ _ _ _) (.symm (.a5 _))
    · simp only [synchronize, if_neg h]
      have hm : y ≠ x ∨ w ≠ z := (not_and_or.mp h).imp Ne.symm Ne.symm
      exact .trans (.a14 _ _) (.a15 (.recvSend hm))

def commMerge (xs ys : HeadNormalForm schema) : HeadNormalForm schema :=
  xs.flatMap fun a => ys.flatMap (synchronize a)

theorem commMerge_correct (env : RecEnv schema) (xs ys : HeadNormalForm schema) :
    DerivesNoAIP env (.commMerge (render xs) (render ys)) (render (commMerge xs ys)) := by
  apply distribute env (fun p => .commMerge p (render ys)) _
    (.a15 .deadlock) (fun _ _ => .a13 _ _ _) _ xs
  intro a
  apply distribute env (fun q => .commMerge a.render q) _
    (.trans (.a14 _ _) (.a15 .deadlock)) _ (synchronize_correct env a) ys
  intro p q
  exact .trans (.a14 _ _) (.trans (.a13 _ _ _) (.choiceCongr (.a14 _ _) (.a14 _ _)))

/-- Keep the original operands in interleaving continuations. -/
def parallel (p q : DyNetKAT schema) (xs ys : HeadNormalForm schema) : HeadNormalForm schema :=
  (leftMerge xs q ++ leftMerge ys p) ++ commMerge xs ys

theorem parallel_correct (env : RecEnv schema) {p q : DyNetKAT schema} {xs ys : HeadNormalForm schema}
    (hp : DerivesNoAIP env p (render xs)) (hq : DerivesNoAIP env q (render ys)) :
    DerivesNoAIP env (.parallel p q) (render (parallel p q xs ys)) := by
  have left := DerivesNoAIP.trans (.leftMergeCongr hp (.refl q)) (leftMerge_correct env xs q)
  have right := DerivesNoAIP.trans (.leftMergeCongr hq (.refl p)) (leftMerge_correct env ys p)
  have joint := DerivesNoAIP.trans (.commMergeCongr hp hq) (commMerge_correct env xs ys)
  exact .trans (.a8 _ _) (.trans
    (.choiceCongr (.trans (.choiceCongr left right) (render_append ..)) joint)
    (render_append ..))

open Classical in
noncomputable def restrict (L : Set (CommunicationAction schema)) (xs : HeadNormalForm schema) : HeadNormalForm schema :=
  xs.flatMap fun b =>
    if PrefixBlocked L b.label then [] else [b.withContinuation (.restrict L b.continuation)]

theorem restrict_correct (env : RecEnv schema) (L : Set (CommunicationAction schema)) (xs : HeadNormalForm schema) :
    DerivesNoAIP env (.restrict L (render xs)) (render (restrict L xs)) := by
  classical
  apply distribute env (DyNetKAT.restrict L) _ (.restrictDeadlock _)
    (fun _ _ => .restrictChoice _ _ _) _ xs
  intro b
  by_cases h : PrefixBlocked L b.label
  · simpa only [if_pos h] using
      (DerivesNoAIP.restrictBlocked L b.label b.continuation b.atomic h : DerivesNoAIP env _ _)
  · simp only [if_neg h]
    exact .trans (.restrictAllowed L b.label b.continuation b.atomic h) (.symm (.a5 _))

def project (n : Nat) (xs : HeadNormalForm schema) : HeadNormalForm schema :=
  match n with
  | 0 => []
  | k + 1 => xs.flatMap fun b => [b.withContinuation (.project k b.continuation)]

theorem project_correct (env : RecEnv schema) (n : Nat) (xs : HeadNormalForm schema) :
    DerivesNoAIP env (.project n (render xs)) (render (project n xs)) := by
  cases n with
  | zero => exact .projectZero _
  | succ k =>
    exact distribute env (DyNetKAT.project (k + 1)) _ (.projectDeadlock _)
      (fun _ _ => .projectChoice _ _ _)
      (fun b => .trans (.projectPrefix k b.label b.continuation b.atomic) (.symm (.a5 _))) xs

/-- Every continuation is ground and strictly below the original process. -/
def ResidualBound (p : DyNetKAT schema) (xs : HeadNormalForm schema) : Prop :=
  ∀ b ∈ xs, Ground b.continuation ∧ prefixCount b.continuation < prefixCount p

private theorem ResidualBound.mono {p q : DyNetKAT schema} {xs : HeadNormalForm schema}
    (h : ResidualBound p xs) (hle : prefixCount p ≤ prefixCount q) :
    ResidualBound q xs :=
  fun b hb => ⟨(h b hb).1, (h b hb).2.trans_le hle⟩

private theorem ResidualBound.append {p : DyNetKAT schema} {xs ys : HeadNormalForm schema}
    (hx : ResidualBound p xs) (hy : ResidualBound p ys) : ResidualBound p (xs ++ ys) := by
  intro b hb
  exact (List.mem_append.mp hb).elim (hx b) (hy b)

private theorem leftMerge_bound {p q : DyNetKAT schema} {xs : HeadNormalForm schema}
    (hx : ResidualBound p xs) (hq : Ground q) :
    ResidualBound (.leftMerge p q) (leftMerge xs q) := by
  intro b hb
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
  obtain rfl := List.mem_singleton.mp hb
  obtain ⟨hg, hlt⟩ := hx a ha
  exact ⟨by simpa [HeadSummand.withContinuation, Ground, recursiveVars, Finset.union_eq_empty]
      using And.intro hg hq,
    Nat.add_lt_add_right hlt _⟩

private theorem synchronize_continuation {a b c : HeadSummand schema}
    (h : c ∈ synchronize a b) : c.continuation = .parallel a.continuation b.continuation := by
  cases ha : a.label <;> cases hb : b.label <;> simp [synchronize, ha, hb] at h
  all_goals
    rw [h.2]
    rfl

private theorem commMerge_bound {p q : DyNetKAT schema} {xs ys : HeadNormalForm schema}
    (hx : ResidualBound p xs) (hy : ResidualBound q ys) :
    ResidualBound (.commMerge p q) (commMerge xs ys) := by
  intro c hc
  obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨hga, hla⟩ := hx a ha
  obtain ⟨hgb, hlb⟩ := hy b hb
  rw [synchronize_continuation hc]
  exact ⟨by simpa [Ground, recursiveVars, Finset.union_eq_empty] using And.intro hga hgb,
    Nat.add_lt_add hla hlb⟩

private theorem restrict_bound {p : DyNetKAT schema} {xs : HeadNormalForm schema}
    (L : Set (CommunicationAction schema)) (hx : ResidualBound p xs) :
    ResidualBound (.restrict L p) (restrict L xs) := by
  classical
  intro b hb
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
  by_cases h : PrefixBlocked L a.label
  · simp [if_pos h] at hb
  · simp only [if_neg h, List.mem_singleton] at hb
    subst b
    exact hx a ha

private theorem project_bound {p : DyNetKAT schema} {xs : HeadNormalForm schema}
    (n : Nat) (hx : ResidualBound p xs) :
    ResidualBound (.project n p) (project n xs) := by
  cases n with
  | zero => simp [ResidualBound, project]
  | succ n =>
    intro b hb
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    obtain rfl := List.mem_singleton.mp hb
    exact hx a ha

/-- All continuation references belong to the given source name set. -/
def NamesWithin (S : Set Var) (xs : HeadNormalForm schema) : Prop :=
  ∀ b ∈ xs, ∀ x ∈ recursiveVars b.continuation, x ∈ S

private theorem NamesWithin.append {S : Set Var} {xs ys : HeadNormalForm schema}
    (hx : NamesWithin S xs) (hy : NamesWithin S ys) : NamesWithin S (xs ++ ys) :=
  fun b hb => (List.mem_append.mp hb).elim (hx b) (hy b)

private theorem NamesWithin.leftMerge {S : Set Var} {xs : HeadNormalForm schema} {q : DyNetKAT schema}
    (hx : NamesWithin S xs) (hq : ∀ x ∈ recursiveVars q, x ∈ S) :
    NamesWithin S (leftMerge xs q) := by
  intro b hb x occurs
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
  obtain rfl := List.mem_singleton.mp hb
  exact (Finset.mem_union.mp occurs).elim (hx a ha x) (hq x)

private theorem NamesWithin.commMerge {S : Set Var} {xs ys : HeadNormalForm schema}
    (hx : NamesWithin S xs) (hy : NamesWithin S ys) : NamesWithin S (commMerge xs ys) := by
  intro c hc x occurs
  obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hc
  rw [synchronize_continuation hc, recursiveVars] at occurs
  exact (Finset.mem_union.mp occurs).elim (hx a ha x) (hy b hb x)

private theorem NamesWithin.restrict {S : Set Var} {xs : HeadNormalForm schema}
    (hx : NamesWithin S xs) (L : Set (CommunicationAction schema)) :
    NamesWithin S (restrict L xs) := by
  classical
  intro b hb
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
  by_cases h : PrefixBlocked L a.label
  · simp [if_pos h] at hb
  · simp only [if_neg h, List.mem_singleton] at hb
    subst b
    exact hx a ha

private theorem NamesWithin.project {S : Set Var} {xs : HeadNormalForm schema}
    (hx : NamesWithin S xs) (n : Nat) : NamesWithin S (project n xs) := by
  cases n with
  | zero => simp [NamesWithin, HeadNormalForm.project]
  | succ n =>
    intro b hb
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    obtain rfl := List.mem_singleton.mp hb
    exact hx a ha

end HeadNormalForm

def IsDNKNormalForm (q : DyNetKAT schema) : Prop :=
  ∃ xs : HeadNormalForm schema, q = xs.render

open HeadNormalForm in
private theorem normalizeHead_aux (env : RecEnv schema) (p : DyNetKAT schema) (names : Set Var)
    (bounded : ∀ x ∈ recursiveVars p, x ∈ names)
    (h : GuardedOccurrences p ∨
      ∀ x ∈ recursiveVars p, ∃ xs : HeadNormalForm schema, DerivesNoAIP env (.var x) xs.render ∧ NamesWithin names xs) :
    ∃ xs : HeadNormalForm schema, DerivesNoAIP env p xs.render ∧
      (Ground p → ResidualBound p xs) ∧ NamesWithin names xs := by
  have split (p q : DyNetKAT schema)
      (h : (GuardedOccurrences p ∧ GuardedOccurrences q) ∨
        ∀ x ∈ recursiveVars p ∪ recursiveVars q,
          ∃ xs : HeadNormalForm schema, DerivesNoAIP env (.var x) xs.render ∧ NamesWithin names xs) :
      (GuardedOccurrences p ∨
        ∀ x ∈ recursiveVars p, ∃ xs : HeadNormalForm schema, DerivesNoAIP env (.var x) xs.render ∧ NamesWithin names xs) ∧
      (GuardedOccurrences q ∨
        ∀ x ∈ recursiveVars q, ∃ xs : HeadNormalForm schema, DerivesNoAIP env (.var x) xs.render ∧ NamesWithin names xs) := by
    rcases h with ⟨hp, hq⟩ | h
    · exact ⟨Or.inl hp, Or.inl hq⟩
    · exact ⟨Or.inr (fun x hx => h x (Finset.mem_union_left _ hx)),
        Or.inr (fun x hx => h x (Finset.mem_union_right _ hx))⟩
  have groundPair {p q : DyNetKAT schema} (h : recursiveVars p ∪ recursiveVars q = ∅) :
      Ground p ∧ Ground q := Finset.union_eq_empty.mp h
  have leftNames {p q : DyNetKAT schema}
      (allNames : ∀ x ∈ recursiveVars p ∪ recursiveVars q, x ∈ names) :
      ∀ x ∈ recursiveVars p, x ∈ names :=
    fun x hx => allNames x (Finset.mem_union_left _ hx)
  have rightNames {p q : DyNetKAT schema}
      (allNames : ∀ x ∈ recursiveVars p ∪ recursiveVars q, x ∈ names) :
      ∀ x ∈ recursiveVars q, x ∈ names :=
    fun x hx => allNames x (Finset.mem_union_right _ hx)
  induction p with
  | deadlock => exact ⟨[], .refl _, by simp [ResidualBound], by simp [NamesWithin]⟩
  | nSeq z p =>
    refine ⟨_, packetHeads_correct env z p, ?_, ?_⟩
    · intro hg b hb
      obtain ⟨⟨α, π⟩, _, rfl⟩ := List.mem_map.mp hb
      exact ⟨hg, Nat.lt_succ_self _⟩
    · intro b hb
      obtain ⟨⟨α, π⟩, _, rfl⟩ := List.mem_map.mp hb
      exact bounded
  | recv x z p =>
    refine ⟨[.recv x z p], .symm (.a5 _), ?_, ?_⟩
    · intro hg b hb
      obtain rfl := List.mem_singleton.mp hb
      exact ⟨hg, Nat.lt_succ_self _⟩
    · intro b hb
      obtain rfl := List.mem_singleton.mp hb
      exact bounded
  | send x z p =>
    refine ⟨[.send x z p], .symm (.a5 _), ?_, ?_⟩
    · intro hg b hb
      obtain rfl := List.mem_singleton.mp hb
      exact ⟨hg, Nat.lt_succ_self _⟩
    · intro b hb
      obtain rfl := List.mem_singleton.mp hb
      exact bounded
  | rcfgPrefix x z p =>
    refine ⟨[.rcfg x z p], .symm (.a5 _), ?_, ?_⟩
    · intro hg b hb
      obtain rfl := List.mem_singleton.mp hb
      exact ⟨hg, Nat.lt_succ_self _⟩
    · intro b hb
      obtain rfl := List.mem_singleton.mp hb
      exact bounded
  | choice p q ihp ihq =>
    obtain ⟨hp, hq⟩ := split p q h
    obtain ⟨xs, dx, bx, nx⟩ := ihp (leftNames (q := q) bounded) hp
    obtain ⟨ys, dy, bys, ny⟩ := ihq (rightNames (p := p) bounded) hq
    refine ⟨_, .trans (.choiceCongr dx dy) (render_append ..), fun hg => ?_, nx.append ny⟩
    obtain ⟨gp, gq⟩ := groundPair hg
    exact ((bx gp).mono (Nat.le_add_right ..)).append ((bys gq).mono (Nat.le_add_left ..))
  | parallel p q ihp ihq =>
    obtain ⟨hp, hq⟩ := split p q h
    obtain ⟨xs, dx, bx, nx⟩ := ihp (leftNames (q := q) bounded) hp
    obtain ⟨ys, dy, bys, ny⟩ := ihq (rightNames (p := p) bounded) hq
    refine ⟨_, parallel_correct env dx dy, fun hg => ?_,
      ((nx.leftMerge (rightNames (p := p) bounded)).append
        (ny.leftMerge (leftNames (q := q) bounded))).append (nx.commMerge ny)⟩
    obtain ⟨gp, gq⟩ := groundPair hg
    exact ((leftMerge_bound (bx gp) gq).append
      ((leftMerge_bound (bys gq) gp).mono (Nat.add_comm ..).le)).append
      (commMerge_bound (bx gp) (bys gq))
  | leftMerge p q ihp ihq =>
    obtain ⟨hp, _⟩ := split p q h
    obtain ⟨_, dx, bx, nx⟩ := ihp (leftNames (q := q) bounded) hp
    refine ⟨_, .trans (.leftMergeCongr dx (.refl _)) (leftMerge_correct ..), fun hg => ?_,
      nx.leftMerge (rightNames (p := p) bounded)⟩
    obtain ⟨gp, gq⟩ := groundPair hg
    exact leftMerge_bound (bx gp) gq
  | commMerge p q ihp ihq =>
    obtain ⟨hp, hq⟩ := split p q h
    obtain ⟨_, dx, bx, nx⟩ := ihp (leftNames (q := q) bounded) hp
    obtain ⟨_, dy, bys, ny⟩ := ihq (rightNames (p := p) bounded) hq
    refine ⟨_, .trans (.commMergeCongr dx dy) (commMerge_correct ..), fun hg => ?_, nx.commMerge ny⟩
    obtain ⟨gp, gq⟩ := groundPair hg
    exact commMerge_bound (bx gp) (bys gq)
  | restrict L p ih =>
    obtain ⟨_, dx, bx, nx⟩ := ih bounded h
    exact ⟨_, .trans (.restrictCongr L dx) (restrict_correct ..),
      fun hg => restrict_bound L (bx hg), nx.restrict L⟩
  | project n p ih =>
    obtain ⟨_, dx, bx, nx⟩ := ih bounded h
    exact ⟨_, .trans (.projectCongr n dx) (project_correct ..),
      fun hg => project_bound n (bx hg), nx.project n⟩
  | var x =>
    rcases h with h | h
    · exact False.elim h
    · obtain ⟨xs, dx, nx⟩ := h x (by simp)
      exact ⟨xs, dx, by simp [Ground], nx⟩

theorem Ground.exists_headNormalForm {env : RecEnv schema} {p : DyNetKAT schema} (h : Ground p) :
    ∃ xs : HeadNormalForm schema, DerivesNoAIP env p xs.render ∧ HeadNormalForm.ResidualBound p xs := by
  obtain ⟨xs, dx, hx, _⟩ := normalizeHead_aux env p Set.univ (by simp) (Or.inl h.guarded)
  exact ⟨xs, dx, hx h⟩

/-- Head-summand witness for the typed syntactically guarded domain. -/
theorem exists_headNormalForm_of_guarded (env : RecEnv schema) {p : DyNetKAT schema}
    (h : GuardedOccurrences p) :
    ∃ xs : HeadNormalForm schema, DerivesNoAIP env p xs.render :=
  let ⟨xs, dx, _, _⟩ := normalizeHead_aux env p Set.univ (by simp) (Or.inl h)
  ⟨xs, dx⟩

/-- arXiv v4 Lemma 9, under the Lean interpretation of guarded occurrences. -/
theorem guarded_normalizes (env : RecEnv schema) {p : DyNetKAT schema} (h : GuardedOccurrences p) :
    ∃ q, IsDNKNormalForm q ∧ DerivesNoAIP env p q := by
  obtain ⟨xs, d⟩ := exists_headNormalForm_of_guarded env h
  exact ⟨xs.render, ⟨xs, rfl⟩, d⟩

/-- Normalize without introducing unrelated recursive names into continuations. -/
theorem WellFormed.exists_headNormalForm_closed {env : RecEnv schema} {p : DyNetKAT schema}
    (h : WellFormed env p) : ∃ xs : HeadNormalForm schema, DerivesNoAIP env p xs.render ∧
      ∀ b ∈ xs, WellFormed env b.continuation := by
  let S := {x | ReachableVar env p x}
  have refs (x : Var) (hx : x ∈ recursiveVars p) :
      ∃ xs : HeadNormalForm schema, DerivesNoAIP env (.var x) xs.render ∧ xs.NamesWithin S := by
    obtain ⟨body, lookup, guarded⟩ := h.2 x (.direct hx)
    obtain ⟨xs, d, _, names⟩ := normalizeHead_aux env body S
      (fun _ mem => ReachableVar.throughDefinition (.direct hx) lookup mem) (Or.inl guarded)
    exact ⟨xs, .trans (.unfold lookup) d, names⟩
  obtain ⟨xs, dx, _, names⟩ := normalizeHead_aux env p S (fun _ mem => .direct mem) (Or.inr refs)
  refine ⟨xs, dx, fun b hb => ?_⟩
  have subset {x : Var} (reach : ReachableVar env b.continuation x) : ReachableVar env p x := by
    induction reach with
    | direct mem => exact names b hb _ mem
    | throughDefinition _ lookup mem ih => exact .throughDefinition ih lookup mem
  exact ⟨fun x hx => h.1 x (subset hx), fun x hx => h.2 x (subset hx)⟩

/-- Resolve needed head variables, leaving references behind prefixes as continuations. -/
theorem WellFormed.exists_headNormalForm {env : RecEnv schema} {p : DyNetKAT schema} (h : WellFormed env p) :
    ∃ xs : HeadNormalForm schema, DerivesNoAIP env p xs.render := by
  obtain ⟨xs, d, _⟩ := h.exists_headNormalForm_closed
  exact ⟨xs, d⟩

theorem WellFormed.normalizes {env : RecEnv schema} {p : DyNetKAT schema} (h : WellFormed env p) :
    ∃ q, IsDNKNormalForm q ∧ DerivesNoAIP env p q := by
  obtain ⟨xs, d⟩ := h.exists_headNormalForm
  exact ⟨xs.render, ⟨xs, rfl⟩, d⟩

end DyNetKAT.DyNetKAT
