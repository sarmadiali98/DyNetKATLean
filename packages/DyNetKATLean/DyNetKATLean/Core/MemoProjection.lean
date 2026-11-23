import DyNetKATLean.Core.FiniteProjection

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

open DyNetKAT.NetKAT

/-- An executable partial identity for a fixed graph and body-classifier table.
A hit must preserve the ordinary renderer at every depth. -/
structure ProjectionMemoKey {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema) where
  Key : Type
  eqKey : DecidableEq Key
  key : CheckedResidual schema → Option Key
  sound : ∀ {p q k}, key p = some k → key q = some k →
    ∀ n, renderProjection G bodyChecks n p = renderProjection G bodyChecks n q

namespace ProjectionMemoKey

/-- Reference lookup uses the fixed body classifier. Along a prefix chain
there are no restriction tests of the incoming classifier. -/
inductive PrefixChain (schema : NetKAT.PacketSchema := NetKAT.ctxSchema) where
  | deadlock
  | ref (i : NodeId)
  | step (label : MoveLabel schema) (tail : PrefixChain schema)
  deriving DecidableEq

def PrefixChain.proc : PrefixChain schema → GProc schema
  | .deadlock => .deadlock
  | .ref i => .ref i
  | .step (.visible (.packet z)) p => .nSeq z p.proc
  | .step (.visible (.rcfg x z)) p => .rcfgPrefix x z p.proc
  | .step (.recv x z) p => .recv x z p.proc
  | .step (.send x z) p => .send x z p.proc

def prefixKey : GProc schema → Option (PrefixChain schema)
  | .deadlock => some .deadlock
  | .ref i => some (.ref i)
  | .nSeq z p => (prefixKey p).map (.step (.visible (.packet z)))
  | .rcfgPrefix x z p => (prefixKey p).map (.step (.visible (.rcfg x z)))
  | .recv x z p => (prefixKey p).map (.step (.recv x z))
  | .send x z p => (prefixKey p).map (.step (.send x z))
  | _ => none

theorem prefixKey_proc {p : GProc schema} {k : PrefixChain schema} (h : prefixKey p = some k) :
    k.proc = p := by
  induction p generalizing k <;> simp only [prefixKey] at h
  all_goals first
    | cases h <;> rfl
    | obtain ⟨_, hk, rfl⟩ := Option.map_eq_some'.mp h
      simp only [PrefixChain.proc]
      rw [‹∀ {k}, prefixKey _ = some k → k.proc = _› hk]

theorem prefixChain_checks (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (n : Nat) (k : PrefixChain schema) (c d : RestrictionChecks schema) :
    renderProjection G bodyChecks n ⟨k.proc, c⟩ =
      renderProjection G bodyChecks n ⟨k.proc, d⟩ := by
  induction n generalizing k c d with
  | zero => rfl
  | succ n ih =>
    cases k with
    | deadlock | ref => rfl
    | step l k =>
      have equal := ih k (c.child false) (d.child false)
      cases l with
      | visible l =>
        cases l <;> simp [PrefixChain.proc, renderProjection, checkedMoves, localCheckedMoves, equal]
      | recv | send =>
        simp [PrefixChain.proc, renderProjection, checkedMoves, localCheckedMoves, equal]

def prefixChains (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema) :
    ProjectionMemoKey G bodyChecks where
  Key := (PrefixChain schema)
  eqKey := inferInstance
  key p := prefixKey p.proc
  sound := by
    rintro ⟨p, c⟩ ⟨q, d⟩ k hp hq n
    change prefixKey p = some k at hp
    change prefixKey q = some k at hq
    rw [← prefixKey_proc hp, ← prefixKey_proc hq]
    exact prefixChain_checks G bodyChecks n k c d

/-- Disable all lookups and insertions, for a direct recursion-count baseline. -/
def disabled (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema) :
    ProjectionMemoKey G bodyChecks where
  Key := Unit
  eqKey := inferInstance
  key _ := none
  sound := by simp

end ProjectionMemoKey

structure ProjectionMemoStats where
  /-- Calls served by a cached subtree. -/
  hits : Nat := 0
  /-- Calls computed directly, including unkeyed states and depth zero. -/
  misses : Nat := 0
  /-- Stored positive-depth subproblems at the end of rendering. -/
  entries : Nat := 0
  deriving Repr, DecidableEq

namespace ProjectionMemo

abbrev Table (K : Type) (schema : NetKAT.PacketSchema := NetKAT.ctxSchema) := List ((Nat × K) × (DyNetKAT schema))

structure State (K : Type) (schema : NetKAT.PacketSchema := NetKAT.ctxSchema) where
  table : (Table K (schema := schema)) := []
  hits : Nat := 0
  misses : Nat := 0

variable {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}

/-- The cache is private to a single fixed graph, classifier table, and key interface. -/
def Valid (keys : ProjectionMemoKey G bodyChecks) (table : (Table keys.Key (schema := schema))) : Prop :=
  ∀ n k q, ((n, k), q) ∈ table → ∀ p, keys.key p = some k →
    renderProjection G bodyChecks n p = some q

theorem valid_empty (keys : ProjectionMemoKey G bodyChecks) : Valid keys [] := by
  simp [Valid]

def lookup {K : Type} [DecidableEq K] (table : (Table K (schema := schema))) (n : Nat) (key : K) :
    Option (DyNetKAT schema) :=
  (table.find? fun e => decide (e.1 = (n, key))).map Prod.snd

theorem lookup_correct {keys : ProjectionMemoKey G bodyChecks} {table : (Table keys.Key (schema := schema))}
    {n : Nat} {k : keys.Key} {p : CheckedResidual schema} {q : DyNetKAT schema}
    (valid : Valid keys table) (hk : keys.key p = some k)
    (hit : @lookup schema _ keys.eqKey table n k = some q) :
    renderProjection G bodyChecks n p = some q := by
  letI := keys.eqKey
  obtain ⟨⟨idx, t⟩, he, rfl⟩ := Option.map_eq_some'.mp hit
  have hidx : idx = (n, k) := of_decide_eq_true (List.find?_some (p := fun e : (Nat × keys.Key) × (DyNetKAT schema) => decide (e.1 = (n, k))) he)
  subst idx
  exact valid n k t (List.mem_of_find?_eq_some he) p hk

theorem insert_valid {keys : ProjectionMemoKey G bodyChecks} {table : (Table keys.Key (schema := schema))}
    {n : Nat} {k : keys.Key} {p : CheckedResidual schema} {q : DyNetKAT schema}
    (valid : Valid keys table) (hk : keys.key p = some k)
    (result : renderProjection G bodyChecks n p = some q) :
    Valid keys (((n, k), q) :: table) := by
  intro m j t hm u hu
  rcases List.mem_cons.mp hm with he | he
  · cases he
    rw [← keys.sound hk hu]
    exact result
  · exact valid m j t he u hu

/-- Thread the cache through siblings in the ordinary row order. -/
def branches {K : Type} (run : CheckedResidual schema → (State K (schema := schema)) → Option ((DyNetKAT schema) × (State K (schema := schema)))) :
    List (CheckedMove schema) → (State K (schema := schema)) → Option (List (DyNetKAT schema) × (State K (schema := schema)))
  | [], s => some ([], s)
  | (label, p) :: row, s => do
      let (q, s) ← run p s
      let (qs, s) ← branches run row s
      return (label.prefix q :: qs, s)

def run (keys : ProjectionMemoKey G bodyChecks) :
    Nat → CheckedResidual schema → (State keys.Key (schema := schema)) → Option ((DyNetKAT schema) × (State keys.Key (schema := schema)))
  | 0, _, s => some (.deadlock, { s with misses := s.misses + 1 })
  | n + 1, p, s => do
      let k := keys.key p
      match k.bind (@lookup schema _ keys.eqKey s.table (n + 1)) with
      | some q => return (q, { s with hits := s.hits + 1 })
      | none =>
        let row ← checkedMoves G bodyChecks p
        let (qs, s) ← branches (run keys n) row { s with misses := s.misses + 1 }
        let q := choiceOf qs
        let table := match k with
          | some key => ((n + 1, key), q) :: s.table
          | none => s.table
        return (q, { s with table })

/-- Agreement and invariant preservation, including ordinary failure. -/
def Correct {α : Type} (keys : ProjectionMemoKey G bodyChecks)
    (expected : Option α) (actual : Option (α × (State keys.Key (schema := schema)))) : Prop :=
  actual.map Prod.fst = expected ∧ ∀ a s, actual = some (a, s) → Valid keys s.table

private theorem branches_correct {keys : ProjectionMemoKey G bodyChecks} {n : Nat}
    {run : CheckedResidual schema → (State keys.Key (schema := schema)) → Option ((DyNetKAT schema) × (State keys.Key (schema := schema)))}
    (ih : ∀ p s, Valid keys s.table →
      Correct keys (renderProjection G bodyChecks n p) (run p s))
    (row : List (CheckedMove schema)) (s : (State keys.Key (schema := schema))) (valid : Valid keys s.table) :
    Correct keys (row.mapM fun m => (renderProjection G bodyChecks n m.2).map m.1.prefix)
      (branches run row s) := by
  induction row generalizing s with
  | nil =>
    refine ⟨rfl, ?_⟩
    rintro _ _ h
    cases h
    exact valid
  | cons m row tail =>
    obtain ⟨label, p⟩ := m
    obtain ⟨he, hv⟩ := ih p s valid
    cases hr : run p s with
    | none =>
      simp [hr] at he
      simp [Correct, branches, hr, ← he]
    | some res =>
      obtain ⟨q, s'⟩ := res
      obtain ⟨ht, htValid⟩ := tail s' (hv q s' hr)
      cases hs : branches run row s' with
      | none =>
        simp [hr] at he
        simp [hs] at ht
        simp [Correct, branches, hr, hs, ← he, ← ht]
      | some res =>
        obtain ⟨qs, s''⟩ := res
        simp [hr] at he
        simp [hs] at ht
        simp [Correct, branches, hr, hs, ← he, ← ht, htValid qs s'' hs]

theorem run_correct (keys : ProjectionMemoKey G bodyChecks) (n : Nat)
    (p : CheckedResidual schema) (s : (State keys.Key (schema := schema))) (valid : Valid keys s.table) :
    Correct keys (renderProjection G bodyChecks n p) (run keys n p s) := by
  induction n generalizing p s with
  | zero => simp [Correct, run, renderProjection, valid]
  | succ n ih =>
    cases hh : (keys.key p).bind (@lookup schema _ keys.eqKey s.table (n + 1)) with
    | some q =>
      obtain ⟨k, hk, hit⟩ := Option.bind_eq_some_iff.mp hh
      simp [Correct, run, hh, lookup_correct valid hk hit, valid]
    | none =>
      cases hr : checkedMoves G bodyChecks p with
      | none => simp [Correct, run, hh, hr, renderProjection]
      | some row =>
        let start := { s with misses := s.misses + 1 }
        obtain ⟨he, hv⟩ := branches_correct ih row start valid
        cases hb : branches (run keys n) row start with
        | none =>
          simp [hb] at he
          simp [Correct, run, hh, renderProjection, hr, ← he, hb, start]
        | some res =>
          obtain ⟨qs, s'⟩ := res
          simp [hb] at he
          have result : renderProjection G bodyChecks (n + 1) p = some (choiceOf qs) := by
            simp [renderProjection, hr, ← he]
          have nextValid := hv qs s' hb
          cases hk : keys.key p with
          | none => simp [Correct, run, hh, hr, hb, hk, start, result, nextValid]
          | some k =>
            have newValid := insert_valid nextValid hk result
            have miss : @lookup schema _ keys.eqKey s.table (n + 1) k = none := by
              simpa only [hk, Option.bind_some] using hh
            simp [Correct, run, miss, hr, hb, hk, start, result, newValid]

end ProjectionMemo

/-- Execute from a fresh cache. On a hit the stored rendered subtree is reused
directly, so shared children need no separate DAG expansion procedure. -/
def renderProjectionMemoWith {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}
    (keys : ProjectionMemoKey G bodyChecks) (n : Nat) (p : CheckedResidual schema) :
    Option ((DyNetKAT schema) × ProjectionMemoStats) :=
  (ProjectionMemo.run keys n p {}).map fun (q, s) =>
    (q, ⟨s.hits, s.misses, s.table.length⟩)

theorem renderProjectionMemoWith_eq {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}
    (keys : ProjectionMemoKey G bodyChecks) (n : Nat) (p : CheckedResidual schema) :
    (renderProjectionMemoWith keys n p).map Prod.fst = renderProjection G bodyChecks n p := by
  rw [renderProjectionMemoWith, Option.map_map]
  exact (ProjectionMemo.run_correct keys n p {} (ProjectionMemo.valid_empty keys)).1

def renderProjectionMemo (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (n : Nat) (p : CheckedResidual schema) : Option ((DyNetKAT schema) × ProjectionMemoStats) :=
  renderProjectionMemoWith (.prefixChains G bodyChecks) n p

theorem renderProjectionMemo_eq (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (n : Nat) (p : CheckedResidual schema) :
    (renderProjectionMemo G bodyChecks n p).map Prod.fst = renderProjection G bodyChecks n p :=
  renderProjectionMemoWith_eq _ n p

theorem renderProjectionMemo_exists {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live)
    (n : Nat) {p : CheckedResidual schema} (hp : p.Valid live) :
    ∃ q stats, renderProjectionMemo G bodyChecks n p = some (q, stats) := by
  obtain ⟨q, hq⟩ := renderProjection_exists hG n hp
  rw [← renderProjectionMemo_eq] at hq
  obtain ⟨⟨_, stats⟩, he, rfl⟩ := Option.map_eq_some'.mp hq
  exact ⟨_, stats, he⟩

theorem renderProjectionMemo_source {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) (hw : WellFormed env root)
    (checks : RestrictionChecks schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (hc : AllRestrictionChecksCorrect (toGProc root) checks)
    (hb : ∀ x b, ReachableVar env root x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x))) (n : Nat) :
    ∃ q stats, renderProjectionMemo (toGraph env root S hs) bodyChecks n
      ⟨toGProc root, checks⟩ = some (q, stats) ∧ Bisimilar env q (.project n root) := by
  obtain ⟨q, hr, bis⟩ := renderProjection_source hs hw checks bodyChecks hc hb n
  rw [← renderProjectionMemo_eq] at hr
  obtain ⟨⟨_, stats⟩, hm, rfl⟩ := Option.map_eq_some'.mp hr
  exact ⟨_, stats, hm, bis⟩

theorem renderProjectionMemo_bisimilar {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live)
    {env : RecEnv schema} {p q : DyNetKAT schema} {state : CheckedResidual schema} {n : Nat}
    {stats : ProjectionMemoStats} (hv : state.Valid live) (hc : Corr G env p state.proc)
    (hr : renderProjectionMemo G bodyChecks n state = some (q, stats)) :
    Bisimilar env q (.project n p) := by
  apply renderProjection_bisimilar hG hv hc
  rw [← renderProjectionMemo_eq, hr]
  rfl

theorem renderProjectionMemo_restricted {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) (hw : WellFormed env root)
    (checks : RestrictionChecks schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (hc : AllRestrictionChecksCorrect (toGProc root) checks)
    (hb : ∀ x b, ReachableVar env root x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x)))
    (L : Set (CommunicationAction schema)) (blocked : CommunicationAction schema → Bool)
    (hL : ∀ a, blocked a = true ↔ a ∈ L) (n : Nat) :
    ∃ q stats, renderProjectionMemo (toGraph env root S hs) bodyChecks n
      ((CheckedResidual.mk (toGProc root) checks).restrict L blocked) = some (q, stats) ∧
      Bisimilar env q (.restrict L (.project n root)) := by
  obtain ⟨q, hr, bis⟩ := renderProjection_restricted hs hw checks bodyChecks hc hb L blocked hL n
  rw [← renderProjectionMemo_eq] at hr
  obtain ⟨⟨_, stats⟩, hm, rfl⟩ := Option.map_eq_some'.mp hr
  exact ⟨_, stats, hm, bis⟩

end DyNetKAT.DyNetKAT
