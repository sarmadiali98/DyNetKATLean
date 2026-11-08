# Lean Proof Status and Verbatim Snippets

This report audits the current Lean working tree, including untracked `.lean` files. “Fully proved” means a Lean theorem declaration with a kernel-checked proof in the source and successful compilation of the requested target. A definition or inductive proposition alone is marked “formalized only.”

## Verification

Command run from `lean/`: `lake build DyNetKAT`

Result: **success**, exit status 0; `Build completed successfully`. Linter warnings were reported. No source files were changed by the build as part of this audit.

The repository copy `DyNetKAT.pdf` was inspected through extracted text. Relevant paper anchors: Figure 8, Definition 2, Proposition 1, Lemma 3, Definition 7, Figure 11, Lemmas 5 and 8–11, Theorem 1.

## Exact paper theorem status

| Paper result | Status in Lean workspace |
|---|---|
| Figure 8 operational rules | The core and several extended rules are declared in `Step`. This is a formalization of a relation, not a proof that all paper semantics/results hold. |
| Definition 2 bisimulation | `IsBisimulation` and `Bisimilar` are definitions. Equivalence properties are proved. |
| Proposition 1 semantic layering | No theorem matching the iff between NetKAT denotational equality and `(p;d) ~ (q;d)` for every `d`. |
| Lemma 3 congruence | Per-constructor preservation theorems prove substantial fragments. No single theorem covers every paper context, and recursion substitution/axiom congruence is absent. |
| Definition 7 guardedness | `GuardedOccurrences` is a structural formalization, but is not established equivalent to the paper’s per-occurrence guardedness condition. |
| Figure 11 `EDNK` | No equational syntax/derivability relation for A0–A15/AIP and `ENK` was found. |
| Lemma 5 NetKAT normal forms | Normal-form representation and interpretation are present; general normalization theorem is absent. `NormalForm.lean` comments explicitly disclaim implementing normalization or proving Lemma 5. |
| Lemma 8 branching finiteness | No theorem found. |
| Lemma 9 DyNetKAT normalization | No theorem found. |
| Lemma 10 axiom soundness without AIP | No axiom derivability or soundness proof found. |
| Lemma 11 AIP soundness | No AIP theorem found. Projection SOS/congruence does not imply AIP soundness. |
| Theorem 1 soundness and ground-completeness | **Not proved/formalized as a theorem**. This must not be claimed based on the executable results below. |

## Proven results beyond the paper theorem

### NetKAT denotational semantics and evaluator

`NetKAT/Semantics.lean` defines relational semantics for the repository’s finite packet type and proves basic identities and algebraic laws. In particular, `Semantics` is at lines 61–72, `seq_sem` at 100–102, complete-test/assignment semantics at 252 and 635, and selected NetKAT laws at 389–490 and 498–588.

`NetKAT/Evaluator.lean:1078-1148` proves `execute_correct` for every constructor of its `NetKAT` inductive. The theorem says evaluation always returns a supported finite set and membership in that set is equivalent to relational semantics. The proof handles star via finiteness of `CtxPkt` and bounded reachability stabilization. The evaluator’s `EvalResult` deliberately separates unsupported evaluation from supported empty output (`Evaluator.lean:27-38`).

Verbatim declaration, `NetKAT/Evaluator.lean:1078-1148`:

```lean
theorem execute_correct
    (p : NetKAT) (σ : CtxPkt) :
    ∃ B : Finset CtxPkt,
      execute p σ = .supported B ∧
      ∀ τ, Semantics p σ τ ↔ τ ∈ B := by
  induction p generalizing σ with
  | drop =>
      have h := execute_drop σ
      refine ⟨∅, h, ?_⟩
      intro τ
      simpa [h] using (execute_drop_correct σ τ)
  | id =>
      have h := execute_id σ
      refine ⟨{σ}, h, ?_⟩
      intro τ
      simpa [h] using (execute_id_correct σ τ)
  | test a =>
      exact execute_test_correct a σ
  | completeTest α =>
      refine ⟨if σ = α then {σ} else ∅, ?_, ?_⟩
      · rw [execute_completeTest]
        split <;> rfl
      · intro τ
        by_cases h : σ = α
        · subst h
          simpa [execute_completeTest] using (execute_completeTest_correct σ σ τ)
        · simpa [execute_completeTest, h] using (execute_completeTest_correct α σ τ)
  | assign1 f v =>
      have h := execute_assign1 f v σ
      refine ⟨{Packet.update σ f v}, h, ?_⟩
      intro τ
      simpa [h] using (execute_assign1_correct f v σ τ)
  | union p q ihp ihq =>
      obtain ⟨A, hA, corrA⟩ := ihp σ
      obtain ⟨B, hB, corrB⟩ := ihq σ
      have h := execute_union_supported p q σ A B hA hB
      refine ⟨A ∪ B, h, ?_⟩
      intro τ
      simpa [h] using (execute_union_correct p q σ τ A B hA hB corrA corrB)
  | seq p q ihp ihq =>
      obtain ⟨A, hA, corrA⟩ := ihp σ
      obtain ⟨B, hB⟩ := evalSeqWith_supported (fun τ => execute q τ)
        (fun τ => (execute_supported q τ)) A.1
      have hB' : evalSeq q A.1 = .supported B := by
        simpa [evalSeqWith_execute_eq] using hB
      have hpost : post q A = .supported B := by
        simpa [post] using hB'
      have hcorrB : ∀ r, r ∈ B ↔ ∃ τ, τ ∈ A ∧ Semantics q τ r := by
        exact post_correct q A B hpost (by
          intro τ hτ
          obtain ⟨C, hC, corrC⟩ := ihq τ
          exact ⟨C, hC, corrC⟩)
      have hseq : execute (.seq p q) σ = .supported B := by
        exact execute_seq_supported p q σ A hA |>.trans hB'
      refine ⟨B, hseq, ?_⟩
      intro r
      rw [seq_sem]
      constructor
      · rintro ⟨τ, hp, hq⟩
        exact (hcorrB r).mpr ⟨τ, (corrA τ).mp hp, hq⟩
      · intro hr
        obtain ⟨τ, hτ, hq⟩ := (hcorrB r).mp hr
        exact ⟨τ, (corrA τ).mpr hτ, hq⟩
  | star p ihp =>
      obtain ⟨B, hB⟩ := execute_supported (.star p) σ
      refine ⟨B, hB, ?_⟩
      intro τ
      exact execute_star_correct p σ B hB (by
        intro ρ _
        exact ihp ρ) τ
```

This declaration is fully proved and is a strong executable/denotational correctness result. It is **not** Theorem 1 of the paper: it says nothing about derivability from `EDNK`, bisimilarity of arbitrary DyNetKAT processes, or ground-completeness.

### Packet transition enumeration

Verbatim soundness theorem, `DyNetKAT/Executable.lean:57-88`:

```lean
theorem packetTransitions_sound
    (env : RecEnv)
    (p : NetKAT)
    (continuation : DyNetKAT)
    (pending handled : List CtxPkt)
    (results : Multiset (Action × Config))
    (action : Action)
    (destination : Config)
    (hEval : packetTransitions p continuation pending handled = some results)
    (hMem : (action, destination) ∈ results) :
    Step env
      { proc := .nSeq p continuation
        pending := pending
        handled := handled }
      action destination := by
  cases pending with
  | nil =>
      simp [packetTransitions] at hEval
      subst results
      simp at hMem
  | cons sigma pendingTail =>
      cases hExec : execute p sigma with
      | unsupported =>
          simp [packetTransitions, hExec] at hEval
      | supported outputs =>
          simp [packetTransitions, hExec] at hEval
          subst results
          rcases Multiset.mem_map.mp hMem with ⟨tau, hTau, hPair⟩
          cases hPair
          exact execute_packet_step env p continuation sigma tau pendingTail handled
           outputs hExec hTau
```

Verbatim completeness theorem, `DyNetKAT/Executable.lean:90-119`:

```lean
theorem packetTransitions_complete
    (env : RecEnv)
    (p : NetKAT)
    (continuation : DyNetKAT)
    (pending handled : List CtxPkt)
    (action : Action)
    (destination : Config)
    (hStep :
      Step env
        { proc := .nSeq p continuation
          pending := pending
          handled := handled }
        action destination) :
    ∃ results : Multiset (Action × Config),
      packetTransitions p continuation pending handled = some results ∧
      (action, destination) ∈ results := by
  cases hStep with
  | cpol_seq_ok p continuation sigma sigma' pendingTail handled evaluates =>
      obtain ⟨outputs, hExec, hCorrect⟩ := execute_correct p sigma
      refine ⟨outputs.1.map (fun tau =>
        (Action.packet sigma tau,
          { proc := continuation
            pending := pendingTail
            handled := tau :: handled })), ?_, ?_⟩
      · simp [packetTransitions, hExec]
      · apply Multiset.mem_map.mpr
        refine ⟨sigma', ?_, rfl⟩
        exact (execute_supported_iff_semantics p sigma sigma' outputs hExec).mpr evaluates
```

Both theorems are fully proved for transitions from an `nSeq` source term, which can only make the packet label produced by `cpol_seq_ok`. They do not enumerate arbitrary process transitions and do not establish bisimulation or algebraic soundness/completeness. The environment parameter is present but irrelevant to this constructor beyond the resulting `Step env` type.

## Verbatim declaration: all SOS constructors

Complete declaration from `DyNetKAT/DyNetKAT/Semantics.lean:13-239`:

```lean
inductive Step (env : RecEnv) : Config → Action → Config → Prop
  | cpol_seq_ok
      (p : DyNetKAT.NetKAT.NetKAT) (q : DyNetKAT)
      (sigma sigma' : CtxPkt)
      (pendingTail handled : List CtxPkt)
      (evaluates : DyNetKAT.NetKAT.Semantics p sigma sigma') :
      Step env
        (show Config from
          { proc := .nSeq p q, pending := sigma :: pendingTail, handled := handled })
        (show Action from Action.packet sigma sigma')
         (show Config from
           { proc := q, pending := pendingTail, handled := sigma' :: handled })

  | cpol_choice_l
      (p q p' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .choice p q, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })

  | cpol_choice_r
      (p q q' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        action
        (show Config from { proc := q', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .choice p q, pending := pending, handled := handled })
        action
        (show Config from { proc := q', pending := pending', handled := handled' })

  | cpol_par_l
      (p q p' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .parallel p q, pending := pending, handled := handled })
        action
        (show Config from { proc := .parallel p' q, pending := pending', handled := handled' })

  | cpol_par_r
      (p q q' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        action
        (show Config from { proc := q', pending := pending', handled := handled' })) :
      Step env
         (show Config from { proc := .parallel p q, pending := pending, handled := handled })
         action
         (show Config from { proc := .parallel p q', pending := pending', handled := handled' })

  | cpol_left_merge
      (p q p' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .leftMerge p q, pending := pending, handled := handled })
        action
        (show Config from
          { proc := .parallel p' q, pending := pending', handled := handled' })

  | cpol_comm_merge_recv_send
      (x : Channel) (r : DyNetKAT.NetKAT.NetKAT)
      (q s q' s' : DyNetKAT)
      (pending : List CtxPkt)
      (handled : List CtxPkt)
      (recv_step : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        (show Action from Action.recv x r)
        (show Config from { proc := q', pending := pending, handled := handled }))
      (send_step : Step env
        (show Config from { proc := s, pending := pending, handled := handled })
        (show Action from Action.send x r)
        (show Config from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config from { proc := .commMerge q s, pending := pending, handled := handled })
        (show Action from Action.rcfg x r)
        (show Config from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_comm_merge_send_recv
      (x : Channel) (r : DyNetKAT.NetKAT.NetKAT)
      (q s q' s' : DyNetKAT)
      (pending : List CtxPkt)
      (handled : List CtxPkt)
      (send_step : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        (show Action from Action.send x r)
        (show Config from { proc := q', pending := pending, handled := handled }))
      (recv_step : Step env
        (show Config from { proc := s, pending := pending, handled := handled })
        (show Action from Action.recv x r)
        (show Config from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config from { proc := .commMerge q s, pending := pending, handled := handled })
        (show Action from Action.rcfg x r)
        (show Config from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_recv
      (x : Channel) (p : DyNetKAT.NetKAT.NetKAT)
      (continuation : DyNetKAT)
      (pending handled : List CtxPkt) :
      Step env
        (show Config from
          { proc := .recv x p continuation, pending := pending, handled := handled })
        (show Action from Action.recv x p)
        (show Config from
          { proc := continuation, pending := pending, handled := handled })

  | cpol_send
      (x : Channel) (p : DyNetKAT.NetKAT.NetKAT)
      (continuation : DyNetKAT)
      (pending handled : List CtxPkt) :
      Step env
        (show Config from
          { proc := .send x p continuation, pending := pending, handled := handled })
        (show Action from Action.send x p)
        (show Config from
          { proc := continuation, pending := pending, handled := handled })

  | cpol_rcfg
      (x : Channel) (n : DyNetKAT.NetKAT.NetKAT)
      (continuation : DyNetKAT)
      (pending handled : List CtxPkt) :
      Step env
        (show Config from
          { proc := .rcfgPrefix x n continuation, pending := pending, handled := handled })
        (show Action from Action.rcfg x n)
        (show Config from
          { proc := continuation, pending := pending, handled := handled })

  | cpol_var
      (name : Var) (body body' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (definition : env.lookup name = some body)
      (step : Step env
        (show Config from { proc := body, pending := pending, handled := handled })
        action
        (show Config from { proc := body', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .var name, pending := pending, handled := handled })
        action
        (show Config from { proc := body', pending := pending', handled := handled' })

  | cpol_sync_recv_send
      (x : Channel) (r : DyNetKAT.NetKAT.NetKAT)
      (q s q' s' : DyNetKAT)
      (pending : List CtxPkt)
      (handled : List CtxPkt)
      (recv_step : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        (show Action from Action.recv x r)
        (show Config from { proc := q', pending := pending, handled := handled }))
      (send_step : Step env
        (show Config from { proc := s, pending := pending, handled := handled })
        (show Action from Action.send x r)
        (show Config from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config from { proc := .parallel q s, pending := pending, handled := handled })
        (show Action from Action.rcfg x r)
        (show Config from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_sync_send_recv
      (x : Channel) (r : DyNetKAT.NetKAT.NetKAT)
      (q s q' s' : DyNetKAT)
      (pending : List CtxPkt)
      (handled : List CtxPkt)
      (send_step : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        (show Action from Action.send x r)
        (show Config from { proc := q', pending := pending, handled := handled }))
      (recv_step : Step env
        (show Config from { proc := s, pending := pending, handled := handled })
        (show Action from Action.recv x r)
        (show Config from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config from { proc := .parallel q s, pending := pending, handled := handled })
        (show Action from Action.rcfg x r)
        (show Config from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_project
      (n : Nat)
      (p p' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (step : Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config from
          { proc := .project (n + 1) p, pending := pending, handled := handled })
        action
        (show Config from
          { proc := .project n p', pending := pending', handled := handled' })

  | cpol_restrict
      (actions : Set CommunicationAction)
      (p p' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (allowed : match action with
        | .packet _ _ => True
        | .recv x r => CommunicationAction.recv x r ∉ actions
        | .send x r => CommunicationAction.send x r ∉ actions
        | .rcfg _ _ => True)
      (step : Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .restrict actions p, pending := pending, handled := handled })
        action
        (show Config from
          { proc := .restrict actions p', pending := pending', handled := handled' })
```

## Verbatim declarations: bisimulation and recursion environment

`IsBisimulation` and `Bisimilar` are quoted verbatim in [SOS_AND_BISIMULATION_AUDIT.md](</Users/ali/Desktop/DyNetKAT-Lean/docs/SOS_AND_BISIMULATION_AUDIT.md>) and are located at `Bisimulation.lean:9-27`.

Verbatim recursion environment declarations, `DyNetKAT/RecEnv.lean:9-19`:

```lean
abbrev RecEnv : Type := Var → Option DyNetKAT

/-- Look up the defining body for a recursive variable. -/
def RecEnv.lookup (env : RecEnv) (name : Var) : Option DyNetKAT := env name

/-- The environment with no recursive definitions. -/
def RecEnv.empty : RecEnv := fun _ => none

/-- Add the unique definition for `name`, replacing any previous entry. -/
def RecEnv.define (env : RecEnv) (name : Var) (body : DyNetKAT) : RecEnv :=
  fun candidate => if candidate = name then some body else env candidate
```

Verbatim bisimulation definitions, `DyNetKAT/Bisimulation.lean:9-27`:

```lean
/-- A symmetric process relation that matches labeled transitions while
    preserving both packet histories. -/
def IsBisimulation (env : RecEnv) (R : DyNetKAT → DyNetKAT → Prop) : Prop :=
  (∀ p q, R p q → R q p) ∧
  ∀ p q, R p q →
    ∀ (pending handled : List CtxPkt) (action : Action)
      (p' : DyNetKAT) (pending' handled' : List CtxPkt),
      Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' }) →
      ∃ q',
        Step env
          (show Config from { proc := q, pending := pending, handled := handled })
          action
          (show Config from { proc := q', pending := pending', handled := handled' }) ∧
        R p' q'

/-- Two processes are bisimilar when some bisimulation relates them. -/
def Bisimilar (env : RecEnv) (p q : DyNetKAT) : Prop :=
  ∃ R, IsBisimulation env R ∧ R p q
```

The core congruence theorem statements, all fully proved, include:

| Lean theorem | Source lines |
|---|---:|
| `Bisimilar.choice_left`, `Bisimilar.choice_right` | `Bisimulation.lean:68`, `:109` |
| `Bisimilar.parallel_right`, `Bisimilar.parallel_left` | `:150`, `:214` |
| `Bisimilar.leftMerge_left`, `Bisimilar.leftMerge_right` | `:278`, `:314` |
| `Bisimilar.commMerge_right`, `Bisimilar.commMerge_left` | `:345`, `:393` |
| `Bisimilar.nSeq_left`, `Bisimilar.recv_left`, `Bisimilar.send_left`, `Bisimilar.rcfgPrefix_left` | `:441`, `:472`, `:503`, `:534` |
| `Bisimilar.restrict`, `Bisimilar.project` | `:565`, `:617` |

The complete declarations, including proof terms, are in [Bisimulation.lean](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Bisimulation.lean) at the exact starting lines above. The signatures in the inventory are verbatim declaration statements but intentionally omit the proof bodies; no proof body is reconstructed here. The relation’s universal transition quantification and the congruence proofs are substantial (the source module is 692 lines), so the source link is the authoritative complete verbatim text.

## Verbatim executable bridge declarations

`execute_packet_step` is quoted verbatim in [SOS_AND_BISIMULATION_AUDIT.md](</Users/ali/Desktop/DyNetKAT-Lean/docs/SOS_AND_BISIMULATION_AUDIT.md>) at source lines `NetKATBridge.lean:24-40`. `packetTransitions_sound` and `packetTransitions_complete` are quoted above with their complete proof bodies at `Executable.lean:57-119`. The executable enumeration itself is:

```lean
def packetTransitions
    (p : NetKAT) (continuation : DyNetKAT)
    (pending handled : List CtxPkt) :
    Option (Multiset (Action × Config)) :=
  match pending with
  | [] => some (∅ : Multiset (Action × Config))
  | sigma :: pendingTail =>
      match execute p sigma with
      | .unsupported => none
      | .supported outputs =>
          some (outputs.1.map (fun tau =>
            (Action.packet sigma tau,
              { proc := continuation
                pending := pendingTail
                handled := tau :: handled })))
```

The full `execute_correct` theorem is quoted verbatim in this report at lines 41-111. It establishes exact evaluator/relational-semantics agreement. The packet-transition theorems establish exact enumeration only for the `nSeq` source fragment. These are not the paper’s soundness or ground-completeness results.

## Recursion and guardedness status

`RecEnv := Var → Option DyNetKAT` gives partial mappings. `cpol_var` requires successful lookup, then delegates to a body step. This is a reasonable explicit semantics for paper recursive equations, but it leaves global assumptions as predicates. `Definedness.lean` defines direct/reachable definedness and a guarded-body predicate. Its `GuardedOccurrences` regards all occurrences beneath `nSeq`, communication prefixes, and reconfiguration prefix as guarded without checking the paper’s conditional clause for the prefix subterm. Therefore label it a **candidate structural guardedness condition**, not a verified faithful encoding of Definition 7.

No proofs establish recursive productivity, finitely branching behavior for all guarded processes, AIP soundness, or the paper’s normalization argument. The helper theorem `WellFormed.body` shows closure of the stated well-formedness condition under following a definition; it is not an AIP result.

## Final claim boundary

The strongest defensible presentation claims are:

- The NetKAT relational semantics and evaluator are formalized, with a proof that execution returns exactly the relational output set for every policy in the represented finite-domain language.
- The DyNetKAT SOS relation and environment-relative bisimulation are formalized; reflexivity, symmetry, transitivity, and many constructor-level congruence results are proved.
- Executable packet transition enumeration is proved sound and complete for the `nSeq` packet-processing rule.
- Paper Proposition 1 and Theorem 1, Figure 11 axiom derivability, Lemmas 5 and 8–11, and a faithful guardedness equivalence are not established by the current Lean repository.
