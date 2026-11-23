# H6A - Environment-Free Bisimulation Architecture Audit

Audit and architecture only. No Lean source, AST, `Step`, `RecEnv`, or existing report was
modified. The only artifact added by this task is this file.

**Sources verified directly:**

- **[L]** Lean working tree on branch `history-semantics` (files read in full: `Bisimulation.lean`,
  `Semantics.lean`, `RecEnv.lean`, `Definedness.lean`, `AST.lean`, `Config.lean`, `Action.lean`,
  `NetKATBridge.lean`, `Executable.lean`, `SafetyHead.lean`; declarations indexed in
  `HistorySemantics.lean`, `HistoryEvaluator.lean`, `History.lean`, `Decision.lean`).
- **[P]** `DyNetKAT.pdf` (repo root, arXiv:2102.10035v4), extracted with `pdftotext -layout`.
  Anchors are by equation/definition/figure number as printed; the FoSSaCS PDF has no stable
  page numbering for some anchors (cf. `SAFETY_WORKFLOW_AUDIT.md` §7.4).
- **[R]** architectural recommendation (this task's own analysis).
- **[O]** unproved mathematical obligation.

Label discipline: **[P]** = paper-verified, **[L]** = Lean-verified, **[R]** = recommendation,
**[O]** = open obligation. Nothing below is claimed as proved unless marked **[L]** with a
theorem name that exists in the tree.

---

## 1. Every environment dependency found (Task A)

### 1.1 The three distinct roles of "environment"

The task's central distinction is confirmed by the source. There are three different things
that `RecEnv` does, and they must not be conflated:

1. **Interpreting recursive specifications** - `RecEnv := Var → Option DyNetKAT`
   (`RecEnv.lean:9`) is the mathematical object that gives `.var X` meaning. **[L]**
2. **Executing SOS transitions** - `Step env` (`DyNetKAT/Semantics.lean:14`) carries `env` as
   an index, but exactly one of its 14 constructors consumes it: `cpol_var`
   (`Semantics.lean:159-170`), via the premise `definition : env.lookup name = some body`.
   **[L]**
3. **Comparing two already-resolved processes** - `IsBisimulation env R` / `Bisimilar env p q`
   (`Bisimulation.lean:9,26`) inherit `env` solely because they quantify over `Step env`
   transitions. **[L]**

Roles 2 and 3 are *inherited*; only role 1 is intrinsic to `RecEnv` as a definition.

### 1.2 Occurrence inventory (library code; `lean/test_*.lean` excluded)

| # | Location | Occurrence | Role | Required by the math? | Eliminable after preprocessing? |
|---|---|---|---|---|---|
| 1 | `RecEnv.lean:9-19` | `RecEnv`, `lookup`, `empty`, `define` + 3 simp lemmas | 1 | Yes - the `(cpolX)` rule needs the defining equation `X ≜ p` **[P]** (Fig. 8 premise annotation) | No - this *is* the interpretation mechanism |
| 2 | `DyNetKAT/Semantics.lean:14` | `Step (env : RecEnv)` index | 2 | Only for `cpol_var`; the other 13 constructors never mention `env` **[L]** | Yes, for variable-free processes (needs §3.3 lemma) |
| 3 | `DyNetKAT/Semantics.lean:159-170` | `cpol_var` premise `env.lookup name = some body` | 1+2 | Yes - this is the Lean rendering of the paper's `X ≜ p` side condition **[P]** | Only by removing `.var` from the process (preprocessing) |
| 4 | `Bisimulation.lean:9` | `IsBisimulation env R` | 3 | No - inherited from `Step env`; the paper's Definition 2 is environment-free (context suppressed) **[P]** | Yes for variable-free `p`, `q` (§3.3) |
| 5 | `Bisimulation.lean:26` | `Bisimilar env p q` | 3 | Same as 4 | Same as 4 |
| 6 | `Bisimulation.lean:29-690` | `env` parameter of `refl/symm/trans` + all 14 congruence theorems | 3 | No - **verified [L]: no proof body in `Bisimulation.lean` mentions `cpol_var` or `env.lookup`**; every `env` is threaded opaquely | Yes - statements generalize over `env`; for variable-free processes `env` can be dropped |
| 7 | `Definedness.lean:22,27,35,140` | `Defined env`, `ReachableVar env`, `ClosedDefined env`, `WellFormed env` | 1 | Yes - these are preprocessing/well-formedness predicates about which variables are defined and guarded **[L]** | No - they are preprocessing, not bisimulation; they should stay environment-relative |
| 8 | `NetKATBridge.lean:50,76` | `execute_packet_step env`, `executeHistory_packet_step env` | 2 (inert) | No - `env` appears only in the conclusion's `Step env`; proofs never use it **[L]** | Yes (cosmetic; would require touching `Step`'s type - out of scope) |
| 9 | `Executable.lean:64,97` | `packetTransitions_sound env`, `packetTransitions_complete env` | 2 (inert) | No - the `nSeq` packet fragment cannot reach `cpol_var` **[L]** (a `Step` from `.nSeq …` can only be `cpol_seq_ok`) | Yes, same caveat as 8 |

### 1.3 Why the environment is mathematically necessary at role 1

**[P]** The paper's `(cpolX)` rule (Figure 8) is rendered with the defining equation as a
premise annotation: from `(p, H0, H1) →γ (p0, H00, H10)` and the side condition `X ≜ p`, infer
`(X, H0, H1) →γ (p0, H00, H10)`. The same syntax `.var "X"` has different transitions under
different definitions, so environment-relative semantics is not a Lean artifact - it is the
paper's semantics with the global specification made explicit. `Step.cpol_var` unfolds one step
by delegation to the body; it does not itself assert existence, uniqueness, guardedness, or
productivity (those live in `WellFormed`, `Definedness.lean:140-143`). **[L]**

### 1.4 Why the environment is *not* needed at role 3 for resolved processes

**[L]** Verified structural facts that make elimination provable:

- A `Step env` derivation whose source process contains no `.var` constructor cannot use
  `cpol_var` (its source is `.var name` by the constructor's shape).
- Variable-freeness is preserved along steps: every residual produced by every constructor is
  either a structural subterm of the source (`choice`, `parallel`, `leftMerge`, `commMerge`
  components; `nSeq`/`recv`/`send`/`rcfgPrefix` continuations) or a wrapped residual
  (`.restrict actions p'`, `.project n p'`). No rule introduces a variable except `cpol_var`,
  which is unreachable from a variable-free source.
- Hence `Step env₁` and `Step env₂` coincide on configurations with variable-free `proc`, and
  consequently `Bisimilar env₁ p q ↔ Bisimilar env₂ p q` whenever `p`, `q` are variable-free.
  In particular `Bisimilar env p q ↔ Bisimilar RecEnv.empty p q`.

**[R]** This is exactly the authors' point: once projection and restriction (plus bounded
unfolding) have removed variables, the bisimulation argument needs no environment. The
elimination is *provable*, not merely stylistic; the required lemma is stated in §8
(`Step.env_irrelevant_on_varFree`).

### 1.5 What must *not* be removed

- `RecEnv` itself and `cpol_var`: they are the reference semantics for recursive
  specifications. **[R]** (also mandated by the task constraints).
- `WellFormed`/`ReachableVar`/`ClosedDefined`: preprocessing predicates; they are
  environment-relative by nature. **[R]**

---

## 2. Paper definitions of projection and restriction (Task B, paper side)

All quoted/paraphrased content below was verified against the extracted PDF text. **[P]**

### 2.1 Restriction `δL(−)`

**Operational rule (Eq. (2), §III):**

```
(p, H0, H1) →γ (p0, H00, H10)     γ ∉ L
─────────────────────────────────────      (δ)
(δL(p), H0, H1) →γ (δL(p0), H00, H10)
```

`L` is a set of forbidden actions ranging over `x?z` and `x!z` (the communication actions of
Eq. (1)). The paper: "In practice, we use the restriction operator to force synchronous
communication." Restriction is what makes the `head`/`tail` precondition hold - §V: "we assume
the input D to the operators head and tail do not contain terms of shape x?z and x!z. This can
be ensured by always applying the restriction operator δ on D."

**Axioms (Figure 11):** (δ⊥) `δL(⊥) ≡ ⊥`; (δ;) `δL(at;p) ≡ at;δL(p)` if `at ∉ L`;
(δ;⊥) `δL(at;p) ≡ ⊥` if `at ∈ L`; (δ⊕) `δL(p⊕q) ≡ δL(p) ⊕ δL(q)`.

### 2.2 Projection `πn(−)`

**Operational rule (Eq. (3), §III):** "In the style of [3], we define a projection operator
πn(−) that, intuitively, captures the first n steps of a DyNetKAT policy."

```
(p, H0, H1) →γ (p0, H00, H10)
─────────────────────────────────────      (π)
(πn+1(p), H0, H1) →γ (πn(p0), H00, H10)
```

**Axioms (Figure 11):** (Π0) `π0(p) ≡ ⊥`; (Π⊥) `πn(⊥) ≡ ⊥`; (Π;) `πn+1(at;p) ≡ at;πn(p)`;
(Π⊕) `πn(p⊕q) ≡ πn(p) ⊕ πn(q)`.

**Role:** "πn(−) is crucial for defining the so-called 'Approximation Induction Principle'"
(Figure 11):

```
p ≡ q  if  ∀n ∈ ℕ : πn(p) ≡ πn(q)           (AIP)
```

**AIP soundness (Lemma 11, Proof 6):** assumes `∀n, πn(p) ≡ πn(p0)`, uses Lemma 10 to get
`∀n, πn(p) ∼ πn(p0)`, then builds `R = {(t,t') | ∀n, πn(t) ∼ πn(t')}` (Eq. 22) and proves `R`
is a bisimulation via the decreasing sequence `S1 ⊇ S2 ⊇ …` of one-step-derivative sets
(Eq. 24). The three ingredients, verbatim: (1) monotone decrease "as if πn+1(p) ∼ πn+1(p0)
then πn(p1) ∼ πn(p01)"; (2) nonemptiness "since πn+1(p) ∼ πn+1(p0) by (21)"; (3) "Sn is finite,
for all n ∈ ℕ, as p0 is finitely branching according to Lemma 8". Finiteness comes from
finite branching of the *one-step* derivatives only - the sets range over single-step
derivatives of `p0` with fixed histories `(H0, H00)`, so Lemma 8 alone suffices; no global
reachable-state finiteness is used. The proof is "close to the one of Theorem 2.5.8 in [3]"
(Bergstra–Klop-style).

### 2.3 Guardedness and recursion (Definition 7, Lemma 8)

**[P]** Definition 7: "A DyNetKAT policy p is guarded if and only if all occurrences of all
variables X in p are guarded. An occurrence of a variable X in a policy p is guarded if and
only if (i) p has a subterm of shape p0;t such that either p0 is variable-free, or all the
occurrences of variables Y in p0 are guarded, and X occurs in t, or (ii) if p is of shape
y?X;t, y!X;t or rcfgX,t." Lemma 8: "All guarded DyNetKAT policies are finitely branching."
The paper then assumes guardedness globally ("For simplicity, in what follows, we assume that
DyNetKAT policies are guarded").

**[P]** There is **no** graph, cycle, fixpoint, or "resolution" mechanism anywhere in the
paper: a full-text search for graph/cycle/fixpoint/fixed-point/cyclic returns nothing. The
paper's recursion machinery is exactly: `(cpolX)` (operational unfolding), `πn` (bounded
observation), `AIP` (equational lifting), Lemma 8/9/10/11, Theorem 1. The bounded character
of the implemented procedure is acknowledged by the paper itself (§IV): "for a fixed n, the
verification procedure resembles bounded model checking."

---

## 3. Lean counterparts and the variable-resolution question (Task B, Lean side)

### 3.1 Restriction in Lean

**[L]** `Step.cpol_restrict` (`DyNetKAT/Semantics.lean:223-240`) matches Eq. (2) exactly:
a step of the inner process with `allowed : match action with | .packet _ _ => True |
.recv x r => CommunicationAction.recv x r ∉ actions | .send x r => … ∉ actions | .rcfg _ _ =>
True`, residual `.restrict actions p'`. Packet and `rcfg` actions always pass; only
communication actions can be forbidden - matching the paper's `L ⊆ {x?z, x!z}` by
construction (`AST.lean:66-71`). Congruence: `Bisimilar.restrict` (`Bisimulation.lean:565`).

### 3.2 Projection in Lean

**[L]** `Step.cpol_project` (`DyNetKAT/Semantics.lean:208-221`) matches Eq. (3): `.project
(n+1) p` steps to `.project n p'`. The `n = 0` case has no rule, and `Bisimilar.project`
(`Bisimulation.lean:617-637`) proves `.project 0 p` affords **no** transitions (`cases step`
closes all goals) - the behavioral counterpart of (Π0) `π0(p) ≡ ⊥`. Congruence for `n+1` is
proved with the depth-tracking relation `∃ k c d, k ≤ n+1 ∧ R c d ∧ a = .project k c ∧ …`.

### 3.3 Do they resolve recursive variables? - the critical question

**Answer: No - neither operator, as defined in the paper or in Lean, removes recursive
variables; and the naive preprocessing theorem cannot hold.** Detail:

1. **Restriction never touches variables.** **[P]** The δ rules and axioms only cut
   communication prefixes; no rule mentions `X`. **[L]** `cpol_restrict` delegates to a step
   of the inner process; `.restrict L (.var X)` steps only via `cpol_var` (requiring
   `env.lookup`), and the residual remains `.restrict L body'`. Syntactically, a term under
   `restrict` can still contain `.var`. `recursiveVars (.restrict _ p) = recursiveVars p`
   (`Definedness.lean:16`). **[L]**
2. **Projection (paper SOS reading) does not unfold at the term level.** **[P]** In Eq. (3),
   `πn+1(p)` is an *operator wrapping* `p`; a step of `πn+1(X)` goes through `cpolX` first
   (which needs the defining equation) and lands in `πn(p0)` where `p0` is a body derivative.
   The variable is consumed *by the transition*, not by a term-level rewrite. `π1(X)` is
   still a term containing `X`. The projection budget decrements per **transition**; `cpolX`
   adds no transition of its own.
3. **Projection (tool reading) resolves variables by bounded truncation.** **[V]** (carried
   over from `SAFETY_WORKFLOW_AUDIT.md` §2, re-verified against the paper's §IV–V text): the
   Maude implementation forces unfolding while the `pi` budget remains and cuts with
   `pi{0}(P) = bot`, so after `pi_n` no variable survives - but the result is an
   **under-approximation of depth > n behavior, not a fixpoint resolution**. The paper's own
   caveat: "for a fixed n, the verification procedure resembles bounded model checking." **[P]**
4. **The literal theorem cannot hold.** A statement of the form

   ```lean
   theorem preprocessing_resolves_variables (env : RecEnv) (process : DyNetKAT) :
       NoReachableVariables (preprocess env process)
   ```

   with `preprocess` total on all `env` and producing a *finite variable-free term that is
   behaviorally exact* is **false**, for two independent reasons:

   a. **No finite variable-free term represents unbounded behavior.** For the guarded
      specification `X ≜ id;X` (guarded under Definition 7: the occurrence of `X` sits under
      `id;`), the process affords an unbounded sequence of packet transitions; no finite
      `DyNetKAT` term without `.var` is bisimilar to it. So if `preprocess` is required to be
      exact, its codomain cannot be finite variable-free terms.
   b. **Eager unfolding is not total on arbitrary `env`.** `X ≜ X` makes any unfolding
      function that recurses `unfold (var X) = unfold body` diverge. (The tool avoids this by
      *lazy* unfolding - unfold only when a step is blocked - so `X ≜ X` simply gets stuck,
      matching `cpol_var`'s infinite-regress semantics.) **[V]** tool behavior per
      `SAFETY_WORKFLOW_AUDIT.md` §2; **[L]** `cpol_var` requires a step *of the body*, so
      `X ≜ X` affords no transition.

5. **What the exact correct statements are.** Two shapes, one per architecture track:

   **Bounded (term-level, tool-faithful).** With a *separate* unfolding fuel `k` in addition
   to the projection depth `n` (fuel is needed precisely because unfolding does not consume
   projection budget, cf. 2.2/3.3-2):

   ```lean
   def boundedUnfold (env : RecEnv) : Nat → Nat → DyNetKAT → DyNetKAT
       -- projection depth, unfolding fuel, process

   theorem boundedUnfold_var_free (env : RecEnv) (depth fuel : Nat) (p : DyNetKAT) :
       recursiveVars (boundedUnfold env depth fuel p) = ∅            -- [O] provable by construction

   theorem boundedUnfold_sound                                       -- [O]
       (env : RecEnv) (wf : WellFormed env p) (depth : Nat)
       (fuel_ok : fuel ≥ depth + 1) :
       -- every Step env transition sequence of length ≤ depth from p is matched by
       -- boundedUnfold env depth fuel p, and conversely (trace equivalence up to depth)
   ```

   The fuel bound `fuel ≥ depth + 1` is justified **[O]** by the observation above: under
   `GuardedOccurrences` bodies, every variable occurrence sits directly under a prefix
   (`GuardedOccurrences (.var _) = False`, `Definedness.lean:102`), so every observed
   transition crosses at least one prefix, hence #unfoldings ≤ #transitions + 1 ≤ depth + 1.
   **This is a bounded approximation theorem, not unbounded bisimilarity** - the distinction
   the task explicitly demands.

   **Exact (graph-level).** Variables are not eliminated from the representation; they become
   edges. The correct "resolution" statement is graph well-formedness, not term-level
   variable-freeness (§4).

### 3.4 Summary table for Task B

| Question | Restriction δL | Projection πn |
|---|---|---|
| Unfolds recursive variables (paper) | No **[P]** | Only *through* transitions, via `cpolX`; no term-level unfolding **[P]** |
| Unfolds recursive variables (Lean) | No **[L]** (`cpol_restrict` delegates; `.var` preserved syntactically) | No **[L]** (`cpol_project` wraps; `.var` reachable only via `cpol_var`) |
| Removes all reachable `.var` occurrences | No **[L]** | No (paper SOS); yes in the *tool's* bounded-truncation reading **[V]** |
| Result finite | Input-shaped **[L]** | Bounded-depth term under tool reading **[V]** |
| Preserves intended operational behavior | Yes - Eq. (2) verbatim **[P]/[L]** | Yes for Eq. (3) as an operator **[P]/[L]**; tool's πn is an under-approximation **[V]** |
| Depends on `RecEnv` | Only transitively via `Step env` **[L]** | Same **[L]** |
| Variables possible after both | Yes **[L]** | Yes (paper SOS); No (tool truncation, at the price of depth-n under-approximation) **[V]** |

---

## 4. Cyclic graph representation (Task C)

**[P]** Grounding: the paper does not propose a graph representation; the authors' guidance
("represent infinitely unfolding recursive specifications through cycles in a finite graph")
is extra-paper architectural advice. The design below is therefore **[R]**, constrained to be
faithful to the paper's `(cpolX)`/Lemma 7/8/AIP machinery.

### 4.1 Design

```lean
/-- Node identifiers into a finite graph. `Nat` + a `Finset` of live nodes avoids any
    graph library; well-formedness ties labels to the node set. -/
abbrev NodeId : Type := Nat

/-- The constructor skeleton stored at each node. Recursive variables become
    *references* (back-edges), not names to be looked up. -/
inductive NodeLabel : Type
  | deadlock                                              -- ⊥
  | nSeq       : NetKAT → NodeId → NodeLabel              -- N; D      (successor)
  | recv       : Channel → NetKAT → NodeId → NodeLabel    -- x?N; D
  | send       : Channel → NetKAT → NodeId → NodeLabel    -- x!N; D
  | rcfgPrefix : Channel → NetKAT → NodeId → NodeLabel    -- rcfg_{x,N}; D
  | parallel   : NodeId → NodeId → NodeLabel              -- D ‖ D
  | choice     : NodeId → NodeId → NodeLabel              -- D ⊕ D
  | leftMerge  : NodeId → NodeId → NodeLabel              -- D ⌊⌊ D
  | commMerge  : NodeId → NodeId → NodeLabel              -- D | D
  | restrict   : Set CommunicationAction → NodeId → NodeLabel
  | var        : NodeId → NodeLabel                       -- X ≜ (body at successor node)

structure ProcessGraph where
  nodes : Finset NodeId
  label : NodeId → NodeLabel
  root  : NodeId
  root_live : root ∈ nodes
  closed : ∀ i ∈ nodes, children (label i) ⊆ nodes   -- children : NodeLabel → List NodeId
```

Design decisions and why:

- **`var` carries a `NodeId`, not a `Var`.** This is the whole point: the environment lookup
  is performed *once, at graph-construction time*; the graph needs no `RecEnv`. A cycle
  `X → N;Y`, `Y → M;X` is two nodes with labels `nSeq N (var y)` and `nSeq M (var x)` - the
  back-edges make the infinite unfolding finite. **[R]**
- **`Finset NodeId` + `closed` predicate instead of a graph library.** Totality of every
  successor is an explicit invariant; reachability and cycle checks are finite explorations
  over `nodes`. Mathlib is not needed beyond `Finset`. **[R]**
- **Guardedness becomes a graph property.** Paper Definition 7 says an occurrence of `X` is
  guarded iff it lies under a prefix (`p0;t` with the variable in `t`, or `y?X;t`, `y!X;t`,
  `rcfgX;t`). On the graph this is: **every `var`-edge target is reachable from the source
  only through at least one prefix node** - equivalently, no cycle in the graph consists
  solely of `var` edges (a `var` node whose body node is again immediately a `var` reference
  is the graph image of an unguarded chain `X ≜ Y`). Formally checkable by finite exploration:
  ```lean
  def GraphGuarded (g : ProcessGraph) : Prop :=
    ∀ i ∈ g.nodes, match g.label i with
      | .var j => prefixImmediate g j   -- j's label is a prefix constructor, or j is guarded inductively
      | _ => True
  ```
  **[O]** proving `GraphGuarded g` equivalent to the paper's per-occurrence Definition 7 on
  the unfoldings is a genuine obligation (see §9); note the current Lean `GuardedOccurrences`
  (`Definedness.lean:90-102`) is a *coarser* structural approximation - it declares every
  occurrence under `nSeq`/`recv`/`send`/`rcfgPrefix` guarded without the paper's conditional
  clause on the prefix subterm `p0` (flagged already in `PAPER_TO_LEAN_MATRIX.md`).
- **Successors/reachability/exploration.** `children : NodeLabel → List NodeId`; reachability
  is the reflexive-transitive closure of the child relation restricted to `nodes`; because
  `nodes` is a `Finset`, the standard worklist/`Finset.image` iteration stabilizes within
  `nodes.card` steps, giving a *decidable*, total exploration - no coinduction needed for
  the graph checks themselves. **[R]**

### 4.2 Converting `RecEnv` into this representation

**[R]** Yes, under well-formedness assumptions. Construction: collect the recursively
reachable variables of the root (`ReachableVar env root name`, `Definedness.lean:27-32`) -
under `WellFormed env root` these are all defined; allocate one node per reachable variable,
one node per distinct body subterm position (hash-consing optional; a naive tree-unrolling
with a fuel on *distinct syntax nodes* also works), and translate `.var name` to
`.var (nodeOf name)`. Termination of the construction needs the same care as §3.3-5 (a
variable's body is unrolled with a fuel; under guardedness each unfolding is followed by a
prefix, so a fuel of `depth+1` per observation level suffices) - or, more cleanly, the graph
is built *directly* from the equations without unrolling: each variable gets exactly one node
whose label is its body with `.var Y` replaced by `.var (nodeOf Y)`; bodies are finite terms,
so this is a single structural pass over finitely many bodies, **total on any `WellFormed`
environment** - no fuel needed. This direct construction is the recommended one. **[R]**

```lean
def toGraph (env : RecEnv) (root : DyNetKAT)
    (wf : WellFormed env root) (reachable : Finset Var) : ProcessGraph   -- [O] construction + well-formedness proof
```

### 4.3 Graph transitions

Mirror `Step` with the process component replaced by a node index; the `var` case needs no
environment because the reference *is* the resolution:

```lean
inductive GStep (g : ProcessGraph) : GConfig → Action → GConfig → Prop where
  | seq_ok  (i : NodeId) (N : NetKAT) (j : NodeId) (σ σ' : CtxPkt) (pt hl : List CtxPkt)
      (lab : g.label i = .nSeq N j)
      (evaluates : HistorySemantics N (History.singleton σ) (History.singleton σ')) :
      GStep g ⟨i, σ :: pt, hl⟩ (Action.packet σ σ') ⟨j, pt, σ' :: hl⟩
  | var     (i j : NodeId) (a : Action) (pt pt' hl hl' : List CtxPkt)
      (lab : g.label i = .var j)
      (step : GStep g ⟨j, pt, hl⟩ a ⟨j', pt', hl'⟩) :
      GStep g ⟨i, pt, hl⟩ a ⟨j', pt', hl'⟩
  -- … one constructor per remaining Step constructor, with `lab : g.label i = …` side conditions
```

(`GConfig` = node + pending + handled; packet/comm/rcfg/choice/parallel/merge/restrict/
project rules are structural clones of `Semantics.lean` with node indices.) **[R]**

---

## 5. Finite-depth cutoff and unbounded correctness (Task D)

The four notions, kept strictly apart:

1. **Bounded bisimulation** - `πn(p) ∼ πn(q)` for one fixed `n`. **[P]** Does *not* imply
   `p ∼ q`: differences beyond depth `n` are invisible. The paper itself frames fixed-`n`
   checking as bounded-model-checking-like (§IV). Any checker verdict at a user-supplied `n`
   is sound only for traces of length ≤ n unless a stabilization argument is added.
2. **Bisimulation on a finite cyclic graph** - ordinary LTS bisimulation over the graph
   semantics of §4.3. Because the coinductive definition unrolls cycles without bound, this
   is **genuine unbounded bisimulation of the graph LTS**, and it is *decidable* in principle
   (finite branching + finite node space ⇒ partition refinement terminates). No cutoff, no
   AIP needed. **[R]**
3. **Unbounded bisimulation of the original `Step env` LTS** - equals (2) *given* a
   correspondence theorem between graph transitions and `Step env` transitions (§8, `GStep`
   correspondence). Without that theorem, (2) is a statement about a different LTS.
4. **Stabilization of finite-depth approximations** - the existence of `n0` with
   `πn(p) ∼ πn(q)` for all `n ≥ n0` implying `p ∼ q` is exactly **AIP soundness (Lemma 11)**,
   whose proof (Proof 6) is a decreasing-sequence argument over one-step derivative sets,
   needing Lemma 8 (finite branching). **[P]** For a *checker* that wants to compute a
   cutoff, a stronger, algorithmic stabilization is needed: the reachable process space up
   to bisimilarity must be finite so that `πn` behavior provably repeats. **[O]** This is the
   open obligation already recorded in `SAFETY_WORKFLOW_AUDIT.md` §7.1; the graph
   representation is precisely the structure that makes such an argument *stateable* (finitely
   many nodes; configurations still range over unbounded packet lists, so the stabilization
   must be argued per-history-context, as Proof 6 does - the bisimulation relation of
   `IsBisimulation` quantifies over all `pending`/`handled`, and nothing in the current tree
   bounds them). **[L]** on the quantifier structure of `IsBisimulation`.

**Necessary proof obligations for the graph route:**

- **(G1)** `ProcessGraph` well-formedness (`closed`, `root_live`) - construction lemma. **[O]**
- **(G2)** `GraphGuarded g` ⇒ the graph LTS is finitely branching (Lemma 8 analogue). On the
  graph this is *easier* than the paper's term-level Lemma 8: each node has finitely many
  structural successors and packet transitions are `Finset`-valued (`executeHistory` returns
  `Finset History`, `HistoryEvaluator.lean:58` **[L]**). **[O]**
- **(G3)** Correspondence: `GStep g` traces (or bisimilarity) coincide with `Step env` on the
  unfoldings - see §8 for the proposed statement. Trace-level suffices for the safety
  pipeline (the paper's safety semantics is explicitly trace-based and "not sensitive to
  branching", Definition 14 discussion **[P]**); bisimulation-level is the stronger stretch
  goal. **[O]**
- **(G4)** Stabilization/cutoff theorem for unbounded verdicts - open (§9).

**What must never be claimed:** that checking a fixed arbitrary depth `n` establishes
unbounded bisimulation. **[P]** The paper's only bridges from bounded to unbounded are AIP
(meta-principle, soundness proved via Lemma 8) and the guardedness assumption; the tool
implements neither as an algorithm. **[V]**

---

## 6. Recommended Lean architecture (Task E)

### 6.1 Alternatives compared

**Option 1 - keep `RecEnv` for preprocessing, eliminate it from bisimulation after
normalization.**
Pros: minimal change; all existing theorems (`refl/symm/trans`, 14 congruence results,
`packetTransitions_*`) survive untouched; the environment-irrelevance lemma (§3.3-4, §8) is
self-contained and provable now. Cons: "normalization" can only mean *bounded* unfolding at
term level (§3.3-4a: no finite variable-free term is exact for unbounded recursion), so this
option alone caps the artifact at bounded verdicts.

**Option 2 - convert recursive specifications to finite cyclic graphs; bisimulation directly
over graph nodes.**
Pros: the only option that handles unbounded recursion exactly; finite branching (G2) is
easy; bisimulation on the graph is decidable in principle and needs no `RecEnv`, no AIP;
matches the authors' guidance. Cons: new LTS + correspondence theorem (G3); does not by
itself serve the *bounded* pipeline that mirrors the tool.

**Option 3 - retain environment-dependent `Step`, add an environment-independent bisimulation
interface for "resolved processes".**
Cons: presupposes term-level resolved processes, which do not exist for unbounded recursion
(§3.3-4a). The interface is either bounded (collapses into Option 1) or graph-shaped
(collapses into Option 2). Not independently viable.

### 6.2 Recommendation: two-track hybrid of Options 1 + 2 **[R]**

- **Track A (term level, bounded, zero changes to existing files).** Keep `RecEnv`, `Step
  env`, `Bisimilar env` exactly as they are. Add, in *new* modules: a variable-freeness
  predicate, the environment-irrelevance lemma, an env-free bisimilarity interface for
  variable-free processes, and the fuel-based `boundedUnfold` with its var-freeness and
  bounded-soundness theorems. This serves the tool-faithful safety pipeline (head/tail on
  restricted, projected, variable-free terms) and justifies - *with proof* - dropping `env`
  from every bisimulation statement about preprocessed processes.
- **Track B (graph level, unbounded).** Add `ProcessGraph`/`GStep`/`GBisimilar` and the
  conversion + correspondence theorems. This is where unbounded claims live, and where the
  authors' cyclic-graph guidance is honored without pretending a bounded check is unbounded.

Track A is the prerequisite for the pipeline; Track B is the prerequisite for unbounded
verdicts. They share the `NetKAT` evaluator/decision layer and the `Step` correspondence
discipline already established by H5A.

### 6.3 Proposed Lean signatures (not implemented)

```lean
---------------------------------------------------------------- Track A
/-- Syntactic variable-freeness: no direct `.var` occurrence anywhere. -/
def VarFree (p : DyNetKAT) : Prop := recursiveVars p = ∅

/-- The environment is irrelevant for stepping variable-free processes. -/
theorem Step.env_irrelevant_on_varFree
    (env₁ env₂ : RecEnv) (cfg cfg' : Config) (a : Action)
    (hfree : VarFree cfg.proc) :
    Step env₁ cfg a cfg' ↔ Step env₂ cfg a cfg'                        -- [O] provable now

/-- Environment-free bisimilarity for resolved (variable-free) processes. -/
def BisimilarFree (p q : DyNetKAT) : Prop := Bisimilar RecEnv.empty p q

theorem bisimilarFree_iff_bisimilar (env : RecEnv) (p q : DyNetKAT)
    (hfree_p : VarFree p) (hfree_q : VarFree q) :
    BisimilarFree p q ↔ Bisimilar env p q                              -- [O]

/-- Tool-faithful bounded unfolding (fuel = number of variable unfoldings allowed). -/
def boundedUnfold (env : RecEnv) : Nat → Nat → DyNetKAT → DyNetKAT

theorem boundedUnfold_var_free (env : RecEnv) (depth fuel : Nat) (p : DyNetKAT) :
    VarFree (boundedUnfold env depth fuel p)                           -- [O]

theorem boundedUnfold_trace_sound (env : RecEnv) (p : DyNetKAT)
    (wf : WellFormed env p) (depth fuel : Nat) (hfuel : fuel ≥ depth + 1) :
    -- trace equivalence at depth `depth` between p and boundedUnfold env depth fuel p
    -- (statement to be fixed against the trace semantics used by the pipeline)     -- [O]

/-- Syntactic restriction and projection as AST functions, with soundness against the
    existing SOS constructors (paper δ/π axioms as rewriting). -/
def syntacticRestrict (L : Set CommunicationAction) (p : DyNetKAT) : DyNetKAT
def syntacticProject (n : Nat) (p : DyNetKAT) : DyNetKAT

theorem syntacticRestrict_sound (env : RecEnv) (L) (p) :
    Bisimilar env (.restrict L (syntacticRestrict L p)) (syntacticRestrict L p)   -- [O] shape
theorem syntacticProject_sound (env : RecEnv) (n : Nat) (p : DyNetKAT) :
    Bisimilar env (.project n (syntacticProject n p)) (syntacticProject n p)      -- [O] shape

---------------------------------------------------------------- Track B
/-- Graph construction from a well-formed environment (§4.2). -/
def toGraph (env : RecEnv) (root : DyNetKAT)
    (wf : WellFormed env root) : ProcessGraph                          -- [O]

/-- Graph LTS (§4.3) and graph bisimilarity. -/
inductive GStep (g : ProcessGraph) : GConfig → Action → GConfig → Prop
def IsBisimulationG (g : ProcessGraph) (R : GConfig → GConfig → Prop) : Prop
def GBisimilar (g : ProcessGraph) (c₁ c₂ : GConfig) : Prop :=
  ∃ R, IsBisimulationG g R ∧ R c₁ c₂

/-- Correspondence: depth-n unfoldings of graph nodes coincide with env-based unfoldings. -/
def unfoldNode (g : ProcessGraph) : Nat → NodeId → DyNetKAT            -- depth-bounded unfolding

theorem gstep_unfold_correspondence (g : ProcessGraph) (wf : WellFormed env root)
    (i : NodeId) (n : Nat) :
    -- GStep g from node i matches Step env from unfoldNode g n i, up to depth n
    -- (trace-level first; bisimulation-level as stretch goal)                     -- [O]

/-- Unbounded transfer: graph bisimilarity ⇒ env bisimilarity, via AIP-shaped reasoning
    or directly via a coinductive relational invariant. -/
theorem gbisimilar_implies_bisimilar (…) : …                           -- [O] stretch goal
```

---

## 7. Relationship to the safety checker (Task F)

- **`head` (`SafetyHead.lean:74`, `head_spec` at `:323`).** **[L]** `head` returns `none` on
  `.var` (and on `restrict`/`project`/`parallel`/…); its documented precondition is the
  paper's restricted-input assumption (§V **[P]**). The pipeline must therefore hand `head` a
  *restricted, projected, variable-free* term. Track A's `boundedUnfold` + `syntacticRestrict`
  produce exactly that shape; Track B's graph would need a depth-bounded unfolding
  (`unfoldNode`) before `head` applies. The unfinished normal-form pipeline is blocked
  precisely on this preprocessing stage - not on `head` itself.
- **`netkatEquiv` / `netkatIsZero` (`Decision.lean:77,151`, correctness at `:124,157`).**
  **[L]** Fully proved, packet-level, finite-domain. They are the terminal decision procedures:
  consumed (i) during preprocessing (zero-elimination of NetKAT sub-terms of variable bodies,
  mirroring the tool's `equiv x zero` rewrite **[V]**) and (ii) at verdict time
  (`in · head(Init) · out ≡ 0`, Eqs. (34)-(35) **[P]**). No changes needed; the history-level
  bridge already exists (`historySemantics_singleton_iff_packetSemantics`,
  `NetKATBridge.lean:32` **[L]**).
- **E_NK (Figure 4 / Figure 11 `ENK` block).** **[P]** The two bottom equations -
  `KA-LFP-L`/`KA-LFP-R` (least-fixpoint axioms for `*`) and `PA-CONTRA`/`PA-MATCH-ALL`
  (finite-domain tie-in) - remain mandatory for the eventual equational framework. However,
  per `SAFETY_WORKFLOW_AUDIT.md` §3 **[V]**: the evaluator's `execute_star_correct` and the
  `Fintype CtxPkt` instances already realize their *semantic* content on the finite domain,
  and a semantic decision procedure suffices for the checker; an explicit `EDNK`/`E_NK`
  derivability relation is a separate proof-theory track, not a pipeline dependency. KATch is
  thereby avoidable: the needed functionality is `execute`/`netkatEquiv`/`netkatIsZero`,
  already in-tree and verified. **[L]**
- **Final safety condition.** **[P]** Definition 16 (Eq. 27): `EDNK^tr ⊢ ⟦s⟧ ⊕ i ≡ ⟦s⟧`,
  specialized to reachability/waypointing via `head`/`tail` (Eqs. (29)-(33), examples
  (34)-(35)). In Lean terms the end-to-end shape is: preprocess (δ, πn, unfold) → `head`/`tail`
  → build the reachability/waypointing NetKAT term → `netkatEquiv`/`netkatIsZero` → verdict.

**Component dependency order (next implementations, no KATch):**

1. `syntacticRestrict` + `syntacticProject` (AST → AST) with soundness vs
   `Step.cpol_restrict`/`cpol_project` - unblocks `head`'s precondition formally.
2. `tail` (paper Eqs. (33) + (29)-(32) companions; restricted input) - the missing twin of
   `head`.
3. `boundedUnfold` (Track A) with `boundedUnfold_var_free` + `Step.env_irrelevant_on_varFree`
   + `BisimilarFree` - resolves variables for the bounded pipeline and de-environments the
   bisimulation interface.
4. Verdict layer: property-term construction + `netkatEquiv`/`netkatIsZero` composition
   (thin; both decision procedures exist).
5. Track B graph layer (`toGraph`, `GStep`, correspondence) - parallel track, required only
   for unbounded claims; sequencing after (3) is natural but not strict.

---

## 8. Consolidated list of proposed theorems (for §6.3 quick reference)

| Theorem | Track | Status |
|---|---|---|
| `Step.env_irrelevant_on_varFree` | A | **[O]** provable from current definitions |
| `bisimilarFree_iff_bisimilar` | A | **[O]** follows from the above |
| `boundedUnfold_var_free` | A | **[O]** by construction |
| `boundedUnfold_trace_sound` (fuel ≥ depth+1, `WellFormed`) | A | **[O]** needs the guardedness counting argument (§3.3-5) |
| `syntacticRestrict_sound`, `syntacticProject_sound` | A | **[O]** paper δ/π axioms as rewrite rules |
| `toGraph` well-formedness | B | **[O]** single structural pass over bodies |
| `GraphGuarded` ↔ Definition 7 on unfoldings | B | **[O]** nontrivial; current `GuardedOccurrences` is coarser **[L]** |
| `gstep_unfold_correspondence` (trace level) | B | **[O]** |
| `gbisimilar_implies_bisimilar` | B | **[O]** stretch; may need an AIP formalization or a direct coinductive invariant |
| graph-LTS finite branching (`GraphGuarded` ⇒) | B | **[O]** easy relative to paper Lemma 8 |
| stabilization/cutoff for unbounded verdicts | B | **[O]** open (§9) |

---

## 9. Unresolved mathematical questions

1. **Unbounded verdicts / stabilization theorem.** No algorithm exists in the paper or the
   tool **[P][V]**. The graph representation makes the statement stateable (finitely many
   nodes), but configurations carry unbounded packet lists, and `IsBisimulation` quantifies
   over all of them **[L]**; a per-history-context argument (as in Proof 6) or a quotient
   argument is needed. Open.
2. **Faithful guardedness.** `GuardedOccurrences` is coarser than Definition 7 (no
   conditional check of the prefix subterm `p0`) **[L]**, and no equivalence to the paper's
   per-occurrence condition is proved. The graph-level `GraphGuarded` should be *defined* to
   match Definition 7 and then proved equivalent on unfoldings. Open.
3. **AIP in Lean.** Either formalize Lemma 11 at term level (requires a Lemma 8
   finite-branching theorem for `Step env`, currently missing **[L]** per
   `PAPER_TO_LEAN_MATRIX.md`) or circumvent it via Track B's direct graph bisimilarity. The
   choice affects whether `gbisimilar_implies_bisimilar` needs AIP. Open.
4. **Correspondence strength.** Trace-level correspondence (sufficient for the pipeline,
   since Definition 14's semantics is trace-based **[P]**) vs full bisimulation correspondence
   between `GStep` and `Step env`. Decide before implementing Track B. Open (design decision).
5. **Exact fuel accounting for `boundedUnfold`.** The claim "fuel = depth + 1 suffices under
   guardedness" rests on the counting argument in §3.3-5; it must be machine-checked before
   any bounded verdict is labeled sound. Open obligation, expected to be routine.
6. **Different-environment bisimulation.** The paper suppresses the specification context;
   Lean fixes one shared `env`. If the artifact ever needs to compare processes under
   *different* recursive specifications, a two-environment `IsBisimulation` variant is needed.
   Not needed for the current pipeline. Noted for completeness.

---

## 10. Validation

- Branch: `history-semantics` (unchanged; verified via `git branch --show-current`).
- Worktree: all pre-existing modifications and untracked files intact (50 `git status
  --porcelain` entries before and after this task; 0 stashes).
- `git diff --check`: clean.
- Files changed by this task: exactly one - this report (`docs/BISIMULATION_ENVIRONMENT_AUDIT.md`).
- No Lean build needed: no Lean file was touched.
