# Safety-Checking Workflow Audit (Task S1)

Research and documentation only. No Lean sources were modified.

**Paper:** `DyNetKAT.pdf` (repo root; FoSSaCS 2022 version, arXiv:2102.10035). Page/section
anchors below use the paper's own definition/equation numbers.
**Original tool:** `hcantunc/DyNetiKAT`, commit `1c6bd42` (v1.1) — the same revision audited in
`docs/DYNETIKAT_REFERENCE_AUDIT.md`, whose findings were re-verified against source.
**Source caveat (verified):** `/Users/ali/Desktop/DyNetKAT` no longer hosts the original tool; it
is now the separate `sarmadiali98/DyNetKAT` repository (SDNRacer-oriented). The tool was
therefore re-fetched from GitHub into a scratch directory and inspected read-only. The journal
draft (`DyNetKAT_Journal.pdf`, on the other machine) is a review copy; it adds no tool detail.
Labels: **[V]** verified fact, **[I]** interpretation, **[R]** recommendation.

---

## 1. Confirmed safety-checking pipeline

**[V]** Reconstructed from `dnk.py`, `src/python/{dynetkat,preprocess,maude_parser,netkat_parser}.py`,
`src/maude/{dnk.maude,preprocess.maude}`, cross-checked with paper §IV–V.

1. **Input** (JSON): `recursive_variables` (`X ≜ D` definitions, NetKAT sub-terms quoted),
   `program`, `channels`, paired `in_packets`/`out_packets` predicates, and per-packet
   `properties` `[type, formula, expected, n]` with `type ∈ {r, w}` (`dnk.py:52-56`,
   `dynetkat.py:141-146`).
2. **Preprocessing** (`preprocess.py:78-129` + `preprocess.maude`):
   Maude parses each recursive-variable body, tagging NetKAT sub-terms `@NetKAT(…)` and
   communication terms `@Comm(…)`. Every NetKAT sub-term is sent to the external NetKAT
   decision procedure as `equiv x zero`; terms equivalent to `0` are rewritten to `zero` in the
   variable definitions so the Maude axiom `zero ; P = bot` (`dnk.maude:46`) can fire. All
   communication terms are collected into `data['comm']`.
3. **Module generation** (`preprocess.py:24-50`): a Maude module declares each variable as sort
   `Recursive`, each channel, and one equation `eq getRecPol(X) = <body>.` per recursive
   variable; it imports `DNA` (axioms) and `PROPERTY-CHECKING` (head/tail).
4. **Analysis term** (`dynetkat.py:144`): for each property,
   `delta{H}(pi{n}(program))` where `H` = **all** `x!z`/`x?z` communication terms of the program
   (`compute_encapsulation_set`, `dynetkat.py:20-27`) and `n` is the property's user-specified
   unfolding bound. The property template's `@Program` and `{…}` RSet placeholders are
   substituted (`dynetkat.py:145`).
5. **Maude reduction** (`maude_parser.py:34-47`, `dnk.maude`): the instantiated formula, e.g.
   `head(delta_H(pi_n(program)))` or `head(tail(delta_H(pi_n(program)), {rcfg(x,z)}))`, is
   reduced (`red in MOD : … .`) under: lazy recursive unfolding (`RECURSIVE-DNA`, `dnk.maude:96-125`),
   DyNetKAT axioms A0/A3/A4/A7–A13/A15 (`dnk.maude:46-69,93`), restriction equations
   `[D1]–[D-plus]` (`dnk.maude:72-80`), projection equations `[PI-0]–[PI-plus]`
   (`dnk.maude:83-90`), and head/tail equations (`dnk.maude:140-149`). Result: a **NetKAT term
   as an opaque string** — Maude never reasons about NetKAT algebra.
6. **NetKAT decision** (`netkat_parser.py`): the string is converted to tool syntax
   (`<-`→`:=`, `zero`→`F`/`drop`, `one`→`T`/`pass`, `.`→`;`, integers→binary for `netkat-idd`)
   and checked by the external procedure: `katbv equiv f1 f2` or `Decide_Repl.native "(t1) == (t2)"`.
   - Reachability `r`: `equiv (in · net · out) zero` (`dynetkat.py:72-77`).
   - Waypointing `w`: `equiv (in · net · out + W) W` with
     `W = in · (~out · net)* · wp · (~in · net)* · out` (`dynetkat.py:44-51, 78-85`).
7. **Verdict** (`dynetkat.py:97-122`): `r`/`!0` satisfied iff equiv returns `false`
   (term ≢ 0); `r`/`=0` satisfied iff `true`; `w` satisfied iff `true`; Maude/NetKAT failure
   yields `error`. **No counterexamples are generated** — the backends return only
   true/false; a violation is reported as the bare word "violated".

**[I]** Relation to the paper. The paper's general framework (Def. 12 syntax, Def. 13 head
normal forms `hnf`, Def. 14 semantics `⟦[regexp]false⟧` with the universal policy `Θ`, Def. 15
`EDNK^tr` = `EDNK` + (A16) `p;(q⊕r) ≡ p;q ⊕ p;r` (26), Def. 16 safety check `EDNK^tr ⊢ ⟦s⟧ ⊕ i ≡ ⟦s⟧`
(27), Def. 17 sugars/desugaring `ds`) is **not** implemented as such by the tool. The tool
implements the specialization of (27) to reachability and waypointing via `head`/`tail`
(examples (34)–(35)), exactly as §V describes ("we turn the equational reasoning about safety
into checking for reachability properties"). Def. 14's trace reading makes safety violation =
existence of a finite trace with some forbidden word `wᵢ` as prefix; reachability `≢ 0` is its
decision-theoretic form.

**[V]** `head`/`tail` (paper Eqs. (29)–(33), `dnk.maude:140-149`):
`head(⊥)=0`; `head(N;D)=N+head(D)`; `head(D⊕Q)=head(D)+head(Q)`; `head(rcfg;D)=0` — the sum of
all NetKAT policies reachable before any reconfiguration. `tail(⊥,R)=⊥`; `tail(N;D,R)=tail(D,R)`;
`tail(D⊕Q,R)=tail(D,R)⊕tail(Q,R)`; `tail(rcfg;D,R)=D⊕tail(D,R)` if `rcfg(X,Z)∈R`, else `⊥`.
Both assume the input is restricted (no `x?q`/`x!q` remains) — paper §V and `dnk.maude:138-139`.
Note `head` is applied to the *whole* truncated term, so it sums policies at every depth `≤ n`
that precede the first `rcfg` on each branch; `pi_n` bounds how deep this reaches.

## 2. Recursion and cyclic-graph findings

- **[V]** Representation in the tool: variables are Maude constants of sort `Recursive`; bodies
  live in generated `getRecPol` equations; unfolding is lazy — `pi{s(M)}(P) = pi{s(M)}(unfold(P))`
  fires only when `P` is an (un)guarded term blocking progress (`dnk.maude:114-124`).
- **[V]** Neither operator eliminates recursion *by solving* it. Restriction `δ_H` never touches
  variables (it only cuts communication prefixes, `dnk.maude:72-80`). Projection eliminates
  variables **by bounded truncation**: unfolding is forced while `pi` still has budget, and
  `pi{0}(P) = bot` cuts whatever remains (`dnk.maude:83`). After `pi_n`, no variable survives —
  but the result is an under-approximation of depth > n behavior, not a fixpoint resolution.
- **[V]** No normalization, unfolding-to-fixpoint, or graph/cyclic solving exists anywhere in
  the tool; the A-axioms only normalize choice/parallel structure. The claimed "resolve
  recursive variables before the final reasoning procedure / cyclic graphs" suggestion appears
  in **neither** the FoSSaCS paper nor the journal draft (searched both); it is not reflected in
  the code. Treat it as unverified guidance, not an implemented mechanism.
- **[V]** Unboundedness: the paper itself concedes the bound ("for a fixed n, the verification
  procedure resembles bounded model checking", §IV) and provides only the ingredients — Lemma 8
  (guarded ⇒ finitely branching) and Lemma 11 (AIP soundness, proof uses Lemma 8) — not an
  algorithm. AIP (`p ≡ q if ∀n, pi_n(p) ≡ pi_n(q)`, Fig. 11) is a meta-principle, not a Maude
  equation.
- **[I]** Consequence for us: `RecEnv` can remain a purely semantic device. The checker
  interface should take a *resolved view* — (program, `RecEnv`, property, bound `n`) — and
  perform unfolding internally, mirroring `getRecPol`. An unbounded "safe" verdict additionally
  requires a **stabilization argument**: on the finite packet domain, a guarded, restricted
  system's reachable process space (up to bisimilarity) is finite, so `pi_n` behavior
  stabilizes at some `n₀`; a verdict proven for all `n ≥ n₀` (or a proof that the bounded
  frontier repeats) lifts the bounded result to the unbounded system. Formalizing that
  stabilization theorem is the missing mathematical obligation; nothing in `RecEnv`/`Step`
  needs to change to attempt it.

## 3. Role of E_NK (Figure 4)

**[V]** Figure 4 is the NetKAT equational system `E_NK` [2]: KA axioms (left column), BA axioms
and PA axioms (right column). Verified layout (bbox extraction): the final two rows are

- row n−1: `KA-LFP-L`: `q + p·r ≤ r ⇒ p*·q ≤ r` and `PA-CONTRA`: `f=n · f=n' ≡ 0` if `n ≠ n'`;
- final row: `KA-LFP-R`: `p + q·r ≤ q ⇒ p·r* ≤ q` and `PA-MATCH-ALL`: `Σᵢ f=i ≡ 1`.

Side conditions: `KA-LFP-L/R` carry their premise inequations (`q + p·r ≤ r`, resp.
`p + q·r ≤ q`); `PA-CONTRA` requires `n ≠ n'`; `PA-MATCH-ALL` sums over **all** values `i` of
field `f` and is sound only because field domains are finite (paper: "we consider network
packets with values in finite domains", proof of Lemma 5). If "final two" is read per column,
the PA block ends with `PA-CONTRA` + `PA-MATCH-ALL`; the substantive answers below cover both
readings.

- **What they establish.** `KA-LFP-L/R` are the least-fixpoint (induction) axioms that make
  `*` complete — without them KA reasoning about iteration is incomplete. `PA-CONTRA` and
  `PA-MATCH-ALL` tie the algebra to the finite packet domain; together with `PA-MOD-MOD` they
  are exactly what makes the dup-free normal-form theorem work: Lemma 5 (`E_NK ⊢ p ≡ Σ_{α·π∈G} α·π`,
  via language model (7)–(8)) needs every packet to satisfy *some* complete test
  (`PA-MATCH-ALL`) and inconsistent tests to be unsatisfiable (`PA-CONTRA`).
- **Dependence of the safety workflow.** The pipeline's terminal step is NetKAT equivalence
  checking, whose correctness rests on NetKAT completeness, which rests on Lemma 5, which
  rests on the PA axioms; the `LFP` axioms underpin the star fragments appearing in
  `(p·t)*` reachability/waypointing terms. DyNetKAT normal forms (Def. 6) and hence
  `head`/`tail` applicability inherit this.
- **Does our evaluator implement their behavior?** **[V]** Yes, semantically, on the finite
  `CtxPkt` domain: contradictory tests evaluate to `∅`; every `σ : CtxPkt` satisfies some
  complete test since fields range over the finite `FieldValueEnum` (`Packet.lean` `Fintype`
  instances); star is handled by `boundedStar` with `execute_star_correct` — the semantic
  counterpart of the LFP induction principle (`NetKAT/Evaluator.lean:171,233,244`).
- **Equational derivability vs semantic decision procedure.** **[I]** These must be
  distinguished: Theorem 1 (`EDNK` sound + ground-complete for bisimilarity) is about
  *derivability*; the tool never performs derivations — it delegates equivalence to a decision
  procedure justified by completeness. For our checker, a **semantic decision procedure on the
  finite domain is sufficient and sound and complete** for the relational semantics we have
  verified; an explicit `EDNK`/`E_NK` derivability relation is not needed to build the checker
  (it would only be needed to mirror the paper's proof theory). Mathlib v4.19 (installed)
  provides `KleeneAlgebra` as an ordered idempotent-semiring-with-star class
  (`Mathlib/Algebra/Order/Kleene.lean:89`) — structure only, no NetKAT/packet algebra and no
  decision procedure.

## 4. Maude / Python / NetKAT delegation map

**[V]** (file:function → role)

| Concern | Delegated to | Location |
|---|---|---|
| DyNetKAT structural axioms (A0, A3, A4, A7–A13, A15, `zero;P=bot`, `cr-1`) | Maude | `dnk.maude:46-69,93` |
| Restriction `δ_H` equations | Maude | `dnk.maude:72-80` |
| Projection `π_n` equations | Maude | `dnk.maude:83-90` |
| Lazy recursive unfolding | Maude | `dnk.maude:96-125` (`unfold`, `getRecPol`) |
| `head`/`tail` extraction | Maude | `dnk.maude:140-149` |
| Annotation/parsing of variable bodies | Maude | `preprocess.maude` |
| Encapsulation set `H`, analysis term `delta_H(pi_n(program))`, template instantiation, verdicts, parallelism | Python | `dynetkat.py:20-27,125-155,97-122` |
| Zero-elimination orchestration, module generation | Python | `preprocess.py:68-129` |
| Subprocess wrappers | Python | `maude_parser.py`, `netkat_parser.py` |
| **All** NetKAT equivalence decisions (preprocessing zero-checks *and* final property checks) | external `netkat-idd` (`katbv`) or `netkat-automata` | `netkat_parser.py:17-58` |

**[I]** NetKAT sub-terms are opaque strings to Maude; the "NetKAT backend" is used exactly twice
per pipeline: zero-equivalence during preprocessing and equivalence at verdict time.

## 5. Lean: existing vs missing

**[V] Existing (verified where noted):**
- NetKAT relational `Semantics` + algebraic laws (`NetKAT/Semantics.lean`); verified evaluator
  `execute` with `execute_correct` (`NetKAT/Evaluator.lean:171,1078`) over `Fintype CtxPkt`.
- Full DyNetKAT AST incl. `restrict`/`project`/`var` (`DyNetKAT/AST.lean:100-112`); SOS `Step`
  incl. `cpol_restrict`, `cpol_project`, `cpol_var` (`DyNetKAT/Semantics.lean`); `RecEnv`,
  `Definedness`/`WellFormed` (`RecEnv.lean`, `Definedness.lean`); bisimulation + congruence
  fragments (`Bisimulation.lean`); verified `nSeq` packet-step enumeration
  `packetTransitions_sound/complete` (`Executable.lean:57,90`, `NetKATBridge.lean`).
- `NormalForm` representation only — no normalizer (`NetKAT/NormalForm.lean`, header disclaimer).

**[V] Missing, mapped to pipeline stages:**
1. NetKAT **equivalence decision procedure** (replaces `katbv`/`Decide_Repl`) — used at two
   pipeline points (§4).
2. Encapsulation-set collection over the AST (trivial fold).
3. Syntactic restriction `δ_H : AST → AST` + soundness vs `Step.cpol_restrict`.
4. Syntactic bounded projection/unfolding `π_n` via `RecEnv` + soundness vs
   `Step.cpol_project`/`cpol_var` (the executable counterpart of `getRecPol`).
5. `head`/`tail` as AST functions + correctness theorems (input: restricted term).
6. Property-term construction and verdict classification (thin layer).
7. Optional preprocessing zero-elimination (needs 1).

## 6. Recommended first implementation task

**[R]** **S2 — verified finite-domain NetKAT equivalence checker.** New file (e.g.
`lean/DyNetKAT/NetKAT/Equiv.lean`): a boolean/decidable function comparing `execute p σ` and
`execute q σ` for all `σ` in the finite packet universe, plus special case `equivZero`.

Proof obligation (crisp, self-contained):
`netkatEquiv p q = true ↔ ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ`
(⇒ from `execute_correct`; ⇐ from `execute_correct` + `Fintype CtxPkt` + decidable `Finset`
equality), with corollary `equivZero p ↔ ∀ σ τ, ¬ Semantics p σ τ`.

Why before `head`/`tail` or `δ/π`:
- It is the **only** component the original tool delegates to an external backend (§4), and it
  is consumed at two pipeline points; every other missing stage only *produces* inputs for it.
- It directly serves the project goal of dropping Maude/KATch/external-NetKAT dependencies.
- It reuses only `execute` + `execute_correct` + existing `Fintype` instances: no changes to
  existing semantics, proofs, or `RecEnv`/`Step`.
- `head`/`tail` and `δ/π` correctness theorems are more involved and are only useful once
  verdicts can be decided end-to-end.
Implementation notes (not started): `DecidableEq CtxPkt` exists only as `private`/`local` in
`Evaluator.lean`/`Executable.lean`, so S2 re-derives or hoists it; smoke tests can use
`native_decide` on small policies.

## 7. Open questions requiring mathematical clarification

1. **Unbounded safety verdicts.** No algorithm exists in paper or tool. Candidate obligation:
   a stabilization theorem (finite branching (Lemma 8) + finite packet domain ⇒ the restricted
   system's bisimilarity quotient of reachable states is finite ⇒ ∃ n₀ with
   `pi_{n₀} ≈ pi_{n₀+1}` up to equivalence) lifting bounded verdicts. Needs a precise
   statement before any "unbounded safe" claim is verified.
2. **General safety properties (Defs 12–16).** The tool only implements reachability and
   waypointing. If we target the full `⟦[regexp]false⟧` framework we must formalize `Θ`, `hnf`,
   `ds`, and the trace-equivalence step justified by (A16) (26); decide whether this is in
   scope or whether reachability/waypointing (+ isolation as `=0`) is the target surface.
3. **`head` correctness precondition.** `head`/`tail` are specified only on restricted normal
   forms; the exact precondition our Lean theorems should assume (syntactic restrictedness vs
   semantic characterization) needs a decision before stating them.
4. **Paper numbering.** Definitions 3, 5, 8–11 do not appear in the FoSSaCS text (numbering
   jumps 7 → 12); `docs/DYNETIKAT_REFERENCE_AUDIT.md` §14 cites "Definition 11" for the safety
   semantics map, which is Definition 14 in this PDF. Cite by name, not number, in future work.

## 8. Validation

Run after creating this file (see final report): `git status --porcelain`, `git diff --check`.
Pre-existing worktree state (untouched by S1): modified `lean/DyNetKAT.lean`; untracked
`DyNetKAT.pdf`, 11 `docs/*` files, 4 `lean/DyNetKAT/**` source files, 16 `lean/test_*.lean`
files.
