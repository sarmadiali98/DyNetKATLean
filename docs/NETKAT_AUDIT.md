# NetKAT foundations and decision-procedure audit

## Symbolic native KAT

`KATLean.Native` decides the pure KAT equational theory using reduced ordered
Boolean decision trees and symbolic partial derivatives.
`decideEquiv_iff_equational` characterizes derivability from the KAT rules and
`decideEquiv_iff_algebraicallyEquivalent` characterizes equality in every
abstract KATLean model. `nativeSolver_derives` yields a NetKAT derivation
under any substitution of primitive actions and tests.

`netkatNativeEquiv` adds executable symbolic equivalence for the current
dup-free NetKAT AST. KATLean → native KAT → symbolic packet frontend →
NetKAT equivalence → E_NK → E_DNK is the resulting proof path.
`netkatNativeEquiv_correct` is independent of KATch, concrete packet
enumeration and Boolean valuation enumeration. The E_NK completeness proof
uses symbolic closure and the field-level partition axiom. The public
`netkatEquiv` and `netkatIsZero` APIs serve graph normalization and safety
through the symbolic checker. `legacyNetkatEquiv` is the regression oracle.

See [NATIVE_KAT.md](NATIVE_KAT.md) for the theorem chain and proof construction.

## Packet enumeration at baseline `84bdeab`

| Category | Location | Dependency |
|---|---|---|
| A. Semantics and examples | `Packet.lean`, `Semantics.lean`, `HistorySemantics.lean` | `CtxPkt` models total field valuations. The semantics quantify over packets and finite paths without computing a Cartesian product. The concrete `Fintype` and `ctxPkt_card` provide the exhaustive universe to callers. |
| B. Regression oracle | Concrete Lean evaluator/decision tests and Python differential checks | Compare outputs or relations over the fixed finite model. |
| C. Current equivalence decision | `Decision.lean` | `netkatEquivAt` compares two concrete output sets. `netkatEquiv` runs it on every input. `netkatIsZero` applies the same procedure to `drop`. |
| C. Core callers | `DyNetKAT/SafetyCheck.lean`, `DyNetKAT/GraphNormalization.lean` | Executable guard feasibility, nonzero step tests and static reachability use `netkatIsZero`. |
| D. Lemma 5 | `NormalForm.lean`, `Normalization.lean` | Complete tests and updates populate diagonal, filtered, assignment and composed relations. `netkatNormalForm` queries the evaluator on every input. `packetList` constructs the product of field domains, and `orderedPairs` filters the full input/output product. The derivation proof uses that partition and finite star stabilization. |
| E. Concrete evaluation | `Evaluator.lean`, `HistoryEvaluator.lean`, executable reachability and Python packet/tree APIs | Compute actual outputs from a supplied packet. The evaluator's star bound is `Fintype.card CtxPkt`. Retain the concrete execution API. |
| E. History proof wrappers | `Derives.historySound` and `normalize_history_correct` | Use the legacy equality-correctness and history theorems as proof bridges. They do not execute the old checker. |
| E. Experimental certificates | `BackendCertificate.lean`, `EquationalCertificate.lean`, `KATch.lean`, experimental imports and backend scripts | Whole-relation certificate validation, legacy-exact fallback and experimental semantic comparisons stay outside the symbolic solver. |

## Native engine and remaining concrete dependencies

The public `netkatEquiv` delegates to `netkatNativeEquiv`.
`netkatIsZero` compares against drop. Graph normalization, safety, and the
full-relation nonemptiness probe use these symbolic checks. Category C has
been migrated for the dup-free core.

- `legacyNetkatEquiv` runs the old checker on every input as a regression
  oracle. `netkatEquivAt` compares concrete outputs for a supplied input.
- `execute`, concrete star, and history execution still compute outputs
  for a supplied packet, including in SOS execution and concrete certificates.
- Category D remains in `netkatNormalForm` (every input),
  `NormalForm.orderedPairs` (the input/output product), and the executable
  Lemma 5 normalization and its legacy proof (complete packet partitions and
  bounded stabilization). Head normalization in `HeadNormalForm.lean` consumes the
  complete-pair normal form, and its derivation uses `normalize_derives`.
- Experimental certificates can still enumerate complete relations for
  validation. They are outside the native checker and its proof chain.

### Direct E_NK completeness

`derives_of_equiv_starFree` reduces both policies under a single arbitrary
input observation. Its branch sets are generated from the policy syntax and
reached assignments. The proof lifts agreement under these observations by
induction on fields, distributing the local `paMatchAll` sum at each step.
It constructs no list of complete input packets or packet pairs.

`exists_derives_starFree_symbolic` maintains a star-free syntactic witness
below the original star during canonical diagram squaring. At closure,
the star-free completeness theorem derives the right-star fixed-point
equation, and `lfpR` yields the reverse inequality.
`netkatNativeEquiv_iff_derives` uses these two proofs. Neither the
semantic correctness theorem nor the direct derivation bridge depends on
the concrete evaluator, `packetList`, the bounded-star policy, or the Lemma 5
normalizer.

### Symbolic representation and theorem dependencies

`KATLean.NetKAT.Symbolic.Schema` numbers the bits for individual field/value
pairs. Each field must have exactly one active value in each endpoint bank.
Identity relates equal values fieldwise. An assignment constrains the written
output field and requires equality on all other fields. This gives symbolic
overwrite and independence under composition. Native tests use the input bank
and may contain arbitrary Boolean connectives. A complete-test node conjoins
the field equalities of its single supplied packet.

`Guard.rename` substitutes bit indices. `Guard.project` performs existential
forgetting by disjoining a node's two branches when its bit is eliminated.
`Schema.seq_correct` proves this implements relational composition.
The frontend recognizes empty and identity guards before joining, using
the proved annihilation and identity laws of packet relations.
`Schema.star_correct` proves that successive relational squaring from
identity plus the body reaches precisely reflexive-transitive closure.
Canonical diagram equality controls the executable loop. The proof measures
the finite set of rejected Boolean observations, without constructing a
list of observations or selecting a loop cutoff.

`compileSymbolic_correct` states that arbitrary bit valuations satisfy the
compiled diagram exactly when their two endpoint banks encode related packets.
This also rejects malformed encodings. `compileNative` reifies the whole
relation diagram as a single test, with an empty primitive action alphabet.
`netkatNativeEquiv` invokes the native solver's shared
`compareOutputGuards` directly on compiled diagrams.
`netkatNativeEquiv_eq_solver` proves that this specialization returns the
same Boolean as `Native.decideEquiv` on the reified terms.
The reified native search has one reached pair, because its alphabet has
no actions. Packet composition and star are handled by the symbolic frontend
before the final comparison. `distinguishingGuard` is the symmetric difference
of relation diagrams, with certified satisfiability exactly when the solver
rejects.

### Performance sanity

The focused end-to-end check after specializing the native output comparison
reported the following timings in Lean's evaluator. Timing includes both
packet compilations and their comparison. Node counts are reported for the
left/right final guards. Branch counts count decision nodes only.

| Example | Guard nodes | Branch nodes | Native support sizes | Native pairs | Wall time |
|---|---:|---:|---:|---:|---:|
| Same-field overwrite | 4,760 / 4,760 | 1,955 / 1,955 | 1 / 1 | 1 | 1.62 s |
| Three-step route under nested star | 2,456 / 2,456 | 995 / 995 | 1 / 1 | 1 | 24.28 s |

These are single runs under concurrent verification. Reduced decision trees
can duplicate subdiagrams, and the final node count excludes intermediate
composition diagrams. The measurements establish an executable path and
identify compilation as the main cost in the migrated callers.

## Current scope and roadmap

The source is [arXiv:2102.10035v4](https://arxiv.org/pdf/2102.10035v4),
especially Defs. 1 and 4, Figs. 3–4 and Lemma 5. The
[conformance inventory](PAPER_CONFORMANCE.md) gives the edition crosswalk
and the [proof ledger](PROOF_OBLIGATIONS.md#netkat-foundations) gives the
theorem targets. The dated Task 2N/2R notes below record earlier findings.

| Dimension | Current evidence | Release requirement |
|---|---|---|
| Mathematical model | Generic uniform-codomain `Packet` utilities. `CtxPkt` and the policy AST use `tpSrc`, `tpDst`, `swId`, `port`, each with values 0, 1, 8 and 9. `ctxPkt_card` proves cardinality 256. The history relation and SOS use this instance. | Finite field schema with a finite value domain per field, typed field tests and updates, packet and history semantics and proved complete tests/assignments for every schema. |
| Evaluation and decision | `eval_correct`, `execute_star_correct`, `netkatIsZero_correct`, `netkatEquiv_correct` and their history bridges. Exact star on the current universe uses a cardinality argument and fixpoint detection. | Verified native symbolic packet equivalence for finite schemas, independent of exhaustive packet enumeration. Keep the concrete evaluator as a reference model. NetKAT star remains independent of the DyNetKAT projection depth. |
| Algebra | `Derives` and soundness for the fixed dup-free system. Executable `normalize` produces the finite pair sum of every dup-free `CtxPkt` term, including star, with proved semantic equality. Pair-sum extensionality and star elimination from derivable stabilization are kernel checked. | `normalize_derives_starFree` and `normalize_derives` prove normalization in the existing equational system. `exists_derives_pairSum` closes Lemma 5 on `CtxPkt`. General finite schemas remain open. Full Figure 4 history/dup coverage is an optional supporting extension. |
| Functional query coverage | Fixed-domain relation decisions and the initial/post-event firewall query. | General-domain reachability, non-reachability and waypoint inclusion, in the original dynamic pipeline and as standalone NetKAT decisions. Verify the original backend encodings as separate comparisons. |
| Scalability | Small finite regression universe and differential corpus. | Complete the original FatTree cases through 1,344 switches with measurements of time and memory and baseline comparisons. |

### KATLean algebra bridge

[KATLEAN.md](KATLEAN.md) records the pinned Mathlib classes and every
Figure 4 axiom. `KATLean` is an independent Lean library target with
KA wrappers, Boolean tests and a packet-relation model. The generic
packet interface permits dependent field values and proves the seven
dup-free PA laws. `ctxPacketModel` instantiates it using the existing
packet API. `katInterp_correct` and `execute_katInterp` connect all
current AST operations, including star, to the same evaluator semantics.
`Derives.katSound` and `normalize_katInterp` connect existing
derivations and Lemma 5. The fixed-domain syntax and evaluator remain
the concrete integration target. General-schema normalization remains a core release requirement. Full
NetKAT history/dup coverage is an optional supporting extension.

### Dependency audit

`DyNetKAT.lean` imports KATLean and the existing NetKAT and process proof
modules. Its transitive source imports exclude `NetKAT.KATch`,
`NetKAT.BackendCertificate`, `NetKAT.EquationalCertificate` and
`DyNetKAT.Experimental`. KATLean depends only on Mathlib. The current
NetKAT bridge imports KATLean and NetKAT normalization.

The optional umbrella imports the core and the three backend modules.
`BackendCertificate` imports normalization, the KATch comparison model and
Lean JSON support. `EquationalCertificate` imports that checker.
The subprocess driver lives in `scripts/katch_replay.py`. Core theorem
modules import none of this machinery. Optional theorems remain checked
Lean results whose hypotheses concern candidate validation, while the
external backend supplies no trusted assumption.

### Finite schemas and exact closure

Use a schema-indexed valuation `(f : Field) → Value f`, with computable
enumeration, decidable equality and nonempty finite domains. Keep the
current four-field instance for regression and prove a compatibility
bridge. Validate literal values against the schema during parsing. If an
adapter derives domains from source constants, it must account for all
unmentioned values observable by negated tests, identity, PA-MATCH-ALL
or later input constraints. An exact abstraction can group indistinguishable
values only with a proof that tests, writes, star, zero and equivalence
respect the abstraction, including preservation of unchanged values.

Use the explicit evaluator as a reference. For a fixed input, the
reached-output set grows monotonically and can grow only finitely many
times. A simple finite path bound or the equivalent least-fixed-point
invariant yields exact reflexive-transitive closure. Nested star follows
by structural correctness for the inner policy. Completeness of E_NK is
a separate derivability statement over the current dup-free language.
A future full NetKAT extension could relate its derivations to this
fragment by erasing dup to identity and proving rule preservation.

### Core evaluator and scale

Core query correctness follows from the existing NetKAT evaluator and
KATLean interpretation theorems. Core release criteria concern that
implementation and the intended finite input universe. General-domain
query correctness and scalable parity remain open. Optional external
comparisons are recorded separately below.

Enumerating input packets costs at least the product of field-domain sizes
for a total-domain scan. Materializing all complete test/assignment pairs
can cost the square of that product. At 16 pods the FatTree source
uses switch/location, port, source, destination and traffic-type fields.
Several have large domains. Even the switch count alone exceeds any
current field domain. The complete-pair normal form is useful for the
algebraic proof and as a small-domain oracle. Benchmark implementation
choices before relying on enumeration.

A future internal performance implementation may use
shared decision diagrams or symbolic packet relations with identity,
test, assignment, Boolean union, composition, exact fixed-point closure
and relation emptiness/equality. Prove denotation of each operation and
termination of closure, then compare with the finite oracle. Core
performance claims must be measured end to end on the original workloads.

## Historical implementation audit

**Audit date:** 2026-10-16 (Phase 1.5) / 2026-10-17 (Task 2N)
**Repository:** `/Users/ali/Desktop/DyNetKAT-Lean`
**Paper:** *DyNetKAT: An Algebra of Dynamic Networks*, arXiv:2102.10035v4 (FoSSaCS 2022)
**Scope:**
- Phase 1.5: NetKAT semantic core — `Packet.lean`, `AST.lean`, `Semantics.lean`, Python tests.
- Task 2N: Complete-Test Conformance Audit — Definition 4 (Complete Tests & Assignments), p. 8.

---

## 0. Task 2N — Complete-Test Conformance Audit (Definition 4)

**Task date:** 2026-10-17
**Task ID:** 2N
**Objective:** Verify that `CompleteTest` and `CompleteAssignment` faithfully implement Definition 4 of the paper.

### 0.1 Exact paper definition

**Definition 4 (Complete Tests & Assignments [2], p. 8), verbatim:**

> "Let F = {f₁, . . . , fₙ} be a set of field names with values in Vᵢ, for i ∈ {1, . . . , n}.
> We call *complete test* (typically denoted by α) an expression f₁=v₁ · . . . · fₙ=vₙ, with vᵢ ∈ Vᵢ, for i ∈ {1, . . . , n}.
> We call *complete assignment* (typically denoted by π) an expression f₁←v₁ · . . . · fₙ←vₙ, with vᵢ ∈ Vᵢ, for i ∈ {1, . . . , n}.
> We sometimes write σα to denote the network packet whose fields are assigned the corresponding values in α; symmetrically for σπ."

**Key requirements derived from Definition 4:**
1. A complete test α assigns **exactly one value** to **every** field (total valuation).
2. A complete assignment π overwrites **every** field (total transformation).
3. The notation σα / σπ treats α and π as *valuations* (functions F → Vᵢ) applied to a packet σ.
4. Complete tests and general predicates (Figure 3: `Pr ::= 0 | 1 | f=v | Pr+Pr | Pr·Pr | ¬Pr`) are **distinct** concepts.

**Context from the paper (Lemma 5, p. 647):** "Let A be the set of all complete tests, and Π be the set of all complete assignments. ... Consequently, A and Π are finite." — The finiteness of A and Π follows from the finiteness of each Vᵢ.

### 0.2 Corresponding Lean definitions (as of Task 2R-L, 2026-10-17)

| Paper concept | Lean definition | File:Line |
|---|---|---|
| Complete test α (`f₁=v₁ · ... · fₙ=vₙ`, total valuation) | `def CompleteTest := CtxPkt` | `Packet.lean:193` |
| Complete assignment π (`f₁←v₁ · ... · fₙ←vₙ`, total valuation) | `def CompleteAssignmentValuation := CtxPkt` | `Packet.lean:253` |
| α holds on σ (all fields match) | `def holdsComplete (alpha sigma) := forall f, alpha f = sigma f` | `Packet.lean:204` |
| Apply π to σ (⟦π⟧(σ) = π) | `def applyValuation (pi sigma) := pi` | `Packet.lean:268` |
| ⟦α⟧ = {(σ,σ) \| α holds on σ} | `.completeTest α => holdsComplete α σ ∧ σ = τ` | `Semantics.lean:67` |
| ⟦f←v⟧ = {(σ, σ[f:=v])} (primitive single-field assignment) | `.assign1 f v => τ = Packet.update σ f v` | `Semantics.lean:68` |
| ⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π (complete assignment semantics) | `completeAssignExpr_sem` theorem | `Semantics.lean:635` |
| AST constructor for α | `completeTest : CompleteTest → NetKAT` | `AST.lean:93` |
| AST constructor for f←v (primitive) | `assign1 : FieldName → FieldValueEnum → NetKAT` | `AST.lean:94` |
| Build complete assignment π as compound expression | `completeAssignExpr : CompleteAssignmentValuation → NetKAT` | `AST.lean:137` |

**Legacy types removed (Task 2R-K):** `CompleteAssignment := CtxPkt → CtxPkt`
and `applyAssign` have been removed from `Packet.lean`. Only a comment at
`Packet.lean:239` documents their removal. No active code references remain.

The concrete packet type is `CtxPkt := Packet FieldName FieldValueEnum` where
- `FieldName` is a 4-element inductive type (`tpSrc`, `tpDst`, `swId`, `port`) with `[Fintype FieldName]` (`Packet.lean:117-129`).
- `FieldValueEnum` is a 4-element inductive type (`v0`, `v1`, `v8`, `v9`) with `[Fintype FieldValueEnum]` (`Packet.lean:132-144`).

### 0.3 Correspondence check

#### 0.3.1 Complete tests — equivalent ✅

**Paper:** α = `f₁=v₁ · ... · fₙ=vₙ` — every field assigned exactly one value.
**Lean:** `CompleteTest := CtxPkt = FieldName → FieldValueEnum` — a total function from fields to values.

The total-function representation **enforces** totality by construction: there is no
way to construct a `CompleteTest` that leaves a field unspecified or assigns
conflicting values. The `holdsComplete` function checks `forall f, alpha f = sigma f`,
which is exactly the paper's semantics: α holds on σ iff every field value matches.

**Mathematical equivalence:** ✅ The set of total functions `FieldName → FieldValueEnum`
is in bijection with the set of complete test expressions `f₁=v₁ · ... · fₙ=vₙ`
(each function corresponds to exactly one such expression, and vice versa).
The representation is faithful and introduces **no additional assumptions**.

#### 0.3.2 Complete assignments — fully conformant ✅ (as of Task 2R-L, 2026-10-17)

**Paper:** π = `f₁←v₁ · ... · fₙ←vₙ` — overwrites every field. The notation σπ
denotes the packet resulting from applying π to σ. A complete assignment is a
specific *syntactic form* that always overwrites all fields, implemented as a
sequence of primitive single-field assignments per the PA axioms.

**Lean:** The legacy `CompleteAssignment := CtxPkt → CtxPkt` (arbitrary function
superset) has been **removed**. It is replaced by:
- `CompleteAssignmentValuation := CtxPkt` — a total valuation `FieldName → FieldValueEnum`,
  the direct dual of `CompleteTest`. By construction, every field maps to exactly
  one value, matching Definition 4.
- `applyValuation (pi sigma) := pi` — returns the valuation π itself, matching
  Definition 4's σπ = π ("the result equals the valuation").
- `completeAssignExpr (π)` — builds `assign1 f₀ (π f₀) ; assign1 f₁ (π f₁) ; ...`
  from the `fieldEnum` enumeration, implementing `f₁←v₁ · ... · fₙ←vₙ`.
- `completeAssignExpr_sem` — proves `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π`.

The paper-faithful representation treats π as a valuation (field → value), and
σπ is the packet where every field is overwritten to π's value. No completeness
invariant is needed — the total-function type enforces it by construction.

**Assessment:** ✅ Fully conformant. The superset issue is eliminated. All
assignment theorems are proven with no `sorry`/`admit`/`axiom`.

#### 0.3.3 Single-field assignments — primitive constructor `f←v` ✅ (as of Task 2R-L, 2026-10-17)

The legacy `fieldAssign` helper (`AST.lean` old lines 112-113) has been **removed**.
It is replaced by the paper's primitive single-field assignment constructor:

- `assign1 : FieldName → FieldValueEnum → NetKAT` (`AST.lean:94`) — the paper's
  `f←n` basic term per Figure 3 (p. 5).
- Semantics: `| .assign1 f v => τ = Packet.update σ f v` (`Semantics.lean:68`) —
  matches the paper's `⟦f←v⟧ = {(σ, σ[f:=v])}`.

A single-field assignment `f←v` is a **distinct syntactic category** from complete
assignments π per Definition 4. Complete assignments are built as sequences of
`assign1` operations via `completeAssignExpr`, matching the paper's normal-form
decomposition: `f₁←v₁ · ... · fₙ←vₙ = (f₁←v₁);...;(fₙ←vₙ)` per the PA axioms
(Figure 4).

#### 0.3.4 Complete tests and general predicates — distinct ✅

The implementation correctly maintains the paper's distinction:
- `Predicate` inductive (`AST.lean:37-44`): `pFalse`, `pTrue`, `pFieldEq`, `pAnd`, `pOr`, `pNot` — matches Figure 3.
- `CompleteTest` is a separate type (`CtxPkt`, a total function).
- The `NetKAT` AST has **separate constructors**: `test : Predicate → NetKAT` (line 92) and `completeTest : CompleteTest → NetKAT` (line 93).
- The `holdsFinset` legacy path (`Packet.lean:182`) is **not used** in `Semantics.lean` — only `holdsComplete` is referenced (line 67).

**Assessment:** ✅ No conflation. General predicates and complete tests remain distinct types.

#### 0.3.5 Total-valuation representation preserves paper meaning ✅

- `holdsComplete`: `forall f, alpha f = sigma f` — exactly the paper's "α holds on σ iff all field values match."
- `applyValuation`: `pi sigma := pi` — exactly the paper's `σπ` notation (π applied to σ, output equals π).
- Semantics: `.completeTest α => holdsComplete α σ ∧ σ = τ` — matches `⟦α⟧ = {(σ,σ) | α holds on σ}`.
- Semantics: `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π` — matches `⟦π⟧ = {(σ, π)}` (σπ = π); proven by `completeAssignExpr_sem` theorem.

**Assessment:** ✅ The total-valuation representation preserves the paper's meaning for complete tests and complete assignments. The `holdsComplete_iff_eq` theorem (`Packet.lean:218`) establishes the proven correspondence: a complete test α holds on σ iff σ = α. For complete assignments, `applyValuation` and `completeAssignExpr_sem` establish σπ = π (the result of a complete assignment equals the valuation itself, independently of the input packet). No conflation between total valuations and arbitrary functions remains.

### 0.4 Missing proof obligations

| # | Obligation | Paper reference | Status |
|---|---|---|---|
| 1 | `Fintype CtxPkt` instance | Lemma 5: "A and Π are finite" | **Satisfied** — `instance : Fintype CtxPkt` at `Packet.lean:158-161` (established by Task 2S); `Fintype CompleteTest` and `Fintype CompleteAssignmentValuation` instances also registered at `Packet.lean:198-200` and `Packet.lean:258-260` |
| 2 | `Fintype CompleteTest` (finite A) | Lemma 5: "A is finite" | **Satisfied** — `instance : Fintype CompleteTest` at `Packet.lean:198-200`, obtained by transferring `Fintype CtxPkt` along `CompleteTest = CtxPkt` |
| 3 | `Fintype CompleteAssignmentValuation` (finite Π) | Lemma 5: "Π is finite" | **Satisfied** — `instance : Fintype CompleteAssignmentValuation` at `Packet.lean:258-260`, obtained by transferring `Fintype CtxPkt` along `CompleteAssignmentValuation = CtxPkt` |
| 4 | Completeness invariant for complete assignments | Definition 4: π = `f₁←v₁ · ... · fₙ←vₙ` | **Satisfied (by construction)** — `CompleteAssignmentValuation := CtxPkt` (a total valuation) enforces one-value-per-field by type, and `applyValuation pi _sigma := pi` directly returns π, matching σπ = π |
| 5 | Equivalence of `CompleteTest` representation ↔ Definition 4 | Definition 4 | **Proven** — `holdsComplete_iff_eq` (`Packet.lean:218`) establishes that a complete test α holds on σ iff σ = α, confirming exactly-one-packet-matching semantics |
| 6 | Each complete test specifies exactly one value per field | Definition 4: "vi ∈ Vi for i ∈ {1,...,n}" | **Proven (by construction + theorem)** — `CompleteTest := CtxPkt` (total function `FieldName → FieldValueEnum`) enforces one value per field; `holdsComplete_iff_eq` confirms uniqueness |

### 0.5 Actual semantic discrepancies

| # | Discrepancy | Severity | Paper reference | Lean location |
|---|---|---|---|---|
| 1 | `holdsFinset` (legacy `Finset FieldEq` path) conflates predicate `1` with complete test | Low (not used in semantics) | Definition 4 | `Packet.lean:182` |
| 2 | `holdsFinset` empty-set-as-true behavior | Low (not used in semantics) | Definition 4 | `Packet.lean:182` |

> **Note on resolved discrepancies (Task 2R-L):** The legacy `CompleteAssignment := CtxPkt → CtxPkt` (arbitrary function superset, old `Packet.lean:177`) and `fieldAssign` (old `AST.lean:112-113`) were both **removed** as part of the assignment conformance migration (Task 2R-K). The current `CompleteAssignmentValuation := CtxPkt` (total valuation at `Packet.lean:253`) enforces totality by construction. The `Fintype CtxPkt` instance (`Packet.lean:158-161`) was also established (Task 2S). These are no longer discrepancies.

### 0.6 Conclusions

1. **Complete tests are faithfully implemented** ✅ — The total-function
   representation (`CompleteTest := CtxPkt`) enforces exactly-one-value-per-field
   by construction, matching Definition 4. `holdsComplete` correctly checks
   all fields. The `holdsComplete_iff_eq` theorem (`Packet.lean:218`) proves the
   key correspondence: α holds on σ iff σ = α. No additional assumptions are introduced.

2. **Complete assignments are faithfully represented** ✅ —
   The legacy `CompleteAssignment := CtxPkt → CtxPkt` (arbitrary function superset)
   has been removed. The replacement `CompleteAssignmentValuation := CtxPkt` (total
   valuation at `Packet.lean:253`) is the direct dual of `CompleteTest` and enforces
   one-value-per-field by construction. Its semantics (`completeAssignExpr_sem`,
   `Semantics.lean:635`) proves `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π`, matching
   Definition 4's σπ = π. `applyValuation pi _sigma := pi` (`Packet.lean:268`)
   directly returns π, confirming the output depends only on π, not σ.

3. **Complete tests and general predicates are distinct** ✅ — Separate `Predicate`
   (inductive, `AST.lean:37-44`) and `CompleteTest` (total valuation) types with
   separate AST constructors (`test` at `AST.lean:92`, `completeTest` at `AST.lean:93`).
   No conflation. The only legacy artifact is `holdsFinset` (`Packet.lean:182`),
   which is retained as a backward-compatibility helper but is **not used** in the
   active semantics (`Semantics.lean:67` uses `holdsComplete`).

4. **No missing assumptions for complete tests** ✅ — The representation introduces
   no assumptions absent from Definition 4 for complete tests. The `Fintype` instances
   for `CtxPkt`, `CompleteTest`, and `CompleteAssignmentValuation` are all registered
   (`Packet.lean:158-200, 258-260`), satisfying the finiteness requirement of
   Lemma 5 for the finite (4×4) concrete domain.

5. **Finite-domain infrastructure** ✅ — The `[Fintype CtxPkt]` instance
   (`Packet.lean:158-161`) is established. However, the star-termination theorem
   (`star_terminates` — proof that `StarClosure` stabilizes in ≤ `|CtxPkt|²` steps on
   a finite domain) is **not yet proven**. This is a separate obligation from
   complete-test representation and remains deferred.

---

## 1. Summary of Changes (as of Task 2R-L, 2026-10-17)

The repository has one commit (`0393869`, "Phase 1: Implement NetKAT semantic core")
plus uncommitted working-tree changes implementing the Phase 1.5 NetKAT semantic core
and the assignment conformance migration (Tasks 2O–2R-L):

| File | Status | Summary of Changes |
|------|--------|--------------------|
| `lean/DyNetKAT/NetKAT/Packet.lean` | Modified | Parameterized `Packet` over generic `FieldType`/`Value`; `CtxPkt` abbreviation; `CompleteTest`/`CompleteAssignmentValuation` as total valuations; `applyValuation`; paper update theorems; examples. Legacy `CompleteAssignment`/`applyAssign` removed. |
| `lean/DyNetKAT/NetKAT/AST.lean` | Modified | `Predicate` inductive (pFalse, pTrue, pFieldEq, pAnd, pOr, pNot); `assign1` primitive constructor; `fieldEnum`; `completeAssignExpr`; `fieldEnum_complete`/`fieldEnum_nodup` theorems. Legacy `fieldAssign` and `.assign` constructor removed. |
| `lean/DyNetKAT/NetKAT/Semantics.lean` | Modified | `Semantics` over `CtxPkt`; predicate/completeTest/assign1 semantics; Kleene/Boolean/packet algebra theorems; `assign1_sem`, `assign1_seq_sem`, `assign_list_sem`, `fieldEnum_updates_complete`, `completeAssignExpr_sem`. Legacy `.assign` clause and `assign_sem`/`fieldAssign_sem` removed. |
| `docs/DESIGN_ALARMS.md` | Modified | A2–A6 recorded; A7 recorded (Open), marked Resolved by Task 2R-L evidence. |
| `docs/NETKAT_AUDIT.md` | Modified | Updated for conformance verification. |

**No changes** to `python/tests/test_netkat.py` or `python/pyproject.toml`.

---

## 2. Build Status

`lake build DyNetKAT` — **SUCCESS** (exit code 0). Build completes successfully:

```
✔ [540/541] Built DyNetKAT
Build completed successfully.
```

### Build warnings (non-fatal, pre-existing, not introduced by Task 2R-L)

- `AST.lean` dupNamespace linter warnings (all `NetKAT` constructors) — pre-existing.
- `Semantics.lean:586` unused variable `h` — pre-existing in `test_assign_same_field`.
- `git diff --check` reports a new blank line at EOF in `Semantics.lean:656` —
  pre-existing, not introduced by Task 2R-L.

---

## 3. Paper-to-Lean Conformance Audit

### 3.1 Packet Model

**Question:** Is the packet model generic, or still restricted to four fields and four values?

**Paper (Definition 1, p. 5):** "Let F = {f1,...,fn} be a set of field names fi with i ∈ {1,...,n}. We call network packet a function in F → ℕ." The paper says values are in finite domains; it does **not** fix 4 fields or 4 values.

**Current implementation:** The previous agent parameterized the *foundation*:
- `def Packet (FieldType : Type) (Value : Type) := FieldType -> Value` (generic)  ✅
- `namespace Packet` with generic `get`, `update`, `ext`, and update theorems over `{FieldType Value : Type}`.  ✅
- A concrete test fixture: `inductive FieldName` (tpSrc, tpDst, swId, port), `inductive FieldValueEnum` (v0, v1, v8, v9), `abbrev CtxPkt := Packet FieldName FieldValueEnum`.  ✅

**Classification:** ***Already corrected by previous agent.***

The parameterization follows the paper's abstraction. The concrete 4×4 instance
is retained only as a test fixture (matching the design decision in A2).

However, the paper notes per-field value domains (`Vi`), whereas the implementation
uses a single `Value` type for all fields. This is a minor simplification — the
finiteness argument applies equally — but should be documented.

> **Note:** The `Fintype` instances for `FieldName` and `FieldValueEnum` exist,
> but there is no `Fintype CtxPkt` instance (finiteness of the packet domain,
> required for star termination). This was flagged in the original alarms as
> "Open" and remains so.

### 3.2 Complete Tests (Definition 4, p. 8)

**Question:** Are complete tests guaranteed to specify exactly one value for every field?

**Paper (Definition 4, p. 8):** "We call *complete test* ... an expression f₁=v₁ · … · fₙ=vₙ, with vi ∈ Vi, for i ∈ {1,...,n}." A complete test is a **total valuation** — every field gets exactly one value.

**Current implementation:**
- `def CompleteTest := CtxPkt` — represented as a total function `FieldName → FieldValueEnum`.  ✅
- `def holdsComplete (alpha : CtxPkt) (sigma : CtxPkt) : Prop := forall f, alpha f = sigma f` — checks all fields.  ✅

The representation as a total function **enforces** totality by construction —
there is no way to construct a `CompleteTest` that leaves a field unspecified.

**Legacy helper `holdsFinset`:** The `holdsFinset` function (`Packet.lean:182`)
is a **legacy** helper that operates on `Finset FieldEq` (a set of field=value
pairs), not on `CompleteTest`. It is a partial (non-total) test predicate: an
empty `Finset` is treated as the predicate `true` (matching all packets), which
is **not** a complete test per Definition 4 (which requires totality). This
`holdsFinset` helper is retained for backward compatibility but is **not used**
in the active NetKAT semantics — `Semantics.lean:67` uses `holdsComplete` for
`.completeTest`. The `Predicate` inductive (`AST.lean:37-44`) is the proper
typed representation for non-complete predicates including `f=v` tests.

**Classification:** ***Canonical representation is `CompleteTest := CtxPkt`** ✅
— A total function `FieldName → FieldValueEnum` enforcing totality by
construction. `holdsComplete_iff_eq` (`Packet.lean:218`) proves the
one-to-one correspondence: α holds on σ iff σ = α.

### 3.3 Predicate Syntax (Figure 3, p. 5)

**Question:** Are predicate negation, conjunction, disjunction, true, and false represented?

**Paper (Figure 3, p. 5):** `Pr ::= 0 | 1 | Pr+Pr | Pr·Pr | ¬Pr` — predicates include false (0), true (1), disjunction (+), conjunction (·), and negation (¬).

**Current implementation:**
- `inductive Predicate | pFalse | pTrue | pFieldEq | pAnd | pOr | pNot`  ✅
- `def eval (Pr : Predicate) (σ : CtxPkt) : Bool` with full semantics.  ✅
- Boolean algebra lemmas: `not_not`, `excluded_middle`, `contra`, `deMorgan_or`, `deMorgan_and`.  ✅

**Classification:** ***Already corrected by previous agent.***

The paper's `Pr ::= 0 | 1 | Pr+Pr | Pr·Pr | ¬Pr` does not explicitly list `f=v` as
a predicate constructor (it's a shorthand), but the implementation correctly
makes `pFieldEq` an atomic predicate, which matches the paper's usage where
`f=v` is a basic predicate.

### 3.4 NetKAT AST (dup-free fragment)

**Question:** Does the AST cover the required dup-free NetKAT syntax?

**Paper (Eq. 1, p. 6; §I-B):** `N ::= 0 | 1 | f=v | f←n | α | π | N + N | N·N | N*`
(DyNetKAT uses NetKAT⁻ᵈᵘᵖ, i.e., without `dup`).

**Current implementation:**
```lean
inductive NetKAT
  | drop             : NetKAT                  -- 0
  | id               : NetKAT                  -- 1
  | test             : Predicate → NetKAT      -- Pr (general predicate)
  | completeTest     : CompleteTest → NetKAT  -- α (complete test)
  | assign1          : FieldName → FieldValueEnum → NetKAT  -- f←v (primitive single-field assignment)
  | union            : NetKAT → NetKAT → NetKAT  -- N + N
  | seq              : NetKAT → NetKAT → NetKAT  -- N ; N
  | star             : NetKAT → NetKAT          -- N *
```

The legacy `.assign` constructor (which took arbitrary `CtxPkt → CtxPkt` functions)
has been **removed** (Task 2R-J). Complete assignments π are now represented as
total valuations (`CompleteAssignmentValuation := CtxPkt`) that are compiled to
NetKAT expressions via `completeAssignExpr`, which builds a sequence of `assign1`
operations for every field.

**Classification:** ***Conformant** ✅. The AST includes the paper's primitive
`f←v` (`assign1`) as a basic NetKAT term, and complete assignments are represented
as total valuations (not arbitrary functions).

### 3.5 Denotational Semantics

**Question:** Does the denotational semantics match the paper?

**Paper (Figure 3, p. 5–6; §I-B "Semantics"):**
- `⟦0⟧ = ∅`
- `⟦1⟧ = {(σ,σ)}`
- `⟦f=n⟧ = {(σ,σ) | σ(f) = n}` — but the paper's full semantics operates on **histories** `h ∈ H`, with `⟦N⟧ : N → (H → 𝒫(H))`
- `⟦¬a⟧(h) = {h} \ ⟦a⟧(h)`
- `⟦α⟧ = ∩_{f=v ∈ α} ⟦f=v⟧` (conjunction of field tests)
- `⟦π⟧ = {(σ, π(σ))}`
- `⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧`
- `⟦N₁·N₂⟧ = ⟦N₁⟧ • ⟦N₂⟧` (relational composition)
- `⟦N*⟧ = ⋃ₖ⟦N⟧ᵏ` (reflexive-transitive closure)

**Current implementation:**
```lean
def Semantics (N : NetKAT) : CtxPkt → CtxPkt → Prop :=
  match N with
  | .drop => False
  | .id => σ = τ
  | .test Pr => Pr.holds σ ∧ σ = τ
  | .completeTest α => holdsComplete α σ ∧ σ = τ
  | .assign1 f v => τ = Packet.update σ f v
  | .union n₁ n₂ => Semantics n₁ σ τ ∨ Semantics n₂ σ τ
  | .seq n₁ n₂ => ∃ ρ, Semantics n₁ σ ρ ∧ Semantics n₂ ρ τ
  | .star n => StarClosure (Semantics n) σ τ
```

**Findings:**

| Semantic clause | Paper | Current | Match? |
|---|---|---|---|
| `⟦0⟧` | ∅ | `False` | ✅ |
| `⟦1⟧` | `{(σ,σ)}` | `σ = τ` | ✅ |
| `⟦f=v⟧` | `{(σ,σ) \| σ(f)=v}` | `Pr.holds σ ∧ σ=τ` (via `.test (.pFieldEq ...)`) | ✅ |
| `⟦¬a⟧` | `{h} \ ⟦a⟧(h)` | `¬Pr.holds σ ∧ σ=τ` | ✅ (for single-packet semantics) |
| `⟦α⟧` | `∩_{f=v∈α} ⟦f=v⟧` | `holdsComplete α σ ∧ σ=τ` | ✅ (`holdsComplete` checks all fields) |
| `⟦f←v⟧` | `{(σ, σ[f:=v])}` | `τ = Packet.update σ f v` (`.assign1`) | ✅ |
| `⟦π⟧` | σπ = π (overwrite all fields) | `completeAssignExpr π` → proven `⟦⟧(σ,τ) ↔ τ = π` | ✅ (`completeAssignExpr_sem`) |
| `⟦N₁+N₂⟧` | `⟦N₁⟧ ∪ ⟦N₂⟧` | `∨` | ✅ |
| `⟦N₁·N₂⟧` | relational composition | `∃ ρ, ... ∧ ...` | ✅ |
| `⟦N*⟧` | `⋃ₖ ⟦N⟧ᵏ` | `StarClosure (Semantics n)` | ✅ |

**Classification:** ***Conformant** ✅. All semantic clauses match the paper. The
build succeeds and all theorems are machine-checked with no proof holes.

### 3.6 Kleene Star as Unbounded Closure

**Question:** Is Kleene star represented as unbounded closure?

**Paper:** `⟦N*⟧ = ⋃ₖ⟦N⟧ᵏ` — reflexive-transitive closure. On finite domains this is finite.

**Current implementation:**
```lean
inductive StarClosure {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl : ∀ a, StarClosure R a a
  | step : ∀ {a b c}, R a b → StarClosure R b c → StarClosure R a c
```
This is the standard inductive reflexive-transitive closure — the correct
representation of `⋃ₖ⟦N⟧ᵏ`.  ✅

**Classification:** ***Conformant.***

The star is correctly represented as inductive reflexive-transitive closure.
On a finite packet domain, this terminates (finite number of distinct paths).

### 3.7 Paper Example — `(tp_src = 8);drop`

**Paper reference:** §I-A (running example). The policy `(tp_src = 8);drop`
drops packets with `tp_src = 8` and passes others (the test fails → drop).

**Lean:** `def examplePolicy : NetKAT := .seq tpSrc8Test .drop` where
`tpSrc8Test := .test (.pFieldEq ⟨.tpSrc, .v8⟩)`.

**Python:** `semantics_seq(lambda p: semantics_test(test, p), semantics_drop, p8)`
returns `set()` for `p8` with `tp_src = 8` (test passes, then drop produces ∅).

**Classification:** ***Conformant.***

Both implementations correctly model `(tp_src = 8);drop` as: packets with
`tp_src = 8` are dropped (test passes → drop → ∅), packets with `tp_src ≠ 8`
are also dropped (test fails → ∅). Result is always ∅, matching the paper.

> **Note:** The Python `CompleteTest.holds` treats empty constraints as `True`
> (passes on all packets). This is the paper's predicate `1`, not a complete
> test. The Lean implementation distinguishes these via the separate
> `Predicate` type (with `pTrue`) and `CompleteTest` (total valuation).

---

## 4. Remaining Discrepancies and Unresolved Issues (as of Task 2R-L, 2026-10-17)

### 4.1 Build status

`lake build DyNetKAT` — **SUCCESS** (exit code 0). Build completed successfully.
No compilation errors or proof holes remain. The audit sections below describe
the state **after** the assignment conformance migration (Tasks 2O–2R-L).

### 4.2 Build warnings (non-fatal, pre-existing, not introduced by this task)

| Issue | File:Line | Notes |
|---|---|---|
| `git diff --check` | `Semantics.lean:656` | New blank line at EOF (pre-existing) |
| dupNamespace linter warnings | `AST.lean` (all `NetKAT` constructors) | Pre-existing; do not repair per instructions |
| Unused variable `h` | `Semantics.lean:586` | Pre-existing in `test_assign_same_field` |

### 4.3 Semantic concerns (not build-breaking)

| Issue | Paper Reference | Status |
|---|---|---|
| `holdsFinset` (legacy helper, not a complete test) | Definition 4, p. 8 | **Retained but isolated** — legacy `Finset FieldEq`-based helper for partial field-value tests; not used in `.completeTest` semantics (only `holdsComplete` is referenced at `Semantics.lean:67`). This is a non-canonical helper, not a parallel representation of complete tests. |
| Per-field value domains `Vi` vs. single `Value` | Definition 1, p. 5 | **Minor simplification** — documented, acceptable |
| Semantics over single packets vs. histories | Figure 3, p. 181 | **Equivalent for dup-free** — documented in comments at `Semantics.lean:20-25` |

### 4.4 What remains for Lemma 5 (NOT addressed by Task 2R-L)

- Lemma 5 (normal forms) is the Phase 1 deliverable but is **not yet implemented**.
- `[Fintype CtxPkt]` instance **is established** (`Packet.lean:158-161`); however,
  the star-termination theorem (`star_terminates` — proof that `StarClosure`
  stabilizes in ≤ `|CtxPkt|²` steps) is not yet proven, blocking computable star
  evaluation and normalization of star terms.

---

## 5. Paper Conformance Summary (as of Task 2R-L, 2026-10-17)

| Audit Item | Paper Requirement | Current Status | Classification |
|---|---|---|---|
| 1. Packet model generic? | Definition 1: parameterized over finite fields | Parameterized `Packet F V` + concrete fixture | **Conformant** ✅ |
| 2. Complete tests total? | Definition 4: every field assigned a value | `CompleteTest := CtxPkt` (total function) | **Conformant** ✅ |
| 3. Predicate negation/conj/disj? | Figure 3: `Pr ::= 0\|1\|Pr+Pr\|Pr·Pr\|¬Pr` | Full `Predicate` inductive + eval | **Conformant** ✅ |
| 4. Primitive `f←v` constructor? | Figure 3: `N ::= ... \| f←n \| ...` | `assign1 : FieldName → FieldValueEnum → NetKAT` | **Conformant** ✅ |
| 5. Complete assignments as total valuations? | Definition 4: π = `f₁←v₁ · ... · fₙ←vₙ` | `CompleteAssignmentValuation := CtxPkt`; `applyValuation`; `completeAssignExpr` | **Conformant** ✅ |
| 6. Complete-assignment semantics proven? | Definition 4: σπ = π | `completeAssignExpr_sem` proves `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π` | **Proven** ✅ |
| 7. Single-field assignment semantics? | Figure 3: `⟦f←v⟧ = {(σ, σ[f:=v])}` | `assign1_sem`: `⟦assign1 f v⟧(σ,τ) ↔ τ = Packet.update σ f v` | **Proven** ✅ |
| 8. No arbitrary packet-function constructor? | Definition 4: π is a valuation, not arbitrary function | Legacy `.assign` constructor **removed**; no `assign` in `NetKAT` inductive | **Eliminated** ✅ |
| 9. Semantics match paper? | Figure 3 | All clauses match; build succeeds | **Conformant** ✅ |
| 10. Star as unbounded closure? | Figure 3: `⋃ₖ⟦N⟧ᵏ` | `StarClosure` inductive rtc | **Conformant** ✅ |
| 11. `Fintype` for finiteness? | Lemma 5: "A and Π are finite" | `[Fintype CtxPkt]` at `Packet.lean:158-161`; `Fintype CompleteTest`/`Fintype CompleteAssignmentValuation` also registered | **Established** ✅ |

---

## 6. Recommendations (as of Task 2R-L)

### 6.1 Completed (assignment conformance)

All assignments in the previous (stale) recommendations have been addressed:
- ✅ Legacy `CompleteAssignment := CtxPkt → CtxPkt` and `applyAssign` removed.
- ✅ `assign1` constructor added as paper primitive `f←v`.
- ✅ `CompleteAssignmentValuation := CtxPkt` (total valuation) as sole representation.
- ✅ `completeAssignExpr` builds compound assignments from `assign1`.
- ✅ `completeAssignExpr_sem`, `assign1_sem`, `assign_list_sem`, `fieldEnum_updates_complete`
  all proven — no `sorry`/`admit`/`axiom`.
- ✅ Build passes (`lake build DyNetKAT` exit code 0).
- ✅ No dangling references to legacy types.

### 6.2 Remaining (out of scope for Task 2R-L)

- Implement Lemma 5 (normal forms) — Phase 1 deliverable, requires `E_NK` derivability relation.
- Prove `star_terminates` — the theorem that `StarClosure` stabilizes in ≤ `|CtxPkt|²` steps on finite domains (blocks computable star evaluation and star-term normalization).

> **Note:** `[Fintype CtxPkt]` (including `Fintype CompleteTest` and `Fintype CompleteAssignmentValuation`) **has been established** (`Packet.lean:158-200, 258-260`) in a subsequent task. This recommendation is retained from the Task 2R-L perspective but is now satisfied.

---

## 7. Build Preservation

**Yes.** The working-tree changes (now compiling successfully) are conceptually
sound and align with the paper. They correctly:

- Parameterize the packet model over generic finite types.
- Introduce the `Predicate` type matching Figure 3.
- Represent `CompleteTest` as a total valuation (`CompleteTest := CtxPkt`).
- Represent `CompleteAssignmentValuation` as a total valuation (dual of `CompleteTest`).
- Add `assign1` as the paper's primitive single-field assignment `f←v`.
- Add `completeAssignExpr` to compose single-field assignments into complete assignments.
- Add Boolean algebra lemmas (BA-EXCL-MID, BA-CONTRA, De Morgan).
- Add Kleene algebra and packet algebra laws.
- Prove `completeAssignExpr_sem`, `assign1_sem`, `assign_list_sem`,
  `fieldEnum_updates_complete` — no `sorry`/`admit`/`axiom`.

The changes should be **preserved as-is**. Do not revert to the Phase 1 base
(committed HEAD), which lacks the `Predicate` type and the complete test/assignment
distinction.

---

## 8. Historical follow-up

Task 2R-L deferred the finite instance and Lemma 5. The finite instance now
exists. The current roadmap above records the remaining general-schema,
derivability and scalability obligations.

## Optional / experimental tooling

KATch correspondence, differential checks and candidate replay are external
experiments. Their availability and performance are outside core semantics,
E_NK/E_DNK, normalization, completeness, certified analysis and project
completion. The core path interprets NetKAT in KATLean and proves results
in Lean. Import `DyNetKAT.Experimental` to opt into the preserved backend
modules. Standalone core imports exclude them.

### Future acceleration experiments

A future optional experiment may evaluate a certificate architecture in
which a search engine produces a witness or a closed symbolic relation and Lean checks
it. Positive reachability needs a genuine path witness. Zero,
equivalence and waypoint inclusion need coverage or invariant
certificates sufficient to justify universal claims. A star certificate
needs both reachability and closure evidence for exactness. Specify
completeness on the supported query class and keep the checker, parser
and translation in the experimental proof chain. Benchmark candidate generation and checking
at increasing topology sizes and record certificate size and generation
and checking costs where applicable.

### External comparison record

DyNetiKAT v1.1 calls `netkat-idd` by default and also contains an
adapter for `netkat-automata`. Its IDD adapter derives a common
bit width for a comparison from numeric literals and encodes them
in binary. KATch is the separate PLDI 2024 symbolic verifier used
for differential checks in this repository. Backend domain defaults,
negation, bit widths and identity on unmentioned fields must match
the intended finite input universe. In particular, four-value
PA-MATCH-ALL equals identity in Lean and differs from unguarded identity
over arbitrary integer ports. The Lean `KatchSemantics` model is a
semantic bridge, with executable agreement checked on sample inputs.

The working-tree differential corpus ran against the local KATch
checkout at `1af6d337bd45d3d95a32efd89b32fbdd76ee7efa`. All 18 assertions
matched, including the comparison with the restricted-domain guard
removed. This exercises a finite corpus. General compiler/backend
correspondence and scalable parity remain open.
[KATch paper and methods](https://arxiv.org/abs/2404.04760).

### Executable common fragment and KATch domain

| Lean syntax | Evaluator | Zero and equivalence | Use in the safety pipeline |
|---|---|---|---|
| `drop` | Empty output set | Supported | Empty head contribution and zero comparison |
| `id` | Input singleton | Supported | Accepted as a policy or query operand |
| `test` | Predicate on the input packet | Supported | Ingress and egress tests, plus tests in supplied policies |
| `completeTest` | Equality of all four fields | Supported | Accepted in supplied policies and in normal-form summands |
| `assign1` | Update one field | Supported | Accepted in supplied policies and in complete-assignment expressions |
| `union` | Union of output sets | Supported | Graph head unions the collected policies |
| `seq` | Relational composition | Supported | Composes ingress, extracted head and egress |
| `star` | Reflexive-transitive closure | Supported | Accepted in all supplied policy positions |

The `test` row covers `pFalse`, `pTrue`, `pFieldEq`, `pAnd`, `pOr`, and
`pNot`. Preprocessing preserves the NetKAT prefix labels it retains. Head
adds unions and drop, tail carries the original labels into the continuation,
and the safety queries add composition. All of these are in the verified
finite evaluator's domain.

`eval_correct` identifies the executable output set with the denotation.
`execute_star_eq_boundedStar` proves that early stopping at a fixed point
gives the same result as the iteration used in the cardinality proof.
`execute_star_correct` identifies that result with unbounded closure.
`netkatIsZero_history_correct` and `netkatEquiv_history_correct` lift
the decisions to histories over the same packet universe.

`katchSemantics_encode` embeds the four-field packets into integer-valued
packets, with values (0, 1, 8, 9) at each field. The embedding preserves
tests and assignments, then union, sequencing, and star. Every execution
from an encoded packet stays inside the image, including intermediate
packets. `netkatEquiv_katch_restricted` and `netkatIsZero_katch_restricted`
characterize the two queries on this image. `completeTestExpr_correct`
justifies translation of a complete test to four primitive tests.

The common fragment is dup-free standard NetKAT with negation on tests.
KATch's queries apply to the corresponding trace semantics. Without
duplication the only observable output of a run is the final packet.
An input guard requiring each field to be in the four-value domain
gives the restricted query even when KATch permits other values.
For example, the sum of four port tests is identity in the restricted
domain and fails to match identity on unrestricted integer packets.
The Lean statements concern the semantics of the queries. The
[differential corpus](../lean/test_katch_differential.lean) exercises the
published KATch implementation independently.
[KATch paper](https://arxiv.org/abs/2404.04760).

### Checked backend interchange on CtxPkt

The existing differential test generated NKPL assertions from
`netkatEquiv` and compared them with KATch in a separate run. There was
no production subprocess adapter, cached certificate store, or
proof-replay interchange. The pinned differential run described above
is historical. The published NKPL interface supports equivalence and
inequivalence assertions, symbolic packet sets through `forward` and
`backward`, and Graphviz visualization. The paper documents printing
counterexample input sets with backward flow over symmetric difference.
The published interface reviewed here provides no documented canonical
proof-certificate format for those commands. See the [artifact README](https://github.com/julesjacobs/KATch) and [paper](https://arxiv.org/abs/2404.04760).

`KatchExport` reuses the existing corpus printer. The supported
fragment is the complete current dup-free AST, including Boolean tests,
complete tests, assignments, union, composition, and star.
`katchSemantics_encode` establishes the mathematical translation from
the four-field `CtxPkt` domain into integer-field packet relations. NKPL
formatting and the backend parser are outside this theorem.

`BackendCertificate.lean` accepts these JSON candidate shapes:

```json
{"kind":"counterexample","input":[8,1,0,0]}
{"kind":"relation","pairs":[[[8,1,0,9],[0,1,0,9]]]}
```

Each line above is a separate JSON document. Packets list source,
destination, switch, and port, with values in 0, 1, 8, and 9. Relation
pairs list input then output. Omitted pairs denote absence and
duplicates denote the same edge. Invalid JSON, tags, packet lengths and
out-of-domain values fail decoding. Candidate acceptance independently
checks the original Lean policies. A backend Boolean answer is never
used as evidence.

The optional replay entry point is available from `lean/`:

```sh
lake env lean --run test_backend_certificate.lean emit-witness > witness.nkpl
lake env lean --run test_backend_certificate.lean emit-row > row.nkpl
katch run witness.nkpl
katch run row.nkpl
lake env lean --run test_backend_certificate.lean check-witness witness.json
lake env lean --run test_backend_certificate.lean check-relation relation.json
lake env lean --run test_backend_certificate.lean
```

For witness replay, choose a concrete in-domain input from the printed
symbolic set and write the first JSON shape. For relation replay, extract
the output set of the singleton-input query. The emitted example policy
begins with a complete test, so all other input rows are empty.
For general policies a full relation requires all input rows. Conversion
of symbolic output to JSON is manual at this checkpoint. It is outside
the proof boundary. Timeout, unavailability and conversion failure
can be passed as an absent candidate to `decideWithBackend` for exact
fallback. A rejected candidate uses the same fallback.

The relation replay tests use independent fixtures in the interchange
format. The benchmark measures the Lean validation and fallback paths.
A negative witness requires two evaluations on one input, and ordinary
inequivalence may itself stop early. Positive comparison validates every
input for both policies and currently offers no verified speedup.

### Optional KATch driver and equational checking

The [pinned KATch source](https://github.com/julesjacobs/KATch/tree/1af6d337bd45d3d95a32efd89b32fbdd76ee7efa)
was inspected from the archive for revision
`1af6d337bd45d3d95a32efd89b32fbdd76ee7efa`. It declares Scala 3.3.1,
sbt 1.9.6, sbt-assembly 0.15.0, and FastParse 3.0.2. The historical
Dockerfile uses OpenJDK 8. The local OpenJDK 17 build with writable
temporary sbt directories stopped during sbt 1.9.6 dependency retrieval
because outbound sockets were unavailable. A subsequently built assembly
from the pinned checkout was used for live replay through a direct-JAR
launcher under OpenJDK 25.0.5.0.3.

`Main.scala` dispatches `run FILE` to `Runner.runTopLevel`, which reads
one statement per line and writes timing files under the working
directory's `results/`. `Runner.scala` emits an ANSI-colored,
path-and-line-specific pass on stdout. On a failed assertion it throws
a `Throwable` with a different path-and-line-specific message and
summarized operands. Processing stops at the first failure. Parse
errors, missing files, undefined variables and the bisimulation
iteration limit use separate exceptions. The upstream shell launcher
runs cleanup after Java, so its final exit status can mask a JVM failure.

To reproduce, clone [upstream](https://github.com/julesjacobs/KATch)
outside this repository, check out the exact revision in detached mode,
verify it with `git rev-parse HEAD`, and run `sbt -batch assembly`.
Use a launcher with an absolute JAR path that preserves the JVM exit
status. The driver provides an isolated working directory with
`results/` and passes an absolute NKPL path. A container launcher must
expose both to the container.

```sh
# In an executable launcher script, substitute the assembled JAR path.
exec java -Dfile.encoding=UTF-8 -Xss10m -jar /path/to/KATch-assembly-0.1.0-SNAPSHOT.jar "$@"
```

```sh
(cd lean && lake build DyNetKAT.Experimental)
python3 scripts/katch_replay.py both --katch /path/to/pinned-launcher --require-backend
(cd lean && lake env lean --run test_backend_certificate.lean)
```

For a direct protocol check, run the launcher from a scratch directory
with `results/` present. Use separate files for `check ⊤ ≡ ⊤`,
`check ⊤ ≡ ⊥`, `check ⊤ ≡`, and `check undefined ≡ ⊤`, and invoke
another absent `.nkpl` path. Capture stdout, stderr and exit status
separately. Run a two-line file containing the passing assertion then
the failing assertion to verify line numbers and early termination.
Use `--timeout 0.001` on the replay driver to exercise the operational
deadline. Run the existing differential corpus to exercise the printer,
including Boolean tests and complete packet tests, and the row exporter
to exercise the concrete-input query:

```sh
# Run from the DyNetKAT-Lean checkout.
scratch=$(mktemp -d)
mkdir "$scratch/results"
(cd lean && lake env lean --run test_katch_differential.lean) > "$scratch/common.nkpl"
(cd lean && lake env lean --run test_backend_certificate.lean emit-row) > "$scratch/row.nkpl"
(cd "$scratch" && /path/to/pinned-launcher run common.nkpl row.nkpl)
```

The driver calibrates with `check ⊤ ≡ ⊤` and its complement
`check ⊤ ≢ ⊤`. It validates the exact path, line, and diagnostic and
requires opposite results on complementary probes. The local JVM emits
a four-line Scala `LazyVals` warning on startup. The parser consumes
only that recognized leading block and validates the remaining stderr.
It declines unrecognized output and process failures and uses
exact Lean fallback when available. A failed Lean process yields
operational unknown. The firewall/star search performs a domain probe,
two narrowing probes per field, and a final concrete-packet probe. Each
uses the assertion and its complement, for 22 launcher calls including
calibration. Lean checks the nominated input. The larger positive star
pair uses four launcher calls including calibration. Its hint triggers
the existing Lean common-term check.

`Bisim.bisimPrim` uses a local work queue and maps residual pairs to
processed symbolic packet sets. It returns a Boolean and discards those
structures. The CLI's failed assertion reports operands without a
counterexample. `Bisim.forward` and `Bisim.backward` return symbolic
sets internally, but the CLI's display truncates their pretty-printed
form. `Bisim.ε` and `Bisim.δ` expose immediate symbolic packet
transformations and labeled derivatives. `Viz.scala` emits automaton
and per-label decision diagrams for one policy, with generated labels
and no source-term correspondence or bisimulation certificate.
An upstream exporter could expose the residual-pair map on successful
completion and serialize the SP/SPP nodes and derivatives. Lean would
still need to check their correspondence to the original terms and the
symbolic bisimulation obligations. That proof layer is beyond a small
launcher change. There is no certificate export in the pinned CLI.

`EquationalCertificate.lean` checks a proposed common term after
eliminating sequential identities and additive zeros, including under
star. The certificate is a single NetKAT term supplied as a typed Lean
value. The demo supplies its own common term when the backend hint
arrives. KATch does not produce this term. The checker uses existing
`E_NK` derivations and syntactic equality, with work driven by policy
syntax rather than the size of the packet universe. The checker is
incomplete and intentionally small. Complete normal-form relation
checking remains exhaustive. General symbolic partitions, diagrams,
and automata would require coverage and term-correspondence proofs
before they could replace this reference check.

On the firewall-derived star pair with 96 redundant compositions, one
Lean process measured 0.24 ms to generate the common term, 0.08 ms to
check it, 205 ms for exact equivalence and 228 ms for exhaustive shared
relation checking. On the negative firewall/star fixture, JSON witness
decoding and checking took 0.75 ms and exact inequivalence took 0.37 ms.
These are fixture timings, excluding startup and KATch. The optional
runner reports candidate, backend probe wall time,
Lean replay wall time, and total round-trip time. Protocol tests use a subprocess double and
exercise genuine Lean replay. The real pinned launcher also passed
`both --require-backend` with both star fixtures and neither case
using fallback. The positive hint selected the locally supplied
common term `(@port=0 ⋅ @port←1)⋆`. The negative probes retained
the lower half at each split and nominated `[0,0,0,0]` in field order
`src,dst,sw,port`. Lean returned `checkedEquational` and
`checkedCounterexample`, respectively. In one run, positive probe,
Lean replay and total times were 1.41 s, 2.60 s and 6.59 s. Negative
times were 7.40 s, 2.68 s and 12.67 s. Probe times include JVM startup
for each invocation. Total time includes Lean policy export.

The proof boundary consists of the Lean semantics,
`katchSemantics_encode`, the relation, witness and equational checkers,
and their soundness proofs. The KATch executable, textual serializer,
subprocess and output parser, candidate generation and performance
measurements carry no proof authority. Communication labels retain
literal payload syntax.
