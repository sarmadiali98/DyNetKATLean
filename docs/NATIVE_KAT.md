# Native KAT equivalence: first certified layer

## Status and exact scope

Current development baseline: `69cc3a6 add verified native relational KAT equivalence solver`.
`import KATLean.Native` exposes an executable, sound-and-complete decision
procedure for guarded-string equivalence and equivalence in **all relational
KATLean models**, over finite primitive-test and action alphabets. The native
proof imports Mathlib and KATLean only. It never imports `CtxPkt`, its evaluator,
NetKAT Derives, or any external backend.

This is a generic KAT semantic decision layer, not yet a packet-aware NetKAT
solver. Equality in every arbitrary abstract `KAT K B`, or syntactic derivability
from KA/BA axioms, has not been proved equivalent to guarded-language equality
here. The classical KAT equational completeness theorem remains an explicit
additional obligation if that stronger interface is wanted. No such theorem is
assumed by the implementation.

The existing NetKAT equivalence, normalization and analysis routes are preserved.
They still use the concrete finite packet model. Replacing those routes requires
the deferred packet-specific milestone, after algebraic completeness; this checkpoint does not claim their
independence from packet enumeration.

## Symbolic guards and exact completeness audit

This update removes Boolean truth-assignment enumeration from the public native
solver. It **does not close the algebraic completeness gap**. It is a verified
symbolic relational-solver sub-milestone, not completion of the requested generic
algebraic solver milestone. Do not start the NetKAT packet frontend yet.

| Meaning | Formal status |
|---|---|
| Equality in one concrete relation model | Consequence of relational equivalence; its converse is false in general |
| Equality in all KATLean relational models | `RelationalEquivalent` |
| Guarded-string language equality | `LanguageEquivalent`; `relational_iff_language` proves equivalence with all-relational equality |
| Derivability from pure KAT equations | Independent inductive `Equational`; 15 KA, 6 BA, 4 test embeddings and structural/congruence rules |
| Validity in all abstract KATLean KATs | `AlgebraicallyEquivalent` |
| Equational derivation → all abstract models | `Equational.algebraic_sound`, by direct KATLean/Mathlib law reuse |
| All abstract models → all relational models | `AlgebraicallyEquivalent.relational` |
| Equational derivation → symbolic solver positive | `Equational.solver_positive` |
| Pure KAT derivation → existing NetKAT Derives | `nativeEquational_derives`, by syntactic substitution, no normalization/oracle |
| Solver positive / language equality → pure KAT derivation | **Open** |
| Solver positive / language equality → all abstract KAT validity | **Open** |

`Equational` is not defined using solver acceptance or relational validity.
No completeness implication is inserted as an axiom, constructor or hypothesis.
The NetKAT substitution bridge maps actions to arbitrary policies and tests to
predicates; it is not the deferred packet-aware frontend in the other direction.
NetKAT packet equations cannot be added to generic KAT without their hypotheses.

### Completeness construction audit

The installed Mathlib v4.19.0 supplies KA axioms and automata semantics, but no
KA/KAT equational completeness theorem or matrix-star KA instance usable here.
The existing finite-packet normalization theorem is neither a generic KAT
completeness proof nor an acceptable replacement for that proof.

The [formal Coq completeness module](https://perso.ens-lyon.fr/damien.pous/ra/html/RelationAlgebra.kat_completeness.html)
reduces KAT to guarded expressions and then uses a separately formalized KA
completeness theorem. Its implementation is not a Lean theorem. The
[development notes](https://perso.ens-lyon.fr/damien.pous/ra/)
also report that tying algebraic completeness directly to the optimized decision
algorithm complicated the proof. Two viable Lean routes remain: formalize
finite-system elimination/KA completeness and then guarded-expression reduction,
or establish an algebraic finite-automaton simulation theorem. Neither is proved
in this checkpoint. The latter may reuse our finite continuation closure, but
semantic bisimulation by itself does not justify abstract algebraic equality.

### Canonical Boolean representation

`Boolean.Diagram n` is a pure ordered decision tree. The index fixes variable
order: a node consumes the first variable and its children have index `n`;
`skip` ignores a variable without duplicating a subtree. Constants are leaves.
`Reduced` excludes equal node branches and skips above constant leaves. Smart
constructors preserve reduction. `canonical` proves that reduced trees with the
same Boolean function are equal. `Guard` carries the reduction proof.

`apply_correct`, `compile_correct` and `sat_correct` prove Boolean-operation,
test-compilation and satisfiability semantics. Satisfiability traverses the tree;
it does not enumerate assignments. Equality compares canonical trees. Implication
is unsatisfiability of conjunction with a negation. No unique table, DAG sharing
or sophisticated BDD package is assumed. Worst-case tree size can still be
exponential, as for Boolean decision diagrams generally.

`BooleanAlphabet T` supplies an executable numbering into `Fin n`; `Fin n` has a
standard instance. Public solver APIs now require this numbering and `Encodable`
primitive alphabets, rather than a `Fintype T` valuation universe. Actions still
form a finite alphabet. The expression/test syntax itself is unchanged.

### Symbolic derivatives and search

`derivativeRegions_correct` proves that guarded regions represent the old
one-step derivatives exactly. `Covers` requires both soundness of every region
and coverage of every valuation. Overlaps are allowed, but soundness forces
identical successors wherever two guards overlap. `combine` intersects guards
symbolically and discards unsatisfiable intersections using diagram SAT.
`transitionRegions_correct` lifts this property to subset states.

`sameOutput` compares canonical output guards. `successors` ranges over actions
and satisfiable symbolic regions, never over `T → Bool`. `mem_successors_iff`
relates these regions to semantic transitions. Thus the existing support-based
finite bound is reused; `explored_closed` proves search saturation. Relational
soundness and completeness, including `decideEquiv_correct`, remain proved.
`inequivalent_witness` still gives existence, not executable path extraction.

The old valuation-based implementation is retained in `Native/Explicit.lean`,
namespace `KATLean.Native.Explicit`, solely as a regression oracle. It is not
imported by `KATLean.Native` or the DyNetKAT core. Differential testing is not used
in the new correctness proof. `Ordering.lean` supplies compact injective syntax
codes for executable ordering; structural insertion sort preserves kernel
reduction for `by decide` proof examples.

**KATch:** not used by the core. **CtxPkt exhaustive enumeration:** not used by
the native solver. **Boolean valuation enumeration:** removed from the core
native solver. Existing concrete NetKAT C/D dependencies listed below remain;
no packet migration is claimed.

## Construction audit and choice

The installed Mathlib is v4.19.0. Its `Computability.RegularExpressions` supplies
regular expressions, derivatives, language semantics and correct word membership
(`rmatch_iff_matches'`). DFA, NFA and epsilon-NFA modules provide language semantics,
subset construction and epsilon elimination. They do not supply an immediately
usable executable KAT equivalence procedure with Boolean guards and a proved
finite derivative closure.

| Candidate | Proof consideration | Decision |
|---|---|---|
| Brzozowski derivatives | Requires a finite quotient or normalization modulo union laws | Not selected for the first layer |
| Antimirov partial derivatives | Finite syntactic continuations can be proved closed structurally; subset states handle nondeterminism | Selected |
| Thompson epsilon automata | Viable, but guarded epsilon transitions add a compiler and epsilon-closure correctness proof | Deferred |
| Symbolic decision diagrams | Avoid truth-assignment enumeration; require canonical Boolean operations and SAT proofs | Implemented as pure ordered reduced trees; DAG sharing deferred |
| Existing Mathlib automata | Useful infrastructure; adapting Set-based states and guarded fusion still requires executable finiteness proofs | Small dedicated Finset layer used |

References: [Pous, *Kleene Algebra with Tests and Coq Tools for While Programs*](https://arxiv.org/abs/1302.1737)
for guarded languages, completeness and partial-derivative verification;
[Pous, *Symbolic Algorithms for Language Equivalence and KAT*](https://perso.ens-lyon.fr/damien.pous/symbolickat/)
for Boolean symbolic automata; and
[Kozen and Smith, guarded-string completeness](https://www.cs.cornell.edu/kozen/Papers/ags.pdf).
The algorithm uses standard published constructions. No KATch implementation is
copied or called.

## Syntax, guards and semantics

`Test T` is Boolean syntax (false, true, atom, conjunction, disjunction,
complement), with decidable syntactic equality. `Expr T A` has zero, one,
actions, tests, union, composition and star. Its interpretation is defined in
any existing KATLean `KAT`; no duplicate KA class is introduced.

An atom is an abstract truth assignment `T → Bool`. A guarded word consists of
an initial atom and a list of action/next-atom pairs. `Accept` is an independent
inductive guarded-language semantics: composition fuses the shared boundary
atom, and star admits any finite number of iterations. Empty iterations are
allowed. These words record generic KAT action traces, not NetKAT packet histories
or a new DyNetKAT process language.

`nullable` returns a Boolean formula. Guards compile to canonical reduced ordered decision trees. Unused variables
are skipped. Operations, semantic equality and SAT are symbolic, without
generating abstract truth assignments or concrete packet valuations. Tree
sharing and support-minimized numbering are not yet implemented.

## Derivatives, termination and decision

`derivative e atom action` computes an Antimirov set. The central theorem is:

```lean
Accept e atom ((action, next) :: word) ↔
  ∃ rest ∈ derivative e atom action, Accept rest next word
```

`nullable_correct` proves acceptance of the empty word. `continuations e` is a
structurally computed finite set closed under derivatives. `support e` adds the
initial expression. Automaton states are finite subsets of this support.
`transition_correct` lifts derivative correctness to subset states.

The search saturates pairs of subset states, stopping at a fixed point. It uses
the proved bound `2 ^ ((support p).card + (support q).card)`, not an arbitrary
cutoff. A strict increase consumes at least one possible pair. The powerset
carrier appears only in the proof; executable search constructs reachable pairs,
not the whole powerset. The implementation expands the whole visited set on each
round, so it is less efficient than a frontier-only worklist.

`decideLanguageEquiv_correct` proves the exact Boolean/language correspondence.
`interp_iff_accept` relates accepted guarded words and action paths to the
existing KATLean relation interpretation for arbitrary packet/state types.
A faithful trace relation model proves the converse without assuming model
completeness. Thus:

```lean
decideEquiv p q = true ↔ RelationalEquivalent p q
```

`decideEquiv_sound` and `decideEquiv_complete` are separate corollaries.
`inequivalent_witness` proves existence of a distinguishing guarded word on
failure. Executable witness extraction and predecessor storage are not yet
implemented.

## Modules and tests

| Module under `lean/KATLean/Native/` | Responsibility |
|---|---|
| `Syntax.lean` | Boolean and expression syntax, arbitrary KAT interpretation, nullable |
| `Language.lean` | Guarded words, inductive acceptance and nullable correctness |
| `Derivatives.lean` | Partial derivatives, correctness, finite continuation closure |
| `Automaton.lean` | Subset states, outputs, transitions, support finiteness |
| `Search.lean` | Finite saturation and its cardinality-bound proof |
| `Boolean.lean` | Canonical reduced ordered Boolean diagrams, operations and SAT |
| `Ordering.lean` | Compact injective syntax codes and executable ordering support |
| `Symbolic.lean` | Covered symbolic derivative regions and output guards |
| `Decision.lean` | Symbolic pair search, guarded-language soundness and completeness |
| `Explicit.lean` | Old valuation enumeration, regression-only import |
| `Equations.lean` | Pure KAT axioms, abstract soundness and derivation-to-solver theorem |
| `Model.lean` | Arbitrary KATLean relational interpretation correspondence |
| `Correctness.lean` | Faithful trace model, final relational correctness and witness existence |

`lean/KATLean/Native.lean` is the separate public surface; `DyNetKAT.lean`
exports it. The algebra umbrella stays below the native solver, avoiding cycles.
`test_native_kat.lean` covers zero versus one, idempotence, associativity,
distributivity, both star unfolds, a star-induction consequence, Boolean
complement and contradiction, star denesting, nested/nullable stars,
inequivalence, multiple derivative states, empty alphabets and independent tests.
It checks that the native environment contains no concrete packet evaluator or
backend declarations, and prints axioms for the main results. The audited results
use only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with
no proof holes or new axioms.

For `(a+b)* = a* (b a*)*` the regression reports supports of size 2 and 2,
and 2 explored state pairs. Actions are finite; guards are now symbolic.
At the prior explicit-valuation checkpoint, one full focused-test Lean invocation took 8.82 seconds and about 1.25 GiB
peak RSS; this includes elaboration, kernel proofs, import and axiom audits, and
is not a solver-only benchmark. No scalability claim follows from it.

## Existing packet enumeration audit

Categories: A = regression/example; B = concrete evaluator; C = proof foundation;
D = current equivalence/analysis decision path. A module may have multiple roles.

| Existing location/use | Category | Status |
|---|---|---|
| `NetKAT/Packet.lean`: `Fintype CtxPkt`, cardinality 256 | B/C | Concrete schema and legacy finite-model proofs retained |
| `NetKAT/Evaluator.lean`: finite reachability, bounded star and stabilization | B/C | Exact concrete evaluator retained; not imported by native proofs |
| `NetKAT/Decision.lean`: `netkatEquivAt`, `netkatEquiv`, `netkatIsZero` | D (correctness C) | Legacy concrete decision path; replacement pending |
| `NetKAT/NormalForm.lean`, `Normalization.lean`: `Finset.univ` over complete tests, `packetList`, complete pair sums and Lemma 5 | C | Existing fixed-model normalization proof retained; symbolic replacement pending |
| `NetKAT/Interpretation.lean`: `execute_katInterp`; history/evaluator bridges and process `NetKATBridge.lean` | B/C | Semantics and finite-evaluation correspondence retained; no native proof dependency |
| `NetKAT/Axioms.lean`: decidable-equivalence to derivation bridge | C/D | Existing concrete bridge retained; generic native results do not yet feed it |
| `DyNetKAT/GraphNormalization.lean`, `SafetyCheck.lean`: zero/equivalence calls | D | Existing admitted-program analysis retains concrete NetKAT dependencies |
| Optional backend/equational certificates: complete packet relation checks | B/D experimental | Preserved outside core imports; unused by native solver |
| `test_*.lean` concrete policy comparisons and examples | A | Useful future differential oracle |

Therefore the **new native correctness proof** is independent of all concrete
packet enumeration. The **existing project as a whole** still contains C/D
uses and does not yet meet the long-term no-enumeration architecture.

## Next obligations

1. **Close the generic algebraic completeness gap before packet work.** Prove
   relational/guarded-language equality implies `Equational`, or abstract KAT
   validity with a proved derivation bridge. No such result is available yet.
2. Verified packet constraints and updates using KATLean packet laws, without
   enumerating packet valuations. Opaque generic actions cannot establish
   assignment overwrite or field commutation.
3. Existing NetKAT AST frontend with semantic preservation and complete
   packet-aware equivalence, then a solver-to-Derives/E_NK bridge.
4. Replace legacy core C/D uses; retain concrete evaluation as regression/model
   tooling. Preserve Program/Residual and literal communication-payload boundaries.
5. Add executable counterexamples, DAG sharing and a frontier worklist after
   correctness; benchmark independently of elaboration.

KATch is experimental only and unused. No DyNetKAT SOS rule, admission predicate,
communication payload rule, or existing normalization algorithm changes here.

## Prior checkpoint verification (69cc3a6)

- `lake build DyNetKAT`: passed.
- All 37 `test_*.lean` files: passed, including existing normalization,
  equations, grammar-domain, safety and optional-backend regressions.
- Direct `lake env lean` checks of all eight implementation modules and
  `KATLean/Native.lean`: passed; focused native regression passed.
- `scripts/verify.sh`: passed (Lean build and all 35 Python tests).
- `git diff --check`: passed.
- Representative theorem axiom output is described above; no new axiom,
  `sorry`, `admit`, external oracle or packet enumeration enters native correctness.

No commit or push was made. The existing `output/` directory was not modified.

## Symbolic checkpoint performance sanity

The focused regression includes 144 differential comparisons against the old
explicit solver over a two-test alphabet. This oracle is imported by the test
only and does not occur in symbolic correctness. A separate native-only test
checks that neither the oracle nor packet/backend declarations are imported,
and inspects the proof/algorithm bodies for their intended dependencies.

| Example | Expression nodes including test syntax | Support sizes | Explored subset states (left/right) | State pairs | Initial guard regions across actions | Output guard nodes (left/right) | One solver invocation |
|---|---:|---|---|---:|---:|---|---:|
| Distributivity | 12 | 3 / 4 | 4 / 4 | 4 | 2 | 1 / 1 | 7.64 ms |
| Star denesting | 12 | 2 / 2 | 2 / 2 | 2 | 2 | 1 / 1 | 2.36 ms |
| Distribution through a conjunction of 64 tests | 397 | 2 / 2 | 3 / 3 | 3 | 2 | 129 / 129 | 380 ms |

These are single `#eval` sanity runs, not comparative benchmarks. The clock
covers the decision call; metrics are calculated afterward. Concurrent checks
and VM/compiler effects can change timings. A conjunction over 64 tests has
`2^64` possible valuations, but its compiled diagram has 129 nodes. The tests
verify that size and check equivalent/inequivalent policies using it.

During development, higher-order recursion for indexed variable construction
caused severe slowdowns on large indices. Direct first-order recursion fixes
that path. Boolean apply short-circuits constant operands, and compact token
codes replace whole-tree natural-number pairing codes in state ordering.
The final large-guard regression passes without a timeout or semantic cutoff.

The axiom audit covers Boolean canonicity, compilation and SAT, symbolic
regions, finite search, relational soundness/completeness, abstract soundness
of pure equations and the existing Derives embedding. Only standard Lean
axioms occur; `nativeEquational_derives` uses no axioms. There is no axiom-audited
algebraic completeness theorem because that theorem has not been proved.

## Verified symbolic sub-milestone

Baseline: `69cc3a6`. Verification completed:

- `lake build DyNetKAT`: passed.
- All 38 `test_*.lean` files: passed.
- Direct compilation of all nine new/changed native and derivation-bridge
  modules: passed.
- `scripts/verify.sh`: passed, including all 35 Python tests.
- `git diff --check`: passed.
- Focused Boolean, large-alphabet, differential, dependency-body and axiom
  regressions: passed.

This is a commit-sized symbolic Boolean sub-milestone. It is **not** the full
requested algebraic-completeness checkpoint. Suggested message:
`replace native KAT valuation enumeration with symbolic guards`.
The native solver is not yet ready to become the NetKAT equivalence engine.
No packet-aware frontend, concrete evaluator replacement, SOS modification,
commit or push was performed; `output/` was not modified.
