# Native KAT equivalence: first certified layer

## Status and exact scope

Baseline: `2e9d206 make KATLean the foundation of NetKAT derivations`.
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
the next, packet-specific milestone; this checkpoint does not claim their
independence from packet enumeration.

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
| Symbolic BDD automata | Can avoid enumerating truth assignments, but require a verified Boolean canonicalization layer | Future performance work |
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

`nullable` returns a Boolean formula. Guards remain formulas throughout
construction; this first implementation compares outputs and computes successors
over all abstract truth assignments. Cost is exponential in the number of
primitive tests. It does **not** enumerate concrete packets. There is no BDD
canonicalization, formula semantic hashing, or support-minimized alphabet yet.
The finite type supplied as `T` should contain the relevant primitive tests;
unused tests still increase the cost.

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
| `Decision.lean` | Executable pair search, guarded-language soundness and completeness |
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
and 2 explored state pairs, over 2 actions and 2 abstract truth assignments.
One local full focused-test Lean invocation took 8.82 seconds and about 1.25 GiB
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

1. Verified packet constraints and updates using KATLean packet laws, without
   enumerating packet valuations. Opaque generic actions alone cannot establish
   assignment overwrite or field commutation.
2. Existing NetKAT AST frontend with semantic preservation and complete
   packet-aware equivalence, then a Derives/E_NK bridge.
3. Replace legacy core C/D uses; retain concrete evaluation as regression/model
   tooling. Preserve the Program/Residual and literal communication-payload boundaries.
4. If needed, formalize abstract KAT equational completeness; the present final
   theorem quantifies relational KATLean models explicitly.
5. Add executable counterexamples, Boolean sharing and a frontier worklist after
   correctness; benchmark independently of elaboration.

KATch is experimental only and unused. No DyNetKAT SOS rule, admission predicate,
communication payload rule, or existing normalization algorithm changes here.

## Checkpoint verification

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
