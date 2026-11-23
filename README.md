# DyNetKATLean

The mathematical formalization of [DyNetKAT arXiv v4](https://arxiv.org/abs/2102.10035v4)
is complete under the [documented typed scope](docs/PAPER_CONFORMANCE.md),
including the distributed-controller and FatTree case studies. The scope
records the unresolved paper ambiguity in Definition 17 (nested negation).
DyNetiKAT v1.1 tooling and empirical parity are a separate phase.

## Clone the repository

```sh
git clone https://github.com/sarmadiali98/DyNetKATLean.git
cd DyNetKATLean
```

## Verify the release

The mathematical packages are in `packages/`. Their Lake dependency chain is
Mathlib → KATLean → NetKATLean → DyNetKATLean. The `lean/` workspace adds the
compatibility library, CLI, frontend, and examples.

With Elan and Python 3.9 or later installed, run the following from the
repository root. Install pytest in your Python environment for the full run.

```sh
bash scripts/verify-release.sh KATLean
bash scripts/verify-release.sh NetKATLean
bash scripts/verify-release.sh DyNetKATLean
bash scripts/verify-release.sh
```

Each package check runs its native `verify` and `consumer-test`. The former
builds the library and runs every package test, including the smoke import.
The latter builds an isolated Lake consumer. Full verification adds the
integration Lean tests, Python tests, and standalone package-independence checks.

For Docker verification, substitute `katlean`, `netkatlean`, or `dynetkatlean`
to check an individual package.

```sh
target=integration
docker build -f docker/Dockerfile --target "$target" -t "dynetkatlean:$target" .
docker run --rm --network none "dynetkatlean:$target"
```

The image build resolves the checked-in Lake locks. Verification runs with
network access disabled and needs no checkout mount. KATch is optional. The
[historical DyNetiKAT reproduction](docs/DYNETIKAT_V11_CAMPAIGN.md#reconstructed-ubuntu-runtime)
has a separate runtime and is outside mathematical verification.
See the [release build notes](docs/MODULARIZATION_PLAN.md#reproducible-native-and-docker-builds).

## Run v1.1 queries

From `lean/`:

```sh
lake build dynetkat
.lake/build/bin/dynetkat validate input.json
.lake/build/bin/dynetkat query input.json packet_key 0
.lake/build/bin/dynetkat batch --json input.json
```

Batch runs produce ordered checked reachability and waypoint verdicts.
JSON output is one record per query. Exit 1 indicates a fixture assertion
disagreement, exit 2 an input or invocation error, and exit 4 an analysis
diagnostic. A false waypoint verdict is a successful analysis. The
[parity ledger](docs/DYNETIKAT_PARITY.md#checkpoint-3-waypoint-and-batch-execution)
has the schema, scope and reference-validation status.

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

See the [symbolic frontend and dependency audit](docs/NETKAT_AUDIT.md).

See [NATIVE_KAT.md](docs/NATIVE_KAT.md) for the theorem chain and proof construction.

### Native KAT decision layer

`import KATLean.Native` provides a verified partial-derivative equivalence
engine for the pure KAT equational theory over the native finite alphabets.
Its soundness and completeness proofs use no `CtxPkt` enumeration or KATch.
Boolean guards are canonical decision trees; the solver explores satisfiable
symbolic regions instead of abstract truth assignments.
See [NATIVE_KAT.md](docs/NATIVE_KAT.md) for the exact theorem scope and tests.

The symbolic frontend interprets packet equations such as assignment
overwrite before comparing the encoded relations through `KATLean.Native`.
Graph and safety checks share the symbolic zero checker. Lemma 5 and
DyNetKAT packet-head normalization use the same symbolic packet compiler
and exact star fixed point. They emit the paper's complete-pair branches
from accepting diagram paths. `CtxPkt` supplies the concrete field schema
and execution model. Core equivalence, both paper normalizers, graph
normalization, safety and supplied-packet execution correctness use no
full packet-universe enumeration. The exhaustive equivalence checker
and normalizer are available through `DyNetKAT.NetKAT.Legacy`.
KATch remains experimental.

Faithful Lean 4 formalization of the **original DyNetKAT calculus**:
*DyNetKAT: An Algebra of Dynamic Networks* (arXiv:2102.10035v4, FoSSaCS 2022).

## Goal

A complete Lean 4 formalization of the mathematics in the original DyNetKAT
paper, together with a usable implementation of the original DyNetiKAT
analysis workflow. The target includes sound and ground-complete equational
theories, guarded recursion, the full safety framework, and dynamic
reachability and waypointing over general finite packet domains.

See the [roadmap](PLAN.md) for current coverage, the finite-depth projection
workstream and the release criteria. The journal extension on log extraction,
causality and bounded schedules is outside the paper scope.

### Verified language boundary

The raw Lean AST provides syntax for the SOS and proof infrastructure.
`Program` admits entries in the paper source grammar with closed, guarded
recursive declarations. `Program.Residual` additionally carries an SOS path
from its admitted source. Compiled states carry both source and graph
reachability. Use the APIs in `Program.lean` for transitions, projection,
discovery, equivalence and safety queries. Raw graph tables, head and tail
forms, and solver models are internal helper syntax.

The [semantic-domain audit](docs/PAPER_CONFORMANCE.md#source-grammar-and-sos-residual-closure)
lists the source constructors, reachability conditions and classified examples.

Certified finite projection has both SOS exactness
(`renderProjection_bisimilar`) and equational correctness
(`renderProjection_derives`). The latter uses E_DNK without AIP and
covers admitted guarded recursion, including processes with infinitely many
global derivatives. AIP lifts comparisons at every depth to the original
processes.

KATLean supplies the Mathlib-based algebra beneath the NetKAT layer.
It proves the KA/test laws and dup-free packet laws and connects the
current AST and evaluator to a packet-relation model. `Derives` justifies
its KA, Boolean and packet laws directly through KATLean. Its semantic
soundness, Lemma 5 and the E_DNK packet-prefix import follow that proof chain.
Import `KATLean` for the algebra or `DyNetKAT.NetKAT.KATLean` for the
current NetKAT bridge. See [KATLEAN.md](docs/KATLEAN.md) for Figure 4
coverage, general-schema work and the optional full NetKAT history/dup extension.

The core formalization follows the source grammar, `Program` / reachable
`Residual` boundary, SOS semantics, KATLean, dup-free E_NK, E_DNK and
certified analysis. KATch is an optional experiment and comparison point.
Core equivalence theorems use Lean proofs over the native symbolic packet
layer.

## Structure

```
DyNetKATLean/
├── lean/          # Lean 4 formalization (trusted semantic core)
├── python/        # Auxiliary scripts & golden tests (untrusted adapter)
├── docs/          # Research notes, conformance mapping, proof roadmap
├── scripts/       # Build & validation scripts
├── PLAN.md        # Phased roadmap
└── README.md      # This file
```

## Project Policies

- Mathematical references use [arXiv:2102.10035v4](https://arxiv.org/abs/2102.10035v4).
  The [conformance inventory](docs/PAPER_CONFORMANCE.md) maps these references to
  the FoSSaCS 2022 edition. Tool parity targets
  [DyNetiKAT v1.1](https://gitlab.utwente.nl/fmt/dynetikat/-/tree/v1.1).
- Lean 4 is the trusted semantic core. Python is limited to auxiliary scripts,
  golden-value checks, and experiments; it does not carry research-critical
  semantics.
- Preserve the paper's syntax, semantics, equations, and per-packet
  consistency. Distinguish paper definitions from implementation choices and
  extensions, and state finite-domain, termination, or boundedness assumptions
  explicitly.
- Do not use `axiom`, `sorry`, or `admit` as substitutes for proofs. Any
  temporary proof hole must be isolated and explained. Record mathematical
  findings and design conflicts in the relevant `docs/` files.
- Use Lean 4 / Lake, `UpperCamelCase` for types and constructors, and
  `lowerCamelCase` for definitions and theorems. Use Python 3 type hints,
  `snake_case`, and deterministic serialization.

## Future package roadmap

The [post-development modularization plan](docs/MODULARIZATION_PLAN.md)
describes standalone KATLean, NetKATLean, and DyNetKATLean packages,
their downstream workflows, and the coordinated rename planned after
paper and parity development. Use the current build and import instructions
below for this checkout.

## Finite packet schemas

The semantic foundation accepts a `PacketSchema` with finite,
field-dependent value domains. Use `PacketSchema.ofFields` for total
valuations with point updates. A policy `NetKAT schema` supplies the
packet operations for `DyNetKAT schema`. Its recursion environment
determines the schema of `Program`, `Residual`, and `Program.Trace`.
Omitting the schema on the original types selects `ctxSchema` and
`CtxPkt`. The symbolic compiler and NetKATLean's algebraic
normalization support dependent field domains. For a decision that
takes only the packet schema, use `netkatNativeEquivFinite`.
The paper-facing DyNetKAT equational and certified analysis pipeline uses
the same schema. It covers head normalization, ground completeness, AIP,
trace safety and positive absorption, exact graph moves, projections and
reachability. Finite graph compilation requires finite support for the
reachable definition names. Exact executable projection additionally needs
checked classifiers for active restrictions. All-depth analysis uses a
checked finite reachable closure or another suitable checked model. Source trace safety and finite projection also
apply to programs with infinitely many derivatives.

The [FatTree case study](docs/PAPER_CONFORMANCE.md#fattree-migration-in-arxiv-v4)
proves forwarding through the five migration phases, all-trace SSH isolation,
and the final waypoint endpoint-inclusion equation. The topology regression
covers all six reported sizes through 1,344 switches.

## Building

```bash
cd lean
lake build DyNetKAT    # authoritative Lean build
```

## Testing

```bash
cd python
python3 -m pytest -q   # Python auxiliary tests
```

Combined check:
```bash
./scripts/verify.sh
```

A no-argument `lake build` that reports `[0/0]` does not compile the library;
always validate the explicit `DyNetKAT` target. If the system Python lacks
pytest, use a virtual environment and install `pytest>=8` there.

## Paper trace safety

`Program.Trace` is a finite execution of the source SOS with consistent
packet lists. For the arXiv v4 safety formula `[r]false`,
`TraceSafety.Formula.equational_iff` proves Eq. (27) equivalent to excluding
every forbidden initial word on an admitted network over the supplied
finite alphabet. This theorem covers guarded recursion without a finite
derivative closure.

`TraceSafety.check` checks supplied forbidden words against exact symbolic
moves when compilation support and restriction classifiers are supplied.
`TraceSafety.check_correct` connects the result to source safety.
The word length is an exact bound for matching that word. See the
[paper crosswalk](docs/PAPER_CONFORMANCE.md#safety-property-theory).

## Positive reachability and nested tails

`TraceSafety.checkPositive` verifies the §V positive absorption equation
by checking every word of the supplied specification. For endpoint
queries, `projectedReachability` applies the requested sequence of
structural tails and checks for a feasible packet observation within the
specified source projection. An empty stage list checks the initial head.
`normalizedReachability_correct` proves the all-depth endpoint result
when an exact finite derivative table is supplied.

## Checking safety on a recursive graph

`compileGraph env p support` checks that the supplied finite set contains
every variable in the root and in the bodies of the supported definitions.
Each variable must be defined. The returned graph stores the translated
definitions and uses references to represent recursion.

Use `safetyCheckGraph G R ingress egress` on a closed graph in the paper's
head/tail fragment. It reports initial isolation (34) and post-reconfiguration
reachability (35) separately. The results distinguish failed extraction from
an evaluated condition. Raw graph nodes and labels can be checked with
`validateProcessGraph`.

`compileAndSafetyCheckGraph` compiles first, then eliminates the restriction
of communication actions and checks the resulting graph. Its preprocessor
supports recursive sequential terms.

For raw parallel terms and merges, use
`compileNormalizeAndSafetyCheckGraph env p support candidate R ingress egress`.
With an already compiled graph, use
`normalizeAndSafetyCheckGraph G candidate R ingress egress`.
A `NormalizationCandidate n` supplies `n + 1` indexed process derivatives,
their outgoing packet and reconfiguration edges, and an order for evaluating
references needed in the current step. The initial derivative is index zero.
Each later index needs an incoming edge from an earlier index. The checker
validates every row against the SOS under the outer communication restriction
before building the sequential graph.

The Boolean validator accepts some certificate exactly when the restricted
derivative set is finite and the graph satisfies `NormalizationAdmissible`.
Every reachable derivative must be free of restriction constructors in its
own syntax. One reference order must cover the references inspected during
a single step from those derivatives, and each label in that order can
consult only earlier entries. A restriction encountered during this
one-step traversal fails validation. Prefix continuations, the right
operand of left merge, and the body of a zero projection are skipped
during the traversal.

Use `normalizeCertifiedGraph` or `safetyCheckCertifiedGraph` when a Lean
proof of `NormalizationExact` is available. This accepts exact tables for
finite systems with active reference cycles or nested restrictions.
`exists_exactNormalization_iff` proves that such a table exists exactly
when the restricted derivative set is finite. This existence theorem
uses classical reasoning over finite derivative indices and syntactic labels.
Packet labels retain their entire policy relation and use the symbolic zero
check for feasibility. The executable renderer consumes the supplied table
and its proof.

The [graph safety regressions](lean/test_graph_safety.lean) include the
original parallel firewall and its two-state certificate. The
[admissibility regressions](lean/test_normalization_admissibility.lean)
cover silent and productive cycles and nested restriction sets.

## Optional / experimental tooling

`import DyNetKAT` exposes the core formalization. To use the former
backend exports, use `import DyNetKAT.Experimental` or import
`DyNetKAT.NetKAT.KATch`, `BackendCertificate` or `EquationalCertificate`
explicitly. Their existing declaration names and APIs are preserved.

KATch is an optional, untrusted external experiment, comparison point
and possible future accelerator. The replay driver, candidate checkers,
equational checker and tests remain available. Their proof obligations
belong to those experiments. Project completion, E_NK/E_DNK, normalization,
completeness and certified analysis require no KATch installation.
The [NetKAT audit](docs/NETKAT_AUDIT.md#optional--experimental-tooling)
records the common fragment, finite-domain restrictions and replay results.


Build the optional Lean exports before running backend fixtures or the full
Lean regression sweep on a fresh checkout.

```bash
cd lean
lake build DyNetKAT.Experimental
for f in test_*.lean; do
  lake env lean "$f" || exit 1
done
```

Core-only verification uses `lake build DyNetKAT`. Python replay integration
tests skip when the optional Lean target has not been built. The full suite
with that target built exercises the preserved replay infrastructure using
subprocess doubles and needs no KATch installation.
