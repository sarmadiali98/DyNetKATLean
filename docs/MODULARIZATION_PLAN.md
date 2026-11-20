# Post-development modularization and reproducibility

This phase starts after the main paper formalization and DyNetiKAT parity
work reaches a clean, verified development baseline. Record its commit,
toolchain, dependency revisions, proof audit, test results, and benchmark
inputs before changing package boundaries. The current checkpoint records
the plan. Normal paper and parity implementation resumes after this
documentation checkpoint.

## Package boundaries

Start with three independently consumable Lake packages in the same
repository. Decide whether to split repositories after clean downstream
consumption has been demonstrated. Each package has its own Lake metadata,
default library target, public umbrella module, and test suite.

| Package and umbrella import | Supported public scope | Allowed project dependencies |
|---|---|---|
| `KATLean`, `import KATLean` | KAT algebra, Boolean tests, relational and language semantics, equational theory, symbolic Boolean representation, native symbolic equivalence, soundness, completeness, and model interpretation | Mathlib |
| `NetKATLean`, `import NetKATLean` | Dup-free syntax over generic packet schemas, field tests and assignments, symbolic guards and updates, semantics, supplied-packet execution, E_NK and `Derives`, symbolic equivalence and normalization, and certified correctness bridges | KATLean and shared Mathlib dependencies |
| `DyNetKATLean`, `import DyNetKATLean` | Paper syntax, recursion environments, `Program` and reachable `Residual`, SOS, E_DNK, projection, AIP, traces, safety, reachability, certified graph analyses, and paper-facing theorems | NetKATLean, KATLean, and shared Mathlib dependencies |

KATLean users need only the algebra layer and its Lean dependencies.
Packet schemas and packet-specific interfaces belong in NetKATLean.
NetKATLean builds independently of DyNetKAT syntax, SOS, reconfiguration,
and examples. DyNetKATLean owns admission and dynamic behavior. Python,
KATch, and DyNetKAT examples are outside KATLean's dependencies.

Audit imports and public declaration signatures before moving code. For
lower-layer facilities currently stored alongside application-specific
definitions, place the generic interface and its correctness theorems in
the lowest appropriate package, and implement instantiations above it.
Use the verified proof and test baseline to check each extraction.

## Public interfaces and workflows

Publish an API inventory for each umbrella. Include constructors,
configuration and result types, operations, and their associated
correctness or interpretation theorems. Expose analysis certificates
where users need their guarantees, with a public way to inspect the
result and stated scope. Keep derivative automata, BDD nodes, simulation
tables, graph certificate construction, and completeness proof internals
out of routine user workflows. Document any supported specialized import
and its purpose. Use public umbrella APIs in public examples and tutorials
wherever possible. Treat intentional public API breaks as release-note
items.

Each package gets a workflow page organized by input, operation, result,
and evidence. These are the target workflows.

| Package and workflow | Input | Public operation and executable result | Evidence to document |
|---|---|---|---|
| KATLean equivalence | Expressions built from actions and Boolean tests | Run the symbolic equivalence decision and read the verdict | Soundness and completeness, with an example obtaining an equational theorem |
| KATLean interpretation | An expression and a model interpretation | Interpret the expression and inspect a concrete example | Model interpretation laws and preservation of derivable equality |
| NetKATLean execution | A finite packet schema, a dup-free policy, and one supplied packet | Execute the policy and inspect the output set | Agreement with relational semantics for that packet |
| NetKATLean symbolic analysis | A declared schema and one or two policies | Compile symbolically, normalize, or decide equivalence | Semantics preservation, E_NK derivability, and exact decision guarantees |
| DyNetKATLean source behavior | A recursion environment and process | Admit a `Program`, inspect source moves, and follow reachable residuals | Paper admission, SOS correspondence, and residual reachability |
| DyNetKATLean certified analysis | An admitted program or reachable residual, a query, and any required bounds or support | Choose projection, trace checking, safety, reachability, or graph analysis and inspect its result | The relevant theorem or certificate, including whether its scope is bounded, exact, or approximate |

## Documentation and tutorials

Give each package a documentation home with a quickstart, tutorial,
workflow page, API index, and explanation of the semantics and guarantees.
Put every Lean tutorial snippet in a compiled example or test. Include or
extract snippets from those files and have CI detect drift in any
rendered copies. Keep upper-layer examples with their owning package.

- **KATLean** covers a first expression, equivalence and its theorem,
  interpretation in a model, and a high-level account of symbolic solving.
- **NetKATLean** defines a schema, writes tests and assignments, executes
  a policy, normalizes it, checks equivalence, and explains symbolic packet
  constraints.
- **DyNetKATLean** defines a recursion environment, admits a program,
  inspects its SOS transitions, and walks through projection, reachability,
  safety, trace queries, and certified analysis.

## Verification tiers and downstream consumers

| Tier | Execution scope | Required coverage |
|---|---|---|
| Smoke | Each package and its transitive dependencies, with checks aiming to run in seconds once dependencies are built | Umbrella import, construction of a basic object, one executable operation, and one representative theorem |
| Package suite | Each owning package, including its direct and transitive dependencies | All layer-specific regressions and theorem tests. Lower-layer suites run without building upper layers. |
| Full verification | Complete stack | All Lean regressions and package suites, integration, downstream consumers, compiled documentation examples, maintained axiom audits, dependency direction checks, Docker targets, and selected performance regressions |

KATLean smoke constructs two KAT expressions, runs a simple equivalence
decision, and obtains the associated equality theorem. NetKATLean smoke
declares a small two-field schema, builds a test and assignment policy,
executes it on one packet, and checks the correctness theorem. DyNetKATLean
smoke admits a small program, runs finite projection, and uses its SOS
or equational correctness theorem.

Build three external fixtures named `consumer-katlean`,
`consumer-netkatlean`, and `consumer-dynetkatlean`. Each is a clean
minimal Lake project outside the source checkout. Fetch the intended
package through its documented dependency declaration pinned to the
candidate revision. Include only that package as a direct dependency,
use its public umbrella as the fixture's only project import, and
compile a useful example of the kind specified in the smoke criteria.
Resolve lower layers through the published dependency graph. Run without
checkout-relative imports, implicit source-path overrides, or access to
unpublished build artifacts. Inspect the resolved dependency closure as
part of verification. These fixtures are stronger evidence of modularity
than a successful monorepo build, because they exercise the installation
and imports available to a downstream researcher.

## Reproducible native and Docker builds

Pin Lean in `lean-toolchain` and Mathlib to an explicit revision or
compatible release. Record the resolved graph, package version, public
target, and dependency metadata. Document a fresh native setup and the
commands for each test tier. The ordinary build from each package root
should be `lake build`, with a default target that actually builds its
library. Docker stays optional for native Lean development.

Plan separate Docker targets with pinned build inputs. The target names
below are provisional. Select a target through `docker build --target`
with the release's documented context.

| Target | Contents and verification |
|---|---|
| `katlean` | Pinned Lean and Mathlib plus KATLean. Build the package and run its smoke fixture. |
| `netkatlean` | KATLean and NetKATLean. Build NetKATLean and run its smoke fixture. |
| `dynetkatlean` | The supported Lean stack. Build DyNetKATLean and run its smoke fixture. |
| `full-development` | The supported stack plus test, documentation, and benchmark tooling needed for full verification. |

Keep lower-layer images free of unrelated upper-layer dependencies.
Record base image digests and target commands in the release instructions.

## Scalability and benchmarks

| Concern | Evidence to collect |
|---|---|
| Proof scalability | Clean and incremental build times, transitive rebuilds after a local proof change, and proof changes required by public interface edits |
| Solver scalability | Guard node counts, derivative states, pair states, compilation time, and decision time |
| Packet schemas | Results for schemas larger than `CtxPkt`, varying field counts and domain sizes independently |
| Analysis scalability | Graph states and transitions, projection depth, discovered closure size, and reachability and safety time |
| Contributor scalability | Fresh setup steps and time, smoke test latency, tutorial coverage, and stability of public entry points |

Benchmark symbolic KAT decisions, NetKAT compilation, equivalence and
normalization, finite projection, graph extraction, reachability, safety,
and guarded recursive examples with both finite closure and growing
derivatives. Include sparse and dense cases where useful. Check semantic
outputs alongside measurements. Version workload fixtures, generators and
seeds, solver options, toolchain and package revisions, and result format.
Record hardware, worker count, repetitions, wall time, and peak memory.
Keep a tagged reference baseline and versioned summaries so CI can flag
severe regressions on a comparable runner. Record failures and resource
limits separately from timing comparisons.

## Future CI matrix

- Run KATLean smoke and full package jobs, NetKATLean smoke and full
  package jobs, and DyNetKATLean smoke and full package jobs.
- Run all three external consumer projects, all four Docker targets,
  compiled documentation examples, and full integration verification.
- Enforce dependency direction in Lake metadata, resolved dependencies,
  and transitive Lean imports. Assign modules to their owning package and
  fail on upward dependencies in either metadata or imports, including
  imports reached through an umbrella. Build lower-layer jobs from a
  context where upper-layer sources are unavailable.
- Verify canonical naming and prose style. Run maintained axiom audits and
  selected performance regressions through full verification.

## Coordinated naming and prose migration

After the clean verified development baseline, carry out one coordinated
migration from `DyNetKAT-Lean` to `DyNetKATLean`. Use the canonical
names `KATLean`, `NetKATLean`, and `DyNetKATLean` for package metadata
and project-controlled surfaces. Coordinate the GitHub repository rename
to `DyNetKATLean` and the local checkout rename to
`~/Desktop/DyNetKATLean` with maintainers. Update the remote URL, controlled
repository links, Lake packages and project metadata, module and namespace
references as needed, docs, scripts, CI, Docker, badges, examples, setup
instructions, comments, and generated documentation titles. Regenerate
outputs from their source templates. Afterward, verify fresh clones,
pinned downstream dependency declarations, and the full release checks.

Perform a repository-wide prose pass to remove em dashes. Add a CI scan
for Unicode U+2014 in tracked project-controlled prose, including
documentation, tutorials, templates, and comments. Define explicit
exclusions for vendored, external, and generated text, and preserve exact
external quotations through narrow, documented exceptions. Check the
source templates for project-controlled generated prose. Keep the naming
and style gates scoped to maintained material.

## Retirement of development comparisons

After the main development and its final verification, inventory the
remaining callers and record the independent coverage that will protect
the symbolic implementation during retirement. Current comparison
workflows remain available during development.

- Retire KATch replay, adapter code, KATch-only certificate plumbing,
  setup guides, regression workflows, any CI paths, and replay environment
  settings. Update documentation that presents KATch as a supported
  alternative. Begin the inventory at `scripts/katch_replay.py`,
  the optional Lean export and adapter, and the replay and differential
  tests. Check shared certificate code for independent users before
  removing a dependency.
- Retire exhaustive equivalence and normalization comparisons,
  symbolic-versus-exhaustive differential tests, associated scripts,
  and compatibility workflow documentation. Begin with the legacy
  NetKAT exports and their callers. Preserve independently useful
  regressions by checking semantic outcomes or verified symbolic
  properties directly. Supplied-packet execution belongs to the
  supported NetKATLean API.

Old code matters only when it interferes with the supported KATLean,
NetKATLean, or DyNetKATLean architecture. Remove obsolete comparison
paths as a bounded release task and rely on Git history for historical
implementations. The supported user path is the verified symbolic stack
from Mathlib through KATLean, NetKATLean, and DyNetKATLean.

## Release sequence

1. Tag the verified development baseline and record the public interface
   inventory, pinned dependencies, and verification evidence.
2. Establish the package boundaries in the current repository. Prove
   independent consumption through the external fixtures before deciding
   whether separate repositories would help.
3. Complete the coordinated naming and style migration and retire
   development-only integrations. Run the full verification matrix on a
   clean checkout and on the release candidate as consumed downstream.
4. Publish stable package versions with release notes, a compatibility
   matrix across the three packages and toolchain revisions, tagged
   reproducible baselines, and source archives. If Docker images are
   published, tag them against the same releases and record their digests.

## Acceptance criteria

1. KATLean can be consumed independently.
2. NetKATLean can be consumed with KATLean as its only lower project package.
3. DyNetKATLean consumes the lower layers through their declared interfaces.
4. CI automatically checks dependency direction.
5. Each package has a public umbrella import.
6. Each package has smoke and full package tests.
7. Each package has a quickstart and tutorial.
8. Tutorial examples compile in CI.
9. Each package has a pinned, reproducible native environment.
10. Docker targets cover all three layers and the full development stack.
11. All three downstream consumer projects pass in CI.
12. Canonical names are consistent in project-controlled material.
13. The repository and local checkout have the planned `DyNetKATLean` name.
14. Project-controlled prose passes the em dash check.
15. The supported workflow is free of KATch.
16. The supported workflow is free of exhaustive comparisons.
17. The public architecture centers on the verified symbolic implementation.
