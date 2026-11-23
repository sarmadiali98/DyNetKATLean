# DyNetiKAT v1.1 checkpoint 4 campaign

Baseline `96663e191c6755e04318df7251bd3c4353d9d7c6`. Reference revision
`1c6bd422377853378c7516a7875009fcfb5ba881`.

## Initial macOS runtime investigation

The pinned Python and Maude source modules were recovered by exact revision
and kept unchanged. The Python CLI displays its help under Python 3.11.15,
NumPy 1.26.3 and NetworkX 3.6.1. The local host reports macOS 27.2.1
(build 26B131), arm64. The pinned installer expects Maude 3.1 for Linux,
libncurses5, opam, OCaml, mparser 1.2.3 and the external NetKAT build.
It clones NetKAT without an immutable backend revision. No backend
binary or compatible Maude runtime was available on this host. Probes
to the Maude 3.1 download and NetKAT repository timed out at the proxy.
No compatibility or semantic patch was applied.

The CLI startup preflight printed `Please provide the path to the Maude
executable!` and exited 0. This is a setup diagnostic, so it contributes
zero observed query verdicts. The other end of the toolchain also needs
an executable `katbv` (IDD) or `Decide_Repl.native` (automata). For the
reference campaign, record the exact backend revision or archive, the
toolchain used to build it, and the version of Maude alongside the binary
hashes. The orchestrator records the binary hashes, Python package
versions and full commands in the results directory.

### Historical backend recovery

Recovery on baseline `ff0d22ef9ccc8fd5ca7888ffb81f6053bad9d747`
confirmed that the reference tag `v1.1` is identical to the pinned SHA
and located the legacy IDD code in
[`netkat-lang/old-netkat`](https://github.com/netkat-lang/old-netkat).
The pinned [test script](https://github.com/hcantunc/DyNetiKAT/blob/1c6bd422377853378c7516a7875009fcfb5ba881/run_test.sh)
invokes `_build/install/default/bin/katbv`. The installer update
`1fbe0208b4cefef9c351a6966bc63e548274932f` retained an unpinned clone.
The initial README names the same URL and executable. The paper names
the decision procedure without a build revision. The pinned tree has no
`.gitmodules`, `.github/workflows`, `.travis.yml` or Dockerfile at those
paths. The release asset listing could not be inspected. The issue search
for Maude, katbv and artifacts returned no hits.

The retained legacy master history identifies
[`5822459fbfae0f0e9e0622843ebe30208f8bf189`](https://github.com/netkat-lang/old-netkat/commit/5822459fbfae0f0e9e0622843ebe30208f8bf189)
(2020-10-19) as the latest visible legacy commit before the initial
DyNetiKAT publication (2021-05-21), installer update (2021-09-17) and
pinned revision (2021-10-09). Its package metadata still names the
original clone URL. Its source exposes `katbv equiv FILE1 FILE2` and
prints the `expressions equivalent:` line expected by the pinned
wrapper. This is the leading reconstruction candidate. The
[legacy comparison](https://github.com/netkat-lang/old-netkat/compare/0.1...5822459fbfae0f0e9e0622843ebe30208f8bf189)
puts it two commits after the 0.1 tag
`3347316917aadeb86d3e771fe2d2f7e3f4da7619`, with
`0c19199ffb90f7efa647df1d0fd82cea44ad4233` in between. This is a
three-revision comparison set bounded by the compatible release and
the date-constrained legacy tip. The intervening changes touch compiler
or semantics files, so source-level CLI compatibility alone cannot
establish verdict agreement. No artifact ties a revision to the
original execution. The current repository at the old clone URL has
different history and its date-matched 2021 snapshot builds Nerode
tools. The optional automata backend is a separate implementation.

The opam source archive supplied these verified bytes:

| Source | SHA-256 |
| --- | --- |
| [NetKAT 0.1](https://opam.ocaml.org/packages/netkat/netkat.0.1/) | `0f8f1be04daadd1bbff4eeebf709247b17024678943b1ede9ef44c6e76591882` |
| [mparser 1.2.3](https://opam.ocaml.org/packages/mparser/mparser.1.2.3/) | `dd08c884ea6e7d60a84613433ea20e7e198a8f90edad5064e4c0bc1ebc2b9669` |

The legacy CI matrix used Linux and OCaml 4.07.1 and 4.08.1, and
pinned `idds` from Git without a revision. The release's opam metadata
requires OCaml >= 4.07, dune >= 1.10, Jane Street packages from v0.12
through v0.13, and mparser >= 1.2.3 and < 1.3.
Opam's current mparser 1.2.3 recipe requires OCaml < 5.0. Local
opam is 2.5.2; the installed OCaml switches are 5.2.0 and 5.4.1.
The ordinary-switch dry run hit a write-denied lock, and the local
cache lacks the period compiler and dependencies. OCaml 4.08.1 is
an evidence-backed starting point on a Linux x86-64 guest, with a
period opam package index and the legacy checkout's `make` target
after dependency installation. The
[2021-09-17 opam index snapshot](https://github.com/ocaml/opam-repository/tree/3ee0d8336d6616a07c1bd28128e70f56cce623e7)
contains OCaml 4.08.1, mparser 1.2.3, idds 0.2 and NetKAT 0.1.
Its NetKAT recipe names the original GitHub release URL and specifies
the same checksum as the recovered opam archive. This ties the old
repository's release family to the installer URL. The original opam
version and resolved transitive dependency set remain unknown.

The official [Maude3.1 tag](https://github.com/maude-lang/Maude/tree/Maude3.1)
resolves to
`797a2f1ddd63d3b3718c51e74e655981e5cd721c`. Debian bullseye also publishes
[Maude 3.1-2](https://packages.debian.org/en/bullseye/maude) for Linux
amd64 and arm64. The Debian CDN timed out, but the
[WSU Debian mirror](https://mirrors.vcea.wsu.edu/debian/pool/main/m/maude/maude_3.1-2_arm64.deb)
supplied the arm64 package. Its measured SHA-256 is
`42d9e4d8bb7e4a823629c649c03f8ee66f9efd0cfad4d728c9ea432116a8de9f`.
The package identifies itself as Maude 3.1-2. Its extracted ELF requires
the Linux loader and shared libraries. macOS returned an executable
format error (exit 126). This verifies the package format and metadata.
The Maude process itself did not start. The Maude source archive,
attempted GitHub release asset URLs, exact legacy backend source archive
and OCaml 4.08.1 source downloads timed out at CONNECT or TLS.
No usable Linux runtime was found locally. macOS can execute
x86-64 Mach-O through Rosetta, which does not provide a Linux guest.

The concrete acquisition route is a Linux x86-64 guest or host with
archive access. Use the official installer-linked Maude 3.1 Linux
bundle or record the Debian 3.1-2 package as a reconstruction, and
resolve the period OCaml stack for the exact legacy candidate. Record
download and binary hashes, version output and the complete dependency
set, then follow the pinned test command below from an exported
reference working tree. These commands have not executed on a recovered
runtime.

```sh
printf 'quit .\n' | /path/to/maude.linux64
python3 dnk.py /path/to/maude.linux64 /path/to/katbv \
  benchmarks/stateful_firewall.json -t 1 -v netkat-idd -s
```

For exact historical provenance, an original backend checkout,
original executable with provenance, or original build log and lock
is still needed. A timestamp-constrained build can supply explicitly
labelled reconstructed results after runtime checks. No fixed-fixture
query executed, both controller cases remain unavailable, and
preprocessed and worker-count behavior remains untested.

## Reconstructed Ubuntu runtime

The Ubuntu x86-64 run used pinned DyNetiKAT
`1c6bd422377853378c7516a7875009fcfb5ba881`, Maude 3.1 (Debian
`3.1-2`), and `katbv` built from
`netkat-lang/old-netkat@5822459fbfae0f0e9e0622843ebe30208f8bf189`.
This backend is the strongest reconstructed candidate. Its exact use in
the historical installation has not been established.

The compiler was OCaml 4.08.1 with opam 2.3.0 and `mparser` 1.2.3.
The compiler build used GNU C17, `-fcommon`, and a fixed alternate
signal-stack allocation for modern glibc. Jane Street Core v0.14.1
needed a Linux `gettid` stub compatibility patch. The pinned source
trees for DyNetiKAT and NetKAT were unchanged. The reference ran with
Python 3.14.7 and NumPy 2.5.5. The external launcher used multiprocessing
`fork` because the shell sandbox denied the `forkserver` socket bind.

The three fixed fixtures returned all 12 verdicts. Fresh preprocessing
and loading the generated JSON with `-p` agreed at one and two workers.
Running from another working directory also agreed when the launcher
added the script directory to Python's import path. Controller
preprocessed JSON differed only in the ordering of the serialized
`comm` set. No verdict changed.

The independent controller's `H3_to_H2` and `H1_to_H4` queries at index
1 and depth 3 both violated the fixture's `=0` assertion. The checked
Lean result is nonempty in both cases. These are fixture expectation
defects for the compared bounded queries. The other ten fixed fixture
assertions were satisfied, and all twelve reference verdicts matched
Lean.

## Reproduction

Use Python 3.11.15 and NetworkX 3.6.1 for the generator. The archive
directory must contain the exact pinned `benchmarks/fattree.py`,
`benchmarks/util.py`, three fixed input JSONs and the earlier 24
generated JSONs. The script checks the pinned source and fixed-fixture
Git blob IDs. It runs the generator in a new directory and compares
the reproduced bytes to that archive. An unequal hash with the same
JSON object is reported separately from a JSON content difference. For
the initial comparison corpus, extract the archived generated JSONs into
a staging directory and copy the five pinned blobs from the reference
checkout's `benchmarks/` directory into the same directory. The local
archive stores the generated inputs under `dnk-v11-campaign/generated/`.

Run from the Lean repository root with a built native executable:

```sh
cd lean
lake build dynetkat
cd ..
python3.11 scripts/v11_campaign.py \
  --corpus /path/to/v11-corpus \
  --lean lean/.lake/build/bin/dynetkat \
  --output /path/to/new/results
```

For a live reference campaign append `--reference /path/to/pinned-checkout
--maude /path/to/maude --netkat /path/to/katbv --backend netkat-idd`.
Use an environment with compatible binaries and NumPy, and paths without
whitespace because the reference builds shell commands from filenames. The script
checks the reference HEAD and exports the immutable Git tree to a
separate working directory. The reference command is
`python3.11 dnk.py MAUDE NETKAT INPUT -t 1 -v BACKEND -s`, with
absolute paths and reference working directory. If it emits a
preprocessed input, the runner archives that file and exercises
`-p` for the reused timing mode. This preserves the reference's
temporary file assumptions and leaves the source checkout intact.

For an archived reference comparison use `--reference-results
/path/to/reference.json --observe-only`. Replay recomputes Lean's
checked verdicts and checks query identities and input checksums
before using the archived observations. Raw report lines are
decoded by packet key and per-packet index. Only explicit satisfied
or violated lines become reference Booleans. For reachability the
decoder accounts for the requested polarity. Query tuple expectations
alone supply no reference verdict.

## Evidence layout and measurement

The result directory contains environment and command metadata,
the generated files, a generator hash comparison, input SHA-256
checksums, raw stdout and stderr under `logs/`, fresh/reused comparison,
per-query reference status and differential reports, and raw and
aggregated timing JSON. Preserve this directory when archiving a run.
The history checkout and the measurement runner stay outside the
ordinary Lean build and theorem trust base.

The native campaign invokes one serial process at a time, for each of
six scales and four query groupings, with ten repetitions in each of
the in-memory reused and per-query fresh modes. It uses the same
archived input bytes for both modes. Wall time includes process
startup, input parsing, checking and report output. Native CLI results
do not expose separate preprocessing and query timings. On this host
`/usr/bin/time -l` failed its `kern.clockrate` query, so peak memory
was not collected. The reference's own `-s` figures are retained when
observed, including its reported maximum NetKAT decision time. The
local native campaign shares the host with repository verification.
Its timings do not support a controlled comparison with historical
hardware, a speedup claim or published timing reproduction.

## Semantic differential results

The [reference evidence](DYNETIKAT_V11_REFERENCE_EVIDENCE.json) records
runtime provenance, query identities, input hashes, observed reference
reports, checked Lean verdicts, and individual execution attempts. All
27 input hashes match the native campaign, including all 24 regenerated
FatTree JSON files. The comparison uses query polarity to interpret the
reference's satisfied and violated reports. Fixture assertions are
recorded separately from the resulting Boolean verdicts.

| Query subset | Total | Reference observed | Matches | Mismatches |
| --- | ---: | ---: | ---: | ---: |
| All | 120 | 120 | 120 | 0 |
| Reachability | 108 | 108 | 108 | 0 |
| `!0` | 51 | 51 | 51 | 0 |
| `=0` | 57 | 57 | 57 | 0 |
| Head alone | 6 | 6 | 6 | 0 |
| Single tail | 30 | 30 | 30 | 0 |
| Nested tail | 72 | 72 | 72 | 0 |
| Waypoint | 12 | 12 | 12 | 0 |

There were zero final reference failures, Lean non-verdicts, and
uncomparable cases. The two fixed-fixture expectation defects did not
produce Lean/reference discrepancies.

The initial one-worker fresh runs of all eight 14- and 16-pod inputs
hit the five-minute per-input limit. These attempts are recorded as
timeouts. The 14-pod reachability-1 attempt had written a usable
preprocessed artifact before it timed out. An extended two-worker
fresh run produced the 16-pod combined verdicts and its preprocessed
artifact. At each of these two scales the four raw inputs differed only
in their property maps. For retries in `-p` mode, the run reused the
reference-generated preprocessing and supplied the original ordered
property map for the requested query group. Each group was dispatched
through v1.1. The final corpus contains an actual reference report for
every query, including the separate and combined dispatches.

This completes the scoped semantic differential. The fixed-fixture
mode checks do not establish general native loading of historical
preprocessed JSON or native worker-count parity. The historical timing
matrix remains pending.

## Native timing results

All 480 native runs completed with checked verdicts and no non-verdicts.
Each of the 48 mode/scale/group configurations has ten observations.
The median across 240 reused runs was 0.459 s (range 0.088 to 1.724 s).
The median across 240 fresh runs was 0.483 s (range 0.090 to 1.849 s).
These pooled medians mix workloads of different sizes. The
[native evidence manifest](DYNETIKAT_V11_NATIVE_EVIDENCE.json) records
per-configuration medians, input and generator hashes, and raw-report
checksums. The local raw archive is
`lean/.lake/dynetikat-v11-native-campaign.tar.gz` and stays outside Git.
No historical timing run was possible.

## Ubuntu timing protocol

The empirical comparison schedules 480 runs per implementation across
the same six FatTree scales (6, 8, 10, 12, 14, and 16 pods), four query
groups, two modes, and ten repetitions. The paired Ubuntu Lean run uses
the existing campaign harness. The archived macOS Lean measurements
remain available separately. Linux historical runs use
`scripts/v11_reference_timing.py` with the verified reconstructed
runtime and the hash-verified corpus. Each process runs serially with one
worker. The reference cycles through the matrix for each repetition,
without a separate warmup.

Fresh wall time includes startup, input parsing, preprocessing, Maude
and IDD calls, query evaluation, and report generation. Reused wall
time covers the same CLI invocation with `-p`, using serialized
preprocessing produced by the reference. It still includes loading the
preprocessed JSON and constructing the reference's analysis module.
For groups without a direct preprocessed artifact from the differential,
the runner first verifies that the original inputs differ only in
`properties`, then reuses the reference-generated artifact from that
scale with the original property map for the requested group. The
manifest records the source and resulting digest of each reused input.
Lean reused mode uses in-memory preparation within its batch process,
so the two reuse modes have different boundaries.

The original standardized reference campaign ran with an explicit
300-second cutoff per process. The runner kills the
process group and records elapsed time and the cutoff on timeout.
The timeout attempts remain in the denominator and stay out of the
successful-run median and range. The runner validates every completed
report against the existing reference evidence without creating new
semantic observations. It also records the tool's own total,
preprocessing, and maximum NetKAT times when available. GNU time
provides user CPU, system CPU, and maximum RSS for successful commands.
Maximum RSS is the operating system's reported maximum, with no
aggregation of concurrent process-tree memory.

Raw logs and progressively collected summaries live under
`lean/.lake/v11-ubuntu-timing/`. The [Ubuntu timing evidence snapshot](DYNETIKAT_V11_UBUNTU_TIMING_EVIDENCE.json)
records both completed standardized timing legs and the separate
completed timeout recovery. The native leg completed 480/480 runs. Its pooled fresh
median was 0.491 s (range 0.099 to 1.526 s), and its pooled reused
median was 0.485 s (range 0.098 to 1.481 s).
The standardized reference leg recorded 390 successes, 90 timeouts,
and zero other failures in 480 attempts. The timeouts covered all fresh
14- and 16-pod runs and all reused 16-pod all-properties runs. All 90 attempts completed in the separate uncensored recovery pass.
The original timeout records are retained in the standardized results.

The original IDD wrapper constructs temporary names by splitting the
absolute filename at its first dot. In this work directory under
`lean/.lake`, those temporary operands are `lean/_1.txt` and
`lean/_2.txt`. The reference removes them after its IDD call. The
runner uses one reference process and one worker, so the operands
are not shared between concurrent benchmark invocations.

### Timeout configuration and recovery

Both runners accept an optional positive integer timeout in seconds.
Omitting `--timeout` leaves measured attempts unrestricted.

```sh
# No timeout
python3 scripts/v11_campaign.py --corpus "$corpus" --lean "$lean" --output "$results"

# User-selected timeout
python3 scripts/v11_campaign.py --corpus "$corpus" --lean "$lean" --output "$results" --timeout 300
```

Retry the recorded timeouts from the original reference results in a
separate directory. The recovery runner verifies the original matrix
and input hashes, then appends linked outcomes. To resume after an
interruption, repeat the command with the same results directory.

```sh
python3 scripts/v11_reference_timing.py --runtime "$runtime" \
  --results "$recovery" --retry-timeouts-from "$original_reference"
```

Recovery wall times come from a second pass. Report them separately
from the original censored measurements.

### Completed development timing analysis

The uncensored recovery finished at 00:09:26 Tehran time on November 23,
2026, with 90 successful retries, zero failures, and no duplicate retry IDs.
Each retry links to exactly one original 300-second timeout and matches its
pod count, query group, mode, and repetition. The original timing ledger
matches its previously recorded SHA-256.

The full-coverage analysis uses the 390 original successful timings and the
90 successful retry timings. The original standardized results retain all
90 timeouts. Fresh and reused below are development CLI modes with the
lifecycle boundaries described above. The [CAV benchmark plan](CAV_BENCHMARK_PLAN.md)
defines the publication workloads separately.

| Mode | Matched | Historical total (s) | Lean total (s) | Ratio of totals | Mean paired | Median paired | Geometric mean | Range |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| All | 480 | 75278.60 | 291.03 | 258.66 | 171.79 | 91.69 | 103.83 | 10.30 to 776.88 |
| fresh | 240 | 58476.88 | 145.68 | 401.41 | 266.13 | 239.07 | 199.62 | 46.75 to 776.88 |
| reused | 240 | 16801.72 | 145.35 | 115.59 | 77.44 | 57.58 | 54.01 | 10.30 to 353.22 |

Ratios are historical wall time divided by Lean wall time. The evidence
also gives medians and paired ratios by pod count, query group, and mode.

The **timeout-selected subset** ran for 52,537.51 s in DyNetiKAT and
109.25 s in Lean, a 480.90 ratio of totals. The median paired ratio was
494.39, the geometric mean was 454.87, and the range was 304.67 to 776.88.
The reference reported preprocessing for all 90 retries, totaling
34,216.41 s (65.13% of historical wall time). Median fresh preprocessing
took 267.23 s at 14 pods and 576.45 s at 16 pods.

| Recovered configuration | Runs | Historical median (s) | Lean median (s) | Median paired ratio |
| --- | ---: | ---: | ---: | ---: |
| `14/fresh/all_properties` | 10 | 491.39 | 0.987 | 498.33 |
| `14/fresh/reachability_1` | 10 | 350.16 | 0.950 | 369.76 |
| `14/fresh/reachability_2` | 10 | 350.25 | 0.923 | 380.36 |
| `14/fresh/waypointing` | 10 | 326.29 | 0.932 | 349.84 |
| `16/fresh/all_properties` | 10 | 1030.30 | 1.461 | 706.12 |
| `16/fresh/reachability_1` | 10 | 741.18 | 1.398 | 531.85 |
| `16/fresh/reachability_2` | 10 | 739.84 | 1.350 | 550.18 |
| `16/fresh/waypointing` | 10 | 700.53 | 1.415 | 496.80 |
| `16/reused/all_properties` | 10 | 451.64 | 1.462 | 310.55 |

DyNetiKAT's `NetKAT time` is the maximum NetKAT decision time among
checked properties. It cannot be added to preprocessing time to reconstruct
total wall time. The existing logs lack a complete phase decomposition.
The benchmark-validation gate will add finer-grained instrumentation
before the paper-faithful run.
