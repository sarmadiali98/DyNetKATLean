# DyNetiKAT v1.1 checkpoint 4 campaign

Baseline `96663e191c6755e04318df7251bd3c4353d9d7c6`. Reference revision
`1c6bd422377853378c7516a7875009fcfb5ba881`.

## Reference runtime

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

## Observed results

The native batch returned 120 checked verdicts from 27 inputs. Reachability
returned 53 nonempty and 55 empty bounded results. All 12 waypoint
endpoint-inclusion queries returned true. Fresh and reused execution
agreed for all 120 reports. The two independent-controller assertions
remain fixture-expectation disagreements. Both queries have index 1,
depth 3 and a checked nonempty result, with packet keys `H3_to_H2`
and `H1_to_H4`. Their reference outcomes are unknown.

| Query subset | Total | Observed reference | Comparable | Lean non-verdict |
| --- | ---: | ---: | ---: | ---: |
| All | 120 | 0 | 0 | 0 |
| Reachability | 108 | 0 | 0 | 0 |
| `!0` | 51 | 0 | 0 | 0 |
| `=0` | 57 | 0 | 0 | 0 |
| Head alone | 6 | 0 | 0 | 0 |
| Single tail | 30 | 0 | 0 | 0 |
| Nested tail | 72 | 0 | 0 | 0 |
| Waypoint | 12 | 0 | 0 | 0 |

Matches and semantic mismatches are both zero because the comparison has
zero paired verdicts. All 120 cases are uncomparable due to one reference
runtime setup blocker. No historical query reached execution. Re-running
the pinned generator produced 24 byte-identical archived inputs, zero
formatting or order differences, zero content differences and zero failures.

Functional parity sign-off remains open until the historical runtime returns
query observations and the differential resolves every case. Empirical parity
remains open until the reference timing matrix runs on the comparison host.

The ledger also lists direct loading of historical preprocessed JSON and
serial/parallel agreement as acceptance checks. This work exercised the
raw fixture interface and native in-memory preparation. It did not validate
historical serialized preprocessing or worker-count parity. The live
runner's reference timing mode is serial. Published parallel overhead and
decision-share comparisons still need measured reference results and
appropriate instrumentation.

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
