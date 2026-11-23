# DyNetiKAT v1.1 benchmark validation

## Comparison boundary

These checks use the reconstructed historical v1.1 runtime and native Lean CLI on the Ubuntu comparison host. They use new processes and separate scratch directories.

| Development mode | Lean | DyNetiKAT v1.1 |
| --- | --- | --- |
| Fresh | Batch with `--fresh` loads the input once, then prepares and checks each query. | Without `-p`, parses the original JSON, preprocesses once, writes a prepared JSON artifact, and then checks the properties. |
| Reused | Normal batch loads and prepares once in the new process, then reuses the in-memory job for every query. | With `-p`, parses a serialized preprocessed input, skips normalization and zero checks, and still generates the analysis Maude module before checking properties. |

Lean's lifecycle is in `runQueries` in `lean/DyNetKAT/Main.lean`. The reference boundaries are in pinned `dnk.py` and `src/python/preprocess.py`. The isolated Lean phase executable directly calls the original read, decode, parse, infer, elaborate, prepare, query and reporting operations.

## Measurement and tracing

The harness uses the frozen input manifest and orders verdicts by packet key and query index. A v1.1 reachability report describes satisfaction of the assertion, while Lean's reachability verdict describes nonemptiness. The harness accounts for assertion polarity before matching vectors. Lean exit 1 in the SSH-ingress substitution is the CLI's expected status for a completed query whose result disagrees with the assertion.

The timing passes use external monotonic time, GNU `time -v`, and v1.1's internal timing fields. The side passes use Python audit and profiling hooks for reference process launches, file opens and phase intervals, and a libc open interposer for Lean. Work denied `strace` because `ptrace` is unavailable. The hooks observe the reference coordinator and workers and the Lean CLI's relevant libc calls. The interposer observes native process starts and covered libc opens. The trace does not cover every system call within Maude or `katbv`.

The historical total timer starts after module imports. Its preprocessing interval includes initialization, preprocessing, materializing the analysis Maude module, and serializing the prepared artifact when applicable. The reported `NetKAT time` is the largest per-property NetKAT decision interval. During preprocessing, the parent can run Maude while the preprocessing worker runs NetKAT even with one configured worker per pool. Count overlapping child intervals once when describing elapsed wall-time coverage. Keep remaining elapsed time unattributed.

## Paper experiment

The pinned artifact's Section 5 describes Ubuntu 20.04 LTS, an Intel i9-9980HK reported as 16 cores at 2.4 GHz, and 64 GB RAM. It reports ten-run averages across six FatTree scales, up to 1,344 switches. The four workloads are Reachability-I, Reachability-II, Waypointing, and All Properties. The prose describes one thread for each property in the parallel experiment. The released `run_fattree.sh` invokes `dnk.py … -s` on the four input JSONs at each scale, with no `-p`, no `-t`, and no repetition loop. Each invocation preprocesses its own input and prints separate timing fields. The script's implicit pool size comes from Python's default. The prose specifies one worker per property for the parallel experiment.

A later sensitivity test is feasible with an isolated Python 3.8 environment and an x86-64 NumPy wheel compatible with that interpreter. The pinned README requires Python 3.7 or newer and NumPy. Only the FatTree generator imports NetworkX, so an older NetworkX is needed only for a separate generator test. The available interpreters and NumPy wheel on this host are Python 3.14. Acquire the historical interpreter and compatible wheels before scheduling this test. Confirm dependency versions and the actual process start method, then compare identical input hashes and verdicts on small, medium and large cases. Keep Maude and the reconstructed NetKAT candidate fixed. Freeze the materiality threshold before measuring.

## Lean dispatch audit

The generated C for the production CLI retains a prepare call before the query loop on the normal batch path and a conditional prepare call within the loop for `--fresh`. For each query, the side executable also reports the applicable branch in the existing Lean source. On the six-pod All Properties probe, all eight reachability queries satisfy the depth and pinned-ingress conditions for `tightReachability`. The waypoint query satisfies the depth condition for `tightHead`. These are verified computation paths in `V11Reachability.lean` and `V11Waypoint.lean`. The route probe executes after the separately recorded query check and before the side executable's total ends.

## Initial observations

| FatTree case | Lean external wall | DyNetiKAT external wall | DyNetiKAT reported internal total | Preprocessing | Verdicts |
| --- | ---: | ---: | ---: | ---: | --- |
| 6 pods, 99 switches, All Properties | 0.103 s | 7.927 s | 7.81 s | 3.89 s | 9 identical |
| 12 pods, 612 switches, All Properties | 0.581 s | 215.709 s | 215.59 s | 118.28 s | 9 identical |
| 16 pods, 1,344 switches, All Properties | 1.366 s | 1,028.823 s | 1,028.70 s | 577.72 s | 9 identical |

The 6- and 12-pod cases use Lean prepare-once. The 16-pod case uses the development campaign's Lean `--fresh` setting. Both historical timings start from original JSON with one configured worker. The matching 16-pod normalized vector was `true, true, true, true, false, false, false, false, true`. GNU time independently rounded the 16-pod external times to 1.36 s and 1,028.82 s. The 577.72 s historical preprocessing interval accounts for 56.15% of external time. The maximum NetKAT property interval was 122.03 s.

The 6-pod fresh trace observed 17 preprocessing Maude invocations and 16 NetKAT zero checks, followed by nine Maude and nine NetKAT invocations for the properties. The two one-worker pools ran in separate phases. The preprocessed replay read the exact artifact from the clean historical run, reported the same nine verdicts, and invoked only the nine property checks in each backend. Both tools rejected malformed JSON immediately following a successful execution in the same scratch directory. Lean returned 2 and DyNetiKAT returned 1.

An initial auxiliary ingress perturbation used negation of an entire sequential predicate. The reconstructed `katbv` parser rejected that syntax and the historical Python reporting path raised `TypeError: cannot unpack non-iterable NoneType object`. Lean evaluated the altered input as false. This parser difference was on an auxiliary input outside the pinned matrix. The recorded perturbation check uses the known blocked SSH ingress from the published six-pod input, with the original reachability expression, endpoint predicate and depth.

Each process starts with a new scratch workspace. The operating system's file caches remain under normal host control. A representative reproduction from the checkout builds a separate phase executable and then runs a clean observation and a traced side observation.

```bash
audit_root=$(mktemp -d /tmp/v11-forensics.XXXXXX)
PYTHONPATH=scripts python3 -c 'from pathlib import Path; import sys; from v11_benchmark_validation import build_lean_phases; build_lean_phases(Path(sys.argv[1]))' "$audit_root/phases"
python3 scripts/v11_benchmark_validation.py "$audit_root/6" 6 --lean-phases "$audit_root/phases/phases"
python3 scripts/v11_benchmark_validation.py "$audit_root/6-trace" 6 --traced --check-malformed
python3 scripts/v11_benchmark_validation.py "$audit_root/6-prepared" 6 --traced --prepared "$audit_root/6/reference/output/FAT-TREE_preprocessed.json"
python3 scripts/v11_benchmark_validation.py "$audit_root/6-ssh-perturb" 6 --group reachability_1 --perturb --traced
python3 -m unittest discover -s scripts -p test_v11_benchmark_validation.py
```

The known SSH ingress substitution returned false from both tools, where the original query returned true. Lean exited 1 for a violated fixture assertion, DyNetiKAT exited 0 and reported the assertion as violated, and both produced one determinate verdict.

## Phase breakdown from the side traces

The 12-pod trace recorded 17 preprocessing Maude calls and 16 NetKAT zero checks, followed by nine Maude calls and nine NetKAT decisions for the properties. Python's `NetKATComm.tool_format` rewrites the policy strings to the reconstructed backend's syntax, including rewriting numeric literals to binary. The trace directly measures this work before launch.

| 12-pod trace phase | Phase wall | Python NetKAT formatting, summed | Subprocess intervals, elapsed union | Either observed operation, elapsed union | Unattributed within phase |
| --- | ---: | ---: | ---: | ---: | ---: |
| Preprocessing method | 119.558 s | 62.938 s | 57.100 s | 119.254 s | 0.303 s |
| Property decision method | 97.975 s | 50.724 s | 47.034 s | 97.758 s | 0.217 s |

The union columns count overlapped work once. A subprocess span includes launch, execution, and collection within Python's `subprocess.run`. The clean CLI timing and traced phase measurements are separate observations. The NetKAT property timer in v1.1 wraps backend adapter execution, including formatting, temporary-file handling, and the backend invocation. Its reported maximum can overlap other properties in a parallel run.

The 12-pod Lean phase executable took 0.412 s in decode and parse, 0.070 s in domain inference, elaboration and validation, and about 14 microseconds in the separately named prepare phase. The prepare interval starts after the loader has compiled and admitted the input. These measurements distinguish the actual operations behind the tools' phase names.

The 16-pod traced observation took 1,030.452 s externally. Its internal total was 1,030.23 s, with 578.34 s reported as preprocessing. Both tools exited 0 and returned the clean run's nine-verdict vector.

| 16-pod trace phase | Phase wall | Python NetKAT formatting, summed | Subprocess intervals, elapsed union | Either observed operation, elapsed union | Unattributed within phase |
| --- | ---: | ---: | ---: | ---: | ---: |
| Preprocessing method | 578.321 s | 327.662 s | 251.873 s | 577.687 s | 0.634 s |
| Property decision method | 451.867 s | 265.464 s | 185.896 s | 451.361 s | 0.507 s |

The trace observed one Python coordinator and two worker processes across the sequential preprocessing and analysis pools. Preprocessing launched 17 Maude processes and 16 NetKAT processes. Analysis launched nine of each. Python dispatches those backend commands through a shell. The trace records the coordinator, workers, shells, and backend child PIDs. The observed JSON read and decode took 0.019 s, and prepared JSON serialization took 0.021 s. The measured format and child spans account for almost all time in the two methods. The table leaves the remaining method time unattributed.

The 16-pod Lean phase executable recorded about 38 ms from harness launch to entry, 15 ms reading input, 999 ms decoding and parsing, 163 ms inferring domains and elaborating and validating, 14 microseconds preparing, and 114 ms across nine checks. The input has eight queries eligible for the verified tight reachability route and one waypoint query eligible for the verified tight-head route. The CLI read the input and emitted the verdicts from a single native Lean process. This source and trace evidence explains the different work performed: the reference tool formats and dispatches backend work over substantial policy expressions, while Lean checks the bounded questions in-process after loading the admitted program. The observations provide phase attribution. An ablation would be needed to quantify the causal effect of changing either algorithm or runtime.

## Gate result

**BENCHMARK VALIDATION GATE: PASS**

The clean and traced All Properties observations on 6, 12 and 16 pods each produced nine matching verdicts in both implementations. The prepared replay, supported verdict-changing perturbation, malformed-input rejection, and trace checks passed. The clean 16-pod external and internal timers differed by 0.123 s. The six frozen checkpoint files retained their original SHA-256 values. The machine-readable evidence includes exact input hashes, query operands and update sequences, process statuses, verdict vectors, trace provenance, and host/runtime versions.
