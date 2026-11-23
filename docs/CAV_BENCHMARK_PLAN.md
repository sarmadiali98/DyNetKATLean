# CAV benchmark plan

This plan carries forward the benchmark and release work in the [project roadmap](../PLAN.md) and the evidence in the [DyNetiKAT v1.1 campaign log](DYNETIKAT_V11_CAMPAIGN.md). It defines the workloads, validation gates, and reporting protocol for the paper-faithful reproduction and the final CAV evaluation.

## Campaigns and release sequence

| Campaign | Scope and evidence |
| --- | --- |
| A. Semantic equivalence | 120/120 verdict agreements and 24/24 generated FatTree inputs reproduced. Retain the semantic evidence independently of the timing campaigns. |
| B. Historical development | Lean completed 480/480. DyNetiKAT completed 390 of 480 attempts under an explicit 300 s cutoff. All 90 separate uncensored retries succeeded, giving 480 matched timings with the original timeout records preserved. This campaign supplies development evidence and a repeated-preparation ablation. |
| C. Paper-faithful reproduction | Pass the validation gate before launching the hours-long run. Measure preprocessing separately and reproduce Reachability-I, Reachability-II, Waypointing, and All Properties with the authors' historical parallelism across 6, 8, 10, 12, 14, and 16 pods, with ten repetitions per configuration. |
| D. Final canonical CAV campaign | After package separation and release checks, validate the release candidate and run the full matched, uncensored matrix with detailed phase instrumentation, exact provenance, and raw logs. Use this campaign for the abstract and main performance figures. |

After C, finish the KATLean → NetKATLean → DyNetKATLean separation. For each package, independently exercise build, smoke, test-all, verify, docker-build, docker-test, and consumer-test, and provide independent CI, Docker, and consumer examples. Finish the historical DyNetiKAT reference Docker image, then complete the project-wide em dash cleanup and guard. Freeze the release candidate, complete the performance-gap forensic audit, and run D only after its validation gate passes.

## Reproduction host decision

The six-core Ubuntu paper-reproduction pilot was intentionally abandoned. Its partial measurements were discarded and are excluded from benchmark evidence. The completed six-core Ubuntu campaign and the passing [benchmark-validation gate](DYNETIKAT_V11_BENCHMARK_VALIDATION.md) remain valid same-host preliminary and forensic evidence.

Start the full paper-faithful reproduction on the available 20-core server. The paper uses parallel checking, and All Properties includes nine properties. The server provides room to run a worker per property. Before execution, capture the exact hardware and software provenance, including physical and logical core counts, CPU affinity and limits, OS, runtime and tool revisions. Explicitly configure and record the worker count for each workload. Use nine property workers for All Properties to follow the paper's one-worker-per-property description, and document the explicit policies for the other workloads and preprocessing.

Keep results from different machines out of direct speedup ratios. Decide separately whether the 20-core server should host the final canonical CAV benchmark. If selected, run both Lean and DyNetiKAT on that server under the matched protocol.

## Workload definitions and interpretation

Lean `batch --fresh` recomputes `prepare job` for each query in the input. Normal Lean `batch` prepares the job once in the new process and reuses the in-memory value across queries. DyNetiKAT fresh preprocesses once per input before checking its contained properties. DyNetiKAT `-p` loads a serialized preprocessed artifact. These development modes have different lifecycle boundaries. Repeated preparation adds work on the Lean side of the historical fresh comparison and cannot account for the observed Lean advantage. Interpret those ratios as toolchain workflow measurements. Retain Lean `--fresh` as a conservative stress test or ablation.

| Publication workload | Measurement boundary |
| --- | --- |
| Cold end-to-end batch | Start a new process from the original JSON with no precomputed artifact. Perform all required preparation once in the tool's natural workflow and produce every requested verdict. Use external whole-process wall time. |
| Prepared analysis | Make the required prepared representation available to the analysis code before starting the measurement. Time analysis and checking through the last verdict, excluding preparation and artifact loading. Implement an explicit boundary in each tool and record artifact loading and whole-process time separately where applicable. |
| Full analysis batch | From the original JSON, prepare once and check all nine distinct benchmark properties. This is the All Properties case under the cold end-to-end boundary. Its prepared counterpart checks the same nine properties. |

The three individual query groups are separate experimental configurations. All Properties already contains their nine distinct properties, so a full-batch time or property count comes from that configuration alone.

The revised 960-observation canonical plan comprises six scales × four query groups × two workload boundaries (cold end-to-end and prepared analysis) × ten repetitions × two implementations. Select and verify invocations by workload semantics. Use Lean's prepare-once path for cold end-to-end after validating its boundary. Implement and validate the genuine prepared-analysis boundary separately. Record external whole-process timing for every invocation, including those whose primary metric is the instrumented prepared-analysis interval.

## Mandatory validation before C and D

Run the checks below before starting C and rerun them on the exact release candidate, harness, inputs, and execution environment for D. Keep the validation evidence with each campaign. Apply comparability checks to every observation during both campaigns. A failed comparability check invalidates that observation for performance analysis. Retain the record and resolve the discrepancy before relying on the affected configuration.

### Input and verdict comparability

Have the harness machine-check the exact original input SHA-256, pod count and network size, query type, packet selector, depth, ordered update sequence, and expected property count against the frozen manifest. For prepared runs, also check each tool's prepared artifact or value provenance against the original input and record the artifact digest when serialized. Verify from the observed lifecycle and invocation that both tools performed the same semantic workload. Require successful process exit status and compare normalized verdict vectors in a fixed property order. Reject missing, duplicate, extra, or unparseable verdicts. For All Properties, assert exactly the nine expected verdicts from each tool and exact equality of the normalized vectors.

### Cache and shortcut falsification

Use representative 6-, 12-, and 16-pod cases, including 16-pod All Properties. Repeat from clean temporary and output state, with fresh processes and an alternate working directory. Inspect representative file accesses and the process tree to verify that no cached verdicts are read. In prepared runs, check that reuse is limited to the intended prepared representation. Perturb queries with known expected effects and confirm that the computation responds and that verdicts change where expected. Verify that malformed input is rejected. Restrict profiling and `strace` to forensic runs outside the timed dataset.

### Timer and process-tree validation

Use one pinned external harness with a monotonic wall clock around the entire process, from launch through exit. Instrument internal phase boundaries in both tools. On representative runs, use `/usr/bin/time -v` to record elapsed time, user and system CPU time, maximum RSS, I/O, and voluntary and involuntary context switches. Compare external and internal whole-run totals after accounting for startup and reporting. Establish the expected overhead on representative cases and investigate discrepancies before proceeding. Validate the prepared-analysis interval independently within the whole-run total.

Record observed Maude and NetKAT invocation counts by phase, Python process and worker counts, configured worker count, Lean process count, and parent-child structure. Compare the trace with the expected phases and use observed subprocess costs and counts when explaining architectural overhead.

### Runtime sensitivity before D

Use each tool's natural runtime and the same pinned external harness. For reconstructed DyNetiKAT, compare the current modern Python runtime with at least one historically plausible Python environment if feasible. Cover small, medium, and large cases, including preprocessing-heavy and reused or prepared cases. Hold inputs and other factors fixed where possible. Record necessary dependency or start-method changes, absolute timings, and phase effects. Freeze the materiality criterion before examining the sensitivity results. Document negligible sensitivity. For material sensitivity, select the more historically appropriate environment for D. Record attempted environments and the reason if a historical variant cannot run.

Keep Maude 3.1 and OCaml 4.08.1 pinned for the historical reconstruction. Record the exact old-netkat SHA and label it the strongest reconstructed candidate. The exact historical NetKAT backend remains unverified.

## Runtime decomposition

Record phase intervals in addition to the external total. Track parent and child spans and property identifiers so overlapping work can be inspected. Report elapsed time on the wall-clock critical path and summed parallel task times separately. Use nonoverlapping intervals when reconciling measured phases with the total and report unattributed time as residual.

- **DyNetiKAT.** Capture input and JSON handling, preprocessing Maude work, preprocessing NetKAT zero checks, other preprocessing and orchestration, serialization and any prepared artifact loading, property generation, per-property Maude and NetKAT time, output and orchestration residual, and total wall time. The existing `NetKAT time` field is the maximum property NetKAT time. Adding it to preprocessing cannot reconstruct the whole-run total.
- **Lean.** Capture input read, load and validation, preparation, each query check, output, and total wall time. For representative cases, subdivide preparation where it helps identify its cost.

## Parallelism, environment, and run order

For the controlled head-to-head, fix and verify an equivalent worker and compute policy. Prefer one worker per tool and use the same CPU affinity where practical. Record the reasoning for any other policy. In C, use the authors' historical parallelism, especially for All Properties. Publish C and D in separate tables.

Record CPU model, physical and logical core counts, RAM, kernel, Ubuntu version, CPU governor, and CPU affinity. Record exact tool commits, the Lean toolchain and Mathlib revision, DyNetiKAT revision, Maude version, NetKAT candidate revision, OCaml, Python, NumPy, NetworkX, Docker image hashes when used, and benchmark-harness commit. Record original input SHA-256, timestamps, and run order for every observation.

Use the same host on AC power, avoid concurrent workloads, and run one matched pair at a time. Alternate implementation order deterministically across pairs and record the schedule. Document the OS cache policy and use pairing and order alternation to mitigate cache and order effects. Claim cold OS caches only for runs where the policy explicitly enforces that state.

## Frozen analysis and failure handling

Before generating D's data, write and freeze the analysis script, configuration matrix, manifest, schedule, workload boundaries, exclusions, and statistics. Run ten repetitions per configuration. Retain all raw values and report each implementation's median wall time and IQR for each configuration, using the specified measurement boundary.

For matched repetition `i`, compute `S_i = T_DyNetiKAT_i / T_Lean_i`. Define configuration-level speedup as the median of its ten paired ratios. The primary overall aggregate is the geometric mean of configuration-level speedups, with each predetermined configuration equally weighted. Secondary summaries include median matched speedup, ratio of total elapsed times over matched observations, minimum and maximum, and IQR. If reporting bootstrap confidence intervals, freeze the method and resample in a way that preserves pairing. Keep the arithmetic mean of ratios out of the headline. Use the complete predetermined matrix for the primary result and disclose any incompleteness.

Keep C and D uncensored by default. For D record `crossed_300s=true/false` and actual elapsed wall time through termination, including for unsuccessful processes. Preserve nonzero exits, interruptions, invalid observations, and any explicitly imposed cutoff together with their logs and reason. Do not silently discard attempts or retry until favorable. If a documented recovery is needed, link it to the original attempt and apply the frozen analysis policy.

## Reviewer traceability

Every paper number must trace from the paper table to the generated CSV, to the raw JSONL record or records, to the exact invocation and the binary, container where used, and input hashes. Include stable configuration and repetition IDs, command arguments, working directory, environment, exit status, verdicts, and phase measurements in that chain. Publish absolute times alongside ratios and explain large differences with the measured phase breakdown and observed process structure. Label timeout-subset speedups as conditional development results and keep them out of the abstract and headline. Use the complete canonical campaign for headline claims.
