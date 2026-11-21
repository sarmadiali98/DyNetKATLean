#!/usr/bin/env python3
"""Capture v1.1 observations and native Lean results outside the proof build."""

import argparse
from collections import Counter, defaultdict
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import re
import shutil
from statistics import median
import subprocess
import sys
import tarfile
import time

PIN = "1c6bd422377853378c7516a7875009fcfb5ba881"
FIXED = ("stateful_firewall.json", "distributed_controller_independent.json",
         "distributed_controller_synchronized.json")
BLOBS = {
    "fattree.py": "9026b2be679eb50fbe90934cdeebd8e498881faa",
    "util.py": "80d561992d09397a4252661d2d1701924bc75ca0",
    FIXED[0]: "d27371403ca7c03c9dba4e38aac3e5755671ebc5",
    FIXED[1]: "9f5a1ff5a70ebf4d84e6f58ee66826fe7a9c8987",
    FIXED[2]: "69519129187010c88492b54a7aefe004194a1a88",
}
GROUPS = ("reachability_1", "reachability_2", "waypointing", "all_properties")
REPORT = re.compile(r"Packet: (.+) - property: #(\d+): (property satisfied|property violated|an error occurred while checking this property)\.")
TIMING = re.compile(r"^(Total|Preprocessing|NetKAT) time: ([0-9.]+) seconds$", re.M)


def write(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, cwd, log):
    start = time.perf_counter()
    with log.open("w") as stdout, log.with_suffix(".stderr").open("w") as stderr:
        rc = subprocess.run(command, cwd=cwd, stdout=stdout, stderr=stderr).returncode
    elapsed = time.perf_counter() - start
    timing = dict((k, float(v)) for k, v in TIMING.findall(log.read_text()))
    return {"command": list(map(str, command)), "cwd": str(cwd), "exit": rc,
            "wall_seconds": elapsed, "reported_seconds": timing,
            "stdout": log.name, "stderr": log.with_suffix(".stderr").name}


def queries(path):
    doc = json.loads(path.read_text())
    for key in doc["in_packets"]:
        for index, (kind, expression, operand, depth) in enumerate(doc["properties"].get(key, [])):
            selector = "nested_tail" if expression.count("tail(") > 1 else (
                "tail" if "tail(" in expression else "head")
            if kind == "w":
                selector = "waypoint"
            yield {"input": path.name, "module": doc["module_name"], "packet": key,
                   "index": index, "kind": kind, "expression": expression, "selector": selector,
                   "polarity": operand if kind == "r" else None, "depth": depth}


def native_records(log, expected):
    records = []
    for line in log.read_text().splitlines():
        item = json.loads(line)
        records.append({"input": Path(item["input"]).name, **item["result"]})
    if len(records) != len(expected):
        raise ValueError(f"{log}: expected {len(expected)} native records, got {len(records)}")
    for row, query in zip(records, expected):
        for key in ("input", "module", "packet", "index", "expression", "depth", "polarity"):
            if row[key] != query[key]:
                raise ValueError(f"{log}: native identity mismatch on {key}: {row}")
        if row["kind"] != {"r": "reachability", "w": "waypoint"}[query["kind"]]:
            raise ValueError(f"{log}: native query kind mismatch")
    return records


def reference_records(log, expected, exit_code):
    observations = {}
    keys = {(q["packet"], q["index"]) for q in expected}
    for line in log.read_text().splitlines():
        match = REPORT.fullmatch(line)
        if not match:
            continue
        packet, index, result = match.groups()
        key = (packet, int(index))
        if key not in keys or key in observations:
            raise ValueError(f"{log}: unexpected or duplicate reference observation {key}")
        observations[key] = result
    rows = []
    for q in expected:
        observed = observations.get((q["packet"], q["index"]))
        verdict = None
        if observed in ("property satisfied", "property violated"):
            verdict = (observed == "property satisfied") == (q["polarity"] != "=0")
        rows.append({**q, "reference_verdict": verdict, "reference_report": observed,
                     "reference_status": "observed" if verdict is not None else "execution_failure",
                     "reference_exit": exit_code})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--reference-results", type=Path,
                        help="replay an archived reference.json without running the historical tool")
    parser.add_argument("--observe-only", action="store_true", help="skip timing repetitions")
    parser.add_argument("--maude", type=Path)
    parser.add_argument("--netkat", type=Path)
    parser.add_argument("--backend", choices=("netkat-idd", "netkat-automata"), default="netkat-idd")
    args = parser.parse_args()
    if any((args.reference, args.maude, args.netkat)) and not all(
            (args.reference, args.maude, args.netkat)):
        parser.error("--reference, --maude and --netkat must be provided together")
    if args.reference and args.reference_results:
        parser.error("choose live --reference or archived --reference-results")
    for key in ("corpus", "lean", "output", "reference", "maude", "netkat", "reference_results"):
        value = getattr(args, key)
        if value is not None:
            setattr(args, key, value.resolve())
    if not os.access(args.lean, os.X_OK):
        parser.error("--lean must be executable")

    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    logs = out / "logs"
    logs.mkdir()
    generated = out / "generated"
    generated.mkdir()
    instruments = args.corpus
    env = {"platform": platform.platform(), "machine": platform.machine(),
           "python": sys.version, "networkx": __import__("networkx").__version__,
           "pinned_reference": PIN, "reference_available": bool(args.reference),
           "lean_sha256": digest(args.lean), "workers": 1}
    if args.reference:
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=args.reference,
                                         text=True).strip()
        if commit != PIN:
            parser.error(f"reference HEAD is {commit}, expected {PIN}")
        for binary in (args.maude, args.netkat):
            if not os.access(binary, os.X_OK):
                parser.error(f"{binary} must be executable")
        ref = out / "reference"
        ref.mkdir()
        archive = subprocess.check_output(["git", "archive", PIN], cwd=args.reference)
        with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
            tar.extractall(ref, filter="data")
        instruments = ref / "benchmarks"
        env.update(numpy=__import__("numpy").__version__, backend=args.backend, maude_sha256=digest(args.maude),
                   netkat_sha256=digest(args.netkat), maude=str(args.maude), netkat=str(args.netkat))
    env["generator_blobs"] = {}
    for name, expected_blob in BLOBS.items():
        raw = (instruments / name).read_bytes()
        blob = hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()
        if blob != expected_blob:
            raise ValueError(f"{name}: expected pinned blob {expected_blob}, got {blob}")
        env["generator_blobs"][name] = blob
    write(out / "environment.json", env)

    for name in ("fattree.py", "util.py"):
        shutil.copyfile(instruments / name, generated / name)
    generation = run([sys.executable, "fattree.py"], generated, logs / "generator.stdout")
    write(out / "generator-run.json", generation)
    if generation["exit"]:
        raise SystemExit("generator failed; see generator logs")
    matrix = [(pods, group, generated / f"fattree_{pods}_pods_{group}.json")
              for pods in (6, 8, 10, 12, 14, 16) for group in GROUPS]
    comparisons = []
    for pods, group, path in matrix:
        old = args.corpus / path.name
        a, b = digest(path), digest(old)
        status = "exact" if a == b else ("json_equal" if json.loads(path.read_text()) ==
                                          json.loads(old.read_text()) else "json_difference")
        comparisons.append({"file": path.name, "pods": pods, "group": group,
                            "generated_sha256": a, "baseline_sha256": b, "status": status})
    write(out / "generator-comparison.json", comparisons)
    # Reuse archived input bytes for both implementations and for timings.
    matrix = [(pods, group, args.corpus / path.name) for pods, group, path in matrix]
    inputs = [instruments / name for name in FIXED] + [path for _, _, path in matrix]
    write(out / "inputs.json", {p.name: digest(p) for p in inputs})
    input_hashes = {p.name: digest(p) for p in inputs}
    expected = [{**q, "input_sha256": input_hashes[p.name]} for p in inputs for q in queries(p)]
    if len(expected) != 120:
        raise ValueError(f"expected 120 queries, found {len(expected)}")

    native = {}
    for mode, flags in (("reused", []), ("fresh", ["--fresh"])):
        log = logs / f"lean-{mode}.jsonl"
        item = run([args.lean, "batch", "--json", *flags, *inputs], out, log)
        write(out / f"lean-{mode}-run.json", item)
        native[mode] = native_records(log, expected)
    write(out / "fresh-reused.json", {"total": 120, "identical": sum(
        a == b for a, b in zip(native["reused"], native["fresh"]))})

    def reference_command(path):
        return [sys.executable, ref / "dnk.py", args.maude, args.netkat, path,
                "-t", "1", "-v", args.backend, "-s"]

    observations = []
    cached = {}
    for path in inputs:
        wanted = [{**q, "input_sha256": input_hashes[path.name]} for q in queries(path)]
        if args.reference:
            log = logs / f"reference-{path.stem}.stdout"
            item = run(reference_command(path), ref, log)
            write(log.with_suffix(".json"), item)
            observations.extend(reference_records(log, wanted, item["exit"]))
            artifact = ref / "output" / (wanted[0]["module"] + "_preprocessed.json")
            if artifact.is_file():
                cache_dir = out / "reference-preprocessed"
                cache_dir.mkdir(exist_ok=True)
                cached[path.name] = cache_dir / path.name
                shutil.copyfile(artifact, cached[path.name])
                artifact.unlink()
        else:
            observations.extend({**q, "reference_status": "runtime_unavailable",
                                 "reference_verdict": None} for q in wanted)
    if args.reference_results:
        observations = json.loads(args.reference_results.read_text())
        if len(observations) != len(expected) or any(
            any(row.get(k) != v for k, v in q.items()) for row, q in zip(observations, expected)
        ):
            raise ValueError("archived reference query identity or input checksum changed")
        for row in observations:
            verdict = row["reference_verdict"]
            if row["reference_status"] == "observed":
                if type(verdict) is not bool:
                    raise ValueError("observed reference verdict must be Boolean")
            elif verdict is not None:
                raise ValueError("unavailable reference verdict must be null")
    write(out / "reference.json", observations)
    differential = []
    for q, lean in zip(observations, native["reused"]):
        rv, lv = q["reference_verdict"], lean["verdict"]
        status = ("uncomparable" if rv is None or lv is None else
                  "match" if rv == lv else "mismatch")
        differential.append({**q, "lean_verdict": lv, "lean_diagnostic": lean["diagnostic"],
                             "fixture_agreement": lean["expectation_agrees"], "comparison": status})
    write(out / "differential.json", differential)
    groups = defaultdict(Counter)
    for d in differential:
        for key in {"all", d["kind"], d["selector"], d["polarity"] or "waypoint"}:
            groups[key][d["comparison"]] += 1
            groups[key]["reference_" + d["reference_status"]] += 1
            groups[key]["lean_nonverdict"] += d["lean_verdict"] is None
    write(out / "differential-summary.json", groups)

    if args.observe_only:
        return
    buckets = defaultdict(list)
    with (out / "timings.jsonl").open("w") as stream:
        for pods, group, path in matrix:
            modes = [("lean-reused", [args.lean, "batch", "--json", path], out),
                     ("lean-fresh", [args.lean, "batch", "--json", "--fresh", path], out)]
            if args.reference:
                modes.append(("reference-raw", reference_command(path), ref))
                if path.name in cached:
                    modes.append(("reference-reused", reference_command(cached[path.name]) + ["-p"], ref))
            for implementation, command, cwd in modes:
                key = f"{implementation}/{pods}/{group}"
                for repeat in range(1, 11):
                    log = logs / f"{implementation}-{pods}-{group}-{repeat:02d}.stdout"
                    item = run(command, cwd, log)
                    expected_rows = list(queries(path))
                    try:
                        if implementation.startswith("reference-"):
                            verdicts = reference_records(log, expected_rows, item["exit"])
                            missing = sum(row["reference_verdict"] is None for row in verdicts)
                            success = item["exit"] == 0 and missing == 0
                        else:
                            verdicts = native_records(log, expected_rows)
                            missing = sum(row["verdict"] is None for row in verdicts)
                            success = item["exit"] in (0, 1) and missing == 0
                    except ValueError as error:
                        missing, success = len(expected_rows), False
                        item["report_error"] = str(error)
                    item.update(implementation=implementation, pods=pods, group=group,
                                input_bytes=path.stat().st_size, repeat=repeat, success=success,
                                nonverdicts=missing)
                    stream.write(json.dumps(item, sort_keys=True) + "\n")
                    stream.flush()
                    buckets[key].append(item)
    write(out / "reference-reuse-unavailable.json", [
        path.name for _, _, path in matrix if path.name not in cached])
    write(out / "timing-summary.json", {
        key: {"runs": len(items), "success": sum(r["success"] for r in items),
              "median_wall_seconds": median(r["wall_seconds"] for r in items)}
        for key, items in buckets.items()})


if __name__ == "__main__":
    main()
