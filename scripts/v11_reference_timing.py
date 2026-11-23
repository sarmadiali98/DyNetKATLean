#!/usr/bin/env python3
"""Measure the pinned v1.1 reference serially, with resumable raw results."""

import argparse
from collections import Counter, defaultdict
import fcntl
import json
import os
from pathlib import Path
import platform
import shutil
from statistics import median
import subprocess
import time
from datetime import datetime, timezone

from v11_campaign import GROUPS, PIN, TIMING, digest, positive_timeout, queries, reference_records, wait_for_process, write

SCALES = (6, 8, 10, 12, 14, 16)
ROOT = Path(__file__).resolve().parents[1]


def run_timed(command, cwd, env, log, timeout):
    stdout, stderr, resources = (log.with_suffix(s) for s in (".stdout", ".stderr", ".time"))
    timed_command = ["/usr/bin/time", "-o", str(resources), "-f", "%U %S %M", *command]
    start = time.monotonic()
    with stdout.open("w") as out, stderr.open("w") as err:
        with subprocess.Popen(timed_command, cwd=cwd, env=env, start_new_session=True,
                              stdout=out, stderr=err) as child:
            code = wait_for_process(child, timeout)
    elapsed = time.monotonic() - start
    values = resources.read_text().split() if resources.exists() else []
    return {
        "exit": code, "status": "timeout" if code is None else "failure",
        "wall_seconds": elapsed, "timeout_seconds": timeout,
        "resource_usage": dict(zip(("user_seconds", "system_seconds", "peak_rss_kib"),
                                   map(float, values))) if len(values) == 3 and code == 0 else None,
        "reported_seconds": {k: float(v) for k, v in TIMING.findall(stdout.read_text())},
        "stdout_sha256": digest(stdout), "stderr_sha256": digest(stderr),
    }


def stage_reused(path, differential, destination):
    raw = json.loads(path.read_text())
    filename = raw["module_name"] + "_preprocessed.json"
    direct = [differential / (path.stem + "-" + mode) / "output" / filename
              for mode in ("fresh1", "extended")]
    source = next((candidate for candidate in direct if candidate.is_file()), None)
    if source is not None:
        shutil.copyfile(source, destination)
        rebound = False
    else:
        prefix = path.stem.split("_pods_")[0] + "_pods_"
        suffix = {"fattree_14_pods_": "reachability_1-fresh1",
                  "fattree_16_pods_": "all_properties-extended"}[prefix]
        anchor_group = suffix.rsplit("-", 1)[0]
        anchor_raw = json.loads((path.parent / (prefix + anchor_group + ".json")).read_text())
        if {k: v for k, v in raw.items() if k != "properties"} != {
                k: v for k, v in anchor_raw.items() if k != "properties"}:
            raise ValueError(f"preprocessing anchor does not describe the same input: {path}")
        source = differential / (prefix + suffix) / "output" / filename
        preprocessed = json.loads(source.read_text())
        if preprocessed["properties"] != anchor_raw["properties"]:
            raise ValueError(f"preprocessing anchor properties changed: {source}")
        preprocessed["properties"] = raw["properties"]
        destination.write_text(json.dumps(preprocessed, ensure_ascii=False, indent=4))
        rebound = True
    if json.loads(destination.read_text())["properties"] != raw["properties"]:
        raise ValueError(f"property map changed: {path}")
    return {"source": str(source), "source_sha256": digest(source),
            "sha256": digest(destination), "property_map_rebound": rebound}


def summarize(rows):
    groups = defaultdict(list)
    for row in rows:
        groups[f'{row["mode"]}/{row["pods"]}/{row["group"]}'].append(row)
        groups[row["mode"]].append(row)
    result = {}
    for group, items in groups.items():
        completed = [r["wall_seconds"] for r in items if r["status"] == "completed"]
        result[group] = {
            "attempted": len(items), **Counter(r["status"] for r in items),
            "median_wall_seconds": median(completed) if completed else None,
            "range_wall_seconds": [min(completed), max(completed)] if completed else None,
        }
    return result


def attempt_key(row):
    return row["pods"], row["group"], row["mode"], row["repeat"]


def recovery_selection(rows):
    expected = {(n, g, mode, r) for n in SCALES for g in GROUPS
                for mode in ("fresh", "reused") for r in range(1, 11)}
    if len(rows) != len(expected) or {attempt_key(row) for row in rows} != expected:
        raise ValueError("recovery requires the complete original matrix with unique IDs")
    if len({row["log"] for row in rows}) != len(rows):
        raise ValueError("duplicate original attempt ID")
    selected = {attempt_key(row): row for row in rows if row["status"] == "timeout"}
    counts = Counter((row["pods"], row["group"], row["mode"]) for row in selected.values())
    required = {(n, g, "fresh"): 10 for n in (14, 16) for g in GROUPS}
    required[16, "all_properties", "reused"] = 10
    if counts != required or any(row["timeout_seconds"] != 300 for row in rows):
        raise ValueError("unexpected original timeout accounting")
    return selected


def retry_metadata(source):
    if source is None:
        return {}
    return dict(retry_of=source["log"], original_status=source["status"],
                original_timeout_seconds=source["timeout_seconds"])


def recorded_attempts(rows, selected):
    done = set()
    for row in rows:
        key = attempt_key(row)
        expected_link = retry_metadata(selected[key]) if selected is not None else {}
        if key in done or any(row.get(k) != v for k, v in expected_link.items()):
            raise ValueError("duplicate attempt or invalid recovery link")
        done.add(key)
    return done


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--timeout", type=positive_timeout, metavar="SECONDS",
                        help="per-attempt timeout in seconds (omitted: no timeout)")
    parser.add_argument("--retry-timeouts-from", type=Path, metavar="DIRECTORY",
                        help="retry timeouts from a completed standardized campaign")
    args = parser.parse_args()
    runtime, out = args.runtime.resolve(), args.results.resolve()
    selected = None
    source_dir = args.retry_timeouts_from
    if source_dir is not None:
        source_dir = source_dir.resolve()
        if out == source_dir or source_dir in out.parents or out in source_dir.parents:
            parser.error("recovery needs a separate results directory")
        with (source_dir / ".lock").open() as source_lock:
            try:
                fcntl.flock(source_lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
            except BlockingIOError:
                parser.error("the original campaign is still active")
            source_records = source_dir / "timings.jsonl"
            source_bytes = source_records.read_bytes()
            selected = recovery_selection([json.loads(line) for line in source_bytes.splitlines()])
            original = json.loads((source_dir / "manifest.json").read_text())
            if original["timeout_seconds"] != 300:
                parser.error("the original manifest must record the 300-second timeout")
    out.mkdir(parents=True, exist_ok=True)
    lock = (out / ".lock").open("w")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        parser.error("this results directory already has an active runner")
    evidence = json.loads((ROOT / "docs/DYNETIKAT_V11_REFERENCE_EVIDENCE.json").read_text())
    provenance = evidence["provenance"]
    paths = {k: Path(p) for k, p in provenance["paths"].items()}
    for path, sha in provenance["binary_sha256"].items():
        if digest(Path(path)) != sha:
            raise ValueError(f"runtime binary changed: {path}")
    if paths["reference"] != runtime / ("DyNetiKAT-" + PIN):
        raise ValueError("runtime path does not match recorded reference provenance")
    matrix = [(n, g, runtime / "corpus" / f"fattree_{n}_pods_{g}.json")
              for n in SCALES for g in GROUPS]
    expected_rows = defaultdict(list)
    for row in evidence["queries"]:
        expected_rows[row["input"]].append(row)

    work = out / "reference"
    work.mkdir(exist_ok=True)
    shutil.copyfile(paths["reference"] / "dnk.py", work / "dnk.py")
    shutil.copytree(paths["reference"] / "src", work / "src", dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns("__pycache__"))
    logs = out / "logs"
    logs.mkdir(exist_ok=True)
    preprocessed = out / "preprocessed"
    preprocessed.mkdir(exist_ok=True)
    cpu_fields = {"Model name:", "CPU(s):", "Thread(s) per core:", "Core(s) per socket:",
                  "Socket(s):", "CPU min MHz:", "CPU max MHz:"}
    cpu = json.loads(subprocess.check_output(["lscpu", "--json"], text=True))["lscpu"]
    manifest = {
        "host": {"platform": platform.platform(), "architecture": platform.machine(),
                 "cpu": {r["field"].rstrip(":"): r["data"] for r in cpu if r["field"] in cpu_fields},
                 "affinity_cpus": sorted(os.sched_getaffinity(0)),
                 "mem_total": Path("/proc/meminfo").read_text().splitlines()[0],
                 "os_release": Path("/etc/os-release").read_text()},
        "runtime": provenance, "modes": ["fresh", "reused"], "workers": 1,
        "repetitions": 10, "warmup_runs": 0, "timeout_seconds": args.timeout,
        "target": 480, "inputs": {}, "preprocessing": {},
    }
    if selected is not None:
        manifest.update(target=len(selected), recovery={
            "source": str(source_records), "source_sha256": digest(source_records),
            "selection": [dict(id=row["log"], pods=row["pods"], group=row["group"],
                               mode=row["mode"], repeat=row["repeat"], status=row["status"],
                               timeout_seconds=row["timeout_seconds"]) for row in selected.values()],
        })
        for key in ("host", "runtime", "workers"):
            if original[key] != manifest[key]:
                raise ValueError(f"recovery configuration differs from original: {key}")
    for _, _, path in matrix:
        expected = expected_rows[path.name]
        if digest(path) != expected[0]["input_sha256"]:
            raise ValueError(f"corpus input changed: {path}")
        manifest["inputs"][path.name] = digest(path)
        if selected is None:
            manifest["preprocessing"][path.name] = stage_reused(
                path, runtime / "differential", preprocessed / path.name)
        else:
            staged = source_dir / "preprocessed" / path.name
            entry = original["preprocessing"][path.name]
            if digest(staged) != entry["sha256"] or digest(path) != original["inputs"][path.name]:
                raise ValueError(f"original timing input changed: {path}")
            manifest["preprocessing"][path.name] = entry
    manifest_path = out / "manifest.json"
    if manifest_path.exists() and json.loads(manifest_path.read_text()) != manifest:
        raise ValueError("campaign configuration changed; use a fresh results directory")
    write(manifest_path, manifest)

    records = out / "timings.jsonl"
    rows = [json.loads(line) for line in records.read_text().splitlines()] if records.exists() else []
    done = recorded_attempts(rows, selected)
    (out / "current.json").unlink(missing_ok=True)
    env = dict(os.environ, **provenance["maude_environment"], PYTHONDONTWRITEBYTECODE="1")
    with records.open("a", buffering=1) as stream:
        for repeat in range(1, 11):
            for pods, group, path in matrix:
                for mode in ("fresh", "reused"):
                    identity = (pods, group, mode, repeat)
                    if identity in done or (selected is not None and identity not in selected):
                        continue
                    reused = preprocessed if selected is None else source_dir / "preprocessed"
                    chosen = path if mode == "fresh" else reused / path.name
                    command = [str(paths["python"]), "-c", provenance["launcher"], str(work / "dnk.py"),
                               str(paths["maude"]), str(paths["katbv"]), str(chosen),
                               "-t", "1", "-v", "netkat-idd", "-s"]
                    if mode == "reused":
                        command.append("-p")
                    local_output = work / "output"
                    if local_output.exists():
                        shutil.rmtree(local_output)
                    (work / "FAT-TREE.maude").unlink(missing_ok=True)
                    for artifact in work.glob("output_*.txt"):
                        artifact.unlink()
                    key = f"{pods}-{group}-{mode}-{repeat:02d}"
                    log = logs / key
                    link = {}
                    if selected is not None:
                        link = retry_metadata(selected[identity])
                        log = logs / f"retry-{key}"
                        # Preserve partial raw logs if an attempt was interrupted before its result was flushed.
                        while log.with_suffix(".stdout").exists():
                            log = log.with_name(log.name + "-resume")
                    current = dict(attempt_id=log.name, **link, started_at=datetime.now(timezone.utc).isoformat())
                    write(out / "current.json", current)
                    try:
                        row = run_timed(command, work, env, log, args.timeout)
                    except KeyboardInterrupt:
                        with (out / "interruptions.jsonl").open("a") as interruptions:
                            interruptions.write(json.dumps(current) + "\n")
                        raise
                    row.update(pods=pods, group=group, repeat=repeat, mode=mode, command=command,
                               log=log.name, attempt_id=log.name, **link)
                    if row["exit"] == 0:
                        try:
                            verdicts = reference_records(log.with_suffix(".stdout"), list(queries(path)), 0)
                            expected = expected_rows[path.name]
                            if [r["reference_verdict"] for r in verdicts] == [
                                    r["reference_verdict"] for r in expected]:
                                row["status"] = "completed"
                            else:
                                row["diagnostic"] = "reports differ from validated reference observations"
                        except ValueError as exc:
                            row["diagnostic"] = str(exc)
                    stream.write(json.dumps(row, sort_keys=True) + "\n")
                    rows.append(row)
                    (out / "current.json").unlink()
                    write(out / "summary.json", summarize(rows))
                    print(f'{len(rows)}/{manifest["target"]} {key}: {row["status"]} {row["wall_seconds"]:.3f}s', flush=True)


if __name__ == "__main__":
    main()
