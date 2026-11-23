#!/usr/bin/env python3
"""Run isolated, single-worker v1.1 forensic comparisons."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
import os
import re
from pathlib import Path
import shutil
import shlex
import tarfile
import subprocess
import platform
import time

from v11_campaign import GROUPS, digest, native_records, queries, reference_records, TIMING, write

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "docs/DYNETIKAT_V11_REFERENCE_EVIDENCE.json"
LEAN = ROOT / "lean/.lake/build/bin/dynetkat"

# Separate observation pass. No changes to the pinned program or executables.
TRACE = r"""
import multiprocessing.process
import os
import sys
import time
import json
import shlex

fd = os.open(os.environ["DNK_AUDIT_LOG"], os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)

def log(event, **fields):
    entry = dict(event=event, pid=os.getpid(), ppid=os.getppid(),
                 monotonic=time.monotonic(), **fields)
    os.write(fd, (json.dumps(entry, default=str) + "\n").encode())

def audit(event, args):
    if event == "subprocess.Popen":
        executable, argv = args[:2]
        launched = shlex.split(argv[2])[0] if os.path.basename(executable) == "sh" and argv[1] == "-c" else executable
        log(event, executable=launched, launcher=executable, argv=argv)
    if event == "open" and isinstance(args[0], str):
        log(event, path=args[0], mode=args[1])

def profile(frame, event, arg):
    if event not in ("call", "return"):
        return
    filename = frame.f_code.co_filename
    name = frame.f_code.co_name
    if ((filename.endswith("/multiprocessing/process.py") and name == "run")
        or (filename.endswith("/subprocess.py") and name in ("run", "_execute_child"))
        or (filename.endswith("/dnk.py") and name == "<module>")
        or ("/src/python/" in filename and name in (
            "preprocess", "decide", "process", "netkat_process",
            "execute", "tool_format", "generate_maude_file", "report_results",
            "hbh_reachability_term", "waypointing_term", "compute_encapsulation_set"))
        or (filename.endswith("/json/__init__.py") and name in ("load", "dump"))):
        fields = dict(function=name, source=filename, line=frame.f_code.co_firstlineno)
        if name == "_execute_child" and event == "return":
            fields["child_pid"] = frame.f_locals["self"].pid
        if name == "process" and filename.endswith("/dynetkat.py"):
            fields["packet"] = frame.f_locals["q"]
            fields["index"] = frame.f_locals["counter"]
        if name == "<module>" and event == "return":
            fields["source_clocks"] = {
                key: frame.f_globals[key] for key in (
                    "program_start", "preprocessing_start", "preprocessing_stop", "program_stop")
                if key in frame.f_globals
            }
        log(event, **fields)

sys.addaudithook(audit)
sys.setprofile(profile)
"""


def timed(command, cwd, env, folder):
    folder.mkdir()
    stdout, stderr, resources = (folder / name for name in ("stdout", "stderr", "time"))
    started_at = datetime.now(timezone.utc).isoformat()
    with stdout.open("w") as out, stderr.open("w") as err:
        start = time.monotonic_ns()
        process = subprocess.run(
            ["/usr/bin/time", "-v", "-o", str(resources), *map(str, command)],
            cwd=cwd, env=dict(env, LC_ALL="C"), stdout=out, stderr=err,
        )
        stop = time.monotonic_ns()
    wall = (stop - start) / 1_000_000_000
    metrics = time_metrics(resources.read_text())
    return dict(command=list(map(str, command)), cwd=str(cwd), exit=process.returncode,
                wall_seconds=wall, gnu_time=metrics, started_at=started_at,
                finished_at=datetime.now(timezone.utc).isoformat(),
                harness_monotonic_ns=[start, stop],
                stdout_sha256=digest(stdout), stderr_sha256=digest(stderr),
                reported_seconds={k: float(v) for k, v in TIMING.findall(stdout.read_text())})


def time_metrics(output):
    values = dict(line.strip().rsplit(": ", maxsplit=1) for line in output.splitlines()
                  if ": " in line)
    durations = [float(value) for value in
                 values["Elapsed (wall clock) time (h:mm:ss or m:ss)"].split(":")]
    metrics = {"elapsed_seconds": sum(value * 60 ** index
                                      for index, value in enumerate(reversed(durations)))}
    for key, field in {
        "user_seconds": "User time (seconds)", "system_seconds": "System time (seconds)",
        "max_rss_kib": "Maximum resident set size (kbytes)", "fs_inputs": "File system inputs",
        "fs_outputs": "File system outputs", "voluntary_switches": "Voluntary context switches",
        "involuntary_switches": "Involuntary context switches",
    }.items():
        metrics[key] = float(values[field])
    return metrics


def summarize_trace(path):
    active = {}
    scopes = {}
    processes = {}
    spans = []
    opens = set()
    for line in path.read_text().splitlines():
        entry = json.loads(line)
        pid, event = entry["pid"], entry["event"]
        function = entry.get("function")
        source = Path(entry.get("source", "")).name
        timestamp = entry["monotonic"]
        if event == "open":
            opens.add((entry["path"], entry["mode"] or ""))
        elif event == "call" and source == "process.py" and function == "run":
            processes[pid] = entry["ppid"]
        elif event == "subprocess.Popen":
            executable = Path(entry["executable"]).name
            active[pid] = (executable, timestamp)
        elif event == "return" and function == "_execute_child" and pid in active:
            executable, start = active[pid]
            active[pid] = (executable, start, entry.get("child_pid"))
        elif event == "return" and source == "subprocess.py" and function == "run" and pid in active:
            executable, start, child = active.pop(pid)
            phase = ("preprocess" if (pid, "preprocess.py", "netkat_process") in scopes
                     or (pid, "preprocess.py", "preprocess") in scopes else "analysis")
            spans.append(dict(executable=executable, phase=phase, parent=pid, pid=child,
                              start=start, elapsed=timestamp - start))
        if function and source != "subprocess.py":
            key = (pid, source, function)
            if event == "call":
                scopes[key] = timestamp
            elif event == "return" and key in scopes:
                start = scopes.pop(key)
                if function in {"load", "dump", "preprocess", "decide", "process", "report_results",
                                "generate_maude_file", "execute", "tool_format", "<module>",
                                "hbh_reachability_term", "waypointing_term", "compute_encapsulation_set"}:
                    spans.append(dict(function=function, source=source, pid=pid, start=start,
                                      elapsed=timestamp - start,
                                      **{field: entry[field] for field in ("packet", "index", "source_clocks") if field in entry}))
    counts = Counter((span["phase"], span["executable"]) for span in spans if "executable" in span)
    return {"workers": processes, "spans": spans, "python_opens": sorted(opens),
            "invocation_counts": {"/".join(key): value for key, value in sorted(counts.items())}}


def verdicts(log, expected, exit_code, implementation):
    if implementation == "lean":
        result = native_records(log, expected)
        if any(item["diagnostic"] is not None for item in result):
            raise ValueError("Lean returned a non-verdict")
        values = [item["verdict"] for item in result]
    else:
        values = [item["reference_verdict"] for item in reference_records(log, expected, exit_code)]
    if not all(type(value) is bool for value in values):
        raise ValueError(f"{implementation} produced an incomplete verdict vector")
    return values


def network_size(document, pods):
    expected = pods ** 3 // 4 + pods ** 2 + pods ** 2 // 4
    observed_ids = {int(match) for policy in document["recursive_variables"].values()
                    for match in re.findall(r"\bsw\s*=\s*(\d+)", policy)}
    if observed_ids != set(range(expected)):
        raise ValueError(f"policy switch IDs do not cover the {expected}-switch FatTree")
    return expected


def audit_case(folder, path, provenance, baseline, traced=False, prepared=None, lean_fresh=False,
               metadata=None, lean_exit=0, lean_phases=None, check_malformed=False):
    folder.mkdir()
    work = folder / "reference"
    work.mkdir()
    source = Path(provenance["paths"]["reference"])
    shutil.copyfile(source / "dnk.py", work / "dnk.py")
    shutil.copytree(source / "src", work / "src", ignore=shutil.ignore_patterns("__pycache__"))
    cwd = folder / "alternate-cwd"
    cwd.mkdir()
    env = dict(os.environ, **provenance["maude_environment"], PYTHONDONTWRITEBYTECODE="1",
               DNK_AUDIT_LOG=str(folder / "audit.jsonl"))
    paths = provenance["paths"]
    launcher = (TRACE + "\n" if traced else "") + provenance["launcher"]
    command = [paths["python"], "-c", launcher, work / "dnk.py", paths["maude"],
               paths["katbv"], prepared or path, "-t", "1", "-v", "netkat-idd", "-s"]
    if prepared:
        command.append("-p")
    expected = list(queries(path))
    document = json.loads(path.read_text())
    properties = [
        dict(query, updates=[{"channel": channel, "payload": payload} for channel, payload in
                             re.findall(r'rcfg\(([^,]+),\s*"([^"]*)"\)', query["expression"])],
             operand=document["properties"][query["packet"]][query["index"]][2])
        for query in expected
    ]
    identities = {(item["kind"], item["expression"], item["operand"], item["depth"],
                   document["in_packets"][item["packet"]], document["out_packets"][item["packet"]])
                  for item in properties}
    if len(identities) != len(properties):
        raise ValueError("input repeats a semantic question")
    if any(item["expression"].count("tail(") != len(item["updates"]) for item in properties):
        raise ValueError("could not recover the ordered update sequence")
    row = dict(input=str(path), sha256=digest(path), properties=properties,
               expected_count=len(expected), workers=1,
               prepared_sha256=digest(prepared) if prepared else None, traced=traced,
               packet_predicates={key: document[key]
                                  for key in ("in_packets", "out_packets")})
    row.update(metadata or {})
    lean_env = reference_env = env
    if traced:
        interposer = folder / "lean-trace.so"
        subprocess.run(["cc", "-Wall", "-Wextra", "-shared", "-fPIC", "-o", str(interposer),
                        str(ROOT / "scripts/v11_benchmark_file_trace.c"), "-ldl"], check=True)
        lean_env = dict(env, LD_PRELOAD=str(interposer), DNK_FILE_AUDIT_LOG=str(folder / "lean-audit.tsv"))
        reference_env = dict(env, LD_PRELOAD=str(interposer),
                             DNK_FILE_AUDIT_LOG=str(folder / "reference-native-audit.tsv"))
    row["lean"] = timed([LEAN, "batch", "--json", *(["--fresh"] if lean_fresh else []), path],
                        cwd, lean_env, folder / "lean")
    row["reference"] = timed(command, cwd, reference_env, folder / "historical")
    for impl, dirname in (("lean", "lean"), ("reference", "historical")):
        value = row[impl]
        value["verdicts"] = verdicts(folder / dirname / "stdout", expected, value["exit"], impl)
        value["actual_count"] = len(value["verdicts"])
    row["timers_agree"] = timers_agree(row)
    row["matches"] = (row["lean"]["verdicts"] == row["reference"]["verdicts"] == baseline
                      and row["timers_agree"] and row["lean"]["exit"] == lean_exit and row["reference"]["exit"] == 0)
    if lean_phases:
        side = timed([lean_phases, path], cwd, env, folder / "lean-phases")
        side["verdicts"] = verdicts(folder / "lean-phases/stdout", expected, side["exit"], "lean")
        phase_values = dict(line.split() for line in (folder / "lean-phases/stderr").read_text().splitlines())
        clocks = [int(phase_values.pop(key)) for key in ("entry_clock", "exit_clock")]
        low, high = side["harness_monotonic_ns"]
        side["clock_alignment"] = low <= clocks[0] <= clocks[1] <= high
        if side["clock_alignment"]:
            side["launch_to_lean_entry_ns"] = clocks[0] - low
            side["lean_exit_marker_to_reap_ns"] = high - clocks[1]
        side["phases_ns"] = {key: int(value) for key, value in phase_values.items() if not key.startswith("route/")}
        side["query_routes_from_source_guards"] = {key.removeprefix("route/"): value
                                                   for key, value in phase_values.items() if key.startswith("route/")}
        row["lean_phases"] = side
        row["matches"] &= (side["verdicts"] == baseline and side["exit"] == lean_exit
                           and side["clock_alignment"])
    if traced:
        trace = folder / "audit.jsonl"
        lean_trace = folder / "lean-audit.tsv"
        lean_events = [line.split("\t") for line in lean_trace.read_text().splitlines()]
        lean_processes = [event for event in lean_events
                          if event[2:] == ["process_start", str(LEAN)]]
        lean_pids = {event[0] for event in lean_processes}
        native_trace = folder / "reference-native-audit.tsv"
        native_events = [line.split("\t") for line in native_trace.read_text().splitlines()]
        native_starts = [event for event in native_events if event[2] == "process_start"]
        backend_counts = Counter(Path(event[3]).name for event in native_starts
                                 if Path(event[3]).name in ("maude", "katbv"))
        row["trace"] = {"historical_sha256": digest(trace), "lean_sha256": digest(lean_trace),
                        "reference_native_sha256": digest(native_trace),
                        "reference_native_processes": native_starts,
                        "reference_backend_counts": dict(backend_counts),
                        "lean_processes": lean_processes,
                        "lean_opens": [event for event in lean_events
                                       if event[0] in lean_pids and event[2] in {"fopen", "open"}],
                        **summarize_trace(trace)}
        expected_analysis = {f"analysis/{tool}": len(expected) for tool in ("maude", "katbv")}
        invocations = row["trace"]["invocation_counts"]
        expected_preprocess_maude = 0 if prepared else len(document["recursive_variables"])
        row["matches"] &= (dict(backend_counts) == {
                               tool: sum(count for key, count in invocations.items() if key.endswith("/" + tool))
                               for tool in ("maude", "katbv")}
                           and all(invocations.get(key) == count for key, count in expected_analysis.items())
                           and invocations.get("preprocess/maude", 0) == expected_preprocess_maude
                           and len(lean_processes) == 1
                           and str(path) in {event[3] for event in row["trace"]["lean_opens"]}
                           and len(row["trace"]["workers"]) == (1 if prepared else 2)
                           and str(prepared or path) in dict(row["trace"]["python_opens"]))
        local_reference_reads = [name for name, mode in row["trace"]["python_opens"]
                                 if mode.startswith("r") and Path(name).is_relative_to(work)
                                 and not name.endswith((".py", ".pyc", ".maude"))]
        unexplained_lean_opens = [event[3] for event in row["trace"]["lean_opens"]
                                  if event[3] != str(path) and not event[3].startswith(("/dev/", "/proc/"))]
        row["trace"]["unexplained_reference_scratch_reads"] = local_reference_reads
        row["trace"]["unexplained_lean_opens"] = unexplained_lean_opens
        row["matches"] &= not local_reference_reads and not unexplained_lean_opens
    if not prepared:
        generated = work / "output" / (document["module_name"] + "_preprocessed.json")
        row["prepared_output"] = {"path": str(generated), "sha256": digest(generated)}
    if check_malformed:
        invalid = cwd / "invalid.json"
        invalid.write_text('{"module_name":')
        historical = list(command)
        historical[6] = invalid
        # Disable the trace for this second invocation to keep the original trace immutable.
        historical[2] = provenance["launcher"]
        row["malformed"] = {
            "lean": timed([LEAN, "batch", "--json", invalid], cwd, env, folder / "lean-invalid"),
            "reference": timed(historical, cwd, env, folder / "historical-invalid"),
        }
        for impl, dirname in (("lean", "lean-invalid"), ("reference", "historical-invalid")):
            row["matches"] &= row["malformed"][impl]["exit"] != 0 and not (
                folder / dirname / "stdout").read_text().strip()
    write(folder / "result.json", row)
    print(folder.name, row["matches"], row["reference"]["wall_seconds"], flush=True)
    if not row["matches"]:
        raise ValueError("verdict or exit-status mismatch")


def timers_agree(row):
    external = row["reference"]["wall_seconds"]
    internal = row["reference"]["reported_seconds"].get("Total")
    startup_tolerance = 2.0 if row["traced"] else 0.4
    return (internal is not None and -0.015 <= external - internal <= max(startup_tolerance, external * 0.01)
                           and all(abs(run["wall_seconds"] - run["gnu_time"]["elapsed_seconds"]) < 0.1
                                   for run in (row["lean"], row["reference"])))

def verify_reference_source(source, archive, provenance):
    if digest(archive) != provenance["archive_sha256"][archive.name]:
        raise ValueError("reference source archive digest differs from the pinned archive")
    files = {"dnk.py", "run_fattree.sh", "paper.pdf"}
    files.update(str(path.relative_to(source)) for path in (source / "src").rglob("*")
                 if path.is_file() and "__pycache__" not in path.parts)
    with tarfile.open(archive) as bundle:
        prefix = bundle.getmembers()[0].name
        archive_files = {member.name.removeprefix(prefix + "/") for member in bundle
                         if member.isfile() and member.name.startswith(prefix + "/src/")}
        if not archive_files <= files:
            raise ValueError("reference runtime is missing pinned source files")
        for name in files:
            with bundle.extractfile(prefix + "/" + name) as original:
                if original.read() != (source / name).read_bytes():
                    raise ValueError(f"reference runtime differs from pinned archive: {name}")


def build_lean_phases(directory):
    """Relink with the existing native CLI's exact library objects and link options."""
    directory = directory.resolve()
    if directory == ROOT or ROOT in directory.parents:
        raise ValueError("build the forensic executable outside the checkout")
    directory.mkdir()
    lean = ROOT / "lean"
    source = ROOT / "scripts/V11BenchmarkPhases.lean"
    generated = directory / "phases.c"
    obj = generated.with_suffix(".o")
    binary = generated.with_suffix("")
    subprocess.run(["lake", "env", "lean", "--root=" + str(source.parent),
                    "-c", str(generated), str(source)], cwd=lean, check=True)
    subprocess.run(["lake", "env", "leanc", "-O3", "-c", str(generated), "-o", str(obj)],
                   cwd=lean, check=True)
    trace = json.loads((lean / ".lake/build/bin/dynetkat.trace").read_text())
    link = shlex.split(trace["log"][0]["message"].removeprefix(".> "))
    link[link.index("-o") + 1] = str(binary)
    cli = next(arg for arg in link if arg.endswith("/DyNetKAT/Main.c.o.export"))
    link[link.index(cli)] = str(obj)
    subprocess.run(link, cwd=lean, check=True)
    return binary


def live_provenance(provenance):
    def measure(*args, **kwargs):
        return subprocess.check_output(args, text=True, **kwargs).strip()

    paths = {key: Path(path) for key, path in provenance["paths"].items()}
    runtime = paths["reference"].parent
    lean = ROOT / "lean"
    return {
        "historical": provenance,
        "os_release": Path("/etc/os-release").read_text(),
        "kernel": platform.release(),
        "architecture": platform.machine(),
        "cpu": {entry["field"]: entry["data"] for entry in json.loads(measure("lscpu", "--json"))["lscpu"]
                if entry["field"] in {"Model name:", "CPU(s):", "Core(s) per socket:", "Socket(s):",
                                      "Thread(s) per core:", "CPU max MHz:", "CPU min MHz:"}},
        "affinity": sorted(os.sched_getaffinity(0)),
        "memory": Path("/proc/meminfo").read_text().splitlines()[0],
        "effective_cpus": Path("/sys/fs/cgroup/cpuset.cpus.effective").read_text().strip()
                          if Path("/sys/fs/cgroup/cpuset.cpus.effective").exists() else None,
        "cpu_governors": sorted({path.read_text().strip() for path in
                                 Path("/sys/devices/system/cpu").glob("cpu[0-9]*/cpufreq/scaling_governor")}),
        "python_sha256": digest(paths["python"]),
        "python_numpy_networkx": measure(paths["python"], "-c",
            "import platform, numpy, networkx; print(platform.python_version(), numpy.__version__, networkx.__version__)"),
        "ocaml": measure(runtime / "ocaml-prefix/bin/ocamlc", "-version"),
        "opam": measure(runtime / "bin/opam", "--version"),
        "maude": measure(paths["maude"], "--version",
                         env=dict(os.environ, **provenance["maude_environment"])),
        "lean": measure("lake", "env", "lean", "--version", cwd=lean),
        "lean_sha256": digest(LEAN),
        "toolchain": (lean / "lean-toolchain").read_text().strip(),
        "mathlib_checkout": measure("git", "rev-parse", "HEAD", cwd=lean / ".lake/packages/mathlib"),
        "mathlib": next(p["rev"] for p in json.loads((lean / "lake-manifest.json").read_text())["packages"]
                        if p["name"] == "mathlib"),
        "git_head": measure("git", "rev-parse", "HEAD", cwd=ROOT),
    }


def interval_union(intervals):
    total = 0.0
    end = float("-inf")
    for start, stop in sorted(intervals):
        total += max(0.0, stop - max(start, end))
        end = max(end, stop)
    return total


def restore_initial_metadata(row):
    """Bring the first clean timing pass into the final forensic schema."""
    path = Path(row["input"])
    match = re.fullmatch(r"fattree_(16)_pods_(all_properties)\.json", path.name)
    if not match or row["traced"] or "--fresh" not in row["lean"]["command"]:
        raise ValueError("cannot infer metadata for an unknown capture format")
    document = json.loads(path.read_text())
    if digest(path) != row["sha256"]:
        raise ValueError("initial capture input changed")
    row.update(pods=int(match[1]), group=match[2], switches=network_size(document, int(match[1])), perturbation=False,
               original_sha256=row["sha256"], lean_mode="prepare_per_query",
               reference_mode="preprocess_once",
               packet_predicates={key: document[key] for key in ("in_packets", "out_packets")})
    for item in row["properties"]:
        item["updates"] = [{"channel": channel, "payload": payload}
                           for channel, payload in re.findall(r'rcfg\(([^,]+),\s*"([^"]*)"\)',
                                                             item["expression"])]
        item["operand"] = document["properties"][item["packet"]][item["index"]][2]
    for key in ("lean", "reference"):
        row[key]["gnu_time"] = time_metrics(row[key]["resources"])
    row["timers_agree"] = timers_agree(row)
    row["matches"] &= row["timers_agree"]


def summarize_cases(folders):
    cases = []
    for folder in folders:
        folder = folder.resolve()
        result = folder / "result.json"
        row = json.loads(result.read_text())
        if "pods" not in row:
            restore_initial_metadata(row)
        row["result_file"] = str(result)
        row["result_sha256"] = digest(result)
        for kind in ("lean", "historical"):
            record = row["lean" if kind == "lean" else "reference"]
            for name in ("stdout", "stderr"):
                if digest(folder / kind / name) != record[name + "_sha256"]:
                    raise ValueError(f"raw log has changed: {folder / kind / name}")
        if "lean_phases" in row:
            side = row["lean_phases"]
            side["binary_sha256"] = digest(Path(side["command"][0]))
            for name in ("stdout", "stderr"):
                if digest(folder / "lean-phases" / name) != side[name + "_sha256"]:
                    raise ValueError(f"phase log changed: {folder / 'lean-phases' / name}")
        if row["traced"]:
            trace = row["trace"]
            trace["interposer_sha256"] = digest(folder / "lean-trace.so")
            for name, field in (("audit.jsonl", "historical_sha256"), ("lean-audit.tsv", "lean_sha256"),
                                ("reference-native-audit.tsv", "reference_native_sha256")):
                if digest(folder / name) != trace[field]:
                    raise ValueError(f"trace log changed: {folder / name}")
            spans = [span for span in trace["spans"] if "executable" in span]
            for phase in ("preprocess", "analysis"):
                current = [s for s in spans if s["phase"] == phase]
                trace[phase + "_child_seconds_sum"] = {
                    name: sum(s["elapsed"] for s in current if s["executable"] == name)
                    for name in ("maude", "katbv")
                }
                trace[phase + "_child_elapsed_union"] = interval_union(
                    (s["start"], s["start"] + s["elapsed"]) for s in current)
            scope_names = {"preprocess": "preprocess", "analysis": "decide"}
            for phase, function in scope_names.items():
                scope, = [span for span in trace["spans"] if span.get("function") == function]
                start, stop = scope["start"], scope["start"] + scope["elapsed"]
                trace[phase + "_scope_seconds"] = scope["elapsed"]
                formats = [s for s in trace["spans"] if s.get("function") == "tool_format"
                           and start <= s["start"] and s["start"] + s["elapsed"] <= stop]
                trace[phase + "_netkat_formatting_sum"] = sum(s["elapsed"] for s in formats)
                observed = formats + [s for s in spans if s["phase"] == phase]
                covered = interval_union((s["start"], s["start"] + s["elapsed"]) for s in observed)
                trace[phase + "_child_or_format_elapsed_union"] = covered
                trace[phase + "_unattributed_scope_seconds"] = max(0, scope["elapsed"] - covered)
            for function in ("load", "dump"):
                trace["json_" + function + "_seconds"] = sum(
                    s["elapsed"] for s in trace["spans"] if s.get("source") == "__init__.py"
                    and s.get("function") == function)
        cases.append(row)
    roles = {(row.get("pods"), row["traced"], row["expected_count"],
              bool(row["prepared_sha256"]), bool(row.get("perturbation")), "malformed" in row) for row in cases}
    required = {(pods, traced, 9, False, False, pods == 6 and traced)
                for pods in (6, 12, 16) for traced in (False, True)}
    required |= {(6, True, 9, True, False, False), (6, True, 1, False, True, False)}
    checks = {
        "required_cases": required <= roles,
        "verdicts_statuses_and_timers": all(row["matches"] for row in cases),
        "lean_phase_observations": {row.get("pods") for row in cases if "lean_phases" in row}
                                  == {6, 12, 16},
        "large_gap_independently_measured": any(row.get("pods") == 16 and not row["traced"]
            and row["expected_count"] == 9 and row["reference"]["wall_seconds"] > 300
            and row["lean"]["wall_seconds"] < 3 for row in cases),
    }
    return {"gate": "PASS" if all(checks.values()) else "FAIL", "checks": checks, "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("pods", type=int, choices=(6, 12, 16))
    parser.add_argument("--group", default="all_properties", choices=GROUPS)
    parser.add_argument("--check-malformed", action="store_true")
    parser.add_argument("--lean-phases", type=Path, help="native isolated phase-instrumented Lean executable")
    parser.add_argument("--perturb", action="store_true", help="substitute the published blocked SSH ingress for the first query")
    parser.add_argument("--prepared", type=Path, help="artifact produced by the corresponding forensic fresh case")
    parser.add_argument("--traced", action="store_true")
    parser.add_argument("--lean-fresh", action="store_true")
    args = parser.parse_args()
    evidence = json.loads(EVIDENCE.read_text())
    provenance = evidence["provenance"]
    for name, fingerprint in provenance["binary_sha256"].items():
        if digest(Path(name)) != fingerprint:
            raise ValueError(f"historical binary changed: {name}")
    source = Path(provenance["paths"]["reference"])
    if ROOT == args.directory.resolve() or ROOT in args.directory.resolve().parents:
        parser.error("run directories must be outside the checkout")
    for candidate in (Path.home() / "Downloads/dynetikat-v11/DyNetiKAT-1c6bd42.tar.gz",
                      Path("/home/ali/Downloads/dynetikat-v11/DyNetiKAT-1c6bd42.tar.gz")):
        if candidate.is_file():
            verify_reference_source(source, candidate, provenance)
            break
    else:
        parser.error("pinned source archive required to authenticate the reference copy")
    path = source.parent / "corpus" / f"fattree_{args.pods}_pods_{args.group}.json"
    rows = [item for item in evidence["queries"] if item["input"] == path.name]
    if not rows or any(item["input_sha256"] != digest(path) for item in rows):
        raise ValueError(f"unexpected input: {path}")
    if args.group == "all_properties" and len(rows) != 9:
        raise ValueError("all-properties must contain nine distinct queries")
    folder = args.directory.resolve()
    baseline = [item["reference_verdict"] for item in rows]
    source_hash = digest(path)
    if args.perturb:
        if args.prepared or args.pods != 6 or args.group != "reachability_1" or not baseline[0]:
            parser.error("perturbation requires unprepared 6-pod reachability_1")
        original = json.loads(path.read_text())
        packet = rows[0]["packet"]
        original["properties"] = {packet: [original["properties"][packet][0]]}
        all_properties = json.loads(path.with_name("fattree_6_pods_all_properties.json").read_text())
        blocked = all_properties["properties"]["1"][0]
        first = original["properties"][packet][0]
        if (blocked[:2] != first[:2] or blocked[3] != first[3] or blocked[2] != "=0"
                or all_properties["out_packets"]["1"] != original["out_packets"][packet]):
            raise ValueError("published blocked query no longer matches the control query")
        original["in_packets"][packet] = all_properties["in_packets"]["1"]
        staged = folder.with_name(folder.name + "-input")
        staged.mkdir()
        path = staged / path.name
        write(path, original)
        baseline = [False]
    prepared = args.prepared.resolve() if args.prepared else None
    if prepared:
        original_properties = json.loads(path.read_text())["properties"]
        if json.loads(prepared.read_text())["properties"] != original_properties:
            raise ValueError("prepared artifact changes the property map")
        if prepared.parent.parent.parent.joinpath("result.json").exists():
            producer = json.loads(prepared.parent.parent.parent.joinpath("result.json").read_text())
            if (producer["sha256"] != source_hash or not producer["matches"]
                    or producer["prepared_output"] != {"path": str(prepared), "sha256": digest(prepared)}):
                raise ValueError("prepared artifact producer did not validate this input")
        else:
            raise ValueError("missing forensic producer evidence")
    audit_case(folder, path, provenance, baseline, args.traced, prepared=prepared,
               lean_fresh=args.lean_fresh, lean_exit=1 if args.perturb else 0,
               lean_phases=args.lean_phases, check_malformed=args.check_malformed,
               metadata=dict(pods=args.pods, group=args.group,
                   switches=network_size(json.loads(path.read_text()), args.pods),
                   original_sha256=source_hash, perturbation=args.perturb,
                   lean_mode="prepare_per_query" if args.lean_fresh else "prepare_once",
                   reference_mode="serialized_preprocessed" if prepared else "preprocess_once"))


if __name__ == "__main__":
    main()
