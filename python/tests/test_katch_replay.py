"""Exercise the adapter protocol with a subprocess double, independently of KATch."""
import importlib.util
from pathlib import Path
import sys

import pytest

SCRIPT = Path(__file__).resolve().parents[2] / "scripts" / "katch_replay.py"
SPEC = importlib.util.spec_from_file_location("katch_replay", SCRIPT)
adapter = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(adapter)

FAKE = """
import os, pathlib, signal, sys, time
mode, invocation, filename = sys.argv[1:]
assert invocation == 'run'
assert pathlib.Path.cwd() == pathlib.Path(filename).parent
assert pathlib.Path('results').is_dir()
lines = pathlib.Path(filename).read_text().splitlines()
statement = lines[-1]
location = f"{filename}:{len(lines)}"
def respond(passed, masked=False):
    if mode in ('jvm-warning', 'jvm-warning-with-error'):
        print("WARNING: A terminally deprecated method in sun.misc.Unsafe has been called",
              "WARNING: sun.misc.Unsafe::objectFieldOffset has been called by scala.runtime.LazyVals$ (file:/example.jar)",
              "WARNING: Please consider reporting this to the maintainers of class scala.runtime.LazyVals$",
              "WARNING: sun.misc.Unsafe::objectFieldOffset will be removed in a future release",
              sep='\\n', file=sys.stderr)
        if mode == 'jvm-warning-with-error':
            print("unexpected error", file=sys.stderr)
    if passed:
        print(f"\\x1b[32mCheck passed in {location}\\x1b[0m")
        sys.exit(0)
    print('Exception in thread "main" java.lang.Throwable: '
          f'\\x1b[31m!!! Check failed in {location} !!!\\x1b[0m', file=sys.stderr)
    sys.exit(0 if masked else 1)
if mode == 'timeout':
    time.sleep(10)
with open("probes.log", "a", encoding="utf-8") as log:
    print(statement, file=log)
if statement == 'check ⊤ ≡ ⊤': respond(True)
if statement == 'check ⊤ ≢ ⊤': respond(False, mode == 'masked')
if mode == 'crash': sys.exit(17)
if mode == 'signal': os.kill(os.getpid(), signal.SIGTERM)
if mode == 'parse':
    print(f"Could not parse {location}", file=sys.stderr)
    sys.exit(1)
if mode == 'missing-file':
    print(f"File {filename} not found", file=sys.stderr)
    sys.exit(1)
if mode == 'malformed':
    sys.stdout.buffer.write(b'\\xff')
    sys.exit(0)
if mode == 'ambiguous': respond(True)
if mode == 'wrong-line':
    location = f"{filename}:999"
    respond(True)
if mode == 'wrong-path':
    location = f"other.nkpl:{len(lines)}"
    respond(True)
# Nominate the first packet (all zero), or an equivalent pair.
respond((' ≢ ' in statement) == (mode == 'negative'), mode == 'masked')
"""


def command(tmp_path, mode):
    path = tmp_path / "fake_katch.py"
    path.write_text(FAKE, encoding="utf-8")
    return [sys.executable, str(path), mode]


@pytest.mark.parametrize("case, expected", [
    ("positive", "equational"),
    ("negative", {"kind": "counterexample", "input": [0, 0, 0, 0]}),
])
def test_probe_candidate(tmp_path, case, expected):
    assert adapter.backend_candidate(command(tmp_path, case), "left = ⊤\nright = ⊥",
                                     case, tmp_path, 5) == expected


@pytest.mark.parametrize("mode", ["masked", "jvm-warning"])
def test_known_launcher_diagnostics(tmp_path, mode):
    assert adapter.backend_candidate(command(tmp_path, mode), "", "positive",
                                     tmp_path, 5) == "equational"


def test_preflight_emits_distinct_complementary_programs(tmp_path):
    adapter.backend_candidate(command(tmp_path, "positive"), "left = ⊤\nright = ⊤",
                              "positive", tmp_path, 5)
    probes = (tmp_path / "probes.log").read_text(encoding="utf-8").splitlines()
    assert probes[:2] == ["check ⊤ ≡ ⊤", "check ⊤ ≢ ⊤"]


@pytest.mark.parametrize("mode, reason", [
    ("crash", "unexpected"),
    ("signal", "unexpected"),
    ("parse", "unexpected"),
    ("missing-file", "unexpected"),
    ("wrong-line", "unexpected"),
    ("wrong-path", "unexpected"),
    ("jvm-warning-with-error", "unexpected"),
    ("malformed", "unreadable"),
    ("ambiguous", "inconsistent"),
    ("timeout", "timeout"),
])
def test_operational_failure(tmp_path, mode, reason):
    with pytest.raises(adapter.BackendFailure, match=reason):
        adapter.backend_candidate(command(tmp_path, mode), "left = ⊤\nright = ⊥", "positive", tmp_path,
                                  0.2 if mode == "timeout" else 5)


def test_missing_backend(tmp_path):
    with pytest.raises(adapter.BackendFailure, match="unavailable"):
        adapter.backend_candidate([str(tmp_path / "missing")], "", "negative", tmp_path, 5)


@pytest.mark.parametrize("mode, case, method, equivalent", [
    ("positive", "positive", "checkedEquational", True),
    ("negative", "negative", "checkedCounterexample", False),
    ("malformed", "negative", "exactFallback", False),
])
def test_lean_round_trip(tmp_path, mode, case, method, equivalent):
    if not (adapter.ROOT / "lean/.lake/build/lib/lean/DyNetKAT/Experimental.olean").exists():
        pytest.skip("build DyNetKAT.Experimental to exercise optional Lean replay")
    result = adapter.replay(case, command(tmp_path, mode), timeout=None, lean_timeout=None)
    assert result["method"] == method
    assert result["equivalent"] is equivalent
