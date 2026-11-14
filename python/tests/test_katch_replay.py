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
import pathlib, sys, time
mode, invocation, filename = sys.argv[1:]
assert invocation == 'run'
statement = pathlib.Path(filename).read_text().splitlines()[-1]
if mode == 'timeout':
    time.sleep(10)
if statement == 'check ⊤ ≡ ⊤': sys.exit(0)
if statement == 'check ⊤ ≡ ⊥': sys.exit(1)
if mode == 'crash': sys.exit(17)
if mode == 'malformed':
    sys.stdout.buffer.write(b'\\xff')
    sys.exit(0)
if mode == 'ambiguous': sys.exit(0)
# Nominate the first packet (all zero), or an equivalent pair.
sys.exit(int((' ≢ ' in statement) != (mode == 'negative')))
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


@pytest.mark.parametrize("mode, reason", [
    ("crash", "inconsistent"),
    ("malformed", "unreadable"),
    ("ambiguous", "inconsistent"),
    ("timeout", "timeout"),
])
def test_operational_failure(tmp_path, mode, reason):
    with pytest.raises(adapter.BackendFailure, match=reason):
        adapter.backend_candidate(command(tmp_path, mode), "", "positive", tmp_path,
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
    if not (adapter.ROOT / "lean/.lake/build/lib/lean/DyNetKAT.olean").exists():
        pytest.skip("build DyNetKAT to exercise Lean replay")
    result = adapter.replay(case, command(tmp_path, mode), 10, 30)
    assert result["method"] == method
    assert result["equivalent"] is equivalent
