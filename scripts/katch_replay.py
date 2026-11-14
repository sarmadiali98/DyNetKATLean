#!/usr/bin/env python3
"""Optional KATch assertion probes followed by Lean replay of the original pair."""

import argparse
import json
import math
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ["lake", "env", "lean", "--run", "test_backend_certificate.lean"]
FIELDS = ("src", "dst", "sw", "port")
VALUES = (0, 1, 8, 9)
DOMAIN = " ⋅ ".join("(" + " ∪ ".join(f"@{f}={v}" for v in VALUES) + ")" for f in FIELDS)
REPLAY = re.compile(r"DyNetKAT\.NetKAT\.BackendMethod\."
                    r"(checkedCounterexample|checkedEquational|exactFallback): "
                    r"equivalent = (true|false)")


class BackendFailure(Exception):
    pass


def run(command, deadline, cwd=None):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise BackendFailure("timeout")
    try:
        result = subprocess.run(command, cwd=cwd, capture_output=True,
                                timeout=remaining)
        return result.returncode, result.stdout.decode("utf-8")
    except FileNotFoundError as exc:
        raise BackendFailure("unavailable") from exc
    except subprocess.TimeoutExpired as exc:
        raise BackendFailure("timeout") from exc
    except (OSError, UnicodeError) as exc:
        raise BackendFailure("unreadable process output") from exc


def query(guard, operator):
    return f"check (({guard}) ⋅ left) {operator} (({guard}) ⋅ right)"


def packet_guard(packet):
    return " ⋅ ".join(f"@{field}={value}" for field, value in zip(FIELDS, packet))


def propose(assertion, case):
    """Only the affirmative probe outcome nominates a candidate."""
    if case == "positive":
        return "equational" if assertion(query(DOMAIN, "≡")) else None

    if not assertion(query(DOMAIN, "≢")):
        return None
    # Narrow one field at a time, retaining the full domain guard.
    packet = []
    for field in FIELDS:
        values = VALUES
        while len(values) > 1:
            middle = len(values) // 2
            subset = " ∪ ".join(f"@{field}={value}" for value in values[:middle])
            guard = " ⋅ ".join(filter(None, (DOMAIN, packet_guard(packet), f"({subset})")))
            values = values[:middle] if assertion(query(guard, "≢")) else values[middle:]
        packet.append(values[0])
    if not assertion(query(packet_guard(packet), "≢")):
        return None
    return {"kind": "counterexample", "input": packet}


def backend_candidate(command, policy, case, directory, timeout):
    deadline = time.monotonic() + timeout
    path = directory / "probe.nkpl"

    def invoke(text):
        path.write_text(text + "\n", encoding="utf-8")
        return run([*command, "run", str(path)], deadline)

    # Check the launcher protocol against both a passing and a failing
    # assertion before interpreting any exit codes. Do not assume a stable
    # textual format or interpret an error as a policy verdict.
    good, _ = invoke("check ⊤ ≡ ⊤")
    bad, _ = invoke("check ⊤ ≡ ⊥")
    if good != 0 or bad <= 0:
        raise BackendFailure("unsupported assertion exit protocol")

    def assertion(statement):
        # Require complementary results, so two process failures cannot
        # masquerade as a successful branch of the search.
        if " ≢ " in statement:
            opposite = statement.replace(" ≢ ", " ≡ ", 1)
        else:
            opposite = statement.replace(" ≡ ", " ≢ ", 1)
        code, _ = invoke(policy + "\n" + statement)
        inverse, _ = invoke(policy + "\n" + opposite)
        if (code, inverse) == (good, bad):
            return True
        if (code, inverse) == (bad, good):
            return False
        raise BackendFailure("inconsistent KATch assertion results")

    return propose(assertion, case)


def replay(case, command, timeout, lean_timeout):
    code, policy = run([*LEAN, "emit-live", case], time.monotonic() + lean_timeout,
                       ROOT / "lean")
    if code != 0:
        raise BackendFailure("Lean policy export failed")
    with tempfile.TemporaryDirectory(prefix="katch-replay-") as tmp:
        directory = Path(tmp)
        started = time.monotonic()
        try:
            candidate = backend_candidate(command, policy, case, directory, timeout)
            reason = "candidate" if candidate is not None else "no candidate"
        except BackendFailure as exc:
            candidate, reason = None, str(exc)
        candidate_ms = (time.monotonic() - started) * 1000
        if isinstance(candidate, dict):
            path = directory / "candidate.json"
            path.write_text(json.dumps(candidate), encoding="utf-8")
            argument = str(path)
        else:
            argument = candidate or "-"

        started = time.monotonic()
        code, output = run([*LEAN, "replay-live", case, argument],
                           started + lean_timeout, ROOT / "lean")
        verdict = REPLAY.fullmatch(output.strip())
        if code != 0 or verdict is None:
            raise BackendFailure("invalid Lean replay response")
        method, equivalence = verdict.groups()
        if method == "exactFallback" and candidate is not None:
            reason = "certificate rejected"
        return {
            "case": case,
            "method": method,
            "equivalent": equivalence == "true",
            "backend": reason,
            "candidate_ms": round(candidate_ms, 3),
            "lean_replay_ms": round((time.monotonic() - started) * 1000, 3),
        }


def positive_timeout(text):
    value = float(text)
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError("timeout must be finite and positive")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", choices=("positive", "negative", "both"))
    parser.add_argument("--timeout", type=positive_timeout, default=60)
    parser.add_argument("--lean-timeout", type=positive_timeout, default=60)
    parser.add_argument("--require-backend", action="store_true",
                        help="fail if the checked candidate path was not exercised")
    parser.add_argument("--katch", default="katch",
                        help="KATch launcher, accepting 'run FILE'")
    args = parser.parse_args()
    cases = ("positive", "negative") if args.case == "both" else (args.case,)
    status = 0
    for case in cases:
        try:
            result = replay(case, [args.katch], args.timeout, args.lean_timeout)
        except BackendFailure as exc:
            result = {"case": case, "method": "unknown", "reason": str(exc)}
            status = 1
        print(json.dumps(result))
        expected = "checkedEquational" if case == "positive" else "checkedCounterexample"
        if args.require_backend and result["method"] != expected:
            status = 1
    return status


if __name__ == "__main__":
    raise SystemExit(main())
