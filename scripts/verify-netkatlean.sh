#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../lean"
lake build NetKATLean
lake env python3 - <<'PY'
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

root = Path.cwd()
kat = root.parent / "packages/KATLean"

def module_root(name):
    return kat if name.split(".")[0] == "KATLean" else root

optional = {"BackendCertificate", "EquationalCertificate", "KATch", "Legacy"}
tests = ["test_netkatlean_import.lean", "test_netkat_axioms.lean",
         "test_decision.lean", "test_symbolic_netkat.lean"]
modules = set()

def visit(source):
    for line in source.read_text().splitlines():
        match = re.match(r"^\s*import\s+([^\s]+)", line)
        if not match:
            continue
        name = match[1]
        family, _, tail = name.partition(".")
        if family in {"Mathlib", "Lean", "Std", "Init"}:
            continue
        if not (name == "NetKATLean" or family == "KATLean" or name.startswith("NetKATLean.PacketAdapter.") or
                (name.startswith("DyNetKAT.NetKAT.") and tail.split(".")[1] not in optional)):
            raise SystemExit(f"{source.relative_to(root.parent)} imports forbidden module {name}")
        if source.is_relative_to(kat):
            if family != "KATLean" or tail.split(".")[0] == "NetKAT":
                raise SystemExit(f"Generic KATLean imports a higher layer: {name}")
        if name not in modules:
            modules.add(name)
            visit(module_root(name) / (name.replace(".", "/") + ".lean"))

visit(root / "NetKATLean.lean")
for test in tests:
    visit(root / test)

prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
deps = [str(Path(p).resolve()) for p in os.environ.get("LEAN_PATH", "").split(os.pathsep)
        if p and Path(p).resolve().is_relative_to(root / ".lake/packages")]
with tempfile.TemporaryDirectory(prefix="netkatlean-consumer-") as scratch:
    isolated = Path(scratch)
    for name in sorted(modules):
        path = Path(name.replace(".", "/") + ".olean")
        destination = isolated / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(module_root(name) / ".lake/build/lib/lean" / path, destination)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([scratch, *deps]))
    print(f"Checking {len(modules)} local modules in the isolated import closure", flush=True)
    for test in tests:
        shutil.copyfile(root / test, isolated / test)
        subprocess.run([str(Path(prefix) / "bin/lean"), test], cwd=isolated, env=env, check=True)
PY
