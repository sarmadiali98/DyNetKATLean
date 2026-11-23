#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../lean"

lake env python3 - <<'PY'
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

root = Path.cwd()
build = root / ".lake/build/lib/lean"
umbrella = "DyNetKATLean"
case_study = "DyNetKAT.Examples.DistributedControllers"
optional = {"BackendCertificate", "EquationalCertificate", "KATch", "Legacy"}

def layer(name):
    if name.partition(".")[0] in {"Mathlib", "Lean", "Std", "Init"}:
        return 0
    if name.startswith("KATLean.NetKAT."):
        return 2
    if name == "KATLean" or name.startswith("KATLean."):
        return 1
    if name == "NetKATLean" or (name.startswith("DyNetKAT.NetKAT.")
                                and name.split(".")[2] not in optional):
        return 2
    if name == umbrella or name.startswith("DyNetKAT.DyNetKAT."):
        return 3
    if name == case_study:
        return 4
    raise SystemExit(f"Forbidden import: {name}")

def module_path(name, suffix):
    return Path(*name.split(".")).with_suffix(suffix)

def closure(entry):
    visited = set()

    def visit(name):
        if name in visited:
            return
        level = layer(name)
        if level == 0:
            return
        visited.add(name)
        for line in (root / module_path(name, ".lean")).read_text().splitlines():
            match = re.match(r"^\s*import\s+(\S+)", line)
            if match:
                dependency = match[1]
                if layer(dependency) > level:
                    raise SystemExit(f"Upward import: {name} -> {dependency}")
                visit(dependency)

    visit(entry)
    return visited

modules = closure(umbrella)
expected_core = {"DyNetKAT.DyNetKAT." + p.stem
                 for p in (root / "DyNetKAT/DyNetKAT").glob("*.lean")}
if not expected_core <= modules or "NetKATLean" not in modules:
    raise SystemExit("Public closure is missing dynamic core modules or NetKATLean")

case_modules = closure(case_study) - modules
subprocess.run(["lake", "build", umbrella], check=True)
prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
deps = [str(Path(p).resolve()) for p in os.environ.get("LEAN_PATH", "").split(os.pathsep)
        if p and Path(p).resolve().is_relative_to((root / ".lake/packages").resolve())]

tests = [
    "test_dynetkatlean_import.lean",
    "test_paper_domain.lean",
    "test_typed_guardedness.lean",
    "test_guarded_moves.lean",
    "test_finite_projection.lean",
    "test_equations.lean",
    "test_equations_aip.lean",
    "test_ground_completeness.lean",
    "test_finite_abstraction.lean",
    "test_trace_safety.lean",
]
with tempfile.TemporaryDirectory(prefix="dynetkatlean-consumer-") as scratch:
    isolated = Path(scratch)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([scratch, *deps]))

    def copy_modules(names):
        for name in sorted(names):
            path = module_path(name, ".olean")
            target = isolated / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(build / path, target)

    def check(name):
        print(f"Checking isolated {name}", flush=True)
        subprocess.run([str(Path(prefix) / "bin/lean"), name], cwd=isolated, env=env, check=True)

    copy_modules(modules)
    print(f"Checking {len(modules)} local modules in the public closure", flush=True)
    for name in tests:
        source = (root / name).read_text()
        if name != "test_dynetkatlean_import.lean":
            old_import = "import DyNetKAT\n"
            if not source.startswith(old_import):
                raise SystemExit(f"Unexpected first import in {name}")
            source = source.replace(old_import, "import DyNetKATLean\n", 1)
        (isolated / name).write_text(source)
        check(name)

    subprocess.run(["lake", "build", "+" + case_study], check=True)
    copy_modules(case_modules)
    (isolated / "CaseStudy.lean").write_text(
        f"import {case_study}\n"
        "#check DyNetKAT.DyNetKAT.DistributedControllers.independent_unsafe\n"
        "#check DyNetKAT.DyNetKAT.DistributedControllers.synchronized_eq28\n"
    )
    check("CaseStudy.lean")
PY
