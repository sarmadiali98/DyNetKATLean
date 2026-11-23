"""Audit the local public closure and its dependency direction."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
LAYERS = {"KATLean": ROOT.parent / "KATLean",
          "NetKATLean": ROOT.parent / "NetKATLean", "DyNetKATLean": ROOT}
ORDER = tuple(LAYERS)
EXTERNAL = {"Mathlib", "Lean", "Std", "Init"}
visited = set()


def visit(module, ceiling):
    family = module.split(".")[0]
    if family in EXTERNAL:
        return
    if family not in LAYERS or ORDER.index(family) > ceiling:
        raise ValueError(f"Forbidden import: {module} (from {ORDER[ceiling]})")
    if module in visited:
        return
    path = LAYERS[family] / Path(*module.split(".")).with_suffix(".lean")
    visited.add(module)
    for imported in re.findall(r"^\s*import\s+(\S+)", path.read_text(), re.M):
        visit(imported, ORDER.index(family))


visit("DyNetKATLean", 2)
expected = {"DyNetKATLean", *("DyNetKATLean.Core." + p.stem
                             for p in (ROOT / "DyNetKATLean/Core").glob("*.lean"))}
if {module for module in visited if module.split(".")[0] == "DyNetKATLean"} != expected:
    raise ValueError("Public closure differs from the owned mathematical source tree")
if not {"NetKATLean", "KATLean"} <= visited:
    raise ValueError("Public closure is missing a lower package")
print(f"Audited {len(expected)} owned modules and {len(visited)} local modules transitively")
