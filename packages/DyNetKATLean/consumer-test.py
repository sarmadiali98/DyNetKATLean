"""Verify a Lake path consumer with DyNetKATLean and its locked dependencies."""
import json
import os
from pathlib import Path
import subprocess
import tempfile


def verify_consumer():
    package = Path(__file__).resolve().parent
    lock = json.loads((package / "lake-manifest.json").read_text())
    lower = {name: (package / ".." / name).resolve()
             for name in ("NetKATLean", "KATLean")}
    paths = [dep for dep in lock["packages"] if dep["type"] == "path"]
    resolved = {dep["name"]: (package / dep["dir"]).resolve() for dep in paths}
    if len(paths) != len(lower) or resolved != lower:
        raise ValueError("Expected only sibling NetKATLean and KATLean dependencies")
    cache = (package / lock["packagesDir"]).resolve()
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)
    with tempfile.TemporaryDirectory(prefix="dynetkatlean-consumer-") as scratch:
        root = Path(scratch)
        (root / "lean-toolchain").write_bytes((package / "lean-toolchain").read_bytes())
        (root / "lakefile.toml").write_text(
            'name = "Consumer"\ndefaultTargets = ["Consumer"]\n'
            f'[[require]]\nname = "DyNetKATLean"\npath = {json.dumps(str(package))}\n'
            '[[lean_lib]]\nname = "Consumer"\n'
        )
        lock.update(name="Consumer", packages=[
            dict(type="path", name="DyNetKATLean", scope="", dir=str(package),
                 manifestFile="lake-manifest.json", inherited=False, configFile="lakefile.toml"),
            *(dict(dep, inherited=True, dir=str(lower[dep["name"]])) for dep in paths),
            *(dict(dep, inherited=True) for dep in lock["packages"] if dep["type"] == "git"),
        ])
        (root / "lake-manifest.json").write_text(json.dumps(lock))
        (root / ".lake").mkdir()
        (root / lock["packagesDir"]).symlink_to(cache, target_is_directory=True)
        (root / "Consumer.lean").write_bytes((package / "test_dynetkatlean_import.lean").read_bytes())

        def lake(*args):
            return subprocess.check_output(["lake", *args], cwd=root, env=env, text=True).strip()

        prefix = Path(lake("env", "lean", "--print-prefix")).resolve()
        for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
            for component in filter(None, lake("env", "printenv", key).split(os.pathsep)):
                resolved = (root / component).resolve()
                if not any(resolved.is_relative_to(base) for base in (root, package, *lower.values(), cache, prefix)):
                    raise ValueError(f"Unexpected {key} entry: {resolved}")
        subprocess.run(["lake", "build"], cwd=root, env=env, check=True)


if __name__ == "__main__":
    verify_consumer()
