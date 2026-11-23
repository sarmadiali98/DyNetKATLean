"""Verify a Lake path consumer with NetKATLean and its locked dependencies."""
import json
import os
from pathlib import Path
import subprocess
import tempfile


def verify_consumer():
    package = Path(__file__).resolve().parent
    lock = json.loads((package / "lake-manifest.json").read_text())
    kat = (package / "../KATLean").resolve()
    paths = [dep for dep in lock["packages"] if dep["type"] == "path"]
    if len(paths) != 1 or paths[0]["name"] != "KATLean" or (package / paths[0]["dir"]).resolve() != kat:
        raise ValueError("Expected KATLean as the only local dependency")
    cache = (package / lock["packagesDir"]).resolve()
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)
    with tempfile.TemporaryDirectory(prefix="netkatlean-consumer-") as scratch:
        root = Path(scratch)
        (root / "lean-toolchain").write_bytes((package / "lean-toolchain").read_bytes())
        (root / "lakefile.toml").write_text(
            'name = "Consumer"\ndefaultTargets = ["Consumer"]\n'
            f'[[require]]\nname = "NetKATLean"\npath = {json.dumps(str(package))}\n'
            '[[lean_lib]]\nname = "Consumer"\n'
        )
        lock.update(name="Consumer", packages=[
            dict(type="path", name="NetKATLean", scope="", dir=str(package),
                 manifestFile="lake-manifest.json", inherited=False, configFile="lakefile.toml"),
            dict(paths[0], inherited=True, dir=str(kat)),
            *(dict(dep, inherited=True) for dep in lock["packages"] if dep["type"] == "git"),
        ])
        (root / "lake-manifest.json").write_text(json.dumps(lock))
        (root / ".lake").mkdir()
        (root / lock["packagesDir"]).symlink_to(cache, target_is_directory=True)
        (root / "Consumer.lean").write_bytes((package / "test_netkatlean_import.lean").read_bytes())

        def lake(*args):
            return subprocess.check_output(["lake", *args], cwd=root, env=env, text=True).strip()

        prefix = Path(lake("env", "lean", "--print-prefix")).resolve()
        for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
            for component in filter(None, lake("env", "printenv", key).split(os.pathsep)):
                resolved = (root / component).resolve()
                if not any(resolved.is_relative_to(base) for base in (root, package, kat, cache, prefix)):
                    raise ValueError(f"Unexpected {key} entry: {resolved}")
        subprocess.run(["lake", "build"], cwd=root, env=env, check=True)


if __name__ == "__main__":
    verify_consumer()
