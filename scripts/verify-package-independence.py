#!/usr/bin/env python3
"""Build standalone packages and three Lake consumers in a fresh external tree."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


REPO = Path(__file__).resolve().parents[1]
SOURCE = REPO / "lean"
LAYERS = ("KATLean", "NetKATLean", "DyNetKATLean")
EXTERNAL = {"Lean", "Init", "Std", "Mathlib"}


def source_manifest():
    """Use the public closures and the previously audited generic KAT target."""
    entries = {}

    def visit(module, owner):
        if module.partition(".")[0] in EXTERNAL or module in entries:
            return
        if owner == "KATLean":
            allowed = module in {"KATLean", "KATLean.KAT", "KATLean.Kleene", "KATLean.Relation",
                                 "KATLean.Native"} or module.startswith("KATLean.Native.")
        elif owner == "NetKATLean":
            allowed = (module == owner or module in {
                "KATLean.NetKAT." + name for name in ("Packet", "Guard", "Symbolic", "Closure")
            } or (module.startswith("DyNetKAT.NetKAT.") and module.split(".")[2] not in
                  {"Legacy", "KATch", "BackendCertificate", "EquationalCertificate"}))
        else:
            allowed = module == owner or module.startswith("DyNetKAT.DyNetKAT.")
        if not allowed:
            raise ValueError(f"{owner} has an unaudited or upward import: {module}")
        path = Path(*module.split(".")).with_suffix(".lean")
        content = (SOURCE / path).read_bytes()
        imports = re.findall(r"^\s*import\s+(\S+)", content.decode(), re.M)
        local = [name for name in imports if name.partition(".")[0] not in EXTERNAL]
        entries[module] = dict(module=module, source=str(Path("lean") / path),
                               package_path=str(path), owner=owner, local_imports=local,
                               external_imports=[name for name in imports if name not in local],
                               compatibility_path=not (module == owner or module.startswith(owner + ".")),
                               sha256=hashlib.sha256(content).hexdigest())
        for name in local:
            visit(name, owner)

    visit("KATLean", "KATLean")
    visit("KATLean.Native", "KATLean")
    for path in sorted((SOURCE / "KATLean/Native").glob("*.lean")):
        visit("KATLean.Native." + path.stem, "KATLean")
    for owner in LAYERS[1:]:
        visit(owner, owner)
    return entries


def prototype_module(name):
    # Lean 4.19 searches by the first component before checking the full path.
    if name.startswith("KATLean.NetKAT."):
        return "NetKATLean.PacketAdapter." + name.removeprefix("KATLean.NetKAT.")
    if name.startswith("DyNetKAT.NetKAT."):
        return "NetKATLean.Core." + name.removeprefix("DyNetKAT.NetKAT.")
    return name


def run(cwd, args, env, label):
    with (cwd / f"{label}.log").open("w") as log:
        result = subprocess.run(args, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{args} failed in {cwd}; see {log.name}")
    print(f"{cwd.name}: {label} passed", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache", type=Path, default=SOURCE / ".lake/packages",
                        help="directory containing the pinned external Lake dependency checkouts")
    args = parser.parse_args()
    root = Path(tempfile.mkdtemp(prefix="dynetkat-package-prototypes-", dir="/tmp")).resolve()
    if root.is_relative_to(REPO):
        raise ValueError("prototype root must be outside the checkout")
    print(f"Prototype workspace: {root}", flush=True)
    entries = source_manifest()
    for entry in entries.values():
        module = prototype_module(entry["module"])
        entry["prototype_module"] = module
        entry["prototype_imports"] = [prototype_module(name) for name in entry["local_imports"]]
        entry["package_path"] = str(Path(*module.split(".")).with_suffix(".lean"))
    pinned = json.loads((SOURCE / "lake-manifest.json").read_text())
    external = {item["name"]: item for item in pinned["packages"]}
    mathlib = external["mathlib"]
    env = {key: value for key, value in os.environ.items()
           if key not in {"LEAN_PATH", "LEAN_SRC_PATH", "LAKE_PACKAGES_DIR", "LEAN_SYSROOT"}}
    cache = root / "external"
    cache.mkdir()
    for name, entry in external.items():
        if entry["type"] != "git":
            raise ValueError(f"expected a pinned Git dependency: {name}")
        src = args.cache / name
        revision = subprocess.check_output(["git", "-C", src, "rev-parse", "HEAD"], text=True).strip()
        if revision != entry["rev"]:
            raise ValueError(f"incorrect cached revision for {name}: {revision}")
        shutil.copytree(src, cache / name, symlinks=True)
    for link in cache.rglob("*"):
        if link.is_symlink() and not link.resolve().is_relative_to(cache):
            raise ValueError(f"external cache symlink escapes the prototype: {link}")

    def require(name, **settings):
        return "[[require]]\n" + f'name = "{name}"\n' + "".join(
            f"{key} = {json.dumps(value)}\n" for key, value in settings.items())

    def prepare(name, config):
        package = root / name
        package.mkdir()
        shutil.copyfile(SOURCE / "lean-toolchain", package / "lean-toolchain")
        (package / "lakefile.toml").write_text(f'name = "{name}"\ndefaultTargets = ["{config[0]}"]\n\n'
                                             + config[1])
        git_deps = package / ".lake/packages"
        git_deps.mkdir(parents=True)
        for dep in external:
            (git_deps / dep).symlink_to(cache / dep, target_is_directory=True)
        return package

    def lock(package, expected_local, consumer=False):
        # Preserve the audited Git pins and resolve only the new local path dependencies.
        git_entries = [dict(item, inherited=item["inherited"] or consumer)
                       for item in external.values()]
        next(item for item in git_entries if item["name"] == "mathlib")["inputRev"] = mathlib["rev"]
        path_entries = [
            dict(type="path", scope="", name=name, manifestFile="lake-manifest.json",
                 inherited=name != expected_local[-1], dir=f"../{name}", configFile="lakefile.toml")
            for name in expected_local
        ]
        manifest = dict(version=pinned["version"], packagesDir=".lake/packages",
                        lakeDir=".lake", name=package.name, packages=path_entries + git_entries)
        (package / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    def check_resolution(package, expected_local):
        manifest = json.loads((package / "lake-manifest.json").read_text())
        local = set()
        git_names = set()
        for dep in manifest["packages"]:
            if dep["type"] == "path":
                local.add(dep["name"])
                if (package / dep["dir"]).resolve() != root / dep["name"]:
                    raise ValueError(f"unexpected package location: {dep}")
            elif dep["type"] == "git":
                git_names.add(dep["name"])
                expected = external[dep["name"]]
                if dep["rev"] != expected["rev"] or dep["url"] != expected["url"]:
                    raise ValueError(f"dependency pin changed: {dep}")
                if (package / manifest["packagesDir"] / dep["name"]).resolve() != cache / dep["name"]:
                    raise ValueError(f"unexpected Git dependency location: {dep}")
            else:
                raise ValueError(f"unexpected package type: {dep}")
        if local != set(expected_local) or git_names != set(external):
            raise ValueError(f"unexpected dependency sets for {package.name}: {local}, {git_names}")
        paths = json.loads(subprocess.check_output(
            ["lake", "env", "python3", "-c",
             "import json, os; print(json.dumps({k: os.getenv(k, '') for k in ('LEAN_PATH', 'LEAN_SRC_PATH')}))"],
            cwd=package, env=env, text=True))
        prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                              cwd=package, env=env, text=True).strip()).resolve()
        allowed = [prefix, package, *(root / name for name in expected_local), *[cache / name for name in external]]
        for value in paths.values():
            for component in filter(None, value.split(os.pathsep)):
                resolved = (package / component).resolve()
                if resolved.is_relative_to(REPO) or not any(resolved.is_relative_to(base) for base in allowed):
                    raise ValueError(f"unexpected Lake search path: {resolved}")
        (package / "resolved-paths.json").write_text(json.dumps(paths, indent=2) + "\n")

    for index, name in enumerate(LAYERS):
        owned = sorted((entry for entry in entries.values() if entry["owner"] == name),
                       key=lambda entry: entry["module"])
        globs = json.dumps([entry["prototype_module"] for entry in owned])
        lower = require(LAYERS[index - 1], path=f"../{LAYERS[index - 1]}") if index else ""
        package = prepare(name, (name, lower + require("mathlib", git=mathlib["url"], rev=mathlib["rev"])
                                 + f'\n[[lean_lib]]\nname = "{name}"\nglobs = {globs}\n'))
        for entry in owned:
            destination = package / entry["package_path"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            source = (REPO / entry["source"]).read_text()
            transformed = re.sub(r"^(\s*import\s+)(\S+)",
                                 lambda m: m[1] + prototype_module(m[2]), source, flags=re.M)
            destination.write_text(transformed)
            entry["prototype_sha256"] = hashlib.sha256(destination.read_bytes()).hexdigest()
        (package / "source-manifest.json").write_text(json.dumps(owned, indent=2) + "\n")
        lock(package, LAYERS[:index])
        check_resolution(package, LAYERS[:index])
        run(package, ["lake", "build"], env, "build")

        consumer = prepare(name + "Consumer", ("Consumer", require(name, path=f"../{name}")
                                                + '\n[[lean_lib]]\nname = "Consumer"\n'))
        test = SOURCE / f"test_{name.lower()}_import.lean"
        source = test.read_text()
        if name == "KATLean":
            source += "\n#guard KATLean.Native.decideEquiv (T := Fin 1) (A := Fin 1) (.plus .one .one) .one\n"
        (consumer / "Consumer.lean").write_text(source)
        lock(consumer, LAYERS[:index + 1], consumer=True)
        check_resolution(consumer, LAYERS[:index + 1])
        run(consumer, ["lake", "build"], env, "build")


if __name__ == "__main__":
    main()
