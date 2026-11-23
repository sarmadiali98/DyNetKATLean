"""Reuse only the image's own Git checkouts, and only for identical pins."""
import json
from pathlib import Path
import subprocess
import sys


def load_lock(package):
    lock = json.loads((package / "lake-manifest.json").read_text())
    pins = {dep["name"]: (dep["url"], dep["rev"])
            for dep in lock["packages"] if dep["type"] == "git"}
    return package / lock["packagesDir"], pins


def main():
    seed = Path(__file__).resolve().parents[1] / "packages/KATLean"
    target = Path(sys.argv[1]).resolve()
    cache, pins = load_lock(seed)
    destination, required = load_lock(target)
    if required != pins:
        raise SystemExit(f"Git dependency pins differ: {target}")
    for name, (_, revision) in pins.items():
        actual = subprocess.check_output(
            ["git", "-C", cache / name, "rev-parse", "HEAD"], text=True
        ).strip()
        if actual != revision:
            raise SystemExit(f"Git checkout mismatch for {name}: {actual} != {revision}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.symlink_to(cache, target_is_directory=True)


if __name__ == "__main__":
    main()
