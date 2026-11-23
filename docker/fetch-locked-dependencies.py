"""Fetch the immutable Git revisions needed by the clean Docker build."""
import json
from pathlib import Path
import subprocess
import sys
import time


def git(directory, *args):
    return subprocess.check_output(["git", "-C", str(directory), *args], text=True).strip()


def main():
    package = Path(sys.argv[1])
    lock = json.loads((package / "lake-manifest.json").read_text())
    for dep in lock["packages"]:
        if dep["type"] != "git":
            continue
        revision = dep["rev"]
        checkout = package / lock["packagesDir"] / dep["name"]
        checkout.mkdir(parents=True)
        git(checkout, "init", "--quiet")
        git(checkout, "remote", "add", "origin", dep["url"])
        for delay in (2, 5, None):
            try:
                git(checkout, "-c", "http.version=HTTP/1.1",
                    "fetch", "--no-tags", "--depth=1", "origin", revision)
                break
            except subprocess.CalledProcessError:
                if delay is None:
                    raise
                print(f"Retrying {dep['name']} in {delay}s", flush=True)
                time.sleep(delay)
        git(checkout, "checkout", "--quiet", "--detach", revision)
        if git(checkout, "rev-parse", "HEAD") != revision:
            raise SystemExit(f"Git checkout mismatch: {dep['name']}")
        # Lake's cloud-release resolver uses a tag pointing to the checked-out
        # revision. ProofWidgets has an explicit release tag in Mathlib's lock.
        if dep["name"] == "proofwidgets":
            tag = dep["inputRev"]
            git(checkout, "fetch", "--depth=1", "origin", f"refs/tags/{tag}:refs/tags/{tag}")
            if git(checkout, "rev-parse", f"{tag}^{{commit}}") != revision:
                raise SystemExit("ProofWidgets release tag differs from the lock")


if __name__ == "__main__":
    main()
