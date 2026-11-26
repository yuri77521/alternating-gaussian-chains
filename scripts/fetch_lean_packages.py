"""Prepare the pinned, public Lake checkouts after study/reproduce.py setup."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

STUDY = Path(__file__).resolve().parents[1] / "study"


def git(directory, *args):
    return subprocess.check_output(["git", "-C", str(directory), *args], text=True).strip()


def prepare(work):
    manifest = work / "lean/lake-manifest.json"
    pins = dict(line.split("  ", 1)[::-1] for line in
                (STUDY / "upstream-files.sha256").read_text("utf-8").splitlines())
    if hashlib.sha256(manifest.read_bytes()).hexdigest() != pins["lean/lake-manifest.json"]:
        raise ValueError("Run setup first and use its hash-verified Lake manifest")
    lock = json.loads(manifest.read_text("utf-8"))
    packages = manifest.parent / lock["packagesDir"]
    packages.mkdir(parents=True, exist_ok=True)
    for pkg in lock["packages"]:
        target = packages / pkg["name"]
        revision = pkg["rev"]
        tag = pkg["inputRev"]
        if not target.exists():
            with tempfile.TemporaryDirectory(dir=packages) as stage:
                repo = Path(stage) / "checkout"
                subprocess.run(["git", "init", "--quiet", str(repo)], check=True)
                git(repo, "remote", "add", "origin", pkg["url"])
                git(repo, "fetch", "--quiet", "--depth=1", "--no-tags", "origin", revision)
                git(repo, "-c", "core.autocrlf=false", "checkout", "--quiet", "--detach", revision)
                if re.fullmatch(r"v[0-9][\w.-]*", tag):
                    git(repo, "fetch", "--quiet", "--depth=1", "origin", f"refs/tags/{tag}:refs/tags/{tag}")
                    if git(repo, "rev-parse", tag + "^{commit}") != revision:
                        raise ValueError(f"Unexpected release tag for {pkg['name']}")
                repo.rename(target)
        if git(target, "rev-parse", "HEAD") != revision:
            raise ValueError(f"Existing checkout is at a different revision: {target}")
        if git(target, "remote", "get-url", "origin").rstrip("/").removesuffix(".git") != pkg["url"].rstrip("/").removesuffix(".git"):
            raise ValueError(f"Unexpected origin for {pkg['name']}")
        if pkg["name"] == "proofwidgets" and git(target, "rev-parse", tag + "^{commit}") != revision:
            raise ValueError("ProofWidgets needs its matching public release tag")
        print(pkg["name"], revision, flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    prepare(parser.parse_args().work_dir.resolve())
