"""Build the pinned prior four-site result and audit the four cluster lemmas.

Use the working copy created by reproduce.py setup. For a clean replay, that
copy may contain third-party packages in lean/.lake/packages. The project's
own compiled objects are generated from source during this run.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tomllib


MOMENTS = "../research/exact-clusters/AlternatingMoments.lean"
DECLARATIONS = {
    "Counterexample.lean": {
        "AlternatingParticleChains.admissible_gaussian_counterexample",
        "AlternatingParticleChains.admissible_cells_and_energy_gap",
    },
    MOMENTS: {
        "AlternatingMoments.firstMoment",
        "AlternatingMoments.secondMoment",
        "AlternatingMoments.tripleVariance_eq",
        "AlternatingMoments.triple_gap_derivatives",
    },
}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def audit(root, installed):
    lean = root / "lean"
    if not (lean / "lakefile.toml").is_file() or not (lean / MOMENTS).is_file():
        raise SystemExit("Run reproduce.py setup first and pass its working copy as --root.")
    config = tomllib.loads((lean / "lakefile.toml").read_text(encoding="utf-8"))
    modules = config["lean_lib"][0]["roots"]
    outputs = lean / ".lake" / "build" / "lib" / "lean"
    if any(outputs.rglob("*.olean")):
        raise SystemExit("A clean replay needs a fresh setup work directory. "
                         "Only the third-party directory lean/.lake/packages may be reused.")
    if len(modules) != 12 or set(modules) != {path.stem for path in lean.glob("*.lean")}:
        raise RuntimeError("Unexpected upstream module inventory")

    if installed:
        manifest = json.loads((lean / "lake-manifest.json").read_text(encoding="utf-8"))
        for pkg in manifest["packages"]:
            dep = lean / manifest["packagesDir"] / pkg["name"]
            if not dep.is_dir():
                raise SystemExit(f"Missing installed dependency {pkg['name']}")
            revision = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=dep, encoding="ascii").strip()
            if revision != pkg["rev"]:
                raise RuntimeError(f"Installed revision mismatch for {pkg['name']}")
    else:
        imports = set()
        for source in [*sorted(lean.glob("*.lean")), lean / MOMENTS]:
            imports.update(re.findall(r"^import (Mathlib\.[\w.]+)$",
                                      source.read_text(encoding="utf-8"), re.M))
        subprocess.run(["lake", "exe", "cache", "get", *sorted(imports)],
                       cwd=lean, check=True)
    version = subprocess.check_output(["lake", "env", "lean", "--version"],
                                      cwd=lean, encoding="utf-8").strip()
    print(version, flush=True)
    if not re.search(r"\bversion 4\.28\.0\b", version):
        raise RuntimeError("This upstream manifest requires Lean 4.28.0")
    subprocess.run(["lake", "--no-cache", "build"], cwd=lean, check=True)
    if any(not (outputs / f"{name}.olean").is_file() for name in modules):
        raise RuntimeError("Expected one newly compiled object for each upstream module")

    for file, expected in DECLARATIONS.items():
        report = subprocess.check_output(["lake", "env", "lean", file],
                                         cwd=lean, encoding="utf-8")
        print(report, end="")
        rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", report)
        if len(rows) != len(expected) or {name for name, _ in rows} != expected:
            raise RuntimeError(f"Unexpected theorem names or missing audit in {file}")
        for name, axioms in rows:
            if set(map(str.strip, axioms.split(","))) != AXIOMS:
                raise RuntimeError(f"Unexpected axiom dependencies for {name}: {axioms}")
    print("Compiled all 12 upstream modules and verified all six axiom reports.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd(),
                        help="fresh assembled working copy (default: current directory)")
    parser.add_argument("--installed-dependencies", action="store_true",
                        help="use the populated lean/.lake/packages at the manifest revisions")
    args = parser.parse_args()
    audit(args.root.resolve(), args.installed_dependencies)
