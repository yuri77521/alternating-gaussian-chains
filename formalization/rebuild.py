"""Build all project modules and audit their exported certificates.

The default starts with empty project outputs. --resume continues an earlier
local build using Lake's dependency traces and reruns the final audit.
"""
import argparse
import graphlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parent
STANDARD = {"propext", "Quot.sound", "Classical.choice"}


def proof_text(code):
    """Strip Lean's nested block comments and prose strings for the source audit."""
    output = []
    pos = depth = 0
    while pos < len(code):
        if code.startswith("/-", pos):
            depth += 1
            output.append(" ")
            pos += 2
        elif depth and code.startswith("-/", pos):
            depth -= 1
            pos += 2
        elif depth:
            pos += 1
        elif code.startswith("--", pos):
            end = code.find("\n", pos)
            pos = len(code) if end < 0 else end
        elif code[pos] == '"':
            pos += 1
            while pos < len(code) and code[pos] != '"':
                pos += 2 if code[pos] == "\\" else 1
            pos += 1
            output.append(" ")
        else:
            output.append(code[pos])
            pos += 1
    return "".join(output)


def run(args, capture=False):
    if capture:
        return subprocess.check_output(args, cwd=ROOT, encoding="utf-8")
    subprocess.run(args, cwd=ROOT, check=True)


def check_sources(modules):
    paths = [ROOT / (module + ".lean") for module in modules]
    files = set(ROOT.glob("*.lean"))
    if set(paths) != files:
        raise SystemExit("The Lake roots and the proof source inventory differ.")
    forbidden = re.compile(r"\b(?:sorry|admit|sorryAx|native_decide|axiom)\b")
    imports = set()
    for path in paths:
        code = path.read_text(encoding="utf-8")
        if forbidden.search(code) and (match := forbidden.search(proof_text(code))):
            raise SystemExit(f"Inspect forbidden proof token {match[0]} in {path.name}.")
        imports.update(re.findall(r"^import (Mathlib(?:\.[\w.]+)*)$", code, re.M))
    return sorted(imports)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-git", type=Path)
    parser.add_argument("--installed-dependencies", action="store_true")
    parser.add_argument("--resume", action="store_true",
                        help="continue the existing local build and retain completed certificate pages")
    parser.add_argument("--batch-size", type=int, default=2,
                        help="prebuild this many modules at a time (default 2); zero goes directly to the default build")
    args = parser.parse_args()
    cmd = [sys.executable, "setup.py"]
    if args.upstream_git:
        cmd.extend(["--upstream-git", str(args.upstream_git.resolve())])
    run(cmd)
    build = ROOT / ".lake/build"
    if not args.resume and build.exists() and any(build.rglob("*.olean")):
        raise SystemExit("Use a fresh checkout for a cold rebuild, or --resume to continue this checkout.")
    if not re.search(r"\bversion 4\.28\.0\b", run(["lean", "--version"], True)):
        raise SystemExit("Use Lean 4.28.0.")
    config = tomllib.loads((ROOT / "lakefile.toml").read_text("utf-8"))
    roots = config["lean_lib"][0]["roots"]
    imports = check_sources(roots)
    if not args.installed_dependencies:
        run(["lake", "exe", "cache", "get", *imports])
    manifest = json.loads((ROOT / "lake-manifest.json").read_text("utf-8"))
    for dep in manifest["packages"]:
        d = ROOT / manifest["packagesDir"] / dep["name"]
        rev = run(["git", "-C", str(d), "rev-parse", "HEAD"], True).strip()
        if rev != dep["rev"]:
            raise SystemExit(f"Dependency revision mismatch for {dep['name']}.")
        if run(["git", "-C", str(d), "status", "--porcelain", "--untracked-files=no"], True).strip():
            raise SystemExit(f"Tracked source differs from the pinned {dep['name']} checkout.")
    if args.batch_size < 0:
        parser.error("batch size must be nonnegative")
    if args.batch_size:
        root_set = set(roots)
        deps = {m: root_set.intersection(re.findall(r"^import ([\w.]+)", (ROOT/(m+".lean")).read_text("utf8"), re.M))
                for m in roots}
        order = list(graphlib.TopologicalSorter(deps).static_order())
        if args.resume:
            lib = build / "lib/lean"
            order = [m for m in order if not ((lib/f"{m}.olean").is_file()
                                              and (lib/f"{m}.trace").is_file())]
        for offset in range(0, len(order), args.batch_size):
            group = order[offset:offset+args.batch_size]
            run(["lake", "--no-cache", "build", *("+" + m for m in group)])
    # Lake validates the complete graph again, including its previous outputs.
    run(["lake", "--no-cache", "build"])
    for name in roots:
        if not (build / "lib/lean" / f"{name}.olean").is_file():
            raise SystemExit(f"The default target did not compile {name}.")
    audit = ROOT / "Axioms.lean"
    expected = set(re.findall(r"^#print axioms ([\w.]+)$", audit.read_text("utf-8"), re.M))
    result = run(["lake", "env", "lean", str(audit)], True)
    print(result, end="")
    rows = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result)
    if not expected or {name for name, _ in rows} != expected:
        raise SystemExit("Missing or unexpected declarations in the axiom transcript.")
    for name, axioms in rows:
        deps = {a.strip() for a in axioms.split(",") if a.strip()}
        if not deps.issubset(STANDARD):
            raise SystemExit(f"Unexpected axiom dependencies for {name}: {deps - STANDARD}")
    print(f"Verified {len(roots)} project modules and {len(expected)} audited declarations.")


if __name__ == "__main__":
    main()
