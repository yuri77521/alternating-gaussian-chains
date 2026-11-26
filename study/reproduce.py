"""Rebuild the certificates, figure, papers and Lean proofs from this distribution."""
import argparse
import hashlib
import os
from pathlib import Path, PurePosixPath
import re
import runpy
from difflib import unified_diff
import shutil
import subprocess
import sys
import tempfile
import time
from urllib.request import urlopen

SOURCE = Path(__file__).resolve().parent
UPSTREAM = "3389797a4aac8ed1c65e93c864cfa2305b65359a"
RAW = f"https://raw.githubusercontent.com/xiujiang4/alternating-particle-chains/{UPSTREAM}/"
MESH = "code/probe_six_site_transition.py"
SWEEP = "code/probe_six_site_s9.py"
CHECKS = {
    "gaussian-infimum": ["code/verify_gaussian_infimum.py"],
    "exact-clusters": ["code/verify_exact_clusters.py"],
    "certificates": ["code/replay_six_site_certificates.py"],
    "supplementary": ["manuscript/paper/reproduction/replay_supplement.py"],
    "rounding-low": [MESH, "--mesh", "48", "--band", ".080", ".100", "20"],
    "rounding-high": [MESH, "--mesh", "40", "--band", ".100", ".132", "32"],
    "mesh-and-seeds": [MESH, "--mesh", "32", "--starts", "24"],
    "search-9": [SWEEP, "--detail"],
    "search-825": [SWEEP, "--width", "8.25", "--h", ".000000001", ".1300211", ".1300212", ".131", ".1322869", ".1322870", "49999997/300000000", "--detail"],
    "search-85": [SWEEP, "--width", "8.5", "--h", ".000000001", ".1289694", ".1289695", ".130", ".1313559", ".1313560", "49999997/300000000", "--detail"],
    "search-875": [SWEEP, "--width", "8.75", "--h", ".000000001", ".1279892", ".1279893", ".129", ".1304821", ".1304822", "49999997/300000000", "--detail"],
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def inventory(file):
    rows = {}
    for line in file.read_text(encoding="utf-8").splitlines():
        checksum, name = line.split("  ", 1)
        path = PurePosixPath(name)
        if (not re.fullmatch("[0-9a-f]{64}", checksum) or not path.parts
                or path.is_absolute() or ".." in path.parts or ":" in name
                or "\\" in name or path.as_posix() != name or name in rows):
            raise ValueError(f"Invalid manifest entry in {file.name}: {name}")
        rows[name] = checksum
    return rows


def checked(data, expected, name):
    if digest(data) != expected:
        raise ValueError(f"SHA-256 mismatch for {name}")
    return data


def setup(args):
    public = inventory(SOURCE / "SHA256SUMS.txt")
    for name, expected in public.items():
        checked((SOURCE / name).read_bytes(), expected, name)
    manifest = (SOURCE / "SHA256SUMS.txt").read_bytes()
    public["SHA256SUMS.txt"] = digest(manifest)
    upstream = inventory(SOURCE / "upstream-files.sha256")
    if set(public).intersection(upstream):
        raise ValueError("Duplicated public and external inputs")
    work = args.work_dir.resolve()
    if work.is_relative_to(SOURCE) or SOURCE.is_relative_to(work):
        raise ValueError("Use a work directory outside the extracted source")
    marker = ".assembled-source.sha256"
    if work.exists():
        if not (work / marker).is_file() or (work / marker).read_text("ascii").strip() != digest(manifest):
            raise ValueError("Choose a new work directory or one prepared from this exact archive")
        for name, expected in {**public, **upstream}.items():
            checked((work / name).read_bytes(), expected, name)
    else:
        work.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=work.parent, prefix="chain-setup-") as temp:
            stage = Path(temp) / "source"
            for name in public:
                dst = stage / name
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(SOURCE / name, dst)
                checked(dst.read_bytes(), public[name], name)
            for name, expected in upstream.items():
                if args.upstream_git:
                    data = subprocess.check_output(
                        ["git", "-C", str(args.upstream_git.resolve()), "cat-file", "blob", f"{UPSTREAM}:{name}"])
                else:
                    with urlopen(RAW + name, timeout=120) as response:
                        data = response.read()
                dst = stage / name
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes(checked(data, expected, name))
            (stage / marker).write_text(digest(manifest) + "\n", encoding="ascii")
            stage.rename(work)
    (work / "results").mkdir(exist_ok=True)
    print(f"Verified {len(public)} package files and {len(upstream)} pinned external files.", flush=True)
    return work


def run(work, name, args):
    log = work / "results" / (name + ".txt")
    env = dict(os.environ, PYTHONUTF8="1", PYTHONIOENCODING="utf-8")
    start = time.monotonic()
    print(f"Running {name}", flush=True)
    with log.open("wb") as output:
        rc = subprocess.run(args, cwd=work, env=env, stdout=output, stderr=subprocess.STDOUT).returncode
    if rc:
        raise SystemExit(f"{name} exited with code {rc}. See {log}")
    print(f"Passed {name} ({time.monotonic() - start:.1f}s).", flush=True)


def strict_lines(name, body):
    lines = body.strip().splitlines()
    if name == "supplementary":
        # These rows describe projected floating searches; the subsequent X, Z
        # and fine-grid witness intervals are exact and stay in the comparison.
        return [row for row in lines if not re.match(r"^(?:[01]{6} |descents )", row)]
    return lines


def compare_strict(work, name, expected):
    log = work / "results" / (name + ".txt")
    actual = strict_lines(name, log.read_text(encoding="utf-8"))
    reference = strict_lines(name, expected)
    if actual != reference:
        diff = unified_diff(reference, actual, fromfile="reference", tofile=str(log), n=1)
        raise ValueError("Certified output differs:\n" + "\n".join(diff))
    return len(reference)


def numeric(work):
    logs = work / "logs"
    parts = re.split(r"(?m)^=== ([a-z0-9-]+) ===\n", (logs / "experiments.txt").read_text("utf-8"))
    experiments = dict(zip(parts[1::2], parts[2::2]))
    strict = {name: experiments[name] for name in ("supplementary", "rounding-low", "rounding-high")}
    strict["certificates"] = (logs / "certificates.txt").read_text("utf-8")
    verified = []
    for name, arguments in CHECKS.items():
        # The supplementary driver starts isolated children and the frozen log includes a Unicode path.
        flags = ["-I"] if name == "supplementary" else ["-E"]
        run(work, name, [sys.executable, *flags, "-X", "utf8", "-B", *arguments])
        if name in strict:
            count = compare_strict(work, name, strict[name])
            verified.append(f"{name}: {count} certified transcript lines matched")
    (work / "results/strict-checks.txt").write_text("\n".join(verified) + "\n", encoding="utf-8")
    print("\n".join(verified), flush=True)


def artifacts(work, args):
    # The typesetter and the Chinese plot use the same hash-checked font files.
    builder_file = work / "manuscript/paper/build_papers.py"
    stage_fonts = runpy.run_path(str(builder_file))["stage_fonts"]
    with tempfile.TemporaryDirectory() as temporary:
        fonts = Path(temporary) / "fonts"
        stage_fonts(fonts, args.font_dir)
        render_artifacts(work, args, fonts)


def render_artifacts(work, args, fonts):
    figure = work / "results" / "width-strip.png"
    plot_python = str(args.figure_python.resolve()) if args.figure_python else sys.executable
    run(work, "figure", [plot_python, "-B", "code/plot_six_site_width_strip.py", "--output", str(figure)])
    chinese = work / "results/width-strip-zh.png"
    run(work, "figure-zh", [plot_python, "-B", "code/plot_six_site_width_strip.py", "--language", "zh",
                             "--font-dir", str(fonts), "--output", str(chinese)])
    comparison = [(f, work / "research/six-site" / f.name) for f in (figure, chinese)]
    builder = [sys.executable, "-B", "manuscript/paper/build_papers.py", "--output-dir", str(work / "results"), "--keep-logs"]
    builder.extend(["--font-dir", str(fonts)])
    if args.only_cached:
        builder.append("--only-cached")
    run(work, "papers", builder)
    comparison.extend((work / "results" / f"paper-{lang}.pdf", work / f"paper-{lang}.pdf") for lang in ("en", "zh"))
    for output, reference in comparison:
        actual = digest(output.read_bytes())
        print(f"{actual}  {output.name}", flush=True)
        if actual != digest(reference.read_bytes()):
            raise SystemExit(f"Generated {output.name} differs from the archived bytes. See README.md for the reference toolchain.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task", choices=("setup", "numeric", "artifacts", "lean", "all"))
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--upstream-git", type=Path, help="local Git repository containing the pinned upstream revision")
    parser.add_argument("--figure-python", type=Path, help="Python executable with the pinned plotting packages")
    parser.add_argument("--font-dir", type=Path, help="directory with the two pinned Noto OTF files")
    parser.add_argument("--only-cached", action="store_true", help="use only previously cached Tectonic bundle resources")
    parser.add_argument("--installed-dependencies", action="store_true", help="verify and use installed third-party Lake packages")
    args = parser.parse_args()
    work = setup(args)
    if args.task in ("numeric", "all"):
        numeric(work)
    if args.task in ("artifacts", "all"):
        artifacts(work, args)
    if args.task in ("lean", "all"):
        cmd = [sys.executable, "-B", "reproduce_lean.py", "--root", str(work)]
        if args.installed_dependencies:
            cmd.append("--installed-dependencies")
        run(work, "lean", cmd)


if __name__ == "__main__":
    main()
