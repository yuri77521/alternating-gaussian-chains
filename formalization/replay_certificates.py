"""Rebuild the archived numerical evidence and check the generated Lean packet data.

The Python checks establish regeneration and transcript agreement. The Lean
theorems are checked separately by rebuild.py.
"""
import argparse
from pathlib import Path
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
STUDY = ROOT.parent / "study"
PY = [sys.executable, "-X", "utf8", "-B"]


def run(script, *args, cwd=None, log=None, env=None):
    cmd = [*PY, str(script), *map(str, args)]
    subprocess.run(cmd, cwd=cwd or ROOT, env=env, check=True,
                   stdout=log, stderr=subprocess.STDOUT if log else None)


def match(actual, reference):
    if actual.read_text("utf8").splitlines() != reference.read_text("utf8").splitlines():
        raise ValueError(f"Regenerated text differs from {reference.name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--upstream-git", type=Path)
    args = parser.parse_args()
    work = args.work_dir.resolve()
    setup = ["setup", "--work-dir", work]
    if args.upstream_git:
        setup += ["--upstream-git", args.upstream_git.resolve()]
    run(STUDY / "reproduce.py", *setup)
    env = dict(os.environ, PYTHONPATH=str(work/"code"), PYTHONDONTWRITEBYTECODE="1")
    results = work / "results"
    log = results / "lean-formalization-python.txt"
    with log.open("wb") as stream:
        run(work / "code/replay_six_site_certificates.py", cwd=work, log=stream, env=env)
    match(log, work / "logs/certificates.txt")
    print(f"Frozen verifier transcript: {len(log.read_text('utf8').splitlines())} lines.", flush=True)

    with tempfile.TemporaryDirectory(dir=results) as tmp:
        out = Path(tmp)
        for s in range(3):
            name = f"BandPackets{s}.lean"
            run(ROOT/"emit_band.py", "--study", work, "--output", out/"packets",
                "--slab", s, "--lean", out/name, env=env)
            match(out/name, ROOT/name)
        run(ROOT/"band_row_proofs.py", "--candidates", out/"packets", "--output", ROOT, "--check", env=env)
        run(ROOT/"phase_strip_data.py", work, "--output", out, env=env)
        for file in out.glob("PhaseStrip*.lean"):
            match(file, ROOT/file.name)
    run(ROOT.parent/"scripts/generate_root_witnesses.py", "--check", env=env)
    run(ROOT/"CertTreeAtlasExample.py", env=env)
    run(ROOT/"CertTreeWidthSamples.py", "--check", env=env)
    run(ROOT/"band_cache_generate.py", "--check", env=env)
    run(ROOT/"point22_atlas_generate.py", "--check", env=env)
    run(ROOT/"point22_atlas_tables.py", "--check", env=env)
    run(ROOT/"point22_atlas_tables_proofs.py", "--check", env=env)
    run(ROOT/"point22_atlas_ranges_generate.py", "--check", env=env)
    run(ROOT/"point22_atlas_word_proofs.py", "--check", env=env)
    run(ROOT/"point22_two_trees_generate.py", "--check", env=env)
    run(ROOT/"point22_score_nodes.py", env=env)
    print("Candidate regeneration and archived verifier replay passed.")


if __name__ == "__main__":
    main()
