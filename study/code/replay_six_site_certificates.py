"""Replay the proof certificates and the executable blocks in their appendices."""

import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = (
    "verify_six_site_bifurcation.py",
    "verify_six_site_contact.py",
    "verify_six_site_global_reduction.py",
    "verify_six_site_width_band.py",
    "verify_six_site_s9_mesh.py",
    "verify_six_site_s9_thresholds.py",
    "verify_six_site_s9_small.py",
    "verify_six_site_s9_faces.py",
    "verify_six_site_width_strip.py",
    "verify_six_site_strip_thresholds.py",
    "verify_six_site_strip_separation.py",
    "verify_six_site_s22.py",
    "verify_six_site_s22_faces.py",
    "verify_six_site_s22_block_atlas.py",
    "verify_six_site_s22_local.py",
)
APPENDICES = (
    "early-global.md",
    "packed-face.md",
    "global-referee.md",
    "block-translation-note.md",
    "block-translation-referee.md",
    "width-referee.md",
    "width-stability.md",
    "width-band-referee.md",
    "s9-referee.md",
    "width-strip-probes.md",
    "width-strip-referee.md",
    "s22-competitor.md",
    "s22-analytic-faces.md",
    "s22-interior.md",
    "s22-kernel.md",
    "s22-referee.md",
)


def main():
    if not __debug__:
        raise SystemExit("Enable Python assertions before running the certificates.")
    for name in SCRIPTS:
        print(f"Running {name}", flush=True)
        subprocess.run(
            [sys.executable, "-E", "-B", str(ROOT / "code" / name)],
            cwd=ROOT, check=True,
        )
    for name in APPENDICES:
        appendix = ROOT / "research" / "six-site" / name
        blocks = re.findall(r"^~~~python\n(.*?)^~~~$", appendix.read_text(encoding="utf-8"),
                            flags=re.MULTILINE | re.DOTALL)
        if len(blocks) != 1:
            raise ValueError(f"Expected one Python certificate in {name}, found {len(blocks)}")
        print(f"Running assertions in {name}", flush=True)
        subprocess.run(
            [sys.executable, "-I", "-B", "-"], input=blocks[0].encode("utf-8"),
            cwd=ROOT, check=True,
        )
    print("All six-site certificates passed.")


if __name__ == "__main__":
    main()
