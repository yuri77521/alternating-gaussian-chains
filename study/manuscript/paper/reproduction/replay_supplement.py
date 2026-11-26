"""Replay the three standalone witnesses outside the six-site master replay.

Run from any working directory. All three inputs are fixed manuscript sources.
The s=22 search also reports exploratory endpoints. Its assertions re-evaluate
the energies of the rational competitors. No search is used as a global bound.
"""

from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[3]
WITNESSES = (
    "research/exact-clusters/certificate-referee.md",
    "research/exact-clusters/六粒子去对径初检.md",
    "research/six-site/s22-search.md",
)


def main():
    for name in WITNESSES:
        source = (ROOT / name).read_text(encoding="utf-8")
        matches = re.findall(r"^(`{3}|~{3})python\n(.*?)^\1$", source, re.M | re.S)
        if len(matches) != 1:
            raise ValueError(f"Expected one complete Python block in {name}")
        print(f"Running {name}", flush=True)
        subprocess.run(
            [sys.executable, "-I", "-B", "-"],
            cwd=ROOT, input=matches[0][1].encode("utf-8"), check=True,
        )
    print("All three supplementary witnesses passed.")


if __name__ == "__main__":
    main()
