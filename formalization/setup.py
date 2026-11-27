"""Materialize the immutable inputs without vendoring the upstream proof sources."""
import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
PAPER = "9a1909592c7131c12ddc176fbe153e442fbe0362"
UPSTREAM = "4c92f3aea0bd43931001f12f660b43e5d3ccb628"
URL = "https://github.com/xiujiang4/alternating-particle-chains.git"
MODULES = (
    "ArithmeticBounds Counterexample Direct FourPointCounterexample GaussianClass "
    "GaussianFourier GaussianDisplacement GaussianDisplacementEnergy GaussianMargin "
    "ImageReindex ParticleEnergy PeriodFourGaussian PeriodicGaussian PhysicalCellCore"
).split()


def retrieve(repo, revision, name, dest):
    data = subprocess.check_output(["git", "-C", repo, "cat-file", "blob", f"{revision}:{name}"])
    if dest.exists():
        if dest.read_bytes().replace(b"\r\n", b"\n") != data.replace(b"\r\n", b"\n"):
            raise SystemExit(f"Existing input differs from its pinned source: {dest}")
        return
    dest.write_bytes(data)


def setup(repo):
    for name in ["lean-toolchain", "lake-manifest.json", *(x + ".lean" for x in MODULES)]:
        retrieve(repo, UPSTREAM, "lean/" + name, ROOT / name)
    name = "AlternatingMoments.lean"
    retrieve(ROOT.parent, PAPER, "study/research/exact-clusters/" + name, ROOT / name)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-git", type=Path)
    args = parser.parse_args()
    if args.upstream_git:
        setup(args.upstream_git.resolve())
    else:
        with tempfile.TemporaryDirectory() as tmp:
            subprocess.run(["git", "clone", "--bare", URL, tmp], check=True)
            setup(Path(tmp))
