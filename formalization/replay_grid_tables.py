"""Replay the five kernel tables and compare against the v1.0.1 programs.

First run lake build +CertTreeGridCache. With lake on PATH run
    python replay_grid_tables.py
Use --local-runner to use this workspace's bounded Windows Lean launcher.
The Lean kernel proof for every row is Tables.gridTable_eq together with
Tables.gridNode_strip_sound or Tables.gridNode_point_sound.
"""
import argparse
from fractions import Fraction
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT.parent / "study" / "code"))
from verify_six_site_global_reduction import GRID, UNIT, ceil_div, samples
from six_site_s22_block_kernel import _node_values
from verify_six_site_s22_block_atlas import gaussian_nodes

DUMP = r'''
import CertTreeGridCache

open GaussianChains.Cert GaussianChains.Cert.Tables

private def endpoints (unit : ℕ+) (I : Interval) : String :=
  let lo : ℤ := ⌊I.lo*(unit:ℚ)⌋
  let hi : ℤ := ⌈I.hi*(unit:ℚ)⌉
  s!"{lo}\t{hi}"

def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "one output directory required")
  let rows : List (String × ℚ × ℕ+ × ℕ+ × ℕ+) :=
    [("8",8,10^32,10^9,8192), ("8.25",33/4,10^32,10^9,8192),
     ("8.75",35/4,10^32,10^9,8192), ("22-face",22,10^32,10^9,16000),
     ("22-atlas",22,10^35,10^11,32000)]
  for (name,s,scale,unit,M) in rows do
    let table := gridTable scale unit M s
    let path := System.FilePath.mk folder / s!"grid-{name}.tsv"
    IO.FS.withFile path .write fun handle => do
      for row in table do
        handle.putStrLn (endpoints unit row.value ++ "\t" ++ endpoints unit row.first ++
          "\t" ++ endpoints unit row.second)
    IO.println s!"{name}: {table.size} grid nodes"
'''

def read_rows(directory, name, grid):
    file = directory / f"grid-{name}.tsv"
    rows = [tuple(map(int, line.split())) for line in file.read_text(encoding="utf8").splitlines()]
    if len(rows) != grid + 1 or any(len(row) != 6 for row in rows):
        raise ValueError(f"wrong dimensions in {file}")
    return rows


def compare(directory):
    for name in ("8", "8.25", "8.75"):
        rows = read_rows(directory, name, GRID)
        lo, hi = samples(Fraction(name))
        for p, row in enumerate(rows):
            expected = []
            for j, cap in enumerate((4, 20, 150)):
                pad = ceil_div(cap * UNIT, 2 * GRID)
                expected.extend([lo[j][p] + pad, hi[j][p] - pad])
            if row != tuple(expected):
                raise ValueError(f"s={name}, p={p}: {row} != {expected}")
        print(f"s={name}: {6 * len(rows)} integer endpoints agree", flush=True)

    m = 16000
    rows = read_rows(directory, "22-face", m)
    mids, errors = _node_values(m)
    radii = [0, 0, 0]
    for p, row in enumerate(rows[:m]):
        for j in range(3):
            lo, hi = row[2*j:2*j+2]
            mid = (lo + hi) // 2
            if mid != mids[j][p]:
                raise ValueError(f"s=22 face table: midpoint mismatch at ({p}, {j})")
            radii[j] = max(radii[j], hi - mid)
    if radii != errors:
        raise ValueError(f"s=22 face table: radius mismatch {radii} != {errors}")
    print(f"s=22 face table: {3*m} midpoints and three maximal radii agree", flush=True)
    m = 32000
    rows = read_rows(directory, "22-atlas", m)
    for p, (actual, expected) in enumerate(zip(rows[:m], gaussian_nodes(), strict=True)):
        if actual != expected:
            raise ValueError(f"s=22 atlas table: mismatch at {p}")
    print(f"s=22 atlas table: {6*m} integer endpoints agree", flush=True)


def replay(directory, local_runner, lake):
    source = directory / "DumpGrid.lean"
    with source.open("x", encoding="utf8") as out:
        out.write(DUMP)
    if local_runner:
        cmd = [str(Path(os.environ["ProgramFiles"]) / "PowerShell/7/pwsh.exe"),
               "-NoProfile", "-File", str(ROOT / "run-lean.ps1"), "--run"]
    else:
        cmd = [lake, "env", "lean", "--run"]
    subprocess.run([*cmd, str(source), str(directory)], cwd=ROOT, check=True)
    compare(directory)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="path to Lake")
    parser.add_argument("--local-runner", action="store_true")
    parser.add_argument("--keep", type=Path, help="new directory for emitted tables")
    args = parser.parse_args()
    if args.keep:
        dest = args.keep.resolve()
        dest.mkdir(parents=True, exist_ok=False)
        replay(dest, args.local_runner, args.lake)
    else:
        with tempfile.TemporaryDirectory(prefix="cert-grids-") as tmp:
            replay(Path(tmp), args.local_runner, args.lake)

