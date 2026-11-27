"""Run the extracted Lean integer checks as a quick candidate preflight.

The separate Lake target Point22AtlasTablesChecked supplies the kernel proof.
"""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = """import Point22AtlasTablesChecks
open GaussianChains.Point22.Atlas.Tables

def main : IO Unit := do
  let start ← IO.monoMsNow
  unless decide (restart 0 = init) do throw (IO.userError "initial state mismatch")
  for i in [:2000] do
    unless traceOK i do throw (IO.userError s!"sample segment {i} failed")
  unless decide (savedSample 128000 = (restart 2000).sample) do
    throw (IO.userError "final sample mismatch")
  let mid ← IO.monoMsNow
  for p in [:32000] do
    unless rowOK p do throw (IO.userError s!"output row {p} failed")
  let last ← IO.monoMsNow
  IO.println s!"128001 samples in {mid-start} ms; 192000 output endpoints in {last-mid} ms"
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--local-runner", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="atlas-table-preflight-") as tmp:
        test = Path(tmp) / "AtlasTableCheck.lean"
        test.write_text(SOURCE, encoding="utf8")
        if args.local_runner:
            command = [str(Path(os.environ["ProgramFiles"]) / "PowerShell/7/pwsh.exe"),
                       "-NoProfile", "-File", str(ROOT/"run-lean.ps1"), "--run"]
        else:
            command = ["lake","env","lean","--run"]
        subprocess.run([*command,str(test)], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()

