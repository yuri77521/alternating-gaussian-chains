"""Generate lossless integer lookup tables for the width-22 atlas from v1.0.1.

The generated literal modules are data. Their correctness is a separate Lean
statement; equality of generated text alone supplies no mathematical bound.
"""
import argparse
from fractions import Fraction
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT.parent / "study" / "code"))
from verify_six_site_s22_block_atlas import GRID, WORK, exp_step, gaussian_nodes


def packed(rows, fields, bits, bias):
    limit = 1 << bits
    words = []
    acc = 0
    for i, row in enumerate(rows):
        if len(row) != fields:
            raise ValueError("wrong number of endpoints")
        for j, v in enumerate(row):
            if not 0 <= v + bias < limit:
                raise ValueError(f"lane overflow at row {i}: {v}")
            acc |= (v + bias) << (bits * ((i % 16) * fields + j))
        if i % 16 == 15:
            words.append(acc)
            acc = 0
    if len(rows) % 16:
        words.append(acc)
    return words


def banks(words, name):
    banks = [words[p:p+16] for p in range(0, len(words), 16)]
    lines = []
    for k, bank in enumerate(banks):
        words_text = ",\n  ".join(hex(w) for w in bank)
        lines.append(f"private def {name}Bank{k} : Array Nat := #[\n  {words_text}]\n")

    def pick(lo, hi, level):
        if hi-lo == 1:
            return f"({name}Bank{lo}[i % 16]?).getD 0"
        m = (lo+hi)//2
        pad = "  " * (level + 1)
        return (f"if i < {16*m} then\n{pad}{pick(lo,m,level+1)}\n"
                f"{'  '*level}else\n{pad}{pick(m,hi,level+1)}")
    lines.append(f"private def {name} (i : ℕ) : ℕ :=\n  {pick(0,len(banks),1)}\n")
    return "\n".join(lines)


def node_file():
    words = packed(gaussian_nodes(), 6, 48, 1 << 47)
    return """import Point22AtlasTablesTypes

/-! Frozen atlas candidate data. Each group packs sixteen rows in
little-endian 48-bit lanes with signed bias 2^47 (value, first and second
derivatives, low endpoint then high). Regenerate with point22_atlas_tables.py.
No assertions about the Gaussian kernel occur in this data module. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains.ImageBounds

""" + banks(words, "nodeWord") + """
private def orderLane : Order → ℕ
  | .value => 0 | .first => 2 | .second => 4

def verifiedRow (j : Order) (p : ℕ) : Ticks :=
  let word := nodeWord (p / 16)
  let offset := 48 * (6 * (p % 16) + orderLane j)
  let lower := (word >>> offset) % 281474976710656
  let upper := (word >>> (offset + 48)) % 281474976710656
  ⟨(lower : ℤ) - 140737488355328, (upper : ℤ) - 140737488355328⟩

end GaussianChains.Point22.Atlas.Tables
"""


def samples_file():
    z = Fraction(22, GRID**2)
    rl, rh = exp_step(z)
    sl, sh = exp_step(2*z)
    lo = hi = WORK
    samples, starts = [], []
    for i in range(4*GRID+1):
        samples.append((lo, hi))
        if i % 64 == 0:
            starts.append((lo, hi, rl, rh))
        lo, hi = lo*rl//WORK, -(-hi*rh//WORK)
        rl, rh = rl*sl//WORK, -(-rh*sh//WORK)
    return """import Point22AtlasTablesFixed

/-! Frozen integer samples and restart states. These are candidate numbers.
Each 64-step segment has its own exact-arithmetic verification. -/
namespace GaussianChains.Point22.Atlas.Tables

""" + banks(packed(samples, 2, 120, 0), "sampleWord") + """
private def sampleLane (word offset : ℕ) : ℤ :=
  ((word >>> offset) % 1329227995784915872903807060280344576 : ℕ)

def savedSample (p : ℕ) : Ticks :=
  let word := sampleWord (p / 16)
  let offset := 240*(p % 16)
  ⟨sampleLane word offset, sampleLane word (offset+120)⟩

""" + banks(packed(starts, 4, 120, 0), "restartWord") + """
def restart (b : ℕ) : State :=
  let word := restartWord (b / 16)
  let offset := 480*(b % 16)
  ⟨⟨sampleLane word offset,sampleLane word (offset+120)⟩,
   ⟨sampleLane word (offset+240),sampleLane word (offset+360)⟩⟩

end GaussianChains.Point22.Atlas.Tables
"""


def main():
    p = argparse.ArgumentParser()
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--write", action="store_true")
    g.add_argument("--check", action="store_true")
    args = p.parse_args()
    for file, expected in [("Point22AtlasNodeData", node_file()),
                           ("Point22AtlasTablesSamples", samples_file())]:
        path = ROOT / (file + ".lean")
        if args.write:
            if not path.exists() or path.read_text(encoding="utf8") != expected:
                path.write_text(expected, encoding="utf8", newline="\n")
        elif path.read_text(encoding="utf8") != expected:
            raise SystemExit(f"candidate mismatch: {path.name}")
        print(f"{path.name}: {len(expected.encode('utf8'))} bytes")


if __name__ == "__main__":
    main()

