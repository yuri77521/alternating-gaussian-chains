"""Emit bounded kernel reduction jobs for the frozen width-22 tables.

Each proof checks a small contiguous range. A balanced conjunction of those
proofs covers every restart link and each of the 32000 six-endpoint rows.
"""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SHARDS = 32


def combine(names):
    if len(names) == 1:
        return names[0]
    k = len(names)//2
    return f"(Checked.join {combine(names[:k])} {combine(names[k:])})"


def checks(tag, pred, lo, hi, per, rule="Checked.of_segment"):
    records = []
    names = []
    for start in range(lo, hi, per):
        last = min(hi, start+per)
        name = f"{tag}At{start}"
        names.append(name)
        records.append(f"private theorem {name} : Checked {pred} {start} {last} :=\n"
                       f"  {rule} (lo := {start}) (count := {last-start}) "
                       "(by decide +kernel)\n")
    records.append(f"theorem {tag}From{lo} : Checked {pred} {lo} {hi} :=\n  {combine(names)}\n")
    return "\n".join(records)


def split(total, i):
    return (total*i//SHARDS, total*(i+1)//SHARDS)


def modules():
    previous = "Point22AtlasTablesChecks"
    samples, rows = [], []
    for i in range(SHARDS):
        name = f"Point22AtlasTablesPart{i:02d}"
        s, t = split(2000, i)
        a, b = split(32000, i)
        samples.append(f"bandsFrom{s}")
        rows.append(f"rowsFrom{a}")
        # Keep the reference summation for the first quarter of the grid;
        # the other rows share each of their seven images across all orders.
        extra = "import Point22AtlasTablesFused\n" if i == 8 else ""
        rule = "Checked.of_fused_segment" if i >= 8 else "Checked.of_segment"
        txt = (f"import {previous}\n{extra}\n"
               "/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/\n"
               "namespace GaussianChains.Point22.Atlas.Tables\n"
               "set_option Elab.async false\nset_option maxRecDepth 20000\nset_option maxHeartbeats 30000000\n\n"
               + checks("bands", "traceOK", s, t, 4) + "\n"
               + checks("rows", "rowOK", a, b, 32, rule)
               + "\nend GaussianChains.Point22.Atlas.Tables\n")
        yield name, txt
        previous = name
    txt = "import " + previous + """

/-! All 128001 samples and all 32000 rows now have a kernel-checked
connection to the actual periodized Gaussian and its two spatial derivatives. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains GaussianChains.ImageBounds
"""
    txt += f"\ntheorem allSamples : Checked traceOK 0 2000 :=\n  {combine(samples)}\n"
    txt += f"\ntheorem allRows : Checked rowOK 0 32000 :=\n  {combine(rows)}\n"
    txt += """
theorem verifiedRow_eq_gridNode (j : Order) {p : ℕ} (hp : p < 32000) :
    (verifiedRow j p).decode unit = GaussianChains.Cert.Tables.gridNode work unit grid 22 j p :=
  verifiedRow_eq_gridNode_of_checks allSamples allRows j hp

theorem verifiedRow_sound (j : Order) {p : ℕ} (hp : p < 32000) :
    ((verifiedRow j p).decode unit).Mem
      ((deriv^[orderIndex j] (kernel 22)) ((p:ℝ)/32000)) :=
  verifiedRow_sound_of_checks allSamples allRows j hp

#print axioms verifiedRow_sound
end GaussianChains.Point22.Atlas.Tables
"""
    yield "Point22AtlasTablesChecked", txt


def main():
    p = argparse.ArgumentParser()
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--write", action="store_true")
    g.add_argument("--check", action="store_true")
    args = p.parse_args()
    for name, source in modules():
        path = ROOT / (name + ".lean")
        if args.write:
            if not path.exists() or path.read_text(encoding="utf8") != source:
                path.write_text(source, encoding="utf8", newline="\n")
        elif not path.exists() or path.read_text(encoding="utf8") != source:
            raise SystemExit(f"generated source differs: {path.name}")


if __name__ == "__main__":
    main()

