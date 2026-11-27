"""Generate the range-membership proof for the two-tree width-22 reduction.

The 21111 and 3111 trees query ordered block-size pairs (1,1), (2,1) and (3,1).
Each retained proof references a range already checked against the certified
mesh. The Lean kernel checks the membership argument for every cut of the
binary claim index as well as the negative test for each irrelevant leaf.
"""

import argparse
import csv
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from point22_atlas_ranges_generate import group_header, pair_proof

HERE = Path(__file__).resolve().parent


def generate():
    with (HERE / "certificates" / "point22-atlas-ranges.tsv").open(encoding="utf-8", newline="") as file:
        rows = [(int(r["a"]), int(r["b"]), int(r["ord"])) for r in csv.DictReader(file, delimiter="\t")]
    relevant = lambda a, b: b == 1 and a in (1, 2, 3)
    groups = sorted({(a, b, o) for a, b, o in rows if relevant(a, b)})
    lines = ["import Point22TwoTreeLookup", "import Point22AtlasRangesSound", "import Point22AtlasTablesChecked"]
    lines.extend("import " + group_header(g) for g in groups)
    lines.extend([
        "", "/-! Only the 11, 21 and 31 block ranges are used by the two-tree reduction.",
        "Regenerate with point22_two_trees_generate.py --write. -/",
        "namespace GaussianChains.Point22.Atlas", "open RangeTicks Tables", "",
        "set_option maxRecDepth 100000", "",
        "private def Needed (c : RangeClaim) : Prop :=",
        "  TwoTreePair c.a c.b → CheckedClaim verifiedRow c", "",
        "private theorem used {c : RangeClaim} (h : CheckedClaim verifiedRow c) : Needed c := fun _ => h",
        "private theorem unused {c : RangeClaim} (h : ¬TwoTreePair c.a c.b) : Needed c := fun hc => (h hc).elim", "",
    ])
    pages = []
    for start in range(0, len(rows), 64):
        end = min(start + 64, len(rows))
        page = start // 64
        proofs = [
            f"(used claim{i})" if relevant(*rows[i][:2]) else "(unused (by decide))"
            for i in range(start, end)
        ]
        lines.extend([f"private theorem groupPage{page} : Every Needed rangePage{page} :=", "  " + pair_proof(proofs), ""])
        pages.append(f"groupPage{page}")
    lines.extend([
        "private theorem neededClaims : ∀ c ∈ claimIndex.entries, Needed c :=",
        "  every_mem (" + pair_proof(pages) + ")", "",
        "theorem two_tree_ranges_valid : ∀ c ∈ claimIndex.entries, TwoTreePair c.a c.b → RangeValid c := by",
        "  intro c hc hpair",
        "  exact checkedClaim_valid (node := verifiedRow) (fun j p hp => verifiedRow_sound j hp)",
        "    (neededClaims c hc hpair)", "",
        "#print axioms two_tree_ranges_valid", "end GaussianChains.Point22.Atlas", "",
    ])
    return "\n".join(lines), sum(relevant(a, b) for a, b, _ in rows), len(rows)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--write", action="store_true")
    modes.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text, count, total = generate()
    target = HERE / "Point22TwoTreeRanges.lean"
    if args.write:
        target.write_text(text, encoding="utf-8", newline="\n")
    elif text != target.read_text(encoding="utf-8"):
        raise SystemExit("Point22TwoTreeRanges.lean differs from the generated certificate index")
    print(f"{target.name}: {count} of {total} stored claims have relevant ordered block sizes.")
