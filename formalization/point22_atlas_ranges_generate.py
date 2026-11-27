"""Generate kernel-reduced integer range proofs for the frozen width-22 atlas.

Each raw sample lookup reads a separately certified node. Short dyadic runs
check every node. Long runs join verified children, so distinct queries reuse
the same integer comparisons. The exporter is untrusted; the generated Lean
modules prove all comparisons and the membership coverage of the claim list.
"""
import argparse
from collections import defaultdict
import csv
from functools import lru_cache
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent / "study" / "code"))
from verify_six_site_s22_block_atlas import gaussian_nodes, GRID, H, DERIVATIVE_CAPS, UNIT, ceil_div

ORDERS = ("value", "first", "second")
LEAF = 256
SHARD_WIDTH = 4096


def cover(lo, hi):
    pieces = []
    while lo <= hi:
        width = lo & -lo if lo else 1 << (hi + 1).bit_length()
        while lo + width - 1 > hi:
            width >>= 1
        pieces.append((lo, width))
        lo += width
    return pieces


def raw_row(nodes, a, b, order):
    intervals = []
    for p in range(GRID + 1):
        low = high = 0
        for i in range(a):
            for j in range(b):
                q = (p + H*(j - i)) % GRID
                seed_low, seed_high = nodes[q][2*order:2*order+2]
                if (i+j) % 2:
                    low -= seed_high
                    high -= seed_low
                else:
                    low += seed_low
                    high += seed_high
        intervals.append((low, high))
    return intervals


def group_header(x):
    return "Point22AtlasRangeGroup" + "".join(map(str, x))


def emit_group(rows, a, b, order, nodes, data_module, row_name, previous):
    values = raw_row(nodes, a, b, order)
    group_name = group_header((a,b,order))
    fragment_namespace = f"Leaf{a}{b}{order}"
    leaves = defaultdict(list)
    result = ["import Point22AtlasFastBlock", f"import {data_module}", "",
              "/-! Verified signed-kernel range facts generated from the frozen atlas. -/",
              "namespace GaussianChains.Point22.Atlas.RangeTicks", "open Tables GaussianChains.ImageBounds", "",
              "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "set_option Elab.async false", "",
              f"open {fragment_namespace}", "",
              f"private abbrev get := fastBlock {row_name} {a} {b} .{ORDERS[order]}",
              f"private theorem get_eq_raw : get = rawBlock {row_name} {a} {b} .{ORDERS[order]} :=",
              f"  funext (fastBlock_eq_raw {row_name} {a} {b} .{ORDERS[order]})", ""]

    @lru_cache(None)
    def run(start, count):
        name = f"s{start}_{count}"
        if count > LEAF:
            h = count//2
            left, low1, high1 = run(start, h)
            right, low2, high2 = run(start+h, h)
            low, high = min(low1, low2), max(high1, high2)
            proof = f"join {left} {right} (by decide) (by decide)"
        else:
            part = values[start:start+count]
            assert len(part) == count
            low, high = min(p[0] for p in part), max(p[1] for p in part)
            leaves[start // SHARD_WIDTH].extend([
                f"theorem {name} : Run get {start} {count} ⟨{low},{high}⟩ :=",
                "  of_check (by decide +kernel)", ""
            ])
            return name, low, high
        result.extend([f"private theorem {name} : Run get {start} {count} ⟨{low},{high}⟩ :=",
                       f"  {proof}", ""])
        return name, low, high

    pad = ceil_div(a * b * DERIVATIVE_CAPS[order] * UNIT, 8 * GRID**2)
    for idx, row in rows:
        _, _, _, left, right, low, high = row
        parts = [run(l,n) for l,n in cover(left,right)]
        assert low+pad == min(x[1] for x in parts)
        assert high-pad == max(x[2] for x in parts)
        record = ",".join(map(str,row))
        names = [f"(widen {name} (by decide))" for name,_,_ in parts]
        proof = names[-1]
        for part in reversed(names[:-1]):
            proof = f"(append {part} {proof})"
        result.extend([f"theorem claim{idx} : CheckedClaim {row_name} ⟨{record}⟩ := by",
                       f"  change Run (rawBlock {row_name} {a} {b} .{ORDERS[order]}) {left} {right+1-left} ⟨{low+pad},{high-pad}⟩",
                       "  rw [← get_eq_raw]",
                       f"  exact {proof}",""])
    result.append("end GaussianChains.Point22.Atlas.RangeTicks")
    # Each shard is a normal Lake module. Keeping the imports in stream order
    # bounds the number of simultaneous big-integer kernel reductions during
    # a clean default build. All arithmetic claims are ordinary Lean theorems.
    for bank in sorted(leaves):
        part = f"{group_name}Part{bank}"
        head = [f"import {previous}"] if previous else ["import Point22AtlasFastBlock",f"import {data_module}"]
        head += ["", "/-! One bounded segment of the width-22 integer range certificate. -/",
                 f"namespace GaussianChains.Point22.Atlas.RangeTicks.{fragment_namespace}",
                 "open Tables GaussianChains.ImageBounds", "",
                 "set_option maxRecDepth 1000000","set_option maxHeartbeats 0",
                 "set_option Elab.async false","",
                 f"private abbrev get := fastBlock {row_name} {a} {b} .{ORDERS[order]}", ""]
        yield part, "\n".join(head + leaves[bank] + [f"end GaussianChains.Point22.Atlas.RangeTicks.{fragment_namespace}"])+"\n"
        previous = part
    result[:2] = [f"import {previous}"]
    yield group_name, "\n".join(result) + "\n"


def pair_proof(names):
    if len(names) == 1:
        return names[0]
    mid = len(names)//2
    return f"⟨{pair_proof(names[:mid])}, {pair_proof(names[mid:])}⟩"


def generate(data_module, row_name):
    rows_path = HERE / "certificates" / "point22-atlas-ranges.tsv"
    with rows_path.open(encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f, delimiter="\t")
        rows = [tuple(int(r[k]) for k in ("a","b","ord","L","R","lo","hi")) for r in reader]
    assert rows == sorted(rows)
    assert len(set(r[:5] for r in rows)) == len(rows)
    groups = defaultdict(list)
    for idx,r in enumerate(rows): groups[r[:3]].append((idx,r))
    nodes = gaussian_nodes()
    previous = None
    for group, gs in groups.items():
        for name, source in emit_group(gs,*group,nodes,data_module,row_name,previous):
            yield name, source
            previous = name

    result = ["import Point22AtlasClaims"] + [f"import {group_header(g)}" for g in groups]
    result += ["","/-! Every integer range lookup used by the width-22 trees. -/",
               "namespace GaussianChains.Point22.Atlas.RangeTicks","open Tables","",
               "set_option maxRecDepth 1000000",""]
    pages = []
    for page,start in enumerate(range(0,len(rows),64)):
        names = [f"claim{i}" for i in range(start,min(start+64,len(rows)))]
        result += [f"private theorem page{page} : Every (CheckedClaim {row_name}) rangePage{page} :=",
                   "  "+pair_proof(names),""]
        pages.append(f"page{page}")
    result += [f"theorem checked_claimIndex : ∀ c ∈ claimIndex.entries, CheckedClaim {row_name} c :=",
               "  every_mem (idx:=claimIndex) ("+pair_proof(pages)+")","","#print axioms checked_claimIndex","",
               "end GaussianChains.Point22.Atlas.RangeTicks"]
    yield "Point22AtlasRangeChecked", "\n".join(result)+"\n"


def main():
    p=argparse.ArgumentParser(description=__doc__)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write",action="store_true")
    mode.add_argument("--check",action="store_true")
    p.add_argument("--dir",type=Path,default=HERE)
    p.add_argument("--data-module",default="Point22AtlasNodeData")
    p.add_argument("--row-name",default="verifiedRow")
    args=p.parse_args()
    for name,source in generate(args.data_module,args.row_name):
        dest=args.dir / (name+".lean")
        current = dest.read_text(encoding="utf8") if dest.exists() else None
        if args.write and current != source:
            dest.write_text(source,encoding="utf8",newline="\n")
        elif not args.write and current != source:
            raise ValueError(f"generated content mismatch in {dest.name}")
        print(f"{name}: {len(source)} bytes",flush=True)

if __name__=="__main__":
    main()

