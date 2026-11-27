"""Generate small local kernel obligations for every physical strip box.

Endpoints come from the candidate producer. Each intermediate chamber is checked,
so a proof for a node never re-expands the contractions above it.
"""
import argparse
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
SLABS = ["narrow", "lower", "upper"]
FLOORS = [14, 49, 49]
BARY = 8192


def supports():
    from itertools import combinations
    return [a for n in range(1, 6) for a in combinations(range(5), n)
            if a != (2,) and a <= tuple(4-k for k in reversed(a))]


def packed(v):
    if len(v) != 6 or any(not 0 <= k <= BARY for k in v):
        raise ValueError(f"invalid 14-bit vector {v}")
    return sum(x << (14*i) for i, x in enumerate(v))


def one_pass(lo, hi):
    sl, sh = sum(lo), sum(hi)
    if sl > BARY or sh < BARY:
        raise ValueError("unexpected empty chamber in the published width trees")
    raised = [max(l, BARY-sh+h) for l, h in zip(lo, hi)]
    lowered = [min(h, BARY-sum(raised)+l) for h, l in zip(hi, raised)]
    newlo = [*raised[:5], max(raised)]
    newhi = [min(h, lowered[5]) for h in lowered]
    return [raised, lowered, newlo, newhi], newlo, newhi


def bcode(lo, hi):
    return f"(box {packed(lo)} {packed(hi)})"


def pcode(p):
    return "(stage " + " ".join(str(packed(v)) for v in p) + ")"


def materialize(tree, lo, hi):
    p1, middle_lo, middle_hi = one_pass(lo, hi)
    p2, clo, chi = one_pass(middle_lo, middle_hi)
    raw = bcode(lo, hi)
    transition = f"(by decide +kernel : checkChamber {raw} {pcode(p1)} {pcode(p2)} = true)"
    tag = tree[0]
    if tag == "s":
        _, k, mid, lt, rt = tree
        lhi, rlo = chi[:], clo[:]
        lhi[k], rlo[k] = mid, mid
        left = yield from materialize(lt, clo, lhi)
        right = yield from materialize(rt, rlo, chi)
        call = (f"nodeSafe_split {k} {mid} {transition} (by decide +kernel) (by decide +kernel) "
                f"({left} V) ({right} V)")
    else:
        if tag == "g":
            reason = f"(.transfer (.gradient {tree[1]}))"
        elif tag == "c":
            reason = f"(.transfer (.curvature {tree[1]} {tree[2]}))"
        elif tag == "v":
            reason = f"(center {packed(tree[1])})"
        else:
            raise ValueError(f"unexpected terminal {tag}")
        call = f"nodeSafe_leaf V {transition} {reason} (by decide +kernel)"
    return (yield raw, call)


def emit_slab(args, slab, tag):
    mods, records, starts, floor_modules = [], [], set(), []
    index = 0
    group = 0
    rows = []
    def module_name(g):
        return f"BandRows{tag.title()}{g:02}"
    def flush():
        nonlocal group
        if not records:
            return
        mod = module_name(group)
        dep = "BandLocalProof\nimport BandNodeData" if group in starts else module_name(group-1)
        body = ["import " + dep, "", "namespace GaussianChains.Band.Material",
                "set_option Elab.async false", "set_option maxRecDepth 500000",
                "set_option maxHeartbeats 0", "", *records, "", "end GaussianChains.Band.Material", ""]
        emit(args, mod, "\n".join(body))
        mods.append(mod)
        records.clear()
        group += 1
    supp = supports()
    for b in range(FLOORS[slab]):
        starts.add(group)
        rnames = []
        for i, a in enumerate(supp):
            file = args.candidates/f"band-{slab}-{b:02}-{i:02}.json"
            rec = json.loads(file.read_text("ascii"))
            j = rec["trial"]
            hf = f"(floorId .{tag} {b})"
            vtype = f"(V : Fast.Valid .{tag} (Fast.packetCache .{tag}))"
            hi = [BARY//2 if k in a else 0 for k in range(5)] + [BARY]
            gen = materialize(rec["tree"], [0]*6, hi)
            name = None
            while True:
                try:
                    raw, call = gen.send(name)
                except StopIteration as end:
                    top = end.value
                    break
                name = f"node{slab}_{index}"
                records.append(f"theorem {name} {vtype} : NodeSafe .{tag} {hf} {i} {j} {raw} :=\n  {call}\n")
                index += 1
                # A short independent first page measures cost before the long run.
                if (group == 0 and len(records) >= 7) or len(records) >= args.nodes:
                    flush()
            rn = f"safe{slab}_{b}_{i}"
            records.append(f"theorem {rn} {vtype} : RowExcluded .{tag} {hf} {i} :=\n"
                           f"  rowExcluded_of_nodeSafe (by decide +kernel) ({top} V)\n")
            rnames.append(rn)
        floorname = f"floor{slab}_{b}"
        records.append(f"theorem {floorname} {vtype} (i : Fin 18) : RowExcluded .{tag} {hf} i := by\n"
                       "  fin_cases i\n" + "\n".join("  · exact "+n+" V" for n in rnames)+"\n")
        rows.append(floorname)
        flush()
        floor_modules.append(mods[-1])
    return floor_modules, rows, index


def emit(args, name, text):
    file = args.output/(name+".lean")
    if args.check:
        if file.read_text("utf8") != text:
            raise ValueError(f"mismatched generated module {name}")
    elif not file.exists() or file.read_text("utf8") != text:
        file.write_text(text, encoding="utf8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidates", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--nodes", type=int, default=192)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    imports, cases = [], []
    for s, tag in enumerate(SLABS):
        mods, rows, count = emit_slab(args,s,tag)
        page_imports = ["import "+mod for mod in mods]
        slab_module = "BandSlab" + tag.title() + "Checked"
        imports.extend([*page_imports, "import " + slab_module])
        emit(args,slab_module,"\n".join([*page_imports, "import BandVerifiedCacheValidity",
            f"import BandVerifiedCacheProof{s}", "", "namespace GaussianChains.Band.Material", "",
            "set_option maxRecDepth 100000 in", "set_option maxHeartbeats 0 in",
            f"theorem {tag}OfValid (V : Fast.Valid .{tag} (Fast.packetCache .{tag}))",
            f"    (b : Fin Slab.{tag}.count) (i : Fin 18) : RowExcluded .{tag} b i := by",
            "  fin_cases b", *("  · exact "+r+" V i" for r in rows), "",
            f"theorem {tag}Checked (b : Fin Slab.{tag}.count) (i : Fin 18) : RowExcluded .{tag} b i :=",
            f"  {tag}OfValid (Fast.packetCache_valid .{tag} Fast.checkedAnchor{s}) b i", "",
            f"#print axioms {tag}Checked", "end GaussianChains.Band.Material",""]))
        cases.append(f"  | {tag} => exact {tag}OfValid (V .{tag}) b i")
        print(tag, count, "nodes", mods[-1], flush=True)
    emit(args,"BandRowsDecided","\n".join([*imports, "", "namespace GaussianChains.Band.Material", "",
        "set_option maxRecDepth 100000 in", "set_option maxHeartbeats 0 in",
        "theorem allExcluded (V : ∀ s, Fast.Valid s (Fast.packetCache s))",
        "    (s : Slab) (b : Fin s.count) (i : Fin 18) : RowExcluded s b i := by",
        "  cases s with", *cases, "", "#print axioms allExcluded", "end GaussianChains.Band.Material",""]))


if __name__ == "__main__":
    main()
