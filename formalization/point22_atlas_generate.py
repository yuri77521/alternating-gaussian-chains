"""Extract the frozen atlas's complete binary cover as Lean data.

The verifier supplies candidates only. The Lean tree distinguishes a gap-order
prune, trial score, zero gradient, positive curvature and local-domain leaf.
The inner coordinates and split labels are integer ticks of 1/32000.

Run with Python 3 from any working directory. --check compares against the
existing Lean source, while --write regenerates it in place.
"""
import argparse
from collections import Counter
from functools import lru_cache
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent / "study" / "code"))
import verify_six_site_s22_block_atlas as atlas


def collect():
    lines = Path(atlas.__file__).read_text(encoding="utf-8").splitlines()
    reasons = ("order", "score", "gradient", "curvature", "local")
    markers = {next(i for i, ln in enumerate(lines, 1) if f'stats["{r}"] += 1' in ln): r
               for r in reasons}
    markers[next(i for i, ln in enumerate(lines, 1) if "todo.extend((" in ln)] = "split"
    nodes = atlas.gaussian_nodes()
    kernel = lru_cache(None)(lambda a, b: atlas.BlockKernel(nodes, a, b))
    floor = atlas.signed_point_score(nodes, [v * atlas.H for v in atlas.WITNESS])
    witness_hi = sum(atlas.signed(nodes[(b-a)*atlas.H], (-1)**(j-i))[1]
                     for i,a in enumerate(atlas.WITNESS)
                     for j,b in enumerate(atlas.WITNESS) if i<j)
    forest = {}
    ranges = {}
    internals = {}
    examples = []
    for word in atlas.contact_words():
        sequence = []
        terms = [atlas.signed(nodes[(j-i)*atlas.H], (-1)**(j-i))
                 for size in word for i in range(size) for j in range(i+1,size)]
        internals[word] = (sum(r[0] for r in terms),sum(r[1] for r in terms))
        def visit(frame, event, arg):
            if frame.f_code is not atlas.verify_face.__code__:
                return None
            kind = markers.get(frame.f_lineno) if event == "line" else None
            if kind is None:
                return visit
            d = frame.f_locals
            lo, hi = d["lo"], d["hi"]
            if kind == "split":
                entry = kind, d["k"], d["mid"]
            elif kind == "order":
                empty = next((i for i,(a,b) in enumerate(zip(lo,hi)) if b<a), None)
                if empty is not None:
                    entry = kind, empty
                else:
                    i = next(i for i in d["equal_starts"]
                             if lo[i]-hi[i-1]-(word[i-1]-1)*atlas.H > d["wrap_upper"])
                    entry = kind, 6+i
            elif kind == "gradient":
                i = next(i for i,(a,b) in enumerate(zip(d["grad_lower"],d["grad_upper"]))
                         if a>0 or b<0)
                entry = kind, i
                if word == (3,1,1,1):
                    examples.append((d["stats"]["visited"],tuple(lo),tuple(hi),i,
                                     d["grad_lower"][i],d["grad_upper"][i]))
            elif kind == "curvature":
                j = next(j for j,row in enumerate(d["weights"])
                         if sum(w*d["hessian_lower"][k] for k,w in row)>0)
                v = d["directions"][j]
                # Ternary digit 0,1,2 encodes -1,0,1, least significant first.
                entry = kind, sum((v_i+1)*3**i for i,v_i in enumerate(v))
            else:
                entry = kind,
                if kind == "score" and word == (3,1,1,1):
                    examples.append((d["stats"]["visited"], tuple(lo), tuple(hi), d["score_upper"], floor))
            if kind in ("score","gradient","curvature"):
                for i,j,lower,upper,_,tab in d["pairs"]:
                    if kind == "gradient" and entry[1] not in (i,j):
                        continue
                    if kind == "curvature" and v[i] == v[j]:
                        continue
                    left, right = max(lo[j]-hi[i],lower), min(hi[j]-lo[i],upper)
                    o = {"score":0,"gradient":1,"curvature":2}[kind]
                    ans = tab.range(left,right)
                    ranges[word[i],word[j],o,left,right] = ans[2*o:2*o+2]
            sequence.append(entry)
            return visit
        try:
            sys.settrace(visit)
            stats = atlas.verify_face(word,nodes,kernel,floor)
        finally:
            sys.settrace(None)
        assert len(sequence) == stats["visited"]
        forest[word] = sequence
        print("".join(map(str, word)), stats["visited"], dict(Counter(e[0] for e in sequence)))
    return forest,examples,ranges,internals,(floor,witness_hi)


def tree_expr(tag, sequence):
    pos = 0
    defs = []
    def descend():
        nonlocal pos
        item = sequence[pos]
        pos += 1
        kind = item[0]
        if kind != "split":
            if kind == "local":
                return ".localDomain", 1
            names = {"order":"feasible", "score":"score", "gradient":"gradient", "curvature":"curvature"}
            return f".leaf (.{names[kind]} {item[1] if len(item)>1 else 0})", 1
        # The Python stack visits the right child first.
        right, nr = descend()
        left, nl = descend()
        expr = f".split {item[1]} {item[2]} ({left}) ({right})"
        size = 1+nl+nr
        if size >= 32:
            name = f"branch{tag}_{len(defs)}"
            defs.append(f"private def {name} : Tree 6 :=\n  {expr}\n")
            return name, 1
        return expr, size
    expr,_ = descend()
    assert pos == len(sequence)
    defs.append(f"def tree{tag} : Tree 6 :=\n  {expr}\n")
    return "\n".join(defs)


def output(forest):
    lines = ["import CertTree", "import Point22Contacts", "",
             "/-! Complete frozen width-22 contact-block atlas, in units of 1/32000.",
             "Regenerate using point22_atlas_generate.py --write. These trees supply no inequalities. -/",
             "", "namespace GaussianChains.Point22.Atlas", "open GaussianChains.Cert", ""]
    words = {(6,):"six", (3,3):"threeThree", (4,2):"fourTwo", (5,1):"fiveOne",
             (2,2,2):"twoTwoTwo", (3,2,1):"threeTwoOne", (4,1,1):"fourOneOne",
             (2,1,2,1):"twoOneTwoOne", (2,2,1,1):"twoTwoOneOne", (1,1,1,1,1,1):"singletons",
             (2,1,1,1,1):"twoOneOneOneOne", (3,1,1,1):"threeOneOneOne"}
    assert set(words) == set(forest)
    for w,seq in forest.items():
        lines.append(tree_expr("".join(map(str,w)), seq))
    lines += ["def tree : Word → Tree 6"]
    for w in forest:
        lines.append(f"  | .{words[w]} => tree{''.join(map(str,w))}")
    lines += ["","end GaussianChains.Point22.Atlas",""]
    return "\n".join(lines)


def signed(n):
    return f"({n})" if n < 0 else str(n)


def packed_key(k):
    a,b,o,l,r = k
    return (((a*7+b)*3+o)*32001+l)*32001+r


def table_code(ranges,internals,witness):
    # Numerical inputs have no authority until each claimed interval is justified.
    lines = ["import Point22AtlasIndex", "", "namespace GaussianChains.Point22.Atlas",
             "open GaussianChains.Cert", ""]
    rows = sorted((packed_key(k),k,v) for k,v in ranges.items())
    assert len({entry[0] for entry in rows}) == len(rows)
    chunks = []
    def binary(entries, leaf, name, indent="  "):
        if len(entries) == 1:
            return leaf(entries[0])
        mid=len(entries)//2
        p=entries[mid-1][0]
        ls=binary(entries[:mid],leaf,name,indent+"  ")
        rs=binary(entries[mid:],leaf,name,indent+"  ")
        return f".fork {p}\n{indent}  ({ls})\n{indent}  ({rs})"
    for start in range(0,len(rows),64):
        group = rows[start:start+64]
        name = f"rangePage{len(chunks)}"
        body = binary(group,lambda e: ".leaf ⟨"+", ".join(map(str,(*e[1],*e[2])))+"⟩",name)
        lines += [f"def {name} : RangeIndex :=",f"  {body}",""]
        chunks.append((group[-1][0],name))
    lines += ["def claimIndex : RangeIndex :=",
              "  "+binary(chunks,lambda e:e[1],"claimIndex"),""]
    lines += [f"def witnessTicks : Interval := ofTicks {signed(witness[0])} {signed(witness[1])}", "",
              "def internalTicks : Word → Interval"]
    names = {(6,):"six",(3,3):"threeThree",(4,2):"fourTwo",(5,1):"fiveOne",
        (2,2,2):"twoTwoTwo",(3,2,1):"threeTwoOne",(4,1,1):"fourOneOne",(2,1,2,1):"twoOneTwoOne",
        (2,2,1,1):"twoTwoOneOne",(1,1,1,1,1,1):"singletons",(2,1,1,1,1):"twoOneOneOneOne",
        (3,1,1,1):"threeOneOneOne"}
    for word,(lo,hi) in internals.items():
        lines.append(f"  | .{names[word]} => ofTicks {signed(lo)} {signed(hi)}")
    return "\n".join(lines+["","end GaussianChains.Point22.Atlas",""])


def main():
    parser = argparse.ArgumentParser()
    g = parser.add_mutually_exclusive_group(required=True)
    g.add_argument("--write", action="store_true")
    g.add_argument("--check", action="store_true")
    args = parser.parse_args()
    forest, examples, ranges, internals, witness = collect()
    tsv = "a\tb\tord\tL\tR\tlo\thi\n" + "".join(
        "\t".join(map(str,(*key,*r)))+"\n" for key,r in sorted(ranges.items()))
    artifacts = {"Point22AtlasData.lean":output(forest), "Point22AtlasClaims.lean":table_code(ranges,internals,witness),
                 "certificates/point22-atlas-ranges.tsv":tsv}
    for dest,expected in artifacts.items():
        path = HERE / dest
        if args.write:
            path.parent.mkdir(exist_ok=True)
            path.write_text(expected,encoding="utf-8",newline="\n")
        elif path.read_text(encoding="utf-8") != expected:
            raise SystemExit(f"Generated atlas differs from {path}")
    print(sum(map(len,forest.values())), "nodes;", len(forest), "words")
    print(len(ranges),"distinct signed-block queries; witness bounds (ticks)",witness)
    # Print the narrowest nontrivial score leaf for the independent image-energy spot check.
    pick = min((r for r in examples if len(r)==5 and any(a<b for a,b in zip(r[1],r[2]))),
               key=lambda r: (max(b-a for a,b in zip(r[1],r[2])),r[0]))
    print("real score leaf", pick)
    grad = min((r for r in examples if len(r)==6 and any(a<b for a,b in zip(r[1],r[2]))),
               key=lambda r: (max(b-a for a,b in zip(r[1],r[2])),r[0]))
    if grad[:4] != (434, (0,8033,16034,24031), (0,8034,16035,24033), 2):
        raise RuntimeError("The independent gradient leaf no longer matches the frozen atlas")
    print("real gradient leaf", grad)


if __name__ == "__main__":
    main()

