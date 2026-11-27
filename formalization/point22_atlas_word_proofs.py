"""Generate kernel-checkable evaluation shards for the twelve width-22 atlas trees.

The input is the frozen atlas generator's Point22AtlasData.lean. Node counts,
child boxes and page boundaries guide evaluation only. Lean recomputes each join
and runs the real replay on every terminal. Run with --write or --check.
"""
import argparse
from dataclasses import dataclass
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
JOINS = "Point22AtlasWordPartitions"
WORDS = {
    "6": "six", "33": "threeThree", "42": "fourTwo", "51": "fiveOne",
    "222": "twoTwoTwo", "321": "threeTwoOne", "411": "fourOneOne",
    "2121": "twoOneTwoOne", "2211": "twoTwoOneOne", "3111": "threeOneOneOne",
    "21111": "twoOneOneOneOne", "111111": "singletons",
}


@dataclass
class Node:
    size: int = 1
    axis: int | None = None
    cut: int = 0
    left: object = None
    right: object = None
    reason: str = ""
    code: int = 0


def parse_trees():
    src = (HERE / "Point22AtlasData.lean").read_text(encoding="utf-8")
    definitions = {}
    pattern = r"^(?:private )?def (branch\d+_\d+|tree\d+) : Tree 6 :=\s*\n  ([^\n]+)"
    for name, body in re.findall(pattern, src, re.M):
        tokens = iter(re.findall(r"(?:branch\d+_\d+|\.\w+|\d+)", body))
        def consume():
            tag = next(tokens)
            if tag == ".localDomain":
                return Node(reason="local")
            if tag == ".leaf":
                reason, code = next(tokens), next(tokens)
                if reason not in {".score", ".gradient", ".curvature", ".feasible"} or not code.isdigit():
                    raise ValueError(f"Unrecognized leaf: {reason} {code}")
                return Node(reason=reason[1:], code=int(code))
            if tag in definitions:
                return definitions[tag]
            if tag != ".split":
                raise ValueError(f"Unrecognized constructor: {tag}")
            axis, cut = int(next(tokens)), int(next(tokens))
            left, right = consume(), consume()
            return Node(1 + left.size + right.size, axis, cut, left, right)
        definitions[name] = consume()
        if next(tokens, None) is not None:
            raise ValueError(f"Trailing tokens in {name}")
    result = {tag: definitions["tree" + tag] for tag in WORDS}
    if sum(n.size for n in result.values()) != 5638:
        raise ValueError("Unexpected number of nodes in the frozen forest")
    return result


def root_box(word):
    return tuple((0, 0 if i == 0 or i >= len(word) else 32000-32*word[-1]) for i in range(6))


def children_boxes(word, box, node):
    lo, hi = map(list, zip(*box))
    for i in range(1, len(word)):
        lo[i] = max(lo[i], lo[i-1] + 32 * word[i-1])
    for i in reversed(range(len(word)-1)):
        hi[i] = min(hi[i], hi[i+1] - 32 * word[i])
    mid, k = node.cut, node.axis
    if not lo[k] <= mid <= hi[k]:
        raise ValueError("Cut outside narrowed parent")
    lh, rl = hi.copy(), lo.copy()
    lh[k], rl[k] = mid, mid
    return tuple(zip(lo, lh)), tuple(zip(rl, hi))


def show_box(box):
    return "endpointsBox " + " ".join(f"({lo},{hi})" for lo,hi in box)


class SplitProof:
    def __init__(self, word, box, tree, name, limit):
        self.word, self.box, self.tree, self.name = word, box, tree, name
        self.children = []
        if tree.size > limit:
            left, right = children_boxes(word, box, tree)
            self.children = [
                SplitProof(word, left, tree.left, name + "L", limit),
                SplitProof(word, right, tree.right, name + "R", limit),
            ]

    def pre(self):
        yield self
        for c in self.children:
            yield from c.pre()

    def post(self):
        for c in self.children:
            yield from c.post()
        yield self


def header(imports):
    return [*(f"import {m}" for m in imports), "",
            "/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/",
            "namespace GaussianChains.Point22.Atlas", "open GaussianChains.Cert",
            "", "set_option maxRecDepth 200000", "set_option maxHeartbeats 0", ""]


def definitions(lines, p, enum, initial):
    if initial:
        lines.extend([f"def {p.name}Box := rootBox .{enum}",
                      f"def {p.name}Tree := tree .{enum}", ""])
    for parent in p.pre():
        for child, side in zip(parent.children, ("left", "right")):
            lines.extend([f"def {child.name}Box := {show_box(child.box)}",
                          f"def {child.name}Tree := {side}Subtree {parent.name}Tree", ""])


def proof(lines, p, enum, alias=None):
    result = alias or p.name + "OK"
    lines.append(f"theorem {result} : replay .{enum} (wordBounds .{enum}) {p.name}Box {p.name}Tree = true := by")
    if not p.children:
        lines.append("  decide +kernel")
    else:
        l,r = p.children
        lines.extend([f"  exact replay_join_checked .{enum} {p.name}Box {l.name}Box {r.name}Box {p.name}Tree",
                      f"    (by decide +kernel) {l.name}OK {r.name}OK"])
    lines.append("")


def generate():
    trees = parse_trees()
    parts = header(["Point22AtlasWordJoin", "Point22AtlasAcceptance"])
    parts += ["abbrev wordBounds (w : Word) := boundsFrom checkedLookup internalTicks witnessTicks w", ""]
    files = {}
    tops = {}
    last_page = {}
    small_predecessor = JOINS
    for tag, enum in WORDS.items():
        if tag in {"6", "33"}:
            continue
        w = tuple(map(int, tag))
        top = SplitProof(w, root_box(w), trees[tag], "w"+tag, 300)
        tops[tag] = top
        definitions(parts, top, enum, True)
        for j, tip in enumerate(p for p in top.pre() if not p.children):
            # The linear data size and memory budget of each module are bounded.
            module = f"Point22AtlasWord{tag}Page{j}"
            last_page[tag] = module
            chunk = SplitProof(w, tip.box, tip.tree, tip.name, 13)
            # A fresh Lake build replays this word one page at a time. Different
            # words remain independent, keeping the kernel's memory use bounded.
            predecessor = JOINS if j == 0 else f"Point22AtlasWord{tag}Page{j-1}"
            if trees[tag].size <= 25:
                predecessor, small_predecessor = small_predecessor, module
            lines = header([predecessor])
            definitions(lines, chunk, enum, False)
            for p in chunk.post():
                proof(lines, p, enum)
            files[module] = lines
    files[JOINS] = parts
    final_imports = [small_predecessor]
    for tag, top in tops.items():
        if top.children:
            module = f"Point22AtlasWord{tag}"
            joins = header([last_page[tag]])
            for p in top.post():
                if p.children:
                    proof(joins, p, WORDS[tag])
            joins += [f"theorem word{tag}_accept : atlasAccept .{WORDS[tag]} = true := {top.name}OK", ""]
            files[module] = joins
            final_imports.append(module)
    final = header(final_imports)
    final.extend(["theorem all_words_accept (w : Word) : atlasAccept w = true := by",
                  "  cases w with"])
    for tag, enum in WORDS.items():
        thm = {"6":"six_block_accept", "33":"two_triples_accept"}.get(tag, "w"+tag+"OK")
        final.append(f"  | {enum} => exact {thm}")
    final.extend(["", "#print axioms all_words_accept"])
    files["Point22AtlasWords"] = final
    return {name + ".lean": "\n".join(lines+["","end GaussianChains.Point22.Atlas",""])
            for name,lines in files.items()}


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    flags = cli.add_mutually_exclusive_group(required=True)
    flags.add_argument("--check", action="store_true")
    flags.add_argument("--write", action="store_true")
    args = cli.parse_args()
    for name, content in generate().items():
        path = HERE / name
        if args.write and (not path.is_file() or path.read_text(encoding="utf-8") != content):
            path.write_text(content, encoding="utf-8")
        elif not path.is_file() or path.read_text(encoding="utf-8") != content:
            raise SystemExit(f"Regeneration differs for {name}")
    print("Width-22 shards cover all 5638 nodes in the original twelve trees.")
