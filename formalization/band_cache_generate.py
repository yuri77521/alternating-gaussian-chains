"""Regenerate the packed candidates for the three frozen strip tables.

Run python band_cache_generate.py --check for a bytewise comparison with the
generated Lean sources. The target lake build +BandVerifiedCacheCertified
proves that the literals enclose the Gaussian and its derivatives throughout
each query. The integer checks cover every recurrence step and every spatial
grid row. Equalities over adjacent pages are joined in Lean.
"""
import argparse
from fractions import Fraction
from math import factorial
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT.parent / "study" / "code"))
from verify_six_site_global_reduction import GRID, UNIT, ceil_div, sampled_images, samples

SCALE = 10**32
PAGE = 32
ANCHORS = (Fraction(8), Fraction(33, 4), Fraction(35, 4))
CHECK_ONLY = False

def write_source(name, sections):
    path = ROOT / name
    data = "".join(sections).encode("utf8")
    if not path.exists() or path.read_bytes() != data:
        if CHECK_ONLY:
            raise SystemExit(f"Generated file changed: {path.name}")
        path.write_bytes(data)


def balanced(values, offset=0):
    if all(x == values[0] for x in values):
        return hex(values[0])
    mid = len(values) // 2
    left = balanced(values[:mid], offset)
    right = balanced(values[mid:], offset + mid)
    return f"(if p < {offset + mid} then {left} else {right})"


def packed_function(name, width, values):
    if not all(0 <= x < (1 << width) for x in values):
        raise ValueError(f"{name} word overflow")
    pages = [sum(x << (width * k) for k, x in enumerate(values[start:start + PAGE]))
             for start in range(0, len(values), PAGE)]
    return (f"private def {name}Pages (p : Nat) : Nat :=\n  {balanced(pages)}\n\n"
            f"def {name} (i : Nat) : Nat := wordAt {width} {PAGE} {name}Pages i\n\n")


def emit(anchor, s):
    code = ["import BandVerifiedCachePacking\n\n",
            f"namespace GaussianChains.Band.Fast.Anchor{anchor}\n\n"]
    low, high = samples(s)
    for j, cap in enumerate((4, 20, 150)):
        pad = ceil_div(cap * UNIT, 2 * GRID)
        words = []
        for l, h in zip(low[j], high[j], strict=True):
            l, h = l + pad, h - pad
            if h - l not in (3, 4):
                raise ArithmeticError("unexpected interval width")
            words.append(2 * (l + (1 << 35)) + (h - l - 3))
        code.append(packed_function(f"raw{j}", 37, words))
    code.append(f"end GaussianChains.Band.Fast.Anchor{anchor}\n")
    write_source(f"BandVerifiedCacheData{anchor}.lean", code)

    scale, nodes = sampled_images(s)
    if scale != SCALE:
        raise ValueError("unexpected recurrence scale")

    def seed(z):
        z /= GRID**2
        hi = sum((-z)**j / factorial(j) for j in range(5))
        return int(scale * (hi - z**4 / 24)), ceil_div(scale * hi, 1)

    ratio_lo, ratio_hi = seed(s)
    factor_lo, factor_hi = seed(2*s)
    ratios = []
    for n in range(4 * GRID + 1):
        ratios.append((ratio_lo, ratio_hi))
        ratio_lo = ratio_lo * factor_lo // scale
        ratio_hi = ceil_div(ratio_hi * factor_hi, scale)

    source = ["import BandVerifiedCachePacking\n\n",
              f"namespace GaussianChains.Band.Fast.Anchor{anchor}\n\n"]
    for name, vals in (("gaussLo", [p[0] for p in nodes]),
                       ("gaussDelta", [p[1] - p[0] for p in nodes]),
                       ("ratioLo", [p[0] for p in ratios]),
                       ("ratioDelta", [p[1] - p[0] for p in ratios])):
        source.append(packed_function(name, max(vals).bit_length(), vals))
    source.append(f"end GaussianChains.Band.Fast.Anchor{anchor}\n")
    write_source(f"BandVerifiedCacheSamples{anchor}.lean", source)


def test_tree(target, level, leaf_level, prefix, *, offset=0):
    """Join small opaque proofs. Parent nodes reuse child theorems."""
    lines = []
    for k in range(leaf_level, level + 1):
        for p in range(offset, offset + (1 << level), 1 << k):
            statement = f"runChecks ({target}) {k} {p} = true"
            if k == leaf_level:
                proof = "by decide +kernel"
            else:
                proof = (f"runChecks_join {prefix}_{k-1}_{p} "
                         f"{prefix}_{k-1}_{p + (1 << (k-1))}")
            lines.append(f"private theorem {prefix}_{k}_{p} : {statement} := {proof}\n")
    return "".join(lines)


def emit_sharded_checks(anchor):
    # Consecutive imports bound peak memory in a default Lake build. Each
    # row theorem only computes a 32-node page; coarser levels use proven pages.
    prefix = f"BandVerifiedCacheProof{anchor}"
    previous = "BandVerifiedCacheClaims"
    for part in range(8):
        tag = f"Anchor{anchor}Part{part}"
        code = [f"import {previous}\n\nnamespace GaussianChains.Band.Fast.{tag}\n\n",
                "set_option Elab.async false\nset_option maxRecDepth 100000\n",
                "set_option maxHeartbeats 0\n\n",
                test_tree(f"validatePage {anchor}", 7, 4, "rec", offset=part*128),
                f"theorem recurrence : runChecks (validatePage {anchor}) 7 {part*128} = true := "
                f"rec_7_{part*128}\n\n",
                test_tree(f"validateNode {anchor}", 10, 5, "grid", offset=part*1024),
                f"theorem nodes : runChecks (validateNode {anchor}) 10 {part*1024} = true := "
                f"grid_10_{part*1024}\n\nend GaussianChains.Band.Fast.{tag}\n"]
        previous = f"{prefix}Part{part}"
        write_source(f"{previous}.lean", code)

    code = [f"import {previous}\n\nnamespace GaussianChains.Band.Fast\n\n",
            "set_option Elab.async false\nset_option maxRecDepth 100000\n\n"]
    for name, target, start, field in (("rec", "validatePage", 7, "recurrence"),
                                        ("grid", "validateNode", 10, "nodes")):
        proofs = [f"Anchor{anchor}Part{i}.{field}" for i in range(8)]
        level = start
        while len(proofs) > 1:
            new = []
            for i in range(0, len(proofs), 2):
                p = i << level
                lemma = f"{name}_{level+1}_{p}"
                code.append(f"private theorem {lemma} : runChecks ({target} {anchor}) "
                            f"{level+1} {p} = true := runChecks_join {proofs[i]} {proofs[i+1]}\n")
                new.append(lemma)
            proofs, level = new, level+1
    code.extend([f"\ntheorem checkedAnchor{anchor} : Checked {anchor} where\n",
                 "  init := by decide +kernel\n  recurrence := rec_10_0\n",
                 "  grid := grid_13_0\n  last := by decide +kernel\n\n",
                 f"#print axioms checkedAnchor{anchor}\n\nend GaussianChains.Band.Fast\n"])
    write_source(f"{prefix}.lean", code)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="compare generated sources byte for byte without writing")
    CHECK_ONLY = parser.parse_args().check
    for anchor, s in enumerate(ANCHORS):
        emit(anchor, s)
        emit_sharded_checks(anchor)
    if CHECK_ONLY:
        print("Three strip anchors: every generated Lean input matches.")
