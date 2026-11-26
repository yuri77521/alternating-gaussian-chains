"""Counterexample search on the six-site slack supports for 8 <= s <= 9."""

import argparse
import itertools
import math
import random
from fractions import Fraction
from functools import lru_cache

from verify_exact_clusters import canonical, certified_energy, modes, positions
from verify_stability import exponential_bounds


N = 6
COARSE = 16
DENOM = 2**20
PACKED_DENOM = 2**40
WEIGHTS, _ = modes(math.exp(-math.pi**2 / 9), N)
FLOORS = (
    ".000001", ".001", ".01", ".03", ".06", ".09", ".1", ".12", ".125",
    ".1270778", ".127078", ".128", ".1296619", ".1296622", ".135", ".15",
    ".16", ".166", ".16665",
)


def packed_reference(h, weights=WEIGHTS):
    """Rational trial picked via the packed-edge derivative; either endpoint is exact."""
    floor = float(h)
    limit = 0.5 - 3 * floor
    coeffs = [(-1)**(n+1) * n * a * (2 * math.cos(math.tau*n*floor) - 1)**2
              for n, a in enumerate(weights, 1)]

    def derivative(t):
        z = math.cos(math.tau*t)
        prev, value = 0.0, 1.0
        result = 0.0
        for coefficient in coeffs:
            result += coefficient*value
            prev, value = value, 2*z*value - prev
        return result

    if h <= Fraction(1, 8) or derivative(0) >= 0:
        part = PACKED_DENOM // 2
    elif derivative(limit) <= 0:
        part = PACKED_DENOM
    else:
        left, right = 0.0, limit
        for _ in range(52):
            mid = (left + right) / 2
            if derivative(mid) < 0:
                left = mid
            else:
                right = mid
        part = round(PACKED_DENOM * (0.5 + (left+right)/(4*limit)))
    return (part, 0, 0, PACKED_DENOM-part, 0, 0)


def positive_rows(support, denominator):
    """All ordered positive allocations of denominator to this exact support."""
    for cuts in itertools.combinations(range(1, denominator), len(support)-1):
        row = [0] * N
        for i, a, b in zip(support, (0, *cuts), (*cuts, denominator)):
            row[i] = b-a
        yield tuple(row)


def make_score(floor, weights=WEIGHTS):
    """The variable pair contribution to the energy, in positive Fourier units."""
    slack = 1 - N*floor

    @lru_cache(maxsize=None)
    def kernel(k, units):
        angle = math.tau * (k*floor + slack*units/DENOM)
        return sum(w*math.cos(n*angle) for n, w in enumerate(weights, 1))

    def score(row):
        a, b, c, d, e, f = row
        return (sum(kernel(1, i) for i in row)
                - sum(kernel(2, i) for i in (a+b, b+c, c+d, d+e, e+f, f+a))
                + sum(kernel(3, i) for i in (a+b+c, b+c+d, c+d+e)))

    return score


def descend(score, start, support, lower):
    """Transfer between two selected gaps; decrease by powers of four down to one unit."""
    row = start
    value = score(row)
    step = DENOM // COARSE
    while step:
        for _ in range(128):
            best_value = value
            best = row
            for i in support:
                amount = min(step, row[i] - lower)
                if not amount:
                    continue
                shifted = list(row)
                shifted[i] -= amount
                for j in support:
                    if i == j:
                        continue
                    shifted[j] += amount
                    trial_value = score(shifted)
                    if trial_value < best_value:
                        best_value, best = trial_value, tuple(shifted)
                    shifted[j] -= amount
            if best == row:
                break
            value, row = best_value, best
        step //= 4
    return value, row


def packed(row):
    return any(row[i] + row[i+3] == sum(row) for i in range(3))


def image_energy(h, row, width=9):
    total = sum(row)
    gaps = [h + (1-N*h)*Fraction(i, total) for i in row]
    assert sum(gaps) == 1 and min(gaps) >= h
    return certified_energy(positions(gaps), width, radius=4)


def search(h, detail, width=9):
    assert 0 < h < Fraction(1, 6)
    weights, _ = modes(math.exp(-math.pi**2 / float(width)), N)
    score = make_score(float(h), weights)
    rng = random.Random(9016)
    reference = packed_reference(h, weights)
    reference_lo, reference_hi = image_energy(h, reference, width)
    centered_lo, centered_hi = image_energy(h, (1, 0, 0, 1, 0, 0), width)
    closest = None
    ahead_of_center = 0
    closed_nonpacked = set()
    finalists = set()
    face_count = searches = 0
    for mask in itertools.product(range(2), repeat=N):
        if not any(mask) or mask != canonical(mask):
            continue
        face_count += 1
        support = tuple(i for i, active in enumerate(mask) if active)
        rows = [tuple(u*(DENOM//COARSE) for u in r)
                for r in positive_rows(support, COARSE)]
        seeds = {min(rows, key=score), min(rows, key=lambda r: sum(v*v for v in r))}
        seeds.update(rng.sample(rows, min(3, len(rows))))
        for lower in (0, 1):
            outcomes = [descend(score, row, support, lower) for row in sorted(seeds)]
            searches += len(outcomes)
            for _, row in outcomes:
                assert sum(row) == DENOM and min(row) >= 0
                assert all(row[i] >= lower for i in support)
                if not packed(row):
                    row = canonical(row)
                    finalists.add(row)
                    if lower == 0:
                        closed_nonpacked.add(row)
    assert face_count == 12
    for row in sorted(finalists):
        lo, hi = image_energy(h, row, width)
        gap = lo-reference_hi, hi-reference_lo
        ahead_of_center += hi < centered_lo
        if closest is None or gap < closest[:2]:
            closest = *gap, row
        if gap[0] <= 0:
            raise ArithmeticError(f"Investigate h={h}, surplus={row}/{DENOM}, "
                                  f"trial={reference}/{PACKED_DENOM}, E difference={gap}")
    lo, hi, row = closest
    scale = 10**22
    print(f"h={str(h):>13} runs={searches} outside={len(finalists)} "
          f"closed_outside={len(closed_nonpacked)} "
          f"min_delta=[{math.floor(lo*scale)},{math.ceil(hi*scale)}]e-22 "
          f"surplus={row} ahead_of_center={ahead_of_center}", flush=True)
    if detail:
        print(f"  packed reference={reference}/{PACKED_DENOM}")
        for closed_row in sorted(closed_nonpacked):
            other_lo, other_hi = image_energy(h, closed_row, width)
            print(f"  closed-face off-edge endpoint {closed_row}, excess in units of 1e-22:",
                  math.floor((other_lo-reference_hi)*scale), math.ceil((other_hi-reference_lo)*scale))
        winner_lo, winner_hi = image_energy(h, row, width)
        print("  closest minus centered in units of 1e-22:",
              math.floor((winner_lo-centered_hi)*scale), math.ceil((winner_hi-centered_lo)*scale))
    if h <= Fraction(1, 16):
        # Continue the s=22 example from verify_exact_clusters to the current floor.
        eighth = Fraction(1, 8)
        sites = [0, eighth, eighth+h, 2*eighth, 4*eighth, 6*eighth]
        assert min(b-a for a, b in zip(sites, sites[1:]+[1])) >= h
        rival_lo, rival_hi = certified_energy(sites, width, radius=4)
        if rival_lo <= reference_hi:
            raise ArithmeticError(f"Investigate continued s=22 example at h={h}")
        if detail:
            print("  continued s=22 example minus trial in units of 1e-22:",
                  math.floor((rival_lo-reference_hi)*scale), math.ceil((rival_hi-reference_lo)*scale))
    exponential_bounds.cache_clear()
    return searches, len(finalists)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--width", type=Fraction, default=9, help="rational Gaussian width in [8,9]")
    parser.add_argument("--h", nargs="+", default=FLOORS, help="rational gap floors")
    parser.add_argument("--detail", action="store_true", help="also show closed-face endpoints")
    args = parser.parse_args()
    if not 8 <= args.width <= 9:
        parser.error("--width must be in [8,9]")
    runs = outside = 0
    for value in args.h:
        count, unique = search(Fraction(value), args.detail, args.width)
        runs += count
        outside += unique
    print(f"Total searches={runs}, distinct off-edge endpoints checked across floors={outside}")


if __name__ == "__main__":
    main()
