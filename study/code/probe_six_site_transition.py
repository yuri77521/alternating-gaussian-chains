"""Six-site alpha=8 finite rational meshes and continuous face searches (stdlib)."""

import argparse
import itertools
import math
import random
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache

from verify_exact_clusters import canonical, certified_energy, kernel_derivative, modes, positions
from verify_stability import add_scaled, exponential_bounds


GAPS = (".10", ".115", ".125", ".13", ".131", ".13114", ".131146", ".1311468", ".13115", ".132")
Q = math.exp(-math.pi**2 / 8)
WEIGHTS, SCORE_TAIL = modes(Q, 6)
ENERGY_FACTOR = math.sqrt(math.pi / 8) * Q / 3
SEED = 20261126
SCALE = 10**24


def mesh_orbits(mesh):
    """Ordered nonnegative integer allocations modulo cyclic shifts and reversal."""
    rows = []
    for cuts in itertools.combinations(range(1, mesh + 6), 5):
        a, b, c, d, e = cuts
        row = (a - 1, b - a - 1, c - b - 1, d - c - 1, e - d - 1, mesh + 5 - e)
        if row[0] == min(row) and row == canonical(row):
            rows.append(row)
    return rows


@lru_cache(maxsize=None)
def kernel(t, exponent=8):
    """Outward integer bounds, in units of 10^-24, for the image kernel."""
    assert exponent in (8, 9)
    if t > F(1, 2):
        return kernel(1 - t, exponent)
    assert 0 <= t <= 1
    values = [exponential_bounds(exponent * (t + k)**2) for k in range(-3, 4)]
    tail = F(2, 2**(9*exponent)) / (1 - F(1, 2**(7*exponent)))
    return math.floor(sum(v[0] for v in values) * SCALE), math.ceil((sum(v[1] for v in values) + tail) * SCALE)


def energy_tables(mesh, h, exponent=8):
    step = (1 - 6 * h) / mesh
    return [[kernel(k * h + j * step, exponent) for j in range(mesh + 1)] for k in (1, 2, 3)]


def mesh_bounds(mesh, h, exponent=8):
    one, two, three = energy_tables(mesh, h, exponent)
    def bounds(row):
        a, b, c, d, e, f = row
        positive = [one[i] for i in row]
        positive.extend((three[a+b+c], three[b+c+d], three[c+d+e]))
        negative = [two[i] for i in (a+b, b+c, c+d, d+e, e+f, f+a)]
        lo = sum(v[0] for v in positive) - sum(v[1] for v in negative)
        hi = sum(v[1] for v in positive) - sum(v[0] for v in negative)
        return lo, hi
    return bounds


def mesh_comparison(mesh, rows, h):
    bounds = mesh_bounds(mesh, h)
    base = canonical((mesh // 2, 0, 0, mesh // 2, 0, 0))
    base_lo, base_hi = bounds(base)
    champion = None
    lower_bounds = {}
    losing = ahead = unresolved = 0
    for row in rows:
        if row == base:
            continue
        lo, hi = bounds(row)
        lo, hi = lo - base_hi, hi - base_lo
        ahead += hi < 0
        losing += lo > 0
        unresolved += lo <= 0 <= hi
        support = sum(x > 0 for x in row)
        lower_bounds[support] = min(lower_bounds.get(support, lo), lo)
        if champion is None or lo < champion[0]:
            champion = (lo, hi, row)
    assert ahead + losing + unresolved == len(rows) - 1
    lo, hi, row = champion
    print(f"mesh h={float(h):.7f} higher={losing} lower={ahead} unresolved={unresolved} "
          f"least interval=[{lo/(3*SCALE):+.10e},{hi/(3*SCALE):+.10e}] row={row} "
          f"3+free lower={min(x for n,x in lower_bounds.items() if n >= 3)/(3*SCALE):+.7e}")


@lru_cache(maxsize=None)
def first_derivative(t):
    """Rational image enclosure of G'(t) on [0,1]."""
    assert 0 <= t <= 1
    if t > F(1, 2):
        lo, hi = first_derivative(1 - t)
        return -hi, -lo
    result = (F(0), F(0))
    for k in range(-3, 4):
        result = add_scaled(result, -16*(t+k), exponential_bounds(8*(t+k)**2))
    tail = F(320, 2**72)
    return result[0]-tail, result[1]+tail


def band_proof(mesh, rows, left, right, bands):
    """Certify reduction to the packed-triple edge throughout a given h interval."""
    assert kernel_derivative(F(0), 8, 2)[0] > -16
    width = (right-left)/bands
    edge_rows = {canonical((0,0,i,0,0,mesh-i)) for i in range(mesh//2+1)}
    base = canonical((0,0,mesh//2,0,0,mesh//2))
    outside = [row for row in rows if row not in edge_rows]
    edge = [(0,0,j,0,0,mesh-j) for j in range(mesh//2+1)]

    def endpoint(h):
        bounds = mesh_bounds(mesh, h)
        hi = bounds(base)[1]
        gap = F(min(bounds(row)[0] for row in outside)-hi, 3*SCALE)
        return gap, [F(bounds(row)[0]-hi,3*SCALE) for row in edge]

    prev, prev_edge = endpoint(left)
    min_exclusion = min_gradient = None
    for k in range(bands):
        h0 = left + k*width
        h1 = h0 + width
        nxt, nxt_edge = endpoint(h1)
        delta = (1-6*h0)/mesh
        # 105 is the maximum sum of squared velocity differences;
        # 24 is the sum on the centered comparison configuration.
        loss = F(16*(105+24),3)*width**2/8 + 10*delta**2
        gap = min(prev,nxt) - loss
        min_exclusion = gap if min_exclusion is None else min(gap,min_exclusion)
        assert gap > 0, (float(h0), "grid exclusion", float(gap))
        mid = (h0+h1)/2
        for row, e0, e1 in zip(edge, prev_edge, nxt_edge):
            if min(e0,e1) > loss:
                continue
            sites = positions([mid + (1-6*mid)*F(r,mesh) for r in row])
            velocity = positions([1-6*F(r,mesh) for r in row])
            for i in (0,1,3,4):
                lower = F(0)
                for u in range(i+1):
                    for v in range(i+1,6):
                        t = sites[v]-sites[u]
                        coeff = F(-(-1)**(v-u),3)
                        # All cross-pair distances increase along release g_i at fixed origin.
                        lower += add_scaled((0,0),coeff,first_derivative(t))[0]
                        lower -= F(16,3) * (delta + abs(velocity[v]-velocity[u])*width/2)
                min_gradient = lower if min_gradient is None else min(lower,min_gradient)
                assert lower > 0, (float(h0), f"gradient {i} at {row}", float(lower))
        prev, prev_edge = nxt, nxt_edge
    print(f"continuous-domain certificate [{left},{right}], M={mesh}, bands={bands}, "
          f"exclusion > {math.floor(min_exclusion*10**9)}e-9, "
          f"release > {math.floor(min_gradient*10**9)}e-9", flush=True)


def score_gradient(h, surplus):
    """Normalized charge score and derivatives with respect to slack fractions."""
    slack = 1 - 6*h
    x = positions([h + slack*t for t in surplus])
    phases = [complex(math.cos(math.tau*y), math.sin(math.tau*y)) for y in x]
    powers = [(-1)**i for i in range(6)]
    grad = [0.] * 6
    score = 0.
    for n, w in enumerate(WEIGHTS, 1):
        powers = [p*z for p,z in zip(powers, phases)]
        total = sum(powers)
        score += w * abs(total)**2
        for i, z in enumerate(powers):
            grad[i] -= 2 * math.tau*n*w * (z * total.conjugate()).imag
    acc = 0.
    for i in reversed(range(6)):
        grad[i], acc = slack*acc, acc + grad[i]
    return score, grad


def project(y, support):
    """Euclidean projection to the closed unit simplex on a specified support."""
    sorted_values = sorted((y[i] for i in support), reverse=True)
    running = 0.
    for j, v in enumerate(sorted_values, 1):
        running += v
        shift = (running - 1)/j
        if j == len(support) or sorted_values[j] <= shift:
            break
    projected = [max(0., y[i] - shift) if i in support else 0. for i in range(6)]
    # A large spectral step can lose precision in y[i]-shift.
    largest = max(support, key=projected.__getitem__)
    projected[largest] += 1. - math.fsum(projected)
    return projected


def ascend(h, start, support):
    """Projected gradient ascent, Armijo backtracking, safeguarded spectral steps."""
    y = start
    val, grad = score_gradient(h, y)
    step = 1.
    for _ in range(220):
        for _ in range(32):
            nxt = project([a + step*b for a,b in zip(y, grad)], support)
            dy = [b-a for a,b in zip(y, nxt)]
            if max(map(abs, dy)) < 1e-12:
                return val, y
            test, grad2 = score_gradient(h, nxt)
            if test >= val + .0001 * sum(a*b for a,b in zip(grad, dy)) - 2e-15:
                break
            step *= .5
        else:
            return val, y
        curvature = sum(a*(b-c) for a,b,c in zip(dy, grad, grad2))
        step = min(1e5, max(1e-4, sum(a*a for a in dy)/curvature)) if curvature > 1e-20 else min(1e5, 2*step)
        y, val, grad = nxt, test, grad2
    return val, y


def continuous(h, starts):
    rng = random.Random(SEED)
    base, _ = score_gradient(h, [.5,0,0,.5,0,0])
    best = None
    count = 0
    # Force all topological types, including adjacent, distance-two and opposite slack gaps.
    for mask in itertools.product((0,1), repeat=6):
        if not any(mask) or mask != canonical(mask):
            continue
        support = [i for i in range(6) if mask[i]]
        for j in range(1 if len(support) == 1 else starts):
            if j == 0:
                seed = list(mask)
            else:
                seed = [rng.expovariate(1.)**(1 + j % 3) if t else 0. for t in mask]
            seed_sum = sum(seed)
            val, y = ascend(h, [t/seed_sum for t in seed], support)
            count += 1
            if best is None or val > best[0]:
                best = val, y
    val, y = best
    print(f"float h={h:.7f} starts={count} min E-E(3+3)={-(val-base)*ENERGY_FACTOR:+.10e} "
          f"slack={tuple(round(x,7) for x in y)}")


def offcenter_certificate():
    h, d = F(2623, 20000), F(1, 1000)
    half = F(1, 2)
    base = [0, h, 2*h, half, half+h, half+2*h]
    other = base[:3] + [x+d for x in base[3:]]
    assert all(min(b-a for a,b in zip(x, x[1:]+[1])) >= h for x in (base, other))
    left, right = certified_energy(base, 8), certified_energy(other, 8)
    lo, hi = left[0]-right[1], left[1]-right[0]
    assert 0 < lo <= hi
    print(f"rational certificate h={h}, d={d}, E(centered)-E(shifted) "
          f"in [{math.floor(lo*10**18)}, {math.ceil(hi*10**18)}] * 10^-18")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mesh", type=int, default=24, help="even number of slack units")
    parser.add_argument("--starts", type=int, default=12)
    parser.add_argument("--h", nargs="+", default=GAPS)
    parser.add_argument("--band", nargs=3, metavar=("LEFT","RIGHT","COUNT"),
                        help="instead certify the full continuum in this h interval")
    args = parser.parse_args()
    assert args.mesh >= 6 and args.mesh % 2 == 0 and args.starts >= 1
    rows = mesh_orbits(args.mesh)
    print(f"mesh={args.mesh}, ordered={math.comb(args.mesh+5,5)}, orbits={len(rows)}, "
          f"orbits by #free={dict(sorted(Counter(sum(i>0 for i in x) for x in rows).items()))}")
    if args.band:
        left, right, n = args.band
        assert 0 < F(left) < F(right) < F(1,6) and int(n) >= 1
        band_proof(args.mesh, rows, F(left), F(right), int(n))
        return
    for value in args.h:
        h = F(value)
        assert 0 < h < F(1,6)
        mesh_comparison(args.mesh, rows, h)
        continuous(float(h), args.starts)
    offcenter_certificate()


if __name__ == "__main__":
    main()
