"""Checks for exact small-gap clusters. Run with standard-library Python 3.9+."""

import cmath
import itertools
import math
import random
from fractions import Fraction

from verify_gaussian_infimum import balanced_trial, image_energy
from verify_stability import add_scaled, exponential_bounds


def widths(q):
    s = -math.pi**2 / math.log(q)
    return s, math.sqrt(math.pi / s)


def modes(q, count):
    """Coefficients for U = N(1-E)/(2cq), with an explicit absolute tail."""
    weights = []
    while True:
        n = len(weights) + 1
        tail = count**2 * q ** (n * n - 1) / (1 - q ** (2 * n + 1))
        if tail < 1e-18:
            return weights, tail
        weights.append(q ** (n * n - 1))


def score(sites, weights):
    phases = [cmath.exp(1j * math.tau * x) for x in sites]
    powers = [(-1) ** i for i in range(len(sites))]
    total = 0.0
    for weight in weights:
        for j, phase in enumerate(phases):
            powers[j] *= phase
        total += weight * abs(sum(powers)) ** 2
    return total


def compare_sums(sites, q):
    """Compare the image sum of directed interactions with the charge Fourier sum."""
    count = len(sites)
    weights, fourier_tail = modes(q, count)
    s, c = widths(q)
    radius = 1 + math.ceil(math.sqrt(50 / s))  # image_energy uses this radius for L=1.
    image_tail = 2 * count * math.exp(-s * radius**2) / (1 - math.exp(-s * (2 * radius + 1)))
    fourier = 1 - 2 * c * q * score(sites, weights) / count
    direct = image_energy(sites, 1.0, s)
    assert image_tail < 1e-18 and 2 * c * q * fourier_tail / count < 1e-18
    assert abs(direct - fourier) < 3e-13, (direct, fourier)
    return abs(direct - fourier)


def positions(gaps):
    return [0, *itertools.accumulate(gaps[:-1])]


def canonical(gaps):
    return min(g[i:] + g[:i] for g in (gaps, gaps[::-1]) for i in range(len(g)))


def balanced_gaps(count, mesh, floor):
    small = 2 * ((count // 2 - 1) // 2) + 1
    outer = (mesh - (count - 2) * floor) // 2
    assert 2 * outer + (count - 2) * floor == mesh
    return canonical((floor,) * (small - 1) + (outer,) + (floor,) * (count - small - 1) + (outer,))


def grid_search(count, mesh, floor, qs):
    """Every fixed-origin cyclic gap vector on the grid, with symmetry reduction."""
    slack = mesh - count * floor
    pairs = [(i, j, (-1) ** (i + j)) for i in range(count) for j in range(i)]
    widths_s = [widths(q)[0] for q in qs]
    kernels = []
    for s in widths_s:
        r = 1 + math.ceil(math.sqrt(50 / s))
        kernels.append(
            [
                math.fsum(math.exp(-s * (j / mesh + k) ** 2) for k in range(-r, r + 1))
                for j in range(mesh)
            ]
        )

    def energies(gaps):
        x = positions(gaps)
        return [
            1 - g[0] - 2 / count * math.fsum(sign * g[x[i] - x[j]] for i, j, sign in pairs)
            for g in kernels
        ]

    trial = balanced_gaps(count, mesh, floor)
    trial_energy = energies(trial)
    best_other = [(math.inf, ()) for q in qs]
    ordered = representatives = 0
    for cuts in itertools.combinations(range(1, slack + count), count - 1):
        gaps = tuple(floor + b - a - 1 for a, b in zip((0,) + cuts, cuts + (slack + count,)))
        ordered += 1
        if gaps[0] != min(gaps) or gaps != canonical(gaps):
            continue
        representatives += 1
        if gaps == trial:
            continue
        for j, energy in enumerate(energies(gaps)):
            best_other[j] = min(best_other[j], (energy, gaps))
    assert ordered == math.comb(slack + count - 1, count - 1)
    print(f"grid N={count} mesh={mesh} floor={floor} words={ordered} orbits={representatives}")
    for q, base, (other, gaps) in zip(qs, trial_energy, best_other):
        for word, ref in ((trial, base), (gaps, other)):
            coords = [j / mesh for j in positions(word)]
            compare_sums(coords, q)
            assert abs(image_energy(coords, 1.0, widths(q)[0]) - ref) < 3e-13
        print(
            f"  q={q:.6f} E(packed)={base:.12f} best other - packed={other-base:+.8e} other={gaps}"
        )
        if count * floor / mesh <= 0.5:
            assert other - base > 3e-13, (q, mesh, gaps)
    return ordered


def cluster_cell(first, second, displacement):
    """Specify internal gaps and signed-centroid displacement relative to antipodes."""
    a = [0.0, *itertools.accumulate(first)]
    b = [0.0, *itertools.accumulate(second)]
    shift = 0.5 + displacement + math.fsum(a[::2]) - math.fsum(a[1::2])
    shift -= math.fsum(b[::2]) - math.fsum(b[1::2])
    return a + [shift + y for y in b]


def competitors(count, h, rng):
    # Include all odd splits. Move centers, release individual gaps and couple releases.
    for a_count in range(1, count // 2 + 1, 2):
        a = a_count - 1
        b = count - a_count - 1
        for shift in (-0.19, -0.013 * h, 0.0, 0.013 * h, 0.37 * h, 0.19):
            yield cluster_cell([h] * a, [h] * b, shift)
        for index in range(a + b):
            for factor in (0.0037, 0.29, 1.7):
                g = [h] * (a + b)
                g[index] += factor * h
                for shift in (-0.21 * h, 0.0, 0.21 * h):
                    yield cluster_cell(g[:a], g[a:], shift)
        for _ in range(80):
            g = [h * (1 + rng.random() ** 3) for i in range(a + b)]
            yield cluster_cell(g[:a], g[a:], h * rng.uniform(-0.7, 0.7))
    # Search the whole continuous gap simplex with dense, sparse, and single-slack draws.
    slack = 1 - count * h
    for j in range(240):
        size = 1 + j % count
        gaps = [h] * count
        indices = rng.sample(range(count), size)
        excess = [rng.expovariate(1.0) for i in indices]
        total_excess = sum(excess)
        for index, value in zip(indices, excess):
            gaps[index] += slack * value / total_excess
        yield positions(gaps)


def continuous_checks(qs):
    rng = random.Random(20261126)
    print("off-grid: closest geometrically distinct sampled competitor, in U units")
    total = 0
    largest_discrepancy = 0.0
    for count in (4, 6, 8, 10, 12):
        for filling in (0.0061, 0.0713, 0.3137):
            h = filling / count
            sites = balanced_trial(count, 1.0, h)
            weights = [modes(q, count)[0] for q in qs]
            base = [score(sites, ws) for ws in weights]
            best = [(-math.inf, []) for q in qs]
            words = 0
            for x in competitors(count, h, rng):
                gaps = [b - a for a, b in zip(x, x[1:] + [1.0])]
                if min(gaps) < h - 2e-15:
                    continue
                # The constructed unshifted balanced trial occurs once in each search.
                if max(abs(t - u) for t, u in zip(sites, x)) < 2e-14:
                    continue
                words += 1
                for j, ws in enumerate(weights):
                    candidate = score(x, ws)
                    if candidate > best[j][0]:
                        best[j] = candidate, x
            margin = []
            for q, trial, (candidate, x) in zip(qs, base, best):
                largest_discrepancy = max(
                    largest_discrepancy, compare_sums(sites, q), compare_sums(x, q)
                )
                margin.append(trial - candidate)
            assert min(margin) > 2e-13, (count, h, margin)
            total += words
            print(
                f"  N={count:2} Nh={filling:.4f} candidates={words:4} margins="
                + " ".join(f"{value:.3e}" for value in margin)
            )
    print(f"{total} off-grid candidate cells, {total*len(qs)} comparisons")
    print(
        f"largest independent energy discrepancy among off-grid finalists: {largest_discrepancy:.3e}"
    )


def certified_energy(sites, s, radius=3):
    """Rational image-energy bounds for sites in a unit cell and rational s >= 1."""
    s = Fraction(s)
    sites = tuple(map(Fraction, sites))
    if s < 1 or not isinstance(radius, int) or radius < 0:
        raise ValueError("expected width >= 1 and a nonnegative integer image radius")
    if not sites or max(sites) - min(sites) > 1:
        raise ValueError("the sites must lie in an interval of length one")
    n = len(sites)
    bounds = (Fraction(1), Fraction(1))
    for i, x in enumerate(sites):
        for j, y in enumerate(sites):
            sign = Fraction(-((-1) ** (i + j)), n)
            for k in range(-radius, radius + 1):
                bounds = add_scaled(bounds, sign, exponential_bounds(s * (x - y + k) ** 2))
    # |x-y|<=1, so the first omitted distance is at least radius.
    # Flooring both powers enlarges the dyadic majorant at noninteger widths.
    first_power = math.floor(s * radius**2)
    ratio_power = math.floor(s * (2 * radius + 1))
    tail = Fraction(2 * n, 2 ** first_power) / (1 - Fraction(1, 2 ** ratio_power))
    return bounds[0] - tail, bounds[1] + tail


def kernel_derivative(center, s, order):
    """Enclose the second or fourth L=1 derivative at 0 or 1/2."""
    assert center in (0, Fraction(1, 2)) and s >= 8 and order in (2, 4)
    bounds = (Fraction(0), Fraction(0))
    for k in range(-5, 6):
        t = center + k
        coefficient = (
            4 * s**2 * t**2 - 2 * s
            if order == 2
            else 16 * s**4 * t**4 - 48 * s**3 * t**2 + 12 * s**2
        )
        bounds = add_scaled(bounds, coefficient, exponential_bounds(s * t * t))
    # Both derivative polynomials are bounded by C (j+1)^4 for |k|=j>=6.
    # The majorant's successive ratios are <= (8/7)^4 * 2^(-11s) < 1/2.
    c = 16 * s**4 + 48 * s**3 + 12 * s**2
    tail = Fraction(4 * c * 7**4, 2 ** (25 * s))
    return bounds[0] - tail, bounds[1] + tail


def tiny_spacing():
    """N=6; L=1 after scaling. This s also corresponds to L=6, alpha=1/4."""
    s, n, h = 9, 6, Fraction(1, 10**6)
    half = Fraction(1, 2)
    a = [0, h, 2 * h, half, half + h, half + 2 * h]
    # pi < 22/7 gives a rational lower bound on the sufficient threshold.
    pi_upper = Fraction(22, 7)
    assert exponential_bounds(pi_upper**2 / s)[0] > Fraction(1, 3)
    assert exponential_bounds(Fraction(314, 100) ** 2 / s)[1] < Fraction(17, 50)
    assert 2 * pi_upper * h < 1 / (n * (1 + 3 * pi_upper * (n // 2) ** 2) ** 2)
    base = certified_energy(a, s, radius=5)
    for label, other in (
        ("center shifted by h/100", a[:3] + [x + h / 100 for x in a[3:]]),
        ("one internal gap released by h/100", [0, h + h / 100, 2 * h + h / 100] + a[3:]),
        ("unbalanced 1+5", [0] + [half + j * h for j in range(-2, 3)]),
    ):
        assert min(y - x for x, y in zip(other, other[1:] + [1])) >= h
        other_lo, other_hi = certified_energy(other, s, radius=5)
        lo, hi = other_lo - base[1], other_hi - base[0]
        assert lo > 0 and hi - lo < Fraction(1, 10**34)
        print(f"tiny h={h}, s={s}, {label}: E(other)-E(packed) = {float(lo):.9e}")

    # Compare the exact E(h)-I-A2*h^2 quotient to the predicted quartic
    # A4 = (7/18)(G^(4)(1/2)-G^(4)(0)) in physical L=1 units.
    dipole = certified_energy([0, 0, 0, half, half, half], s, radius=5)
    coefficients = []
    for order, factor in ((2, Fraction(2, 3)), (4, Fraction(7, 18))):
        right = kernel_derivative(half, s, order)
        left = kernel_derivative(0, s, order)
        coefficients.append((factor * (right[0] - left[1]), factor * (right[1] - left[0])))
    a2, a4 = coefficients
    quotient = (
        (base[0] - dipole[1] - a2[1] * h * h) / h**4,
        (base[1] - dipole[0] - a2[0] * h * h) / h**4,
    )
    assert max(abs(quotient[0] - a4[1]), abs(quotient[1] - a4[0])) < Fraction(1, 10**6)
    print(
        f"tiny s=9 q={math.exp(-math.pi**2/s):.12f}, "
        f"quartic quotient={float(quotient[0]):.9f}, prediction={float(a4[0]):.9f}"
    )


def counterexamples():
    for s, denominator, trial, competitor, lower in [
        (8, 20, (0, 3, 6, 10, 13, 16), (0, 3, 6, 9, 12, 15), "0.00129689"),
        (22, 1000, (0, 1, 2, 500, 501, 502), (0, 125, 126, 250, 500, 750), "0.00231609"),
    ]:
        a = [Fraction(x, denominator) for x in trial]
        b = [Fraction(x, denominator) for x in competitor]
        h = a[1] - a[0]
        assert all(min(y - x for x, y in zip(v, v[1:] + [1])) >= h for v in (a, b))
        for v in (a, b):
            compare_sums(list(map(float, v)), math.exp(-math.pi**2 / s))
        e, f = certified_energy(a, s), certified_energy(b, s)
        assert e[0] - f[1] > Fraction(lower)
        print(
            f"certified s={s}, h={h}, E(packed)={float(e[0]):.12f}, "
            f"E(other)={float(f[0]):.12f}, packed - other > {lower}"
        )


def main():
    qs = (0.05, 0.2, 1 / 3)
    print("Widths q =", qs)
    words = 0
    for case in (
        (6, 16, 1),
        (6, 24, 1),
        (6, 32, 1),
        (6, 30, 2),
        (6, 30, 3),
        (6, 30, 4),
        (6, 20, 3),
        (8, 20, 1),
        (8, 24, 2),
    ):
        words += grid_search(*case, qs)
    print(f"{words} ordered grid words before symmetry reduction")
    continuous_checks(qs)
    counterexamples()
    tiny_spacing()


if __name__ == "__main__":
    main()
