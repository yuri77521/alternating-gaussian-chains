"""Direct rational periodic-image audit at s=22, h=1/1000.

Check E(packed triples) - E(witness) > 0.002284370362225 for every feasible
center separation, with E=1-G(0)-W/3 and W the unordered signed pair sum.
No imports from the other six-site certificates are used.
"""

from fractions import Fraction
from functools import lru_cache


S = 22
H = Fraction(1, 1000)
UNIT = 10**15
TARGET = Fraction("0.002284370362225")
IMAGE_RADIUS = 2
WITNESS = (0, 125, 126, 250, 500, 750)


def ceil_fraction(x):
    return -((-x.numerator) // x.denominator)


@lru_cache(maxsize=None)
def exp_interval(z):
    """Integer endpoints in units of 1/UNIT for exp(-z), 0 <= z <= 198."""
    assert 0 <= z <= 198
    y = z / 256
    term = Fraction(1)
    value = term
    for k in range(1, 17):
        term = -term * y / k
        value += term
    # For 0 <= y <= 1, degree 17 is a lower and degree 16 an upper bound.
    lower = (value - term * y / 17) * UNIT
    lo = lower.numerator // lower.denominator
    hi = ceil_fraction(value * UNIT)
    assert 0 <= lo <= hi
    # Positive squaring eight times, rounding outward at every operation.
    for _ in range(8):
        lo = lo * lo // UNIT
        hi = (hi * hi + UNIT - 1) // UNIT
    return lo, hi


# At x in [0, 1], images |k| >= 3 obey |k+x| >= |k|-1. As e>2,
# their sum is < 2 sum_{m>=2} 2^(-22m^2). The first term has exponent
# 88 and the ratios are at most 2^(-110). Enlarge only the upper endpoint.
TAIL = ceil_fraction(UNIT * Fraction(2, 2**88) / (1 - Fraction(1, 2**110)))


@lru_cache(maxsize=None)
def kernel_box(left, right):
    """Enclose G(x)=sum_k exp(-22(x+k)^2) simultaneously for x in [left,right]."""
    assert 0 <= left <= right <= 1
    lower, upper = 0, TAIL
    for k in range(-IMAGE_RADIUS, IMAGE_RADIUS + 1):
        u, v = left + k, right + k
        near = 0 if u <= 0 <= v else min(abs(u), abs(v))
        far = max(abs(u), abs(v))
        lower += exp_interval(Fraction(S) * far**2)[0]
        upper += exp_interval(Fraction(S) * near**2)[1]
    return lower, upper


def weighted_sum(terms):
    """Enclose the signed weighted sum of intervals, still in units of 1/UNIT."""
    low = high = 0
    for weight, (lo, hi) in terms:
        if weight < 0:
            lo, hi = hi, lo
        low += weight * lo
        high += weight * hi
    return low, high


def witness_pair_sum():
    xs = [Fraction(p, 1000) for p in WITNESS]
    gaps = [b - a for a, b in zip(xs, xs[1:])] + [1 + xs[0] - xs[-1]]
    assert len(xs) == 6 and min(gaps) >= H and sum(gaps) == 1
    terms = []
    for i, p in enumerate(xs):
        for j in range(i + 1, len(xs)):
            d = xs[j] - p
            terms.append(((-1)**(i + j), kernel_box(d, d)))
    return weighted_sum(terms)


def packed_pair_sum(left, right):
    # Sites 0,h,2h,d,d+h,d+2h have internal score -4G(h)+2G(2h).
    # The other nine pairs have separations d+kh, k=-2,...,2.
    terms = [(-4, kernel_box(H, H)), (2, kernel_box(2 * H, 2 * H))]
    for k, weight in zip(range(-2, 3), (-1, 2, -3, 2, -1)):
        terms.append((weight, kernel_box(left + k * H, right + k * H)))
    return weighted_sum(terms)


def main():
    if not __debug__:
        raise RuntimeError("Run without -O so the certificate assertions are enabled")
    witness_lo, witness_hi = witness_pair_sum()
    g0_lo, g0_hi = kernel_box(Fraction(0), Fraction(0))
    # Feasible d=1/2+t ranges over [3h,1-3h]. G is even and periodic
    # and the five weights are symmetric, so d and 1-d have equal energy.
    initial = (3 * H, Fraction(1, 2))
    pending = [(*initial, 0)]
    accepted = 0
    visited = 0
    total_length = Fraction(0)
    min_margin = None
    max_depth = 0
    while pending:
        a, b, depth = pending.pop()
        visited += 1
        _, packed_hi = packed_pair_sum(a, b)
        # E_packed-E_witness=(W_witness-W_packed)/3 for the very same s.
        lower_difference = Fraction(witness_lo - packed_hi, 3 * UNIT)
        if lower_difference > TARGET:
            accepted += 1
            total_length += b - a
            min_margin = (lower_difference if min_margin is None
                          else min(min_margin, lower_difference))
            max_depth = max(max_depth, depth)
        else:
            if depth >= 30:
                raise ArithmeticError(f"Unresolved separation interval [{a},{b}]")
            mid = (a + b)/2
            pending.extend(((a, mid, depth + 1), (mid, b, depth + 1)))

    assert total_length == initial[1] - initial[0] and visited == 2 * accepted - 1
    assert min_margin > TARGET
    energy_lower = 1 - Fraction(3 * g0_hi + witness_hi, 3 * UNIT)
    energy_upper = 1 - Fraction(3 * g0_lo + witness_lo, 3 * UNIT)
    print(f"Witness E in [{energy_lower}, {energy_upper}]")
    print(f"Covered d in [{initial[0]}, {initial[1]}] and its reflection, h={H}, s={S}")
    print(f"Visited {visited} boxes, certified {accepted} leaves, maximum depth {max_depth}")
    print(f"E_packed-E_witness >= {min_margin} > {TARGET}")


if __name__ == "__main__":
    main()
