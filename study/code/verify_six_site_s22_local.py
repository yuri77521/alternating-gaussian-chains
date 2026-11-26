"""Local contact locking, strict concavity and minimizer bounds for s=22, h=1/1000."""

from fractions import Fraction as F
from functools import lru_cache
from itertools import product

from verify_stability import add_scaled, exponential_bounds

H = F(1, 1000)
HALF = F(1, 2)
# On |x|<=1 the omitted |k|=j>=5 terms of orders 0, 1, 2 are
# bounded by (1936(j+1)^2+44) 2^(-22(j-1)^2), with ratio <1/2.
TAIL = F(4 * (1936 * 36 + 44), 2**352)


@lru_cache(maxsize=None)
def kernel(left, right, order):
    """Rational enclosure for G, G' or G'' on the indicated interval."""
    assert -1 <= left <= right <= 1 and order in (0, 1, 2)
    lower, upper = -TAIL, TAIL
    for k in range(-4, 5):
        a, b = k + left, k + right
        near = 0 if a <= 0 <= b else min(abs(a), abs(b))
        far = max(abs(a), abs(b))
        exp_lo = exponential_bounds(22 * far**2)[0]
        exp_hi = exponential_bounds(22 * near**2)[1]
        if order == 0:
            polynomial = (1, 1)
        elif order == 1:
            polynomial = (-44 * b, -44 * a)
        else:
            polynomial = (1936 * near**2 - 44, 1936 * far**2 - 44)
        bounds = [p * e for p, e in product(polynomial, (exp_lo, exp_hi))]
        lower += min(bounds)
        upper += max(bounds)
    return lower, upper


def packed_kernel(left, right, order):
    """Field of the three consecutive sites -h,0,h with signs +,-,+."""
    value = kernel(left - H, right - H, order)
    value = add_scaled(value, -1, kernel(left, right, order))
    return add_scaled(value, 1, kernel(left + H, right + H, order))


def certify_curvature():
    """Each loop covers the closed interval with touching rational cells."""
    for i in range(0, 40):
        assert kernel(i * H, (i + 1) * H, 2)[1] < -38
    for i in range(210, 330):
        assert kernel(i * H, (i + 1) * H, 2)[0] > 14
    for i in range(420, 580):
        assert kernel(i * H, (i + 1) * H, 2)[1] < 7
    for i in range(210, 310):
        assert packed_kernel(i * H, (i + 1) * H, 2)[0] > 14
    for i in range(420, 580):
        assert packed_kernel(i * H, (i + 1) * H, 2)[1] < 7


def symmetric_derivative(r):
    """Half of the derivative of the unordered score on the reflection line."""
    value = add_scaled((0, 0), -1, packed_kernel(r, r, 1))
    value = add_scaled(value, 1, kernel(HALF - r, HALF - r, 1))
    return add_scaled(value, -1, kernel(1 - 2 * r, 1 - 2 * r, 1))


def energy_interval(lo, hi):
    """Physical directed energy using all 15 unordered signed pairs."""
    points = [(-H, -H), (0, 0), (H, H), (lo, hi), (HALF, HALF), (1 - hi, 1 - lo)]
    energy = add_scaled((1, 1), -1, kernel(F(0), F(0), 0))
    for j, (a, b) in enumerate(points):
        for i in range(j):
            x, y = points[i]
            weight = F(-((-1)**(i + j)), 3)
            energy = add_scaled(energy, weight, kernel(a - y, b - x, 0))
    return energy


def main():
    if not __debug__:
        raise SystemExit("Enable assertions before running this certificate")
    certify_curvature()
    # These are consecutive rational grid points, not rounded root evaluations.
    denom = 10**24
    r = F(249999032167246504146498, denom)
    r_upper = r + F(1, denom)
    assert symmetric_derivative(r)[0] > 0 > symmetric_derivative(r_upper)[1]
    low, high = energy_interval(r, r_upper)
    assert F("0.665035844513390868270") < low < high < F("0.665035844513390868271")
    print("Local capture: adjacent gaps [.001,.02], four other gaps [.21,.29].")
    print("Reflection root lies strictly between 249999032167246504146498 / 10^24"
          " and 249999032167246504146499 / 10^24.")
    print("Physical energy lies in (0.665035844513390868270, 0.665035844513390868271).")


if __name__ == "__main__":
    main()
