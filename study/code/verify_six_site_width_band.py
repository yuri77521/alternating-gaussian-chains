"""Six alternating sites: a full-simplex certificate uniform over widths [7.99,8.01].

From the repository root run python code/verify_six_site_width_band.py.
The integer kernel and face-cover routines are shared with the s=8 certificate.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import factorial

from verify_six_site_global_reduction import (
    BARY, DEN, PAIRS, UNIT, Band, Kernel, ceil_div, center_value, search, terms,
)


S_LO, S_HI = F("7.99"), F("8.01")
Q_CAP = F(".292")
PI_UP = F(22, 7)


def perturbation():
    # q_s <= Q_CAP via exp(pi^2/s) > 1/Q_CAP, uniformly in the stated band.
    z = F("3.1415") ** 2 / S_HI
    if Q_CAP * sum(z**j / factorial(j) for j in range(9)) <= 1:
        raise ArithmeticError("q bound")
    if PI_UP / 8 >= F(".63")**2:
        raise ArithmeticError("Poisson amplitude bound")
    # Freeze the constant and first Fourier amplitude at s=8. For coefficients
    # a_n(s)=q_s**(n^2-1), differentiate in s and bound the n>=2 sum by ratios.
    factor = 2 * F(".63") * Q_CAP * (PI_UP / S_LO)**2 * max(8 - S_LO, S_HI - 8)
    errors = []
    for r in range(3):
        ratio = F(3, 2)**r * F(8, 3) * Q_CAP**5
        bound = factor * (4 * PI_UP)**r * 3 * Q_CAP**3 / (1 - ratio)
        if ratio >= 1:
            raise ArithmeticError("derivative tail")
        errors.append(ceil_div(UNIT * bound, 1))
    return tuple(errors)


class WidthBand(Band):
    def __init__(self, kernel, left, right, errors):
        self.errors = errors
        super().__init__(kernel, left, right)

    def _get(self, order, span, a, b):
        lower, upper = super()._get(order, span, a, b)
        delta = self.errors[order]
        return lower - delta, upper + delta


def check(kernel, left, right, errors):
    band = WidthBand(kernel, left, right, errors)
    target = []
    for u in (0, BARY // 8, BARY // 4, 3 * BARY // 8, BARY // 2):
        trial = [0, 0, u, 0, 0, BARY - u]
        target.append(center_value(band, trial, trial, terms(band, trial, trial, 1))[0])
    # The s=8 scalar midpoint score used for each side can be wrong by at most
    # len(PAIRS)*errors[0] at another width. Combine both corrections in target.
    threshold = max(target) - 2 * len(PAIRS) * errors[0]
    result = Counter()
    for n in range(1, 6):
        for active in combinations(range(5), n):
            if active != (2,) and active <= tuple(4 - k for k in reversed(active)):
                result.update(search(band, active, threshold))
    band.get.cache_clear()
    band.at.cache_clear()
    return result


def main():
    errors = perturbation()
    print("Unit-scaled kernel enclosures for orders 0,1,2:", errors)
    kernel = Kernel()
    endpoints = list(range(DEN // 10, 36000, 600)) + [36000, 40200, 42000, 45000, DEN // 6]
    totals = Counter()
    for left, right in zip(endpoints, endpoints[1:]):
        result = check(kernel, left, right, errors)
        totals.update(result)
        print(f"[{left}/{DEN},{right}/{DEN}]: {result['boxes']} boxes")
    print("Opposite-gap edge for 7.99 <= s <= 8.01, .1 <= h <= 1/6:", dict(totals))


if __name__ == "__main__":
    main()
