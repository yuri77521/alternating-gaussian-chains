"""Exclude every off-edge relative interior for six sites at s=9, 1/20 <= h < 1/6."""
from collections import Counter
from fractions import Fraction as F
from math import factorial

from verify_six_site_global_reduction import DEN, UNIT, Kernel, certify


def check_kernel_bounds():
    # Physical-image tail for G, G', G'' on 0 <= x <= 1, omitting |p| >= 4.
    # For j=|p| the majorant is (324*(j+1)**2+18)*2**(-9*(j-1)**2).
    weight_at_four = 324 * 5**2 + 18
    assert F(6, 5)**2 * F(1, 2**63) < F(1, 2)
    assert F(4 * weight_at_four, 2**81) < F(1, UNIT)

    # q=exp(-pi**2/9) < 0.34; sqrt(pi/9) < 0.6.
    q_upper = F(17, 50)
    exponent_lower = F("3.14")**2 / 9
    assert q_upper * sum(exponent_lower**j / factorial(j) for j in range(8)) > 1
    assert F(22, 7 * 9) < F(3, 5)**2
    for order, cap in enumerate((4, 20, 150), start=1):
        ratio = F(3, 2)**order * q_upper**5
        fourier_sum = q_upper + 2**order * q_upper**4 / (1 - ratio)
        assert ratio < 1 and F(6, 5) * F(44, 7)**order * fourier_sum < cap


def main():
    if not __debug__:
        raise RuntimeError("run with Python assertions enabled")
    check_kernel_bounds()
    kernel = Kernel(exponent=9)
    endpoints = list(range(DEN // 20, 36000, 600)) + [36000, 40200, 42000, 45000, DEN // 6]
    total = Counter()
    for left, right in zip(endpoints, endpoints[1:]):
        counts = certify(kernel, left, right, exclude_vertex=False)
        total.update(counts)
        print(f"[{left}/{DEN},{right}/{DEN}]: {counts['boxes']} boxes", flush=True)
    assert len(endpoints) - 1 == 39
    assert total == Counter(boxes=60182, value=7328, gradient=4267, curvature=18847)
    leaves = total['value'] + total['gradient'] + total['curvature']
    assert total['boxes'] == 2 * leaves - (len(endpoints) - 1) * 18
    print("Closed opposite-gap edge at s=9 on [1/20,1/6]:", dict(total))


if __name__ == "__main__":
    main()
