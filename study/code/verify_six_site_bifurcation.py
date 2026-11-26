"""Rational certificates for the six-site packed branch, L=1, alpha=8.

Run with Python 3.9+ from the repository root:
    python code/verify_six_site_bifurcation.py
"""

from fractions import Fraction as F
from math import isqrt

from verify_stability import exponential_bounds


D = 10**32
MODES = 6


class Interval:
    """Closed rational intervals with outward rounding to the 1/D lattice."""

    def __init__(self, lo, hi=None):
        hi = lo if hi is None else hi
        assert lo <= hi
        self.lo = F((F(lo) * D).__floor__(), D)
        self.hi = F((F(hi) * D).__ceil__(), D)

    def __add__(self, other):
        other = box(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-box(other))

    def __mul__(self, other):
        other = box(other)
        corners = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(corners), max(corners))

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        a, b = self.lo**n, self.hi**n
        lo = 0 if n > 0 and n % 2 == 0 and self.lo <= 0 <= self.hi else min(a, b)
        return Interval(lo, max(a, b))


def box(x):
    return x if isinstance(x, Interval) else Interval(x)


def sqrt_box(x):
    x = box(x)
    assert x.lo >= 0
    a = isqrt((x.lo * D**2).__floor__())
    b = isqrt((x.hi * D**2).__floor__())
    return Interval(F(a, D), F(b + 1, D))


def atan_reciprocal(k):
    # Decreasing alternating terms. Degrees through 117 and 119 bracket atan.
    partial = F(0)
    for j in range(60):
        before = partial
        partial += F((-1)**j, (2*j + 1) * k**(2*j + 1))
    return Interval(partial, before)


def cosine_point(x):
    # After the constant term all term ratios are < 1 for 0 <= x <= 2.
    assert 0 <= x <= 2
    term = total = F(1)
    for j in range(1, 21):
        term *= -x*x / ((2*j - 1) * (2*j))
        total += term
    return Interval(total - term, total)


def cosine_box(x):
    assert 0 <= x.lo <= x.hi <= 2
    return Interval(cosine_point(x.hi).lo, cosine_point(x.lo).hi)


PI = 16 * atan_reciprocal(5) - 4 * atan_reciprocal(239)
OMEGA = 2 * PI
C = sqrt_box(PI * F(1, 8))
B = F(2, 3) * C
EXPONENT = PI**2 * F(1, 8)
Q = Interval(exponential_bounds(EXPONENT.hi)[0], exponential_bounds(EXPONENT.lo)[1])


def chebyshev(u):
    """Pairs T_n(u), U_{n-1}(u) for n=1,...,MODES."""
    previous_t, t = box(1), u
    previous_u, sine_ratio = box(0), box(1)
    for _ in range(MODES):
        yield t, sine_ratio
        previous_t, t = t, 2 * u * t - previous_t
        previous_u, sine_ratio = sine_ratio, 2 * u * sine_ratio - previous_u


def gaussian_moment_tail(first):
    """Upper bound for sum over n>=first of n^4 q^(n^2)."""
    assert first >= 3
    ratio = F(first + 1, first)**4 * Q.hi**(2*first + 1)
    assert ratio < F(1, 2)
    return 2 * first**4 * Q.hi**(first*first)


def derivatives(h, max_abs_t=0):
    """kappa, kappa', E_tttt(h,|t|<=max_abs_t), one inward slope at t=0."""
    u = cosine_box(OMEGA * h)
    sin_x = sqrt_box(box(1) - u**2)
    v = Interval(cosine_box(OMEGA * max_abs_t).lo, 1)
    k = dk = fourth = slope = box(0)
    for n, ((tn, un), (tv, _)) in enumerate(zip(chebyshev(u), chebyshev(v)), start=1):
        amplitude = 2 * tn - 1
        w = Q**(n*n)
        signed = (-1)**n * w
        k += -n*n * signed * amplitude**2
        dk += n**3 * signed * amplitude * un
        fourth += n**4 * signed * amplitude**2 * tv
        if n % 2:
            slope += n * w * amplitude * un
    tail = gaussian_moment_tail(MODES + 1)
    err = Interval(-tail, tail)
    return (
        B * OMEGA**2 * (k + 9 * err),
        4 * B * OMEGA**3 * sin_x * (dk + 3 * err),
        B * OMEGA**4 * (fourth + 9 * err),
        2 * B * OMEGA * sin_x * (slope + 3 * err),
    )


def assert_inside(value, lo, hi):
    assert F(lo) < value.lo <= value.hi < F(hi), (float(value.lo), float(value.hi), lo, hi)


def full_interval_signs():
    # u=cos(2*pi*h) lies in (1/2,1). Remove sin(2*pi*h) from kappa'.
    # First two normalized modes give -q(2u-1)+16u*q^4*(4u^2-3).
    # First case: u <= 2/3. Second: 2/3 <= u <= 5/6. Third: 5/6 <= u.
    bounds = (-F(88, 9) * Q**4, -F(1, 3) * Q, -F(2, 3) * Q + 16 * Q**4)
    high_modes = gaussian_moment_tail(3)
    upper = max(z.hi for z in bounds) + 3 * high_modes
    assert (4 * B * OMEGA**3 * upper).hi < -26

    # For odd n, (2T_n-1)U_{n-1} vanishes at u=1/2. The quotient after
    # dividing by 2u-1 has magnitude <= (5/2)n^3 by the mean value theorem.
    error = F(5, 2) * high_modes
    factored_slope = 2 * B * OMEGA * (Q + Interval(-error, error))
    assert_inside(factored_slope, '1.49', '1.57')
    print("All 0<h<1/6: kappa'/sin(2*pi*h) < -26")
    print("All 0<h<1/6: 1.49 < slope/[sin(2*pi*h)*(2*cos(2*pi*h)-1)] < 1.57")


def main():
    assert F('0.29121293') < Q.lo <= Q.hi < F('0.29121294')
    full_interval_signs()
    left, right = F('0.13114680495074'), F('0.13114680495076')
    assert_inside(derivatives(box(left))[0], '4e-13', '6e-13')
    assert_inside(derivatives(box(right))[0], '-8e-13', '-5e-13')
    print(f"Root bracket: ({float(left):.14f}, {float(right):.14f}); opposite signs")

    _, dk, fourth, slope = derivatives(Interval(left, right))
    assert_inside(dk, '-58.94248', '-58.94246')
    assert_inside(fourth, '70.22242', '70.22244')
    assert_inside(slope, '.40191212', '.40191214')
    ratio = 6 * (-dk) * Interval(1/fourth.hi, 1/fourth.lo)
    assert_inside(sqrt_box(ratio), '2.24414', '2.24416')
    assert_inside((-dk) * ratio * F(1, 4), '74.2115', '74.2119')
    print("Root bracket: -58.94248 < kappa' < -58.94246; 70.22242 < E_tttt < 70.22244")
    print("Root bracket: .40191212 < each contact slope < .40191214")
    print("Displacement coefficient in (2.24414,2.24416); energy gain coefficient in (74.2115,74.2119)")

    _, dk, fourth, slope = derivatives(Interval(F('.13114'), F('.13116')), F('.001'))
    assert_inside(dk, '-59.1', '-58.8')
    assert_inside(fourth, '69', '72')
    assert_inside(slope, '.400', '.403')
    print(".13114 <= h <= .13116: -59.1 < kappa' < -58.8; .400 < each contact slope < .403")
    print("Same h, |t| <= .001: 69 < E_tttt(h,t) < 72")

    kernel_moment = sum(n*n * Q**(n*n) for n in range(1, MODES + 1))
    kernel_bound = 2 * C * OMEGA**2 * (kernel_moment + gaussian_moment_tail(MODES + 1))
    assert kernel_bound.hi < 16
    # Endpoint-midpoint coordinates. At most 2 intratrimer and 9 intertrimer
    # pairs carry velocities 1 and 1/2, respectively, for a single gap.
    max_pair_shift = F('.003')
    assert F('.400') - F(13, 6) * max_pair_shift * 16 == F('.296')
    delta = F('1.9e-7')
    assert right + delta < F('.13116')
    assert F('59.1') * delta < F(69, 6) * F('.001')**2
    print("Same h,t and four independent gap releases <= .001: every gap slope > .296")
    print("For 0 < h-h_c <= 1.9e-7: exactly two interior face minima in |t| <= .001")


if __name__ == '__main__':
    main()
