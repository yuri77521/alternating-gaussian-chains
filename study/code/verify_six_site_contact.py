"""Rational certificate for the outer contact of the six-site packed family."""

from fractions import Fraction as F
from math import floor

from verify_stability import add_scaled, ceil, exponential_bounds


def atan_inverse_bounds(d):
    """Use 32 terms and the first omitted term of atan(1/d)."""
    lo = sum(F((-1)**k, (2*k + 1) * d**(2*k + 1)) for k in range(32))
    return lo, lo + F(1, 65 * d**65)


def pi_bounds():
    a, b = atan_inverse_bounds(5)
    c, d = atan_inverse_bounds(239)
    return 16*a - 4*d, 16*b - 4*c


def cos_bounds(angle):
    """Alternating cosine series on [0,1]."""
    assert 0 <= angle <= 1
    term = total = F(1)
    for k in range(1, 15):
        term *= -angle**2 / ((2*k - 1) * 2*k)
        total += term
    return total - term, total


def chebyshev_values(argument, second_kind, degree):
    values = [F(1), (2 if second_kind else 1) * argument]
    for _ in range(2, degree + 1):
        values.append(2 * argument * values[-1] - values[-2])
    return values


def series_bounds(x, nome):
    """Enclose B at rational x by the first six modes and a geometric tail."""
    t = chebyshev_values(x, False, 6)
    u = chebyshev_values(-t[3], True, 5)
    bounds = F(0), F(0)
    for n in range(1, 7):
        coefficient = (-1)**(n+1) * n * (2*t[n] - 1)**2 * u[n-1]
        powers = tuple(q**(n*n - 1) for q in nome)
        bounds = add_scaled(bounds, coefficient, powers)
    q_upper = F(3, 10)
    ratio = F(8, 7)**2 * q_upper**15
    tail = 9 * 7**2 * q_upper**48 / (1-ratio)
    return bounds[0]-tail, bounds[1]+tail


def verify():
    # A coarse rational pi interval keeps cosine Taylor denominators small.
    pi_lo, pi_hi = pi_bounds()
    scale = 10**30
    pi_lo = F(floor(pi_lo * scale), scale)
    pi_hi = F(ceil(pi_hi * scale), scale)
    nome = exponential_bounds(pi_hi**2 / 8)[0], exponential_bounds(pi_lo**2 / 8)[1]
    assert F(1, 4) < nome[0] <= nome[1] < F(3, 10)

    # Uniform bound on |sum_{n>=3} B_n'(x)| over 1/2 <= x <= 1/sqrt(2).
    ratio = F(4, 3)**4 * F(3, 10)**7
    derivative_error = 39 * 3**4 * F(3, 10)**8 / (1-ratio)
    assert derivative_error < F(208, 1000) < F(1, 4)
    print("B'(x) > 1/4 - 208/1000 on the whole interval")

    for h, sign in [("0.13327908477025674", 1), ("0.13327908477025675", -1)]:
        # The reversal comes from cos decreasing. B is increasing in x.
        x_lo = cos_bounds(2*pi_hi*F(h))[0]
        x_hi = cos_bounds(2*pi_lo*F(h))[1]
        x_lo = F(floor(x_lo * scale), scale)
        x_hi = F(ceil(x_hi * scale), scale)
        assert F(1, 2) < x_lo <= x_hi and x_hi**2 < F(1, 2)
        lo, hi = series_bounds(x_lo, nome)[0], series_bounds(x_hi, nome)[1]
        assert (lo > 0 if sign == 1 else hi < 0)
        out_scale = 10**18
        print(f"B({h}) in [{floor(lo*out_scale)}, {ceil(hi*out_scale)}] x 10^-18")


if __name__ == "__main__":
    verify()
