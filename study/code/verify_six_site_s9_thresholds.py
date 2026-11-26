"""Certify the two six-site packed-edge thresholds at s=9 with rational bounds."""

from fractions import Fraction as F
from math import ceil, floor

from verify_six_site_bifurcation import (
    MODES, OMEGA, PI, Interval, box, chebyshev, cosine_box,
)
from verify_stability import exponential_bounds


def nome_at_width(width):
    """Enclose exp(-pi^2 / width) with rational bounds."""
    width = F(width)
    if width <= 0:
        raise ValueError("the Gaussian width must be positive")
    exponent = PI**2 * (1 / width)
    return Interval(exponential_bounds(exponent.hi)[0],
                    exponential_bounds(exponent.lo)[1])


def nome_at_nine():
    return nome_at_width(9)


def endpoint_derivative(h, contact, nome):
    """Enclose Phi'_h(0) or Phi'_h(y_b) including all Fourier modes."""
    x = cosine_box(OMEGA * h)
    z = 3*x - 4*x**3 if contact else box(1)
    assert F(1, 2) <= x.lo <= x.hi and x.hi**2 <= F(1, 2)
    assert F(1, 2) <= z.lo <= z.hi <= 1
    total = box(0)
    modes = zip(chebyshev(x), chebyshev(z))
    for n, ((t, _), (_, u)) in enumerate(modes, start=1):
        weight = (-1)**(n+1) * n * nome**(n*n-1)
        total += weight * (2*t-1)**2 * u

    first = MODES + 1
    ratio = F(first+1, first)**2 * nome.hi**(2*first+1)
    assert ratio < 1
    tail = 9*first**2 * nome.hi**(first**2-1) / (1-ratio)
    return total + Interval(-tail, tail)


def main():
    if not __debug__:
        raise RuntimeError("Run this certificate with assertions enabled.")
    nome = nome_at_nine()
    assert F(".33399718") < nome.lo <= nome.hi < F(".33399719") < F(17, 50)
    for name, contact, left, right in [
        ("center", False, ".12707787492004334", ".12707787492004335"),
        ("outer contact", True, ".12966203092650766", ".12966203092650767"),
    ]:
        for h, sign in [(left, 1), (right, -1)]:
            value = endpoint_derivative(F(h), contact, nome)
            assert value.lo > 0 if sign == 1 else value.hi < 0
            print(f"{name} at {h}: [{floor(value.lo*10**18)}, "
                  f"{ceil(value.hi*10**18)}] x 10^-18")


if __name__ == "__main__":
    main()
