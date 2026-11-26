"""Rational implicit-derivative bounds for the width of the shifted phase."""

from fractions import Fraction as F
from math import ceil, floor

from verify_six_site_bifurcation import (
    MODES, OMEGA, PI, Interval, box, chebyshev, cosine_box, sqrt_box,
)
from verify_six_site_s9_thresholds import nome_at_width
from verify_six_site_strip_thresholds import root_bracket


def root_slope_factor(h, nome, contact):
    """q*P_q/(sin(2*pi*h)*P_x) on a box; h'(s) is this times pi/(2*s^2)."""
    x = cosine_box(OMEGA*h)
    assert x.lo >= F(1, 2) and x.hi**2 <= F(1, 2)
    z = 3*x-4*x**3 if contact else box(1)
    dz = box(3)-12*x**2 if contact else box(0)
    u_prev, u = box(0), box(1)
    du_prev, du = box(0), box(0)
    px = q_pq = box(0)
    for n, (t, v) in enumerate(chebyshev(x), 1):
        a = 2*t-1
        weight = (-1)**(n+1)*n*nome**(n*n-1)
        px += weight*(4*n*a*v*u + a**2*du*dz)
        q_pq += (n*n-1)*weight*a**2*u
        du_prev, du = du, 2*u+2*z*du-du_prev
        u_prev, u = u, 2*z*u-u_prev

    first = MODES+1
    ratio = F(first+1, first)**4 * nome.hi**(2*first+1)
    assert ratio < 1
    tail = first**4 * nome.hi**(first**2-1) / (1-ratio)
    err = Interval(-tail, tail)
    denominator = sqrt_box(box(1)-x**2)*(px+39*err)
    assert denominator.lo > 0
    return (q_pq+9*err)*Interval(1/denominator.hi, 1/denominator.lo)


def certificate(slabs):
    previous = None
    bounds = []
    for j in range(slabs+1):
        s = 8 + F(j, slabs)
        q = nome_at_width(s)
        roots = [root_bracket(s, contact, digits=6) for contact in (False, True)]
        if previous is not None:
            s_left, q_left, roots_left = previous
            nome = Interval(q_left.lo, q.hi)
            slopes = [root_slope_factor(Interval(right[0], left[1]), nome, contact)
                      for contact, left, right in zip((False, True), roots_left, roots)]
            prefactor = PI*Interval(1/(2*s*s), 1/(2*s_left*s_left))
            bounds.append(prefactor*(slopes[1]-slopes[0]))
        previous = s, q, roots
    return min(b.lo for b in bounds), max(b.hi for b in bounds)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run this certificate with assertions enabled.")
    lo, hi = certificate(32)
    print(f"32 slabs: (h_b-h_c)' in [{floor(lo*10**9)}, {ceil(hi*10**9)}]e-9")
    assert F(209555, 10**9) < lo <= hi < F(734655, 10**9)
    for s, lower, upper in ((8, 213227981950811, 213227981950813),
                            (9, 258415600646431, 258415600646433)):
        c, b = root_bracket(s, False), root_bracket(s, True)
        assert (b[0]-c[1], b[1]-c[0]) == (F(lower, 10**17), F(upper, 10**17))
        print(f"s={s}: h_b-h_c in ({lower}, {upper}) / 10^17")
