"""Rational constants for the small-floor block proof at Gaussian exponent 9."""

from fractions import Fraction as F
from math import factorial


def check_small_floors():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")

    q = F(".335")
    e = F(".44")
    assert q * sum((F("3.14")**2/9)**k / factorial(k) for k in range(8)) > 1
    assert 2 * F(22, 7) * F(7, 100) == e

    def tail(power):
        ratio = F(4, 3)**power * q**7
        assert ratio < 1
        return 3**power * q**8 / (1 - ratio)

    score = F(".608")
    slope = F(".616")
    curvature = F("1.246")
    fourth_moment = F(".615")
    assert 16*q**3 + 4*tail(2) < score
    assert 16*q**3 + 10*tail(2) < slope
    assert 32*q**3 + 10*tail(3) < curvature
    assert 16*q**3 + tail(4) < fourth_moment

    amplitude = F("1.41")
    radius = F(".46")
    assert 4*(1-e**2)**2 - score > amplitude**2
    assert amplitude*(radius-radius**3/6) > slope
    assert amplitude*(1-radius**2/2) > curvature
    assert 2*radius < F("3.14")/2
    assert 1-e**2 > F(".8")
    assert 3*e < amplitude

    # The second harmonic of the five-site block has modulus at most one.
    assert 2*e < F("3.14")/3
    assert 1 - 3*e**2 - 4*q**3 - 5*tail(2) > F(".26")
    assert 4*(1-e**2/6)**2*(1-e**2)**2 - 9*fourth_moment*e**2 > F("1.36")
    assert (1-e**2)**2 - 4*q**3 - 9*tail(2) > F(".48")

    # Distinct charged packets in the collision-permitted h=0 endpoint.
    assert 4 - score > F("1.84")**2
    assert 1 - 4*q**3 - tail(2) > F(".84")


if __name__ == "__main__":
    check_small_floors()
    print("s=9: small-floor block inequalities passed for 0 < h <= 7/100.")
