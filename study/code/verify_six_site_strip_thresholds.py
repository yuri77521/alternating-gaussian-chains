"""Rational enclosures of the two six-site threshold curves on 8 <= s <= 9."""

from fractions import Fraction as F

from verify_six_site_s9_thresholds import endpoint_derivative, nome_at_width


def root_bracket(width, contact, digits=17):
    """Strict lower/upper floor bounds at a rational width. contact selects h_b."""
    width = F(width)
    if not 8 <= width <= 9 or not isinstance(digits, int) or not 3 <= digits <= 17:
        raise ValueError("expected 8 <= width <= 9 and 3 <= digits <= 17")
    denominator = 10**digits
    nome = nome_at_width(width)

    def slope(k):
        return endpoint_derivative(F(k, denominator), contact, nome)

    left, right = 126 * (denominator//1000), 135 * (denominator//1000)
    if slope(left).lo <= 0 or slope(right).hi >= 0:
        raise ArithmeticError("the initial threshold interval has unverified signs")
    while right - left > 1:
        mid = (left + right) // 2
        value = slope(mid)
        if value.lo > 0:
            left = mid
        elif value.hi < 0:
            right = mid
        else:
            # Near a decimal grid line the Fourier tail may obscure its sign.
            # Keep the proven bracket and tighten each side with its own test.
            if slope(mid-1).lo > 0:
                left = mid-1
            if slope(mid+1).hi < 0:
                right = mid+1
            break
    return F(left, denominator), F(right, denominator)


def main():
    if not __debug__:
        raise RuntimeError("Run this certificate with assertions enabled.")
    scale = 10**17
    previous = None
    slab_gaps = []
    for width in (F(8), F(33, 4), F(17, 2), F(35, 4), F(9)):
        center = root_bracket(width, contact=False)
        boundary = root_bracket(width, contact=True)
        assert center[1] < boundary[0]
        for label, (lo, hi) in (("h_c", center), ("h_b", boundary)):
            assert hi-lo == F(1, scale)
            print(f"s={width}, {label} from ({lo*scale}, {hi*scale}) / 10^17")
        if previous is not None:
            # Both curves decrease; throughout the slab h_b(s)-h_c(s)
            # exceeds h_b's right-end lower bound minus h_c's left-end upper.
            slab_gaps.append(boundary[0]-previous[1])
        previous = center
    assert min(slab_gaps) > F(".00114")
    print("On every intervening width slab: h_b(s)-h_c(s) > 0.00114")


if __name__ == "__main__":
    main()
