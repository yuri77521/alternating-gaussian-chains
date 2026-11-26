"""Exclude all off-edge supports on 8 <= s <= 9 and .07 <= h < 1/6."""

from collections import Counter
from fractions import Fraction as F
from math import ceil

from verify_six_site_bifurcation import PI, sqrt_box
from verify_six_site_global_reduction import DEN, UNIT, Kernel
from verify_six_site_s9_thresholds import nome_at_width
from verify_six_site_width_band import check


def check_table_constants():
    # Common image tail for orders 0,1,2 on 0 <= x <= 1 and 8 <= s <= 9.
    assert F(6, 5)**2 * F(1, 2**56) < F(1, 2)
    assert F(4 * (324*5**2 + 18), 2**72) < F(1, UNIT)
    # Three spatial Lipschitz bounds used in Kernel, including the Taylor cap 20.
    q_upper, c_upper = F(".335"), F(".63")
    assert nome_at_width(9).hi < q_upper and PI.hi/8 < c_upper**2
    for order, cap in enumerate((4, 20, 150), start=1):
        ratio = F(3, 2)**order * q_upper**5
        assert ratio < 1
        moment = q_upper + 2**order * q_upper**4 / (1-ratio)
        assert 2*c_upper*(2*PI.hi)**order * moment < cap


def width_errors(left, center, right):
    """Uniform sup-norm differences from the physical anchor G_center, in UNITs."""
    q_left, q_center, q_right = map(nome_at_width, (left, center, right))
    amplitude = 2 * sqrt_box(PI * (1 / F(center))).hi * q_center.hi
    errors = []
    for order in range(3):
        error = F(0)
        for n in (2, 3, 4):
            power = n*n - 1
            discrepancy = max(q_right.hi**power - q_center.lo**power,
                              q_center.hi**power - q_left.lo**power)
            error += (2*PI.hi*n)**order * discrepancy
        ratio = F(6, 5)**order * q_right.hi**11
        assert ratio < 1
        error += (10*PI.hi)**order * q_right.hi**24 / (1-ratio)
        errors.append(ceil(UNIT * amplitude * error))
    return tuple(errors)


def main():
    if not __debug__:
        raise SystemExit("Run with Python assertions enabled.")
    check_table_constants()
    floor_edges = [*range(7*DEN//100, DEN//6, DEN//500), DEN//6]
    total = Counter()
    for left, right in [(F(8), F(17, 2)), (F(17, 2), F(9))]:
        center = (left + right)/2
        kernel = Kernel(exponent=center)
        errors = width_errors(left, center, right)
        counts = Counter()
        for low, high in zip(floor_edges, floor_edges[1:]):
            counts.update(check(kernel, low, high, errors))
        roots = 18 * (len(floor_edges) - 1)
        leaves = counts["value"] + counts["gradient"] + counts["curvature"] + counts["empty"]
        assert counts["boxes"] == 2*leaves - roots
        print(f"s=[{left},{right}], anchor={center}, errors={errors}, "
              f"{len(floor_edges)-1} floor bands: {dict(counts)}", flush=True)
        total.update(counts)
    print("Closed opposite-gap edge for 8 <= s <= 9 and .07 <= h < 1/6:", dict(total))


if __name__ == "__main__":
    main()
