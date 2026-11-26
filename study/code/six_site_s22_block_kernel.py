"""Integer enclosures for interactions between two tight blocks at s=22, h=1/1000."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import ceil

from verify_six_site_global_reduction import ceil_div, sampled_images


D = 1_000_000
UNIT = 10**9
GRID = 16_000


def _node_values(grid):
    scale, images = sampled_images(22, grid)
    denominator = grid**2 * scale
    # Two tails, first |k|=4, bounding amplitudes for derivatives 0,1,2 together.
    assert Fraction(6, 5)**2 / 2**154 < Fraction(1, 2)
    assert 4 * (1936 * 5**2 + 44) * UNIT < 2**198
    values = [[], [], []]
    errors = [0, 0, 0]
    for p in range(grid):
        low, high = [0, 0, 0], [0, 0, 0]
        for k in range(-3, 4):
            m = p + k * grid
            e, f = images[abs(m)]
            w = 44 * m
            weights = (grid**2, -w * grid, w**2 - 44 * grid**2)
            for j, weight in enumerate(weights):
                low[j] += min(weight * e, weight * f)
                high[j] += max(weight * e, weight * f)
        for j in range(3):
            lo = low[j] * UNIT // denominator - 1
            hi = ceil_div(high[j] * UNIT, denominator) + 1
            mid = (lo + hi) // 2
            values[j].append(mid)
            errors[j] = max(errors[j], hi - mid)
    assert max(errors) <= 3
    return values, errors


def _derivative_caps():
    """Bounds on sup |G^(k)| for k=2,...,6 from the absolute Fourier series."""
    q = Fraction(2, 3)
    p = Fraction(9, 22)
    assert 1 + p + p**2 / 2 + p**3 / 6 > 1 / q
    assert Fraction(22, 7 * 22) < Fraction(2, 5)**2
    caps = {}
    for k in range(2, 7):
        ratio = Fraction(5, 4)**k * q**9
        assert ratio < 1
        series = sum(n**k * q**(n * n) for n in (1, 2, 3))
        series += 4**k * q**16 / (1 - ratio)
        caps[k] = ceil(Fraction(4, 5) * Fraction(44, 7)**k * series)
    return caps


class _Range:
    """Sparse tables of node extrema plus a uniform linear interpolation error."""

    def __init__(self, nodes, error):
        self.nodes = nodes
        self.error = error
        self.layers = [(nodes, nodes)]
        width = 1
        while 2 * width <= len(nodes):
            lows, highs = self.layers[-1]
            self.layers.append(([min(x, y) for x, y in zip(lows, lows[width:])],
                                [max(x, y) for x, y in zip(highs, highs[width:])]))
            width *= 2

    def extrema(self, first, last):
        level = (last - first + 1).bit_length() - 1
        lo, hi = self.layers[level]
        other = last + 1 - (1 << level)
        return min(lo[first], lo[other]), max(hi[first], hi[other])

    def interpolation(self, k, rem):
        if rem == 0:
            return self.nodes[k] * D
        return self.nodes[k] * (D - rem) + self.nodes[k + 1] * rem

    def interval(self, left, right, grid):
        first_node, rem_l = divmod(left * grid, D)
        last_node, rem_r = divmod(right * grid, D)
        if last_node - first_node > 3:
            # Including the extra endpoint node on either side only widens the range.
            lo, hi = self.extrema(first_node, last_node + int(rem_r != 0))
        else:
            first = self.interpolation(first_node, rem_l)
            last = self.interpolation(last_node, rem_r)
            lo = min(first, last) // D
            hi = ceil_div(max(first, last), D)
            for i in range(first_node + 1, last_node + 1):
                lo = min(lo, self.nodes[i])
                hi = max(hi, self.nodes[i])
        return lo - self.error, hi + self.error


class BlockKernel:
    """get(a,b,j,l,r) encloses the j-th derivative of the signed block interaction.

    The integers l,r use the coordinate scale D. Returned endpoints use UNIT.
    Signs are internal to each alternating block starting at positive charge.
    """

    def __init__(self, grid=GRID):
        if grid < 1000 or grid % 1000:
            raise ValueError("grid must be a positive multiple of 1000")
        self.grid = grid
        self.values, self.errors = _node_values(grid)
        self.caps = _derivative_caps()
        self.tables = {}
        self.get = lru_cache(maxsize=131072)(self._get)

    def _table(self, a, b, order):
        key = a, b, order
        if key in self.tables:
            return self.tables[key]
        grid = self.grid
        single = self.values[order]
        weights = Counter()
        for i in range(a):
            for j in range(b):
                weights[(j - i) * (grid // 1000)] += (-1)**(i + j)
        nodes = [0] * grid
        for shift, weight in weights.items():
            for p in range(grid):
                nodes[p] += weight * single[(p + shift) % grid]
        nodes.append(nodes[0])
        node_error = self.errors[order] * sum(map(abs, weights.values()))
        evens = int(a % 2 == 0) + int(b % 2 == 0)
        multiplicity = (a if a % 2 else a // 2) * (b if b % 2 else b // 2)
        cap = self.caps[order + 2 + evens] * multiplicity
        interpolation_error = ceil_div(UNIT * cap, 8 * grid**2 * 1000**evens)
        table = _Range(nodes, node_error + interpolation_error)
        self.tables[key] = table
        return table

    def _get(self, a, b, order, left, right):
        if not (a >= 1 and b >= 1 and a + b <= 6 and 0 <= order <= 2
                and 0 <= left <= right <= D):
            raise ValueError("invalid block sizes, order or distance interval")
        if a < b:
            lo, hi = self._table(b, a, order).interval(D - right, D - left, self.grid)
            return (-hi, -lo) if order % 2 else (lo, hi)
        return self._table(a, b, order).interval(left, right, self.grid)
