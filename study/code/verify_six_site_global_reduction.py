"""Full-simplex certificate for period 1, exponent 8, and six alternating sites.

Run python code/verify_six_site_global_reduction.py. Only the standard library
is required. All comparisons and table construction use exact arithmetic.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import factorial


GRID = 8192                 # grid for sampling the periodic Gaussian
BARY = 8192                 # denominator of normalized slack box endpoints
UNIT = 10**9                # fixed-point unit for function and derivative bounds
DEN = 300000                # denominator of parameter-band endpoints
PAIRS = [(i, j, j - i, (-1)**(j - i)) for i in range(6) for j in range(i + 1, 6)]


def ceil_div(n, d):
    return -((-n) // d)


def sampled_images(exponent=8, grid=GRID):
    """Enclose exp(-exponent*m**2/grid**2), 0 <= m <= 4*grid, in fixed point."""
    scale = 10**32

    def exp_step(n):
        z = Fraction(n, grid**2)
        upper = sum((-z)**j / factorial(j) for j in range(5))
        lower = upper - z**4 / 24
        return int(scale * lower), ceil_div(scale * upper, 1)

    ratio_lo, ratio_hi = exp_step(exponent)
    step_lo, step_hi = exp_step(2 * exponent)
    lo = hi = scale
    nodes = [(lo, hi)]
    for _ in range(4 * grid):
        lo = lo * ratio_lo // scale
        hi = ceil_div(hi * ratio_hi, scale)
        ratio_lo = ratio_lo * step_lo // scale
        ratio_hi = ceil_div(ratio_hi * step_hi, scale)
        nodes.append((lo, hi))
    return scale, nodes


def samples(exponent=8):
    # The width-strip proof gives the same derivative and tail caps on [8,9].
    if not isinstance(exponent, (int, Fraction)) or not 8 <= exponent <= 9:
        raise ValueError("kernel exponent must be rational and in [8,9]")
    scale, images = sampled_images(exponent)
    changes = (4, 20, 150)
    low, high = [[] for _ in changes], [[] for _ in changes]
    numerator, denominator = exponent.numerator, exponent.denominator
    scaled_grid = denominator * GRID
    squared_grid = scaled_grid**2
    den = squared_grid * scale
    for p in range(GRID + 1):
        lower, upper = [0] * 3, [0] * 3
        for k in range(-3, 4):
            m = p + k * GRID
            e, f = images[abs(m)]
            linear = 2*numerator*m
            weights = (squared_grid, -linear * scaled_grid,
                       linear**2 - 2*numerator*denominator*GRID**2)
            for j, weight in enumerate(weights):
                lower[j] += min(weight * e, weight * f)
                upper[j] += max(weight * e, weight * f)
        for j, change in enumerate(changes):
            # One scaled unit on either side covers all omitted images.
            a = lower[j] * UNIT // den - 1
            b = ceil_div(upper[j] * UNIT, den) + 1
            if b - a > 4:
                raise ArithmeticError("kernel sample uncertainty")
            pad = ceil_div(change * UNIT, 2 * GRID)
            low[j].append(a - pad)
            high[j].append(b + pad)
    return low, high


class Kernel:
    def __init__(self, exponent=8):
        low, high = samples(exponent)
        self.nodes = [[(x + y) // 2 for x, y in zip(a, b)] for a, b in zip(low, high)]
        self.ranges = []
        for lows, highs in zip(low, high):
            # Level r tabulates each consecutive range of 2**r nearest nodes.
            table = [(lows, highs)]
            step = 1
            while 2 * step <= len(lows):
                a, b = table[-1]
                table.append(([min(x, y) for x, y in zip(a, a[step:])],
                              [max(x, y) for x, y in zip(b, b[step:])]))
                step *= 2
            self.ranges.append(table)


class Band:
    def __init__(self, kernel, left, right):
        if not 0 <= left < right <= DEN // 6:
            raise ValueError("invalid gap-floor interval")
        self.kernel = kernel
        self.left, self.right = left, right
        self.slack_lo, self.slack_hi = DEN - 6 * right, DEN - 6 * left
        self.get = lru_cache(maxsize=65536)(self._get)
        self.at = lru_cache(maxsize=65536)(self._at)

    def _at(self, span, coordinate):
        # Linear Taylor polynomial at nearest node, at the band's midpoint.
        den = 2 * DEN * BARY
        x = span * (self.left + self.right) * BARY + (self.slack_lo + self.slack_hi) * coordinate
        index = (2 * GRID * x + den) // (2 * den)
        delta = GRID * x - index * den
        return self.kernel.nodes[0][index] + self.kernel.nodes[1][index] * delta // (GRID * den)

    def _get(self, order, span, a, b):
        # Distance is span*h + (1-6h)*u, a/BARY <= u <= b/BARY.
        den = DEN * BARY
        x = min(span * self.left * BARY + self.slack_hi * a,
                span * self.right * BARY + self.slack_lo * a)
        y = max(span * self.left * BARY + self.slack_hi * b,
                span * self.right * BARY + self.slack_lo * b)
        left = (2 * GRID * x + den) // (2 * den)
        right = (2 * GRID * y + den) // (2 * den)
        level = (right - left + 1).bit_length() - 1
        lows, highs = self.kernel.ranges[order][level]
        other = right + 1 - (1 << level)
        return min(lows[left], lows[other]), max(highs[left], highs[other])


def terms(band, lo, hi, order):
    lower, upper = [], []
    sum_lo, sum_hi = sum(lo), sum(hi)
    for i, j, span, sign in PAIRS:
        lsum, hsum = sum(lo[i:j]), sum(hi[i:j])
        a = max(lsum, BARY - (sum_hi - hsum))
        b = min(hsum, BARY - (sum_lo - lsum))
        x, y = band.get(order, span, a, b)
        lower.append(x if sign == 1 else -y)
        upper.append(y if sign == 1 else -x)
    return lower, upper


def chamber(lo, hi):
    # Keep every feasible point where the distinguished last gap is largest.
    for _ in range(2):
        if sum(lo) > BARY or sum(hi) < BARY:
            return False
        sh = sum(hi)
        lo[:] = [max(x, BARY - sh + y) for x, y in zip(lo, hi)]
        sl = sum(lo)
        hi[:] = [min(y, BARY - sl + x) for x, y in zip(lo, hi)]
        lo[-1] = max(lo)
        hi[:] = [min(v, hi[-1]) for v in hi]
        if any(x > y for x, y in zip(lo, hi)):
            return False
    return sum(lo) <= BARY <= sum(hi)


def center_value(band, lo, hi, grad):
    # Reconcile the componentwise midpoint with the affine sum constraint.
    c = [(x + y) // 2 for x, y in zip(lo, hi)]
    rest = BARY - sum(c)
    for k in range(6):
        step = min(rest, hi[k] - c[k]) if rest >= 0 else max(rest, lo[k] - c[k])
        c[k] += step
        rest -= step
    if rest:
        raise ArithmeticError("no center in box")
    value, h_lo, h_hi = 0, 0, 0
    for p, (i, j, span, sign) in enumerate(PAIRS):
        u = sum(c[i:j])
        value += sign * band.at(span, u)
        v = span * BARY - 6 * u
        a, b = grad[0][p] * v, grad[1][p] * v
        h_lo += min(a, b)
        h_hi += max(a, b)
    error = len(PAIRS) * (4 + ceil_div(20 * UNIT, 8 * GRID**2))
    error += ceil_div(max(abs(h_lo), abs(h_hi)) * (band.right - band.left), 2 * DEN * BARY)
    return value - error, value + error, c


def search(band, support, target):
    stats = Counter()
    affected = [[p for p, (i, j, _, _) in enumerate(PAIRS) if i <= k < j] for k in support]
    cuts = affected + [sorted(set(a) ^ set(b)) for a, b in combinations(affected, 2)]
    initial = [BARY // 2 if k in support else 0 for k in range(5)] + [BARY]
    stack = [([0] * 6, initial)]
    while stack:
        lo, hi = stack.pop()
        stats['boxes'] += 1
        if not chamber(lo, hi):
            stats['empty'] += 1
            continue
        lower, upper = terms(band, lo, hi, 1)
        grad = [(sum(lower[p] for p in indices), sum(upper[p] for p in indices))
                for indices in affected]
        if any(a > 0 or b < 0 for a, b in grad):
            stats['gradient'] += 1
            continue
        hess, _ = terms(band, lo, hi, 2)
        if any(sum(hess[p] for p in indices) > 0 for indices in cuts):
            stats['curvature'] += 1
            continue
        _, value, center = center_value(band, lo, hi, (lower, upper))
        gain = sum(max((hi[k] - center[k]) * b, (lo[k] - center[k]) * a, 0)
                   for k, (a, b) in zip(support, grad))
        value += ceil_div(band.slack_hi * gain, DEN * BARY)
        if value < target:
            stats['value'] += 1
            continue
        widths = [hi[k] - lo[k] for k in support]
        if not widths or max(widths) <= 1:
            raise ArithmeticError((support, lo, hi, grad, value - target))
        k = support[widths.index(max(widths))]
        mid = (lo[k] + hi[k]) // 2
        left, right = hi[:], lo[:]
        left[k], right[k] = mid, mid
        stack.extend([(lo, left), (right, hi)])
    return stats


def certify(kernel, left, right, exclude_vertex):
    band = Band(kernel, left, right)
    targets = []
    for u in (0, BARY // 8, BARY // 4, 3 * BARY // 8, BARY // 2):
        trial = [0, 0, u, 0, 0, BARY - u]
        targets.append(center_value(band, trial, trial, terms(band, trial, trial, 1))[0])
    total = Counter()
    for n in range(0 if exclude_vertex else 1, 6):
        for active in combinations(range(5), n):
            if active != (2,) and active <= tuple(4 - i for i in reversed(active)):
                total.update(search(band, active, max(targets)))
    band.get.cache_clear()
    band.at.cache_clear()
    return total


def main():
    kernel = Kernel()
    narrow = certify(kernel, 3 * 13114, 3 * 13115, exclude_vertex=True)
    print("Strict two-gap support in bifurcation band:", dict(narrow), flush=True)
    endpoints = list(range(6000, 36000, 600)) + [36000, 40200, 42000, 45000, DEN // 6]
    totals = Counter()
    for left, right in zip(endpoints, endpoints[1:]):
        result = certify(kernel, left, right, exclude_vertex=False)
        totals.update(result)
        print(f"[{left}/{DEN},{right}/{DEN}]: {result['boxes']} boxes", flush=True)
    print("Closed opposite-gap edge on [1/50,1/6]:", dict(totals))


if __name__ == '__main__':
    main()
