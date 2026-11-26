"""Independent contact-block certificate for s=22, h=1/1000. Standard Python 3."""
from array import array
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import accumulate, combinations, product
from math import factorial


GRID = 32000
H = GRID // 1000
UNIT = 10**11
WORK = 10**35
# Bounds for the second, third and fourth spatial derivatives of G_22.
DERIVATIVE_CAPS = (44, 1500, 22000)
WITNESS = (0, 125, 126, 250, 500, 750)
LOCAL_WORD = (3, 1, 1, 1)
LOCAL_CENTERS = (0, 8032, 16032, 24032)
LOCAL_RADIUS = 2


def ceil_div(a, b):
    return -(-a // b)


def check_constants():
    assert H * 1000 == GRID
    # Four external gaps of every accepted box lie in the local uniqueness region.
    y1, y2, y3 = LOCAL_CENTERS[1:]
    for gap, radius in ((y1 - 2 * H, LOCAL_RADIUS), (y2 - y1, 2 * LOCAL_RADIUS),
                        (y3 - y2, 2 * LOCAL_RADIUS), (GRID - y3, LOCAL_RADIUS)):
        assert 21 * GRID <= 100 * (gap - radius)
        assert 100 * (gap + radius) <= 29 * GRID
    # q < 2/3 since pi>3 and exp(9/22)>3/2, and 2 sqrt(pi/22)<1.
    x = Fraction(9, 22)
    assert sum(x**k / factorial(k) for k in range(4)) > Fraction(3, 2)
    for order in (3, 4):
        q = Fraction(2, 3)
        ratio = Fraction(6, 5)**order * q**11
        series = sum(n**order * q**(n*n) for n in range(1, 5))
        series += 5**order * q**25 / (1 - ratio)
        assert Fraction(44, 7)**order * series < DERIVATIVE_CAPS[order - 2]
    # Both image tails after k=3. The first omitted |k| is 4.
    tail = Fraction(4 * (1936 * 25 + 44), 2**198)
    assert tail < Fraction(1, UNIT)
    assert Fraction(6, 5)**2 * Fraction(1, 2**154) < Fraction(1, 2)


def exp_step(z):
    """Outward fixed-point bounds for exp(-z) at one small lattice increment."""
    assert 0 <= z <= 1
    even = sum((-z)**j / factorial(j) for j in range(5))
    odd = even - z**4 / factorial(4)
    return odd * WORK // 1, ceil_div(even * WORK, 1)


def gaussian_nodes():
    # u_n=exp(-22 n^2 / GRID^2), r_n=u_(n+1)/u_n;
    # r_(n+1)/r_n = exp(-44/GRID^2).
    ratio_lo, ratio_hi = exp_step(Fraction(22, GRID**2))
    step_lo, step_hi = exp_step(Fraction(44, GRID**2))
    images = [(WORK, WORK)]
    lo = hi = WORK
    for _ in range(4 * GRID):
        lo = lo * ratio_lo // WORK
        hi = ceil_div(hi * ratio_hi, WORK)
        images.append((lo, hi))
        ratio_lo = ratio_lo * step_lo // WORK
        ratio_hi = ceil_div(ratio_hi * step_hi, WORK)

    den = WORK * GRID**2
    nodes = []
    for index in range(GRID):
        ends = [0] * 6
        for k in range(-3, 4):
            m = index + k * GRID
            elo, ehi = images[abs(m)]
            linear = -44 * m
            coefficients = (GRID**2, linear * GRID, linear**2 - 44 * GRID**2)
            for order, w in enumerate(coefficients):
                a, b = w * elo, w * ehi
                ends[2 * order] += min(a, b)
                ends[2 * order + 1] += max(a, b)
        nodes.append(tuple((v * UNIT // den - 1) if j % 2 == 0
                           else (ceil_div(v * UNIT, den) + 1)
                           for j, v in enumerate(ends)))
    return nodes


def signed(values, sign):
    if sign == 1:
        return values
    return (-values[1], -values[0], -values[3], -values[2],
            -values[5], -values[4])


class BlockKernel:
    """Binary range tree of values, gradients and curvatures for two fixed blocks."""
    def __init__(self, nodes, left_size, right_size):
        shifts = Counter()
        for i in range(left_size):
            for j in range(right_size):
                shifts[(j - i) * H] += (-1)**(i + j)
        shifts = [(shift, w) for shift, w in shifts.items() if w]
        # Index D duplicates index 0 by periodicity.
        self.size = 1 << GRID.bit_length()
        self.ends = [array("q", [0]) * (2 * self.size) for _ in range(6)]
        error = [ceil_div(left_size * right_size * cap * UNIT, 8 * GRID**2)
                 for cap in DERIVATIVE_CAPS]
        for p in range(GRID + 1):
            ends = [0] * 6
            for shift, w in shifts:
                val = nodes[(p + shift) % GRID]
                if w < 0:
                    val = signed(val, -1)
                for j in range(6):
                    ends[j] += abs(w) * val[j]
            for j in range(6):
                pad = error[j // 2]
                self.ends[j][p + self.size] = ends[j] + (pad if j % 2 else -pad)
        for j, band in enumerate(self.ends):
            combine = max if j % 2 else min
            for p in range(self.size - 1, 0, -1):
                band[p] = combine(band[2*p], band[2*p+1])

    @lru_cache(maxsize=65536)
    def range(self, lo, hi):
        assert 0 <= lo <= hi <= GRID
        a, b = self.size + lo, self.size + hi + 1
        pieces = []
        while a < b:
            if a % 2:
                pieces.append(a)
                a += 1
            if b % 2:
                b -= 1
                pieces.append(b)
            a //= 2
            b //= 2
        return tuple((max if j % 2 else min)(band[i] for i in pieces)
                     for j, band in enumerate(self.ends))


def canonical(word):
    rev = word[::-1]
    return max(w[i:] + w[:i] for w in (word, rev) for i in range(len(w)))


def contact_words():
    words = set()
    for bits in product((0, 1), repeat=6):
        cuts = [i for i, strict in enumerate(bits) if strict]
        if not cuts:
            continue  # six copies of h cannot sum to one
        lengths = tuple(b - a for a, b in zip(cuts, cuts[1:] + [cuts[0] + 6]))
        words.add(canonical(lengths))
    return sorted(words, key=lambda word: (len(word), word))


def signed_point_score(nodes, positions):
    low = 0
    for i, j in combinations(range(len(positions)), 2):
        ends = nodes[(positions[j] - positions[i]) % GRID]
        low += signed(ends, (-1)**(j-i))[0]
    return low


def verify_face(word, nodes, kernel, score_floor):
    count = len(word)
    first = (0, *accumulate(word[:-1]))
    # Extend the domains to include equality in strict-gap and wrap constraints.
    pairs = []
    for i, j in combinations(range(count), 2):
        diff = first[j] - first[i]
        pairs.append((i, j, diff*H, GRID-(6-diff)*H,
                      (-1)**diff, kernel(word[i], word[j])))
    internal_upper = 0
    for n in word:
        for i, j in combinations(range(n), 2):
            internal_upper += signed(nodes[(j-i)*H], (-1)**(j-i))[1]

    # Simultaneous translations of subsets, and relative translations of two blocks.
    directions = [v + (0,) for v in product((0, 1), repeat=count-1) if any(v)]
    for i, j in combinations(range(count), 2):
        v = [0] * count
        v[i], v[j] = -1, 1
        directions.append(v)
    weights = [[(k, (v[j]-v[i])**2) for k, (i,j,*_) in enumerate(pairs) if v[i]!=v[j]]
               for v in directions]
    equal_starts = [i for i in range(1, count) if word[i:] + word[:i] == word]
    stats = Counter()
    todo = [([0] * count, [0] + [GRID - H * word[-1]] * (count - 1))]
    while todo:
        lo, hi = todo.pop()
        stats["visited"] += 1
        for i in range(1, count):
            lo[i] = max(lo[i], lo[i-1] + word[i-1]*H)
        for i in range(count-2, -1, -1):
            hi[i] = min(hi[i], hi[i+1] - word[i]*H)
        wrap_upper = GRID - lo[-1] - (word[-1]-1)*H
        if any(a > b for a, b in zip(lo, hi)) or any(
            lo[i] - hi[i-1] - (word[i-1]-1)*H > wrap_upper for i in equal_starts
        ):
            stats["order"] += 1
            continue
        if word == LOCAL_WORD and all(a >= p - LOCAL_RADIUS and b <= p + LOCAL_RADIUS
                                      for a,b,p in zip(lo, hi, LOCAL_CENTERS)):
            stats["local"] += 1
            continue
        grad_lower = [0] * count
        grad_upper = [0] * count
        hessian_lower = []
        score_upper = internal_upper
        for i, j, left, right, sgn, table in pairs:
            a = max(lo[j] - hi[i], left)
            b = min(hi[j] - lo[i], right)
            assert a <= b
            _, upper, gl, gu, hl, _ = signed(table.range(a,b), sgn)
            score_upper += upper
            grad_lower[i] -= gu
            grad_upper[i] -= gl
            grad_lower[j] += gl
            grad_upper[j] += gu
            hessian_lower.append(hl)
        if score_upper < score_floor:
            stats["score"] += 1
        elif any(a > 0 or b < 0 for a, b in zip(grad_lower, grad_upper)):
            stats["gradient"] += 1
        elif any(sum(w*hessian_lower[k] for k,w in row) > 0 for row in weights):
            stats["curvature"] += 1
        else:
            size, k = max(((hi[i]-lo[i], i) for i in range(count)), key=lambda pair: pair[0])
            if size <= 1:
                raise AssertionError(f"unresolved {word}: {lo}, {hi}")
            mid = (lo[k] + hi[k]) // 2
            left_hi, right_lo = hi.copy(), lo.copy()
            left_hi[k] = right_lo[k] = mid
            todo.extend(((lo, left_hi), (right_lo, hi)))
    assert stats["visited"] == 2*(sum(stats.values())-stats["visited"])-1
    return stats


def main():
    if not __debug__:
        raise SystemExit("Run without -O to enable certificate assertions")
    check_constants()
    nodes = gaussian_nodes()
    kernel = lru_cache(None)(lambda a,b: BlockKernel(nodes, a, b))
    score_floor = signed_point_score(nodes, [v*H for v in WITNESS])
    words = contact_words()
    assert len(words) == 12 and LOCAL_WORD in words
    total = Counter()
    for word in words:
        stats = verify_face(word, nodes, kernel, score_floor)
        assert bool(stats["local"]) == (word == LOCAL_WORD)
        print("".join(map(str,word)),
              *(stats[k] for k in ("visited", "order", "score", "gradient", "curvature", "local")))
        total.update(stats)
    print("Total", *(total[k] for k in ("visited", "order", "score", "gradient", "curvature", "local")))
    print(f"All maximizers lie on {LOCAL_WORD}, within {LOCAL_RADIUS}/{GRID} of the stated centers.")


if __name__ == "__main__":
    main()
