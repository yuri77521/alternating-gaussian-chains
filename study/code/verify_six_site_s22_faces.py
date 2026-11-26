"""Global comparison on the one-contact and adjacent-two-contact faces at s=22.

The analytic exclusions reduce all other supports to these two or exclude
them. Each box uses physical loose gaps, with the sum constraint retained.
Run with standard-library Python and assertions enabled.
"""
from collections import Counter
from itertools import combinations

from six_site_s22_block_kernel import BlockKernel, D, UNIT
from verify_six_site_s22 import UNIT as WITNESS_UNIT, witness_pair_sum


H = D // 1000
assert D % 1000 == 0


def signed(interval, sign):
    lo, hi = interval
    return (lo, hi) if sign == 1 else (-hi, -lo)


def intersect(lo, hi, total):
    """Keep the sum hyperplane and the reflection chamber g[0] <= g[-1]."""
    for _ in range(2):
        lo[-1] = max(lo[0], lo[-1])
        hi[0] = min(hi[0], hi[-1])
        low_sum = sum(lo)
        high_sum = sum(hi)
        if low_sum > total or high_sum < total:
            return False
        for k in range(len(lo)):
            lo[k], hi[k] = (max(lo[k], total - high_sum + hi[k]),
                            min(hi[k], total - low_sum + lo[k]))
        if any(a > b for a, b in zip(lo, hi)):
            return False
    return sum(lo) <= total <= sum(hi)


class GapFace:
    def __init__(self, kernel, block):
        self.block = block
        self.sizes = [block] + [1] * (6 - block)
        self.m = len(self.sizes)
        self.total = D - (block - 1) * H
        self.get = kernel.get
        starts = [sum(self.sizes[:j]) for j in range(self.m)]
        self.pairs = []
        for i, j in combinations(range(self.m), 2):
            contacts = (starts[j] - starts[i]) - (j - i)
            sign = (-1)**(starts[j] - starts[i])
            self.pairs.append((i, j, self.sizes[i], self.sizes[j], contacts * H, sign))
        internal = [signed(self.get(1, 1, 0, k * H, k * H), (-1)**k)
                    for k in range(1, block)]
        self.internal_upper = sum((block - k) * tup[1]
                                  for k, tup in enumerate(internal, start=1))
        # Moving any proper group of whole blocks is a two-sided feasible variation
        # in the relative interior. Complementary groups give equivalent tests.
        self.cut_vectors = []
        for mask in range(1, 1 << (self.m - 1)):
            cut = []
            for k, (i, j, *_) in enumerate(self.pairs):
                move = ((mask >> j) & 1) - ((mask >> i) & 1)
                if move:
                    cut.append((k, move))
            self.cut_vectors.append(cut)
        self.cut_vectors.sort(key=len)

    def ranges(self, lo, hi):
        low_sum, high_sum = sum(lo), sum(hi)
        intervals = []
        for i, j, a, b, internal, sign in self.pairs:
            left = sum(lo[i:j])
            right = sum(hi[i:j])
            left, right = (max(left, self.total - high_sum + right),
                           min(right, self.total - low_sum + left))
            intervals.append((a, b, internal + left, internal + right, sign))
        return intervals

    def terms(self, intervals, order):
        return [signed(self.get(a, b, order, lo, hi), sign)
                for a, b, lo, hi, sign in intervals]

    def cutoff(self, lo, hi, x_score):
        intervals = self.ranges(lo, hi)
        score = self.internal_upper + sum(b for a, b in self.terms(intervals, 0))
        if score < x_score:
            return "X"
        # With exactly two adjacent contacts the block is a tight triple.
        # The local theorem covers this entire closed four-gap rectangle.
        if self.block == 3 and min(lo) >= 21 * D // 100 and max(hi) <= 29 * D // 100:
            return "local"
        gradient = self.terms(intervals, 1)
        for cut in self.cut_vectors:
            low = sum(gradient[p][0] if move == 1 else -gradient[p][1] for p, move in cut)
            high = sum(gradient[p][1] if move == 1 else -gradient[p][0] for p, move in cut)
            if low > 0 or high < 0:
                return "first"
        hess = self.terms(intervals, 2)
        for cut in self.cut_vectors:
            if sum(hess[p][0] for p, _ in cut) > 0:
                return "second"
        return None

    def search(self, x_score):
        stack = [([H] * self.m, [self.total - (self.m - 1) * H] * self.m)]
        counts = Counter()
        while stack:
            lo, hi = stack.pop()
            counts["boxes"] += 1
            if not intersect(lo, hi, self.total):
                counts["empty"] += 1
                continue
            label = self.cutoff(lo, hi, x_score)
            if label:
                counts[label] += 1
                continue
            k = max(range(self.m), key=lambda k: hi[k] - lo[k])
            if hi[k] - lo[k] < 2:
                raise ArithmeticError((self.block, lo, hi))
            mid = (lo[k] + hi[k]) // 2
            left_hi, right_lo = hi[:], lo[:]
            left_hi[k], right_lo[k] = mid, mid
            stack.extend(((lo, left_hi), (right_lo, hi)))
        leaves = sum(n for k, n in counts.items() if k != "boxes")
        assert counts["boxes"] == 2 * leaves - 1
        return counts


def main():
    if not __debug__:
        raise RuntimeError("enable Python assertions")
    kernel = BlockKernel()
    x_lower, _ = witness_pair_sum()
    x_score = x_lower * UNIT // WITNESS_UNIT
    expected = {2: Counter(boxes=1269, X=36, first=283, second=316),
                3: Counter(boxes=541, X=24, first=158, second=79, local=10)}
    for block in (2, 3):
        face = GapFace(kernel, block)
        counts = face.search(x_score)
        assert counts == expected[block], (block, counts)
        print(f"Tight block size {block}, X score cutoff {x_score}: {dict(counts)}")


if __name__ == "__main__":
    main()
