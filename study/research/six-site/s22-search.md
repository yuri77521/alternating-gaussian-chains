# 从原有上界到相邻两接触的六粒子候选

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

取周期一、$s=22$、$h=1/1000$。原有试探 $X=(0,125,126,250,500,750)/1000$ 在全可行集上提供能量上界 $E(X)<0.667106810407357$，并已排除整条紧双簇边。[紧双簇排除证明](s22-competitor.md)

## 可逐点复算的更低试探

取点列 $Z=(0,1,2,251,501,751)/1000$。其间隙为 $(1,1,249,250,250,249)/1000$，达到下限的两个间隙相邻。为比较近旁的另一试探 $W$，写 $g_i=h+(1-6h)u_i$，取

$$
2^{20}u(W)=(0,0,261616,262672,262672,261616).
$$

三者都满足循环间隙约束。按完整有向周期像求和，以下整数界须乘以 $10^{-19}$ 才是物理每粒子能量或能差。

| 量 | 下界整数 | 上界整数 |
|---|---:|---:|
| $E(X)$ | 6671068104073566285 | 6671068104073566286 |
| $E(Z)$ | 6650358445233044362 | 6650358445233044363 |
| $E(W)$ | 6650358445155248351 | 6650358445155248352 |
| $E(X)-E(Z)$ | 20709658840521923 | 20709658840521924 |
| $E(Z)-E(W)$ | 77796011 | 77796012 |

因此 $X$ 和 $Z$ 都严格失优。$E(W)-E(Z)$ 的绝对值只有约 $7.78\times10^{-12}$，不过用于排除 $X$ 时，简单的千分点列 $Z$ 已足够。表中针对 $W$ 的结论是可行能量上界。

## 十二类支撑上的搜索结果

间隙大于 $h$ 的位置组成松弛支撑。用 1 标出松弛位置，0 标出接触。旋转及反射作用下，全部非空六位支撑有十二类。每类都在总余量为 16 单位的正整数分配上选种子，再细化到 $2^{20}$ 单位。每个种子分别在闭面及保留原支撑的网格上作一次转移下降。闭面允许松弛量归零。在保留支撑的网格上，每个原松弛位置至少保留一个单位。两种模式共 146 次下降，按间隙的旋转、反射去重后得到 23 个终点。逐一使用有理像和界确认这些终点的能量，再用不相交的区间判定各模式所得最低终点。

下表的 $k$ 表示**搜索所得最低终点**的能量在 $[k,k+1]\,10^{-15}$ 内。闭面包含它的低维边界，因此不同的搜索支撑可能给出同一个终点。

| 松弛支撑 | 闭面搜索的 $k$ | 保留支撑搜索的 $k$ |
|---|---:|---:|
| 000001 | 999934023954049 | 999934023954049 |
| 000011 | 669438766382902 | 669438766382902 |
| 000101 | 999934023954049 | 999934023965057 |
| 000111 | 669438766382902 | 669438796449213 |
| 001001 | 669422909776542 | 669422909776542 |
| 001011 | 669422909776542 | 669422924814430 |
| 001111 | 665035844515524 | 665035844515524 |
| 010101 | 999934023954049 | 999934023976067 |
| 010111 | 669422909776542 | 669422939852318 |
| 011011 | 669422909776542 | 669422939852318 |
| 011111 | 665035844515524 | 665035869586280 |
| 111111 | 665035844515524 | 665035894680801 |

以 $E(X)$ 为第一道阈值，支撑 001111、011111 和 111111 各有严格低于阈值的有理点。后两支撑在保留原支撑的网格上也能击败 $X$，所以仅靠该上界无法整类排除它们。闭面搜索则在三类上都到达相邻两接触的 $W$。其余九类在这些起点下找到的终点都输给 $X$。要排除这九类的全部连续构型，以及处理前两类高维支撑任意接近 $W$ 的位置，还需覆盖连续域的证明。网格终点的精确能量不能给未采样构型提供下界。

## 复算

以下代码在仓库根目录以开启断言的标准库 Python 运行。探索部分复用六粒子间隙转移程序，用当前参数 $s=22$ 重新计算 Fourier 权重，固定随机种子 22001。不同的浮点数学库可能把下降路径引向相邻网格点，因此终点数及表中末位可随运行环境变化。对给定的有理坐标，能量比较重新计算有限像和并加入无穷尾项，所得严格判号可以脱离搜索单独重放。[搜索工具](../../code/probe_six_site_s9.py) · [有理能量实现](../../code/verify_exact_clusters.py)

~~~python
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import ceil, exp, floor, pi
from random import Random
import sys
sys.path.insert(0, "code")
from probe_six_site_s9 import COARSE, DENOM, canonical, descend, image_energy
from probe_six_site_s9 import make_score, modes, positive_rows
from verify_exact_clusters import certified_energy

h = F(1, 1000)
score = make_score(float(h), modes(exp(-pi*pi/22), 6)[0])
rng = Random(22001)

@lru_cache(None)
def energy(row):
    return image_energy(h, row, 22)

runs = 0
for mask in product(range(2), repeat=6):
    if not any(mask) or mask != canonical(mask):
        continue
    active = tuple(i for i, bit in enumerate(mask) if bit)
    rows = [tuple(x * (DENOM // COARSE) for x in row)
            for row in positive_rows(active, COARSE)]
    seeds = {min(rows, key=score), min(rows, key=lambda r: sum(x*x for x in r))}
    seeds.update(rng.sample(rows, min(5, len(rows))))
    reports = []
    for lower in (0, 1):
        endpoints = set()
        for seed in sorted(seeds):
            _, row = descend(score, seed, active, lower)
            assert sum(row) == DENOM
            assert all(x >= lower if i in active else x == 0 for i, x in enumerate(row))
            endpoints.add(canonical(row))
        runs += len(seeds)
        best = min(endpoints, key=lambda row: energy(row)[1])
        lo, hi = energy(best)
        assert all(row == best or hi < energy(row)[0] for row in endpoints)
        k = floor(10**15 * lo)
        assert k + 1 == ceil(10**15 * hi)
        reports.append(k)
    print("".join(map(str, mask)), *reports)
print("descents", runs, "distinct endpoints", energy.cache_info().currsize)

def sites(row):
    return tuple(F(i, 1000) for i in row)

x = certified_energy(sites((0, 125, 126, 250, 500, 750)), 22)
z = certified_energy(sites((0, 1, 2, 251, 501, 751)), 22)
fine = energy((0, 0, 261616, 262672, 262672, 261616))
for name, pair in (("X", x), ("Z", z), ("fine", fine),
                   ("X-Z", (x[0] - z[1], x[1] - z[0])),
                   ("Z-fine", (z[0] - fine[1], z[1] - fine[0]))):
    print(name, floor(10**19 * pair[0]), ceil(10**19 * pair[1]))
assert fine[1] < z[0] < z[1] < x[0]
~~~
