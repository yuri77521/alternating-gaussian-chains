# 六粒子连续宽度相图的独立审查

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

## 小间距与一维分类

归一化 Fourier 得分把第一模的系数固定为一，而 \(q=\exp(-\pi^2/s)\) 在 \([8,9]\) 上递增。[小间距脚本](../../code/verify_six_site_s9_small.py)中每个含高模的误差都用正系数级数或正项几何尾估计；最大 nome 的上界 \(0.335\) 因而适用于全段。特别是排除 \(5+1\) 的严格得分优势 \(1.36(2\pi h)^2\) 对每个正 \(h\) 都有效，允许它在 \(h\downarrow0\) 时趋于零。固定势的峰位定位及圆周次序的证明只依赖第一模下界、尾项上界和 \(0<2\pi h<0.44\)。在允许碰撞的 \(h=0\) 闭包中，需要另外使用带电块的可行双向平移；此前的端点证明同样只使用这些统一上界。

[紧双簇能量](packed-face.md)在 \(h\le1/8\) 随 \(y=1-\cos(2\pi t)\) 严格增加，且在 \(1/8\le h<1/6\) 对 \(y\) 严格凸。\([8,9]\) 的 nome 上界小于其假设 \(17/50\)。在后一个间距区间，两端的**归一化斜率**均随 \(h\) 和 \(s\) 分别严格递减。接触端的导数包括移动边界 \(z=3x-4x^3\) 对 \(x\) 的贡献。[临界曲线导数证明](width-referee.md)中 \(|z'|\le3\) 和尾和界 \(39H<16\) 同时覆盖两种边界。严格凸性保证两个临界值不同并正确归属各自的端点。这个一维结论需要与全域接触面排除合用。

## 连续宽度与接触面的覆盖

独立运行[连续宽度搜索](../../code/verify_six_site_width_strip.py)后，左、右两宽度段分别访问 40740、39056 个盒。从整数端点重建的参数域为 \([8,17/2]\cup[17/2,9]\)，每个宽度段分别覆盖 49 个间距区间。网格分母为 300000，从 21000 到 49800 按步长 600 包含 48 段，最后一段为 \([49800,50000]/300000\)。故 \(h=7/100\) 与解析证明相接，共同宽度端点 \(17/2\) 也在两侧闭段之内。

每个参数矩形有 18 棵接触支撑搜索树。在 32 个「第六间距最大」子集中，反射固定 8 个，故有 20 个代表，去掉目标闭边的两种支撑恰剩 18 个。即使有两个最大间距并列，仍可在原构型空间于严格松弛间距之间双向转移。归一化余量的转移速度含 \(1-6h\)，判号的必要条件用于 \(h<1/6\)。在 \(h=1/6\) 只有等间距可行。复算终止盒的计数为 5938 个分数排除、5823 个梯度排除、29019 个曲率排除，满足 \(2(5938+5823+29019)-2\cdot49\cdot18=79796\)。

设锚点为 \(m\)，\(c_m=\sqrt{\pi/m}\)，箱内工作核为
\[
 F_s(x)=c_m+2c_mq_m\sum_{n\ge1}q_s^{n^2-1}\cos(2\pi nx).
\]
此核与物理核 \(G_s\) 相差正比例及常数，且 \(F_m=G_m\)。沿 \(h\) 和余量坐标的分数变化使用扩宽后的 \(F_s'\) 区间，曲率使用扩宽后的 \(F_s''\)。在盒中心和试探中心各调用一次锚点标量插值。若单核宽度差至多 \(\epsilon_0\)，15 对的两次比较合计需 \(30\epsilon_0\)。代码从试探阈值中扣除了这一项。沿坐标盒内的线段使用 \(F_s'\) 时，线段端点共享宽度且满足同一总和约束，导数无需插值于不同宽度之间。严格导数排除仅针对被检支撑的相对内部，开支撑边界在自己的支撑上另受检验。完整分盒证明

另核过有理锚点的制表公式。写 \(m=A/B\)，像的位置为 \(v=k/M\)。乘以共同分母 \(B^2M^2\) 后，零、一、二阶导数的像乘子依次为 \(B^2M^2,-(2Ak)BM,(2Ak)^2-2ABM^2\)，与代码一致。每个舍弃像用 \(s\ge8\) 给出衰减、\(s\le9\) 控制多项式，宽度方向扩宽与位置方向的 Taylor 余量分别计入。

另外对两个锚点各取八个节点，包含端点、非对称点、半周期点及其邻点。独立计算 \(G_m,G'_m,G''_m\) 的 48 个区间，在主表中去除供非节点使用的 Lipschitz 余量后，逐一检验包含关系。这个抽查使用下文的独立指数算法和 11 个像。

## 宽度余量的独立上界

令当前闭段为 \([a,b]\)，中点 \(m=(a+b)/2\)。对 \(n\ge2\) 置 \(w=(n^2-1)\pi^2\)，\(f(s)=e^{-w/s}\)。因为
\[
 f'(s)=w f(s)/s^2>0,\qquad f''(s)=w(w-2s)f(s)/s^4>0,
\]
其中 \(w\ge3\pi^2>18\ge2s\)，故中点两侧的最大偏差统一出现在右端。可以只计算
\[
 f(b)-f(m)=e^{-w/b}\bigl(1-e^{-w(1/m-1/b)}\bigr).
\]
以下用独立的指数上下界计算 \(n=2,\ldots,7\) 的这一乘积。取 \(Q=17/50\)，利用 \(q(9)<Q\)，余下 \(r\) 阶空间导数的系数和至多
\[
 (16\pi)^r Q^{63}/[1-(9/8)^r Q^{17}],\qquad 0\le r\le2.
\]
乘以 \(2c_mq_m\) 后向上取整到 \(10^{-9}\) 单位。两个锚点依次得到 \((1156027,14580271,184224459)\)、\((1309984,16545550,209498224)\)，均不超过主程序使用的 \((1156027,14580271,184224460)\)、\((1309984,16545550,209498225)\)。这一估计连续覆盖所有宽度，而核值和物理能量阈值的独立检查分别验证实现及数值代表点。

## 以物理空间像和审核阈值

表中的五个宽度包括三个区间内点。逐点从物理能量的九个跨簇粒子对出发，独立检验阈值表的二十个有理端点。固定 \(h\)，写 \(b=1/2-3h\)。在中心计算 \(E_{tt}(h,0)\)，在接触边界计算 \(E_t(h,b)\)。两者分别是对应 \(y\) 端点斜率乘以正因子，后者用到 \(0<b<1/2\)。若 \(r=2\) 取 \(t=0\)，若 \(r=1\) 取 \(t=b\)，两种待判量同为

\[
\frac13\sum_{d=-2}^{2}(-1)^d(3-|d|)
              G_s^{(r)}(1/2+t+dh).
\]

函数及导数的定义直接来自 \(G_s(x)=\sum_p e^{-s(x+p)^2}\)。对 \(v=x+p\)，一、二阶乘子分别为 \(-2sv\) 和 \(4s^2v^2-2s\)。保留 \(-5\le p\le5\)，此处所有 \(x\in[0,1]\)，当 \(|p|=j\ge6\) 时两阶导数项均由 \([324(j+1)^2+18]\,2^{-8(j-1)^2}\) 控制。相邻主项的比至多 \((8/7)^2\,2^{-88}<1/2\)，两侧尾项至多 \(4(324\cdot7^2+18)2^{-200}\)。五个带符号权重的绝对值总和为 3，故把这个尾项乘 3 后加在最终和式两侧。

对每个指数自变量 \(z\ge0\)，取 \(M=2^{128}\)，\(u=z/M<1\)。由 \(1-u\le e^{-u}\le1/(1+u)\)，把两端平方 128 次得到 \(e^{-z}\) 的两侧界。每步在 \(10^{-90}\) 单位向外取整。这一检查从有理宽度和有理间距出发，计算全程没有使用 \(\pi\)、三角函数、Chebyshev 多项式或主程序的指数 Taylor 展开。

| \(s\) | \(10^{18}E_{tt}\)，中心阈值左、右端点 | \(10^{18}E_t\)，接触阈值左、右端点 |
|---|---|---|
| \(8\) | \([230,231],[-359,-358]\) | \([27,28],[-30,-29]\) |
| \(33/4\) | \([126,127],[-509,-508]\) | \([37,38],[-26,-25]\) |
| \(17/2\) | \([616,617],[-64,-63]\) | \([34,35],[-35,-34]\) |
| \(35/4\) | \([147,148],[-578,-577]\) | \([72,73],[-2,-1]\) |
| \(9\) | \([37,38],[-733,-732]\) | \([17,18],[-64,-63]\) |

## 中间相宽度的导数

令 \(\Delta=h_b-h_c\)。两条临界曲线都下降，仍须比较下降速度才能判定 \(\Delta'\) 的符号。对任一端点根写 \(P(q,x)=0\)，此处 \(x=\cos(2\pi h)\)，接触端的 \(P_x\) 是把 \(z=3x-4x^3\) 代入后的全导数。由 \(x_h=-2\pi\sin(2\pi h)\) 和 \(q_s=\pi^2q/s^2\) 得
\[
 h'(s)=\frac{\pi}{2s^2}\frac{qP_q}{\sin(2\pi h)P_x}.
\]
在第 \(n\) 项中令 \(A=2T_n(x)-1\)，则 \(\partial_x A^2=4nA U_{n-1}(x)\)。另一因子 \(U_{n-1}(z)\) 的导数从三项递推求得，链式法则在接触端另乘 \(3-12x^2\)。将 \(|A|\le3\)、\(|U_{n-1}|\le n\)、\(|U_{n-1}'|\le n(n-1)^2\) 代入，得到 \(P_x\) 每项的绝对界 \(39n^4 q^{n^2-1}\)，\(qP_q\) 对应的界为 \(9n^4 q^{n^2-1}\)。几何尾从第七项开始并在每个区间两侧加入。程序只在导数分母的区间严格为正后取倒数。

[相宽导数脚本](../../code/verify_six_site_strip_separation.py)沿宽度使用 32 个闭段 \([8+k/32,8+(k+1)/32]\)。按各根随宽度严格递减的已证结论，将右端根的下界和左端根的上界配成区间。nome 的上下界顺序相反，因为 \(q\) 递增。两项斜率相减后才乘共同正因子 \(\pi/(2s^2)\)；两条根的区间可以独立取值而仍包含同一宽度下的真实差。复跑得到 \(209555\cdot10^{-9}\le\Delta'\le734655\cdot10^{-9}\)，足以在整段严格定号。

在 \(s=17/2\) 另外以实空间核检验斜率。令 \(H\) 为前述物理判号量。中心根使用 \(G''\)，有 \(v_h=d\)。接触根使用 \(G'\)，有 \(v_h=d-3\)。在根处直接用 \(h'=-H_s/H_h\)；若 \(H\) 含随宽度或间距而变的正归一化因子，则求导后该因子的导数项乘以零。对保留的各像分别求宽度参数 \(s\) 和位置 \(v\) 的偏导，中心量的两种乘子为 \(-2+10sv^2-4s^2v^4\)、\(12s^2v-8s^3v^3\)，接触量为 \(-2v+2sv^3\)、\(4s^2v^2-2s\)。每项还乘原指数，位置导数须再乘 \(v_h\)。四个多项式绝对值在 \(|p|=j\ge6\) 均至多为 \(7000(j+1)^4\)。再次用 \(|v_h|\le5\)、权重绝对值之和为 3，便得到两种偏导共用的双侧尾项。对每个根，\(h\) 遍历已严格验证的整个 \(10^{-17}\) 宽区间。实空间计算给出
\[
10^{12}h_c'\in[-4062107312,-4062107311],\qquad
10^{12}h_b'\in[-3607080764,-3607080763],\qquad
10^{12}\Delta'\in[455026548,455026549].
\]

## 复算

下列有理证书归入一键重放。行中两个整数是阈值严格下界的分子，分母均为 \(10^{17}\)。右端分子各加一。

~~~python
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, floor

@lru_cache(None)
def negative_exp(z):
    levels, unit = 128, 10**90
    u = z/(2**levels)
    assert 0 <= u < 1
    lower = floor((1-u)*unit)
    upper = ceil(unit/(1+u))
    for _ in range(levels):
        lower = lower*lower//unit
        upper = (upper*upper+unit-1)//unit
    return F(lower, unit), F(upper, unit)

def image_derivative(s, h, order):
    assert 8 <= s <= 9 and order in (1, 2)
    signed_shift = F(1,2)-3*h if order == 1 else F(0)
    lo = hi = F(0)
    for d in range(-2, 3):
        x = F(1,2)+signed_shift+d*h
        assert 0 <= x <= 1
        charge = F((1 if d%2 == 0 else -1)*(3-abs(d)), 3)
        for p in range(-5, 6):
            v = x+p
            factor = charge*(-2*s*v if order == 1 else 4*s*s*v*v-2*s)
            a, b = negative_exp(s*v*v)
            lo += min(factor*a, factor*b)
            hi += max(factor*a, factor*b)
    assert F(8,7)**2 * F(1, 2**88) < F(1,2)
    tail = 3*4*F(324*7**2+18, 2**200)
    return floor((lo-tail)*10**18), ceil((hi+tail)*10**18)

for s, center, contact, expected in [
    (8, 13114680495074862, 13327908477025674, (230,-359,27,-30)),
    (F(33,4), 13002116216464920, 13228696963489349, (126,-509,37,-26)),
    (F(17,2), 12896949017617399, 13135593571511805, (616,-64,34,-35)),
    (F(35,4), 12798925229764372, 13048218048706585, (147,-578,72,-2)),
    (9, 12707787492004334, 12966203092650766, (37,-733,17,-64)),
]:
    actual = [image_derivative(s, F(n+k,10**17), order)
              for n, order in ((center,2),(contact,1)) for k in (0,1)]
    assert actual == [(v,v+1) for v in expected]
    assert all(actual[j][0] > 0 and actual[j+1][1] < 0 for j in (0,2))
    print(f's={s}: physical-space endpoint derivatives x 10^18 = {actual}')

from math import isqrt
import sys
sys.path.insert(0, "code")
from verify_six_site_global_reduction import GRID, UNIT, ceil_div, samples
from verify_six_site_width_strip import width_errors

def arctan_bounds(inverse):
    t = F(1, inverse)
    lo = sum((-1)**k*t**(2*k+1)/(2*k+1) for k in range(24))
    return lo, lo+t**49/49

a, b = arctan_bounds(5)
c, d = arctan_bounds(239)
pi_lo, pi_hi = 16*a-4*d, 16*b-4*c

def sqrt_upper(x):
    scale = 10**32
    return F(isqrt(floor(x*scale**2))+1, scale)

def width_bound(m, right, j):
    amplitude = 2*sqrt_upper(pi_hi/m)*negative_exp(pi_lo**2/m)[1]
    total = F(0)
    for n in range(2, 8):
        power = n*n-1
        endpoint = negative_exp(power*pi_lo**2/right)[1]
        spread = 1-negative_exp(power*pi_hi**2*(1/m-1/right))[0]
        total += (2*pi_hi*n)**j * endpoint * spread
    cap = F(17,50)
    assert negative_exp(pi_lo**2/9)[1] < cap
    tail = (16*pi_hi)**j*cap**63/(1-F(9,8)**j*cap**17)
    return ceil(UNIT*amplitude*(total+tail))

for left, right, expected in [
    (F(8), F(17,2), (1156027,14580271,184224459)),
    (F(17,2), F(9), (1309984,16545550,209498224)),
]:
    m = (left+right)/2
    verified = tuple(width_bound(m, right, j) for j in range(3))
    used = width_errors(left, m, right)
    assert verified == expected and all(x <= y for x, y in zip(verified, used))
    print(f's in [{left},{right}]: independent width errors {verified} in 1e-9 units')
    low, high = samples(exponent=m)
    indices = [0,1,127,GRID//4,GRID//2-1,GRID//2,GRID-23,GRID]
    assert len(set(indices)) == 8
    for k in indices:
        x = F(k,GRID)
        for j, cap in enumerate((4,20,150)):
            lower = upper = F(0)
            for p in range(-5,6):
                v = x+p
                multiplier = (1, -2*m*v, 4*m*m*v*v-2*m)[j]
                lo, hi = negative_exp(m*v*v)
                lower += min(multiplier*lo, multiplier*hi)
                upper += max(multiplier*lo, multiplier*hi)
            tail = 4*F(324*7**2+18, 2**200)
            pad = ceil_div(cap*UNIT, 2*GRID)
            assert low[j][k]+pad <= (lower-tail)*UNIT <= (upper+tail)*UNIT <= high[j][k]-pad
    print(f'anchor {m}: 24 independent image intervals inside unpadded table')

from verify_six_site_bifurcation import Interval, box

def physical_root_slope(s, h, center):
    ps = ph = box(0)
    for d in range(-2,3):
        velocity = d if center else d-3
        x = (F(1,2) if center else 1) + velocity*h
        assert 0 <= x.lo <= x.hi <= 1
        charge = F((1 if d%2 == 0 else -1)*(3-abs(d)),3)
        for p in range(-5,6):
            v = x+p
            z = s*v**2
            a = Interval(negative_exp(z.hi)[0], negative_exp(z.lo)[1])
            if center:
                ds = -2 + 10*s*v**2 - 4*s**2*v**4
                dx = 12*s**2*v - 8*s**3*v**3
            else:
                ds = -2*v + 2*s*v**3
                dx = 4*s**2*v**2 - 2*s
            ps += charge*ds*a
            ph += charge*velocity*dx*a
    assert F(8,7)**4 / 2**88 < F(1,2)
    tail = F(15*4*7000*7**4, 2**200)
    ps += Interval(-tail, tail)
    ph += Interval(-tail, tail)
    assert ph.hi < 0
    return -ps*Interval(1/ph.hi,1/ph.lo)

slopes = []
for n, center in ((12896949017617399,True),(13135593571511805,False)):
    h = Interval(F(n,10**17),F(n+1,10**17))
    slopes.append(physical_root_slope(F(17,2),h,center))
intervals = [(floor(v.lo*10**12),ceil(v.hi*10**12))
             for v in (slopes[0],slopes[1],slopes[1]-slopes[0])]
assert intervals == [(-4062107312,-4062107311),(-3607080764,-3607080763),
                     (455026548,455026549)]
print(f's=17/2: physical implicit slopes x 10^12 = {intervals}')
~~~
