# 六粒子全间隙单纯形的独立复核

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

**结论。** 取 $N=6,L=1,\alpha=8$。对 $1/50\le h<1/6$，每个全局能量极小点均由两个间距恰为 $h$ 的紧三元簇构成。两个外间隙中可以有一个也达到下限；在临界闭区间 $I=[0.13114,0.13115]$ 中两者都严格松弛。$h=1/6$ 时六个间隙都等于 $1/6$。本报告逐项审查并复跑了 54 段主证书，另以独立的 Fourier 有理数程序重复认证临界带与接近单纯形退化端点的三个参数带。

## 物理能量、支持与可行变分

令 $g_i=x_{i+1}-x_i$，$x_6=x_0+1$，$S=1-6h>0$，$u_i=(g_i-h)/S$。除去平移后，$u$ 遍历整个闭单纯形。物理能量中的六个对角项各为 $G(0)$，其余每对计两次，因此对无序对和 $Q=\sum_{i<j}(-1)^{j-i}G(x_j-x_i)$ 有
$$
E=1-G(0)-Q/3 .
$$
全局极小 $E$ 等价于全局极大 $Q$。$Q$ 允许为负；严格排除顶点所需的不等式为 $Q_{\rm vertex}<Q_{\rm trial}$。

六个坐标至少有一个最大且严格为正。循环重编号可令它为 $u_5$，其中奇数位移只将全部电荷同时反号。反射 $x_i\mapsto -x_{5-i}$ 保持成对乘积，把前五个间隙的下标送到 $4-i$ 并固定间隙 $5$。对 $A=\{k<5:u_k>0\}$ 的 $32$ 个子集，反射不动的有 $2^3=8$ 个，因为只须选两对互换下标和一个中间下标。故有 $(32+8)/2=20$ 个轨道。宽区间保留 $\varnothing$ 和 $\{2\}$，每段需排除 $18$ 个；在 $I$ 上只保留 $\{2\}$，需排除 $19$ 个。若两个或更多间隙并列最大，可任选其一。实际的小扰动可以离开这一个“最大间隙”区域，仍在原单纯形内。

在支持的相对内部，$k\in A$ 时方向 $e_k-e_5$ 可双向移动；任意 $k,\ell\in A$ 的 $e_k-e_\ell$ 也可双向移动。第 $ij$ 对的跨度为
$$
d_{ij}=(j-i)h+S\sum_{i\le a<j}u_a .
$$
记 $b_{ij,k}=\mathbf 1_{i\le k<j}$。沿第一种方向，一阶和二阶导数分别是带号核导数和乘 $S b_{ij,k}$、$S^2b_{ij,k}$ 后求和。沿第二种方向，二阶系数为 $S^2(b_{ij,k}-b_{ij,\ell})^2$，对应两个受影响对集合的对称差。全局极大必要条件是一阶导数为零、二阶导数非正。严格正曲率即排除极大，即使一阶导数区间横跨零。某支撑盒碰到 $u_k=0$ 的端点时，这个测试仅排除其相对内部；端点另属更小的支持。仅余 $u_5>0$ 的顶点在宽区间属于允许的闭边端点，在 $I$ 上单独比较。连续能量在紧单纯形上取到最小值。$h=1/6$ 处不宜除去因子 $S,S^2$，也无须定义 $u$。此时 $g_i\ge1/6$、$\sum g_i=1$ 唯一决定均匀构型；末段的导数检验只用于 $h<1/6$。

## 物理像和证书的数值审查

复跑[主程序](../../code/verify_six_site_global_reduction.py)并核对证明的覆盖规则。Python 3.12.10，运行命令为 `python -B code/verify_six_site_global_reduction.py`，复核版本 SHA-256 为 `4343155e67425439ef884c2ec2ed5cb47b9040f7676c74081572dad05f1bb02a`。所有计数均来自本次复跑。

| 主程序范围 | 盒数 | 严格分数比较叶 | 非零梯度叶 | 正曲率叶 |
|---|---:|---:|---:|---:|
| $[1/50,1/6]$，54 段合计 | 186,266 | 38,660 | 15,335 | 39,624 |
| 窄带 $I$ | 129 | 2 | 0 | 72 |

通分为 $300000$ 后，前 $50$ 个闭段从分子 $6000$ 到 $36000$，步长 $600$；再依次接到 $40200,42000,45000,50000$。它们首尾相接，端点分别恰为 $1/50$ 和 $1/6$。前者含 $54\cdot18=972$ 个二叉树根、$93619$ 个终端，满足 $2\cdot93619-972=186266$。窄带的分子端点为 $39342,39345$，$19$ 个根、$74$ 个终端也满足同一恒等式。宽带内试探点的 $u_2$ 分别为 $0,1/8,1/4,3/8,1/2$，各自都对该段全部 $h$ 可行，各试探下界的最大值仍是最优分数在整段的下界。

格点分母取 $M=8192$，核值尺度取 $V=10^9$。下列界覆盖所有参数带及所有非格点位置。

- 指数采样以 $R_m=e^{-8(2m+1)/M^2}$、$e_0=1$ 开始，$e_{m+1}=e_m R_m$，$R_{m+1}=R_m e^{-16/M^2}$。对两个起始因子用三、四次交错 Taylor 多项式夹住，乘除均以整数向外取整。于是取到 $|m|=4M$ 的端点也有效。乘 $-16y$ 和 $256y^2-16$ 时上下界随符号交换。
- 对 $0\le x\le1$、$|k|=r\ge4$，前三个核 $G,G',G''$ 的单项绝对值均小于 $272(r+1)^2\,2^{-8(r-1)^2}$。该上界的相邻比从 $r=4$ 起小于 $1/2$，计入双侧和后总余尾至多 $4\cdot272\cdot25\cdot2^{-72}<6\cdot10^{-18}$。程序加减 $1/V$ 包含它。
- 取 $q=e^{-\pi^2/8}<3/10$、$2c=2\sqrt{\pi/8}<13/10$，记 $R=3/10$。Poisson 公式给出 $j=1,2,3$ 时的全域导数上界
  $$
  \|G^{(j)}\|_\infty\le\frac{13}{10}(44/7)^j
  \left(R+\frac{2^jR^4}{1-(3/2)^jR^5}\right).
  $$
  这三个有理数分别小于 $2.59,17.09,117.96$。因此距最近节点至多 $1/(2M)$ 时，采用 $4,20,150$ 的 Lipschitz 常数均安全。区间段的两个重叠、等长的二进制区块覆盖了全部节点。距离对部分间隙和单调，其对 $h$ 的导数可以变号；用两个 $h$ 端点取较小/较大值即覆盖这一情形。
- 像和节点的未加 Lipschitz 余量的整数区间宽度至多 $4$，程序逐节点检查。其整数中点偏差至多 $2$ 个单位。对 $G$ 在最近节点做一阶 Taylor 展开，函数值误差为 $2$，斜率误差至多 $2/(2M)$，整数乘除产生的误差小于 $1$，二阶余项不超过 $20V/(8M^2)$。逐对预留 $4+\lceil20V/(8M^2)\rceil$ 个单位足够。
- 修正区域中心使之满足仿射和约束时，每一分量仍在本盒内。就算中心不满足最大间隙排序，连向真实候选点的线段仍在同一盒与同一和超平面内；部分间隙和的界只用到了它们。固定中心后，$\partial_h d_{ij}=j-i-6\sum_{i\le k<j}u_k$，程序先乘带号导数区间再取绝对上界，乘所在参数带的半宽覆盖全段。固定 $h$ 时沿线段积分，以区间导数分别乘允许的正负位移；取两端乘积及零的最大值就是该坐标的收益上界。乘最大松弛量 $S$ 后向上取整，得到候选 $Q$ 的上界。试探点也使用同一参数导数估计。

## 独立的 Fourier 全支持证书

为检验同一结论，下面的程序使用四个 Fourier 模式、全部 $31$ 个非目标支持和一种不同的盒收缩。它没有导入主程序，也不需要像和表、中心插值或沿盒积分。令
$$
K(d)=\sum_{n\ge1}q^{n^2}\cos(2\pi n d),\qquad
\widetilde Q=\sum_{i<j}(-1)^{j-i}K(d_{ij}).
$$
$G=c+2cK$，故两个构型间的 $Q$ 差为 $\widetilde Q$ 差乘 $2c>0$。对 $m=0,2$ 检验 $K^{(m)}(d)/(2\pi)^m$；余尾用首个遗漏项 $5^m R^{25}$ 除以 $1-(6/5)^mR^{11}$。Machin 公式和指数的相邻 Taylor 和提供有理数权重端点。各模式在距离区间的余弦范围由两个端点及其中全部整数、半整数周的极值给出。计算端点时，折至第一象限、将 $\pi$ 向上近似至 $10^{-12}$、取十六次余弦 Taylor 和。带入角误差小于 $1/(2\cdot10^{12})$，Taylor 余项小于 $10^{-12}$，最终取整误差小于 $10^{-12}$，总共向两端各扩三个单位。

这里只在前五个 $u$ 坐标上二分，第六个坐标恒为 $1-\sum_{k<5}u_k$。以 $B=65536$ 为坐标单位，记已有下限和 $s=\sum l_k$、最大下限 $m_0=\max l_k$。由 $u_k\le u_5$，第 $k$ 维上界可缩到 $\lceil(B-s+l_k)/2\rceil$，也可缩到 $B-s+l_k-m_0$。部分间隙和的第二个上界来自从单位总和中扣除该部分之外的已知下界和第六间隙的下界。二分共用中点，端点仍属于覆盖；$B$ 仅编码盒端点，盒内 $u$ 可取任意实数。距离对 $h$ 与部分间隙和是双仿射函数，在四个角上取极值。

| 独立复算项目 | 结果 |
|---|---:|
| 逐一处理的非目标支持 | 31 |
| 盒总数（含单松弛顶点） | 1,987 |
| 由 $e_k-e_5$ 方向正曲率排除的叶子 | 1,008 |
| 由试探值排除的叶子 | 1 |
| 由不可行性排除的盒 | 0 |
| 全部曲率叶中，所用方向最小的已证正下界，除去 $S^2(2\pi)^2$，按 $\widetilde Q$ 计 | $136645045\cdot10^{-12}$ |
| $\inf_I\widetilde Q_{\rm trial}-\sup_I\widetilde Q_{\rm vertex}$ 的下界 | $495546578\cdot10^{-12}$ |

曲率排除覆盖了 $30$ 个非空非目标支持。顶点的上界与居中试探的下界分别是 $-820803398584\cdot10^{-12}$ 和 $-820307852006\cdot10^{-12}$。这两个检验独立证实了 $I$ 上的全空间约化。结合[紧三元簇面内的形状定理](packed-face.md)，临界点 $h_c$ 两侧得到全空间居中、偏心极小的分类。对 $[0.134,0.14]$、$[0.14,0.15]$、$[0.15,1/6]$，同一 Fourier 程序还直接复核了每一段的 $30$ 个非空非目标支持，分别用 $841,389,90$ 个正曲率叶封闭。顶点在这三个区间作为允许的边端点保留，$h=1/6$ 的唯一性由上文单点论证给出。较小参数 $0<h<1/50$ 的结论另有[小间隙分析证明](early-global.md)，本报告的主证书审查以 $h=1/50$ 为下限。

### 可复算代码

以下为独立运行的 Python 3 标准库程序。末尾断言逐段固定覆盖计数和严格余量。

~~~python
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import factorial

U, B = 10**12, 2**16
DEN = 300000
D, P = DEN * B, 3141592653590
floors = (3*13114, 3*13115)

def floor(x):
    return x.numerator // x.denominator

def ceil(x):
    return -floor(-x)

def atan_pair(d):
    low = sum(F((-1)**k, (2*k+1)*d**(2*k+1)) for k in range(16))
    return low, low + F(1, 33*d**33)

a, b = atan_pair(5), atan_pair(239)
assert F(P-1,U) < 16*a[0]-4*b[1] <= 16*a[1]-4*b[0] < F(P,U)

def exp_sum(x, m):
    return sum((-x)**k / factorial(k) for k in range(m+1))

ql = exp_sum(F(P,U)**2 / 8, 27)
qh = exp_sum(F(P-1,U)**2 / 8, 26)
R = F(3,10)
assert 0 < ql < qh < R
weights = [(floor(U*ql**(n*n)), ceil(U*qh**(n*n))) for n in range(1,5)]
tail = {m: ceil(U*5**m*R**25/(1-F(6,5)**m*R**11)) for m in (0,2)}
assert F(8,5)**18 / factorial(18) < F(1,U)

@lru_cache(None)
def quadrant_cos(t):
    z = F(2*P*t, U*D)
    term = total = F(1)
    for k in range(1,9):
        term = -term*z*z/((2*k-1)*(2*k))
        total += term
    return floor(U*total)

def cosine(t):
    t %= D
    t = min(t, D-t)
    return quadrant_cos(t) if t <= D//4 else -quadrant_cos(D//2-t)

def cosine_range(a, b):
    endpoints = cosine(a), cosine(b)
    neg_peak = (a+D//2-1)//D < (b+D//2)//D
    pos_peak = (a-1)//D < b//D
    return (-U if neg_peak else min(endpoints)-3,
             U if pos_peak else max(endpoints)+3)

@lru_cache(None)
def kernel(m, span, a, b):
    ds = [span*h*B+(DEN-6*h)*x for h in floors for x in (a,b)]
    low, high = -tail[m], tail[m]
    for n, (wl,wh) in enumerate(weights, 1):
        vl,vh = cosine_range(n*min(ds)+m*D//4, n*max(ds)+m*D//4)
        corners = [w*v*n**m for w in (wl,wh) for v in (vl,vh)]
        low += min(corners)//U
        high -= (-max(corners))//U
    return low,high

pairs = [(i,j,(-1)**(j-i)) for j in range(1,6) for i in range(j)]

def pair_bounds(m, lo, hi):
    bounds = []
    for i,j,sgn in pairs:
        a = sum(lo[i:j])
        b = min(sum(hi[i:j]), B-max(lo)-sum(lo[:i])-sum(lo[j:]))
        x,y = kernel(m,j-i,a,b)
        bounds.append((x,y) if sgn==1 else (-y,-x))
    return bounds

compar = [0,0,B//2,0,0]
vertex = [0]*5
trial_lo = sum(x for x,y in pair_bounds(0,compar,compar))
vertex_hi = sum(y for x,y in pair_bounds(0,vertex,vertex))
assert trial_lo > vertex_hi

def cover(A):
    stack = [([0]*5, [B//2 if k in A else 0 for k in range(5)])]
    boxes = leaves = empty = 0
    weakest = None
    while stack:
        lo,hi = stack.pop()
        boxes += 1
        s = sum(lo)
        if s+max(lo) > B:
            empty += 1
            continue
        for k in A:
            hi[k] = min(hi[k], (B-s+lo[k]+1)//2, B-s+lo[k]-max(lo))
        assert all(x<=y for x,y in zip(lo,hi))
        lbs = [x for x,y in pair_bounds(2,lo,hi)]
        best = max(sum(x for x,(i,j,_) in zip(lbs,pairs) if i<=k<j) for k in A)
        if best > 0:
            leaves += 1
            weakest = best if weakest is None else min(weakest,best)
            continue
        k = max(A, key=lambda t: hi[t]-lo[t])
        assert hi[k]-lo[k] > 1
        mid = (lo[k]+hi[k])//2
        lh,rl = hi.copy(),lo.copy()
        lh[k],rl[k] = mid,mid
        stack.extend([(lo,lh),(rl,hi)])
    return boxes, leaves, empty, weakest

def run_faces():
    trees = [cover(A) for n in range(1,6) for A in combinations(range(5),n)
             if A != (2,)]
    assert len(trees)==30 and sum(t[2] for t in trees)==0
    return sum(t[0] for t in trees), sum(t[1] for t in trees), min(t[3] for t in trees)

assert run_faces() == (1986, 1008, 136645045)
assert trial_lo-vertex_hi == 495546578
print('critical band',trial_lo,vertex_hi)
for floors,expected in [((40200,42000),(1652,841,121716939)),
                        ((42000,45000),(748,389,1357543271)),
                        ((45000,50000),(150,90,3387437373))]:
    kernel.cache_clear()
    result = run_faces()
    assert result == expected
    print(floors, result)
~~~
