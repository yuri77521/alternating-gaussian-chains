# \(s=9\) 全局相图的独立复核

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

## 接触支撑的覆盖

取 \(L=1\)。在 \(0<h\le7/100\) 的小间距证明中，弧积分给出 \(|P_2|\le4\)，结合对径试探得到 \(|P_1|>1.41\)。检查固定势的正负号可直接从两项恒等式 \(\cos(u-\eta/2)-\cos(u+\eta/2)=2\sin(u)\sin(\eta/2)\) 看出。正偶块的第一模峰位为 \(\pi/2\)，负偶块为 \(3\pi/2\)。驻点的斜率约束同时允许峰与谷，正二阶导数排除谷。四种容许弧不重叠且有固定的环上次序。只要出现奇块，其起始符号在奇块子序列中交替，所以正负奇块各至多一个。两个相邻奇块之间若夹有偶块，其所需峰位在另一条有向弧上。全偶情况则可把六点分成三个紧异号对，直接与第一模下界矛盾。五点块与单点的比较先在每个相对位置取上界，再利用恒等式 \(1+B(x)=2\cos x(2\cos x-1)\) 比较居中两种分割。这两步合起来覆盖偏心的 \(5+1\) 竞争者。复跑小间距脚本的全部有理断言通过。

在 \(1/20\le h<1/6\) 的接触面证明中，取最大余隙为第六个，其余五个指标的 \(32\) 个子集在反射下有 \(8\) 个不动者，共 \((32+8)/2=20\) 类。扣除一个单余隙顶点及一个对侧双余隙支撑，剩 \(18\) 类。最大余隙若并列，仍可在原可行域中双向转移两个严格为正的余隙，所以梯度和曲率检验依然成立。分数上界使用满足总和约束的盒中心，连接中心和候选点的线段留在坐标区间和总和超平面内。各分量位移的左右端点异号，因此梯度区间 \([a,b]\) 与位移区间 \([l,u]\) 的乘积上界可用 \(\max(0,la,ub)\)。五个试探的最优下界适用于整段 \(h\)。

独立运行大间距脚本得到 \(39\) 段、\(60182\) 个盒。按分数、梯度、曲率排除的叶数分别为 \(7328,4267,18847\)，合计 \(30442\)，满足 \(2(30442)-39(18)=60182\)。两证明在 \([1/20,7/100]\) 上重叠；\(h=1/6\) 单独由总长约束给出。去除全空间平移后，两种位移符号通过反射互换，循环重标三个粒子也会交换两簇。

若允许重合，零间距端点需重新检查。把相同坐标处的连续标签合为一组，包括跨周期接缝的一组。偶数组完全抵消，奇数组的贡献等于其起始符号乘固定势。每个不同坐标的组都可作小幅双向平移；带电组的峰位约束及其环上交替次序排除多于两个净电荷。剩下的一正一负若有相对偏移，第一模造成的损失系数大于所有高模可能补回的系数。故仅有对径净电荷达到极值，插入两组相消的异号粒子对仍有同一能量。此推导使用了零长弧的积分为零，适用于有中性组处在两个带电组之间的情形。

## 用实空间导数独立核对四个端点

临界间距证书用 Fourier 多项式计算 \(\Phi'_h\)。这里直接对物理像和求导。固定 \(h\)，与两簇相对位移 \(t\) 有关的九对粒子给出
\[
 E(h,t)=C(h)+\frac13\sum_{d=-2}^{2}(-1)^d(3-|d|)\,
 G_9\!\left(\tfrac12+t+dh\right).
\]
这里 \(C(h)\) 包含所有与 \(t\) 无关的项。取 \(r=2,t=0\) 检查中心曲率，取 \(r=1,t=1/2-3h\) 检查接触端的单侧斜率。由 \(y=1-\cos(2\pi t)\)，前一种导数是 \(\Phi'_h(0)\) 乘以正数，后一种是 \(\Phi'_h(y_b)\) 乘以正数。对每个像 \(v=x+p\)，导数乘子为 \(-18v\) 或 \(324v^2-18\)。保留 \(-5\le p\le5\)。对于 \(|p|=j\ge6\)，\(0\le x\le1\)，两个乘子与指数乘积的绝对值均至多 \([324(j+1)^2+18]2^{-9(j-1)^2}\)。相邻主项比小于 \(1/2\)，两个方向总尾项不超过 \(4(324\cdot7^2+18)2^{-225}\)。

| 判号量 | 左端 \(h\) | 左端导数乘以 \(10^{18}\) | 右端 \(h\) | 右端导数乘以 \(10^{18}\) |
|---|---|---:|---|---:|
| \(E_{tt}(h,0)\) | .12707787492004334 | \([37,38]\) | .12707787492004335 | \([-733,-732]\) |
| \(E_t(h,1/2-3h)\) | .12966203092650766 | \([17,18]\) | .12966203092650767 | \([-64,-63]\) |

这样以不同公式独立确认了两个 \(10^{-17}\) 宽区间的端点符号。每个根的唯一性仍由[端点导数的严格单调性](width-referee.md)保证。

## 用 Fourier 公式审查全部实空间表值

主程序以实空间像和建表。这里从 \(G_9=c+2c\sum_{n\ge1}q^{n^2}\cos(2\pi nx)\) 出发，\(c=\sqrt{\pi/9}\)。对 \(r=0,1,2\)，第 \(n\) 模的导数系数为 \(w_{n,r}=2c(2\pi n)^r q^{n^2}\)，相位增加 \(r\pi/2\)。仅取 \(n=1,\ldots,6\)，余项绝对值至多为
\[
 2c(2\pi)^r \frac{7^r q^{49}}{1-(8/7)^r q^{15}} .
\]
使用有理上界计算此式。令 \(M=8192\)，从第一象限两端的精确余弦 \(1,0\) 开始，以
\[
 \cos((a+b)/2)=\frac{\cos a+\cos b}{2\cos((b-a)/2)}
\]
逐层二分。每层的分母以平方根半角公式更新，再用对称性扩到整圆。由 \(r\pi/2\) 对应整数个格点，可用同一张余弦表处理两阶导数。程序在每个节点检查 Fourier 区间整个落入主程序的像和区间；比较前先移除原表供非节点使用的 Lipschitz 余量。所有 \(3(8192+1)=24579\) 次包含关系成立。节点外的导数界以及盒内的插值误差另由接触面证明控制。

下列标准库程序从仓库根目录运行。一键证书可直接执行该代码块。

~~~python
from fractions import Fraction as F
from math import ceil, floor
import sys
sys.path.insert(0, 'code')
from verify_stability import add_scaled, exponential_bounds
from verify_six_site_bifurcation import D, PI, OMEGA, Interval, box, sqrt_box
from verify_six_site_global_reduction import GRID, UNIT, ceil_div, samples

def kernel_derivative(x, order):
    assert 0 <= x <= 1 and order in (1, 2)
    result = F(0), F(0)
    for p in range(-5, 6):
        v = x + p
        w = -18*v if order == 1 else 324*v*v - 18
        result = add_scaled(result, w, exponential_bounds(9*v*v))
    tail = F(4*(324*7**2+18), 2**225)
    assert F(8, 7)**2 * F(1, 2**99) < F(1, 2)
    return result[0]-tail, result[1]+tail

def shift_derivative(h, order):
    t = F(1, 2)-3*h if order == 1 else F(0)
    result = F(0), F(0)
    for d in range(-2, 3):
        multiplicity = 3-abs(d)
        sign = 1 if d % 2 == 0 else -1
        result = add_scaled(result, F(sign*multiplicity, 3),
                            kernel_derivative(F(1, 2)+t+d*h, order))
    return floor(result[0]*10**18), ceil(result[1]*10**18)

for order, left, right, expected in (
    (2, '.12707787492004334', '.12707787492004335', ((37, 38),(-733, -732))),
    (1, '.12966203092650766', '.12966203092650767', ((17, 18),(-64, -63))),
):
    bounds = shift_derivative(F(left), order), shift_derivative(F(right), order)
    assert bounds == expected
    print(f'Image derivative of order {order}: {bounds} x 10^-18')

def audit_nodes():
    m = GRID
    assert m >= 4 and m & (m-1) == 0
    quarter = m//4
    cosine = {0: box(1), quarter: box(0)}
    step, arc_cos = quarter, box(0)
    while step > 1:
        arc_cos = sqrt_box((box(1)+arc_cos)*F(1,2))
        divisor = Interval(1/(2*arc_cos.hi), 1/(2*arc_cos.lo))
        for k in range(0, quarter, step):
            cosine[k+step//2] = (cosine[k]+cosine[k+step])*divisor
        step //= 2
    def full_cos(k):
        k %= m
        k = min(k, m-k)
        return cosine[k] if k <= quarter else -cosine[2*quarter-k]
    trig = [full_cos(k) for k in range(m)]
    c = sqrt_box(PI*F(1,9))
    exponent = PI**2 * F(1,9)
    q = Interval(exponential_bounds(exponent.hi)[0], exponential_bounds(exponent.lo)[1])
    assert q.hi < F(17,50)
    lower, upper = samples(exponent=9)
    cosine_int = [(int(v.lo*D), int(v.hi*D)) for v in trig]
    for r, cap in enumerate((4,20,150)):
        # Store interval endpoints as integers in the native Interval scale.
        weights = [2*c*q**(n**2)*(OMEGA*n)**r for n in range(1,7)]
        modes = [(int(w.lo*D), int(w.hi*D)) for w in weights]
        constant = c if r == 0 else box(0)
        tail = 2*c.hi*OMEGA.hi**r * 7**r*q.hi**49/(1-F(8,7)**r*q.hi**15)
        error = ceil(tail*D**2)
        pad = ceil_div(cap*UNIT, 2*m)
        for k in range(m+1):
            lo, hi = int(constant.lo*D)*D-error, int(constant.hi*D)*D+error
            for n,(wl,wh) in enumerate(modes,1):
                x,y = cosine_int[(n*k+r*quarter) % m]
                lo += min(wl*x,wh*x)
                hi += max(wl*y,wh*y)
            assert (lower[r][k]+pad)*D**2 <= lo*UNIT <= hi*UNIT <= (upper[r][k]-pad)*D**2
    print(f'Fourier intervals contained in all {3*(m+1)} unpadded image intervals')

audit_nodes()
~~~
