# 小间距能量的独立 Fourier 误差核算

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

2026-11-26。式 (14) 的严格下界、三个小扰动的能差符号及式 (13) 的物理单位均通过复核。独立计算从六个有序坐标构造 Fourier 电荷强度，用有理数运算给出下表。原脚本则在实空间逐像计算 Gaussian。复核时稿件和验证脚本的 SHA-256 前 12 位分别为 E756F1492598、A61F15914B88。

## 六点反例

在 $L=1,\ s=\alpha L^2=8,\ h=3/20$ 下，$Y=(0,3,6,10,13,16)/20$ 的间隙为 $(3,3,4,3,3,4)/20$，$X=(0,3,6,9,12,15)/20$ 的间隙为 $(3,3,3,3,3,5)/20$。两者满足同一间隙限制。独立的向外舍入区间如下。

| 量 | 下端点 | 上端点 |
|---|---:|---:|
| $E(Y)$ | 0.99239363714082433655 | 0.99239363714082433656 |
| $E(X)$ | 0.99109674409986065590 | 0.99109674409986065591 |
| $E(Y)-E(X)$ | 0.00129689304096368065 | 0.00129689304096368066 |

这验证了稿中的两个十一位小数能量区间及严格下界 $0.00129689$。另一组脚本示例取 $s=22,\ h=1/1000$，其 $E(Y)-E(X)$ 落在 $[0.00231609936918621072,\,0.00231609936918621073]$。该组宽度超出定理区间。

## 小扰动与单位

取 $s=9,\ L=1,\ h=10^{-6}$。间隙放宽时左簇从 $(0,h,2h)$ 变为 $(0,h+\delta,2h+\delta)$，其中 $\delta=h/100$。其有符号一阶矩为 $0-(h+\delta)+(2h+\delta)=h$，右簇固定。中点平移一项则使整个右簇平移 $\delta$。独立区间均为 $E_{\rm other}-E_{\rm packed}$。

| 变化 | 下端点 | 上端点 |
|---|---:|---:|
| 平移右簇 | $2.2133840961528\,10^{-16}$ | $2.2133840961529\,10^{-16}$ |
| 放宽左簇第一个间隙 | $1.0401592591955413\,10^{-13}$ | $1.0401592591955414\,10^{-13}$ |
| 两簇改为对跖的 $1+5$ | $1.040159259092364916\,10^{-11}$ | $1.040159259092364917\,10^{-11}$ |

$h$ 为当前周期的长度坐标，$\eta=2\pi h/L$。将同一归一化配置缩放到周期 $L$ 时，$s=\alpha L^2$ 固定，归一化坐标为 $x/L$。例如 $L=6,\ \alpha=1/4$ 对应这里的 $s=9$，算例间距变成 $6\cdot10^{-6}$。以物理长度为自变量，二阶和四阶系数分别乘 $L^{-2}$ 和 $L^{-4}$。

令 $A_2,A_4$ 是单位周期、以物理间距 $h$ 展开的系数。独立极限系数为 $A_4\in[-484.412441053589,-484.412441053588]$，而 $(E(h)-I-A_2h^2)/h^4\in[-484.412441050486,-484.412441050485]$。两者的差（有限间距商减极限系数）属于 $[0.0000000031028255,0.0000000031028256]$。角间距展开中，二阶及四阶系数须分别乘 $(2\pi/L)^2$、$(2\pi/L)^4$ 才能进行这种比较。

## 原脚本审查与实验范围

原证书对半径 $R$ 外的像取绝对值。若 $d=x_i-x_j$ 且 $|d|\le1$，对 $|p|\ge R+1$ 有 $|d+p|\ge |p|-1$。于是每一配置的能量尾项至多
\[
2N\sum_{j=R}^{\infty}2^{-s j^2}
 \le \frac{2N\,2^{-sR^2}}{1-2^{-s(2R+1)}}.
\]
$R=3$ 即稿中式 (14) 的公式。已逐项检查交错 Taylor 的 35/36 阶夹逼、非负端点向外平方、带符号区间加法与两份能量区间的下端减上端。导数脚本中的遗漏像 $j=|p|\ge6$ 满足 $|x+p|\ge j-1$、$|x+p|\le j+1$，四阶多项式的绝对值由 $C(j+1)^4$ 控制，$C=16s^4+48s^3+12s^2$，也覆盖所用的二阶导数。两侧余项由 $4C\,7^4\,2^{-25s}$ 控制。

Python 3.12.10 重跑原仓库命令，退出码为 0。9 个网格共 303,706 个有序间隙向量。每个网格的独立计数式为 $\binom{J-Nr+N-1}{N-1}$。固定种子的 8,475 次候选试探在 3 个宽度下共有 25,425 次比较。入围的连续配置中，像和 Fourier 能量的浮点差最大为 $2.220\cdot10^{-16}$。稿件正确区分了有理区间的严格不等式、有限网格或连续采样的浮点观察，以及需要解析定理的全局结论。能差为正只排除了指定的两个紧堆积三元组在该点为最优。最早转变位置和该反例处的全局最优配置仍待证明。

## 独立频域证书

取 $q=e^{-\pi^2/s}, c=\sqrt{\pi/s}$。以实际坐标和电荷构造
\[
B_n=6+2\sum_{j<i}(-1)^{i+j}\cos(2\pi n(x_i-x_j)),
\qquad E=1-\frac c3\sum_{n=1}^\infty q^{n^2}B_n.
\]
$0\le B_n\le36$，且本报告各参数满足 $q<16/25$。保留 $1\le n\le16$，省略项的能量绝对值由 $12(16/25)^{289}/[1-(16/25)^{35}]$ 控制。

附录以 Machin 恒等式及反正切交错级数验证 50 位 $\pi$ 下界 $P$。所有计算采用整数与分数。折叠到 $[0,\pi]$ 后，余弦近似的 Taylor 残差至多 $(22/7)^{66}/66!$。取 $z=P^2/s<5/4$，指数近似残差至多 $(5/4)^{56}/56!$。这两个余项均小于 $10^{-50}$。以 $D=10^{50}$ 定点向下舍入，加入 $\pi-P<D^{-1}$ 的影响后，余弦、$q$ 和 $c$ 的各近似误差均小于 $\epsilon=10^{-48}$。权重再舍入一次，故 $|\widehat w_n-q^{n^2}|\le(n^2+1)\epsilon$。因此保留项的能量绝对误差至多 $(16/3)(36+257\cdot37+36)\epsilon$。加尾项仍小于每份能量所用的 $10^{-42}$。

独立的物理系数由奇数模态求和得到 $A_2=(8/3)c(2\pi)^2\sum n^2q^{n^2}$ 和 $A_4=-(14/9)c(2\pi)^4\sum n^4q^{n^2}$。其尾和可按 $2\cdot17^4(16/25)^{289}$ 估计，因为 $n\ge17$ 时 $n^4(16/25)^{n^2}$ 的相邻比小于 $1/2$。有限和中的权重误差至多 $16\cdot16^4\cdot257\,\epsilon$。连同 $c$、$\pi$ 的输入误差与两式各自的因子，两个系数各取 $10^{-34}$ 的绝对半径足够。有限间距四阶商的半径为 $(2\cdot10^{-42}+10^{-34}h^2)/h^4$。

### 可执行见证

下列完整 Python 3 标准库代码可在独立目录运行，不读取被审查脚本或其辅助函数。最后的区间均按指定小数位向外舍入。

```python
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, isqrt

D = 10**50
P = F("3.14159265358979323846264338327950288419716939937510")
eps = F(1, 10**48)
energy_error, coeff_error = F(1, 10**42), F(1, 10**34)

def down(x):
    return F((D*x)//1, D)

def atan_sum(a, k):
    return sum(F((-1)**j, (2*j+1)*a**(2*j+1)) for j in range(k+1))

assert P < 16*atan_sum(5, 49)-4*atan_sum(239, 50)
assert 16*atan_sum(5, 50)-4*atan_sum(239, 49) < P+F(1,D)
assert F(22, 7)**66/factorial(66) < F(1,D)
assert F(5, 4)**56/factorial(56) < F(1,D)

@lru_cache(None)
def cosine(turns):
    t = 2*P*min(turns, 1-turns)
    term = value = F(1)
    for k in range(1, 33):
        term *= -t*t/((2*k-1)*(2*k))
        value += term
    return down(value)

@lru_cache(None)
def params(s):
    z = P**2/s
    assert z < F(5, 4)
    term = value = F(1)
    for k in range(1, 56):
        term *= -z/k
        value += term
    q = down(value)
    c = F(isqrt((P*D*D/s)//1), D)
    assert 0 < q-eps < q+eps < F(16, 25)
    return c, [down(q**(n*n)) for n in range(1,17)]

def energy(positions, s):
    c, weights = params(s)
    total = F(0)
    for n, w in enumerate(weights, 1):
        a = 6
        for i in range(6):
            for j in range(i):
                a += 2*(-1)**(i+j)*cosine(n*(positions[i]-positions[j])%1)
        total += w*a
    return 1-c*total/3

def bracket(label, mid, err, digits):
    scale = 10**digits
    lo, hi = ((mid-err)*scale)//1, -((-mid-err)*scale//1)
    def fmt(v):
        sign = "-" if v < 0 else ""
        a,b = divmod(abs(v), scale)
        return f"{sign}{a}.{b:0{digits}d}"
    print(label, f"[{fmt(lo)}, {fmt(hi)}]")

def coords(v, d):
    return [F(j, d) for j in v]

for s, d, y, x in [
    (8, 20, [0,3,6,10,13,16], [0,3,6,9,12,15]),
    (22, 1000, [0,1,2,500,501,502], [0,125,126,250,500,750]),
]:
    b, a = energy(coords(y,d),s), energy(coords(x,d),s)
    bracket(f"s={s} E(Y)", b, energy_error, 20)
    bracket(f"s={s} E(X)", a, energy_error, 20)
    bracket(f"s={s} E(Y)-E(X)", b-a, 2*energy_error, 20)

h, t = F(1,10**6), F(1,2)
base = [0,h,2*h,t,t+h,t+2*h]
e0 = energy(base,9)
for label, v in [
    ("shift", base[:3]+[v+h/100 for v in base[3:]]),
    ("release", [0,h+h/100,2*h+h/100]+base[3:]),
    ("1+5", [0]+[t+i*h for i in range(-2,3)]),
]:
    assert min(b-a for a,b in zip(v,v[1:]+[1])) >= h
    bracket(label, energy(v,9)-e0, 2*energy_error, 29)

c, weights = params(9)
a2 = F(8,3)*c*(2*P)**2*sum(n**2*weights[n-1] for n in range(1,17,2))
a4 = -F(14,9)*c*(2*P)**4*sum(n**4*weights[n-1] for n in range(1,17,2))
ei = energy([0,0,0,t,t,t],9)
q4 = (e0-ei-a2*h*h)/h**4
q4error = (2*energy_error+coeff_error*h*h)/h**4
bracket("A4", a4, coeff_error, 12)
bracket("Q4", q4, q4error, 12)
bracket("Q4-A4", q4-a4, q4error+coeff_error, 16)
```
