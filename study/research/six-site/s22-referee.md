# 宽度 22、间距下限 1/1000 的六粒子解独立复核

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

以下计算直接从完整实空间高斯像和出发。取 $h=1/1000$、$G(x)=\sum_{k\in\mathbb Z}\exp[-22(x+k)^2]$，给定带电位置 $p_i$ 与 $\sigma_i=(-1)^i$，有向每粒子能量为

$$
E=1-G(0)-\frac13\sum_{i<j}\sigma_i\sigma_jG(p_i-p_j).
$$

## 驻点与接触导数

紧三粒子簇中点取为零。考察位置 $p=(-h,0,h,u,1/2,1-u)$，其六个循环间隙为 $(h,h,u-h,1/2-u,1/2-u,u-h)$。将与 $u$ 有关的九个无序粒子对按圆周反射合并，令 $F=3E'(u)/2$，得到

$$
F(u)=G'(u-h)-G'(u)+G'(u+h)-G'(1/2-u)-G'(2u).
$$

反射配合保持符号的重标号将第四、第六个粒子互换，第五个粒子固定。于是 $F(u)=0$ 时三个自由粒子的力分别为零，两接触面上的全部切向导数也为零。在任一端点单独向外移动紧三粒子簇的该粒子，其余五个粒子固定，就打开该端一个接触。该可行方向的能量导数由粒子对逐项求导得到

$$
D_{\rm open}=\frac{G'(h)-G'(2h)+G'(u+h)-G'(u-h)+G'(1/2-h)}{3}.
$$

设 $u_-=0.249999032167246504146498709394$、$u_+=u_-+10^{-30}$。分别验证两端的 $F$ 符号相反，再将整个闭区间代入能量及开接触导数，得到

$$
\begin{aligned}
u_-&<u_*<u_+,\\
0.66503584451339086827047430&<E(u_*)<0.66503584451339086827047431,\\
0.02644726931591318017&<D_{\rm open}(u_*)<0.02644726931591318018 .
\end{aligned}
$$

## 两接触面上的局部唯一性

在 $(-h,0,h)$ 固定后，独立改变三个单粒子位置 $(p_3,p_4,p_5)$。分别以 $1/4,1/2,3/4$ 为中心、取半径 $1/1000$ 的闭立方体。设 $H$ 是此三维面上 $E$ 的 Hessian，则

$$
H_{ii}=-\frac13\sum_{k\ne i}\sigma_i\sigma_kG''(p_i-p_k),\qquad
H_{ij}=\frac13\sigma_i\sigma_jG''(p_i-p_j)\quad(i\ne j).
$$

置 $v=(1,4/3,1)$。以下程序对每一行验证 $H_{ii}v_i>\sum_{j\ne i}|H_{ij}|v_j$。经正对角相似变换的矩阵行严格对角占优，又与实对称矩阵 $H$ 同谱，故整个立方体内 $H$ 正定。对称根给出的点即为该立方体唯一的面内极小者。正的两个开接触导数还保证固定平移后的全五维可行域内为严格局部极小点。为见此，选左、右端粒子各自的开接触量和三个单粒子的绝对坐标作局部坐标。开接触导数在驻点附近保持正号，任一正释放量皆可单独缩回到零而降低能量，所有相邻松弛间隙仍为正。全局结论还须将其与完整构型空间的排除证明合用。

## 有理像和的误差

对 $x\in[-1,1]$，保留 $-5\le k\le5$。零、一、二阶导数的像乘子依次为 $1,-44z,1936z^2-44$，$z=x+k$。当 $|k|=m\ge6$ 时三者绝对值均小于 $2025(m+1)^2$。高斯因子小于 $2^{-22(m-1)^2}$。相邻上界的比至多为 $(8/7)^2 2^{-242}<1/2$，故计入两侧后任一导数的遗漏绝对值小于 $4\cdot2025\cdot49\,2^{-550}<10^{-150}$。

计算 $e^{-z}$ 时先令 $t=z/1024$。有限像有 $0\le t<1$，29、30 阶交错 Taylor 和分别给出下、上界。先变为 $10^{-68}$ 单位的整数区间，再向外舍入并连续平方十次。区间版导数同时包围像乘子和指数，未取样中点代替整段。以下检查只需开启断言的标准库 Python。

~~~python
from fractions import Fraction as Q
from functools import lru_cache

unit = 10**68
tail = Q(1, 10**150)
h = Q(1, 1000)
half = Q(1, 2)
assert 4 * 2025 * 49 * tail.denominator < 2**550

def point(x):
    return (x, x)

def add(x, y):
    return (x[0] + y[0], x[1] + y[1])

def scale(c, x):
    a, b = c*x[0], c*x[1]
    return (min(a,b), max(a,b))

def sub(x, y):
    return add(x, scale(-1, y))

def mul(x, y):
    vals = [a*b for a in x for b in y]
    return (min(vals), max(vals))

def square(x):
    a, b = x
    return (0 if a <= 0 <= b else min(a*a, b*b), max(a*a, b*b))

@lru_cache(None)
def decay(z):
    t = Q(z, 1024)
    assert 0 <= t < 1
    term = upper = Q(1)
    for j in range(1, 31):
        term *= -t/j
        upper += term
    lower = (upper - term) * unit
    upper *= unit
    a = lower.numerator // lower.denominator
    b = -(-upper.numerator // upper.denominator)
    assert a >= 0
    for j in range(10):
        a = a*a // unit
        b = -(-(b*b) // unit)
    return (Q(a,unit), Q(b,unit))

@lru_cache(None)
def kernel(order, x):
    assert -1 <= x[0] <= x[1] <= 1 and order in (0,1,2)
    result = (-tail, tail)
    for k in range(-5,6):
        z = add(x, point(k))
        z2 = square(z)
        e = (decay(22*z2[1])[0], decay(22*z2[0])[1])
        coeff = (point(1), scale(-44,z), add(scale(1936,z2),point(-44)))[order]
        result = add(result, mul(coeff,e))
    return result

def sum_boxes(terms):
    result = point(0)
    for coeff, value in terms:
        result = add(result, scale(coeff,value))
    return result

def symmetric_force(u):
    offsets = [(1,sub(u,point(h))), (-1,u), (1,add(u,point(h))),
               (-1,sub(point(half),u)), (-1,scale(2,u))]
    return sum_boxes((c,kernel(1,x)) for c,x in offsets)

u0 = Q("0.249999032167246504146498709394")
u1 = u0 + Q(1,10**30)
assert symmetric_force(point(u0))[1] < 0 < symmetric_force(point(u1))[0]
u = (u0,u1)
positions = [point(-h),point(0),point(h),u,point(half),sub(point(1),u)]
power = lambda i,j: (-1)**(i+j)
pairs = sum_boxes((power(i,j),kernel(0,sub(positions[i],positions[j])))
                  for i in range(6) for j in range(i))
energy = sub(sub(point(1), kernel(0,point(0))), scale(Q(1,3),pairs))
assert Q(".66503584451339086827047430") < energy[0] <= energy[1] < Q(".66503584451339086827047431")

normal_terms = [(1,point(h)), (-1,point(2*h)), (1,add(u,point(h))),
                (-1,sub(u,point(h))), (1,point(half-h))]
normal = scale(Q(1,3), sum_boxes((c,kernel(1,x)) for c,x in normal_terms))
assert Q(".02644726931591318017") < normal[0] <= normal[1] < Q(".02644726931591318018")

cube = positions[:3] + [(Q(i,4)-h,Q(i,4)+h) for i in (1,2,3)]
weights = (1,Q(4,3),1)
for i in (3,4,5):
    # Use 3H throughout, so no rounding enters the matrix normalization.
    curv = {j:scale(power(i,j),kernel(2,sub(cube[i],cube[j]))) for j in range(6) if j != i}
    diag_lo = -sum(t[1] for t in curv.values())
    radius = sum(weights[j-3]*max(abs(t[0]),abs(t[1]))
                 for j,t in curv.items() if j >= 3)
    assert diag_lo * weights[i-3] > radius
print("Independent width-22 root, energy, normal derivatives and Hessian passed.")

# Independent physical-space checks on the shared production interpolation tables.
import sys
sys.path.insert(0, "code")
from six_site_s22_block_kernel import BlockKernel, D, UNIT

production = BlockKernel()
samples = ((0,0), (0,7113), (123457,123457), (499970,500033),
           (747803,839103), (999971,D), (D,D))
compared = 0
for a in range(1,6):
    for b in range(1,7-a):
        for left,right in samples:
            for order in (0,1,2):
                low, high = production.get(a,b,order,left,right)
                for t in {Q(left,D),Q(left+right,2*D),Q(right,D)}:
                    # Reduce each distance modulo one before summing its images.
                    exact = sum_boxes(((-1)**(i+j),
                                       kernel(order,point((t+(j-i)*h) % 1)))
                                      for i in range(a) for j in range(b))
                    assert low <= UNIT*exact[0] <= UNIT*exact[1] <= high
                    compared += 1
assert compared == 675
print(f"{compared} independent signed block-interaction enclosures passed.")

# Contrast the independent continuous block atlas with the same direct image oracle.
import verify_six_site_s22_block_atlas as atlas
atlas.check_constants()
atlas_nodes = atlas.gaussian_nodes()
atlas_checks = 0
for a,b in ((1,1),(2,2),(3,1),(1,3)):
    table = atlas.BlockKernel(atlas_nodes,a,b)
    for left,right in samples:
        start = left * atlas.GRID // D
        end = -(-right * atlas.GRID // D)
        bounds = table.range(start,end)
        for order in (0,1,2):
            for t in {Q(left,D),Q(left+right,2*D),Q(right,D)}:
                truth = sum_boxes(((-1)**(i+j),
                                   kernel(order,point((t+(j-i)*h) % 1)))
                                  for i in range(a) for j in range(b))
                low,high = bounds[2*order:2*order+2]
                assert low <= atlas.UNIT * truth[0] <= atlas.UNIT * truth[1] <= high
                atlas_checks += 1
    table.range.cache_clear()
assert atlas_checks == 180
print(f"{atlas_checks} additional independent atlas image checks passed.")
~~~

最后的交叉检验用同一套独立实空间像和逐个生成簇间带符号作用，比较主程序查表返回的值、一阶及二阶导数包围。测试取全部 15 种有序块长组合，含相同块长与交换块长，位置覆盖两端、半周期附近、非网格节点及横跨多个插值网格的宽区间。在宽区间内另取其中点及两端，共进行 675 个精确有理像和比较。整段插值的严格性还依赖主程序对二阶插值余项的全域控制；这些逐点检查单独检验实现。

相同的直接像和还检验另一程序的独立核表。在 $(1,1),(2,2),(3,1),(1,3)$ 四种块长上，用该程序的 $32000$ 个网格段向外扩张同一批区间，三种导数阶数的 180 次包含关系均成立。[全支撑块坐标程序](../../code/verify_six_site_s22_block_atlas.py)
