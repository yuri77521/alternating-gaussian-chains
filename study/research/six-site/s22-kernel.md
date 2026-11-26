# 固定宽度 22 的紧块作用核

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

在 $s=22$、$h=1/1000$ 时，若两个可独立平移的接触块各有 $a,b$ 个粒子，且两块首粒子之间的有向距离为 $d$，则块间有符号配对和在乘上两首粒子的电荷乘积以前为

$$
K_{ab}(d)=\sum_{i=0}^{a-1}\sum_{j=0}^{b-1}(-1)^{i+j}
                 G(d+(j-i)h),\qquad
G(x)=\sum_{k\in\mathbb Z}e^{-22(x+k)^2}.
$$

在给定闭区间 $[l/D,r/D]$ 上，需要 $K_{ab}$ 及其前两阶导数的上下界，其中 $D=10^6$。若把含有两个紧邻异号粒子的块拆成多个独立的区间再相减，可能丢掉相差一个 $h$ 所带来的抵消，尤其在仅有一个接触时。下文先在节点合成带符号的块相互作用，再延伸到连续距离区间。[块核程序](../../code/six_site_s22_block_kernel.py)

## 周期节点及导数

令 $M=16000$，可整除式 $Mh=16$ 使每个簇内平移都落在节点上。在 $p=0,\ldots,M-1$，对 $p/M$ 及 $|k|\le3$ 的周期像，采用已有有理程序生成 $e^{-22m^2/M^2}$ 的上下界，其中 $m=p+kM$。相邻两项之比为 $e^{-22(2|m|+1)/M^2}$，比值本身每一步再乘 $e^{-44/M^2}$。首比值与递推因子用三、四阶交错 Taylor 展开夹住，乘法在 $10^{-32}$ 单位下向外舍入。[有理指数递推](../../code/verify_six_site_global_reduction.py)

把各像分别乘以 $1$、$-44m/M$、$(44m/M)^2-44$，即得零、一、二阶导数。设 $j=|k|\ge4$，每一阶的像绝对值均不超过 $[1936(j+1)^2+44]2^{-22(j-1)^2}$，相邻主项之比不超过 $(6/5)^2\,2^{-154}<1/2$。两侧无穷尾和小于 $4(1936\cdot5^2+44)2^{-198}<10^{-9}$。取 $U=10^9$，将节点值在 $1/U$ 单位下向外取整并加回尾界。程序存放所得区间的整数中点，对每阶分别检验全表最大半宽不超过三个单位。这里的半宽取距离两端中较大的一个。

## 合成与插值

在节点处按 $m=j-i$ 合并带符号整数系数 $w_m=\sum_{j-i=m}(-1)^{i+j}$，对第 $p$ 个节点，读取基本核表中 $p+16m\bmod M$ 的值。合成节点误差不超过基本表半宽乘 $\sum_m |w_m|$。这一步对两块首粒子间的全周期距离都有效。核的偶性与周期性给出 $K_{ab}^{(j)}(d)=(-1)^jK_{ba}^{(j)}(1-d)$，从而交换块长时无需另建表。

由 Fourier 展开，$q=e^{-\pi^2/22}<2/3$、$c=\sqrt{\pi/22}<2/5$。第一个不等式利用 $\pi>3$ 及指数在 $9/22$ 处的三阶正 Taylor 下界。记 $Q=2/3$，从第四个模态开始，相邻 $n^kQ^{n^2}$ 项的比值不超过 $(5/4)^kQ^9$。对于 $2\le k\le6$，有

$$
\|G^{(k)}\|_\infty\le\frac45(44/7)^k
\left(\sum_{n=1}^3 n^k Q^{n^2}
+\frac{4^kQ^{16}}{1-(5/4)^kQ^9}\right)\le M_k ,
$$

其中 $M_2,\ldots,M_6$ 依次取 $55,607,7931,117765,1933938$，均由整数及分数运算验证。要界定 $K_{ab}^{(j+2)}$，对偶数长度的一块将相邻异号项配对，得到 $a/2$ 或 $b/2$ 个步长为 $h$ 的一阶差分，按积分中值估计可多取得因子 $h$。两块都为偶数时可连续用两次。写 $e$ 为 $a,b$ 中偶数的个数，$v(a)=a$（奇）或 $a/2$（偶），则

$$
\|K_{ab}^{(j+2)}\|_\infty\le v(a)v(b)h^e M_{j+2+e}.
$$

在间隔 $1/M$ 的两个节点之间，线性插值的绝对误差至多为上式除以 $8M^2$。乘以 $U$ 并向上取整，再加节点误差后即可包围精确块核及其导数。在跨越多个节点的询问区间上，分段线性函数的极值只可能取于两端或内部节点。短区间直接在精确端点插值；较长区间用包含它的外侧两节点和中间节点统一取极值。后者的二幂长度区间预先制表，任一连续节点段均为两段等长区间的并，可直接返回最小值和最大值。所有返回的整数端点仍以 $1/U$ 为单位。

## 实空间交叉检查

为检测导数阶数、交换块长后的符号和跨周期索引，以下程序另行直接计算 $|k|\le2$ 的像。每一基本导数的遗漏量均小于 $4(1936\cdot4^2+44)2^{-88}$，指数项用缩小自变量、交错 Taylor 与八次向外平方夹住。对所有 $a+b\le6$ 的块长、前三个导数阶数，在指定闭区间的端点和中点检查了 630 次包含关系。此检查核对实现，连续域覆盖由上节插值误差保证。

~~~python
from fractions import Fraction as F
from functools import lru_cache
import sys
sys.path.insert(0, "code")
from six_site_s22_block_kernel import BlockKernel, D, UNIT
from verify_six_site_s22 import exp_interval, UNIT as scale

@lru_cache(maxsize=None)
def physical(order, d):
    x = F(d % D, D)
    tail = F(4*(1936*4**2 + 44), 2**88)
    # -2 <= k <= 2; first omitted distance >= 2, geometric ratio < 1/2.
    assert F(5,4)**2 * F(1,2**110) < F(1,2)
    lo, hi = -tail, tail
    for k in range(-2,3):
        y = x + k
        a,b = exp_interval(22*y*y)
        w = (1, -44*y, (44*y)**2 - 44)[order]
        lo += min(w*a,w*b)/F(scale)
        hi += max(w*a,w*b)/F(scale)
    return lo,hi

kernel = BlockKernel()
tests = 0
for a in range(1,6):
    for b in range(1,7-a):
        for j in range(3):
            for l,r in [(0,0),(1000,1100),(123457,123458),(248000,256001),
                        (499999,500001),(999999,1000000)]:
                low,high = kernel.get(a,b,j,l,r)
                for d in set((l,(l+r)//2,r)):
                    xlo = xhi = F(0)
                    for i in range(a):
                        for n in range(b):
                            lo,hi = physical(j,d+(n-i)*1000)
                            if (n+i)%2:
                                lo,hi = -hi,-lo
                            xlo += lo
                            xhi += hi
                    assert low <= UNIT*xlo <= UNIT*xhi <= high, (a,b,j,l,r,d,low,high)
                    tests += 1
print("Independent block kernel point checks passed:", tests)
~~~
