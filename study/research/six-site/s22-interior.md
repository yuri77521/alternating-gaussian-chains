# 无接触的六粒子构型不能是局部极小点

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

固定 $s=22$、$h=1/1000$，沿圆周的电荷为 $\sigma_j=(-1)^j$。若所有相邻间隙均严格大于 $h$，则任一粒子都能独立向两个方向移动充分小的距离。以下利用这个事实完全排除无接触支撑；其中也包括能量严格低于已知点 $X$ 的可行构型。[搜索与严格能量比较](s22-search.md)

**命题。** 此支撑的相对内部没有局部能量极小点。

**证明。** 记 $G(x)=\sum_{k\in\mathbb Z}e^{-22(x+k)^2}$，固定一个假设的极小点，并用其坐标定义 $V(x)=\sum_j\sigma_j G(x-x_j)$。能量极小等价于有向带符号核和 $S=\sum_{i,j}\sigma_i\sigma_jG(x_i-x_j)$ 极大。独立移动第 $i$ 个粒子时，自作用常数没有变化，而两个方向的配对各贡献一次。因此沿这个方向的二阶必要条件为

$$
0\ge \partial_{x_i}^2S=2\,[\sigma_i V''(x_i)-G''(0)] .
$$

写 $q=e^{-\pi^2/22}$、$c=\sqrt{\pi/22}$、$P_n=\sum_j\sigma_j e^{2\pi i n x_j}$。将 $V''$ 的 Fourier 展开截到 $n=2$，得到实三角多项式 $T$。设 $B=2c(2\pi)^2$，则

$$
-G''(0)=B\sum_{n\ge1}n^2q^{n^2}\ge B(q+4q^4),\qquad
\|V''-T\|_\infty\le 6B\sum_{n\ge3}n^2 q^{n^2}.
$$

上式只用了 $|P_n|\le6$。取 $q_- =63/100$、$q_+=64/100$，则 $q_-<q<q_+$。由相邻项之比递减，

$$
6\sum_{n\ge3}n^2 q^{n^2}
\le \frac{54q_+^9}{1-(4/3)^2q_+^7}
<q_-+4q_-^4 .
$$

于是截断误差小于 $-G''(0)$，每个粒子处都满足 $\sigma_i T(x_i)<0$。圆周上的六个互异点符号严格交替，六个开间隙内各自至少有一个零点。另一方面，乘以 $z^2$，其中 $z=e^{2\pi i x}$，可将二次三角多项式变为次数至多为四的普通多项式。上述严格符号已排除零多项式，故在圆周上至多有四个不同零点。矛盾。

下列标准库断言核对用到的全部数值不等式。高斯级数及所用导数绝对一致收敛，逐项求导成立。常数 $\pi$ 使用 $3.14<\pi<22/7$。

~~~python
from fractions import Fraction as F
import sys
sys.path.insert(0, "code")
from verify_stability import exponential_bounds

q_lower, q_upper = F(63, 100), F(64, 100)
assert exponential_bounds(F(22, 7)**2 / 22)[0] > q_lower
assert exponential_bounds(F(314, 100)**2 / 22)[1] < q_upper
ratio = F(4, 3)**2 * q_upper**7
assert ratio < 1
assert 54 * q_upper**9 / (1 - ratio) < q_lower + 4*q_lower**4
print("No-contact support: six alternating signs cannot occur in a degree-two trigonometric polynomial.")
~~~
