# 两对不共享粒子的接触给出统一能量下界

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

取 $s=22$、$h=1/1000$。若六粒子构型含两对不共享粒子的接触，则每粒子能量 **$E>0.66807$**。原始可行构型 $X$ 满足 $E(X)<0.667106810407357$，从而同时排除满足该接触条件的九种循环块长词。下面的证明适用于它们的整个闭面。[原始上界](s22-competitor.md) · 十二类接触表

令 $G(x)=\sum_{k\in\mathbb Z}e^{-22(x+k)^2}$，$S=\sum_{i,j}\sigma_i\sigma_jG(x_i-x_j)$，所以 $E=1-S/6$。实际删掉两对接触，留下两个异号粒子，其较短弧长记为 $r\le1/2$，写 $\delta=1/2-r$。只保留这两个粒子贡献的带符号核和为 $S_0=2G(0)-2G(r)$。对应六粒子归一化的辅助能量是 $E_0(r)=1+[G(r)-G(0)]/3$。

## 偶极项的符号

记 $K=44$。高斯的周期 Fourier 系数为正，故 $|G''(x)|\le-G''(0)<K$。下方断言核对 $G$ 在 $(0,1/2)$ 严格递减。偶性与周期性给出 $G'(0)=G'(1/2)=0$。一对接触本身对 $S$ 的贡献为 $2[G(0)-G(h)]\le Kh^2$。两对接触之间的相互作用是一项二重差分，两个积分长度均为 $h$。计入两个方向，其绝对值至多 $2Kh^2$。两对的自身及相互作用合计至多 $4Kh^2$。

剩下的两个粒子把圆周割成弧长为 $u=r$ 和 $u=1-r$ 的两段。沿任一弧，自起点开始记坐标为 $v$。若弧起点带电 $\tau$，终点就带电 $-\tau$，弧内的每个被删接触对依次带 $-\tau,+\tau$。这是因为弧上它之前的被删粒子都成对出现。定义 $\Phi_u(v)=G(v)-G(u-v)$。一对接触的左端若在 $v$，它与两个保留粒子的无序交叉和就是 $\Phi_u(v+h)-\Phi_u(v)$。导数为

$$
\Phi'_u(w)=G'(w)+G'(u-w),\qquad v\le w\le v+h.
$$

若两个自变量都不超过 $1/2$，则两项均非正。否则只有一个自变量超过 $1/2$，且至多超出 $\delta$，因为 $u\le1/2+\delta$。该项由 $G'(1/2)=0$ 和 $|G''|<K$ 控制在 $K\delta$ 以下。故每对的无序交叉和至多 $Kh\delta$。将两对及两个方向都计入，

$$
S\le S_0+4Kh\delta+4Kh^2 .
$$

若将两项 $G'$ 分开取绝对值，就会在对径情形 $\delta=0$ 丢失准确的符号，只得到随 $h$ 一次下降的粗界。上式保留弧的方向，因此可以用位移的二次能量代价补偿交叉项。

## 剩余异号对的位移代价

当 $1/4\le r\le1/2$ 时，$G''>1$，从 $1/2$ 积分两次得 $G(r)-G(1/2)\ge\delta^2/2$。当 $0\le r\le1/4$，单调性及 $G(1/4)-G(1/2)>1/8\ge\delta^2/2$ 给出同一结论。于是配方得到

$$
E\ \ge\ E_0(1/2)+\frac{\delta^2}{6}-\frac{2Kh\delta}{3}-\frac{2Kh^2}{3}
\ \ge\ E_0(1/2)-\frac{2K^2+2K}{3}h^2>0.66807 .
$$

删对条件只取决于接触是否共享粒子。九种循环块长词 $6,33,42,51,222,321,411,2121,2211$ 均可选出这样的两对。其他三类恰为无接触、单接触及相邻两接触，定点全局证明继续处理这些面。另一套全接触枚举对上述九类只作能量排除，共 30 个叶盒，提供独立核对。全域枚举

下列断言用现有实空间有理像和程序包住完整闭区间。由 $G''<0$ 于 $[0,1/10]$、$G'<0$ 于 $[1/10,1/4]$、$G''>1$ 于 $[1/4,1/2]$ 及两个对称端点的零导数，即得证明所用的严格单调性。像和及尾界

~~~python
from fractions import Fraction as Q
import sys

sys.path.insert(0, "code")
from verify_six_site_s22_local import kernel

h = Q(1, 1000)
half = Q(1, 2)
quarter = Q(1, 4)
K = 44
assert -kernel(Q(0), Q(0), 2)[0] < K
for j in range(500):
    left, right = j*h, (j+1)*h
    if j < 100:
        assert kernel(left, right, 2)[1] < 0
    elif j < 250:
        assert kernel(left, right, 1)[1] < 0
    else:
        assert kernel(left, right, 2)[0] > 1

at_half = kernel(half, half, 0)
assert kernel(quarter, quarter, 0)[0] - at_half[1] > Q(1, 8)
base = 1 + (at_half[0] - kernel(Q(0), Q(0), 0)[1])/3
assert base - (2*K**2 + 2*K)*h**2/3 > Q(66807, 100000)
print("Two disjoint contacts: E > 0.66807 on all nine closed faces.")
~~~
