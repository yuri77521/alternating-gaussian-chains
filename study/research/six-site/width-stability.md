# Stability of the full six-site phase diagram on a width interval

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

**Theorem.** Let $s=\alpha L^2\in[7.995,8.005]$ and write $h=h_{\rm phys}/L$. For six alternating charges with the complete directed Gaussian interaction, all global minimizers at each $0<h\le1/6$ are cyclic shifts of two packed triples. The triple midpoints are antipodal for $0<h\le h_c(s)$. There are two reflected interior displacements for $h_c(s)<h<h_b(s)$. Five successive gaps equal $h$ for $h_b(s)\le h<1/6$. The sole feasible cell at $1/6$ is uniform. Both threshold functions are real analytic and have strictly negative derivatives in $s$ throughout this interval. At its endpoints the analytic functions have local analytic continuations. The classification of minimizers outside the certified interval requires separate estimates.

**中文摘要。** 固定六个粒子，允许无量纲参数 $\alpha L^2$ 在 $[7.995,8.005]$ 内变化，仍能确定每个正间距下限的全部全局极小构型。依次出现中点对径的双簇、互为反射的偏心双簇，以及五个连续间隙达到下限的排列。两个临界间距都随 $\alpha L^2$ 严格下降，并且是实解析函数。下文给出覆盖连续参数和完整构型空间的可复算证书。

## The two thresholds on the packed edge

For $q=\exp(-\pi^2/s)$ and $1/8\le h\le1/6$, put $x=\cos(2\pi h)$, $b=1/2-3h$, and $y=1-\cos(2\pi t)$, where $t$ is the signed displacement from antipodal midpoints. On $0\le y\le y_b=1-\cos(2\pi b)$ the signed energy, after subtracting its value at zero and dividing by a positive factor independent of $y$, is the function $\Phi$ in the [packed-edge analysis](packed-face.md). For $0<q\le17/50$ that analysis gives strict convexity here and unique centering for $0<h\le1/8$.

For each endpoint $y=0,y_b$, the derivative $\Phi_y$ is a function $P(q,x)$ with $P_x>0$ and $P_q<0$. In its Chebyshev series the second harmonic supplies the derivative bounds $16q^3$ from below for $\partial_x$ and $-6q^3$ from above for $q\partial_q$. After division by $q^3$ the respective absolute remainder bounds are $39H<16$ and $9H<6$, with $H=3^4(17/50)^5/[1-(4/3)^4(17/50)^7]$. Both endpoint derivatives are positive at $h=1/8$ and negative at $1/6$, where $y_b=0$. Since $dx/dh<0$, each has exactly one simple zero. The centered derivative vanishes first by strict convexity and $y_b>0$ in the interior. The normally convergent series is jointly real analytic in $q,x$. The analytic implicit-function theorem gives both curves, and $dh/dq=-P_q/P_h<0$. Also $dq/ds>0$. These assertions, with the individual tail estimates, hold throughout the stated $q$ range on the packed edge. [Independent derivation](width-referee.md)

The convex minimizer is $0$, the interior zero of $\Phi_y$, or $y_b$, according to the signs at the two endpoints. At the first critical curve the center is still the unique minimizer in $y$. Just above it the minimizing $y$ increases linearly to leading order because $\Phi_{yh}<0$ and $\Phi_{yy}>0$ there. As $y=2\pi^2t^2+O(t^4)$, the two signed branches emerge continuously with square-root order. The second critical curve belongs to the five-contact phase. Away from its two ends the interior displacement is jointly analytic in $h,s$.

## From the edge to the entire simplex

Normalize $L=1$. For $0<h\le1/25$ the [small-floor proof](early-global.md) uses only the upper bound $q\le0.292$. Its remainder estimates majorize each positive Fourier tail by evaluating it at that same rational upper bound. All subsequent constants and the comparisons after factoring out the powers of $h$ are uniform. This handles $h\downarrow0$ despite near-colliding neutral pairs.

For $1/25\le h<1/6$ use the normalized excesses $u_i=(g_i-h)/(1-6h)$, summing to one. Write $G_s(d)=\sum_{p\in\mathbb Z}\exp[-s(d+p)^2]$. Minimizing the physical energy is equivalent to maximizing the signed unordered 15-term score $Q_s=\sum_{i<j}(-1)^{j-i}G_s(x_j-x_i)$. For the exact hypotheses on each face, the sum constraints, trial choices, image tails and outward interval rounding, we use the full-simplex certificate. All distances are computed from $h,u$ independently of $s$. The first derivatives divided by $1-6h$ and the curvatures divided by $(1-6h)^2$ are signed sums of $G_s'$ and $G_s''$. In particular the expressions to enclose remain continuous at $h=1/6$. The divisors are used only for $h<1/6$.

At $s=8$ every nonempty terminal box that was discarded by a sign or value test has a strictly positive integer margin in units of $10^{-9}$. Geometry-only exclusions are width independent. There are finitely many boxes, so uniform continuity of the true normalized cuts, curvatures and trial differences already proves the qualitative persistence of all these exclusions for $s$ in an open neighborhood of 8. In taking a limit in $s$, one retains the original boxes with their true inequalities. No continuity of a rounding routine is needed. To obtain the larger interval in the theorem we subdivide again, allowing uniform kernel variation.

Let $c_s=\sqrt{\pi/s}$, $Q_0=0.292$. On $[7.995,8.005]$ we have $q<Q_0$, $c_s<0.63$ and $\pi^2/s^2<0.155$. The logarithmic width derivative of $c_sq^{n^2}$ for $n\ge1$ is $\pi^2n^2/s^2-1/(2s)$, positive since $2\pi^2>s$, and at most $0.155n^2$. Also $|c_s'|<0.04$. The Poisson series and its width and distance derivatives converge uniformly by the Gaussian Fourier tail. From $n=2$ onward, the ratio of successive $n^4Q_0^{n^2}$ is bounded by $(3/2)^4Q_0^5$. Thus
$$
 \sum_{n\ge1} n^4q^{n^2}\le Q_0+\frac{16Q_0^4}{1-(3/2)^4Q_0^5}<0.42 .
$$
The positive Fourier modes and their negative counterparts give at most $2(0.63)(0.155)(2\pi)^r(0.42)$ for the $r$th spatial derivative of $\partial_sG_s$, $0\le r\le2$. Add $0.04$ for the constant mode when $r=0$. The resulting suprema are smaller than $1/8,1,4$, respectively.

Set $\rho=0.005$. On every box use the original width-eight enclosures of $G_8',G_8''$ enlarged on each side by $\rho$ and $4\rho$. These enclose the derivatives at every width in the interval, and in particular at width eight. The Taylor and gradient score routines with these enlarged bounds still enclose the score at **width eight**, since their point evaluation uses $G_8$. Comparing a configuration with a trial at the same $h$ changes a difference of two scores by at most $30\rho/8$ as the width moves from 8 to $s$. Subtract this quantity, rounded upward in fixed-point units, from the best certified trial lower bound before excluding a box by its score. The 44 closed floor bands beginning at $1/25$ now exclude all 18 unwanted support representatives, allowing both single-slack vertices and the edge with two opposite slack gaps. At $1/6$ the gap sum itself gives the conclusion. Compactness gives existence at each positive floor. Combining this reduction with the packed-edge classification proves the theorem.

## Reproduction and a limitation of the enclosure

Execute the single Python block below from the repository root with assertions enabled. It uses the existing standard-library verifier at width eight. The exact integer comparisons also cover every real $s$ between the stated endpoints. The counts are 103,672 visited boxes, 16,047 score exclusions, 7,929 gradient exclusions and 28,256 curvature exclusions. With the same absolute error allowances scaled up to $\rho=0.01$, the first floor band $[0.040,0.042]$ left a terminal box unresolved for a slack gap adjacent to the largest one. This failure indicates loss of enclosure accuracy; the comparison at those wider widths remains a separate question for this method.

~~~python
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import factorial
from pathlib import Path
import sys

sys.path.insert(0, str(Path("code").resolve()))
import verify_six_site_global_reduction as cert

s_lo, s_hi = F("7.995"), F("8.005")
pi_lo, pi_hi = F("3.14"), F(22, 7)
q_max = F(".292")
z = pi_lo**2 / s_hi
assert q_max * sum(z**n / factorial(n) for n in range(8)) > 1
assert 2*pi_lo**2 > s_hi
assert pi_hi / s_lo < F(".63")**2 and F(".63")/(2*s_lo) < F(".04")
assert pi_hi**2 / s_lo**2 < F(".155")
assert q_max + 16*q_max**4 / (1-F(3, 2)**4*q_max**5) < F(".42")
c = 2*F(".63")*F(".155")*F(".42")
assert F(".04")+c < F(1, 8) and c*2*pi_hi < 1 and c*(2*pi_hi)**2 < 4

radius_units = 5_000_000
assert F(radius_units, cert.UNIT) == F(1, 200)

def verify_band(kernel, low, high):
    band = cert.Band(kernel, low, high)
    @lru_cache(maxsize=65536)
    def widened(order, span, a, b):
        bottom, top = band._get(order, span, a, b)
        assert order in (1, 2)
        pad = (1 if order == 1 else 4) * radius_units
        return bottom-pad, top+pad
    band.get = widened
    targets = []
    for part in range(5):
        x = part*cert.BARY//8
        trial = [0, 0, x, 0, 0, cert.BARY-x]
        grad = cert.terms(band, trial, trial, 1)
        targets.append(cert.center_value(band, trial, trial, grad)[0])
    target = max(targets) - cert.ceil_div(30*radius_units, 8)
    result = Counter()
    for size in range(1, 6):
        for active in combinations(range(5), size):
            reverse = tuple(4-k for k in reversed(active))
            if active != (2,) and active <= reverse:
                result.update(cert.search(band, active, target))
    band.get.cache_clear()
    band.at.cache_clear()
    return result

kernel = cert.Kernel()
ends = list(range(12000, 36000, 600)) + [36000, 40200, 42000, 45000, 50000]
assert cert.DEN == 300000 and len(ends) == 45
total = Counter()
for low, high in zip(ends, ends[1:]):
    total.update(verify_band(kernel, low, high))
assert [total[k] for k in ("boxes", "value", "gradient", "curvature")] == [
    103672, 16047, 7929, 28256
]
print("Uniform width certificate passed", dict(total))
~~~
