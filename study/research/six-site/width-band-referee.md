# Independent audit of the normalized width-band certificate

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

**Verdict.** For the complete six-site ordered per-particle Gaussian energy and $7.99\le s=\alpha L^2\le8.01$, the joint width-and-floor proof excludes every global minimizer outside the packed-triple edge for $1/10\le h=h_{\rm phys}/L<1/6$. Its small-floor argument covers the complementary interval $0<h\le1/10$, and $h=1/6$ has a singleton feasible set. The [monotone endpoint derivative theorem](width-referee.md) then gives both actual global transitions throughout the width band. I independently inspected and ran the [width checker](../../code/verify_six_site_width_band.py), the underlying [simplex checker](../../code/verify_six_site_global_reduction.py), and the exact Fourier check below. The restricted-width proof using unnormalized images gives further corroboration. [Unnormalized certificate](width-stability.md)

### Energy normalization and variation bounds

For $c_s=\sqrt{\pi/s}$ and $q_s=e^{-\pi^2/s}$ define $F_s=c_8+(c_8q_8/(c_sq_s))(G_s-c_s)$, with $G_s(d)=\sum_p e^{-s(d+p)^2}$. The ratio is positive. Also $\sum_{i<j}\sigma_i\sigma_j=-3$ is configuration independent. Thus the signed score of $F_s$ is a positive multiple of the signed score of $G_s$ plus a constant, and their maximizers coincide at each width. Self-image contributions to the full energy are also constant at fixed width. The physical energy remains the one with the full Gaussian image sum.

The normalized constant and first Fourier mode coincide at all widths. For $n\ge2$, $\partial_s q_s^{n^2-1}=(n^2-1)(\pi/s)^2 q_s^{n^2-1}$. Differentiation in the spatial argument $r$ times multiplies the bound by $(2\pi n)^r$. The ratio of the $n+1$ bound to the $n$ bound is at most $(3/2)^r(8/3)(0.292)^5$. The three factors using powers of $n$, $n^2-1$, and $q$ are each maximized at $n=2$. The width derivative is integrable uniformly across the parameter interval. The source checker obtains $\|F_s^{(r)}-G_8^{(r)}\|_\infty\le (42761,539098,6806367)_r10^{-9}$; each upper endpoint is rounded outward. The spectral endpoint calculation below independently gives smaller bounds for all three derivatives.

### Midpoint interpolation, trial comparisons and end cases

The scale-eight midpoint table and its Taylor interpolation continue to represent $G_8$, whereas the intervals for $G_s'$ and $G_s''$ after normalization represent $F_s',F_s''$. The width-dependent cut gradient, curvature, derivative with respect to the floor, and integration from a box center to a point use these widened intervals. At *one point* where the interpolated scalar value is used, one further uniform error of $\epsilon_0$ per pair is needed for $F_s$. Let $L_j$ be the returned lower bound for the $j$th trial before this correction, and $U$ the box's returned upper bound. The true signed trial score is at least $L_j-15\epsilon_0$ and the competitor is at most $U+15\epsilon_0$. Consequently $U<\max_j L_j-30\epsilon_0$ is sufficient. This exact threshold is used, with strict inequality and units consistent across the three enclosures.

The 14 floor intervals cover $[0.1,1/6]$, with ten intervals of length $.002$ before $.12$ and four later intervals. I reproduced the three error bounds and 6,068 box visits: 261 score exclusions, 377 cut-gradient exclusions and 2,522 cut-curvature exclusions. All 18 unwanted support types occur. Lower-dimensional supports have their own searches. The normalized cuts require $1-6h>0$ when translated into necessary optimality conditions; at the right endpoint only the equal-gap configuration exists. At lower floors the [maximal-block proof](block-translation-note.md) depends only on the checked upper bound $q<.292$. This supplies all positive floors, so no appeal to uniqueness at $h=0$ is needed.

### Independent exact Fourier difference check

The coefficients $q_s^{n^2-1}$ are increasing in $s$ for $n\ge2$, so their maximum deviation from scale eight occurs at one of the two width endpoints. The following check encloses the first five nonconstant differences individually, using rational endpoints for the exponentials. For $n\ge7$ the whole possible coefficient difference is bounded by $q_{8.01}^{n^2-1}$ and the tail by a geometric series. It uses the existing interval bounds for $\pi$, $c_8$ and $q_8$ and can be run from the repository root.

~~~python
from fractions import Fraction as F
import sys
sys.path.insert(0, "code")
from verify_six_site_bifurcation import PI, Interval, Q, C
from verify_stability import exponential_bounds
def nome(s):
    x = PI**2*(1/s)
    return Interval(exponential_bounds(x.hi)[0], exponential_bounds(x.lo)[1])
ql, qh = nome(F("7.99")), nome(F("8.01"))
for r, (expected, bound) in enumerate(zip([41980, 528998, 6675319],
                                          [42761, 539098, 6806367])):
    error = 0
    for n in range(2,7):
        k = n*n-1
        difference = max(qh.hi**k-Q.lo**k, Q.hi**k-ql.lo**k)
        error += n**r * difference
    tail_ratio = F(8,7)**r*qh.hi**15
    error += 7**r*qh.hi**48/(1-tail_ratio)
    high = 2*C.hi*Q.hi * (2*PI.hi)**r * error
    units = (high * 10**9).__ceil__()
    print(r, units)
    assert units == expected and units <= bound
~~~
