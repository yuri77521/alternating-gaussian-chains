# Width stability and the motion of the two transition floors

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

Write $s=\alpha L^2$, normalize lengths by $L$, and set $q=e^{-\pi^2/s}$. This note gives an independent derivative estimate for the two thresholds on the packed-triple edge, then audits the transfer of the full-simplex result to nearby widths.

## Two simple, decreasing thresholds on the packed edge

For every $0<q\le Q=17/50$, there are unique numbers $1/8<h_c(q)<h_b(q)<1/6$. On the two-packed-triple edge the minimizing shifts are zero for $h\le h_c$, a reflected interior pair for $h_c<h<h_b$, and the two endpoints for $h_b\le h<1/6$. Both critical floors vary real analytically and strictly decrease with $q$ and with $s$. Real analyticity at $Q$ means local continuation of the roots. This assertion concerns all displacements on the specified edge.

For $1/8\le h\le1/6$ put $x=\cos(2\pi h)\in[1/2,1/\sqrt2]$. Let $z=1$ for the curve at the center, or $z=-T_3(x)=3x-4x^3$ for the curve at the contact boundary. Then $1/2\le z\le1$ and $-3\le z'\le0$ for both choices. By the [packed-edge energy identity](packed-face.md), the two signed endpoint derivatives, divided by their common positive energy normalization, are
$$
 P(q,x)=\sum_{n\ge1}(-1)^{n+1}q^{n^2-1}\,n(2T_n(x)-1)^2 U_{n-1}(z).
$$
Specifically these derivatives are $\Phi'_h(0)$ and $\Phi'_h(y_b)$. The first two terms are $(2x-1)^2$ and $-4q^3(4x^2-3)^2z$. The first is independent of $q$ and has nonnegative $x$ derivative. The derivative in $x$ of the second is
$$
 64q^3x(3-4x^2)z-4q^3(4x^2-3)^2 z'\ \ge\ 16q^3.
$$
Its $q\partial_q$ derivative is at most $-6q^3$ since $(3-4x^2)^2\ge1$ and $z\ge1/2$.

For the remaining terms use $|T_n|\le1$, $|T'_n|\le n^2$, $|U_{n-1}|\le n$ and $|U_{n-1}'|\le n(n-1)^2$ on $[-1,1]$. The last bound follows from the finite cosine representation of $U_{n-1}(\cos\theta)$, as detailed in the contact calculation. The bounds on one summand and its two derivatives are respectively
$$
 9n^2q^{n^2-1},\qquad 39n^4q^{n^2-1}\quad(\partial_x),\qquad
 9n^4q^{n^2-1}\quad(q\partial_q).
$$
Hence the tails after dividing by $q^3$ are bounded by $9H,39H,9H$, where
$$
 H=\frac{3^4 Q^5}{1-(4/3)^4Q^7}.
$$
The ratio estimate uses $n\ge3$ and $q\le Q$. Exact rational arithmetic gives $39H<16$ and $9H<6$. Consequently $P_x>0$ and $P_q<0$ for both curves throughout the stated strip.

At $h=1/8$ the proof of the [packed-edge shape theorem](packed-face.md) gives $\Phi'_h(y)>0$ for all $0\le y\le2$. At $h=1/6$, $x=1/2$ and $z=1$ for either evaluation. The first term vanishes, the second is $-16q^3$, and the tail has absolute value at most $9Hq^3$. Thus both curves change sign exactly once, with $P_h=-2\pi\sin(2\pi h)P_x<0$. In the interior of this strip $y_b>0$, so strict convexity gives $\Phi'_h(y_b)>\Phi'_h(0)$, proving $h_c<h_b$. Minimization of a strictly convex function on $[0,y_b]$ gives the three phases and assigns each equality to its correct endpoint.

On compact complex neighborhoods with $|q|<1$ the Fourier series and its derivatives converge normally, since the Chebyshev factors grow at most exponentially in $n$ while $q^{n^2-1}$ decays faster. Simplicity and the analytic implicit-function theorem give both analytic branches, and implicit differentiation yields $dh/dq=-P_q/P_h<0$. The factor $dq/ds=\pi^2q/s^2$ is positive. In particular **both transition floors fall as the width parameter $s$ increases through 8**. The interval of global reduction determines where this is also a statement about unconstrained contact patterns.

## Uniform transfer of the full-simplex certificate

The [full-simplex verifier](../../code/verify_six_site_global_reduction.py) works on closed boxes independent of $s$. Each feasible terminal box excluded at $s=8$ has one of three strict integer inequalities, each with at least $10^{-9}$ true margin: a positive or negative cut gradient, a positive cut curvature, or a fixed feasible trial score strictly above the box score. The trial with largest *lower bound* can be chosen once per floor band. Empty chambers follow from geometry alone. These statements hold for the relative interior of the support; the derivative inequalities themselves hold up to the enclosed boundary. All cut quantities use $G_s'$ or $G_s''$ before multiplication by $1-6h$ or $(1-6h)^2$. They extend continuously across $h=1/6$ in the independent coordinates. Divide by these factors only when $h<1/6$. At $h=1/6$ the physical configuration is unique for every width.

Here is an independent upper bound for changes in the expressions tested at the leaves. On $7\le s\le9$, Poisson expansion with $c_s=\sqrt{\pi/s}$ gives $q<0.34$ and $c_s<0.68$. The first inequality follows already from $\pi>3.14$ and the degree-five partial sum of $\exp(3.14^2/9)$, the second from $\pi<22/7$. A coefficient $c_sq^{n^2}$ has logarithmic derivative $-1/(2s)+\pi^2 n^2/s^2$. For $r=0,1,2$, bounding $(2\pi n)^r\le40n^2$ for $n\ge1$ gives
$$
 \sup_d|\partial_s G_s^{(r)}(d)|
 \le 0.68/14 +2(0.68)\,40(0.072+0.202)
       \left[0.34+\frac{16(0.34)^4}{1-(3/2)^4(0.34)^5}\right] <9.
$$
The bracket majorizes $\sum n^4q^{n^2}$. A cut contains at most 15 pairs, and a difference between a trial and a configuration contains at most 30 signed terms. On $|s-8|\le10^{-13}$ every strict margin therefore shrinks by at most $270\cdot10^{-13}<10^{-9}$. This argument compares the true functions at the same $(h,u)$ and requires no continuity of the implementation's integer rounding. It also supplies the larger bound $|s-8|\le3\cdot10^{-12}$ for this exclusion step alone. The specified interval is a sufficient bound, without a claim about its optimal size.

At small floors, all constants and comparison arguments in the [analytic proof](early-global.md) use $q<0.292$. Its rational upper bounds after this substitution are independent of $s$. The same inequality holds on $|s-8|\le3\cdot10^{-12}$ by $\pi>3.14$ and the degree-seven positive Taylor sum for $\exp(3.14^2/(8+3\cdot10^{-12}))$. The $h^2$ factor in the final energy comparison stays strictly positive at each $h>0$; a fixed positive gap at $h=0$ is unnecessary. The two proofs overlap on $[1/50,1/25]$. The assumption $h>0$ excludes colliding neutral pairs; the $h=0$ endpoint has different uniqueness properties as recorded in the small-floor review.

Thus the global classification and decreasing critical curves indeed persist at least on the explicit interval $|s-8|\le3\cdot10^{-12}$. The leaf argument does not extend the all-configuration theorem to every $0<q\le17/50$.

## Cross-check of the unnormalized width certificate

I independently ran the literal Python block from the [width-interval proof](width-stability.md). It terminated at the stated 103,672 boxes for $7.995\le s\le8.005$ and $1/25\le h\le1/6$; the three types of nonempty terminal exclusions counted 16,047, 7,929 and 28,256. The logarithmic coefficient derivative is positive for $n\ge1$ because $2\pi^2>s$, and its stated uniform upper bound $0.155n^2$ yields the three claimed sup-norm bounds. A trial and a competitor each contain 15 signed unordered terms, so subtracting $30(0.005)/8$ from the unperturbed inclusive trial score lower bound provides the correct two-sided guard. The first and second cut derivatives are evaluated with widened enclosures at the variable width. Equivalently the guarded score test can be proved using the original width on both sides before bounding the true score change. This check uses all 18 excluded support representatives over 44 floor bands and the single feasible cell at $h=1/6$. The positive small-floor conclusion uses the genuine uniform upper bound $q<0.292$. I found no gap in this certificate.

## Width of the intermediate phase at scale eight

Write $D_c=h_c'(8)$ and $D_b=h_b'(8)$ with differentiation in the dimensionless width $s$. The interval computation below gives
$$
 -.004653798<D_c<-.004653797,\qquad
 -.004095783<D_b<-.004095782,\qquad
 .0005580150<D_b-D_c<.0005580151 .
$$
Thus the interval of intermediate global minimizers **widens** as $s$ increases through 8. By analyticity it widens on some open neighborhood of 8. No derivative sign for its width over the whole packed-family nome range is inferred.

To obtain these enclosures use the rigorous scale-eight brackets for $h_c,h_b$. The input $x$ is enclosed with the [existing rational cosine and $\pi$ bounds](../../code/verify_six_site_bifurcation.py). For each mode, differentiate $T_n$ using $T'_n=nU_{n-1}$, and generate the derivative of $U_{n-1}(z)$ by differentiating its three-term recurrence. Write $P_h=-2\pi\sin(2\pi h)P_x$, $P_s=(\pi^2/64)qP_q$. The polynomial tail bounds above from $n=7$ supply enclosures for both derivatives. Their quotient $-P_s/P_h$ gives the result. All decisions use rational interval endpoints.

## Rational checks

Run the following Python block from the repository root. The first part checks the uniform constants, and the second uses the repository's rational interval primitives to enclose the three slopes.

~~~python
from fractions import Fraction as F
from math import factorial

q = F(17, 50)
H = 3**4 * q**5 / (1-F(4, 3)**4*q**7)
assert 39*H < 16 and 9*H < 6
pi_low = F("3.14")
def exp_low(t, degree):
    return sum(t**k / factorial(k) for k in range(degree + 1))

assert q*exp_low(pi_low**2/9, 5) > 1
pi_high = F(22, 7)
assert pi_high < 7*F(".68")**2 and (2*pi_high)**2 < 40
assert F(1, 14) < F(".072") and (pi_high/7)**2 < F(".202")
modes = q + 16*q**4 / (1-F(3, 2)**4*q**5)
assert F(".68")/14 + 2*F(".68")*40*F(".274")*modes < 9
eps = F(3, 10**12)
assert 270*eps < F(1, 10**9)
assert F(".292") * exp_low(pi_low**2/(8+eps), 7) > 1

import sys
sys.path.insert(0, "code")
from verify_six_site_bifurcation import (Interval, PI, OMEGA, Q as nome, box,
    cosine_box, sqrt_box, chebyshev)
def derivative_at(left, right, contact):
    h = Interval(F(left), F(right))
    x = cosine_box(OMEGA*h)
    z = 3*x-4*x**3 if contact else box(1)
    dz = box(3)-12*x**2 if contact else box(0)
    u_prev, u = box(0), box(1)
    du_prev, du = box(0), box(0)
    px = q_pq = box(0)
    for n,(t,v) in enumerate(chebyshev(x), 1):
        a = 2*t-1
        w = (-1)**(n+1)*n*nome**(n*n-1)
        px += w*(4*n*a*v*u + a**2*du*dz)
        q_pq += (n*n-1)*w*a**2*u
        du_prev, du = du, 2*u+2*z*du-du_prev
        u_prev, u = u, 2*z*u-u_prev
    tail = F(7)**4 * F(".30")**48 / (1-F(8,7)**4*F(".30")**15)
    err = Interval(-tail,tail)
    ph = -OMEGA*sqrt_box(box(1)-x**2)*(px+39*err)
    ps = PI**2*F(1,64)*(q_pq+9*err)
    assert ph.hi < 0
    return -ps*Interval(1/ph.hi, 1/ph.lo)
dc = derivative_at(".13114680495074", ".13114680495076", False)
db = derivative_at(".13327908477025674",".13327908477025675", True)
gap = db-dc
assert F("-.004653798") < dc.lo <= dc.hi < F("-.004653797")
assert F("-.004095783") < db.lo <= db.hi < F("-.004095782")
assert F(".0005580150") < gap.lo <= gap.hi < F(".0005580151")
~~~
