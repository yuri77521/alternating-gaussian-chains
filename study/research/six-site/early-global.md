# Global packing for six sites up to a physical gap of 1/25

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

**Theorem.** Take six alternating sites on a circle of length one with Gaussian exponent eight and physical minimum gap $0<h\le1/25$. Every global minimum consists of two packed triples with antipodal midpoints. In physical units their positions, up to the symmetries of the energy, are $(-h,0,h)$ and $(1/2-h,1/2,1/2+h)$. The proof applies throughout the interval, including arbitrarily small positive floors.

## A quantitative semicircle estimate

Use angular positions $\theta_j=2\pi x_j$, floor $\eta=2\pi h<0.252$, signs $\sigma_j=(-1)^j$, and Fourier weights $a_n=q^{n^2-1}$ for $q=e^{-\pi^2/8}$. Set
$$
 K(u)=\sum_{n\ge1} a_n\cos(nu),\quad P_n=\sum_j\sigma_j e^{in\theta_j},\quad
 Q=\sum_{i,j}\sigma_i\sigma_jK(\theta_i-\theta_j)=\sum_{n\ge1}a_n|P_n|^2 .
$$
Maximizing $Q$ is equivalent to minimizing the physical energy. The signed dipole at $0,\pi$ has score $Q_H=4\sum_{n\,{\rm odd}}a_n$. The following rational bounds suffice:
$$
 R=\sum_{n\ge2}n^4a_n<0.41,\qquad
 T=\sum_{n\ge3}n^2a_n<0.001,\qquad
 D=2\sum_{n\,{\rm odd}}n^2a_n<2.01,
 \qquad 16q^3+6T<0.41. \tag{1}
$$
In particular $q<0.292$. To check this last bound on $q$, use $3.14<\pi<22/7$ and the partial sum of $\exp(3.14^2/8)$ through degree seven. For $p=2,4$ and $j\ge2$, the tail of $\sum_{n\ge j}n^pa_n$ is bounded by $j^p(0.292)^{j^2-1}/[1-((j+1)/j)^p(0.292)^{2j+1}]$. Then $D\le2(1+T)$.

Let $A$ be the union of the three positive-to-negative arcs, so that $(\mathbf 1_A)'=\sum_j\sigma_j\delta_{\theta_j}$. Write $F=Q_H-Q$. The semicircle rearrangement proof, §2 gives, at the present width,
$$
 F\ \ge\ 0.59(4-|P_1|^2). \tag{2}
$$
Indeed, use $v=K-0.59\cos$ in that proof. Its first cosine coefficient is $0.41$, larger than $R$. Both $v$ and $-v''$ decrease on $[0,\pi]$, since $|\sin(nu)|\le n\sin u$ there. Circular rearrangement bounds the score of $v$ on $A$ by the score on a single arc of the same measure, and the arc score $2[v(0)-v(b)]$ is largest at length $b=\pi$. The removed first harmonic contributes exactly the right-hand side of (2).

For centered packed triples, the even weights vanish and the odd weights are $4(2\cos(n\eta)-1)^2$. The elementary identity $1-(2\cos x-1)^2=4\cos x(1-\cos x)\le2x^2$ bounds the trial deficit by $4D\eta^2$. Thus every maximizer satisfies
$$
 |P_1|^2\ge4-8.04\eta^2/0.59>(1.77)^2,qquad
 J=2-|P_1|\le \frac{8.04\eta^2}{0.59(2+1.77)}<3.62\eta^2.
 \tag{3}
$$
Rotate so $P_1$ is positive real. Integration by parts gives $P_1=-i\int_A e^{iu}\,du$, so $J=\int_{A\triangle(0,\pi)}|\sin u|\,du$.

For a site at distance $r\ge\eta$ from the nearer of $0,\pi$, both adjacent intervals of length $\eta$ have constant semicircle indicator, and opposite $A$ indicators. One interval contributes to $J$ throughout. A point at arc length $s$ from the site has distance at least $r-s$ from the nearer endpoint. Therefore
$$
  J\ge\int_0^\eta\sin(r-s)\,ds
  =2\sin(\eta/2)\sin(r-\eta/2).
$$
Now $J/[2\sin(\eta/2)]<3.62\eta/(1-\eta^2/24)<0.916$. Meanwhile $\sin(1.30-0.252/2)>0.916$ by Taylor's lower bound through degree seven. Since $r\le\pi/2$, this gives $r<1.30$; the same bound is immediate when $r<\eta$. On each arc between the two closed neighborhoods of radius $1.30$, $A$ must agree with $(0,\pi)$. Otherwise the whole arc would contribute $2\cos(1.30)>0.5$ to $J$, contradicting (3). These complementary arcs are nonempty. Consequently both clusters have odd size, the first with net charge $+1$ and the second with net charge $-1$.

## Every internal gap is at the floor

Keep the potential of a maximizing configuration fixed at
$$
 V(u)=\sum_j \sigma_j K(u-\theta_j).
$$
For every $n$, integration by parts gives $P_n=-in\int_A e^{inu}\,du$. The projection of the integral onto its own direction has absolute value at most the integral of the positive part of $\cos(nu-\varphi)$ over a full circle, which equals $2$. Also $|P_n|\le6$. Hence the curvature from $n\ge2$ has absolute value at most $16q^3+6T<0.41$. The first harmonic of $V''$ is $-|P_1|\cos u$. From (3) and $\cos(1.30)>1/4$, one obtains
$$
 V''(u)<0\quad (|u|\le1.30),\qquad
 V''(u)>0\quad (|u-\pi|\le1.30)
 \tag{4}
$$
with angles read modulo $2\pi$.

Fix one internal gap and call its one-based index within the cluster $p$. When increasing this gap, move its suffix to the right if $p$ is odd, or its prefix to the left if $p$ is even, with unit speed. Each moving block has even size. The full score derivative is $2\sum_j\sigma_j\dot\theta_jV'(\theta_j)$ by evenness of $K$. In particular the formula already accounts for the moving sites' contributions to the potential. In either choice of block, successive pairs $(l,r)$ of moving sites contribute
$$
  s\,[V'(r)-V'(l)]=s\int_l^r V''(u)\,du
$$
to half the derivative, where $s$ is the cluster's net sign. For a suffix the pair signs are $(-s,s)$, and for a prefix they are $(s,-s)$ with both velocities negative. Every such term is strictly negative by (4), since $r-l\ge\eta>0$. A slack internal gap could therefore be shortened to increase the score. Shortening translates the chosen block inward and widens the exterior gap on its side. This is a feasible variation and contradicts maximality. All internal gaps are packed.

## Comparing the two possible odd splits

The sizes are $3+3$ or $5+1$. The [packed-triple theorem](packed-face.md) gives unique relative midpoint separation $\pi$ for $3+3$ throughout $h\le1/25$. For five packed sites, their signed amplitude about their midpoint is
$$
 B(x)=1-2\cos x+2\cos 2x .
$$
At midpoint separation $\pi+t$ the squared weight including the opposite singleton is $B(n\eta)^2+1-2(-1)^n B(n\eta)\cos(nt)$. Thus half the score advantage of $t=0$ over $t$ is at least
$$
 [B(\eta)-5\sum_{n\ge2}n^2a_n](1-\cos t)>0
$$
whenever $t\not\equiv0\pmod{2\pi}$. Here $|B|\le5$, $|1-\cos nt|\le n^2(1-\cos t)$, $B(\eta)\ge1-3\eta^2$ by the sine product for $\cos2\eta-\cos\eta$, and $\sum_{n\ge2}n^2a_n\le R/4$. The centered configuration is feasible since its exterior gaps are $\pi-2\eta\ge\eta$.

It remains to compare the centered scores. For odd $n$, write $x=n\eta$, $c_x=\cos x$. The weight for two triples minus the five-site-plus-singleton weight equals
$$
 \Delta(x)=[2(2c_x-1)]^2-[B(x)+1]^2
          =4(1-c_x)(2c_x-1)(c_x+\cos2x).
$$
For $n=1$ we have $\Delta(\eta)>3\eta^2$. Indeed $1-\cos\eta\ge(1/2-\eta^2/24)\eta^2$, $2\cos\eta-1\ge1-\eta^2$ and $\cos\eta+\cos2\eta\ge2-5\eta^2/2$. For all real $x$, $|\Delta(x)|\le12x^2$ by the factored expression. For even $n$, the triples have weight zero and the other cell contributes $[B(x)-1]^2\le9x^4$ since $|2\cos2x-2\cos x|\le3x^2$. Summing shows that the score advantage of the two triples exceeds
$$
  (3-12T-9R\eta^2)\eta^2>0 .
$$
This excludes the only other odd split and completes the full-simplex proof.

## Exact numerical checks

All decimals in the proof denote rationals. The checks below use standard-library rational arithmetic. They can be run as one Python block.

~~~python
from fractions import Fraction as F
from math import factorial

q, e, r = F("0.292"), F("0.252"), F("1.30")
def tail(j, p):
    ratio = F(j + 1, j)**p * q**(2*j + 1)
    return j**p * q**(j*j - 1) / (1 - ratio)

assert 2*F(22, 7)/25 < e
assert sum((F("3.14")**2/8)**k/factorial(k) for k in range(8)) * q > 1
assert tail(2, 4) < F(".41") and tail(3, 2) < F(".001")
assert 16*q**3 + 6*tail(3, 2) < F(".41")
assert 4 - F("8.04")*e**2/F(".59") > F("1.77")**2
assert F("8.04")/(F(".59")*F("3.77")) < F("3.62")
assert F("3.62")*e/(1-e**2/24) < F(".916")
w = r-e/2
assert w - w**3/6 + w**5/120 - w**7/5040 > F(".916")
assert 1 - r**2/2 + r**4/24 - r**6/720 > F(1,4)
assert F("3.62")*e**2 < F(1,2) and F("1.77")/4 > F(".41")
assert 1 - 3*e**2 - 5*F(".41")/4 > 0
assert 4*(F(1,2)-e**2/24)*(1-e**2)*(2-F(5,2)*e**2) > 3
assert 3 - 12*F(".001") - 9*F(".41")*e**2 > 0
~~~
