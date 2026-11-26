# Global antipodal triples on the six-site simplex up to floor 1/10

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

**Theorem.** For six alternating particles, period one and Gaussian exponent eight, every global minimizer at every physical floor $0<h\le1/10$ is a pair of packed antipodal triples, up to rotation and cyclic relabelling. The proof uses translations of maximal packed blocks and holds uniformly as $h\downarrow0$.

## A lower bound for the leading mode of every maximizer

Use angular coordinates $\theta_j=2\pi x_j$, $\eta=2\pi h$, $q=\exp(-\pi^2/8)$ and $a_n=q^{n^2-1}$. Thus $0<\eta\le\pi/5<22/35$. Define
$$
 K(u)=\sum_{n\ge1}a_n\cos(nu),\quad
 P_n=\sum_{j=0}^5\sigma_j e^{in\theta_j},\quad
 Q=\sum_{n\ge1}a_n|P_n|^2,\qquad \sigma_j=(-1)^j .
$$
Maximizing $Q$ minimizes the physical energy. A maximizer exists by compactness. For the union $A$ of positive-to-negative arcs one has $P_n=-in\int_A e^{inu}\,du$, so $|P_n|\le\min(6,2n)$. The latter bound follows by projecting the integral onto its own direction and integrating the positive part of a cosine over the whole circle. Write
$$
 T_p=\sum_{n\ge3}n^pa_n,\qquad R=\sum_{n\ge2}n^4a_n .
$$
With $q<0.292$, the inequalities used below are
$$
 R<0.41,\quad 16q^3+4T_2<0.405,\quad
 16q^3+10T_2<0.41,\quad 32q^3+10T_3<0.82.
 \tag{1}
$$
The total score in $n\ge2$ is at most $16q^3+4T_2$, since $36\le4n^2$ for $n\ge3$. The centered packed triples have first squared weight $4(2\cos\eta-1)^2$ and are feasible. Since $\cos\eta>0.8088$, any maximizer satisfies
$$
 |P_1|^2\ge4(2\cos\eta-1)^2-0.405>(1.055)^2 . \tag{2}
$$
Rotate it to make $P_1>0$ real.

## Which blocks can occur at a global maximum?

A maximal packed block is a run of successive particles spaced by exactly $\eta$, with slack gaps on either side; an isolated site is a block of length one. At least one gap is slack, since $6\eta<2\pi$. If there is more than one block, each block can be translated a little in either direction.

Let $V(u)=\sum_j\sigma_j K(u-\theta_j)$ be the fixed potential of a maximizer $X$. For another feasible configuration $Y$ one has
$$
 Q(Y)-Q(X)=2\left[\sum_j\sigma_j V(Y_j)-\sum_j\sigma_j V(\theta_j)\right]
          +\sum_{n\ge1}a_n|P_n(Y)-P_n(X)|^2 .
$$
Here $Y_j$ are angular positions. Since the left side is nonpositive, the fixed-potential score $\sum_j\sigma_j V(Y_j)$ is also maximal at $X$. In particular the contribution of each separately movable block is at a local maximum as a function of its midpoint $u$.

For a block of $b=1,2,3,4$ particles with first sign $s\in\{-1,1\}$, write this contribution as
$$
 G_b(u)=s\sum_{j=0}^{b-1}(-1)^jV(u+(j-(b-1)/2)\eta).
$$
The alternating cosine sum on a single harmonic $\cos(nu)$ gives a cosine for odd $b$ and a sine for even $b$. The corresponding multipliers, evaluated at $x=n\eta$, are respectively
$$
 C_1(x)=1,\quad C_2(x)=2\sin(x/2),\quad C_3(x)=2\cos x-1,\quad
 C_4(x)=4\cos x\,\sin(x/2).
$$
For the actual complex harmonics of $V$, the same multipliers apply to their amplitudes. All $C_b(\eta)$ are positive. After division by $C_b(\eta)$, the first harmonic of $G_b$ is $P_1\cos(u-\phi)$ with the following centers.

| Starting sign | Odd block | Even block |
| --- | --- | --- |
| $+1$ | $0$ | $\pi/2$ |
| $-1$ | $\pi$ | $3\pi/2$ |

For $b\le4$, $|C_b(2\eta)|/C_b(\eta)\le2$. For $b=3$, use $|2\cos(2\eta)-1|\le1$ and $2\cos\eta-1>0.6$. For $b=4$, use $0\le\cos(2\eta)\le\cos\eta$ and $\sin\eta/\sin(\eta/2)\le2$. For $n\ge3$ all four ratios are at most $5n/3$. Indeed $b=3$ gives at most $3/0.6=5$, and $b=2,4$ give at most $n/\cos\eta<1.25n$ by the elementary sine-multiple bound. Consequently, after division by $C_b(\eta)$, the absolute remainders in $G_b'$ and $G_b''$ are at most the third and fourth bounds in (1), respectively. These estimates use $|P_2|\le4$ and $|P_n|\le6$ for $n\ge3$.

At a stationary midpoint, $|\sin(u-\phi)|\le0.41/1.055<\sin(0.42)$. Thus it is within $0.42$ radians of $\phi$ or $\phi+\pi$ modulo $2\pi$. Throughout the latter arc the normalized second derivative is at least $1.055\cos(0.42)-0.82>0$, excluding a local maximum. **Every independently movable block of size at most four therefore has its midpoint within $0.42$ of its stated center.** The four arcs are disjoint and occur in the order displayed by $0,\pi/2,\pi,3\pi/2$.

Suppose first there are at least three blocks. Each then has size at most four. In cyclic order, an odd block reverses the next block's starting sign, whereas an even block preserves it. In the subsequence of odd blocks the signs thus alternate. Since positive odd midpoints are all near $0$ and negative odd midpoints all near $\pi$, traversing the circle visits each of these two disjoint arcs only once. Hence, if odd blocks occur, there is exactly one of each sign. Between the positive odd midpoint and the negative odd midpoint, in the positive direction, each intervening even block would have to start negative. Its required arc near $3\pi/2$ is outside that path. On the other path, an even block would start positive and require the arc near $\pi/2$, again outside. This rules out three or more blocks whenever at least one has odd size.

The all-even possibilities for any number of blocks are $6$, $4+2$ or $2+2+2$. For a single packed block of length six, summation of the alternating geometric series gives $|P_1|=|\sin(3\eta)|/\cos(\eta/2)<1.055$, contradicting (2). In both other cases every block starts with the same sign. Their midpoints therefore lie in a common arc of length $0.84$. The sum of the first-mode magnitudes of their three constituent opposite-sign pairs is $6\sin(\eta/2)\le3\eta$. For $\eta\le0.30$ this contradicts (2). For $\eta>0.30$, midpoints of blocks of lengths four and two have distance at least $3\eta$ in either circular direction. For three dimers, lift their midpoints into the common $0.84$ arc. From the first to the last the distance is at least $4\eta$, since each successive midpoint separation is at least $2\eta$. Both bounds exceed $0.84$. This excludes all-even decompositions.

Thus the maximizing configuration consists of exactly two odd packed blocks. Their sizes are $3+3$ or $5+1$. The argument also covers the possibility of very small strictly positive slack gaps: the existence of a two-sided shift only requires a positive amount.

## Excluding five packed sites plus a singleton

Put $A(x)=2\cos x-1$ and $B(x)=1-2\cos x+2\cos(2x)$. These are the signed amplitudes of three and five packed sites, starting positive. The geometric-series identity $B(\eta)=\cos(5\eta/2)/\cos(\eta/2)$ gives $B(\eta)\ge0$ all the way to $\eta=\pi/5$. For centered antipodal blocks the first-mode score difference (triples minus the unequal split) is
$$
 \Delta(\eta)=4A(\eta)^2-(1+B(\eta))^2
             =4(1-\cos^2\eta)(2\cos\eta-1)^2 .
 \tag{3}
$$
For any placement of the singleton, its first-mode score with the five-site block is bounded by $(1+B(\eta))^2$.

If $0.40\le\eta\le\pi/5$, then $0.8<\cos\eta<0.922$. The derivative of $4(1-c^2)(2c-1)^2$ has the sign of $2+c-4c^2$ on this interval. It has its minimum at an endpoint, and both endpoint values exceed $0.405$. By (1) the higher modes of *any* six-site cell contribute less than $0.405$. The centered triple competitor therefore beats the unequal split at every relative position.

If $\eta\le0.40$, the unequal split itself has its largest score at antipodal midpoints. At midpoint separation $\pi+t$ its squared $n$th weight is $B(n\eta)^2+1-2(-1)^nB(n\eta)\cos(nt)$. By $1-\cos(nt)\le n^2(1-\cos t)$ and $|B|\le5$, the centered score exceeds the displaced score by at least
$$
 2\left[B(\eta)-5\sum_{n\ge2}n^2a_n\right](1-\cos t).
$$
The bracket is positive since $B(\eta)\ge1-3\eta^2$ and $\sum_{n\ge2} n^2 a_n\le R/4$. The bound on $B$ follows from $|2\cos(2x)-2\cos x|\le 3x^2$, by the cosine difference identity. The centered split is feasible since its two exterior gaps are $\pi-2\eta\ge\eta$.

For these two centered cells the odd-mode score difference is exactly $\Delta(n\eta)\ge0$ by (3), valid as a polynomial identity for any real argument. At even $n$ the triples give zero score and the unequal split has squared weight $[B(n\eta)-1]^2\le9(n\eta)^4$. Therefore the score advantage of the triples is at least
$$
 \Delta(\eta)-9R\eta^4
 \ \ge\ \big[4(1-\eta^2/6)^2(1-\eta^2)^2-9R\eta^2\big]\eta^2>0.
$$
This uses $\sin\eta\ge(1-\eta^2/6)\eta$ and $2\cos\eta-1\ge1-\eta^2$. Finally, the [packed-triple shape theorem](packed-face.md) gives the unique relative displacement $t=0$ for every $h\le1/10<1/8$. Together these comparisons prove the theorem.

## Rational checks

All displayed decimal bounds are exact rationals. The standalone block below checks the numerical inequalities.

~~~python
from fractions import Fraction as F
from math import factorial

q = F(".292")
def tail(start, power):
    ratio = F(start+1, start)**power * q**(2*start+1)
    return start**power * q**(start**2-1) / (1-ratio)

assert q*sum((F("3.14")**2/8)**k/factorial(k) for k in range(8)) > 1
assert tail(2,4) < F(".41")
assert 16*q**3 + 4*tail(3,2) < F(".405")
assert 16*q**3 + 10*tail(3,2) < F(".41")
assert 32*q**3 + 10*tail(3,3) < F(".82")
e = F(22,35)
assert sum((-1)**k*e**(2*k)/factorial(2*k) for k in range(4)) > F(".8088")
assert 4*(2*F(".8088")-1)**2-F(".405") > F("1.055")**2
d = F(".42")
assert F(".41") < F("1.055")*(d-d**3/6)
assert F("1.055")*(1-d**2/2) > F(".82")
assert 1/(1-e**2/8) < F("1.055")
v = F(".4")
assert 1-v**2/2+v**4/24 < F(".922")
assert all(4*(1-c*c)*(2*c-1)**2 > F(".405") for c in [F(".8"),F(".922")])
assert 1-3*v**2-5*F(".41")/4 > 0
assert 4*(1-v**2/6)**2*(1-v**2)**2-9*F(".41")*v**2 > 0
~~~
