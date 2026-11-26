# Global minimization within the family of two packed triples

Historical proof note. Equation numbers and interim questions refer to this stage of the study. See the [final theorem index](../../EVIDENCE.md) for the integrated results.

Consider six alternating sites on the unit circle with the complete directed Gaussian energy defined in (1). The result below is global on a specified one-dimensional family. It does not assert that every minimizer over the five-dimensional gap simplex belongs to that family.

## A shape theorem for the relative displacement

Let $0<h<1/6$ be the physical gap floor, $q=e^{-\pi^2/\alpha}$ and $c=\sqrt{\pi/\alpha}$. Consider
$$
Y(h,t)=(0,h,2h,\tfrac12+t,\tfrac12+t+h,\tfrac12+t+2h),
\qquad |t|\le b(h)=\tfrac12-3h.
$$
The bound on $t$ imposes both wraparound and central exterior gap constraints. Write $A_n=2\cos(2\pi nh)-1$, $y=1-\cos(2\pi t)$, and $y_b=1-\cos(2\pi b(h))$. Set $T_n(\cos\theta)=\cos(n\theta)$ and let $U_n$ denote the Chebyshev polynomial of the second kind. The charge within each triple has amplitude $A_n$ up to a phase. The two triples have opposite net charges. The squared total amplitude of mode $n$ is $2A_n^2[1-(-1)^n\cos(2\pi nt)]$. The zero mode cancels. On subtracting the centered energy, Poisson summation gives
$$
E(Y(h,t))-E(Y(h,0))=(4cq/6)\,\Phi_h(y),\quad
\Phi_h(y)=\sum_{n\ge1}(-1)^n q^{n^2-1}A_n^2[T_n(1-y)-1].
$$
The change of variable maps $|t|\in[0,b]$ bijectively to $y\in[0,y_b]$.

**Theorem.** For every $0<q\le17/50$ the following conclusions hold.

1. For $0<h\le1/8$ the centered cell is the unique minimum in this family.
2. For $1/8\le h<1/6$, $\Phi_h$ is strictly convex on $[0,2]$. Its unique minimizing $y$ on $[0,y_b]$ is zero if $\Phi'_h(0)\ge0$, the endpoint $y_b$ if $\Phi'_h(y_b)\le0$, and otherwise the unique interior zero of $\Phi'_h$. An interior minimizing $y$ corresponds to two displacements related by reflection. At $y_b$ the exterior gap on one side reaches $h$, giving a chain with five consecutive contacts.

**Proof.** From $T'_n=nU_{n-1}$ and
$$
U_{n-1}(\cos\theta)=\sum_{j=0}^{n-1}\cos((n-1-2j)\theta)
$$
we obtain $|T'_n|\le n^2$. Differentiating the polynomial identity on the right and applying the same bound to each $T_{|n-1-2j|}$ gives $|T''_n|\le n\sum_{j=0}^{n-1}(n-1-2j)^2\le n^4$ on $[-1,1]$, including the endpoints. Gaussian decay justifies both differentiations of $\Phi_h$ uniformly.

Put $Q=17/50$. When $h\le1/8$, $A_1^2\ge3-2\sqrt2>17/100$, $|A_2|\le1$, and $|A_3|\le1+\sqrt2$, whence $A_3^2<6$. For all harmonics, $|A_n|\le3$. The first derivative of the second mode is $q^3 A_2^2(4y-4)$. For $n\ge4$ the ratio of successive terms in $n^2 Q^{n^2-1}$ is at most $(5/4)^2 Q^9$. Thus throughout $[0,2]$
$$
\Phi'_h(y)>\frac{17}{100}-
\left(4Q^3+54Q^8+\frac{144Q^{15}}{1-(5/4)^2Q^9}\right)>0.
$$
The last inequality is rational. The elementary square comparison $(283/200)^2>2$ gives the first-mode bound.

When $h\ge1/8$, $4\pi h\in[\pi/2,2\pi/3]$, so $A_2^2\ge1$. The first mode has zero second derivative and the second contributes $4q^3 A_2^2$. Bounding the rest by absolute values gives
$$
\frac{\Phi''_h(y)}{q^3}\ge
4-9\sum_{n\ge3}n^4 q^{n^2-4}
\ge4-\frac{729 Q^5}{1-(4/3)^4 Q^7}>0 .
$$
The ratio bound applies from $n=3$ onward. Strict increase of $\Phi'_h$ gives the three cases, including the weak endpoint inequalities. This proof needs no numerical phase search.

## Consequence at Gaussian scale 8

For $\alpha=8$ define $h_c$ by $\Phi'_h(0)=0$ and $h_b$ by $\Phi'_h(y_b)=0$ in $1/8,1/6)$. The [center certificate proves that the centered curvature in physical $t$ is strictly decreasing with one zero. This curvature is $(4cq/6)(2\pi)^2\Phi'_h(0)$. The outer-contact certificate proves that the boundary derivative has a unique zero and changes from positive to negative. The two roots satisfy
$$
0.13114680495074<h_c<0.13114680495076,\qquad
0.13327908477025674<h_b<0.13327908477025675.
$$
The complete family classification now follows. For $0<h\le h_c$ the minimizing displacements consist of $t=0$. For $h_c<h<h_b$, there is exactly one reflected pair $\{-t_*(h),t_*(h)\}$ of interior minimizers. For $h_b\le h<1/6$, they are the endpoints $t=\pm b(h)$. At $h=1/6$ only $t=0$ is feasible. By strict convexity and the implicit function theorem the interior solution is real analytic in $h$ away from its endpoints. At $h_b$ it reaches the contact boundary continuously by compactness and uniqueness in $y$. The local theorem treats variations that release any of the four internal contacts near $h_c$.

The centered and five-contact cells have continuous energies, with opposite strict order at $h_c$ and $h_b$. Whenever their energies agree strictly between those endpoints, strict convexity places the interior minimizer below both. Comparing just the two endpoint energies therefore cannot identify the first transition even within this family.

## Reproduction

Run the two standard-library programs from the repository root.

~~~sh
python -B code/verify_six_site_bifurcation.py
python -B code/verify_six_site_contact.py
~~~

The following independent rational checks suffice for the two uniform derivative estimates.

~~~python
from fractions import Fraction as F
Q = F(17, 50)
assert 4*Q**3 + 54*Q**8 + 144*Q**15/(1-F(25,16)*Q**9) < F(17,100)
assert 729*Q**5/(1-F(4,3)**4*Q**7) < 4
~~~

The proof uses the relative displacement variable only after the four internal gaps have been fixed. A general pattern with a released gap is outside its scope.
