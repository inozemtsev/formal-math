# From one mark to the physical matrix

This chapter supplies the finite change of variables between (B17) and
the matrix (M18c). Extra marks are introduced by a common dilation of the
two integers. They are then removed by an exact finite reindexing and a
quantitative estimate for collisions.

## 1. The raw shared-prime sum

Put $q=1/2$, $M=J+1$, and let $G$ denote the set of all marked groups.
For each $g\in G$ draw $J$ labelled primes $s_{g,i}\in P_g$ independently
with probabilities $1/(V_gs_{g,i})$. Write

$$
D_s=\prod_{g,i}s_{g,i},\qquad
\mu(s)=D_s^{-1}\prod_gV_g^{-J},\qquad \sum_s\mu(s)=1.
$$

Repeated draws are included. For positive $w$, let $\mathcal A_s(w)$
be the set of complete ordered lists of $M$ distinct primes in each
group, all dividing $D_sw$, whose first $J$ coordinates are the given
$s_{g,i}$. In particular this set is empty if any shared list repeats
a prime. Put

$$
H(n)=\prod_g q^{\max(\omega_g(n)-M,0)/2},
\qquad
R_s(w,w')=
\frac{H(D_sw)^2H(D_sw')^2}{D_s\prod_gV_g^{J+2}}
 |\mathcal A_s(w)|\,|\mathcal A_s(w')|. \tag{L1}
$$

On a nonempty completion the maximum in $H$ can be omitted. Formula
(L1) is exactly the raw physical slice: the state mass contributes
$\prod V_g^{-M}$, the raw row contributes $\prod V_g^{-1}$, and its
two half dampings combine with the two endpoint half dampings. Averaging
the endpoint permutations gives the same fixed-slot completion sum;
each relabelling has the inverse permutation as its unique inverse.
The factor $D_s^{-1}$ comes from the harmonic factor $1/n$ after
putting $n=D_sw$.

Call a draw clean if its primes are distinct in each group and none
divides $ww'$. Then
$\omega_g(D_sw)=J+\omega_g(w)$ and each completion is specified by
one prime divisor of $w$ in each group. Substitution in (L1) gives

$$
R_s(w,w')=\mu(s)W(w)W(w')\quad\text{on clean draws}. \tag{L2}
$$

This explains why an original integer with only one marked divisor in
a group is allowed: its physical integer is $D_sw$, which has the
additional $J$ shared marked divisors on a clean draw.

Let $I=J|G|$, $P_{\min}\le\min_{p\in\cup P_g}p$, and
$v\le\min_gV_g$. The probability of a collision or a prime dividing
$ww'$ is at most

$$
\frac{I(\log_2 w+\log_2 w')+I^2}{vP_{\min}}. \tag{L3}
$$

Indeed every atom has mass at most $1/(vP_{\min})$; a positive integer
has at most its base-two logarithm distinct prime divisors. Sum these
bounds over the draws and over pairs of draws. On any draw, completions
can only lose free choices compared with the one-mark lists of $w,w'$.
At most $J$ shared primes per group already divide either integer, so
removing the associated damping costs at most $q^{-2M|G|}$. Therefore

$$
\left|\sum_sR_s(w,w')-W(w)W(w')\right|
\le(q^{-2M|G|}+1)W(w)W(w')
 \frac{I(\log_2 w+\log_2 w')+I^2}{vP_{\min}}. \tag{L4}
$$

This is obtained by summing $R_s-\mu(s)W(w)W(w')$, which vanishes
on clean draws by (L2). Thus no conditioning or renormalization of the
prime law occurs. Since $J$ is fixed, $|G|=O(\log L)$ and
$P_{\min}\ge e^{L^{1/10}}$, the factor in (L4) is a fixed power of
$L$ times $e^{-L^{1/10}}$ when $w,w'\le e^{2L}$.

## 2. The arithmetic factors and the exact reindexing

Write $a_1=\tau+\xi_3$, $a_2=-\tau$ for the phases in (B17),
and set $E=\overline F$. Then the product of the two cores is
$\overline{E(w)}G(w')$. Let $\Psi(t)=t\psi(t)$ and define

$$
K(w,w')=\frac{\Psi(w/Z)}w\,w^{ia_1}(w')^{ia_2}
 \overline{E(w)}G(w')\varepsilon(w)\varepsilon(w').
$$

Consequently $\mathcal C_{k,Z}/Z=
\sum_{w>0,\,w+2k>0}K(w,w+2k)W(w)W(w+2k)$.
The sum is finite by the support of $\psi$.

For a raw frame set $n=D_sw$, $n'=D_sw'$. Its equation
$n'-n=2kD_s$ is equivalent to $w'-w=2k$; the change of variables is
bijective on the positive integers divisible by $D_s$. Moreover

$$
(D_sw)_*=w_*,\qquad
\varepsilon(D_sw)\varepsilon(D_sw')
 =\varepsilon(w)\varepsilon(w'). \tag{L5}
$$

The first identity uses only that $D_s$ is supported on marked primes;
the second uses complete multiplicativity and $\varepsilon(D_s)^2=1$.
They hold even on dirty draws and preserve the original multiplicities.
Taking the frame phase $D_s^{i\zeta}$ with
$\zeta=-(a_1+a_2)=-\xi_3$ also cancels the common dilation in the
two imaginary powers. The cutoff is evaluated at $n/(ZD_s)=w/Z$.
Expanding the raw physical pairing and reindexing therefore gives exactly

$$
Q_{\rm raw}=
\sum_{w>0,\,w+2k>0}K(w,w+2k)\sum_s R_s(w,w+2k). \tag{L6}
$$

Choose the finite physical window to contain these dilated positions
and their edge neighbours. This is possible uniformly: $D_s$ is at most
$\exp(O_J(L^{2/5}\log L))$, while $w\asymp Z=xL^{O(1)}$.
No contributing term is added or lost when the common finite carrier
replaces the individual quotient carriers.

Applying (L4) in (L6), the pointwise logarithmic bounds for $W$, and
the divisor-moment bounds for the cores shows that
$Q_{\rm raw}-\mathcal C_{k,Z}/Z$ is smaller than any fixed inverse
power of $L$. For example, Cauchy--Schwarz bounds the sum of the two
core moduli over $w\asymp Z$ by $ZL^{O(1)}$, and the factor $1/w$
cancels $Z$. The remaining factor is $L^{O_J(1)}e^{-L^{1/10}}$.
Physical marked-part caps are removed separately by (M27); one must
not identify a cap at $D_sw$ with the same cap at $w$.

## 3. The endpoint vectors and the signed difference

Partition the first integer position into dyadic intervals $[X,2X)$.
On a physical state $s$ at position $n$, put

$$
\begin{aligned}
f_{X,\nu}(s)&=\sqrt{m_0}\,1_{X\le n<2X}\frac Xn
 (n/Z)^{-2\pi i\nu}n^{-ia_1}E(n)\varepsilon(n)H(n),\\
g_X(s)&=\sqrt{m_0}\,n^{ia_2}G(n)\varepsilon(n)H(n).
\end{aligned} \tag{L7}
$$

Restrict $g_X$ to the finite neighbourhood reachable from the first
interval; this does not change the pairing. These formulas specify the
extra endpoint damping, separately from the damping already in the
matrix. The first vector depends only on the integer position.

Let $f_\Psi(t)=\Psi(e^t)$ and use
$\widehat f_\Psi(\nu)=\int_{\mathbb R}f_\Psi(t)e^{-2\pi i\nu t}\,dt$.
Fourier inversion of the actual frame cutoff, followed by finite
summation, gives

$$
Q_{\rm raw}-Q_{\rm cmp}
 =\sum_X\frac1X\int_{\mathbb R}\widehat f_\Psi(\nu)
   \langle f_{X,\nu},A(\zeta-2\pi\nu)g_X\rangle\,d\nu.
\tag{L8}
$$

Here $A(v)$ is precisely (M18c) with frame phase $D_f^{iv}$, and
$Q_{\rm cmp}$ is the sum of its nonempty comparison patterns with
the signs in (M2). The conjugation of the first vector supplies
$(n/Z)^{2\pi i\nu}$; its product with $D_f^{-2\pi i\nu}$ is
$e^{2\pi i\nu\log(n/(ZD_f))}$. This proves (L8) without replacing
$D_f$ by a representative cell value. Compact support and smoothness
make $\widehat f_\Psi$ integrable. Fourier tails are bounded with the
fixed derivative budgets before the polynomial frequency restriction
in the correlation estimate is applied.

The vector norms in (M20) follow by first fixing the complete distinct
mark product $P_0$. It divides $n$, and the core has size at most a
fixed logarithmic factor times $d_2(n/P_0)^2$. Thus its squared sum
over $n\le3X$ is at most $(3X/P_0)L^{O(1)}$, using the fourth divisor
moment. Finally
$m_0\sum_{\text{distinct lists}}1/P_0\le
\prod_g V_g^{-M}(\sum_{p\in P_g}1/p)^M=1$.
This gives $\|f_{X,\nu}\|,\|g_X\|\le\sqrt X L^{C_{\rm norm}}$
with exponent independent of $J$. The rough-factor counting bound for
the core gives the supremum bound in (M20). Applying that estimate in
(L8), paying for the logarithmic number of dyads and the Fourier norm,
and then using (L4)--(L6), proves the claimed saving for the original
correlation minus its comparison term.

## Source correspondence

The raw slice is `parityRawPhysicalSlice434` in
[Correlation/Part072](../Green64/Library/Correlation/Part072.lean).
The clean identity and (L4) are `parity_raw_clean_slice_exact434` and
`parity_raw_shared_restoration_bound434` in
[RawSharedRestoration](../Green64/Library/Weights/RawSharedRestoration.lean).
The carrier reindexing is in
[RawSharedCarrier](../Green64/Library/Weights/RawSharedCarrier.lean),
and the arithmetic cancellation and original-source identification are in
[Weights/Part115](../Green64/Library/Weights/Part115.lean).
The endpoint vectors, removed-product fourth moment, and exact Fourier
pairing are in [Weights/Part109](../Green64/Library/Weights/Part109.lean).
