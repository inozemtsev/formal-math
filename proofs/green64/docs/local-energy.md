# From complete-cell discrepancy to additive arc energy

We supply the local-energy inequality and the separation of variables
used in (M26). The term with factor $(H/Y)^2$ is the error in replacing
a linear window by a logarithmic window. The separate error in peeling
a SMALL prime is supported on its square multiples.

## 1. A finite local-energy inequality

Let $(a_n)$ be a finite complex sequence supported on $Y/A\le n\le AY$,
where $A\ge1$, and assume $1\le H\le Y/(8A)$. Choose a fixed smooth
function $K$ supported on $[-\delta,\delta]$, $0<\delta\le1$, with
Lipschitz constant $M_K$ and

$$
|\widehat K(t)|\ge c_K>0\quad(|t|\le1).
$$

Such a function is obtained by shrinking a nonnegative smooth bump of
integral one. Its Fourier transform stays close to one on $[-1,1]$.
Put

$$
\begin{aligned}
P(\beta)&=\sum_n a_n\mathrm e(n\beta),\qquad
P_a(t)=\sum_n a_n n^{it},\\
Q(v)&=\sum_n a_nK((n-v)/H),\qquad
R(v)=\sum_n a_nK(v\log(n/v)/H),\quad v>0.
\end{aligned}
$$

For every integer $j\ge2$ there is a constant $C_j$, depending only
on $A,K,j$, such that

$$
c_K^2\int_{-1/H}^{1/H}|P(\beta)|^2\,d\beta
\le \frac{C_j}{Y}\int_{\mathbb R}
 \frac{|P_a(t)|^2}{(1+(H/Y)|t|)^j}\,dt
 +2C_{\rm lin}(H/Y)^2\sum_n|a_n|^2,
\tag{E1}
$$

where $C_{\rm lin}=4\delta(4\delta+1)(16A\delta^2M_K)^2$.
The constant is uniform in the sequence, $H$ and $Y$.

Indeed, $\widehat Q(-\beta)=H\widehat K(-H\beta)P(\beta)$.
Plancherel bounds the left side by $H^{-2}\int|Q(v)|^2\,dv$.
The support of $Q$ lies in $V=[Y/(2A),2AY]$. If either kernel in
$Q(v)-R(v)$ is nonzero, then $|n-v|\le2\delta H$. Taylor's
estimate for $\log(1+u)$, using $v\ge Y/(2A)$ and
$H\le Y/(8A)$, gives

$$
\left|K((n-v)/H)-K(v\log(n/v)/H)\right|
 \le16A\delta^2M_K H/Y. \tag{E2}
$$

At each $v$ at most $(4\delta+1)H$ integers contribute; for each
$n$ the contributing $v$ lie in an interval of length $4\delta H$.
Cauchy--Schwarz and integration give

$$
H^{-2}\int_V|Q(v)-R(v)|^2\,dv
 \le C_{\rm lin}(H/Y)^2\sum_n|a_n|^2. \tag{E3}
$$

To estimate $R$, choose a fixed smooth compactly supported $\chi$
equal to one on $\log(V/Y)$, set $h=H/Y$, and write

$$
\mathcal Q(u)=\int_{\mathbb R}
 \chi(u)e^{-u}\widehat K(he^{-u}t/(2\pi))
 e^{-itu}Y^{-it}P_a(t)\,dt.
$$

Fourier inversion with $t=2\pi v\xi/H$ gives exactly

$$
\chi(\log(v/Y))R(v)=\frac H{2\pi Y}
                   \mathcal Q(\log(v/Y)). \tag{E4}
$$

The amplitude is smooth and compactly supported in $u$. Its first two
$u$-derivatives, multiplied by any fixed power of $1+h|t|$, are bounded
uniformly in $h,t$, by Schwartz decay of $\widehat K$. Two integrations
by parts bound its Fourier transform by
$C(1+h|t|)^{-j}(1+|s|)^{-2}$. Including $e^{-itu}$ replaces the
last factor by $(1+|s+t/(2\pi)|)^{-2}$. Its row and column integrals
are bounded constants. Weighted Schur and Plancherel yield

$$
\int|\mathcal Q(u)|^2\,du
 \le C'_j\int(1+h|t|)^{-j}|P_a(t)|^2\,dt.
$$

The Jacobian of $v=Ye^u$ is $Ye^u=O(Y)$ on the support of $\chi$.
Together with (E4) and division by $H^2$, this leaves precisely
$Y^{-1}$. Now $|Q|^2\le2|R|^2+2|Q-R|^2$ proves (E1).

## 2. Exact separation of the arithmetic coefficient

Use (M21)--(M23) at rational center $h_0/d$. Denote the distinguished
SMALL prime set by $S$ and its harmonic mass by $V_s$. After peeling
its distinguished mark, the main coefficient is

$$
a_n=\psi(n/Y)n^{iv_1}\mathrm e(h_0n/d)\varepsilon(n)
 \operatorname{Core}(n_*)\frac1{V_s}
 \sum_{s\in S,\ s\mid n}W_{\rm lo}(n/s).
\tag{E5}
$$

The weight $W_{\rm lo}$ has one fewer mark in $S$ and keeps all other
groups and the bounded list coefficient $b$. Expanding the core writes
$n=msp r$, where $m$ is rough, $s\in S$ is the peeled prime, and
$p$ lies in the complete ordinary prime slot. The integers $m,p$
have no marked prime factors, and all of $m,s,p$ are coprime to $d$.
Thus the remaining marked weight is exactly $W_{\rm lo}(r)$, while
the parity factor is $\varepsilon(s)\varepsilon(r)$. The main term
does not require $s$ to occur only to the first power.

For $d_0=\gcd(r,d)$ put $q=d/d_0$. On units modulo $q$ expand

$$
\mathrm e(h_0u/q)=\sum_{\xi\bmod q}c_{q,\xi}\xi(u),\qquad
c_{q,\xi}=\frac1{\varphi(q)}\sum_{u\in(\mathbb Z/q\mathbb Z)^\times}
 \mathrm e(h_0u/q)\overline{\xi(u)}.
\tag{E6}
$$

All characters, including principal and imprimitive ones, occur.
We have $|c_{q,\xi}|\le1$; their total number over $d_0\mid d$ is
$\sum_{d_0\mid d}\varphi(d/d_0)=d$. Define

$$
d_{d_0,\xi}(r)=1_{\gcd(r,d)=d_0}\,
 c(r_*)W_{\rm lo}(r)\varepsilon(r)\xi(r/d_0). \tag{E7}
$$

This coefficient is independent of $m,s,p$. In particular
$c(n_*/mp)$ has become $c(r_*)$; it is not absorbed into $\alpha$.
The marked-weight bound gives $|d_{d_0,\xi}(r)|\le C K^{g+1}$,
where $g=O(\log L)$ is the group count and $K$ depends only on the
fixed mark counts, damping and lower harmonic-mass bound. This is a
fixed polynomial in $L$.

Partition each of $m,s,p,r$ into canonical dyads. On one box put

$$
\begin{aligned}
S_\xi(t)&=\sum_{s\in S\text{ in the dyad}}
             \varepsilon(s)\xi(s)s^{-1+it},\\
P_\xi(t)&=\sum_{p\text{ in the slot dyad}}\xi(p)p^{-1+it},\\
A_\xi(t)&=\sum_{m\text{ in the factor interval and dyad}}
             \alpha(m)\chi_0(m)\xi(m)m^{-1+it},\\
D_{d_0,\xi}(t)&=\sum_{r\text{ in the dyad}}
             d_{d_0,\xi}(r)r^{-1+it},\\
F_{d_0,\xi}(t)&=S_\xi(t)P_\xi(t+\sigma_1)
                    A_\xi(t+\sigma_0)D_{d_0,\xi}(t).
\end{aligned} \tag{E8}
$$

With $f(u)=e^u\psi(e^u)$, Fourier inversion of the product cutoff is

$$
\frac{P_a(t)}Y=
\frac1{V_s}\sum_{d_0\mid d}\sum_{\xi\bmod d/d_0}
 c_{d/d_0,\xi}\sum_{\rm boxes}
 \int_{\mathbb R}\widehat f(\nu)Y^{-2\pi i\nu}
 F_{d_0,\xi}(t+v_1+2\pi\nu)\,d\nu.
\tag{E9}
$$

All integer sums are finite. The cutoff restricts the product to
$[Y/A,AY]\subset[1,N_{\rm cap}]$, so the independent four dyads
neither omit nor add a nonzero term. The reciprocal factors in (E8)
multiply to $1/n$; the factor $e^u=n/Y$ in $f$ explains $P_a/Y$.
There are at most $(1+\log_2N_{\rm cap})^4$ boxes.

For $T_0+|\sigma_0|\le L^B$, (M24) bounds
$A_\xi(t+\sigma_0)$ on $|t|\le T_0$. Its joint character has
modulus at most $q_{\rm base}d$, within the requested budget. If the
other coefficient bounds are $C_s,C_p,C_r$, their reciprocal sums
on dyads are at most $2C_s,2C_p,2C_r$. Hence

$$
\int_{-T_0}^{T_0}|F_{d_0,\xi}(t)|^2\,dt
 \le2T_0\bigl[(2C_s)(2C_p)(2C_r)L^{-B}\bigr]^2.
\tag{E10}
$$

This applies discrepancy only after exact separation, with no
$m$-dependent coefficient left in the other factors.

## 3. The rest of the Mellin window

The window extends beyond polynomial frequencies, so (E10) alone does
not suffice. Put $T=2LY/H$. Discard boxes whose product interval misses
the cutoff support: their contribution before Fourier separation is zero.
On each remaining box with small-prime scale $P$,
long-prime scale $N$, and other scales $M,R$, the actual comparison
cells imply

$$
T\le MNR,\qquad Y\asymp PMNR,\qquad
\lceil Y\rceil^{3/5}\le MR\le\lceil Y\rceil.
\tag{E11}
$$

Here $\log P\in[L^{a_s},L^{b_s}]$ up to fixed factors,
$a_s<b_s<3/10$, and $x^\tau/2\le N\le x^\eta$, $\eta<1/4$.
The two nonempty BIG probe products ensure
$H'\gg LP L^{C_{\rm arc}}$, giving the first inequality.
The lower bound for $MR$ follows from $Y\ge e^{3L/4}$ and
$PN\le e^{o(L)}x^\eta$; the upper bound follows from the product
support. Fixed comparison constants are absorbed by the strict
exponent margins and a larger threshold.

Choose $\delta=L^{-A_s}$. Where $|S_\xi(t)|\le\delta$, collapse
the other three factors to a Dirichlet polynomial of length at most
$8MNR$. Its mean square on $[-T,T]$ is bounded by

$$
[2T+128MNR(1+\log(8MNR))]
 \frac{(C_mC_pC_r)^2}{MNR}(1+\log(8MNR))^{16}.
$$

Integrating the off-diagonal terms uses
$|\log(n/m)|^{-1}\le\max(m,n)/|n-m|$; the divisor moment bounds
the collapsed coefficients. Multiplication by $\delta^2$ and a
sufficient choice of $A_s$ give any required logarithmic saving.

Cover the remaining times by occupied unit intervals. The factorial
moment estimate for the small-prime polynomial implies that their
number in each class of indices modulo three is at most
$\lceil Y\rceil^{1/20}$, eventually. Raise the polynomial to a power
of order $\log Y/\log P$. Unique factorization bounds ordered
representations by the factorial of that power. The separated
sampling estimate then gives an exceptional count $\exp(o(\log Y))$:
the factorial and threshold losses have logarithm
$O((\log Y/\log P)\log L)=o(\log Y)$, and $\log P=o(\log Y)$.
This proves the stated exponent for every fixed $A_s$.

On the occupied intervals the residual satisfies the explicit bound

$$
\sum_{j\in\mathcal J}\int_j^{j+1}
 |A_\xi(t+\sigma_0)D_{d_0,\xi}(t)|^2\,dt
 \le10752(C_mC_r)^2(1+\log(4\lceil Y\rceil))^4.
\tag{E12}
$$

Indeed, its collapsed coefficients on $[U,4U]$, $U=MR$, have squared
norm at most $(C_mC_r/U)^2\,4U(1+\log(4U))^3$. For $s$
one-separated sample times in $[-\lceil Y\rceil,\lceil Y\rceil]$,
the complete Gram row is at most

$$
448U(1+\log(2\lceil Y\rceil))+448s\sqrt{\lceil Y\rceil}.
$$

The first-derivative bound for $\sum_{U\le n\le4U}n^{it}$ is
$O(U/|t|)$ for $1\le|t|\le U$; the second-derivative bound is
$O(\sqrt{\lceil Y\rceil})$ for $U<|t|\le2\lceil Y\rceil$.
Their sum at separated times gives this row estimate. Since
$s\le\lceil Y\rceil^{1/20}$ and $U\ge\lceil Y\rceil^{3/5}$,
the second term is absorbed by $448U$. Schur's inequality gives
$3584(C_mC_r)^2(1+\log(4\lceil Y\rceil))^4$.
Choose independently in each interval a residual maximizer and a
point witnessing the large small-prime sum. Indices in one class
modulo three make both families one-separated. Summing the three
classes proves (E12).

On occupied intervals above a sufficiently large fixed power of $L$,
the long-prime estimate (U1), proved below, gives
$|P_\xi(t+\sigma_1)|\le K_D L^{-D}$ for every fixed $D$, uniformly
for the polynomial conductor budget and $|t+\sigma_1|\le x^2$.
Multiply it by (E12), using $|S_\xi|\le2$.
The other occupied intervals lie at polynomial frequencies and are
covered by (E10). Thus the entire window has arbitrary logarithmic
saving for each four-factor box.

Its constants, and those of the factorial-moment and Gram bounds,
precede the cutoff and box endpoints. To use (E9), restrict $|\nu|$ to a fixed polynomial
range, enlarge the phase budgets, and apply Minkowski. Bound the
omitted Fourier integral by repeated integration by parts. The
logarithmic derivative budget for $\psi$ supplies the required norms
and tails. Cauchy--Schwarz over the $d$ character terms and four dyads
then gives, for any prescribed $D$ after requesting sufficient
precision in (M24),

$$
\int_{-2LY/H}^{2LY/H}|P_a(t)/Y|^2\,dt
 \le V_s^{-2}d^2(1+\log_2N_{\rm cap})^8 L^{-D}.
\tag{E13}
$$

## 4. The high-frequency prime input

**Long-prime estimate.** Fix $0<\tau<\eta<1/4$ and $C,A>0$.
There are $B_0,K>0$ and $x_0\ge3$ such that, for $x\ge x_0$,
uniformly for $x^\tau/2\le N\le x^\eta$, $1\le q\le(\log x)^C$,
every Dirichlet character $\chi\bmod q$, every interval
$I\subset[N,2N]$, and $(\log x)^{B_0}\le|u|\le x^2$,

$$
\left|\sum_{\substack{p\in I\\p\ \mathrm{prime}}}
       \chi(p)p^{-1+iu}\right|\le K(\log x)^{-A}.
\tag{U1}
$$

Principal and imprimitive characters are included. In particular,
the estimate holds at $u=t+\sigma_1$ when
$L^{B_0}+|\sigma_1|\le|t|$ and $|t+\sigma_1|\le x^2$.
This lower bound on $|t|$ explains the polynomial-frequency region
handled separately by (E10).

The analytic input is the Vinogradov--Korobov zero-free region

$$
L(s,\chi)\ne0\quad\text{for}\quad
\Re s\ge1-
 \frac1{10.5\log q+61.5(\log|\Im s|)^{2/3}
                              (\log\log|\Im s|)^{1/3}},
\quad q\ge3,\quad |\Im s|\ge10.
\tag{U2}
$$

This is [Khale, Theorem 1.1](https://arxiv.org/pdf/2210.06457#page=1),
with the displayed conductor and height range.

Put $L=\log x$ and choose

$$
\epsilon=L^{-(A+5)},\quad H=L^{A+7},\quad c=L^{-1},\quad
Q=3L^C,\quad V=3e^{3L},
$$

$$
D=10.5\log Q+61.5(\log V)^{2/3}(\log\log V)^{1/3},
\qquad \delta=(100D)^{-1},\qquad B_0=A+10.
\tag{U3}
$$

For moduli one and two induce to modulus $3q$. The extra Euler
factor is nonzero in the positive half-plane, so (U2) gives the
needed region for the original character as well. Smooth the
interval $I$ with relative boundary width $\epsilon$. The Mellin
transform of this cutoff has decay constant
$B_j\ll_j\epsilon^{-j}\le C_jL^{(j+1)(A+5)}$ at order $j$.
Mellin inversion expresses the smoothed Mangoldt sum with coefficient
$\Lambda(n)\chi(n)n^{-1+iu}$ using
$-L'/L(1-iu+z,\chi)$ on $\Re z=c$.
Shift the central segment $|\Im z|\le H$ to $\Re z=-\delta$.
Here $|u|\ge L^{A+10}$ keeps the rectangle away from the principal
pole and low heights. The denominator $D$ dominates the zero-free
widths for all its conductors and heights. The logarithmic-derivative
bound in this smaller rectangle, the cutoff decay, and
$N^c\le e^\eta$ bound the left side, the horizontal sides, and the
remaining right-line tails by

$$
\mathcal M_j\ll B_j\left(
 HLN^{-\delta}
 +(c+\delta)e^\eta LH^{-j}
 +e^\eta L^2H^{1-j}\right).
\tag{U4}
$$

These bounds are uniform in the interval endpoints. Since
$D\ll_C L^{3/4}$ and $\log N\ge\tau L-\log2$,
$N^{-\delta}$ is smaller than every fixed inverse power of $L$.
Choose a fixed integer $j>2A+30$. The other terms in (U4) are also
$O(L^{-A-2})$: substituting (U3) gives exponents at most
$-2j+2A+14$. Removing the smoothing, deleting higher prime powers,
and partial summation to remove $\log p$ give

$$
\left|\sum_{p\in I}\chi(p)p^{-1+iu}\right|
\le\frac1{\log N}\left[
 \frac{\mathcal M_j}{2\pi}
 +\frac{2\log(3N)}N(2\epsilon N+2)
 +\frac{4\log(4N)}{\sqrt N}\right].
\tag{U5}
$$

The last two terms are respectively the boundary collars and the
prime powers. The exponential lower bound on $N$ makes (U5)
$O(L^{-A})$, proving (U1). Finally
$|t+\sigma_1|\ge|t|-|\sigma_1|$ proves the shifted assertion.

## 5. The four terms in (M26)

For the peeled coefficient $|a_n|\le B_{\rm amp}d_2(n)^3$.
With $N=\lceil AY\rceil$ this gives

$$
\sum_n|a_n|^2\le B_{\rm amp}^2N(1+\log N)^{63}, \tag{E14}
$$

because $d_2(n)^6\le d_{64}(n)$ and
$\sum_{n\le N}d_{64}(n)\le N(1+\log N)^{63}$.
The finite Dirichlet-polynomial mean-square estimate, applied on
dyadic time intervals and multiplied by $(1+(H/Y)|t|)^{-j}$, bounds
the part $|t|>LY/H$ by

$$
4L^{-(j-2)}[LY/H+16N(1+\log N)]
 B_{\rm amp}^2N(1+\log N)^{63}. \tag{E15}
$$

In (E1), (E13) contributes $Y$ times its right side, and (E15)
contributes $Y^{-1}$ times its right side. Formula (E3), with (E14),
gives the third line of (M26).

The difference between the original coefficient and (E5) vanishes
unless $s^2\mid n$ for a peeled prime $s\in S$. The marked-weight
bound and the fourth divisor moment on square multiples bound its
squared coefficient mass by

$$
3L B_s^2N(1+\log N)^{16}e^{-L^{a_s}}. \tag{E16}
$$

The factor $3L$ pays for the dyadic SMALL-prime ranges, and
$e^{-L^{a_s}}$ comes from summing $s^{-2}$ for
$s\ge e^{L^{a_s}}$. Parseval bounds its arc energy by this full
coefficient mass. Combining (E13)--(E16) with (E1) and
$|u+v|^2\le2|u|^2+2|v|^2$ gives the four terms in (M26), up to
constants fixed before $L$.

## Source correspondence

The local-energy transfer is `source_linear_to_log_arc434` in
[Weights/Part012](../Green64/Library/Weights/Part012.lean), using
`source_physical_collar_replacement_error434` in
[Analysis/PrimeNumberTheorem/Part003](../Green64/Library/Analysis/PrimeNumberTheorem/Part003.lean).
The weighted Schur estimate is
`source_actual_physical_normalized_L2_schur434` in
[Weights/Part023](../Green64/Library/Weights/Part023.lean).
The arithmetic identities and (E13) are in
[Analysis/Estimates/Part009](../Green64/Library/Analysis/Estimates/Part009.lean),
especially `source_original_global_physical_mellin_exact434` and
`eventually_source_original_global_physical_from_literal_cells434`.
The direct low-frequency estimate is in
[SourceLowFrequencyFourFactorIntegral](../Green64/Library/Analysis/Estimates/SourceLowFrequencyFourFactorIntegral.lean).
The three-region argument and retained Fourier frequencies are in
[Weights/Part040](../Green64/Library/Weights/Part040.lean).
The exceptional residual estimates are in
[Weights/Part035](../Green64/Library/Weights/Part035.lean) and
[Weights/Part039](../Green64/Library/Weights/Part039.lean).
The long-prime statement (U1) and its shift are
`sourceCorrelationLongPrime_shifted_U1` in
[Correlation/Part002](../Green64/Library/Correlation/Part002.lean).
The contour bound (U4), its closure (U3)--(U5), and the matching
zero-free interface are `p1p2_canonical_source_prime_bound`,
`sourceLongPrimeU1_of_sourceKhaleZeroFree`, and `KhalePublished11` in
[Estimates/Part003](../Green64/Library/Analysis/Estimates/Part003.lean).
The unconditional declaration there, `sourceLongPrimeU1_unconditional`,
obtains (U2) from the included stronger theorem
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` in
[Detector/Part016](../Green64/Library/Analysis/NumberTheory/DirichletL/Detector/Part016.lean).
The text invokes the weaker, independently published statement (U2);
no stronger zero-free conclusion is needed for the contour proof.
The use of (U1) on occupied intervals is in
[Analysis/Estimates/Part006](../Green64/Library/Analysis/Estimates/Part006.lean).
The final four-term estimate is
`eventually_source_original_full_additive434` in
[Correlation/Part033](../Green64/Library/Correlation/Part033.lean).
