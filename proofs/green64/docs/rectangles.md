# A positive estimate on factor rectangles

We prove the finite estimate underlying (S2) in [the sieve argument](sieve.md).
The notation for the ordinary bands $Q_j$, marked groups $P_g$, and
harmonic factors $H_Q,H_P$ is fixed in [the weight chapter](weights.md).
Write $x=e^L$ and

$$
\theta_0=\frac32\frac1{44}2^{-20},\qquad z=x^{\theta_0},\qquad
Z=\lfloor z^{10}\rfloor.
$$

Let $K\subset[A,B)$ and $N\subset[C,E)$ be finite sets of positive
integers, with natural endpoints $A\le B$, $C\le E$. Set

$$
\mathcal A=(B-A)(E-C),\qquad T=(B-A)+(E-C).
$$

For $2\le W\le z$, use the indicator $R_W$ from (C1), which vanishes
at $0$ and $1$. The finite rough-factor sum is

$$
\mathcal R_\rho(K,N;W)
=\sum_{u\le Y}w_\rho(u)
 \sum_{\substack{m\in K,\ n\in N\\mn=u+2}}
 R_W(m)R_W(n).
$$

The argument only uses $|\rho|\le1$, $0\le\Psi\le1$, and $\Psi(0)=0$;
the outer cutoff $Y$ may be any natural number. Uniformly in these data,
for sufficiently large $L$,

$$
\begin{aligned}
\mathcal R_\rho(K,N;W)\le{}&
 K_0\mathcal A H_QH_PV(W)^2V(z)\\
&+200^{400}H_Q
 \left(2TZx^{1/20}+4Z^2x^{1/10}\right)(1+\log Z)^3,
\end{aligned} \tag{R1}
$$

where $V(y)=\prod_{p\le y}(1-1/p)$ and $K_0$ is an absolute constant.
The proof keeps the additional factor $V(z)$ in the main term.

## 1. Assignments and random permissions

Since $A_\rho\le A_0$, it suffices to majorize the unsigned weight.
Keep the twenty ordinary slots in each band $j\ge20$, and choose one
marked prime $p_g\in P_g$ from each group. For an assignment $a$, put

$$
D_a=\prod_{j=20}^d\prod_{i=1}^{20}q_{j,i}\prod_gp_g,
\qquad
\eta=\frac1{(20!)^{d+1-20}}\prod_g\frac1{M_g}.
$$

The geometric bound on the ordinary scales and the marked-band bounds give
$D_a\le x^{1/20}$ eventually. Every prime divisor of $D_a$ is at least
$L^{20}$, so $D_a$ is odd.

Let $\mathcal P=\bigcup_gP_g$ and $U_a=\{p\in\mathcal P:p\nmid D_a\}$.
For each subset $S\subset U_a$, give $S$ weight $2^{-|U_a|}$ and call its
primes permitted. Ban every odd prime at most $z$ that neither divides
$D_a$ nor belongs to $S$. For a fixed $u$, independent choices of
permission give the exact identity

$$
2^{-|U_a|}\sum_{S\subset U_a}
 \prod_{p\in U_a\setminus S}1_{p\nmid u}
=\prod_{p\in U_a}
 \begin{cases}1/2,&p\mid u,\\1,&p\nmid u.\end{cases} \tag{R2}
$$

When the marked prime is summed over the distinct divisors from a group,
(R2) recovers its weight
$\omega_g(u)2^{-(\omega_g(u)-1)}/M_g$. Prime multiplicities remain in $u$;
the permissions concern distinct primes.

The omitted ordinary bands $j<20$ consist of primes larger than $z$.
Thus, while the full ordinary factorization is still retained, every
prime at most $z$ in the ordinary part must divide the tail assignment.
This proves the deterministic exclusions needed for the mask majorant.
We may then drop the remaining nonnegative factorial coefficients and
enlarge the tail-assignment sum. Consequently the weighted rectangle sum
is bounded by the sum, over $a$ and masks $S$, of $\eta2^{-|U_a|}$ times
the number of pairs in the rectangle satisfying

$$
mn\equiv2\pmod{D_a},\qquad R_W(m)R_W(n)=1,
\qquad p\nmid mn-2\ \text{for every banned }p. \tag{R3}
$$

The assignment moments used to sum this bound are

$$
\begin{aligned}
\sum_a\frac\eta{D_a}
 &=\prod_{j=20}^d\frac{V_j^{20}}{20!}
 \le200^{400}H_Q,\\
\sum_a\eta&\le200^{400}x^{1/20}H_Q,\\
\sum_a\eta D_a&\le200^{400}x^{1/10}H_Q.
\end{aligned} \tag{R4}
$$

In the first identity the marked reciprocal sums cancel $M_g$ exactly.
The inequality uses $V_j^{20}/20!\ge200^{-20}$ for the twenty omitted
bands. The other two inequalities follow from $D_a\le x^{1/20}$.

## 2. Local densities and the finite sieve

Fix an assignment and mask. Write $D=D_a$. The base congruence
$mn\equiv2\pmod D$ has exactly $\varphi(D)$ residue pairs modulo $D$:
choose the unit $m$, then $n=2m^{-1}$. At an odd prime $p\nmid D$, the
bad residue pairs are $mn=0$ when $p\le W$, and $mn=2$ when $p$ is banned.
These events are disjoint and have $2p-1$ and $p-1$ solutions,
respectively. Thus their combined density is

$$
g(p)=\frac{(2p-1)1_{p\le W}+(p-1)1_{p\text{ banned}}}{p^2},
\qquad 0\le g(p)\le7/9,\quad g(p)\le3/p. \tag{R5}
$$

For squarefree $d$ coprime to $D$, the Chinese remainder theorem makes
the densities multiplicative. Counting each residue class in the two
integer intervals gives

$$
\#\{\text{base pairs bad at every }p\mid d\}
=\frac{\varphi(D)\mathcal A}{D^2}\prod_{p\mid d}g(p)+r_a(d),
$$

with the explicit boundary estimate

$$
|r_a(d)|\le\tau(d)^2(2T+4Dd). \tag{R6}
$$

Indeed, the count in a residue class differs from its interval length
divided by the modulus by at most one in each coordinate; expansion of
the product leaves the two side terms and a corner term. Summing over
the allowed CRT classes and using the local bounds in (R5) gives (R6).

Apply the [finite block sieve](block-sieve.md) with parameter $h=2$. The
reciprocal-prime block bounds give block mass at most $12$, and (R5)
gives the uniform gap $1-g(p)\ge2/9$. The finite sieve is obtained by
upper Bonferroni truncation in each block; it bounds the sifted count by

$$
e^{\mathfrak r_2}\frac{\varphi(D)\mathcal A}{D^2}
 \prod_{\substack{3\le p\le z\\p\nmid D}}(1-g(p))
+\sum_{d\le Z}|r_a(d)|,
\qquad
\mathfrak r_2=\frac{e^{12e+52}}{1-e^{-1}}. \tag{R7}
$$

Here the sieve level is $z^{10}$, so the integer cutoff is $Z$.
The explicit constant follows from (BS2) with $C=12$, $\eta=2/9$.
Its block count may grow with $L$; the displayed bound is uniform
in that count by the finite proof given there.

The elementary divisor estimate
$\sum_{d\le Z}\tau(d)^2\le Z(1+\log Z)^3$ now gives

$$
\sum_{d\le Z}|r_a(d)|
 \le(2TZ+4DZ^2)(1+\log Z)^3. \tag{R8}
$$

The mask weights sum to one. Averaging (R8) over masks and then applying
the last two moments in (R4) gives exactly the error in (R1).

## 3. Averaging the Euler product

Put $v_p=1-1/p$. Direct comparison of the four possibilities in (R5) gives

$$
1-g(p)\le
v_p^{\,2\,1_{p\le W}+1_{p\text{ banned}}}
\left(1+\frac1{p(p-1)}\right). \tag{R9}
$$

The product of the correction factors over odd primes is at most $e^{1/2}$,
since $\log(1+t)\le t$ and
$\sum_{n\ge3}1/(n(n-1))=1/2$.
Before deleting assignment primes or permitting marked primes, the
remaining product is

$$
\prod_{3\le p\le z}v_p^{\,1+2\,1_{p\le W}}
=8V(W)^2V(z). \tag{R10}
$$

The factor eight restores the three omitted factors at the prime two.
Permitting $p\in S$ removes one power of $v_p$. Averaging these removals
over the masks gives

$$
2^{-|U_a|}\sum_{S\subset U_a}\prod_{p\in S}v_p^{-1}
=\prod_{p\in U_a}\left(1+\frac1{2(p-1)}\right)
\le\prod_gZ_g(1/2)\le H_P. \tag{R11}
$$

Deleting primes dividing $D_a$ removes at most three powers per prime.
Their roughness and $D_a\le x^{1/20}$ imply, eventually,

$$
\prod_{p\mid D_a}v_p^{-3}\le e. \tag{R12}
$$

For example, $-\log(1-1/p)\le2/p$, and the number of distinct prime
divisors is at most $\log D_a/\log2$; hence the logarithm of the left
side tends to zero uniformly.

Finally $\varphi(D_a)/D_a^2\le1/D_a$. Combining (R4) and (R7)--(R12)
proves the main term in (R1), with the explicit possible value

$$
K_0=200^{400}\,8e^{3/2+\mathfrak r_2}.
$$

## 4. Normalization by the actual mass

Assume $\mathcal A\le C_{\rm area}x$ and
$T\le C_{\rm side}x^{27/50}$, with fixed constants.
Since $10\theta_0\le1/20$, we have $Z\le x^{1/20}$ and
$(1+\log Z)^3\le8L^3$ for $L\ge1$. The error in (R1) is therefore at most
a fixed constant times

$$
H_QL^3(x^{16/25}+x^{1/5}), \tag{R13}
$$

where $27/50+1/20+1/20=16/25$ and $2/20+1/10=1/5$.
The mass bound $X_\rho\gg xH_QH_P/L$, Mertens' estimate
$V(z)\asymp L^{-1}$, and $H_P\ge1$ show that

$$
X_\rho V(W)^2\gg xH_Q/L^3\qquad(2\le W\le z).
$$

The main term of (R1) is $O(X_\rho V(W)^2)$, and the ratio of (R13) to
this scale is at most a constant times
$L^6(e^{-9L/25}+e^{-4L/5})\to0$.
Thus there is $C_{\rm box}>0$ such that

$$
\mathcal R_\rho(K,N;W)\le C_{\rm box}X_\rho V(W)^2
\qquad(\rho=\pm1).
$$

Both the constant and the eventual threshold precede the two signs,
the admissible threshold $W$, the finite carriers, and their endpoints.
In particular this applies to $W=e^{\sqrt L}$.

## Source correspondence

| Argument | Lean source and declaration |
| --- | --- |
| Assignment-mask majorant | [Foundations/Part056](../Green64/Library/Sieve/Foundations/Part056.lean): `parity_original_A0_assignment_mask_majorant434` |
| Assignment moments, weighted-fibre reduction, sieve application | [Foundations/Part056](../Green64/Library/Sieve/Foundations/Part056.lean) |
| CRT density and boundary count | [Foundations/Part002](../Green64/Library/Sieve/Foundations/Part002.lean), [Weights/Part035](../Green64/Library/Weights/Part035.lean) |
| Finite Brun--Hooley block sieve | [Foundations/Part001](../Green64/Library/Sieve/Foundations/Part001.lean) |
| Euler-product comparison and mask average | [Foundations/Part057](../Green64/Library/Sieve/Foundations/Part057.lean) |
| Complete finite bound (R1) | [Foundations/Part057](../Green64/Library/Sieve/Foundations/Part057.lean): `parity_original_literal_weighted_box_normalized434` |
| Error exponents and uniform normalization | [BoxRemainder](../Green64/Sieve/BoxRemainder.lean), [BoxError](../Green64/Sieve/BoxError.lean), [BoxNormalization](../Green64/Sieve/BoxNormalization.lean) |
| Uniform final statement | [WeightedBoxes](../Green64/Sieve/WeightedBoxes.lean): `weighted_box_bound_uniform` |
