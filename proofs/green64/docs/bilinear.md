# The bilinear reduction

This chapter gives the finite sums and estimates behind the bilinear
replacement in [correlation.md](correlation.md). We use its complete-cell
discrepancies and the weights from [proof.md](proof.md). To distinguish
parity from Fourier frequency, $\rho\in\{\pm1\}$ denotes parity and
$\tau\in\mathbb R$ denotes a Mellin frequency.

## 1. The statement on one factor rectangle

Fix $D>0$, $\eta>0$, and $C_{\rm box}\ge1$. Reserve a slot in a fixed
ordinary band $Q_{j_Q}$ with

$$
\frac65\sigma2^{-j_Q}\le\eta/4.
$$

Choose fixed exponents $A,K_0$ satisfying

$$
A\ge D+C_E+C_F,\qquad K_0\ge2A+2C_W+344. \tag{B1}
$$

Here $C_W\ge0$ bounds $W(u)$ by $L^{C_W}$,
$C_E=2\log(20!)$, and $C_F$ is the fixed Fourier cost defined below.
There are integers $H,J,B$, a mesh exponent $S>2(B+1)+3$, and $C>0$
with the following property. For each fixed $\beta,\gamma>0$, eventually
in $L$, the conclusion holds uniformly in all the data below:

$$
\begin{gathered}
U,V>0,\quad x\le4UV,\quad UV\le C_{\rm box}x,\quad V\ge1,\\
E=UL^{-K_0},\quad1\le E\le x^{1-\eta},\\
2\le a\le b\le2a,\quad x^\beta\le a,\quad b\le x^2,\\
K=[a,b]\cap\mathbb N\subset[U,2U),\qquad
N\subset[V,2V]\cap\mathbb N,\qquad |b_n|\le1.
\end{gathered} \tag{B2}
$$

Let $\alpha$ be the restriction to $K$ of either the prime discrepancy
or the $x^\gamma$-rough discrepancy on the complete cells of width
$L^{-S}$. Then

$$
|\mathcal T_\rho(K,N;\alpha,b)|\le CxL^{-D}
\qquad(\rho=\pm1). \tag{B3}
$$

The parameters $H,J,B,S,C$ are fixed before $\beta,\gamma$ and the
rectangle endpoints; the eventual threshold may depend on
$\beta,\gamma$. There is no regularity hypothesis on $b_n$.
An empty first interval gives zero and may be omitted.
Here $\mathcal T_\rho$ is (C4), with $w_\rho(u)=
\Psi(u/x)A_\rho(u)$ and $x=e^L$; thus the shift is $mn=u+2$.
The constants also depend on the fixed smooth cutoff $\Psi$ and the
reserved band $j_Q$. The integer $H$ is a Fourier-tail order, $J$ is
the number of additional shared marks, $B$ is the requested
complete-cell discrepancy order, and $S$ is its mesh exponent.

The range allows a companion factor of size $x^\eta$: if
$U\asymp x^{1-\eta}$ and $V\asymp x^\eta$, then
$E=UL^{-K_0}\le x^{1-\eta}$ eventually. More generally (B2) implies
$V\ge\tfrac14x^\eta L^{-K_0}$. In the sieve application one fixes
$\eta=b_1/12$ with $0<b_1<1/100$, so $0<\eta<1/1200$.
There is no lower bound on this fixed positive exponent independent
of $b_1$, but it cannot tend to zero with $L$ in this statement.
Uniformity in $b_n$ concerns the entire sum on scale $x$. For a
singleton $N=\{n\}$, (B3) still has right side $CxL^{-D}$, not
$C(x/n)L^{-D}$; it does not assert a prime-correlation saving at
the individual dilation's natural scale $x/n$.

The proof first establishes the same conclusion for each of the weights
$W(u)a(u_*)\varepsilon(u)$, where $\varepsilon=1$ or $\varepsilon=E(u)$.
The identity $A_\rho=(A_0+\rho A_0E)/2$ then proves (B3).

## 2. Allocating ordinary slots

Order the nonreserved ordinary slots by decreasing logarithmic scale,
breaking ties by their slot labels. Write their number as
$n=20(d+1)-1$, their scales as $s_i$, and their prime choices as $q_i$.
Repeated prime values retain their separate labels. An allocation
$\delta\in\{0,1\}^n$ assigns the slots with $\delta_i=1$ to a product
$e$ and the remaining slots to a product $r$.

Use two fixed smooth functions $f_0,f_1$, with values in $[0,1]$,
supported in $[-85,85]$. On $[-84,84]$ they are
$f_1(t)=h(t)$ and $f_0(t)=1-h(t)$, where $h$ is a smooth transition
equal to zero on $(-\infty,0]$ and one on $[1,\infty)$.
At slot $i$, set

$$
R_i=\log E-\sum_{j<i}\delta_j\log q_j,
\qquad
\prod_{i=1}^n f_{\delta_i}\left(\frac{R_i-\log q_i}{s_i}\right)
\tag{B4}
$$

for the allocation weight. The slot geometry makes these weights sum to
one on the relevant tuples and places every contributing selected product
in the interval

$$
EL^{-88}\le e\le E. \tag{B5}
$$

Here is the numerical reason for the lower endpoint. A skipped slot has
$R_i<\log q_i+s_i$. In every nonterminal band, the next band contains at
least nineteen nonreserved slots; their total logarithmic mass is at least
$(19/2)s_i>(11/5)s_i\ge\log q_i+s_i$.
In the last band, $s_d<40\log L$, so
$\log q_i+s_i\le88\log L$. Induction on the remaining slots bounds the
final residual by $88\log L$. A selected slot has $R_i>\log q_i$ and
therefore keeps the residual nonnegative. The same prefix bounds keep
each used argument inside the region where $f_0+f_1=1$; summing the two
choices successively proves the partition identity in (B4).

The initial supply condition is ensured after excluding a large marked
part. On $u\in[x,2x]$, a marked part at most $x^{\eta/4}$ and the reserved
prime at most $x^{\eta/4}$ leave at least $x^{1-\eta/2}$ in the remaining
ordinary slots, whereas $E\le x^{1-\eta}$. The Rankin estimate (W7)
bounds the excluded tuples by any prescribed logarithmic saving. The
finite source comparison also retains the Fourier truncation error;
its total, with coefficients of modulus at most one, is bounded by
$4xL^{-D}$ after the required precision is fixed.

For clarity, the Fourier-separated coefficients can be written explicitly.
Use $\mathrm e(t)=e^{2\pi it}$ and
$\widehat f(\xi)=\int f(t)\mathrm e(-t\xi)\,dt$. For fixed
$\delta,\boldsymbol\vartheta=(\vartheta_i)$, put

$$
\omega_i=-\frac{\vartheta_i}{s_i}
 -\delta_i\sum_{j>i}\frac{\vartheta_j}{s_j}.
$$

The exponent in Fourier inversion of (B4) is
$\log E\sum_i\vartheta_i/s_i+\sum_i\omega_i\log q_i$.
Define the two finite coefficient sums

$$
\begin{aligned}
b_e&=\sum_{\substack{(q_i)_{\delta_i=1}\\\prod q_i=e}}
        \prod_{\delta_i=1}\mathrm e(\omega_i\log q_i),\\
c_r&=(20!)^{-(d+1)}
      \sum_{\substack{(q_i)_{\delta_i=0}\\\prod q_i=r}}
        \prod_{\delta_i=0}\mathrm e(\omega_i\log q_i),\\
H(v_*)&=\sum_{\substack{p\in Q_{j_Q}\\p\mid v_*}}c_{v_*/p}.
\end{aligned} \tag{B6}
$$

Each prime variable lies in its assigned band. In particular $H$ retains
the reserved prime and all repeated-prime assignments.
For $v>0$, define

$$
a_v(v)=v^{i\tau}W(v)\varepsilon(v)H(v_*),
$$

and

$$
a_e(e)=1_{EL^{-88}\le e\le E}\,
\exp(i\tau\log e)\,\mathrm e\!\left(\log E\sum_i\vartheta_i/s_i\right)
\prod_i\widehat f_{\delta_i}(\vartheta_i)\,b_e. \tag{B7}
$$

Here $e$ in $\log e$ is the selected positive integer. With this
notation the finite sum to be estimated is

$$
\mathcal B'=\sum_e a_e(e)\sum_{n\in N}b_n
 \sum_{\substack{m\in K\\mn>2,\ e\mid mn-2}}
 \alpha(m)a_v((mn-2)/e). \tag{B8}
$$

This formula uses the actual integer $u=mn-2$. When a containing interval
is needed after Cauchy--Schwarz, $u\le\lceil6UV\rceil$ suffices.

At most $(20!)^{d+1}$ selected assignments can have a prescribed product.
Since $d+1\le2\log L$,

$$
|a_e(e)|\le G,
\qquad
G=L^{C_E}\prod_i|\widehat f_{\delta_i}(\vartheta_i)|. \tag{B9}
$$

For the complementary sum, the full factorial normalization in (B6)
gives $|c_r|\le1$. Thus $|H(v_*)|\le d_2(v_*)$, where $d_2$ is the
divisor-counting function, and $|a_v(v)|\le L^{C_W}d_2(v)$.

## 3. The positive square and the diagonal

Cauchy--Schwarz in $(e,n)$ gives

$$
|\mathcal B'|^2\le
\left(\sum_{e,n}|a_e(e)b_n|^2\right)
\sum_{e,n}\left|
 \sum_m\alpha(m)1_{e\mid mn-2}a_v((mn-2)/e)\right|^2.
\tag{B10}
$$

The first factor is at most $6EVG^2$. Enlarge the second, nonnegative
sum to all odd $e\le2E$ and all $n\le3V$, using a nonnegative smooth
weight $\eta_e(e/E)\eta_n(n/V)$ that is at least one on (B5) and
$n\in[V,2V]$. Its supremum is at most $2L^{88}$.
Here the supports are part of the construction:

$$
\eta_e(t)\ne0\Longrightarrow \tfrac12L^{-88}<t<2,
\qquad
\eta_n(t)\ne0\Longrightarrow \tfrac12<t<3. \tag{B10a}
$$

For completeness, put $a=L^{-88}$ and fix a smooth function $b$ with
$0\le b\le1$, supported in $(1/2,3/2)$ and equal to one on
$[2/3,4/3]$. The actual majorant is
$\eta_e(t)=b(t)+\sum_{j\ge0,\,2^ja\le1}b(t/(2^ja))$.
The plateaux of successive scales meet, so this is at least one on
$[a,1]$. Every scale lies in $[a,1]$, which proves (B10a).
The number of summands is at most $2L^{88}$ for $L\ge8$, and, for
$K_j=\|b^{(j)}\|_\infty$,
$\|\eta_e^{(j)}\|_\infty\le2K_jL^{88(j+1)}$.
The fixed bump $\eta_n$, equal to one on $[1,2]$ and supported in
$(1/2,3)$, has derivative bounds independent of $L$.
Only after this enlargement do we expand the square into its diagonal
and off-diagonal parts.

Write

$$
F_{e,n}(m)=\alpha(m)1_{mn>2,\ e\mid mn-2}a_v((mn-2)/e).
$$

The off-diagonal is the concrete finite sum

$$
\mathcal O=\sum_{\substack{e\le2E\\e\text{ odd}}}\sum_{n\le3V}
 \eta_e(e/E)\eta_n(n/V)
 \sum_{\substack{m,m'\in K\\m\ne m'}}
 F_{e,n}(m)\overline{F_{e,n}(m')}. \tag{B11}
$$

No positivity is used for (B11). Positivity was used only for the
unexpanded square in (B10).

For the diagonal, fix $u=mn-2$. There are at most $d_2(u+2)$ choices
of $(m,n)$ and at most $d_2(u)$ divisors $e$. The bound after (B9)
therefore gives an unweighted diagonal at most

$$
L^{2C_W}\sum_{1\le u\le\lceil6UV\rceil}d_2(u)^3d_2(u+2).
$$

The elementary divisor-moment estimate is

$$
\sum_{u\le Y}d_2(u)^3d_2(u+2)
 \le(Y+2)(1+\log(Y+2))^{255}. \tag{B12}
$$

Indeed, $d_2(u)^3d_2(u+2)\le d_2(u)^4d_2(u+2)^4$. Cauchy--Schwarz
bounds the sum by the eighth divisor moment up to $Y+2$. The pointwise
comparison $d_2(n)^8\le d_{256}(n)$ and successive harmonic summation give
$\sum_{n\le N}d_{256}(n)\le N(1+\log N)^{255}$. Since $UV\le C_{\rm box}x$, the right
side of (B12) is at most $xL^{256}$ eventually. Including the smoothing
weight gives

$$
\mathcal D\le2xL^{2C_W+344}. \tag{B13}
$$

Thus the remaining estimate needed for (B3) is an arbitrary logarithmic
saving for (B11), with all signed marked factors retained.

## 4. The shifted correlation

For a nonzero summand of (B11), both $mn-2$ and $m'n-2$ are divisible
by the odd integer $e$. The congruence $mn\equiv2\pmod e$ makes $n$
invertible modulo $e$, so $e\mid m'-m$. Put

$$
k=\frac{m'-m}{e}\ne0,\qquad
z=m'\frac{mn-2}{e},\qquad
z+2k=m\frac{m'n-2}{e}. \tag{B14}
$$

Both physical positions are positive. The support of the smoothing gives
$|k|\le L^{K_0+89}$ and places the dyadic scales of $z$ between
$xL^{-(K_0+90)}$ and $xL^{K_0+90}$, with a fixed enlargement for the
smooth dyadic partition. These bounds follow by substituting
$E=UL^{-K_0}$, $m,m'\asymp U$, and the support bounds on $e,n$.
Indeed, (B10a) gives $e>EL^{-88}/2$ and $n>V/2$, while
$|m'-m|\le U$. Thus $|k|<2L^{K_0+88}\le L^{K_0+89}$.
Also $m,m'\in[U,2U]$, $e<2E$ and $n<3V$ give
$cU^2V/E\le z\le CU^2VL^{88}/E$ for fixed $c,C>0$;
the lower bound uses $mn-2\ge mn/2$ eventually.
Together with $UV\asymp x$, these are the stated polynomial
logarithmic bounds, also for negative $k$.

The coefficient $\alpha$ is supported on integers with no prime factor
at most $W=e^{\sqrt L}$. Hence $m,m'$ are units modulo $2|k|$ eventually.
The odd quotient condition on $e$ is the following exact residue mask,
with $d_k=|k|$:

$$
T_{d_k}=
\begin{cases}\{d_k+1\}\pmod{2d_k},&d_k\text{ even},\\
\varnothing,&d_k\text{ odd}.
\end{cases}
$$

For characters modulo $2d_k$, define

$$
c_\chi=\frac1{\varphi(2d_k)}\sum_{r\in T_{d_k}}\overline{\chi(r)}.
$$

Character orthogonality gives

$$
1_{m'm^{-1}\in T_{d_k}}
 =\sum_\chi c_\chi\chi(m')\overline{\chi(m)},
\qquad\sum_\chi|c_\chi|\le1. \tag{B15}
$$

The smoothing factors have explicit expressions in the three logarithmic
coordinates $t_1=\log(m/U)$, $t_2=\log(m'/U)$ and
$t_3=\log(z/Z)$:

$$
\begin{aligned}
g_e(t)&=\frac{U}{kE}(e^{t_2}-e^{t_1}),\\
g_n(t)&=\frac{Z}{kUV}e^{t_3}(e^{-t_1}-e^{-t_2})
           +\frac{2}{UV}e^{-t_1}.
\end{aligned} \tag{B15a}
$$

They equal $e/E$ and $n/V$ respectively by (B14). Multiply
$\eta_e(g_e(t))\eta_n(g_n(t))$ by fixed smooth buffers in the three
coordinates, each equal to one on the relevant containing interval.
This gives a compactly supported function on a fixed logarithmic box.
Since $|k|\ge1$, $U/E=L^{K_0}$ and $Z/(UV)$ is bounded by a fixed
power of $L$, the chain rule and the derivative bounds after (B10a)
bound each of its fixed-order derivatives by a fixed power of $L$.
Fourier inversion of this three-variable function separates $m,m',z$;
the quantitative truncation is given in
[the frequency summation](bilinear.md#5-summing-frequencies-and-returning-to-the-bilinear-sum).

This reduces (B11) to correlations at the shift $2k$. Here are their
actual coefficient functions. For the residual $c$ in (B6), write

$$
H_\sigma(v)=\sum_{\substack{p\in Q_{j_Q}\\p\mid v}}p^{i\sigma}c_{v/p},
$$

and, for $n>0$, put

$$
\begin{aligned}
F(n)&=\sum_{m\mid n_*}\overline{\alpha(m)}\chi(m)
       m^{i(\xi_2-\tau)}H_\sigma(n_*/m),\\
G(n)&=\sum_{m\mid n_*}\alpha(m)\overline{\chi(m)}
       m^{i(\xi_1+\tau)}\overline{H_\sigma(n_*/m)}.
\end{aligned} \tag{B16}
$$

The same original $\alpha$ occurs at both endpoints, with the displayed
conjugation. If $m$ supports $\alpha$, dividing by $m$ removes no marked
prime. Thus $W(n/m)=W(n)$ and $\varepsilon(n/m)=\varepsilon(n)$ whenever
$m\mid n_*$. Multiplicativity of imaginary powers then turns the full
cofactor expansion exactly into

$$
\begin{aligned}
\mathcal C_{k,Z}=
\sum_{\substack{z\ge1\\z+2k>0}}
&\psi(z/Z)z^{i(\tau+\xi_3)}(z+2k)^{-i\tau}
 F(z)G(z+2k)\\
&\hspace{4mm}\cdot W(z)W(z+2k)\varepsilon(z)\varepsilon(z+2k).
\end{aligned} \tag{B17}
$$

The smooth function $\psi$ is supported in $[1/64,64]$, so the sum is
finite. The marked-correlation estimate says that, for any fixed
$D_1,C_Z,C_k,C_f>0$, the mesh can be chosen so that

$$
|\mathcal C_{k,Z}|\le ZL^{-D_1} \tag{B18}
$$

uniformly for $0<|k|\le L^{C_k}$,
$xL^{-C_Z}\le Z\le xL^{C_Z}$, characters modulo $2|k|$, both choices of
$\varepsilon$, and $|\tau|,|\sigma|,|\xi_i|\le L^{C_f}$.
The cutoff is smooth with fixed support and prescribed bounds on its
logarithmic derivatives. The approximation parameters precede the fine
interval's positive lower exponent and the roughness exponent.

The proof of (B18) is given in [marked-correlation.md](marked-correlation.md).
It combines alternating coordinate averages, their arithmetic character
approximation, a physical moment estimate, and a separate discrepancy
bound for the comparison term.
The scope of this assertion matters. $\alpha$ is exactly the restricted
discrepancy (C1), and $c_r$ is exactly the ordinary-slot coefficient
(B6), for an arbitrary allocation and arbitrary slot Fourier frequencies.
Only the external frequencies $\tau,\sigma,\xi_1,\xi_2,\xi_3$ have
the displayed polynomial restriction. For every fixed $j_Q,D_1,C_Z,C_k,
C_f$ and cutoff derivative budget, there are common $J,B,S$; for
each fixed $\beta,\gamma>0$ there is then one threshold, uniform in
the fine interval, its further restriction, allocation, slot frequencies,
character, external frequencies, shift and scale. The result is not
claimed for an arbitrary bounded first coefficient $\alpha$.

## 5. Summing frequencies and returning to the bilinear sum

For completeness, the losses in passing from (B18) to (B11) can be paid
before choosing the cell mesh. Fix the desired off-diagonal accuracy $A$
and let

$$
D_{\rm tail}=A+K_0+200,\qquad
D_{\rm main}=K_0+315+D_{\rm tail}.
$$

Fix an integer $P>3$, so $(1+\|t\|)^{-P}$ is integrable on
$\mathbb R^3$, and set

$$
\begin{aligned}
p_0&=5(K_0+90)(P+1),&p_1&=5(K_0+90)(P+2),\\
D_1&=D_{\rm main}+p_0,&
C_f&=p_1+D_{\rm main}+2C_W+30,\qquad T_f=L^{C_f}.
\end{aligned}\tag{B19}
$$

The five factors defining the cutoff $f=f_{k,Z,L}$ are the two
compositions after (B15a) and the three fixed buffers. They have
common compact support. The chain and product rules give, for each
fixed derivative order $j$, a bound
$\|\partial^j f\|_\infty\le C_jL^{5(K_0+90)(j+1)}$.
Integration by parts through orders $P$ and $P+1$, respectively,
on this fixed support,
therefore gives the two uniform moment bounds

$$
\int_{\mathbb R^3}|\widehat f(\zeta)|\,d\zeta
 \le C_0'L^{p_0},\qquad
\int_{\mathbb R^3}\|\zeta\||\widehat f(\zeta)|\,d\zeta
 \le C_1L^{p_1}.
\tag{B19a}
$$

The constants $C_0',C_1$ depend on the fixed buffers, not on
$L,k,Z$ or the fine cells. In particular the zeroth Fourier moment
itself need not be bounded independently of $L$.

Split Fourier inversion at the ball of radius $T_f$. On the ball,
apply (B18) with saving $D_1$, after shifting $\xi_i$ by $2\pi$
times the Fourier variables and increasing the fixed frequency
exponent. The character coefficients have total modulus at most one
by (B15). Thus the integrated principal term at each $k,Z$ is at most

$$
ZL^{-D_1}C_0'L^{p_0}=C_0'ZL^{-D_{\rm main}}.
\tag{B19b}
$$

There are at most $O(L^{K_0+89})$ shifts and $O(L)$ dyadic scales;
their largest scale is $O(xL^{K_0+90})$. Hence the sum of (B19b)
is $O(xL^{2K_0+180-D_{\rm main}})$, which is $O(xL^{-A})$.
The extra $p_0$ in the requested correlation precision is essential
and is chosen before $J,B,S$.

Outside the ball, use

$$
\int_{\|\zeta\|>T_f}|\widehat f(\zeta)|\,d\zeta
\le T_f^{-1}\int\|\zeta\||\widehat f(\zeta)|\,d\zeta. \tag{B20}
$$

Finite sums of absolute coefficient values and the derivative bounds for
the scaled cutoffs give a polynomial factor in $L$; the additional powers
in (B19) make the total tail $O(xL^{-D_{\rm tail}})$.
In this comparison, a physical pair where a cutoff vanishes is still
included in the finite Fourier integral. Its full Fourier integral is
zero, so its truncated contribution equals minus its tail and is bounded
by (B20). This accounts for the two endpoint cutoff errors without
discarding a signed subfamily.

The resulting bounds are

$$
|\mathcal O_{\rm ball}|\le C_{\rm phys}xL^{-A},\qquad
|\mathcal O-\mathcal O_{\rm ball}|\le24C_1xL^{-D_{\rm tail}},
$$

where $C_1$ is the fixed coefficient in (B19a), and
$C_{\rm phys}=250C_{\rm box}(1+2/\log2)(C_0'+132C_1)$ with a fixed
zeroth-moment coefficient $C_0'$. Hence

$$
|\mathcal O|\le(C_{\rm phys}+24C_1)xL^{-A}. \tag{B21}
$$

Together, (B10), (B13), and (B21) give

$$
|\mathcal B'|^2\le6EVG^2
 \left(2xL^{2C_W+344}+(C_{\rm phys}+24C_1)xL^{-A}\right).
$$

Since $EV\le C_{\rm box}xL^{-K_0}$, (B1) implies
$|\mathcal B'|\le C'GxL^{-A}$ for a fixed $C'$.

Let $M_f\ge1$ bound the $L^1$ norms of $\widehat f_0,\widehat f_1$.
There are at most $40\log L$ nonreserved slots. Integrating all slot
frequencies and summing the two choices at each slot costs at most

$$
(2M_f)^n\le L^{C_F},\qquad C_F=40\log(2M_f). \tag{B22}
$$

Thus (B9) and (B1) absorb the total loss $L^{C_E+C_F}$.
Finally write $\psi_0(t)=\Psi(e^t)$ and restore the localization by
Fourier inversion. The moments

$$
M_0=\int|\widehat\psi_0(s)|\,ds,\qquad
M_H=\int|s|^H|\widehat\psi_0(s)|\,ds
$$

are finite. The first controls bounded Mellin frequencies; for the tail
choose $H$ large enough and use the second. With the source-comparison
error from [the slot allocation](bilinear.md#2-allocating-ordinary-slots),
the resulting constant is bounded by
$4+C'M_0+20(2\pi)^HM_H$. This proves (B3) once (B18) has been established.

## Source correspondence

| Argument | Lean source |
| --- | --- |
| Common-precision rectangle statement | [Foundations/Part050](../Green64/Library/Sieve/Foundations/Part050.lean): `parity_eventually_original_signed_quarter_b629_fine_one_slot_Psi_Mellin_source_anylog_common_precision434` |
| Smooth allocation functions | [Weights/Part003](../Green64/Library/Weights/Part003.lean): `sourceBufferedGateReal` |
| Slot ordering and frequency scales | [Correlation/Part065](../Green64/Library/Correlation/Part065.lean): `sourceOrderedLabels`, `sourceActualSortedFrequencyScales` |
| Prefix bounds, partition, and the exponent $88$ | [Weights/Part117](../Green64/Library/Weights/Part117.lean) |
| Fourier phases and endpoint sums | [Weights/Part020](../Green64/Library/Weights/Part020.lean), [Foundations/Part009](../Green64/Library/Sieve/Foundations/Part009.lean), [Part011](../Green64/Library/Sieve/Foundations/Part011.lean) |
| Intrinsic $H$ and $a_v$ | [Foundations/Part017](../Green64/Library/Sieve/Foundations/Part017.lean): `parityOriginalIntrinsicH434`, `parityOriginalIntrinsicSignedAV434` |
| Windowed $a_e$ and source comparison | [Foundations/Part018](../Green64/Library/Sieve/Foundations/Part018.lean): `parityOriginalHistoricalWindowAE434` |
| Finite $\mathcal B'$ and divisor-moment diagonal | [Foundations/Part032](../Green64/Library/Sieve/Foundations/Part032.lean): `parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434` |
| Smooth square and exact off-diagonal | [Foundations/Part022](../Green64/Library/Sieve/Foundations/Part022.lean), [Part025](../Green64/Library/Sieve/Foundations/Part025.lean), [Part028](../Green64/Library/Sieve/Foundations/Part028.lean) |
| Shift coordinates and residue mask | [Foundations/Part019](../Green64/Library/Sieve/Foundations/Part019.lean), [Part029](../Green64/Library/Sieve/Foundations/Part029.lean), [Weights/Part005](../Green64/Library/Weights/Part005.lean) |
| Exact two-endpoint cofactor identity | [Weights/Part102](../Green64/Library/Weights/Part102.lean): `b633_parity_full_physical_pair434` |
| Physical correlation saving (B18) | [Foundations/Part008](../Green64/Library/Sieve/Foundations/Part008.lean): `parity_eventually_actual_original_Parity417_physical_cofactor_saving_common_precision434` |
| Actual Fourier moments (B19a) and the extra precision in (B19b) | [Foundations/Part026](../Green64/Library/Sieve/Foundations/Part026.lean): `parity_original_historical_full_odd_3d_fourier_moment_uniform_polylog434`; [Part032](../Green64/Library/Sieve/Foundations/Part032.lean): `parity_original_historical_box_source_BH_uniform_polylog434`; [Part037](../Green64/Library/Sieve/Foundations/Part037.lean): `parity_original_actual_capfree_Bprime_M0_uniform_polylog434`, `parity_original_actual_capfree_Bprime_primary_inverse_log_from_M0434` |
| Fourier ball, tails, and common precision | [Foundations/Part046](../Green64/Library/Sieve/Foundations/Part046.lean), [Part049](../Green64/Library/Sieve/Foundations/Part049.lean), [Part050](../Green64/Library/Sieve/Foundations/Part050.lean) |
