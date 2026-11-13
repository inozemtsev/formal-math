# Sieve estimates and the remaining composites

We use the definitions of $w_\rho$, $X_\rho$, and $\mathfrak S$ in
[the main proof](proof.md). The common outer cutoff is
$Y=\lfloor2e^L\rfloor$, because $\Psi$ is supported in $[1,2]$.

## 1. Local densities

Write

$$
V(y)=\prod_{p\le y}(1-1/p),\qquad
V_2(y)=\prod_{3\le p\le y}(1-1/(p-1)).
$$

Every prime factor of a supported integer $u$ is at least $L^{20}$.
For large $L$ this makes $u$, and therefore $u+2$, odd. At an odd prime the excluded unit residue is
$-2$, and the density of the divisibility condition is $g(p)=1/(p-1)$.
The identity

$$
1-\frac1{p-1}=(1-1/p)\left(1-\frac1{(p-1)^2}\right)
$$

gives $V_2(y)/V(y)\to\mathfrak S$. Consequently
$V_2(x^b)\sim\mathfrak S e^{-\gamma_E}/(bL)$ for fixed $b>0$.
The product defining $\mathfrak S$ converges because
$\sum_{p\ge3}(p-1)^{-2}<\infty$. It is at least one: each factor lies in
$(0,1)$, so comparison with all integer indices gives

$$
\prod_{p\ge3}\left(1-\frac1{(p-1)^2}\right)
\ge\prod_{n=2}^{\infty}(1-n^{-2})=\frac12.
$$

The congruence estimate used here is specifically for the negative parity
weight. Put

$$
r(d)=\sum_{d\mid u+2}w_{-1}(u)-\frac{X_{-1}}{\varphi(d)}.
$$

For every fixed $0<\vartheta<1/2$, some $C\ge0$ satisfies,
eventually,

$$
\sum_{\substack{d\le x^\vartheta\\d\text{ odd and squarefree}}}|r(d)|
\le C\bigl(xL^{-230}+X_{-1}L^{-18}\bigr). \tag{S1}
$$

The [residue-class chapter](congruences.md) proves the stronger version
with any fixed accuracy in place of $230$. Character orthogonality
separates nonprincipal characters from the nonunit correction. A reserved
ordinary prime slot, Siegel--Walfisz, and the multiplicative large sieve
control the former; the $L^{20}$-rough support controls the latter.
By $X_{-1}\ge c_0xL^{-221}$, the right side of (S1) is $o(X_{-1}/L)$:
the two ratios are bounded by constants times $L^{-8}$ and $L^{-17}$.

## 2. Positive rectangles

Let $A,B,C,E$ be natural numbers with $A\le B$ and $C\le E$, and let
$K\subset[A,B)$ and $N\subset[C,E)$ be finite sets of positive integers.
For a roughness threshold $W$, define the nonnegative sum

$$
\mathcal R_\rho(K,N;W)
=\sum_{u\le Y}w_\rho(u)
  \sum_{\substack{m\in K,\ n\in N\\mn=u+2}}
    R_W(m)R_W(n).
$$

Fix positive constants
$C_{\rm area},C_{\rm side}$. If

$$
(B-A)(E-C)\le C_{\rm area}x,
\qquad (B-A)+(E-C)\le C_{\rm side}x^{27/50},
$$

then, for $W=e^{\sqrt L}$, there is a constant $C_{\rm box}>0$ such that

$$
\mathcal R_\rho(K,N;W)\le C_{\rm box}X_\rho V(W)^2. \tag{S2}
$$

The constant and the sufficiently large threshold for $L$ precede both
parity signs and all the finite carriers and endpoints.

This is the specialization $W=e^{\sqrt L}$ of
[the normalized rectangle estimate](rectangles.md#4-normalization-by-the-actual-mass).
Its extra sieve factor $V(x^{\theta_0})$ controls prime divisors of
$mn-2$, while the two factors $V(W)$ impose roughness on $m,n$.
That normalization proves the stated uniformity before any balanced
width is chosen.

## 3. Counting balanced rectangles

Put

$$
\mathcal B_\kappa=[x^{1/2-2\kappa},x^{1/2+2\kappa}],
\qquad0\le\kappa\le1/50.
$$

Partition each positive factor by its unique binary index
$k=\lfloor\log_2m\rfloor$. Only rectangles containing a pair with
$mn=u+2$ and $\Psi(u/x)\ne0$ need to be retained. If $(k,j)$ is such a
pair of indices, its geometry implies

$$
x/4<2^k2^j\le4x,
\qquad
x^{1/2-2\kappa}<2^{k+1},\quad 2^k\le x^{1/2+2\kappa}.
$$

The number of first indices is at most $4\kappa L/\log2+2$.
For each first index there are at most five second indices, because their
powers of two lie in an interval with ratio sixteen. Thus the number of
active rectangles is at most

$$
C_{\rm dyad}(\kappa L+1),\qquad
C_{\rm dyad}=5(4/\log2+2). \tag{S5}
$$

The active rectangles partition the supported factor pairs. Each has
area at most $4x$ and side sum at most
$2x^{1/2+2\kappa}\le2x^{27/50}$, so (S2) applies with fixed constants.

Summing (S2) and applying (S5) gives

$$
\sum_{\substack{mn=u+2\\m,n\in\mathcal B_\kappa\\
P^-(m),P^-(n)>W}}w_\rho(u)
\le C_1(\kappa L+1)X_\rho V(W)^2. \tag{S6}
$$

The constant $C_1$ is chosen before $\kappa$.

## 4. Removing the unbalanced composites

The approximation estimate in [correlation.md](correlation.md) permits
replacement of the roughness test on the cofactor of a least prime divisor.
The number of bins is fixed before the approximation parameters; the
parameter theorem remains uniform over the subsequent choice of endpoints.

For small fixed $b>0$, define the rough-number density by

$$
D_b(w)=\frac1w+
\sum_{k\ge2}\frac1{k!}
\int_{\substack{t_1,\ldots,t_{k-1}\ge b\\
                 t_1+\cdots+t_{k-1}\le w-b}}
\frac{dt_1\cdots dt_{k-1}}
 {t_1\cdots t_{k-1}(w-t_1-\cdots-t_{k-1})}.
$$

Only finitely many terms can be nonzero, since the domain is empty
when $kb>w$. The [finite block sieve](block-sieve.md) gives
the preliminary-sieve constant
$C_s=3\exp(8e+16)/(1-e^{-1})$, independent of $b$. Set

$$
A_b=\frac{e^{-\gamma_E}}b
       \left(1-C_s e^{-1/(40b)}\right).
$$

The preliminary sieve and (S1) give, eventually,

$$
\sum_{P^-(u+2)>x^b}w_{-1}(u)
\ge\left(\mathfrak S A_b-\frac{\mathfrak S}{10}\right)
       \frac{X_{-1}}L. \tag{S7}
$$

Choose a finite monotone partition of $(b,1/2-\kappa]$.
For a bin $(\gamma,\gamma']$, the cofactor test is
$1_{P^-(m)>x^\gamma}$ and the other factor is a prime
$n\in(x^\gamma,x^{\gamma'}]$. The sum over all such ordered pairs
dominates the composites whose least prime factor is in that bin:
choose $n=P^-(u+2)$ and $m=(u+2)/n$. No uniqueness of the other
representations is needed because their weights are nonnegative.

For a fixed bin $(\gamma,\eta]$, put

$$
C_{\gamma,\eta}=\sup_{\gamma\le t\le\eta}D_\gamma(1-t),
\qquad
F_{\gamma,\eta}=
\sum_{x^\gamma<p\le x^\eta}
\sum_{\substack{p\mid u+2\\P^-(u+2)>W}}w_{-1}(u),
\quad W=e^{\sqrt L}.
$$

The cofactor $m=(u+2)/p$ has logarithmic exponent in
$[1-\eta,1-\gamma+o(1)]$. The full-cell roughness approximation satisfies,
for every fixed $\delta>0$, eventually on these pairs,

$$
0\le B_{R_{x^\gamma}}(m)
\le\frac{C_{\gamma,\eta}+\delta}{L V(W)}. \tag{S8a}
$$

To obtain (S8a), count products of a fixed number of primes in each
complete logarithmic cell. The prime number theorem and partial
summation give the reciprocal-simplex integrals defining $D_\gamma$.
There are only finitely many possible numbers of prime factors on the
fixed compact exponent range. The denominator in the cell ratio is
its length times $V(W)(1+o(1))$, by the finite rough sieve.
Joint continuity of $D_\gamma(w)$ on this compact range absorbs the
$o(1)$ overshoot at $1-\gamma$ and gives the displayed supremum bound.

If the cofactor approximation is nonzero, then $m$ is $W$-rough.
Since the prime $p>x^\gamma$ also exceeds $W$, the product $u+2=mp$
is $W$-rough, even when $p\mid m$. Reindexing the ordered pair sum by
$p$ and $u$ therefore bounds its approximated value by
$(C_{\gamma,\eta}+\delta)F_{\gamma,\eta}/(LV(W))$.

The conditioned sieve gives

$$
\frac{F_{\gamma,\eta}}{X_{-1}V(W)}
\longrightarrow\mathfrak S\log(\eta/\gamma). \tag{S8b}
$$

Here one chooses $\eta<\vartheta<1/2$ in (S1). For a fixed
$p\in(x^\gamma,x^\eta]$, sieve the condition $p\mid u+2$ by primes
at most $W$. Since $p>W$, its local density separates as
$g(pd)=g(p)g(d)$ for each sieve divisor $d$. The main term is
$X_{-1}g(p)V_2(W)$. Summing over $p$ gives
$\sum g(p)\to\log(\eta/\gamma)$ by the prime reciprocal-sum estimate.
The sieve level can be chosen below $x^\vartheta/p$; its logarithm
divided by $\log W$ tends to infinity uniformly in this bin. Thus its
relative sieve error tends to zero. In the remainder sum, each integer
$pd\le x^\vartheta$ has at most $\vartheta/\gamma$ possible prime factors
from the bin, a fixed bound. Estimate (S1) consequently controls the
summed remainders. Finally $V_2(W)/V(W)\to\mathfrak S$, proving (S8b).

Combining (S8a) and (S8b), and taking $\delta$ sufficiently small, gives
for any $\varepsilon>0$ the per-bin bound

$$
U^{\rm proxy}_{\gamma,\eta}
\le\left(\mathfrak S C_{\gamma,\eta}\log(\eta/\gamma)
          +\varepsilon\right)\frac{X_{-1}}L. \tag{S8c}
$$

For completeness, the choice of partition in this sum is independent
of all subsequent approximation parameters. Set $c=1/2-\kappa$.
The function $F(s,t)=D_s(1-t)$ is continuous on $[b,c]^2$.
Given $\varepsilon>0$, uniform continuity permits an affine grid
$t_i=b+(c-b)i/N$, with $N>0$ fixed, for which

$$
\sum_{i<N}C_{t_i,t_{i+1}}\log(t_{i+1}/t_i)
\le\int_b^c D_t(1-t)\,\frac{dt}{t}+\varepsilon.
$$

Indeed, on each cell the supremum differs from $F(t,t)$ by at most
$\varepsilon/\log(c/b)$; integration against $dt/t$ makes these errors
sum to at most $\varepsilon$.

Partitioning each prime-factor simplex by its least coordinate gives

$$
\int_b^{1/2}D_t(1-t)\,\frac{dt}{t}=D_b(1)-1.
$$

The one-factor term is $1$. In a $k$-factor term, choose its least
coordinate $t$ and integrate the remaining $k-1$ coordinates with lower
bound $t$; the $k$ choices change $1/k!$ to $1/(k-1)!$.
The sets where two coordinates tie have measure zero. All terms are
nonnegative and only finitely many can be nonzero, which justifies the
partition and integration. Restricting the integral to $[b,c]$ only
reduces it. Choose the grid above with $\varepsilon=1/10$.
Sum (S8c) over this fixed grid and use the approximation error
$o(X_{-1}/L)$ from [correlation.md](correlation.md). Allocating the finite
per-bin errors and the replacement error gives

$$
U\le\left(\mathfrak S(D_b(1)-1+1/10)
                   +\frac{\mathfrak S}{10}\right)\frac{X_{-1}}L.
\tag{S8}
$$

The needed small-$b$ estimate is the one-sided bound

$$
D_b(1)\le\frac{e^{-\gamma_E}}b
 \left(1+C_{\rm sieve}e^{-1/(40b)}\right),\qquad0<b\le1/100.
\tag{S8d}
$$

To prove this, let $R_b(z)$ count the
integers in $(0,z]$ with no prime factor at most $z^b$, and take the even
sieve depth $h=2\lfloor1/(40b)\rfloor$. The finite rough sieve gives

$$
R_b(z)\le zV(z^b)(1+C_{\rm sieve}e^{-h})
                 +2z^{b(4h+2)}.
$$

For $b\le1/100$, $h\ge1/(40b)$ and
$b(4h+2)\le1/5+2b<1$. The last term disappears after multiplication
by $\log z/z$. Mertens' formula gives
$(\log z)V(z^b)\to e^{-\gamma_E}/b$.
On the other hand, counting products of distinct primes in compact
subsets of the simplices by the prime number theorem gives

$$
D_b(1)\le\liminf_{z\to\infty}\frac{\log z}{z}R_b(z).
$$

To see the factorial, count ordered $k$-tuples and divide by $k!$;
distinct tuples have exactly $k!$ orderings. Repeated-prime tuples may
be discarded in this lower bound. Refine the compact grids and let their
boundaries tend to the simplex boundary; positivity gives the complete
integral. Again $k\le1/b$ is bounded for fixed $b$. Combining the lower
comparison with the upper sieve bound proves (S8d).

Now put $b=1/(40T)$, with $T\ge25$ chosen so large that

$$
40e^{-\gamma_E}(C_s+C_{\rm sieve})Te^{-T}\le1/10.
$$

Such a $T$ exists because $Te^{-T}\to0$. Then $0<b\le1/1000$, and (S8d)
gives

$$
A_b-(D_b(1)-1+1/10)
\ge\frac9{10}
 -\frac{e^{-\gamma_E}}b(C_s+C_{\rm sieve})e^{-1/(40b)}
\ge\frac45.
$$

Subtracting (S8) from (S7) leaves at least
$(4/5-1/10-1/10)\mathfrak S X_{-1}/L$, which is at least
$(\mathfrak S/2)X_{-1}/L$.

Every composite surviving that subtraction has least prime factor greater
than $x^{1/2-\kappa}$. The finite partition theorem accounts for the strict
lower and closed upper endpoints of every bin. Hence

$$
\mathcal M_{-1}+\mathcal C_{-1}(L,\kappa)
\ge\frac{\mathfrak S}{2}\frac{X_{-1}}L. \tag{S9}
$$

## 5. Balanced composites

For sufficiently large $x$, a composite $u+2\le2x+2$ whose least prime factor
exceeds $x^{1/2-\kappa}$ has exactly two prime factors, counted with
multiplicity: three factors would give
$u+2>x^{3(1/2-\kappa)}>2x+2$. Both factors lie in
$\mathcal B_\kappa$. The argument includes a square of a prime.
Let $I(m)=1_{m\text{ prime}}$, and let $B(m)$ be its full-cell approximation.
The complete-cell prime estimate gives
$0\le B(m)\le3/(LV(W))$ on the balanced range, with rough support.
Therefore (S6) bounds the pair sum with two approximations by

$$
9C_1(\kappa+1/L)\frac{X_\rho}L.
$$

For fixed $\kappa>0$, eventually $1/L\le\kappa$. Thus the constant
$C_{\rm bal}=18C_1$ works for the approximated sum, independently of
$\kappa$ and of the cell precision.

There are exactly two replacement steps:

$$
I(m)I(n)-B(m)B(n)
=(I(m)-B(m))I(n)+B(m)(I(n)-B(n)).
$$

The companion in the second step is bounded but need not be smooth.
Their total is bounded by $\mathcal E(L)=o(X_\rho/L)$ from (C9)--(C12).

It follows that for every fixed $0<\kappa<1/50$ and $\varepsilon>0$,
eventually for both signs,

$$
\mathcal C_\rho(L,\kappa)
\le(C_{\rm bal}\kappa+\varepsilon)\frac{X_\rho}L. \tag{S10}
$$

The bound holds first for the ordered prime-pair sum and hence for the
composite mass it covers. For (S10), the auxiliary partition may be fixed
to one admissible bin with lower endpoint $1/200$. Equations (S9) and
(S10) are the two estimates used in the main proof.

## Source correspondence

| Text | Definitions and proved identities |
| --- | --- |
| Singular product and (S1) | [Foundations/Part006](../Green64/Library/Sieve/Foundations/Part006.lean): `singularSeries_converges_and_ge_one`; the congruence source map is in [congruences.md](congruences.md#source-correspondence) |
| (S6), balanced rectangle count | [BalancedBoxes](../Green64/Sieve/BalancedBoxes.lean): `balanced_rough_pair_bound` |
| (S7)--(S8d), rough density and the full-cell estimate | [Estimates/Part003](../Green64/Library/Analysis/Estimates/Part003.lean): `sourceDensity` (the displayed index is $k=n+2$); [Weights/Part037](../Green64/Library/Weights/Part037.lean): `sourceD29_original_full_proxy_pointwise_compact`, `literal_density_rough_unconditional`, `literal_small_b_exp_bound_unconditional` |
| Conditional Euler limit and (S9) | [Foundations/Part055](../Green64/Library/Sieve/Foundations/Part055.lean): `parity_original_negative_conditional_natural_euler_limit434`, `negative_prime_or_composite_mass_lower_bound` |
| (S10), composite cover and two proxy errors | [Foundations/Part052](../Green64/Library/Sieve/Foundations/Part052.lean): `parity_eventually_original_balanced_composite_prime_pair434`; [ApproximationError](../Green64/Sieve/ApproximationError.lean): `balancedTwoStepError`; [BalancedMass](../Green64/Sieve/BalancedMass.lean) |

The one-bin specialization for (S10) is in
[CompositeMass](../Green64/Sieve/CompositeMass.lean).
