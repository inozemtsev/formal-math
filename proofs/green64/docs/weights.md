# The weights and their mass

We use the notation and fixed prime bands from [the main proof](proof.md).
This file proves nonnegativity, the parity implication, and the uniform
lower bound $X_\rho\gg xL^{-221}$.

## 1. Geometry and exact factorization

The inequalities

$$
1<\frac65<\frac32<\frac95<2,\qquad\frac9{10}<1
$$

separate the two intervals at a given dyadic scale from each other and
from the intervals at the next scale. Thus no prime occurs in two bands.
Every $Q_j$ prime is at least $e^{20T}=L^{20}$. Every $P_g$ prime is at
least $\exp(L^{1/10})$, which exceeds $L^{20}$ eventually.

The logarithm of the ratio of the endpoints of any one band, measured in
the logarithmic variable, is $\log(6/5)$. The prime number theorem and
partial summation therefore give

$$
\sum_{e^a\le p\le e^{6a/5}}\frac1p
  =\log(6/5)+o(1)\qquad(a\to\infty).
$$

The error is uniform when $a\ge20T$. We use the weaker uniform bounds

$$
\frac1{12}\le V_j\le4,\qquad \nu\le M_g\le4,
\qquad \nu=\frac14\log\frac{12}{11}>0.
$$

The containment conditions give $O(T)$ marked groups and at least one
group for all sufficiently large $L$. The moving ordinary depth satisfies
$d+1\le2T$. The containment conditions retain both endpoints of each
whole prime interval.

For $u>0$ the decomposition $u=u_*u_{\mathcal P}$ is unique. Its factors
are coprime because their prime supports are disjoint. If $a(u_*)>0$,
then $\Omega(u_*)=20(d+1)$. Complete additivity of $\Omega$ on positive
integers gives

$$
\lambda(u)=(-1)^{20(d+1)}
 (-1)^{\sum_{p\in\mathcal P}v_p(u)}=E(u).
$$

The projection $(1+\rho E(u))/2$ is either zero or one. This proves
$A_\rho\ge0$ and the implication $A_\rho(u)>0\Rightarrow\lambda(u)=\rho$.
In particular, repeated ordinary primes contribute their full multiplicity;
replacing $\Omega$ by the number of distinct prime divisors would invalidate
this step.

For $k\ge1$, $k2^{-(k-1)}\le1$. Since $a(v)\le1$ and $M_g\ge\nu$,

$$
0\le w_\rho(u)\le A_\rho(u)\le W(u)a(u_*)
 \le\nu^{-|\mathcal G|}\le L^{C_0}. \tag{W1}
$$

## 2. Harmonic probability laws

Put

$$
H_Q=\prod_{j=0}^d\frac{V_j^{20}}{20!}.
$$

Expanding the product over the ordered ordinary slots gives the exact
identity

$$
\sum_{v\ge1}\frac{a(v)}v=H_Q. \tag{W2}
$$

For one marked group define

$$
Z_g(q)=\prod_{p\in P_g}\left(1+\frac q{p-1}\right),\qquad
H_g=\frac{Z'_g(1/2)}{M_g},\qquad H_P=\prod_gH_g.
$$

A nonempty set of distinct group primes of size $k$ receives the factor
$k(1/2)^{k-1}/M_g$. Summing all positive multiplicities of a prime gives
$\sum_{a\ge1}p^{-a}=1/(p-1)$. Differentiating the finite product $Z_g$
therefore proves

$$
H_g=\sum_{\substack{n\ge1\\p\mid n\Rightarrow p\in P_g}}
 \frac{\omega_g(n)2^{-(\omega_g(n)-1)}}{M_gn}
 =\frac{Z_g(1/2)}{M_g}\sum_{p\in P_g}\frac1{p-1/2}.
 \tag{W3}
$$

The zero term for $n=1$ is understood. All series here are absolutely
convergent. Since the prime sets are disjoint, multiplying (W3) gives

$$
\sum_{n:n_*=1}\frac{W(n)}n=H_P. \tag{W4}
$$

The harmonic bounds and $\log(1+t)\le t$ give $Z_g(1/2)\le C$ and
$\sum_{p\in P_g}(p-1/2)^{-1}\le C M_g$ for an absolute $C$.
The reverse inequality $(p-1/2)^{-1}\ge p^{-1}$ gives

$$
1\le Z_g(1/2)\le H_g\le C,
\qquad 1\le H_P\le L^{C_1}. \tag{W5}
$$

Define independent random positive integers $V$ and $R$ by

$$
\Pr(V=v)=\frac{a(v)}{vH_Q},\qquad
\Pr(R=n)=\frac{W(n)}{nH_P}\quad(n_*=1).
$$

The law of $V$ can be realized by independent choices in the twenty slots
of each $Q_j$, each prime $q\in Q_j$ having probability $1/(qV_j)$.
The prime-group components of $R$ are independent as well.

For a single group, total multiplicity one has unnormalized harmonic
mass $M_g/M_g=1$. Total multiplicity two arising from two distinct primes
has mass

$$
\frac1{M_g}\sum_{p<q\in P_g}\frac1{pq}
 =\frac{M_g^2-\sum_{p\in P_g}p^{-2}}{2M_g}.
$$

The second expression is bounded below by a positive absolute constant:
$M_g\ge\nu$ and $\sum p^{-2}=o(1)$ uniformly. By (W5), division by
$H_g$ leaves a positive uniform probability for both parities. Condition
on every group except one. Whatever the parity of their product, the
remaining group can supply either total parity. Hence there is $\delta>0$
such that

$$
\Pr(E(R)=\rho)\ge\delta\qquad(\rho=\pm1). \tag{W6}
$$

We also need a tail estimate. Take $t=L^{-2/5}$. Replace each factor
$1/(p-1)$ in the Euler-product calculation by
$p^{-1+t}/(1-p^{-1+t})$. Since $\log p\le L^{2/5}$, we have
$p^t\le e$. The harmonic sums of these replacement factors are bounded
uniformly, as are the corresponding differentiated finite products.
There are $O(T)$ groups, so

$$
\sum_{n:n_*=1}\frac{W(n)}{n^{1-t}}\le L^{C_2}.
$$

For every fixed $\eta>0$, multiplication by $x^{-\eta t}$ then gives

$$
\sum_{\substack{n>x^\eta\\n_*=1}}\frac{W(n)}n
 \le L^{C_2}\exp(-\eta L^{3/5}). \tag{W7}
$$

Because $H_P\ge1$, (W7) also bounds $\Pr(R>x^\eta)$.
This estimate retains all positive prime multiplicities in $R$.

## 3. Localization

Set $U=VR$. The disjoint prime supports make the factorization into $V$
and $R$ unique. Combining the two probability laws gives

$$
X_\rho=H_QH_P\,
 \mathbb E\big[U\Psi(U/x)\,1_{E(R)=\rho}\big]. \tag{W8}
$$

We prove a lower bound of order $x/L$ for the expectation, uniformly in $\rho$.

Choose $1<\alpha<\beta<2$ and $c_\Psi>0$ with
$\Psi\ge c_\Psi$ on $[\alpha,\beta]$. Write

$$
m_j=\frac{11}{10}s_j,\qquad
\Delta=\frac15\sigma L.
$$

The midpoint sum over all ordinary scales is exactly
$20\sum_{j\ge0}m_j=L$. Keep one $Q_0$ slot unconditioned.
Set $k=13$ and $\epsilon=1/62400$. For each nonreserved slot in a
band $j<k$, restrict the selected prime by

$$
(11/10-\epsilon)s_j<\log q\le(11/10+\epsilon)s_j.
$$

The numerical conditions for this corridor are

$$
288r=5760\le2^{13},\qquad kr\epsilon=\frac1{240}\le\frac1{120},
\qquad0<\epsilon\le\frac1{10}.
$$

There are finitely many restrictions, and the prime reciprocal-sum
estimate gives each a positive harmonic probability bounded below
independently of $L$. Their joint probability has the same property.

For large $L$ we have $d\ge12$. The largest possible sum of logarithms
in the remaining bands is at most

$$
20\frac65\sigma L\sum_{j\ge13}2^{-j}
 =\frac6{11}2^{-12}L<\frac\Delta{24}.
$$

The infinite midpoint sum over those bands is also less than
$\Delta/24$. Their difference consequently has absolute value less than
$\Delta/24$.

Independently require $E(R)=\rho$ and $\log R\le\Delta/12$.
By (W6) and (W7), this event has probability at least $\delta/2$ for large
$L$. On the intersection, if $B$ is the logarithm of the product of all
variables except the reserved prime, then

$$
|B-(L-m_0)|\le\frac\Delta6.
$$

The interval

$$
[L+\log\alpha-B,\ L+\log\beta-B]
$$

lies inside the logarithmic interval of $Q_0$, at distance comparable to
$L$ from its endpoints. Its length is the fixed positive number
$\log(\beta/\alpha)$. The prime number theorem and partial summation give
harmonic probability at least $c/L$ for the reserved prime to lie there,
uniformly in the conditioned variables. On this event
$U\Psi(U/x)\ge\alpha c_\Psi x$.

The probabilities of the restrictions on the other variables have a
positive product independent of $L$. Applying (W8) proves

$$
X_\rho\ge c\frac{xH_QH_P}L
\qquad(\rho=\pm1). \tag{W9}
$$

Finally, use
$200^{-20}\le (1/12)^{20}/20!$, together with $\log200\le11/2$.
Thus $V_j\ge1/12$ and $d+1\le2T$ give

$$
H_Q\ge\left(\frac{(1/12)^{20}}{20!}\right)^{d+1}
 \ge200^{-20(d+1)}\ge L^{-220}.
$$

Together with $H_P\ge1$ and (W9), this yields
$X_\rho\ge c_0xL^{-221}$, as required.
