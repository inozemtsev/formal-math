# Green64: proof idea

We prove that infinitely many primes $p$ have $\Omega(p-2)$ odd, where
$\Omega$ counts prime factors with multiplicity. The argument constructs a
nonnegative weight supported on the desired parity and proves that prime
values of $u+2$ receive positive weight. This is a conceptual outline; the
linked chapters give the full estimates.

The parity-weight, correlation and sieve strategy is based on two OpenAI
manuscripts: [*Prime Predecessors with an Even Number of Prime Factors*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/main.tex)
and [*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026).
Their [collection README at the fixed revision](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/README.md)
describes different stages of verification and possible errors in
unformalized results. The supporting inputs needed here are proved in the
included Lean development. No independent human verification of these
source manuscripts is claimed here; the machine checks do not establish
all of their claims.

## A weight that selects parity

At scale $x=e^L$, divide the selected primes into disjoint bands. The
ordinary part of a weighted integer has exactly twenty prime factors,
counted with multiplicity, in each ordinary band, hence even total
multiplicity. The remaining, marked
part determines its parity. A nonnegative weight on that part, followed
by the projection onto odd multiplicity and a smooth cutoff to $[x,2x]$,
gives a weight $w$ with

$$
w(u)>0\ \Longrightarrow\ \lambda(u)=-1,
\qquad X:=\sum_u w(u)\gg xL^{-221},
\qquad \lambda(u)=(-1)^{\Omega(u)}.
$$

The [mass estimate](weights.md) uses independent harmonic prime choices.
Both parities retain positive probability, and the ordinary bands leave
enough freedom to place the product in the cutoff interval.

## The estimate that permits sieving

The central input allows prime and roughness indicators to be replaced
by their averages on short logarithmic cells. If $\alpha$ is the
difference between either indicator and its
[complete-cell proxy](correlation.md#1-complete-logarithmic-cells), then
on the factor rectangles of
[(B2)](bilinear.md#1-the-statement-on-one-factor-rectangle),

$$
\left|\sum_{m\in K,\ n\in N}
 w(mn-2)\alpha(m)b_n\right|\ll_D xL^{-D},
\qquad |b_n|\le1.
$$

Here $D>0$ is arbitrary and the companion coefficient $b_n$ is unrestricted
apart from its bound; $\alpha$ is the specified discrepancy. The ranges
allow $n\asymp x^\eta$, where $\eta=b_1/12$ and $0<b_1<1/100$ is fixed.
For fixed $D$ and $\eta$, choose the analytic precision and cell mesh
before the rectangle endpoints and $b_n$, and then take $x$ sufficiently
large. The threshold may depend on the fixed lower-range and roughness
exponents. This uniformity permits successive replacements of both factors
in the sieve sums.

## Why the correlation estimate holds

Selecting an ordinary divisor and applying Cauchy--Schwarz reduces the
bilinear estimate to a diagonal and correlations between $z$ and $z+2k$.
The diagonal has an elementary divisor-moment bound. The correlations are
the difficult term, [(B18)](bilinear.md#4-the-shifted-correlation).

For symmetric tests on independent prime coordinates, orthogonal
decomposition and alternating averages force a small component at one
endpoint. The actual kernel's permutation averages supply this symmetry.
There are enough disjoint prime groups to obtain any fixed logarithmic
saving. The coupled phase stays inside the alternating identity (M1)--(M3).

The [arithmetic transfer](marked-correlation.md#3-the-arithmetic-state-space-and-the-local-contraction)
introduces residues and memory of previously used primes. Character
kernels implement the coordinate averages; translated residues track the
actual shifts $2kD$, where $D$ is the product attached to a transition.
The resulting local norm bounds are (F7). Repeated numerical primes are
handled by a signed [forest expansion](forest-moments.md): it combines
cancellation away from the forced coincidences with the small probability
of prescribing a prime value. An exact lifespan identity and Chinese
remainder counting then transfer the history moments to integer positions.

This bounds the difference between the original correlation and a
resampled comparison term. That comparison requires a separate estimate:
the discrepancy's character-sum cancellation, additional prime estimates,
and [local Fourier energy bounds](local-energy.md) make it small. Combining
the two bounds gives (B18); paying the diagonal and Fourier losses gives
the bilinear estimate (B3).

## Positive prime mass

The weighted sieve removes composites except those with least prime
factor exceeding $x^{1/2-\kappa}$. Write $M$ for the weighted prime mass
and $C_\kappa$ for this remaining composite mass. The
[two sieve estimates](proof.md#2-the-two-sieve-estimates) give

$$
M+C_\kappa\ge c\frac XL,
\qquad
C_\kappa\le(C_{\rm bal}\kappa+\varepsilon)\frac XL.
$$

The positive constants $c,C_{\rm bal}$ are independent of $\kappa$.
Choose fixed $0<\kappa<1/50$ and $\varepsilon>0$ with
$C_{\rm bal}\kappa+\varepsilon<c$, then take $x$ sufficiently large.
Subtraction gives $M>0$. Some $u\in[x,2x]$ therefore has $u+2$ prime and
$\lambda(u)=-1$. Taking arbitrarily large $x$ proves infinitude.
