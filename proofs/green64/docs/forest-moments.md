# The forest expansion of the history sum

We give the finite identity and the two estimates used in (M15).
The distinction between a new prime label and a later use of the same
label is essential: the forest expansion applies to the list of births,
not to the list of all visits.

## 1. A linear functional on birth lists

Fix the moment length $N=2R$, the OLD cutoff $T$, and all SMALL labels.
Expand the product of the $N$ signed transitions, including their
comparison patterns and independent endpoint permutations. At the
initial state there are $G(J+\ell)$ potential BIG birth slots. At each
of the $N+1$ background steps there are $GT$ slots, and each of the
$N$ active transitions has $G(J+\ell)$ slots. Here $G$ is the number
of BIG groups. Thus the list has fixed length

$$
A=(N+1)G(J+\ell+T).
$$

An unused slot has value $\varnothing$. Retaining a label already
present in the state creates no new birth. All local distinctness
conditions, transition legality conditions, OLD gates and the initial
distinctness condition remain in the coefficients of this expansion.
Only the additional condition that different births have different
numerical prime labels is set aside temporarily.

Let $\mathcal H$ be this finite collection of expanded histories, let
$b(H)=(b_0(H),\ldots,b_{A-1}(H))$ be its birth list, and let $c_H$
be the product of its transition and boundary coefficients, with the
common baseline and tilted prime masses described below.
In particular $c_H$ includes the sign of every comparison
pattern, all normalized prime and permutation masses, the initial and
terminal boundary factors, and the damping factors. Define the linear
functional

$$
\Lambda(f)=\sum_{H\in\mathcal H}c_H f(b(H)). \tag{F3}
$$

The projected history sum is
$\Lambda(1_{\text{nonempty births distinct}})$.
This construction does not replace the coefficients by their absolute
values. On histories with distinct births its density agrees with the
prime residue averages in (M16). Factoring out the contribution of primes not selected
as births gives the common baseline
$B_{\mathrm{base}}=\prod_p b_p$ and the tilted laws
$\widetilde\mu_g(p)=1/(V_gp b_p)$ from
[the state-space construction](marked-correlation.md#3-the-arithmetic-state-space-and-the-local-contraction).

For a birth list $b$, replace an unused entry at address $j$ by a
symbol $\star_j$ used at no other address. Denote the resulting list
by $x_0,\ldots,x_{A-1}$. A forest is a choice, for each $j$, of either
no parent or one parent $p(j)<j$. Its rank $r(p)$ is the number of
chosen parents. Define

$$
T_p(b)=(-1)^{r(p)}\prod_{j:\,p(j)\text{ chosen}}
                  1_{x_j=x_{p(j)}},\qquad F_p=\Lambda(T_p).
\tag{F4}
$$

The exact identity is

$$
1_{x_0,\ldots,x_{A-1}\text{ distinct}}
 =\prod_{j=0}^{A-1}\left(1-\sum_{i<j}1_{x_j=x_i}\right)
 =\sum_p T_p(b). \tag{F5}
$$

For a distinct list every factor in the product is one. Otherwise,
at the first repeated entry the previous entries are distinct, so
exactly one summand is one and the product vanishes. Expanding the
product gives the second equality. The parent is always earlier, so
cycles are impossible. There are at most $A^{2r}$ forests of rank
$r$: choose at most $A^r$ lists of children and at most $A^r$ lists
of parents. Applying $\Lambda$ to (F5) proves that the original signed
history sum is exactly $\sum_p F_p$.

## 2. The bound preserving signed cancellation

The equality constraints in (F4) cannot be inserted into the local
contraction by conditioning. Instead use independent random sign fields.
For each selected edge $e=(j,p(j))$, let $\epsilon_e(a)$ be independent
uniform signs, indexed by the finite alphabet of primes and private
symbols. Then

$$
1_{x_j=x_{p(j)}}=
\mathbb E\bigl[\epsilon_e(x_j)\epsilon_e(x_{p(j)})\bigr].
\tag{F6}
$$

Independence between the edge fields gives the product of the equality
indicators. For a fixed field assignment, group its signs by address.
To make the multiplier at an unused slot equal to one, divide the
multiplier at address $j$ by its value at $\star_j$, and keep the
product of those values as an overall scalar. That scalar and every
slot multiplier have modulus one. Consequently $F_p$ is exactly
$(-1)^{r(p)}$ times an average of the same history functional with
unit slot multipliers and a unit scalar outside it.

Assign the active birth slots in transition $i$ to that transition;
assign background and initial slots to adjacent visits. Only the
owners of selected children and their parents can acquire a nontrivial
slot multiplier. There are at most $2r(p)$ such owners. The background
operator bound is uniform in all unit multipliers. At an unmarked
active transition the original signed contraction still applies; at
a marked transition use the bound for an arbitrary unit multiplier.

Use exactly the orbit norm $\mathcal E$ defined in (T1)--(T4) of
[marked-correlation.md](marked-correlation.md#3-the-arithmetic-state-space-and-the-local-contraction).
Its OLD residues have counting measure and its ordered memory sectors
have the single factorial in (T3). The local estimates, proved in
(T6)--(T23), are

$$
\mathcal E(E_i f)\le l^2\mathcal E(f),\qquad
\mathcal E(E_i^{\phi}f)\le h^2\mathcal E(f)
\quad(|\phi|\le1),\qquad
\mathcal E(G_i^{\phi}f)\le\Gamma^2\mathcal E(f).
\tag{F7}
$$

Here $E_i$ is the active signed transition, $G_i$ is the background
transition, and $\phi$ multiplies the actual transition coefficient.
In the notation (T21)--(T23), $l=L^{-S_0}$, $h=L^\kappa$,
$b=L^{S_0+\kappa}$ and $K_r=S_0+\kappa$. With the constants $W_0,w_0,\rho_0$ specified after
(M15), the background bound is
$\Gamma=\exp(4W_0w_0G/\rho_0)$.

Iterating (F7) and applying Cauchy--Schwarz to the initial and terminal
vectors bounds each fixed-field scalar by

$$
|B_{\mathrm{base}}|\,\mathcal E(v)\,
 \Gamma^{N+1}\prod_{i=0}^{N-1}
 \begin{cases}h,&i\text{ has a marked owner},\\l,&\text{otherwise}.
 \end{cases}
$$

The initial vector includes the retained initial distinctness mask and
the conjugated initial slot phase; its energy is at most that of the
original boundary vector $v$. Thus, putting
$P_0=|B_{\mathrm{base}}|\mathcal E(v)\Gamma^{N+1}$ and averaging the
unit scalars, we obtain

$$
|F_p|\le P_0 l^N b^{2r(p)}. \tag{F8}
$$

The initial boundary energy occurs once. In particular, (F8) does not
pay an additional factor for the number of histories or sign fields.

## 3. The bound from prescribed prime values

For the second bound keep the equality constraints and use absolute
coefficients. The tilted law satisfies

$$
\sum_p\widetilde\mu_g(p)\le2,\qquad
\sum_{p:\,p=t}\widetilde\mu_g(p)
 \le\delta\sum_p\widetilde\mu_g(p),\qquad
\delta=\frac2{v e^{L^{3/10}}}. \tag{F9}
$$

Expose births in address order. A selected child must equal a label
whose value has already been exposed. In an active transition with
$s$ selected new coordinates the pinned absolute row bound is

$$
\sum_{\text{legal transitions with the prescribed values}}
 |c(x,y)|\,w_0^{|\mathrm{OLD}(y)|}
 \le \delta^s a\,w_0^{|\mathrm{OLD}(x)|}. \tag{F10}
$$

To obtain this bound, expand the comparison pattern, the auxiliary
prime choices and the endpoint permutations before summing the new
coordinates. Their masses are normalized. Each prescribed new value
contributes the atom bound in (F9); cap the character kernel pointwise
as in (M4). The remaining SMALL row sums and promotion damping give
the same absolute row constant $a$ independently of the prescribed
values. For fixed $m$ it satisfies $a\le L^{C_b}$. This argument
retains multiplicities of transitions with the same output.

The corresponding background bound is $\delta^s\Gamma$ with the
same weight $w_0^{|\mathrm{OLD}|}$. Its geometric sum converges because
$1/(\rho_0w_0)+\sqrt q/\rho_0^2\le1$. Apply these two bounds
backwards to successive suffixes of the history. Each selected child
is charged exactly once; a child forced to equal an incompatible
group or a private unused symbol gives zero. A selected child in the
initial block also gives zero, because initial distinctness was
retained. Every surviving forest therefore receives all $r(p)$ atom
factors, including forests with several children of one parent.

The terminal boundary is bounded by $w_0^{|\mathrm{OLD}|}$.
The suffix induction, followed by the initial boundary sum, yields

$$
|F_p|\le P_0 a^N\delta^{r(p)}. \tag{F11}
$$

No independence of the conditioned history is asserted in this
argument: (F10) is uniform in the already exposed state and prescribed
values. Combining (F8) and (F11) proves (M15), for the identical
coefficients $F_p$ defined in (F3)--(F4). The rank split and removal
of the OLD cutoff then proceed as in
[the history restoration](marked-correlation.md#4-restoring-all-histories).

## Source correspondence

The list identity is `source_original_root_LIST_FOREST_EXPANSION434`
in [Weights/Part093](../Green64/Library/Weights/Part093.lean).
The actual linear functional, exact forest sum, sign-field average,
owner count and energy iteration are in
[Correlation/Part064](../Green64/Library/Correlation/Part064.lean),
especially `sourceOriginalRootFunctionalRoot434`,
`source_original_root_ORIGINAL_FOREST_SUM434` and
`source_original_root_FOREST_FINITE_BOUND434`.
The pinned row estimate is `source_original_forest_E_PINNED_FULL_ROW434`
in [Weights/Part090](../Green64/Library/Weights/Part090.lean).
The full-rank suffix induction and the initial distinctness case are
in [Correlation/Part064](../Green64/Library/Correlation/Part064.lean);
the resulting bound (F11) is
`eventually_source_original_global_root_SOURCE_HIGH434` in
[Correlation/Part065](../Green64/Library/Correlation/Part065.lean).
