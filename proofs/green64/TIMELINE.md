# Green64 development timeline

These milestones describe the development of this project. They make no claim
of mathematical priority. Dates and times are expressed in Europe/Madrid;
date ranges group work that continued across a local midnight. Early entries
describe intermediate results and remaining obligations, not a completed
proof of the final theorem.

| Date | Milestone |
| --- | --- |
| 7–8 October 2026 | The fixed-shift plan is recorded. The first conditional Type II argument derives the shift $2k$, the congruence mask modulo $2\lvert k\rvert$, and reduction to a correlation estimate. Positive prime extraction is also reduced to explicit analytic inputs. |
| 8 October | The integer reparametrization is checked in Lean in both directions, including signed quotients, coprimality and congruence conditions. Formalization of the finite state, energy and sieve components begins; the first informal synthesis still needs its analytic dependencies checked. |
| 9 October | The long-prime Dirichlet-polynomial input is proved unconditionally in Lean 4.34.1. Its complete supporting library, theorem statement and axiom audit pass, together with a separate Lean-kernel replay. |
| 10 October | The shift-two weight's pointwise majorant, finite prime assignments and a free-prime-slot lower bound are checked. These supply concrete ingredients for the later positive-mass argument. |
| 13 October | The required Siegel–Walfisz input and finite block sieve are checked. In parallel, the Mellin–Schur local-energy estimate and divisor-moment bounds are formalized. |
| 14 October | An early bound for balanced prime pairs is checked, with a constant uniform in the width of the balanced range. Conditional sieve assembly, full-cell roughness proxies and their character estimates are developed; the final analytic transfer remains open. |
| 15 October | The marked correlation framework gains exact parity projectors, two-endpoint conditioning, signed bilinear forms and harmonic-energy identities. These are local operator results, not yet the final correlation theorem. |
| 21 October | A Lean audit shows that one proposed parameter budget has inconsistent premises for a positive logarithmic saving. The fixed-floor route cannot justify the intended estimate and has to be replaced. |
| 21–23 October | The actual prime-history state is related exactly to the marked operator chain. Background return tails are controlled, allowing the two endpoint cutoffs on previously seen prime factors to be removed with an arbitrarily small logarithmic error. |
| 23 October | The discrepancy between the original signed chain and its restricted chain is bounded by a positive error expression. Estimating that remaining expression is kept as a separate task. |
| 28–31 October | Weighted operator bounds, collision errors and propagation through the full chain are assembled. The plan audit separates these checked ingredients from the remaining transfer to the actual prime weights and Type II estimate. |
| 31 October–2 November | Actual moving prime bands, reciprocal masses and the finite signed correlation identities are integrated with the operator framework. Quantitative cancellation and the final bilinear application remain open. |
| 3 November | Further audits identify a missing transfer from a factorized moment estimate to the actual coupled kernel. They also rule out obtaining the required signed cancellation from endpoint symmetry alone. |
| 4 November | The agent records Guo's GitHub manuscript as a source and uses its exposition to guide the final specialization: $r_0=20$, $\sigma=1/44$, affine arithmetic conditions and approximation precision chosen after the required analytic losses. |
| 6–7 November | Common-dilation restoration, truncation errors and collision/rank estimates are checked and joined into a correlation bound for the special coefficients needed after Cauchy–Schwarz. The general Type II assembly is still separate. |
| 7–8 November | The shift-two arithmetic mask is reconstructed by an exact character expansion with total coefficient mass at most one. Integrality, the vanishing of odd shifts and the bilinear reindexing are checked. |
| 10 November | The smoothed correlation with the actual signed kernel is checked with every fixed logarithmic saving for one reserved prime slot. Summing all outer families and controlling the diagonal and Fourier tails remain explicit obligations. |
| 11–12 November | Common approximation precision, both parity masses, the preliminary sieve, unbalanced-composite bounds, shift-two CRT and weighted rectangles are assembled. The final target reaches the whole-proof verification stage. |
| 12 November, 02:23 | A declaration audit of the exact infinitude target passes: 41,041 residual declarations are replayed by the Lean kernel, with pinned Mathlib and Lean as the trusted baseline. Source-to-object correspondence is still a separate audit at this point. |
| 12 November, 14:33 | The standalone, refactored Mathlib-only project is committed locally. Its full Lean 4.34.1 source build, exact-statement tests, axiom audit and fresh Lean-kernel replay have passed. |
| 12 November, 17:39 | The 63-page TeX article is compiled locally from the Lean-based Markdown exposition after first-reader revisions. Mathematical expressions are preserved by the conversion, and appendices map the text to the formal sources. |
| 12 November, 21:27 | The Lean 4.35.0-rc2 source build and exact-statement/axiom audit pass. Both public theorems use only the three standard axioms; all nine dependency revisions match their pins. Independent-kernel verification remains a separate stage. |
| 12 November, 21:53 | Comparator matches the independent Challenge and Solution statements. NanoDa and a fresh Lean-kernel replay accept the complete proof export in a local diagnostic without the sandbox. |
| 12 November, 22:07 | Con-ron accepts 142,651 declarations in the same proof export. The local statement comparison and all three kernel checks have passed, with unchanged source hashes. The complete protected workflow and registry review are still pending at this milestone. |
| 13 November, 00:04 | The revised 83-page PDF is built after manuscript reviews and repairs. Its build receipt checks the exact input and PDF hashes. Source-provenance edits preserve the reviewed mathematical text and pagination. These are AI manuscript reviews, not independent human peer review. |
| 13 November, 03:12 | The full protected Palomar workflow passes in GitHub CI: fresh source build, protected Challenge comparison, Lean and NanoDa checks, and con-ron acceptance of 142,651 declarations. The report contains no errors or warnings. |
| 13 November, 04:39 | The complete protected verifier also passes locally in about 4 h 31 min, within the 5 h 30 min shared execution budget. The source build starts with fresh candidate build state; only the pinned dependency cache is reused. |

The early milestones follow retained task records, source audits and
verification receipts. The 4 November entry records the agent's consultation
of a manuscript, not its publication or an assertion about when anyone first
found it. Guo did not participate in the project or provide personal assistance.

The later milestones can be checked against the [article build receipt](paper/PDF_BUILD.json),
[PDF review record](paper/PDF_REVIEW.md),
[successful CI run](https://github.com/inozemtsev/formal-math/actions/runs/43325891223),
and [verification record](VERIFICATION.md). See
[mathematical sources and provenance](ACKNOWLEDGEMENTS.md) for the relationship
to the cited manuscripts.

[Back to Green64](README.md)
