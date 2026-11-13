# Reading the Lean proof

The public theorem is `Green64.green_64` in
[Main.lean](../Green64/Main.lean). Its statement is the direct proposition

```lean
{p : ℕ | p.Prime ∧ Odd (Ω (p - 2))}.Infinite
```

The proof first constructs a prime above every natural bound.
`Green64.primes_unbounded` records positivity of $p-2$ as well as its odd
prime-factor count. `scripts/StatementTests.lean` checks both exact
propositions, including the multiplicity convention, and
`scripts/AxiomAudit.lean` prints their dependency axioms.
Mathlib's `Ω` is the length of `Nat.primeFactorsList`, so it counts
prime factors with multiplicity.

The project separates a short final argument from the supporting analytic
library. Module imports form an acyclic graph. Supporting declarations
remain source code in `Green64/Library`; they are not external packages or
precompiled proof objects. The final argument uses the following modules.

| Mathematical step | Module | Main declaration |
| --- | --- | --- |
| Infinitely many primes | [Main](../Green64/Main.lean) | `Green64.green_64` |
| Witness above any bound | [Infinitude](../Green64/Infinitude.lean) | `prime_witnesses_unbounded` |
| Positive mass gives a prime of the required parity | [PrimeExtraction](../Green64/PrimeExtraction.lean) | `negative_parity_prime_candidates` |
| A fixed smooth cutoff | [Localization](../Green64/Localization.lean) | `localizingBump` |
| Subtract balanced composites | [Sieve/PrimeMass](../Green64/Sieve/PrimeMass.lean) | `negative_prime_mass_lower_bound` |
| Cover the composite remainder by prime pairs | [Sieve/CompositeMass](../Green64/Sieve/CompositeMass.lean) | `balanced_composite_mass_bound` |
| Transfer the proxy bound to sharp prime indicators | [Sieve/BalancedMass](../Green64/Sieve/BalancedMass.lean) | `balanced_prime_pair_and_composite_bound` |
| Bound the two prime proxies | [Sieve/BalancedApproximation](../Green64/Sieve/BalancedApproximation.lean) | `balanced_proxy_bound_uniform` |
| Sum positive bounds over balanced rectangles | [Sieve/BalancedBoxes](../Green64/Sieve/BalancedBoxes.lean) | `balanced_rough_pair_bound` |
| Uniform weighted rectangle bound | [Sieve/WeightedBoxes](../Green64/Sieve/WeightedBoxes.lean) | `weighted_box_bound` |
| Linear count of compatible dyadic rectangles | [Sieve/DyadicCounting](../Green64/Sieve/DyadicCounting.lean) | `compatible_dyad_labels_card` |
| Exact finite partition | [Sieve/DyadicPartition](../Green64/Sieve/DyadicPartition.lean) | the active-rectangle partition identities |
| Support and rectangle geometry | [Sieve/DyadicGeometry](../Green64/Sieve/DyadicGeometry.lean) | the bounds for attained dyadic scales |
| Normalize the finite main term | [Sieve/BoxNormalization](../Green64/Sieve/BoxNormalization.lean) | `box_main_Xrho_eventually` |
| Bound the finite remainder | [Sieve/BoxRemainder](../Green64/Sieve/BoxRemainder.lean) | `box_finite_error_exp_bound` |
| Make the remainder negligible | [Sieve/BoxError](../Green64/Sieve/BoxError.lean) | `box_error_uniform_little_o` |
| Euler-product estimates | [Sieve/EulerProduct](../Green64/Sieve/EulerProduct.lean) | `box_euler_bounds` |
| Account for both replacements | [Sieve/ApproximationError](../Green64/Sieve/ApproximationError.lean) | `balanced_sharp_le_proxy_error` |
| Close the analytic parameter choices | [Sieve/Parameters](../Green64/Sieve/Parameters.lean) | `proxy_parameters_exist` |

Unless a row says otherwise, the public analytic declarations are in
namespace `Green64Analytic.Parity`. Lower-level declarations retain their
specific namespaces. Search a declaration with `rg` if using an editor
without Lean's go-to-definition support.

## Correspondence with the mathematical text

The following map records the exact source results used in the Markdown.
The probability notation in the weight chapter rewrites normalized sums;
it does not introduce a probabilistic assumption.

| Text | Lean declarations | Source |
| --- | --- | --- |
| Ordinary bands and moving depth | `sourceOriginalQ0Scale`, `sourceOriginalQActualBands`, `sourceOriginalLiteralDepth` | [Correlation/Part065](../Green64/Library/Correlation/Part065.lean), [Weights/Part097](../Green64/Library/Weights/Part097.lean) |
| Every admissible marked band | `sourceOriginalPGroupIndex`, `source_original_P_all_groups_mem_iff`, `sourceOriginalPAllActualBands` | [group geometry](../Green64/Library/Weights/SourcePOriginalGroupGeometry.lean), [Weights/Part019](../Green64/Library/Weights/Part019.lean), [Correlation/Part032](../Green64/Library/Correlation/Part032.lean) |
| Factorial coefficient and marked weight | `sourceOriginalOrdinaryCoefficient`, `sourceOriginalW1`, `sourceOriginalA0` | [TrueCellPrimeFibre](../Green64/Library/Analysis/Estimates/TrueCellPrimeFibre.lean) |
| Parity projection | `parityWeight` | [Foundations/Part044](../Green64/Library/Sieve/Foundations/Part044.lean) |
| Exact multiplicity sign | `b628_parity_liouville_equals_P_phase434`, `b628_parity_negative_candidate_exact_target434` | [ParityLiteralParityTarget](../Green64/Library/Weights/ParityLiteralParityTarget.lean) |
| Ordinary harmonic lower bounds | `b635_actual_moving_Q_twelfth_floor434`, `b635_parity_admissible_band_count434`, `b635_parity_band_factor_numeric434`, `b635_parity_actual_HQ_lower_220434` | [Weights/Part102](../Green64/Library/Weights/Part102.lean) |
| Ordinary harmonic upper bound | `source_original_Q_actual_band_harmonic_le_four` | [Weights/Part105](../Green64/Library/Weights/Part105.lean) |
| Marked harmonic bounds | `source_original_P_all_actual_reciprocal_le_four434`, `source_original_P_all_reciprocal_floor_eventually` | [Correlation/Part032](../Green64/Library/Correlation/Part032.lean), [Weights/Part107](../Green64/Library/Weights/Part107.lean) |
| Euler normalization and Rankin tail | `source_original_P_group_harmonic_tsum_eq_Hg`, `source_original_P_actual_polylog_rankin_tail` | [Weights/Part103](../Green64/Library/Weights/Part103.lean) |
| Product law and both parity probabilities | `source_original_global_actual_P_normalized_harmonic_law`, `parity_original_P_global_actual_uniform_positive_parity434` | [Weights/Part104](../Green64/Library/Weights/Part104.lean) |
| Exact localized weight identity and corridor | `parity_original_XA_QP_literal_weights_exact_parity434`, `source_original_QP_actual_good_rest_corridor` | [Weights/Part106](../Green64/Library/Weights/Part106.lean) |
| Strong mass lower bound | `parity_original_XA_actual_HQ_HP_floor_eventually_parity434`, `parity_original_XA_literal_depth_lower_eventually_parity434` | [Foundations/Part005](../Green64/Library/Sieve/Foundations/Part005.lean) |
| Shared $X_\rho\ge c_0e^LL^{-221}$ | `localizedMass_lower_bound` | [Foundations/Part050](../Green64/Library/Sieve/Foundations/Part050.lean) |
| Full logarithmic cells and roughness proxy | `sourceD20LogCell`, `sourceD20FullProxy`, `sourceD20FullDelta` | [Weights/Part012](../Green64/Library/Weights/Part012.lean) |
| Prime proxy and character estimate | `b627PrimeFullProxy434`, `b627_actual_fine_rough_all_character_saving434` | [PrimeFineProxy](../Green64/Library/Analysis/Estimates/PrimeFineProxy.lean) |
| Norm of the second proxy | `parity_original_actual_second_proxy_beta_half_norm_le_one434` | [Foundations/Part045](../Green64/Library/Sieve/Foundations/Part045.lean) |
| Actual signed source and common analytic precision | `parity_eventually_original_signed_quarter_b629_fine_one_slot_Psi_Mellin_source_anylog_common_precision434` | [Foundations/Part050](../Green64/Library/Sieve/Foundations/Part050.lean) |
| Whole rectangles and both replacement orders | `parity_eventually_original_both_parity_full_rectangles_proxy_steps434` | [Foundations/Part052](../Green64/Library/Sieve/Foundations/Part052.lean) |
| All finite error terms and normalization | `requiredProxyError`, `allOrdersProxyError`, `parity_original_littleO_exp222_to_Xrho434` | [Foundations/Part053](../Green64/Library/Sieve/Foundations/Part053.lean) |
| Singular product | `singularSeries_converges_and_ge_one` | [Foundations/Part006](../Green64/Library/Sieve/Foundations/Part006.lean) |
| Slot allocation, diagonal estimate, Fourier tails | Detailed source map in [bilinear.md](bilinear.md#source-correspondence) | [Foundations/Part050](../Green64/Library/Sieve/Foundations/Part050.lean) |
| Alternating resampling, physical moments, and comparison subtraction | Derivation in [marked-correlation.md](marked-correlation.md); source map in [marked-correlation.md](marked-correlation.md#correspondence-with-lean) | [Weights/Part092](../Green64/Library/Weights/Part092.lean), [Foundations/Part008](../Green64/Library/Sieve/Foundations/Part008.lean) |
| Negative-parity congruence estimate | `parity_original_negative_congruence_D230_bound434` | [Foundations/Part053](../Green64/Library/Sieve/Foundations/Part053.lean) |
| Character decomposition, deleted-slot convolution, and conductor estimates | Detailed source map in [congruences.md](congruences.md#source-correspondence) | [Weights/Part107](../Green64/Library/Weights/Part107.lean), [Part108](../Green64/Library/Weights/Part108.lean) |
| Assignment masks, CRT, and the finite rectangle sieve | Detailed source map in [rectangles.md](rectangles.md#source-correspondence) | [Foundations/Part056](../Green64/Library/Sieve/Foundations/Part056.lean), [Part057](../Green64/Library/Sieve/Foundations/Part057.lean) |
| Rough-number density | `sourceSimplexTerm`, `sourceDensity` | [Analysis/Estimates/Part003](../Green64/Library/Analysis/Estimates/Part003.lean) |
| Remove unbalanced composites | `parity_original_exists_small_b_unbalanced_margin434`, `negative_prime_or_composite_mass_lower_bound` | [Foundations/Part055](../Green64/Library/Sieve/Foundations/Part055.lean) |

## The analytic library

`Library/Weights` develops labelled prime assignments, multiplicities,
harmonic normalization, and the finite combinatorial operators used by
the correlation argument. `Library/Correlation` contains their signed
correlations and reindexing identities. `Library/Sieve/Foundations`
connects those identities to the sieve and the finite factor sums.
`Library/Analysis`, `Library/OAI`, `Library/ChenTheorem`, and the other
retained source directories provide the analytic and arithmetic estimates
used in those proofs. See [THIRD_PARTY.md](../THIRD_PARTY.md) for their origins.

The [bilinear chapter](bilinear.md) follows the exact Cauchy square,
the diagonal divisor bound, and the integration over the Fourier ball and
its tail. The [marked-correlation chapter](marked-correlation.md) supplies
the cancellation used inside that ball, including the separately bounded
comparison term. The final analytic parameter construction discharges
the hypotheses of these lower-level estimates.

The `PartNNN` files contain supporting results; the named files in
`Green64/Sieve` expose the final argument.

## Checking what is proved

A successful build alone is not the axiom audit. Run `scripts/verify.py`
and inspect its `VALIDATION.json` receipt for the public theorem names,
axioms, source hashes, dependency revisions, and command exit codes.
The audit checks the infinite set proposition itself, together with the
stronger unbounded-witness theorem. It does not substitute a conditional
statement or a wrapper with an assumed analytic conclusion.
