module

public import Green64.Sieve.PrimeMass
public import Green64.Library.Weights.ParityLiteralParityTarget

@[expose] public section

/-!
# Extract a prime from positive weighted mass

A positive finite prime mass has a positive summand. The cutoff locates
its index in `[exp L, 2 * exp L]`, and the negative-parity weight identifies
the full prime-factor multiplicity count as odd.
-/

section

set_option maxHeartbeats 2600000
set_option autoImplicit false
open Filter ArithmeticFunction
open scoped BigOperators Classical Topology ContDiff ArithmeticFunction.Omega
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT FrozenBins

/-- A positive prime-mass summand gives a shifted prime in the support of
the cutoff. `Ω` counts all prime factors with multiplicity. -/
theorem negative_parity_prime_candidates
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hLe : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∀ᶠ L : ℝ in atTop, ∃ u : ℕ,
      u ∈ Finset.range (⌊2 * Real.exp L⌋₊ + 1) ∧
      0 < parityWeight (sourceOriginalLiteralDepth 20 L) L (-1) u ∧
      0 < Psi ((u : ℝ) / Real.exp L) ∧
      Real.exp L ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * Real.exp L ∧
      0 < u ∧ (u + 2).Prime ∧ Odd (Ω u) := by
  filter_upwards [negative_prime_mass_eventually_pos
    Psi hSmooth hSupport hNonneg hLe hInterior] with L hMass
  unfold primeMass at hMass
  have hSome : ∃ u ∈ Finset.range (⌊2 * Real.exp L⌋₊ + 1),
      0 < (if (u + 2).Prime then
        parityWeight (sourceOriginalLiteralDepth 20 L) L (-1) u *
          Psi ((u : ℝ) / Real.exp L) else 0) := by
    by_contra hh
    push Not at hh
    exact (not_lt_of_ge (Finset.sum_nonpos hh)) hMass
  obtain ⟨u, hu, hTerm⟩ := hSome
  have hp : (u + 2).Prime := by
    by_contra h
    simp only [if_neg h, lt_self_iff_false] at hTerm
  have hWeight : 0 < parityWeight (sourceOriginalLiteralDepth 20 L)
      L (-1) u * Psi ((u : ℝ) / Real.exp L) := by
    simpa only [if_pos hp] using hTerm
  have hA : 0 < parityWeight (sourceOriginalLiteralDepth 20 L)
      L (-1) u := by
    by_contra hh
    have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh)
      (hNonneg ((u : ℝ) / Real.exp L))
    linarith
  have hPsi : 0 < Psi ((u : ℝ) / Real.exp L) :=
    (mul_pos_iff_of_pos_left hA).mp hWeight
  have hLoc := hSupport
    (show (u : ℝ) / Real.exp L ∈ Function.support Psi from ne_of_gt hPsi)
  have hLo : Real.exp L ≤ (u : ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ (Real.exp_pos L)).mp hLoc.1
  have hHi : (u : ℝ) ≤ 2 * Real.exp L :=
    (div_le_iff₀ (Real.exp_pos L)).mp hLoc.2
  have huPos : 0 < u := by exact_mod_cast (Real.exp_pos L).trans_le hLo
  have hOriginal : 0 < sourceOriginalA 20
      (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
      (sourceOriginalPAllActualBands 20 L) u := by
    simpa only [parity_original_minus_parity_A_eq_original_A434] using hA
  have hTarget := b628_parity_negative_candidate_exact_target434
    (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
    (sourceOriginalPAllActualBands 20 L) u
    (source_original_Q_actual_prime 20 (sourceOriginalLiteralDepth 20 L) L) hOriginal hp
  have hOdd : Odd (Ω u) := by
    simpa only [Nat.add_sub_cancel] using hTarget.2.2
  exact ⟨u, hu, hA, hPsi, hLo, hHi, huPos, hp, hOdd⟩

end Green64Analytic.Parity

end
