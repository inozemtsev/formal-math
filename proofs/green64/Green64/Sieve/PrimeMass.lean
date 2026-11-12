module

public import Green64.Sieve.CompositeMass
public import Green64.Library.Sieve.Foundations.Part055

@[expose] public section

/-!
# Subtract the balanced composites

Subtract the balanced-composite upper bound from the prime-or-composite
lower bound. Choose the balance parameter after the uniform upper-bound
constant, leaving a positive fraction of the localized mass.
-/

section

set_option maxHeartbeats 3000000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology ContDiff
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT FrozenBins

/-- The negative-parity prime mass retains a quarter of the singular-series
main term after the balanced composites are subtracted. -/
theorem negative_prime_mass_lower_bound
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hLe : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∀ᶠ L : ℝ in atTop,
      (singularSeries / 4) *
        (localizedMass Psi (-1) L / L) ≤
      primeMass Psi (-1) L := by
  obtain ⟨Cbal, hCbal, hBalanced⟩ := balanced_composite_mass_bound
    Psi hSmooth hSupport hNonneg hLe hInterior
  have hSing : 0 < singularSeries :=
    lt_of_lt_of_le zero_lt_one singularSeries_converges_and_ge_one.2
  let kappa : ℝ := min (1 / 100) (singularSeries / (8 * Cbal))
  have hk : 0 < kappa := by
    dsimp [kappa]
    exact lt_min (by norm_num) (by positivity)
  have hkSmall : kappa < 1 / 50 :=
    (min_le_left _ _).trans_lt (by norm_num)
  have hKappaBudget : Cbal * kappa ≤ singularSeries / 8 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * Cbal)).mp
      (show kappa ≤ singularSeries / (8 * Cbal) from min_le_right _ _)
    nlinarith
  filter_upwards [negative_prime_or_composite_mass_lower_bound
      Psi hSmooth hSupport hNonneg hLe hInterior kappa hk hkSmall,
    hBalanced kappa hk hkSmall (singularSeries / 8) (by positivity),
    negative_localizedMass_eventually_pos
      Psi hSmooth.continuous hSupport hNonneg hInterior,
    eventually_gt_atTop (0 : ℝ)] with L hInitial hBalancedL hX hL
  have hScale : 0 ≤ localizedMass Psi (-1) L / L := (div_pos hX hL).le
  have hCoeff : Cbal * kappa + singularSeries / 8 ≤
      singularSeries / 4 := by linarith
  have hSubtract := (hBalancedL (-1) (Or.inr rfl)).trans
    (mul_le_mul_of_nonneg_right hCoeff hScale)
  linarith

theorem negative_prime_mass_eventually_pos
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hLe : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∀ᶠ L : ℝ in atTop, 0 < primeMass Psi (-1) L := by
  have hSing : 0 < singularSeries :=
    lt_of_lt_of_le zero_lt_one singularSeries_converges_and_ge_one.2
  filter_upwards [negative_prime_mass_lower_bound
      Psi hSmooth hSupport hNonneg hLe hInterior,
    negative_localizedMass_eventually_pos
      Psi hSmooth.continuous hSupport hNonneg hInterior,
    eventually_gt_atTop (0 : ℝ)] with L hb hX hL
  exact (mul_pos (div_pos hSing (by norm_num)) (div_pos hX hL)).trans_le hb

end Green64Analytic.Parity

end
