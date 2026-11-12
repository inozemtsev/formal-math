module

public import Green64.Sieve.BalancedMass

@[expose] public section

/-!
# A bound for the mass of balanced composites

Cover each balanced composite by its admissible prime-factor pairs.
Positivity transfers the uniform pair-mass estimate to the composite
remainder in the sieve.
-/

section

set_option maxHeartbeats 2400000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology ContDiff
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT FrozenBins

/-- Parameter-free balanced residual budget, with both parity
branches. The source parameters are constructed after kappa;
only an admissible one-bin source partition is used to project the
already proved balanced terms of the complete ledger. -/
theorem balanced_composite_mass_bound
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hLe : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ Cbal : ℝ, 0 < Cbal ∧
      ∀ kappa : ℝ, 0 < kappa → kappa < 1 / 50 →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      balancedCompositeMass (sourceOriginalLiteralDepth 20 L)
        L rho Psi kappa ⌊2 * Real.exp L⌋₊ ≤
        (Cbal * kappa + eps) * (localizedMass Psi rho L / L) := by
  obtain ⟨Cbal, hCbal, hFull⟩ := balanced_prime_pair_and_composite_bound
    Psi hSmooth hSupport hNonneg hLe hInterior
  refine ⟨Cbal, hCbal, ?_⟩
  intro kappa hk hkSmall
  obtain ⟨H, J, B, S, hBS, hBounds⟩ :=
    hFull (1 / 200) kappa (by norm_num) (by norm_num) hk hkSmall 1
  have hMono : Monotone (affineGrid (1 / 200) (1 / 2 - kappa) 1) := by
    intro i j hij
    have hijr : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hWidth : 0 ≤ (1 / 2 - kappa) - (1 / 200 : ℝ) := by linarith
    have h := mul_le_mul_of_nonneg_left hijr hWidth
    simpa only [affineGrid, Nat.cast_one, div_one, add_comm] using add_le_add_left h (1 / 200 : ℝ)
  intro eps hEps
  have hb := hBounds (affineGrid (1 / 200) (1 / 2 - kappa) 1) hMono
    (affineGrid_zero _ _ _) (affineGrid_last _ _ _ (by norm_num)) eps hEps
  filter_upwards [hb] with L hL
  intro rho hRho
  exact (hL rho hRho).2

end Green64Analytic.Parity

end
