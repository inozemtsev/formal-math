module

public import Green64.Sieve.BalancedBoxes

@[expose] public section

/-!
# Bound the product of two prime proxies

Combine the weighted rectangle bound with the analytic choice of proxy
parameters. The resulting constant is uniform in the balance parameter
and in the two parity signs.
-/

section

set_option maxHeartbeats 1600000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

/-- balanced nonsmooth prime-proxy subtraction cost. The
constant is chosen before S,kappa,gamma and both parity signs.
The full-cell proxies and balanced source are unchanged. -/
theorem balanced_proxy_bound_uniform
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hOne : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ Cbal : ℝ, 0 < Cbal ∧
      ∀ S : ℝ, 0 < S → ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      ∀ kappa : ℝ, 0 ≤ kappa → kappa < 1 / 50 →
      ∀ (gamma : ℝ) (Y : ℕ),
      (balancedFactorSum true true
        (sourceOriginalLiteralDepth 20 L) L rho Psi S gamma kappa Y).re ≤
      Cbal * (kappa + 1 / L) * (localizedMass Psi rho L / L) := by
  obtain ⟨C1, hC1, hrough⟩ := balanced_rough_pair_bound
    Psi hCont hSupport hNonneg hOne hInterior
  refine ⟨9 * C1, by positivity, ?_⟩
  intro S hS
  filter_upwards [hrough, parity_original_balanced_proxy_le_double_rough_mass434
    Psi hNonneg S hS, eventually_gt_atTop (0 : ℝ)] with L hr hp hL
  intro rho hRho kappa hk0 hk gamma Y
  have hAbs : |rho| ≤ 1 := by
    rcases hRho with rfl | rfl <;> norm_num
  have hV := parity_original_subpower_natural_euler_pos434 L
  have hfac : 0 ≤ 9 / (L ^ 2 * (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2) := by
    positivity
  calc
    _ ≤ (9 / (L ^ 2 * (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2)) *
        balancedRoughPairMass (sourceOriginalLiteralDepth 20 L)
          L rho Psi kappa Y :=
      hp (sourceOriginalLiteralDepth 20 L) Y rho gamma kappa hAbs hk
    _ ≤ (9 / (L ^ 2 * (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2)) *
        (C1 * (kappa * L + 1) * localizedMass Psi rho L *
          (sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) ^ 2) :=
      mul_le_mul_of_nonneg_left (hr rho hRho kappa hk0 hk.le Y) hfac
    _ = _ := by field_simp [ne_of_gt hL, ne_of_gt hV] <;> ring

/-- Fixed positive kappa version of the original8.4 loss. The constant
precedes kappa; the final threshold may depend on that chosen kappa and S.
Both Liouville branches use the same constant and threshold. -/
theorem balanced_proxy_bound
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hOne : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ Cbal : ℝ, 0 < Cbal ∧
      ∀ kappa : ℝ, 0 < kappa → kappa < 1 / 50 →
      ∀ S : ℝ, 0 < S → ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      ∀ (gamma : ℝ) (Y : ℕ),
      (balancedFactorSum true true
        (sourceOriginalLiteralDepth 20 L) L rho Psi S gamma kappa Y).re ≤
      Cbal * kappa * (localizedMass Psi rho L / L) := by
  obtain ⟨Cbal, hCbal, hbound⟩ := balanced_proxy_bound_uniform
    Psi hCont hSupport hNonneg hOne hInterior
  refine ⟨2 * Cbal, by positivity, ?_⟩
  intro kappa hk0 hk S hS
  filter_upwards [hbound S hS, localizedMass_eventually_nonneg
    Psi hCont hSupport hNonneg hInterior, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (1 / kappa)] with L hb hx hL hThreshold
  intro rho hRho gamma Y
  have hOne : 1 / L ≤ kappa := by
    apply (div_le_iff₀ hL).2
    have hh := (div_le_iff₀ hk0).mp hThreshold
    nlinarith
  have hsum : kappa + 1 / L ≤ 2 * kappa := by linarith
  calc
    _ ≤ Cbal * (kappa + 1 / L) * (localizedMass Psi rho L / L) :=
      hb rho hRho kappa hk0.le hk gamma Y
    _ ≤ Cbal * (2 * kappa) * (localizedMass Psi rho L / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum hCbal.le)
        (div_nonneg (hx rho hRho) hL.le)
    _ = _ := by ring

end Green64Analytic.Parity

end
