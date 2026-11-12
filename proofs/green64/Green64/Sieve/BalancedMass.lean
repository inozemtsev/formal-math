module

public import Green64.Sieve.Parameters

@[expose] public section

/-!
# Pass from proxy factors to prime factors

Transfer the uniform prime-proxy estimate to sharp prime indicators.
The errors for both replacement orders are absorbed into an arbitrary
positive multiple of the normalized localized mass.
-/

section

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology ContDiff
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT FrozenBins

/-- Full balanced8.4: sharp prime-pair source AND actual
residual composite mass. Both real proxy replacements are paid from
the same proved ledger, with Xrho and both parity signs.
One H,J,B,S is chosen before the admissible bin endpoints. -/
theorem balanced_prime_pair_and_composite_bound
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t) (hLe : ∀ t, Psi t ≤ 1)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ Cbal : ℝ, 0 < Cbal ∧
      ∀ (b1 kappa : ℝ), 0 < b1 → b1 < 1 / 100 → 0 < kappa → kappa < 1 / 50 →
      ∀ N : ℕ, ∃ H J B : ℕ, ∃ S : ℝ, 2 * ((B : ℝ) + 1) + 3 < S ∧
      ∀ t : ℕ → ℝ, Monotone t → t 0 = b1 → t N = 1 / 2 - kappa →
      ∀ eps : ℝ, 0 < eps → ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      (balancedFactorSum false false (sourceOriginalLiteralDepth 20 L)
        L rho Psi S b1 kappa ⌊2 * Real.exp L⌋₊).re ≤
        (Cbal * kappa + eps) * (localizedMass Psi rho L / L) ∧
      balancedCompositeMass (sourceOriginalLiteralDepth 20 L)
        L rho Psi kappa ⌊2 * Real.exp L⌋₊ ≤
        (Cbal * kappa + eps) * (localizedMass Psi rho L / L) := by
  obtain ⟨Cbal, hCbal, hProxy⟩ := balanced_proxy_bound
    Psi hSmooth.continuous hSupport hNonneg hLe hInterior
  refine ⟨Cbal, hCbal, ?_⟩
  intro b1 kappa hb1 hb1Small hk hkSmall N
  obtain ⟨H, J, B, S, hBS, hErrors⟩ := proxy_parameters_exist
    Psi hSmooth hSupport hNonneg hLe hInterior N b1 kappa hb1 hb1Small hk hkSmall
  have hS : 0 < S := by have hB := Nat.cast_nonneg (α := ℝ) B; linarith
  refine ⟨H, J, B, S, hBS, ?_⟩
  intro t ht hFirst hLast eps hEps
  have hPlus := (hErrors t ht hFirst hLast 1 (Or.inl rfl)).1.bound hEps
  have hMinus := (hErrors t ht hFirst hLast (-1) (Or.inr rfl)).1.bound hEps
  filter_upwards [hProxy kappa hk hkSmall S hS, hPlus, hMinus,
    localizedMass_eventually_nonneg
      Psi hSmooth.continuous hSupport hNonneg hInterior,
    parity_eventually_original_balanced_composite_mass_le_source434
      kappa hk hkSmall Psi hSupport hNonneg, eventually_gt_atTop (0 : ℝ)]
    with L hp hePlus heMinus hx hCover hL
  intro rho hRho
  have hAbs : |rho| ≤ 1 := by rcases hRho with rfl | rfl <;> norm_num
  have hScale : 0 ≤ localizedMass Psi rho L / L :=
    div_nonneg (hx rho hRho) hL.le
  have hErrorNonneg := parity_original_sieve_required_proxy_error_nonneg434
    (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2 * Real.exp L⌋₊
  have hNorm :
      ‖requiredProxyError (sourceOriginalLiteralDepth 20 L)
        L Psi S b1 kappa N t ⌊2 * Real.exp L⌋₊‖ ≤
      eps * ‖localizedMass Psi rho L / L‖ := by
    rcases hRho with rfl | rfl
    · exact hePlus
    · exact heMinus
  have he :
      requiredProxyError (sourceOriginalLiteralDepth 20 L)
        L Psi S b1 kappa N t ⌊2 * Real.exp L⌋₊ ≤
      eps * (localizedMass Psi rho L / L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hErrorNonneg, abs_of_nonneg hScale]
      using hNorm
  have hSharp :
      (balancedFactorSum false false (sourceOriginalLiteralDepth 20 L)
        L rho Psi S b1 kappa ⌊2 * Real.exp L⌋₊).re ≤
        (Cbal * kappa + eps) * (localizedMass Psi rho L / L) := by
    calc
      _ ≤ (balancedFactorSum true true (sourceOriginalLiteralDepth 20 L)
          L rho Psi S b1 kappa ⌊2 * Real.exp L⌋₊).re +
          requiredProxyError (sourceOriginalLiteralDepth 20 L)
            L Psi S b1 kappa N t ⌊2 * Real.exp L⌋₊ :=
        balanced_sharp_le_proxy_error
          (sourceOriginalLiteralDepth 20 L) L rho hRho Psi S b1 kappa N t _
      _ ≤ Cbal * kappa * (localizedMass Psi rho L / L) +
          eps * (localizedMass Psi rho L / L) :=
        add_le_add (hp rho hRho b1 ⌊2 * Real.exp L⌋₊) he
      _ = _ := by ring
  exact ⟨hSharp,
    (hCover (sourceOriginalLiteralDepth 20 L) ⌊2 * Real.exp L⌋₊ rho S b1 hAbs).trans hSharp⟩

end Green64Analytic.Parity

end
