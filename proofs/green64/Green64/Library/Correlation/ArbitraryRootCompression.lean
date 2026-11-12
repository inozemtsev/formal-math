module

public import Green64.Library.Weights.SpectralHolder

@[expose] public section

/-!
# Correlation / ArbitraryRootCompression

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ArbitraryRootCompression -/

section

open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Finite complex Cauchy-Schwarz, retaining the actual coefficient mass. -/
theorem b649_complex_sum_squared_cauchy434
    {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i*b i‖^2 ≤
      (∑ i ∈ s, ‖a i‖^2)*(∑ i ∈ s, ‖b i‖^2) := by
  calc
    _ ≤ (∑ i ∈ s, ‖a i*b i‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = (∑ i ∈ s, ‖a i‖*‖b i‖)^2 := by simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- PSD compression at the actual natural-power moment. The physical root
vectors u_i may have different norms, overlap, or be zero. Only the actual
coefficient l² mass and diagonal root moments occur on the right. -/
theorem b649_arbitrary_root_power_compression434
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u : ι → E)
    (B : E →ₗ[ℂ] E) (hB : B.IsPositive) (R : ℕ) :
    (inner ℂ (∑ i ∈ s, c i • u i) ((B^R) (∑ i ∈ s, c i • u i))).re ≤
      (∑ i ∈ s, ‖c i‖^2) * (∑ i ∈ s, (inner ℂ (u i) ((B^R) (u i))).re) := by
  let v := hB.isSymmetric.eigenvectorBasis (rfl : Module.finrank ℂ E = _)
  let lam := hB.isSymmetric.eigenvalues (rfl : Module.finrank ℂ E = _)
  let mass : ℝ := ∑ i ∈ s, ‖c i‖^2
  have hc (j : Fin (Module.finrank ℂ E)) :
      inner ℂ (v j) (∑ i ∈ s, c i • u i) =
        ∑ i ∈ s, c i * inner ℂ (v j) (u i) := by
    simp only [inner_sum, inner_smul_right]
  rw [b649_positive_power_spectral_moment434 B hB R]
  calc
    _ ≤ ∑ j : Fin (Module.finrank ℂ E),
        (mass*(∑ i ∈ s, ‖inner ℂ (v j) (u i)‖^2))*lam j^R := by
      apply Finset.sum_le_sum
      intro j _
      change ‖inner ℂ (v j) (∑ i ∈ s, c i • u i)‖^2 * lam j^R ≤ _
      rw [hc]
      exact mul_le_mul_of_nonneg_right
        (b649_complex_sum_squared_cauchy434 s c (fun i => inner ℂ (v j) (u i)))
        (pow_nonneg (hB.nonneg_eigenvalues rfl j) R)
    _ = mass * ∑ j : Fin (Module.finrank ℂ E),
        (∑ i ∈ s, ‖inner ℂ (v j) (u i)‖^2)*lam j^R := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = mass * ∑ i ∈ s, ∑ j : Fin (Module.finrank ℂ E),
        ‖inner ℂ (v j) (u i)‖^2*lam j^R := by
      congr 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (b649_positive_power_spectral_moment434 B hB R (u i)).symm

/-- The full S02 finite operator endpoint consequence, before the separate
physical moment estimate. The first endpoint is a linear combination of
arbitrary physical root vectors; the second endpoint g has no mark-fibre
restriction. No RMS estimate is an assumption of this operator theorem. -/
theorem b649_arbitrary_mark_fibre_endpoint434
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u : ι → F)
    (A : E →ₗ[ℂ] F) (R : ℕ) (hR : 1 ≤ R) (g : E) :
    ‖inner ℂ (∑ i ∈ s, c i • u i) (A g)‖ ≤
      ‖g‖ * ‖∑ i ∈ s, c i • u i‖^(1-(R:ℝ)⁻¹) *
        ((∑ i ∈ s, ‖c i‖^2) *
          (∑ i ∈ s, (inner ℂ (u i) (((A.comp A.adjoint)^R) (u i))).re))^
            ((2*(R:ℝ))⁻¹) := by
  have h := b649_spectral_endpoint_pairing434 A R hR (∑ i ∈ s, c i • u i) g
  have hc := b649_arbitrary_root_power_compression434 s c u
    (A.comp A.adjoint) A.isPositive_self_comp_adjoint R
  have hm := (b649_positive_power434 (A.comp A.adjoint)
    A.isPositive_self_comp_adjoint R).re_inner_nonneg_right (∑ i ∈ s, c i • u i)
  refine h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ hc ?_) ?_)
  · exact hm
  · positivity
  · exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
end Green64Analytic.SpectralEndpoint

end

end

