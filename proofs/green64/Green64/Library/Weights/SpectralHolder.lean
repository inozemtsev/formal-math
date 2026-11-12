module

public import Green64.Library.Weights.Part004

@[expose] public section

/-!
# Weights / SpectralHolder

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SpectralHolder -/

section

open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Genuine spectral Hölder for a finite positive operator. The weights are
the actual squared coordinates of f; no spectral estimate is assumed. -/
theorem b649_positive_spectral_holder434
    (B : E →ₗ[ℂ] E) (hB : B.IsPositive) (R : ℕ) (hR : 1 ≤ R) (f : E) :
    (inner ℂ f (B f)).re ≤
      (‖f‖^2 : ℝ)^(1-(R:ℝ)⁻¹) *
        ((inner ℂ f ((B^R) f)).re)^((R:ℝ)⁻¹) := by
  let v := hB.isSymmetric.eigenvectorBasis (rfl : Module.finrank ℂ E = _)
  have hRreal : (1:ℝ) ≤ R := by exact_mod_cast hR
  have h := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ hRreal
    (fun i : Fin (Module.finrank ℂ E) => ‖inner ℂ (v i) f‖^2)
    (hB.isSymmetric.eigenvalues rfl)
    (fun i => sq_nonneg _) (hB.nonneg_eigenvalues rfl)
  have hfirst := b649_positive_power_spectral_moment434 B hB 1 f
  simp only [pow_one] at hfirst
  have hlast := b649_positive_power_spectral_moment434 B hB R f
  dsimp only [v] at h
  simp only [Real.rpow_natCast] at h
  rw [(hB.isSymmetric.eigenvectorBasis rfl).sum_sq_norm_inner_right f,
    ← hfirst, ← hlast] at h
  exact h

/-- The original A A* moment controls the actual adjoint norm. No uniform
row bound or RMS bound is inserted as a premise. -/
theorem b649_adjoint_squared_spectral_holder434
    (A : E →ₗ[ℂ] F) (R : ℕ) (hR : 1 ≤ R) (f : F) :
    ‖A.adjoint f‖^2 ≤
      ‖f‖^(2-2/(R:ℝ)) *
        ((inner ℂ f (((A.comp A.adjoint)^R) f)).re)^((R:ℝ)⁻¹) := by
  have h := b649_positive_spectral_holder434
    (A.comp A.adjoint) A.isPositive_self_comp_adjoint R hR f
  have he : (inner ℂ f ((A.comp A.adjoint) f)).re = ‖A.adjoint f‖^2 := by
    change (inner ℂ f (A (A.adjoint f))).re = _
    rw [← A.adjoint_inner_left (A.adjoint f) f]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (A.adjoint f)).symm
  have hf : (‖f‖^2 : ℝ)^(1-(R:ℝ)⁻¹) = ‖f‖^(2-2/(R:ℝ)) := by
    rw [← Real.rpow_natCast ‖f‖ 2, ← Real.rpow_mul (norm_nonneg f)]
    congr 1
    norm_num
    ring
  rwa [he,hf] at h

private theorem b649_rpow_square434 (x a : ℝ) (hx : 0 ≤ x) :
    (x^a)^2 = x^(a*2) := by
  rw [← Real.rpow_natCast (x^a) 2, ← Real.rpow_mul hx]
  norm_num

/-- The S02 spectral endpoint pairing inequality. The second vector g is
arbitrary, so its terminal mark list is unrestricted. R=1 is included. -/
theorem b649_spectral_endpoint_pairing434
    (A : E →ₗ[ℂ] F) (R : ℕ) (hR : 1 ≤ R) (f : F) (g : E) :
    ‖inner ℂ f (A g)‖ ≤ ‖g‖ * ‖f‖^(1-(R:ℝ)⁻¹) *
      ((inner ℂ f (((A.comp A.adjoint)^R) f)).re)^((2*(R:ℝ))⁻¹) := by
  let m : ℝ := (inner ℂ f (((A.comp A.adjoint)^R) f)).re
  have hm : 0 ≤ m :=
    (b649_positive_power434 (A.comp A.adjoint) A.isPositive_self_comp_adjoint R).re_inner_nonneg_right f
  have hRpos : (0:ℝ) < R := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hR)
  have hs := b649_adjoint_squared_spectral_holder434 A R hR f
  have he : (‖f‖^(1-(R:ℝ)⁻¹)*m^((2*(R:ℝ))⁻¹))^2 =
      ‖f‖^(2-2/(R:ℝ))*m^((R:ℝ)⁻¹) := by
    rw [mul_pow, b649_rpow_square434 _ _ (norm_nonneg f), b649_rpow_square434 _ _ hm]
    congr 1
    · congr 1
      ring
    · congr 1
      field_simp
  have hnorm : ‖A.adjoint f‖ ≤ ‖f‖^(1-(R:ℝ)⁻¹)*m^((2*(R:ℝ))⁻¹) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg hm _))).mp
    rw [he]
    exact hs
  rw [← A.adjoint_inner_left g f]
  calc
    _ ≤ ‖A.adjoint f‖*‖g‖ := norm_inner_le_norm _ _
    _ ≤ (‖f‖^(1-(R:ℝ)⁻¹)*m^((2*(R:ℝ))⁻¹))*‖g‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = _ := by dsimp [m]; ring
end Green64Analytic.SpectralEndpoint

end

end

