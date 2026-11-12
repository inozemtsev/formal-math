module

public import Green64.Library.Weights.Part012
public import Mathlib

@[expose] public section

/-!
# Weights / SourceD61CenteredBilinear

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceD61CenteredBilinear -/

section

open scoped BigOperators Classical
namespace Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 5000000

private theorem centered_sum_sub_constant434
    {ι : Type} (S : Finset ι) (w f : ι → ℂ) (c : ℂ)
    (hw : ∑ i ∈ S, w i = 0) :
    (∑ i ∈ S, w i * f i) =
      ∑ i ∈ S, w i * (f i-c) := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hw, zero_mul, sub_zero]

/-- The exact mixed second-difference identity. Works for arbitrary complex
physical kernel H and preserves both signed source weights BEFORE absolute
values, without any cellwise regularity assumption. -/
theorem centered_complex_bilinear_mixed_difference434
    {ι κ : Type} (S : Finset ι) (T : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ)
    (ha : ∑ i ∈ S, a i = 0)
    (hb : ∑ j ∈ T, b j = 0)
    (i₀ : ι) (j₀ : κ) (H : ι → κ → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, a i*b j*H i j) =
      ∑ i ∈ S, ∑ j ∈ T,
        a i*b j*(H i j-H i j₀-H i₀ j+H i₀ j₀) := by
  classical
  calc
    _ = ∑ i ∈ S, a i*(∑ j ∈ T, b j*H i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i ∈ S,
        a i*((∑ j ∈ T, b j*H i j) -
             (∑ j ∈ T, b j*H i₀ j)) := by
      exact (centered_sum_sub_constant434 S a
        (fun i => ∑ j ∈ T, b j*H i j)
        (∑ j ∈ T, b j*H i₀ j) ha)
    _ = ∑ i ∈ S, a i*(∑ j ∈ T, b j*(H i j-H i₀ j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = ∑ i ∈ S,
        a i*(∑ j ∈ T, b j*((H i j-H i₀ j) -
            (H i j₀-H i₀ j₀))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (a i * ·)
        ((centered_sum_sub_constant434 T b
          (fun j => H i j - H i₀ j)
          (H i j₀ - H i₀ j₀) hb))
    _ = ∑ i ∈ S, ∑ j ∈ T,
        a i*b j*(H i j-H i j₀-H i₀ j+H i₀ j₀) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
end Green64ComparisonPartial

end

