module

public import Green64.Library.Weights.Part010

@[expose] public section

/-!
# Correlation / SourceCollarGramDecay

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceCollarGramDecay -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1000000

private theorem collar_reciprocal_pair_bound434
    (A B D : ℝ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hDAB : D ≤ 2*(A+B)) :
    A⁻¹ * B⁻¹ ≤ 2*D⁻¹*(A⁻¹+B⁻¹) := by
  have hDen : 0 < D*A*B := by positivity
  calc
    A⁻¹*B⁻¹ = D/(D*A*B) := by field_simp
    _ ≤ 2*(A+B)/(D*A*B) :=
      div_le_div_of_nonneg_right hDAB hDen.le
    _ = 2*D⁻¹*(A⁻¹+B⁻¹) := by field_simp; ring

/-- The convolution's cross-frequency decay, before integration. -/
theorem collar_schur_gram_pointwise434 (s a b : ℝ) :
    collarSchurWeight434 (s+a) * collarSchurWeight434 (s+b) ≤
      2*collarSchurWeight434 (a-b) *
        (collarSchurWeight434 (s+a)+collarSchurWeight434 (s+b)) := by
  have htri : |a-b| ≤ |s+a|+|s+b| := by
    calc
      |a-b| = |(s+a)-(s+b)| := by congr 1; ring
      _ ≤ |s+a|+|s+b| := by
        simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (s+a) 0 (s+b))
  have hD : (1+|a-b|)^2 ≤ 2*((1+|s+a|)^2+(1+|s+b|)^2) := by
    have hbase : 1+|a-b| ≤ (1+|s+a|)+(1+|s+b|) := by linarith
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|a-b|) hbase 2
    nlinarith [sq_nonneg ((1+|s+a|)-(1+|s+b|))]
  simpa only [collarSchurWeight434] using
    collar_reciprocal_pair_bound434
      ((1+|s+a|)^2) ((1+|s+b|)^2) ((1+|a-b|)^2)
      (by positivity) (by positivity) (by positivity) hD

/-- True Gram overlap: uniform finite integral and inverse-square off-diagonal decay. -/
theorem collar_schur_gram_decay434 (a b : ℝ) :
    (∫ s : ℝ, collarSchurWeight434 (s+a) * collarSchurWeight434 (s+b)) ≤
      4*collarSchurWeight434 (a-b) *
        (∫ s : ℝ, collarSchurWeight434 s) := by
  have ha := (collar_schur_weight_shift434 a).1
  have hb := (collar_schur_weight_shift434 b).1
  have hpair := collar_schur_gram_integrable434 a b
  calc
    _ ≤ ∫ s : ℝ, 2*collarSchurWeight434 (a-b) *
      (collarSchurWeight434 (s+a) + collarSchurWeight434 (s+b)) := by
        exact integral_mono hpair ((ha.add hb).const_mul _) (fun s =>
          collar_schur_gram_pointwise434 s a b)
    _ = 2*collarSchurWeight434 (a-b) *
      ((∫ s : ℝ, collarSchurWeight434 (s+a)) +
        (∫ s : ℝ, collarSchurWeight434 (s+b))) := by
          rw [integral_const_mul, integral_add ha hb]
    _ = _ := by
      rw [(collar_schur_weight_shift434 a).2,
        (collar_schur_weight_shift434 b).2]
      ring
end Green64Analytic.CorrelationSquare

end

