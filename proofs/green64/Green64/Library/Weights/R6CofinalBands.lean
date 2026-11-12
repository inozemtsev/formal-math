module

public import Green64.Library.Weights.R6RealBandCriterion
public import Green64.Library.Weights.Part019
public import Mathlib

@[expose] public section

/-!
# Weights / R6CofinalBands

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeR6CofinalBands -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Rational geometric tenth-root of the actual r=6 L-scale. -/
noncomputable def sourceNativeR6CofinalRoot434 (N : ℕ) : ℝ :=
  (3/2:ℝ)*(2:ℝ)^N

/-- Cofinal original logarithmic asymptotic L with a controlled
arithmetic phase of exact source dyadic P-band boundaries. -/
noncomputable def sourceNativeR6CofinalL434 (N : ℕ) : ℝ :=
  (sourceNativeR6CofinalRoot434 N)^10

private theorem source_native_r6_cofinal_root_pos434 (N : ℕ) :
    0 < sourceNativeR6CofinalRoot434 N := by
  unfold sourceNativeR6CofinalRoot434
  positivity

private theorem source_native_r6_cofinal_root_power434
    (N a : ℕ) :
    (sourceNativeR6CofinalRoot434 N)^a =
       (3/2:ℝ)^a*(2:ℝ)^(N*a) := by
  unfold sourceNativeR6CofinalRoot434
  rw [mul_pow, ← pow_mul]

/-- Exact original SMALL index characterization on the true r=6
cofinal geometric prime-band scale, without changing any interval. -/
theorem source_native_r6_cofinal_small_band_iff434
    (N j : ℕ) :
    (sourceNativeR6CofinalL434 N)^(1/10:ℝ) ≤
       (3/2:ℝ)*sourceOriginalPGroupScale 6
          (sourceNativeR6CofinalL434 N) j ∧
    (9/5:ℝ)*sourceOriginalPGroupScale 6
       (sourceNativeR6CofinalL434 N) j ≤
       (sourceNativeR6CofinalL434 N)^(1/5:ℝ) ↔
    8*N+2 ≤ j ∧ j ≤ 9*N+2 := by
  let u := sourceNativeR6CofinalRoot434 N
  have hu := source_native_r6_cofinal_root_pos434 N
  have hBand := (source_native_r6_small_big_band_real_iff434 u hu j).1
  change (u^10)^(1/10:ℝ) ≤
       (3/2:ℝ)*sourceOriginalPGroupScale 6 (u^10) j ∧
     (9/5:ℝ)*sourceOriginalPGroupScale 6 (u^10) j ≤
       (u^10)^(1/5:ℝ) ↔ 8*N+2 ≤ j ∧ j ≤ 9*N+2
  rw [hBand]
  have hLower : (3/22:ℝ)*u^8 ≤ (2:ℝ)^j ↔ 8*N+2 ≤ j := by
    rw [source_native_r6_cofinal_root_power434 N 8]
    rw [←mul_assoc, mul_comm N 8]
    convert source_native_r6_dyadic_ge_iff434
      ((3/22:ℝ)*(3/2:ℝ)^8) (8*N) 1 j
      (by norm_num) (by norm_num) using 1 <;> omega
  have hUpper : (2:ℝ)^j ≤ (5/44:ℝ)*u^9 ↔ j ≤ 9*N+2 := by
    rw [source_native_r6_cofinal_root_power434 N 9]
    rw [←mul_assoc, mul_comm N 9]
    convert source_native_r6_dyadic_le_iff434
      ((5/44:ℝ)*(3/2:ℝ)^9) (9*N) 2 j
      (by norm_num) (by norm_num) using 1 <;> omega
  exact and_congr hLower hUpper

/-- Exact original BIG index characterization on the same geometric
r=6 cofinal source prime-slice scale. -/
theorem source_native_r6_cofinal_big_band_iff434
    (N j : ℕ) :
    (sourceNativeR6CofinalL434 N)^(3/10:ℝ) ≤
       (3/2:ℝ)*sourceOriginalPGroupScale 6
          (sourceNativeR6CofinalL434 N) j ∧
    (9/5:ℝ)*sourceOriginalPGroupScale 6
       (sourceNativeR6CofinalL434 N) j ≤
       (sourceNativeR6CofinalL434 N)^(2/5:ℝ) ↔
    6*N+1 ≤ j ∧ j ≤ 7*N := by
  let u := sourceNativeR6CofinalRoot434 N
  have hu := source_native_r6_cofinal_root_pos434 N
  have hBand := (source_native_r6_small_big_band_real_iff434 u hu j).2
  change (u^10)^(3/10:ℝ) ≤
       (3/2:ℝ)*sourceOriginalPGroupScale 6 (u^10) j ∧
     (9/5:ℝ)*sourceOriginalPGroupScale 6 (u^10) j ≤
       (u^10)^(2/5:ℝ) ↔ 6*N+1 ≤ j ∧ j ≤ 7*N
  rw [hBand]
  have hLower : (3/22:ℝ)*u^6 ≤ (2:ℝ)^j ↔ 6*N+1 ≤ j := by
    rw [source_native_r6_cofinal_root_power434 N 6]
    rw [←mul_assoc, mul_comm N 6]
    convert source_native_r6_dyadic_ge_iff434
      ((3/22:ℝ)*(3/2:ℝ)^6) (6*N) 0 j
      (by norm_num) (by norm_num) using 1 <;> omega
  have hUpper : (2:ℝ)^j ≤ (5/44:ℝ)*u^7 ↔ j ≤ 7*N := by
    rw [source_native_r6_cofinal_root_power434 N 7]
    rw [←mul_assoc, mul_comm N 7]
    convert source_native_r6_dyadic_le_iff434
      ((5/44:ℝ)*(3/2:ℝ)^7) (7*N) 0 j
      (by norm_num) (by norm_num) using 1 <;> omega
  exact and_congr hLower hUpper
end Green64Analytic.SourceBlockSieve

end

end

