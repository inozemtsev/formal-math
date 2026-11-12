module

public import Green64.Library.Weights.Part019
public import Mathlib

@[expose] public section

/-!
# Weights / R6RealBandCriterion

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeR6RealBandCriterion -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 11500000

private theorem source_r6_tenth_root434
    (u : ℝ) (hu : 0 < u) (a : ℕ) :
    (u^10)^((a:ℝ)/10) = u^a := by
  rw [←Real.rpow_natCast u 10, ←Real.rpow_mul hu.le,
    ←Real.rpow_natCast u a]
  congr 1
  ring

/-- The EXACT original r=6 dyadic P-group exponent L=(u^10)
is rationally equivalent to thresholds on 2^j.
The source factors 3/2, 9/5 and 11/5 are retained literally.
No alternate prime-band family, approximate group count or equality
between SMALL and BIG group counts is assumed. -/
theorem source_native_r6_small_big_band_real_iff434
    (u : ℝ) (hu : 0 < u) (j : ℕ) :
    let L : ℝ := u^10
    let q : ℝ := (2:ℝ)^j
    (L^(1/10:ℝ) ≤
         (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
       (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤
         L^(1/5:ℝ) ↔
       (3/22:ℝ)*u^8 ≤ q ∧ q ≤ (5/44:ℝ)*u^9) ∧
    (L^(3/10:ℝ) ≤
         (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
       (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤
         L^(2/5:ℝ) ↔
       (3/22:ℝ)*u^6 ≤ q ∧ q ≤ (5/44:ℝ)*u^7) := by
  let L : ℝ := u^10
  let q : ℝ := (2:ℝ)^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hScale : sourceOriginalPGroupScale 6 L j =
      (5/66:ℝ)*u^10/q := by
    dsimp [sourceOriginalPGroupScale,L,q]
    ring
  have hA : (3/2:ℝ)*sourceOriginalPGroupScale 6 L j =
      ((5/44:ℝ)*u^10)/q := by rw [hScale]; ring
  have hB : (9/5:ℝ)*sourceOriginalPGroupScale 6 L j =
      ((3/22:ℝ)*u^10)/q := by rw [hScale]; ring
  have hR1 : L^(1/10:ℝ)=u := by
    dsimp [L]
    simpa only [Nat.cast_one,pow_one] using source_r6_tenth_root434 u hu 1
  have hR2 : L^(1/5:ℝ)=u^2 := by
    dsimp [L]
    convert source_r6_tenth_root434 u hu 2 using 1 <;> norm_num
  have hR3 : L^(3/10:ℝ)=u^3 := by
    dsimp [L]
    convert source_r6_tenth_root434 u hu 3 using 1 <;> norm_num
  have hR4 : L^(2/5:ℝ)=u^4 := by
    dsimp [L]
    convert source_r6_tenth_root434 u hu 4 using 1 <;> norm_num
  have hTop1 : (u ≤ ((5/44:ℝ)*u^10)/q) ↔
      q ≤ (5/44:ℝ)*u^9 := by
    rw [le_div_iff₀ hq]
    calc
      (u*q ≤ (5/44:ℝ)*u^10) ↔
        (u*q ≤ u*((5/44:ℝ)*u^9)) := by
          congr 1
          ring
      _ ↔ q ≤ (5/44:ℝ)*u^9 :=
        (mul_le_mul_iff_of_pos_left hu)
  have hBot1 : (((3/22:ℝ)*u^10)/q ≤ u^2) ↔
      (3/22:ℝ)*u^8 ≤ q := by
    rw [div_le_iff₀ hq]
    calc
      ((3/22:ℝ)*u^10 ≤ u^2*q) ↔
        (u^2*((3/22:ℝ)*u^8) ≤ u^2*q) := by
          congr 1
          ring
      _ ↔ (3/22:ℝ)*u^8 ≤ q :=
        (mul_le_mul_iff_of_pos_left (pow_pos hu 2))
  have hTop2 : (u^3 ≤ ((5/44:ℝ)*u^10)/q) ↔
      q ≤ (5/44:ℝ)*u^7 := by
    rw [le_div_iff₀ hq]
    calc
      (u^3*q ≤ (5/44:ℝ)*u^10) ↔
        (u^3*q ≤ u^3*((5/44:ℝ)*u^7)) := by
          congr 1
          ring
      _ ↔ q ≤ (5/44:ℝ)*u^7 :=
        (mul_le_mul_iff_of_pos_left (pow_pos hu 3))
  have hBot2 : (((3/22:ℝ)*u^10)/q ≤ u^4) ↔
      (3/22:ℝ)*u^6 ≤ q := by
    rw [div_le_iff₀ hq]
    calc
      ((3/22:ℝ)*u^10 ≤ u^4*q) ↔
        (u^4*((3/22:ℝ)*u^6) ≤ u^4*q) := by
          congr 1
          ring
      _ ↔ (3/22:ℝ)*u^6 ≤ q :=
        (mul_le_mul_iff_of_pos_left (pow_pos hu 4))
  change
    (L^(1/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
      (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤ L^(1/5:ℝ) ↔
      (3/22:ℝ)*u^8 ≤ q ∧ q ≤ (5/44:ℝ)*u^9) ∧
    (L^(3/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale 6 L j ∧
      (9/5:ℝ)*sourceOriginalPGroupScale 6 L j ≤ L^(2/5:ℝ) ↔
      (3/22:ℝ)*u^6 ≤ q ∧ q ≤ (5/44:ℝ)*u^7)
  rw [hA,hB,hR1,hR2,hR3,hR4]
  constructor
  · simpa only [and_comm] using (and_congr hTop1 hBot1)
  · simpa only [and_comm] using (and_congr hTop2 hBot2)
end Green64Analytic.SourceBlockSieve

end

end

