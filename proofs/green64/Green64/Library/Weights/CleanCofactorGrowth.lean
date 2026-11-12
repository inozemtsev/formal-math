module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

/-!
# Weights / CleanCofactorGrowth

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## CleanCofactorGrowth -/

section

open Filter Real Asymptotics
noncomputable section
namespace Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- A fixed logarithmic coefficient is absorbed by any positive fractional
power, with quantitative margin reserved for the original long cofactor. -/
private theorem eventually_log_below_growth434
    (A κ : ℝ) (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, A*Real.log L ≤ κ*L^(3/5:ℝ) := by
  let M := A+1
  have hM : 0 < M := by dsimp [M]; linarith
  filter_upwards [(isLittleO_log_rpow_atTop
    (by norm_num : (0:ℝ)<(3/5:ℝ))).bound (div_pos hκ hM),
    eventually_gt_atTop (Real.exp 1)] with L hbd hL
  have hL0 : 0 ≤ L := (Real.exp_pos 1).le.trans hL.le
  have hG : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) hL.le
  have hG0 : 0 ≤ Real.log L := by linarith
  have hb : Real.log L ≤ (κ/M)*L^(3/5:ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hG0,
      abs_of_nonneg (Real.rpow_nonneg hL0 _)] using hbd
  calc
    A*Real.log L ≤ M*Real.log L :=
      mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) hG0
    _ ≤ M*((κ/M)*L^(3/5:ℝ)) :=
      mul_le_mul_of_nonneg_left hb hM.le
    _ = κ*L^(3/5:ℝ) := by field_simp [ne_of_gt hM]

/-- True size hierarchy of the original D61 clean cofactor sector:
even the full fixed-log-power k window and two SMALL/BIG auxiliary products
are asymptotically shorter than the product of the long m,t cofactors. -/
theorem eventually_clean_cofactor_growth434
    (C κ : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop,
      8*Real.exp L*L^(2*C) *
          Real.exp (2*C*L^(2/5:ℝ)*Real.log L) <
        Real.exp ((1+2*κ)*L) := by
  have h8 : 0 ≤ Real.log (8:ℝ) :=
    Real.log_nonneg (by norm_num)
  have hA : 0 ≤ Real.log (8:ℝ)+4*C := by linarith
  filter_upwards [eventually_log_below_growth434
     (Real.log 8+4*C) κ hA hκ,
    eventually_gt_atTop (Real.exp 1)] with L hsmall hL
  have hLp : 0 < L := (Real.exp_pos 1).trans hL
  have hG : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) hL.le
  have hG0 : 0 ≤ Real.log L := by linarith
  have hL1 : 1 ≤ L := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans hL.le
  have hP : 1 ≤ L^(2/5:ℝ) :=
    Real.one_le_rpow hL1 (by norm_num)
  have hprod : L^(3/5:ℝ)*L^(2/5:ℝ)=L := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hsmall2 :
      (Real.log 8+4*C)*L^(2/5:ℝ)*Real.log L ≤ κ*L := by
    have hx := mul_le_mul_of_nonneg_right hsmall
      (Real.rpow_nonneg hLp.le (2/5:ℝ))
    nlinarith [hx, hprod]
  have hmult : Real.log L ≤ L^(2/5:ℝ)*Real.log L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hP hG0
  have hunit : (1:ℝ) ≤ L^(2/5:ℝ)*Real.log L := by
    nlinarith [hG, hmult]
  have hcoef :
      Real.log 8+2*C*Real.log L+
          2*C*L^(2/5:ℝ)*Real.log L ≤
        (Real.log 8+4*C)*L^(2/5:ℝ)*Real.log L := by
    nlinarith [mul_le_mul_of_nonneg_left hunit h8,
      mul_le_mul_of_nonneg_left hmult
        (by linarith : 0 ≤ 2*C)]
  have hMargin : Real.log 8+L+2*C*Real.log L+
      2*C*L^(2/5:ℝ)*Real.log L < (1+2*κ)*L := by
    have hL0 : 0 < L := hLp
    nlinarith [hcoef, hsmall2]
  calc
    8*Real.exp L*L^(2*C) *
        Real.exp (2*C*L^(2/5:ℝ)*Real.log L) =
      Real.exp (Real.log 8+L+2*C*Real.log L+
        2*C*L^(2/5:ℝ)*Real.log L) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add,
          Real.exp_log (by norm_num : (0:ℝ)<8),
          Real.rpow_def_of_pos hLp]
        ring
    _ < Real.exp ((1+2*κ)*L) :=
      Real.exp_lt_exp.mpr hMargin

/-- Physical support condition: using the explicit original Z, signed-k,
    auxiliary-product and two long-cofactor bounds gives strict
    cross-product separation, with no extra analytic premise. -/
theorem eventually_clean_cofactor_physical_separation434
    (C κ : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ Z K B m t : ℝ,
        0 ≤ Z → Z ≤ Real.exp L * L^C →
        0 ≤ K → K ≤ L^C →
        0 ≤ B → B ≤ Real.exp (C*L^(2/5:ℝ)*Real.log L) →
        Real.exp ((1/2+κ)*L) ≤ m →
        Real.exp ((1/2+κ)*L) ≤ t →
        4*Z*K*B^2 < m*t := by
  filter_upwards [eventually_clean_cofactor_growth434 C κ hC hκ,
    eventually_gt_atTop (1:ℝ)] with L hgrowth hL
  have hLp : 0 < L := by linarith
  intro Z K B m t hZ hZcap hK hKcap hB hBcap hm ht
  have hpow : (L^C)*(L^C) = L^(2*C) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  have hExp : (Real.exp (C*L^(2/5:ℝ)*Real.log L))^2 =
      Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    4*Z*K*B^2 ≤
        4*(Real.exp L*L^C)*(L^C)*
          (Real.exp (C*L^(2/5:ℝ)*Real.log L))^2 := by
      gcongr
    _ = 4*Real.exp L*L^(2*C)*
          Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := by
      rw [hExp, ← hpow]
      ring
    _ ≤ 8*Real.exp L*L^(2*C)*
          Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := by
      have hpos : 0 ≤ Real.exp L*L^(2*C)*
          Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := by positivity
      nlinarith
    _ < Real.exp ((1+2*κ)*L) := hgrowth
    _ = Real.exp ((1/2+κ)*L)*Real.exp ((1/2+κ)*L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ m*t := mul_le_mul hm ht (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hm)
end Green64ComparisonPartial

end

end

