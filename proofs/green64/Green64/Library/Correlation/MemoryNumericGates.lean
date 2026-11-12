module

public import Green64.Library.Correlation.MemoryActualDomain
public import Green64.Library.Weights.Part050
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Correlation / MemoryNumericGates

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeMemoryNumericGates -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

private theorem eventual_log_below_fractional_power434
    (C D a : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, C * Real.log L + D < L^a := by
  let M := C + D + 1
  have hM : 0 < M := by dsimp [M]; linarith
  filter_upwards [(isLittleO_log_rpow_atTop ha).bound
    (div_pos (by norm_num : (0:ℝ) < 1/2) hM),
    eventually_gt_atTop (Real.exp 1)] with L hbd hL
  have hL0 : 0 ≤ L := le_of_lt ((Real.exp_pos 1).trans hL)
  have hlog1 : 1 ≤ Real.log L :=
    (Real.log_exp (1:ℝ)).symm ▸
      (Real.log_le_log (Real.exp_pos 1) hL.le)
  have hlog0 : 0 ≤ Real.log L := by linarith
  have hpowpos : 0 < L^a := Real.rpow_pos_of_pos ((Real.exp_pos 1).trans hL) _
  have hb : Real.log L ≤ ((1/2:ℝ)/M)*L^a := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hL0 a)] using hbd
  have hcalc : C*Real.log L+D ≤ M*Real.log L := by
    dsimp [M]; nlinarith
  have hbound : M*Real.log L ≤ (1/2:ℝ)*L^a := by
    calc
      _ ≤ M*((1/2:ℝ)/M*L^a) := mul_le_mul_of_nonneg_left hb hM.le
      _ = (1/2:ℝ)*L^a := by field_simp [ne_of_gt hM]
  linarith

/-- Any fixed polynomial, including the factor two in k_C=2k_T,
    is eventually dominated by the literal exp(L^(1/10)) SMALL floor. -/
theorem eventually_native_memory_poly_shift434 (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      4*L^C < Real.exp (L^(1/10:ℝ)) := by
  have hlog4 : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  filter_upwards [eventual_log_below_fractional_power434 C
    (Real.log 4) (1/10) hC hlog4 (by norm_num),
    eventually_gt_atTop (1:ℝ)] with L hsmall hL
  have hpos : 0 < L := by linarith
  calc
    4*L^C = Real.exp (Real.log 4 + C*Real.log L) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 4),
        Real.rpow_def_of_pos hpos]
      ring
    _ < Real.exp (L^(1/10:ℝ)) := Real.exp_lt_exp.mpr (by linarith)

/-- Exact ORIGINAL R=Nat.ceil(L^0.52): positive and below the
    required BIG prime floor even after both directions of visits. -/
theorem eventually_native_memory_original_visits434 :
    ∀ᶠ L : ℝ in atTop,
      0 < Nat.ceil (L^(0.52:ℝ)) ∧
      ((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) <
        Real.exp (L^(3/10:ℝ)) := by
  have hlog5 : 0 ≤ Real.log (5:ℝ) := Real.log_nonneg (by norm_num)
  filter_upwards [eventual_log_below_fractional_power434
      (0.52:ℝ) (Real.log 5) (3/10) (by norm_num) hlog5 (by norm_num),
    eventually_gt_atTop (2:ℝ)] with L hsmall hL
  have hL1 : 1 ≤ L := by linarith
  have hpowpos : 0 < L^(0.52:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpow1 : 1 ≤ L^(0.52:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hceil : (Nat.ceil (L^(0.52:ℝ)):ℝ) < L^(0.52:ℝ)+1 :=
    Nat.ceil_lt_add_one hpowpos.le
  have hvisit : ((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) <
      5*L^(0.52:ℝ) := by
    push_cast
    linarith
  have hlog : 5*L^(0.52:ℝ) < Real.exp (L^(3/10:ℝ)) := by
    calc
      _ = Real.exp (Real.log 5+(0.52:ℝ)*Real.log L) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<5),
          Real.rpow_def_of_pos (by linarith : 0<L)]
        ring
      _ < Real.exp (L^(3/10:ℝ)) :=
        Real.exp_lt_exp.mpr (by linarith [hsmall])
  exact ⟨Nat.ceil_pos.mpr hpowpos, hvisit.trans hlog⟩
end Green64Analytic.SourceBlockSieve

end

end

