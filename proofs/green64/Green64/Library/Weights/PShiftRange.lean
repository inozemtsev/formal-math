module

public import Green64.Library.Weights.SelectedUnitGates
public import Green64.Library.Weights.Part031
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Weights / PShiftRange

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualPShiftRange -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 5000000

private theorem b596_eventually_shift_polynomial_below_P (K : ℝ) (hK : 0≤K) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ 4*L^(K+89)<Real.exp (L^(1/10:ℝ)) := by
  let A : ℝ := K+89+Real.log 4+1
  have hlog4 : 0≤Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have hA : 0<A := by dsimp [A]; linarith
  have he : 0<(1:ℝ)/(2*A) := by positivity
  filter_upwards [(isLittleO_log_rpow_atTop (show (0:ℝ)<1/10 by norm_num)).bound he,
    eventually_ge_atTop (Real.exp 1)] with L hbd hL
  have hL0 : 0<L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1≤L := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hlog1 : 1≤Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hL
  have hlog0 : 0≤Real.log L := by linarith
  have hb : Real.log L≤((1:ℝ)/(2*A))*L^(1/10:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hL0.le (1/10:ℝ))] using hbd
  have hhalf : A*Real.log L≤L^(1/10:ℝ)/2 := by
    calc
      _ ≤ A*(((1:ℝ)/(2*A))*L^(1/10:ℝ)) := mul_le_mul_of_nonneg_left hb hA.le
      _ = L^(1/10:ℝ)/2 := by field_simp
  have hcoef : Real.log 4+(K+89)*Real.log L≤A*Real.log L := by
    dsimp [A]
    nlinarith
  have hstrict : Real.log 4+(K+89)*Real.log L<L^(1/10:ℝ) := by
    have hp : 0<L^(1/10:ℝ) := Real.rpow_pos_of_pos hL0 _
    linarith
  refine ⟨hL1,?_⟩
  calc
    4*L^(K+89) = Real.exp (Real.log 4+(K+89)*Real.log L) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4),Real.rpow_def_of_pos hL0]
      congr 2
      ring
    _ < Real.exp (L^(1/10:ℝ)) := Real.exp_lt_exp.mpr hstrict

/-- Every prime of every ORIGINAL P band exceeds the FULL signed |2k|
for every k in the original sigma=1 smooth comparison window. The fixed
threshold precedes all groups, primes and signed shifts. No truncation of
k or replacement of the original P bands occurs. -/
theorem eventually_b596_original_P_exceeds_all_shifts434
    (r : ℕ) (K : ℝ) (hK : 0≤K) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ k∈sourceCorrectedSmoothKSet (L^K) (L^(89:ℝ)), k≠0 ∧
      ∀ g p, p∈sourceOriginalPAllActualBands r L g → (2*k).natAbs<p := by
  filter_upwards [b596_eventually_shift_polynomial_below_P K hK] with L h
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one h.1
  refine ⟨h.1,?_⟩
  intro k hk
  have hshift := source_corrected_smooth_shift_abs_le
    (L^K) (L^(89:ℝ)) (by positivity) k hk
  refine ⟨hshift.1,?_⟩
  intro g p hp
  have h2k : ((2*k).natAbs:ℝ)≤4*L^(K+89) := by
    calc
      _ = 2*(k.natAbs:ℝ) := by norm_num [Int.natAbs_mul]
      _ ≤ 2*(2*L^K*L^(89:ℝ)) := mul_le_mul_of_nonneg_left hshift.2.2 (by norm_num)
      _ = 4*L^(K+89) := by rw [Real.rpow_add hL0]; ring
  have hprime : Real.exp (L^(1/10:ℝ))≤(p:ℝ) := by
    exact (Real.exp_le_exp.mpr
      (source_original_P_all_actual_band_lower r L h.1 g)).trans
      (source_original_P_closed_range _ p hp).1
  have hh : ((2*k).natAbs:ℝ)<(p:ℝ) := (h2k.trans_lt h.2).trans_le hprime
  exact_mod_cast hh
end Green64Analytic.ShiftTwoTerminal

end

end

