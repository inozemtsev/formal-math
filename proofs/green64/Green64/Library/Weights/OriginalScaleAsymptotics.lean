module

public import Green64.Library.Weights.Part031
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Weights / OriginalScaleAsymptotics

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeOriginalScaleAsymptotics -/

section

open Filter Real Asymptotics
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem native_log_small434 (a C D e : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 < e) :
    ∀ᶠ L : ℝ in atTop, C*Real.log L+D ≤ e*L^a := by
  let M := C+D+1
  have hM : 0 < M := by dsimp [M]; linarith
  filter_upwards [(isLittleO_log_rpow_atTop ha).bound (div_pos he hM),
    eventually_ge_atTop (Real.exp 1)] with L hbd hL
  have hL0 : 0 ≤ L := (Real.exp_pos 1).le.trans hL
  have hlog1 : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hL
  have hlog0 : 0 ≤ Real.log L := by linarith
  have hb : Real.log L ≤ (e/M)*L^a := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hL0 a)] using hbd
  calc
    C*Real.log L+D ≤ M*Real.log L := by dsimp [M]; nlinarith
    _ ≤ M*((e/M)*L^a) := mul_le_mul_of_nonneg_left hb hM.le
    _ = e*L^a := by field_simp [ne_of_gt hM]

/-- One eventual threshold for the literal native Y/cap and signed-chart
budgets. Its fixed constants precede L and every moving native index. -/
theorem eventually_source_native_cell_scalar_budget434
    (K Carc C0 : ℝ) (m : ℕ) (hK : 0 ≤ K) (hCarc : 0 ≤ Carc) (hC0 : 0 ≤ C0) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧ 32 ≤ L ∧ 4*Real.log 32 ≤ L ∧
      2*Real.log 65 ≤ L ∧ Real.log 512+Real.log 32 ≤ L ∧
      (K+89+(m:ℝ)*C0)*Real.log L+Real.log 144 ≤ L^(3/5:ℝ)/2 ∧
      Carc*Real.log L+2+Real.log 2 ≤ 2*L^(3/10:ℝ) ∧
      89*Real.log L+Real.log 512+2 ≤ L := by
  have hlog144 : 0 ≤ Real.log (144:ℝ) := Real.log_nonneg (by norm_num)
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hlog512 : 0 ≤ Real.log (512:ℝ) := Real.log_nonneg (by norm_num)
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (32:ℝ),
    eventually_ge_atTop (4*Real.log 32), eventually_ge_atTop (2*Real.log 65),
    eventually_ge_atTop (Real.log 512+Real.log 32),
    native_log_small434 (3/5) (K+89+(m:ℝ)*C0) (Real.log 144) (1/2)
      (by norm_num) (by positivity) hlog144 (by norm_num),
    native_log_small434 (3/10) Carc (2+Real.log 2) 2
      (by norm_num) hCarc (by linarith) (by norm_num),
    native_log_small434 1 89 (Real.log 512+2) 1
      (by norm_num) (by norm_num) (by linarith) (by norm_num)]
      with L h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨h1,h2,h3,h4,h5,?_,?_,?_⟩
  · linarith
  · linarith
  · simp only [Real.rpow_one, one_mul] at h8
    linarith
end Green64Analytic.ShiftTwoTerminal

end

end

