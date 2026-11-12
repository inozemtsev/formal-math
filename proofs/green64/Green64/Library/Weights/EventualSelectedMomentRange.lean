module

public import Green64.Library.Weights.SelectedLogSize
public import Green64.Library.Weights.OriginalScaleAsymptotics

@[expose] public section

/-!
# Weights / EventualSelectedMomentRange

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## EventualSelectedMomentRange -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Existing original cell scalar asymptotics, applied to 17m selected
factors, prove the moment range budget uniformly at every sufficiently
large real L. No selected-product or divisor-moment estimate is assumed. -/
theorem eventually_b596_selected_log_budget434 (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧ 17*b596SelectedLogBudget m L≤L/2 := by
  let C : ℝ := 3+(Real.log 2)⁻¹
  have hC : 0≤C := by dsimp [C]; positivity
  filter_upwards [eventually_source_native_cell_scalar_budget434
    0 0 C (17*m) (by norm_num) (by norm_num) hC] with L h
  rcases h with ⟨hL,h32,h3,h4,h5,hupper,h7,h8⟩
  have hLpos : 0<L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1≤L := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hlog : 0≤Real.log L := Real.log_nonneg hL1
  have hlog144 : 0≤Real.log (144:ℝ) := Real.log_nonneg (by norm_num)
  have hcoef : 17*(m:ℝ)*C*Real.log L ≤ L^(3/5:ℝ)/2 := by
    push_cast at hupper
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hLpos.le (2/5:ℝ))
  have hrpow : L^(3/5:ℝ)*L^(2/5:ℝ)=L := by
    rw [←Real.rpow_add hLpos]
    norm_num
  refine ⟨hL,?_⟩
  unfold b596SelectedLogBudget
  dsimp [C] at hprod
  nlinarith [hrpow]

private theorem b596_moment_range_of_logs
    (L Y B : ℝ) (XA XB : ℕ) (hXA : 0<XA) (hXB : 0<XB)
    (hA : Real.log (XA:ℝ)≤B) (hB : Real.log (XB:ℝ)≤B)
    (hbudget : 17*B≤L/2) (hY : Real.exp (L/2)≤Y) :
    XA^16≤⌊Y⌋₊/XB ∧ XB^16≤⌊Y⌋₊/XA := by
  have hXAr : 0<(XA:ℝ) := by exact_mod_cast hXA
  have hXBr : 0<(XB:ℝ) := by exact_mod_cast hXB
  have hAB : ((XA^16*XB:ℕ):ℝ)≤Real.exp (L/2) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul (pow_ne_zero 16 hXAr.ne') hXBr.ne',Real.log_pow]
    norm_num
    linarith
  have hBA : ((XB^16*XA:ℕ):ℝ)≤Real.exp (L/2) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul (pow_ne_zero 16 hXBr.ne') hXAr.ne',Real.log_pow]
    norm_num
    linarith
  exact ⟨(Nat.le_div_iff_mul_le hXB).mpr (Nat.le_floor (hAB.trans hY)),
    (Nat.le_div_iff_mul_le hXA).mpr (Nat.le_floor (hBA.trans hY))⟩

/-- The B593/B595 unit-AP size range for both literal selected products
is now an eventual THEOREM. Its threshold precedes J, ell, all original
patterns, both full marked lists and all physical positions. The real
physical cutoff is floored only at the end; no rounding loss is incurred. -/
theorem eventually_b596_actual_selected_moment_range434
    (r m : ℕ) (hr : 1≤ r) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (J ell : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
        (w wp : ℕ)
        (a b : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ),
      a∈bigMarkLists (sourceOriginalPAllActualBands r L)
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w →
      b∈bigMarkLists (sourceOriginalPAllActualBands r L)
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp →
      ∀ (Y : ℝ), Real.exp (L/2)≤Y →
      let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a
      let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b
      XA^16≤⌊Y⌋₊/XB ∧ XB^16≤⌊Y⌋₊/XA := by
  filter_upwards [eventually_b596_selected_log_budget434 m] with L h
  intro J ell hmJ nu w wp a b ha hb Y hY
  have hlog := b596_literal_selected_log_bound434
    r L hr h.1 J ell m hmJ nu w wp a b ha hb
  exact b596_moment_range_of_logs L Y (b596SelectedLogBudget m L) _ _
    hlog.1 hlog.2.1 hlog.2.2.1 hlog.2.2.2 h.2 hY
end Green64Analytic.ShiftTwoTerminal

end

end

