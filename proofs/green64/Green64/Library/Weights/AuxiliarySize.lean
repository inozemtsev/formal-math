module

public import Green64.Library.Weights.SelectedLogSize
public import Green64.Library.Weights.FullBanSelectedUnits
public import Green64.Library.Weights.PShiftRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Weights / AuxiliarySize

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualAuxiliarySize -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Uniform logarithmic bound for the complete original DA*DB, with every
independent auxiliary slot and all numerical repetitions retained. -/
theorem b611_actual_auxiliary_log_bound434
    (r m : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : Real.exp 1 ≤ L)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (haux : aux ∈ Fintype.piFinset
      (sourceOriginalProbeAuxPrimeSets434 m nu (sourceOriginalPAllActualBands r L))) :
    let D := sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux
    0 < D ∧ Real.log (D : ℝ) ≤ 2 * b596SelectedLogBudget m L := by
  dsimp only
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hLp : 0 ≤ L := by linarith
  have hmem : ∀ z, aux z ∈ sourceOriginalPAllActualBands r L
      (sourceOriginalProbeAuxGroup434 m nu z) := by
    intro z
    have hz := Fintype.mem_piFinset.mp haux z
    cases z <;> exact hz
  have hpos : ∀ z, 0 < aux z := fun z =>
    (source_original_P_all_actual_band_prime r L _ _ (hmem z)).pos
  have hbound : ∀ z, Real.log (aux z : ℝ) ≤ L^(2/5 : ℝ) := fun z =>
    source_original_P_all_actual_band_log r L hL1 _ _ (hmem z)
  have hgroup : (Fintype.card (sourceOriginalPAllGroupType r L) : ℝ) ≤
      (3 + (Real.log 2)⁻¹) * Real.log L := by
    simpa only [sourceOriginalPAllGroupType, Fintype.card_coe] using
      source_original_P_all_group_card_log r L hr hL
  have hcA : Fintype.card nu.1 ≤
      Fintype.card (sourceOriginalPAllGroupType r L) * m := by
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using nu.1.card_le_univ
  have hcB : Fintype.card nu.2 ≤
      Fintype.card (sourceOriginalPAllGroupType r L) * m := by
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using nu.2.card_le_univ
  have hcN : Fintype.card (SourceOriginalProbeAuxIndex434 m nu) ≤
      2 * Fintype.card (sourceOriginalPAllGroupType r L) * m := by
    simp only [SourceOriginalProbeAuxIndex434, Fintype.card_sum]
    nlinarith [hcA, hcB]
  have hc : (Fintype.card (SourceOriginalProbeAuxIndex434 m nu) : ℝ) ≤
      2 * (Fintype.card (sourceOriginalPAllGroupType r L) : ℝ) * (m : ℝ) := by
    exact_mod_cast hcN
  rw [← source_original_probe_aux_product_split434]
  refine ⟨Finset.prod_pos (fun z _ => hpos z), ?_⟩
  rw [Nat.cast_prod, Real.log_prod]
  · calc
      (∑ z, Real.log (aux z : ℝ)) ≤ ∑ _z : SourceOriginalProbeAuxIndex434 m nu, L^(2/5 : ℝ) :=
        Finset.sum_le_sum (fun z _ => hbound z)
      _ = (Fintype.card (SourceOriginalProbeAuxIndex434 m nu) : ℝ) * L^(2/5 : ℝ) := by simp
      _ ≤ (2 * (Fintype.card (sourceOriginalPAllGroupType r L) : ℝ) * (m : ℝ)) * L^(2/5 : ℝ) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hLp _)
      _ ≤ (2 * ((3 + (Real.log 2)⁻¹) * Real.log L) * (m : ℝ)) * L^(2/5 : ℝ) := by gcongr
      _ = 2 * b596SelectedLogBudget m L := by unfold b596SelectedLogBudget; ring
  · intro z _
    exact_mod_cast (hpos z).ne'

private theorem b611_eventually_auxiliary_shift_log_budget
    (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
      Real.log 4 + (K+89)*Real.log L + 2*b596SelectedLogBudget m L ≤ Real.sqrt L / 2 := by
  let B : ℝ := 2*(m : ℝ)*(3+(Real.log 2)⁻¹)
  let C : ℝ := Real.log 4+K+89
  let A : ℝ := C+B+1
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hA : 0 < A := by dsimp [A]; linarith
  have he : 0 < (1 : ℝ)/(2*A) := by positivity
  filter_upwards [(isLittleO_log_rpow_atTop (show (0 : ℝ)<1/10 by norm_num)).bound he,
    eventually_ge_atTop (Real.exp 1)] with L hbd hL
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans hL
  have hlog1 : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hL
  have hlog0 : 0 ≤ Real.log L := by linarith
  have hpow1 : 1 ≤ L^(2/5 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hb : Real.log L ≤ ((1 : ℝ)/(2*A))*L^(1/10 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hL0.le (1/10 : ℝ))] using hbd
  have hhalf : A*Real.log L ≤ L^(1/10 : ℝ)/2 := by
    calc
      _ ≤ A*(((1 : ℝ)/(2*A))*L^(1/10 : ℝ)) := mul_le_mul_of_nonneg_left hb hA.le
      _ = L^(1/10 : ℝ)/2 := by field_simp
  have hfirst : Real.log 4+(K+89)*Real.log L ≤ C*Real.log L := by
    dsimp [C]
    nlinarith
  have hfirst' : Real.log 4+(K+89)*Real.log L ≤ C*Real.log L*L^(2/5 : ℝ) :=
    hfirst.trans (le_mul_of_one_le_right (mul_nonneg hC hlog0) hpow1)
  have hbudget : 2*b596SelectedLogBudget m L = B*Real.log L*L^(2/5 : ℝ) := by
    dsimp [b596SelectedLogBudget, B]
    ring
  refine ⟨hL, ?_⟩
  calc
    _ ≤ C*Real.log L*L^(2/5 : ℝ) + B*Real.log L*L^(2/5 : ℝ) := by rw [hbudget]; linarith
    _ = (C+B)*Real.log L*L^(2/5 : ℝ) := by ring
    _ ≤ A*Real.log L*L^(2/5 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show C+B ≤ A by dsimp [A]; linarith) hlog0)
        (Real.rpow_nonneg hL0.le _)
    _ ≤ (L^(1/10 : ℝ)/2)*L^(2/5 : ℝ) :=
      mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hL0.le _)
    _ = Real.sqrt L/2 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hL0, Real.sqrt_eq_rpow]
      norm_num

/-- The original full physical shift, including the complete DA*DB,
is below W=e^(sqrt L), uniformly in every original signed k. -/
theorem eventually_b611_actual_auxiliary_shift_below_W434
    (r m : ℕ) (K : ℝ) (hr : 1 ≤ r) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
      ∀ (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
        (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
      aux ∈ Fintype.piFinset
        (sourceOriginalProbeAuxPrimeSets434 m nu (sourceOriginalPAllActualBands r L)) →
      let D := sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux
      Real.log (D : ℝ) ≤ Real.sqrt L/2 ∧
      ∀ k ∈ sourceCorrectedSmoothKSet (L^K) (L^(89 : ℝ)),
        k ≠ 0 ∧ ((2*k*(D : ℤ)).natAbs : ℝ) ≤ Real.exp (Real.sqrt L) := by
  filter_upwards [b611_eventually_auxiliary_shift_log_budget m K hK] with L h
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le h.1
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans h.1
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  refine ⟨h.1, ?_⟩
  intro nu aux haux
  dsimp only
  let D := sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux
  have hd := b611_actual_auxiliary_log_bound434 r m L hr h.1 nu aux haux
  have hDp : (0 : ℝ) < D := by exact_mod_cast hd.1
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hbase : Real.log 4 + (K+89)*Real.log L + Real.log (D : ℝ) ≤ Real.sqrt L/2 := by
    have hdlog : Real.log (D : ℝ) ≤ 2*b596SelectedLogBudget m L := hd.2
    linarith [h.2]
  refine ⟨by dsimp [D] at hbase ⊢; nlinarith, ?_⟩
  intro k hk
  have hshift := source_corrected_smooth_shift_abs_le
    (L^K) (L^(89 : ℝ)) (by positivity) k hk
  refine ⟨hshift.1, ?_⟩
  have h2k : ((2*k).natAbs : ℝ) ≤ 4*L^(K+89) := by
    calc
      _ = 2*(k.natAbs : ℝ) := by norm_num [Int.natAbs_mul]
      _ ≤ 2*(2*L^K*L^(89 : ℝ)) := mul_le_mul_of_nonneg_left hshift.2.2 (by norm_num)
      _ = 4*L^(K+89) := by rw [Real.rpow_add hL0]; ring
  calc
    ((2*k*(D : ℤ)).natAbs : ℝ) = ((2*k).natAbs : ℝ)*(D : ℝ) := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast, Nat.cast_mul]
    _ ≤ 4*L^(K+89)*(D : ℝ) := mul_le_mul_of_nonneg_right h2k hDp.le
    _ = Real.exp (Real.log 4+(K+89)*Real.log L+Real.log (D : ℝ)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ)<4),
        Real.exp_log hDp, Real.rpow_def_of_pos hL0]
      rw [mul_comm (Real.log L) (K+89)]
    _ ≤ Real.exp (Real.sqrt L/2) := Real.exp_le_exp.mpr hbase
    _ ≤ Real.exp (Real.sqrt L) := Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg L])

end Green64Analytic.ShiftTwoTerminal

end

end

