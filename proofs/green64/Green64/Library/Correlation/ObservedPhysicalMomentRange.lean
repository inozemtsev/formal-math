module

public import Green64.Library.Weights.Part098
public import Green64.Library.Weights.EventualSelectedMomentRange

@[expose] public section

/-!
# Correlation / ObservedPhysicalMomentRange

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ObservedPhysicalMomentRange -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The actual original P-band log bound applied directly to an observed
carrier. Repeated independent draws are allowed; no hidden completion or
physical point is assumed to exist. This is the grouped consumer of the
same band/cardinality argument used in B596. -/
theorem b598_actual_observed_product_log434
    (r m : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : Real.exp 1 ≤ L)
    (c : sourceOriginalPAllGroupType r L → ℕ) (hc : ∀g,c g ≤ m)
    (a : ∀g,Fin (c g) → ℕ)
    (ha : a∈b598RawSelectedGroupLists434 (sourceOriginalPAllActualBands r L) c) :
    0 < (∏g,∏i,a g i) ∧
      Real.log ((∏g,∏i,a g i:ℕ):ℝ) ≤ b596SelectedLogBudget m L := by
  let I := Σg : sourceOriginalPAllGroupType r L,Fin (c g)
  let p : I → ℕ := fun z => a z.1 z.2
  have hmem := (b598_mem_raw_selected_group_lists434 _ c a).mp ha
  have hpos (z : I) : 0 < p z :=
    (source_original_P_all_actual_band_prime r L z.1 (p z) (hmem _ _)).pos
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hL
  have hLp : 0 ≤ L := by linarith
  have hbound (z : I) : Real.log (p z:ℝ) ≤ L^(2/5:ℝ) :=
    source_original_P_all_actual_band_log r L hL1 z.1 (p z) (hmem _ _)
  have hcard : Fintype.card I ≤ Fintype.card (sourceOriginalPAllGroupType r L)*m := by
    dsimp only [I]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    calc
      (∑g,c g) ≤ ∑_g : sourceOriginalPAllGroupType r L,m :=
        Finset.sum_le_sum (fun g _ => hc g)
      _ = _ := by simp
  have hgroup : (Fintype.card (sourceOriginalPAllGroupType r L):ℝ) ≤
      (3+(Real.log 2)⁻¹)*Real.log L := by
    simpa only [sourceOriginalPAllGroupType,Fintype.card_coe] using
      source_original_P_all_group_card_log r L hr hL
  have hcardR : (Fintype.card I:ℝ) ≤
      (Fintype.card (sourceOriginalPAllGroupType r L):ℝ)*(m:ℝ) := by
    exact_mod_cast hcard
  have hprod : (∏z : I,p z)=(∏g,∏i,a g i) := Fintype.prod_sigma p
  rw [←hprod]
  refine ⟨Finset.prod_pos (fun z _ => hpos z),?_⟩
  rw [Nat.cast_prod,Real.log_prod]
  · calc
      (∑z,Real.log (p z:ℝ)) ≤ ∑_z:I,L^(2/5:ℝ) :=
        Finset.sum_le_sum (fun z _ => hbound z)
      _ = (Fintype.card I:ℝ)*L^(2/5:ℝ) := by simp
      _ ≤ ((Fintype.card (sourceOriginalPAllGroupType r L):ℝ)*(m:ℝ))*L^(2/5:ℝ) :=
        mul_le_mul_of_nonneg_right hcardR (Real.rpow_nonneg hLp _)
      _ ≤ (((3+(Real.log 2)⁻¹)*Real.log L)*(m:ℝ))*L^(2/5:ℝ) := by gcongr
      _ = b596SelectedLogBudget m L := by unfold b596SelectedLogBudget; ring
  · intro z hz
    exact_mod_cast (hpos z).ne'

/-- Uniform unit-AP moment range for every raw observed pair from the
literal original P bands. The fixed m precedes the eventual L threshold;
all counts, tuples and real physical lengths follow it. -/
theorem eventually_b598_observed_moment_range434
    (r m : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (cA cB : sourceOriginalPAllGroupType r L → ℕ)
        (_hcA : ∀g,cA g ≤ m) (_hcB : ∀g,cB g ≤ m)
        (a : ∀g,Fin (cB g) → ℕ) (b : ∀g,Fin (cA g) → ℕ),
      a∈b598RawSelectedGroupLists434 (sourceOriginalPAllActualBands r L) cB →
      b∈b598RawSelectedGroupLists434 (sourceOriginalPAllActualBands r L) cA →
      ∀Y : ℝ,Real.exp (L/2) ≤ Y →
      let XB := ∏g,∏i,a g i
      let XA := ∏g,∏i,b g i
      0 < XA ∧ 0 < XB ∧ XA^16 ≤ ⌊Y⌋₊/XB ∧ XB^16 ≤ ⌊Y⌋₊/XA := by
  filter_upwards [eventually_b596_selected_log_budget434 m] with L h
  intro cA cB hcA hcB a b ha hb Y hY
  dsimp only
  have hs := b598_actual_observed_product_log434 r m L hr h.1 cB hcB a ha
  have ht := b598_actual_observed_product_log434 r m L hr h.1 cA hcA b hb
  let XA := ∏g,∏i,b g i
  let XB := ∏g,∏i,a g i
  have hXAN : 0 < XA := ht.1
  have hXBN : 0 < XB := hs.1
  have hXAr : 0 < (XA:ℝ) := by exact_mod_cast ht.1
  have hXBr : 0 < (XB:ℝ) := by exact_mod_cast hs.1
  have hAB : ((XA^16*XB:ℕ):ℝ) ≤ Real.exp (L/2) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul (pow_ne_zero 16 hXAr.ne') hXBr.ne',Real.log_pow]
    norm_num
    have hA : Real.log (XA:ℝ) ≤ b596SelectedLogBudget m L := ht.2
    have hB : Real.log (XB:ℝ) ≤ b596SelectedLogBudget m L := hs.2
    linarith [h.2]
  have hBA : ((XB^16*XA:ℕ):ℝ) ≤ Real.exp (L/2) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul (pow_ne_zero 16 hXBr.ne') hXAr.ne',Real.log_pow]
    norm_num
    have hA : Real.log (XA:ℝ) ≤ b596SelectedLogBudget m L := ht.2
    have hB : Real.log (XB:ℝ) ≤ b596SelectedLogBudget m L := hs.2
    linarith [h.2]
  exact ⟨ht.1,hs.1,
    (Nat.le_div_iff_mul_le hs.1).mpr (Nat.le_floor (hAB.trans hY)),
    (Nat.le_div_iff_mul_le ht.1).mpr (Nat.le_floor (hBA.trans hY))⟩
end Green64Analytic.ShiftTwoTerminal

end

end

