module

public import Green64.Library.Weights.LiteralPBandTwoCore
public import Green64.Library.Correlation.Part032

@[expose] public section

/-!
# Weights / SelectedLogSize

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualSelectedLogSize -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Explicit size of the ACTUAL selected first-m products. The whole
original moving P family is counted, so this bound is uniform in J, ell,
the original pattern, both marked lists and physical endpoints. -/
def b596SelectedLogBudget (m : ℕ) (L : ℝ) : ℝ :=
  (m:ℝ)*(3+(Real.log 2)⁻¹)*Real.log L*L^(2/5:ℝ)

private theorem b596_actual_selected_product_log
    (r m : ℕ) (L : ℝ) (hr : 1≤ r) (hL : Real.exp 1≤L)
    {I : Type} [Fintype I]
    (g : I → sourceOriginalPAllGroupType r L) (p : I → ℕ)
    (hp : ∀ i, p i∈sourceOriginalPAllActualBands r L (g i))
    (hcard : Fintype.card I ≤ Fintype.card (sourceOriginalPAllGroupType r L)*m) :
    0<(∏i,p i) ∧ Real.log ((∏i,p i:ℕ):ℝ) ≤ b596SelectedLogBudget m L := by
  have hL1 : 1≤L := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hL0 : 0≤L := by linarith
  have hpos : ∀ i, 0<p i :=
    fun i => (source_original_P_all_actual_band_prime r L (g i) (p i) (hp i)).pos
  have hbound : ∀ i, Real.log (p i:ℝ) ≤ L^(2/5:ℝ) :=
    fun i => source_original_P_all_actual_band_log r L hL1 (g i) (p i) (hp i)
  have hgroup : (Fintype.card (sourceOriginalPAllGroupType r L):ℝ) ≤
      (3+(Real.log 2)⁻¹)*Real.log L := by
    simpa only [sourceOriginalPAllGroupType,Fintype.card_coe] using
      source_original_P_all_group_card_log r L hr hL
  have hc : (Fintype.card I:ℝ) ≤
      (Fintype.card (sourceOriginalPAllGroupType r L):ℝ)*(m:ℝ) := by
    exact_mod_cast hcard
  refine ⟨Finset.prod_pos (fun i hi => hpos i),?_⟩
  rw [Nat.cast_prod,Real.log_prod]
  · calc
      (∑i,Real.log (p i:ℝ)) ≤ ∑_i:I,L^(2/5:ℝ) :=
        Finset.sum_le_sum (fun i hi => hbound i)
      _ = (Fintype.card I:ℝ)*L^(2/5:ℝ) := by simp
      _ ≤ ((Fintype.card (sourceOriginalPAllGroupType r L):ℝ)*(m:ℝ))*L^(2/5:ℝ) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL0 _)
      _ ≤ (((3+(Real.log 2)⁻¹)*Real.log L)*(m:ℝ))*L^(2/5:ℝ) := by
        gcongr
      _ = b596SelectedLogBudget m L := by unfold b596SelectedLogBudget; ring
  · intro i hi
    exact_mod_cast (hpos i).ne'

/-- Literal selected X_A and X_B, with original free-slot embeddings and
all original P bands. There is no assumed size or P-part cap. Each selected
block contains at most m times the true moving group count. -/
theorem b596_literal_selected_log_bound434
    (r : ℕ) (L : ℝ) (hr : 1≤ r) (hL : Real.exp 1≤L)
    (J ell m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
    (w wp : ℕ)
    (a b : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a∈bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b∈bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp) :
    let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a
    let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b
    0<XA ∧ 0<XB ∧ Real.log (XA:ℝ)≤b596SelectedLogBudget m L ∧
      Real.log (XB:ℝ)≤b596SelectedLogBudget m L := by
  have hmemA : ∀ g i, a g i∈sourceOriginalPAllActualBands r L g := by
    intro g i
    have hg := Fintype.mem_piFinset.mp ha g
    have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
    exact (Finset.mem_filter.mp hi).1
  have hmemB : ∀ g i, b g i∈sourceOriginalPAllActualBands r L g := by
    intro g i
    have hg := Fintype.mem_piFinset.mp hb g
    have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
    exact (Finset.mem_filter.mp hi).1
  have hcardA : Fintype.card nu.1 ≤
      Fintype.card (sourceOriginalPAllGroupType r L)*m := by
    simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using nu.1.card_le_univ
  have hcardB : Fintype.card nu.2 ≤
      Fintype.card (sourceOriginalPAllGroupType r L)*m := by
    simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using nu.2.card_le_univ
  have hs := b596_actual_selected_product_log r m L hr hL
    (fun z : nu.2 => z.val.1)
    (fun z : nu.2 => a z.val.1
      (sourceOriginalProbeFreeIndex434 J ell m hmJ nu z.val.1 z.val.2 (Or.inr z.property)))
    (fun z => hmemA _ _) hcardB
  have ht := b596_actual_selected_product_log r m L hr hL
    (fun z : nu.1 => z.val.1)
    (fun z : nu.1 => b z.val.1
      (sourceOriginalProbeFreeIndex434 J ell m hmJ nu z.val.1 z.val.2 (Or.inl z.property)))
    (fun z => hmemB _ _) hcardA
  exact ⟨ht.1,hs.1,ht.2,hs.2⟩
end Green64Analytic.ShiftTwoTerminal

end

end

