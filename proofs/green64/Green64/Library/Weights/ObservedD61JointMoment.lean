module

public import Green64.Library.Correlation.ObservedPhysicalMomentRange
public import Green64.Library.Weights.ObservedTupleCore
public import Green64.Library.Correlation.PhysicalJointDivisorMoment

@[expose] public section

/-!
# Weights / ObservedD61JointMoment

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ObservedD61JointMoment -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Positive physical rows with the actual signed shift, including both
clean and dirty endpoints. No selected CRT filter is built into this set. -/
def b598PhysicalRows434 (Y D : ℕ) (k : ℤ) : Finset (ℕ×ℕ) :=
  ((Finset.Ioc 0 Y) ×ˢ (Finset.Ioc 0 Y)).filter
    (fun p => (p.2:ℤ)=(p.1:ℤ)+2*k*(D:ℤ))

/-- The literal observed carrier obtained after finite Fubini. Counts
may differ at the two endpoints and no hidden completion is selected. -/
def b598ObservedPhysicalRows434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (cB cA : G → ℕ)
    (marks : ∀g,Fin (cB g) → ℕ) (marks' : ∀g,Fin (cA g) → ℕ)
    (Y D : ℕ) (k : ℤ) : Finset (ℕ×ℕ) :=
  (b598PhysicalRows434 Y D k).filter
    (fun p => marks∈bigMarkLists P cB p.1 ∧ marks'∈bigMarkLists P cA p.2)

@[simp] theorem b598_mem_physical_rows434 {Y D : ℕ} {k : ℤ} {p : ℕ×ℕ} :
    p∈b598PhysicalRows434 Y D k ↔
    (0 < p.1 ∧ p.1 ≤ Y) ∧ (0 < p.2 ∧ p.2 ≤ Y) ∧
      (p.2:ℤ)=(p.1:ℤ)+2*k*(D:ℤ) := by
  simp [b598PhysicalRows434,and_assoc]

/-- A raw observed tuple whose product avoids D is automatically a unit
for the true shift, because every original P prime exceeds 2|k|. No
physical row or probability conditioning is assumed. -/
theorem b598_observed_positive_shift_unit434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (c : G → ℕ)
    (hPrime : ∀g p,p∈P g → p.Prime)
    (D : ℕ) (k : ℤ) (hk : k ≠ 0)
    (hlarge : ∀g p,p∈P g → (2*k).natAbs < p)
    (marks : ∀g,Fin (c g) → ℕ)
    (hmarks : marks∈b598RawSelectedGroupLists434 P c)
    (hunit : (∏g,∏i,marks g i).Coprime D) :
    0 < (∏g,∏i,marks g i) ∧
      (∏g,∏i,marks g i).Coprime (2*k*(D:ℤ)).natAbs := by
  have hmem := (b598_mem_raw_selected_group_lists434 P c marks).mp hmarks
  have hpos (g : G) (i : Fin (c g)) : 0 < marks g i := (hPrime _ _ (hmem g i)).pos
  refine ⟨Finset.prod_pos (fun g _ => Finset.prod_pos (fun i _ => hpos g i)),?_⟩
  have hkunit : (∏g,∏i,marks g i).Coprime (2*k).natAbs := by
    apply Nat.coprime_prod_left_iff.mpr
    intro g hg
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    apply (hPrime _ _ (hmem g i)).coprime_iff_not_dvd.mpr
    intro hd
    have hkpos : 0 < (2*k).natAbs := Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hk)
    exact (not_le_of_gt (hlarge _ _ (hmem g i))) (Nat.le_of_dvd hkpos hd)
  simpa only [Int.natAbs_mul,Int.natAbs_natCast] using hkunit.mul_right hunit

private theorem joint_budget_nonneg (Y XA XB : ℕ) : 0 ≤ b595JointDivisorBudget Y XA XB := by
  by_cases hY : Y=0
  · simp [hY,b595JointDivisorBudget]
  · have hY1 : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hY
    have hlog : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg hY1
    unfold b595JointDivisorBudget
    positivity

/-- Actual sigma-one D61 moment on the direct observed physical carrier.
The unit gates come from retained selected avoidance and the real signed
graph. The moment and both original Q cores are proved, not hypotheses.
The selected-size premises are discharged uniformly by the separate
actual observed P-band theorem before the final full marked envelope. -/
theorem b598_literal_observed_D61_joint_moment434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (cB cA : sourceOriginalPAllGroupType r L → ℕ)
    (marks : ∀g,Fin (cB g) → ℕ) (marks' : ∀g,Fin (cA g) → ℕ)
    (hmarks : marks∈b598RawSelectedGroupLists434 (sourceOriginalPAllActualBands r L) cB)
    (hmarks' : marks'∈b598RawSelectedGroupLists434 (sourceOriginalPAllActualBands r L) cA)
    (Y D : ℕ) (k : ℤ) (hk : k ≠ 0)
    (hlarge : ∀g p,p∈sourceOriginalPAllActualBands r L g → (2*k).natAbs < p)
    (hunitB : (∏g,∏i,marks g i).Coprime D)
    (hunitA : (∏g,∏i,marks' g i).Coprime D)
    (hsizeA : (∏g,∏i,marks' g i)^16 ≤ Y/(∏g,∏i,marks g i))
    (hsizeB : (∏g,∏i,marks g i)^16 ≤ Y/(∏g,∏i,marks' g i))
    (b b' : Fin (d+1)) (slot slot' : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (δ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → Bool)
    (ξ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → ℝ)
    (K K' : Finset ℕ) (a eta b0 : ℝ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (χ : DirichletCharacter ℂ k.natAbs) (σ₀ σ₁ σ₀' σ₁' : ℝ) :
    let P := sourceOriginalPAllActualBands r L
    let XB := ∏g,∏i,marks g i
    let XA := ∏g,∏i,marks' g i
    let F := sourceNativePrimeCore r d L b slot δ ξ K
      (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀ σ₁
    let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
      (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀' σ₁'
    (∑p∈b598ObservedPhysicalRows434 P cB cA marks marks' Y D k,
      ‖primeSlotCoreValue P F p.1 * star (primeSlotCoreValue P F' p.2)‖) ≤
      b595JointDivisorBudget Y XA XB := by
  let P := sourceOriginalPAllActualBands r L
  let XB := ∏g,∏i,marks g i
  let XA := ∏g,∏i,marks' g i
  let S := b598ObservedPhysicalRows434 P cB cA marks marks' Y D k
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀ σ₁
  let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
    (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀' σ₁'
  change (∑p∈S,‖primeSlotCoreValue P F p.1 * star (primeSlotCoreValue P F' p.2)‖) ≤ _
  have hprime := source_original_P_all_actual_band_prime r L
  have hdisj := source_original_P_actual_all_disjoint r L hr hL
  have hs := b598_observed_positive_shift_unit434 P cB hprime D k hk hlarge marks hmarks hunitB
  have ht := b598_observed_positive_shift_unit434 P cA hprime D k hk hlarge marks' hmarks' hunitA
  have hS : S ⊆ b595SelectedPhysicalPairs Y XA XB D k := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    have hrw := b598_mem_physical_rows434.mp hh.1
    have hB := b602_observed_tuple_ordinary_quotient434 P cB hprime hdisj
      p.1 hrw.1.1 marks hh.2.1
    have hA := b602_observed_tuple_ordinary_quotient434 P cA hprime hdisj
      p.2 hrw.2.1.1 marks' hh.2.2
    exact b595_mem_physical_pairs434.mpr ⟨hrw.1,hrw.2.1,hB.1,hA.1,hrw.2.2⟩
  by_cases hne : S.Nonempty
  · obtain ⟨p0,hp0⟩ := hne
    have hrow := b595_mem_physical_pairs434.mp (hS hp0)
    have htarget : (XA:ℤ)∣(p0.1:ℤ)+2*k*(D:ℤ) := by
      rw [←hrow.2.2.2.2]
      exact Int.natCast_dvd_natCast.mpr hrow.2.2.2.1
    have hunit := b587_actual_stripped_quotient_unit434 XA 1 D p0.1 k (one_dvd _) ht.2 htarget
    have hcop : XA.Coprime XB := Nat.Coprime.of_dvd_right hrow.2.2.1
      (by simpa only [Nat.div_one] using hunit)
    calc
      _ ≤ ∑p∈S,((p.1/XB).divisors.card:ℝ)^2*((p.2/XA).divisors.card:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hh := Finset.mem_filter.mp hp
        have hrw := b598_mem_physical_rows434.mp hh.1
        exact b602_literal_P_sigma_one_D61_two_observed_core_bound434
          r d L hr hL cB cA p.1 p.2 hrw.1.1 hrw.2.1.1 marks marks' hh.2.1 hh.2.2
          b b' slot slot' δ ξ δ' ξ' K K' a eta b0 hWy k.natAbs k.natAbs χ χ σ₀ σ₁ σ₀' σ₁'
      _ ≤ _ := b595_physical_joint_two_core_majorant434
        Y XA XB D k S hS ht.1 hs.1 hcop ht.2 hs.2 hsizeA hsizeB
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    exact joint_budget_nonneg Y XA XB
end Green64Analytic.ShiftTwoTerminal

end

end

