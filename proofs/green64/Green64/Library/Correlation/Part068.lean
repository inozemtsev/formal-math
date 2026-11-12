module

public import Green64.Library.Analysis.Estimates.FullBanHarmonicEnvelope
public import Green64.Library.Weights.ObservedD61JointMoment
public import Green64.Library.Weights.PShiftRange
public import Green64.Library.Analysis.Estimates.Part011

@[expose] public section

/-!
# Correlation / Part068

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ObservedPhysicalFubini -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- Exact finite Fubini on the actual divisor-mark carriers. Independent
raw prime draws are used only as a containing carrier; the physical
restrictions remain in the inner observed-row sum. -/
theorem b598_actual_observed_physical_fubini434
    (P : G → Finset ℕ) (cB cA : G → ℕ) (Y D : ℕ) (k : ℤ)
    (f : ℕ×ℕ → ℝ)
    (W : (∀g,Fin (cB g) → ℕ) → (∀g,Fin (cA g) → ℕ) → ℝ) :
    (∑p∈b598PhysicalRows434 Y D k,f p *
      ∑a∈bigMarkLists P cB p.1,∑b∈bigMarkLists P cA p.2,W a b) =
    ∑a∈b598RawSelectedGroupLists434 P cB,
      ∑b∈b598RawSelectedGroupLists434 P cA,W a b *
        ∑p∈b598ObservedPhysicalRows434 P cB cA a b Y D k,f p := by
  have heq (c : G → ℕ) (n : ℕ) :
      bigMarkLists P c n=(b598RawSelectedGroupLists434 P c).filter
        (fun a => a∈bigMarkLists P c n) := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · intro ha
      exact ⟨b598_actual_selected_lists_subset_raw434 P c n ha,ha⟩
    · exact fun ha => ha.2
  have hrow (p : ℕ×ℕ) :
      (∑a∈bigMarkLists P cB p.1,∑b∈bigMarkLists P cA p.2,W a b) =
      ∑a∈b598RawSelectedGroupLists434 P cB,
        ∑b∈b598RawSelectedGroupLists434 P cA,
          if a∈bigMarkLists P cB p.1 ∧ b∈bigMarkLists P cA p.2 then W a b else 0 := by
    conv_lhs => rw [heq cB p.1,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ham : a∈bigMarkLists P cB p.1
    · rw [ite_eq_left ham]
      conv_lhs => rw [heq cA p.2,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [ham,true_and]
    · simp only [ham,false_and,ite_false,Finset.sum_const_zero]
  calc
    _ = ∑p∈b598PhysicalRows434 Y D k,
      ∑a∈b598RawSelectedGroupLists434 P cB,
        ∑b∈b598RawSelectedGroupLists434 P cA,
          if a∈bigMarkLists P cB p.1 ∧ b∈bigMarkLists P cA p.2 then f p*W a b else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hrow]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs <;> simp
    _ = ∑a∈b598RawSelectedGroupLists434 P cB,
      ∑b∈b598RawSelectedGroupLists434 P cA,
        ∑p∈b598PhysicalRows434 Y D k,
          if a∈bigMarkLists P cB p.1 ∧ b∈bigMarkLists P cA p.2 then W a b*f p else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp [mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [b598ObservedPhysicalRows434,Finset.sum_filter,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## LiteralFixedAuxiliaryEnvelope -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Literal original fixed-auxiliary Knu envelope with both actual D61
cores and every hidden mark summed. Actual P harmonic masses, all smooth
signed k, modulus |k|, full Delta, both independent sorted-Q arrays and
all coefficient masks remain present. The original full ban supplies
selected units before hidden slots are bounded. No clean-endpoint,
selected-size, mass-floor, core-norm, kernel-norm or moment premise is
assumed. This is an absolute joint budget; it is not signed RMS saving. -/
theorem eventually_b598_literal_fixed_auxiliary_D61_envelope434
    (r m : ℕ) (hr : 1 ≤ r) (K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J : ℕ) (hmJ : m ≤ J)
        (blockA blockB : Finset (sourceOriginalPAllGroupType r L))
        (_hblocks : Disjoint blockA blockB)
        (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m),
      nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m →
      ∀ (Q : ℕ) (hA hB xi : ℝ),0 < hA → 0 < hB → 0 < xi →
      ∀ (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
      aux∈Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu (sourceOriginalPAllActualBands r L)) →
      ∀ (Y : ℝ),Real.exp (L/2) ≤ Y →
      ∀ k∈sourceCorrectedSmoothKSet (L^K0) (L^(89:ℝ)),
      ∀ (d : ℕ) (b b' : Fin (d+1)) (slot slot' : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (δ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → Bool)
        (ξ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → ℝ)
        (K K' : Finset ℕ) (a eta b0 : ℝ),
      Real.exp (Real.sqrt L) ≤ (Real.exp L)^a →
      ∀ (χ : DirichletCharacter ℂ k.natAbs) (σ₀ σ₁ σ₀' σ₁' : ℝ),
      let P := sourceOriginalPAllActualBands r L
      let V := sourceNativeOriginalAllPMass434 r L
      let D := sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux
      let N := ⌊Y⌋₊
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀ σ₁
      let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
        (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀' σ₁'
      (∑p∈b598PhysicalRows434 N D k,
        ‖primeSlotCoreValue P F p.1 * star (primeSlotCoreValue P F' p.2)‖ *
        ‖sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) p.1 p.2‖) ≤
      32*C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*(Q:ℝ)^4*(N:ℝ)*
        (1+Real.log (N:ℝ))^15 := by
  let vmin : ℝ := Real.log (6/5:ℝ)/2
  have hv : 0 < vmin := source_actual_P_uniform_mass_floor_positive
  obtain ⟨C,hC,henvelope⟩ := b598_actual_full_ban_harmonic_envelope434 vmin m hv
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_b598_observed_moment_range434 r m hr,
    eventually_native_original_ALL_P_masses434 r,
    eventually_b596_original_P_exceeds_all_shifts434 r K0 hK0,
    eventually_gt_atTop (0:ℝ)] with L hrange hmass hshift hL
  intro J hmJ blockA blockB hblocks nu hnu Q hA hB xi hhA hhB hxi aux haux Y hY
    k hk d b b' slot slot' δ ξ δ' ξ' K K' a eta b0 hWy χ σ₀ σ₁ σ₀' σ₁'
  let P := sourceOriginalPAllActualBands r L
  let V := sourceNativeOriginalAllPMass434 r L
  let D := sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux
  let N := ⌊Y⌋₊
  let cB := sourceOriginalProbeChosenGroupCount434 m nu.2
  let cA := sourceOriginalProbeChosenGroupCount434 m nu.1
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀ σ₁
  let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
    (sourceNativeB563OriginalD61Alpha434 a eta b0 L) k.natAbs χ σ₀' σ₁'
  let core := fun p : ℕ×ℕ => ‖primeSlotCoreValue P F p.1 * star (primeSlotCoreValue P F' p.2)‖
  let W := fun (aa : ∀g,Fin (cB g) → ℕ) (bb : ∀g,Fin (cA g) → ℕ) =>
    b579SelectedHarmonicMass cB V aa*b579SelectedHarmonicMass cA V bb *
      ((∏g,∏i,aa g i:ℕ):ℝ)*((∏g,∏i,bb g i:ℕ):ℝ)*
      b598RetainedObservedKnu434 m nu Q hA hB xi P V aux D aa bb
  let H : ℝ := 32*(N:ℝ)*(1+Real.log (N:ℝ))^15
  have hV (g : sourceOriginalPAllGroupType r L) : vmin ≤ V g := (hmass g).1
  have hVp (g : sourceOriginalPAllGroupType r L) : 0 < V g := hv.trans_le (hV g)
  have hdisj := source_original_P_actual_all_disjoint r L hr hL
  have hprime := source_original_P_all_actual_band_prime r L
  have hnuDisj := b598_actual_probe_blocks_disjoint434 blockA blockB hblocks m nu hnu
  have hcA (g : sourceOriginalPAllGroupType r L) : cA g ≤ m :=
    source_original_probe_chosen_group_count_le434 m nu.1 g
  have hcB (g : sourceOriginalPAllGroupType r L) : cB g ≤ m :=
    source_original_probe_chosen_group_count_le434 m nu.2 g
  have hN : 0 < N := by
    have he : (1:ℝ) ≤ Real.exp (L/2) := Real.one_le_exp (by linarith)
    have hh : (1:ℕ) ≤ N := Nat.le_floor (by simpa using he.trans hY)
    omega
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ 1+Real.log (N:ℝ) := by linarith [Real.log_nonneg hN1]
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hCpow : 0 ≤ C^(2*Fintype.card (sourceOriginalPAllGroupType r L)) :=
    pow_nonneg (by linarith) _
  have hmu {c : sourceOriginalPAllGroupType r L → ℕ} (aa : ∀g,Fin (c g) → ℕ) :
      0 ≤ b579SelectedHarmonicMass c V aa :=
    b598_selected_harmonic_nonneg434 c V (fun g => (hVp g).le) aa
  have hterm (aa : ∀g,Fin (cB g) → ℕ) (haa : aa∈b598RawSelectedGroupLists434 P cB)
      (bb : ∀g,Fin (cA g) → ℕ) (hbb : bb∈b598RawSelectedGroupLists434 P cA) :
      W aa bb*(∑p∈b598ObservedPhysicalRows434 P cB cA aa bb N D k,core p) ≤
      H*(b579SelectedHarmonicMass cB V aa*b579SelectedHarmonicMass cA V bb *
        ‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux aa bb‖) := by
    let XB := ∏g,∏i,aa g i
    let XA := ∏g,∏i,bb g i
    have hsize := hrange cA cB hcA hcB aa bb haa hbb Y hY
    have hXAr : 0 < (XA:ℝ) := by exact_mod_cast hsize.1
    have hXBr : 0 < (XB:ℝ) := by exact_mod_cast hsize.2.1
    by_cases hu : XB.Coprime D ∧ XA.Coprime D
    · have hret : b598RetainedObservedKnu434 m nu Q hA hB xi P V aux D aa bb =
          ‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux aa bb‖ := by
        unfold b598RetainedObservedKnu434
        exact ite_eq_left hu
      have hW : 0 ≤ W aa bb := by
        dsimp only [W]
        rw [hret]
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hmu aa) (hmu bb))
          (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (norm_nonneg _)
      have hm := b598_literal_observed_D61_joint_moment434 r d L hr hL cB cA aa bb haa hbb
        N D k (hshift.2 k hk).1 (hshift.2 k hk).2 hu.1 hu.2 hsize.2.2.1 hsize.2.2.2
        b b' slot slot' δ ξ δ' ξ' K K' a eta b0 hWy χ σ₀ σ₁ σ₀' σ₁'
      calc
        _ ≤ W aa bb*b595JointDivisorBudget N XA XB := mul_le_mul_of_nonneg_left hm hW
        _ = _ := by
          dsimp only [W,b595JointDivisorBudget,H]
          rw [hret]
          change b579SelectedHarmonicMass cB V aa*b579SelectedHarmonicMass cA V bb *
              (XB:ℝ)*(XA:ℝ)*‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux aa bb‖ *
              (32*((N:ℝ)/((XA:ℝ)*(XB:ℝ)))*(1+Real.log (N:ℝ))^15) = _
          field_simp [hXAr.ne',hXBr.ne']
    · have hret : b598RetainedObservedKnu434 m nu Q hA hB xi P V aux D aa bb=0 := by
        unfold b598RetainedObservedKnu434
        exact ite_eq_right hu
      dsimp only [W]
      rw [hret,mul_zero,zero_mul]
      exact mul_nonneg hH (mul_nonneg (mul_nonneg (hmu aa) (hmu bb)) (norm_nonneg _))
  have hmassBound :
      (∑aa∈b598RawSelectedGroupLists434 P cB,∑bb∈b598RawSelectedGroupLists434 P cA,
        W aa bb*(∑p∈b598ObservedPhysicalRows434 P cB cA aa bb N D k,core p)) ≤ H*(Q:ℝ)^4 := by
    calc
      _ ≤ ∑aa∈b598RawSelectedGroupLists434 P cB,∑bb∈b598RawSelectedGroupLists434 P cA,
          H*(b579SelectedHarmonicMass cB V aa*b579SelectedHarmonicMass cA V bb *
            ‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux aa bb‖) :=
        Finset.sum_le_sum (fun aa haa => Finset.sum_le_sum (fun bb hbb => hterm aa haa bb hbb))
      _ = H*b598GroupedCanonicalHarmonicMass434 m nu Q hA hB xi P V aux := by
        unfold b598GroupedCanonicalHarmonicMass434
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro aa haa
        apply Finset.sum_congr rfl
        intro bb hbb
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (b598_grouped_canonical_harmonic_l1_434 m nu Q hA hB xi P V hVp hhA hhB hxi aux) hH
  have hfubini := b598_actual_observed_physical_fubini434 P cB cA N D k core W
  change (∑p∈b598PhysicalRows434 N D k,core p*
      b598RetainedObservedHarmonicMass434 m nu Q hA hB xi P V aux D p.1 p.2) = _ at hfubini
  change (∑p∈b598PhysicalRows434 N D k,core p*
      ‖sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) p.1 p.2‖) ≤ _
  calc
    _ ≤ ∑p∈b598PhysicalRows434 N D k,core p*
        (C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*
          b598RetainedObservedHarmonicMass434 m nu Q hA hB xi P V aux D p.1 p.2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (henvelope J hmJ nu hnuDisj Q hA hB xi P V hprime hdisj hV aux haux D rfl p.1 p.2)
        (norm_nonneg _)
    _ = C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*
        (∑p∈b598PhysicalRows434 N D k,core p*
          b598RetainedObservedHarmonicMass434 m nu Q hA hB xi P V aux D p.1 p.2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p hp => by ring)
    _ ≤ C^(2*Fintype.card (sourceOriginalPAllGroupType r L))*(H*(Q:ℝ)^4) := by
      rw [hfubini]
      exact mul_le_mul_of_nonneg_left hmassBound hCpow
    _ = _ := by dsimp only [H]; ring
end Green64Analytic.ShiftTwoTerminal

end

end

