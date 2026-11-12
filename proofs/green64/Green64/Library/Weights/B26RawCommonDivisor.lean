module

public import Green64.Library.Correlation.Part057

@[expose] public section

/-!
# Weights / B26RawCommonDivisor

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26RawCommonDivisor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The mixed endpoint divisor: target first-J labels in block A,
source first-J labels elsewhere. It has no probe-pattern argument. -/
def sourceOriginalB26RawCommonDivisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (blockA : Finset G) (J ell : ℕ) (dsmall : ℕ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) : ℕ :=
  dsmall * ∏ g : G, ∏ i : Fin J,
    if g ∈ blockA then (t g (tau g (i.castAdd ell))).val
    else (s g (sigma g (i.castAdd ell))).val

/-- Nonzero actual fresh law forces the original shared-copy equalities,
with both independently permuted endpoints retained. -/
theorem source_original_B26_RAW_shared_copy434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (hLaw : sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
      J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau ≠ 0)
    (g : G) (i : Fin (J+ell))
    (hi : i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ nu g) :
    t g (tau g i) = s g (sigma g i) := by
  unfold sourceOriginalB26FrozenFreshLaw434 at hLaw
  have hg := (Finset.prod_ne_zero_iff.mp hLaw) g (Finset.mem_univ g)
  have hj := (Finset.prod_ne_zero_iff.mp hg) (tau g i) (Finset.mem_univ _)
  rw [Equiv.symm_apply_apply,source_original_probe_memory_shared_slots434,if_pos hi] at hj
  by_contra hn
  simp [hn] at hj

private theorem actual_free_probe
    {G : Type} [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (a : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g})
    (g : G) (j : Fin m) (hj : (g,j) ∈ nu.1 ∨ (g,j) ∈ nu.2) :
    sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu a g
      (sourceOriginalProbeFreeIndex434 J ell m hmJ nu g j hj) =
      (a g ((j.castLE hmJ).castAdd ell)).val := by
  unfold sourceOriginalProbeMemoryFreeValues434 sourceOriginalProbeMemoryFreeEquiv434
    sourceOriginalProbeFreeIndex434
  simp only [Equiv.trans_apply,Equiv.subtypeEquivRight_apply,Equiv.apply_symm_apply]

/-- On every live two-block RAW transition, the full original divisor
is the same mixed endpoint product. This includes all shared SMALL
factors and does not identify any auxiliary divisor with RAW. -/
theorem source_original_B26_RAW_common_divisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (blockA blockB : Finset G)
    (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (dsmall : ℕ) (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (hLaw : sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
      J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau ≠ 0) :
    sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall s t sigma tau =
      sourceOriginalB26RawCommonDivisor434 P blockA J ell dsmall s t sigma tau := by
  classical
  have hm := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hnu
  have hA (z : nu.1) : z.val.1 ∈ blockA :=
    (Finset.mem_product.mp (hm.2.1 z.property)).1
  have hB (z : nu.2) : z.val.1 ∉ blockA := by
    intro hz
    exact Finset.disjoint_left.mp hBlocks hz
      (Finset.mem_product.mp (hm.2.2.2 z.property)).1
  have hDisj := source_original_probe_memory_actual_pattern_disjoint434
    blockA blockB hBlocks m nu hnu
  let W := fun (g : G) (i : Fin (J+ell)) =>
    if g ∈ blockA then (t g (tau g i)).val else (s g (sigma g i)).val
  have hfree :
      (∏ g : G,∏ j : sourceOriginalProbeFreedSlots434 J m hmJ nu g,
        W g (j.val.castAdd ell)) =
      sourceOriginalProbeFreeTargetX434 J ell m hmJ nu
        (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu
          (fun g i => t g (tau g i))) *
      sourceOriginalProbeFreeSourceX434 J ell m hmJ nu
        (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu
          (fun g i => s g (sigma g i))) := by
    rw [source_original_probe_memory_aux_product_transfer434 J m hmJ nu hDisj
      (fun z => W z.1 (z.2.val.castAdd ell))]
    congr 1
    · unfold sourceOriginalProbeFreeTargetX434
      apply Finset.prod_congr rfl
      intro z hz
      dsimp only [sourceOriginalProbeMemoryAuxSlot434]
      rw [actual_free_probe]
      exact if_pos (hA z)
    · unfold sourceOriginalProbeFreeSourceX434
      apply Finset.prod_congr rfl
      intro z hz
      dsimp only [sourceOriginalProbeMemoryAuxSlot434]
      rw [actual_free_probe]
      exact if_neg (hB z)
  unfold sourceOriginalB26CanonicalRawDivisor434 sourceOriginalB26CanonicalSharedDivisor434
    sourceOriginalB26RawCommonDivisor434
  rw [←hfree,mul_assoc,←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro g hg
  have hs :
      (∏ i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ nu g,
        (s g (sigma g i)).val) =
      ∏ j ∈ (Finset.univ \ sourceOriginalProbeFreedSlots434 J m hmJ nu g),
        W g (j.castAdd ell) := by
    unfold sourceOriginalProbeSharedSlots434 sourceOriginalSharedSlots434
    rw [Finset.prod_image (by
      intro i hi j hj hij
      exact Fin.ext (congrArg (fun z : Fin (J+ell) => z.val) hij))]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hga : g ∈ blockA
    · have hj' : j.castAdd ell ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ nu g :=
        (source_original_shared_slot_mem434 J ell _ j).mpr (Finset.mem_sdiff.mp hj).2
      have hc := source_original_B26_RAW_shared_copy434 P J ell m hmJ nu
        mu s t sigma tau hLaw g (j.castAdd ell) hj'
      exact (congrArg Subtype.val hc).symm.trans (if_pos hga).symm
    · exact (if_neg hga).symm
  rw [hs,Finset.prod_coe_sort (sourceOriginalProbeFreedSlots434 J m hmJ nu g)
    (fun j : Fin J => W g (j.castAdd ell))]
  exact Finset.prod_sdiff (Finset.subset_univ _)

/-- The common-divisor replacement holds after multiplication by the
actual law, even at dead transitions. F can contain the complete
Fourier/Mellin phase and every true SMALL/OLD residue translation. -/
theorem source_original_B26_RAW_common_divisor_weighted434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (blockA blockB : Finset G)
    (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (dsmall : ℕ) (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (s t : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) (F : ℕ → ℂ) :
    sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
      J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
      F (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall s t sigma tau) =
    sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
      J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
      F (sourceOriginalB26RawCommonDivisor434 P blockA J ell dsmall s t sigma tau) := by
  by_cases hz : sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
      J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau = 0
  · simp only [hz,zero_mul]
  · rw [source_original_B26_RAW_common_divisor434 P blockA blockB hBlocks
      J ell m hmJ nu hnu dsmall mu s t sigma tau hz]

end Green64Analytic.CorrelationSquare

end

end

