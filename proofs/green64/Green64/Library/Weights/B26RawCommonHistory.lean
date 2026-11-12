module

public import Green64.Library.Weights.B26RawCommonDivisor

@[expose] public section

/-!
# Weights / B26RawCommonHistory

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26RawCommonHistory -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Perm" => BigGroupPerm (BG := G) (J+ell)

/-- The numerical inventory of the complete active BIG endpoint. -/
def sourceOriginalB26RawInventory434 (a : A) : Finset ℕ :=
  (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) a).image
    (fun p : Sigma BP => p.2.val)

/-- The true numerical free-target birth set, with the target
permutation retained. The separate birth-list Nodup gate is unchanged. -/
def sourceOriginalB26RawBirth434 (nu : SourceOriginalProbePattern434 G m)
    (tau : Perm) (t : A) : Finset ℕ :=
  (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
    (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau t)).image
      (fun p : Sigma BP => p.2.val)

theorem source_original_B26_RAW_inventory_mem434 (a : A) (p : ℕ) :
    p ∈ sourceOriginalB26RawInventory434 P J ell a ↔
      ∃ g,∃ i : Fin (J+ell),(a g i).val=p := by
  constructor
  · intro hp
    obtain ⟨⟨g,v⟩,hv,hp⟩ := Finset.mem_image.mp hp
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (Finset.mem_sigma.mp hv).2
    exact ⟨g,i,(congrArg Subtype.val he).trans hp⟩
  · rintro ⟨g,i,he⟩
    exact Finset.mem_image.mpr ⟨⟨g,a g i⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩⟩,he⟩

theorem source_original_B26_RAW_birth_mem434
    (nu : SourceOriginalProbePattern434 G m) (tau : Perm) (t : A) (p : ℕ) :
    p ∈ sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t ↔
      ∃ g,∃ i : Fin (J+ell),
        i ∉ sourceOriginalProbeSharedSlots434 J ell m hmJ nu g ∧
        (t g (tau g i)).val=p := by
  constructor
  · intro hp
    obtain ⟨⟨g,v⟩,hv,hp⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (Finset.mem_sigma.mp hv).2
    let i := sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ nu g j
    refine ⟨g,i.val,?_,?_⟩
    · simpa only [source_original_probe_memory_shared_slots434] using i.property
    · exact (congrArg Subtype.val he).trans hp
  · rintro ⟨g,i,hi,he⟩
    have hi' : i ∉ sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) g := by
      simpa only [source_original_probe_memory_shared_slots434] using hi
    let j := (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ nu g).symm ⟨i,hi'⟩
    refine Finset.mem_image.mpr ⟨⟨g,t g (tau g i)⟩,?_,he⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
    change t g (tau g (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ nu g j).val) = t g (tau g i)
    simp only [j,Equiv.apply_symm_apply]

/-- The new physical seen set is independent of the probe pattern
on every live copy transition. No cap on the joint future is used. -/
theorem source_original_B26_RAW_common_seen434
    (nu : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ) (s t : A) (sigma tau : Perm)
    (S : Finset ℕ) (hS : sourceOriginalB26RawInventory434 P J ell s ⊆ S)
    (hLaw : sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau ≠ 0) :
    S ∪ sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t =
      S ∪ sourceOriginalB26RawInventory434 P J ell t := by
  ext p
  simp only [Finset.mem_union]
  constructor
  · rintro (hp | hp)
    · exact Or.inl hp
    · obtain ⟨g,i,hi,he⟩ :=
        (source_original_B26_RAW_birth_mem434 P J ell m hmJ nu tau t p).mp hp
      exact Or.inr ((source_original_B26_RAW_inventory_mem434 P J ell t p).mpr
        ⟨g,tau g i,he⟩)
  · rintro (hp | hp)
    · exact Or.inl hp
    · obtain ⟨g,i,he⟩ :=
        (source_original_B26_RAW_inventory_mem434 P J ell t p).mp hp
      let j := (tau g).symm i
      have hj : tau g j=i := Equiv.apply_symm_apply _ _
      by_cases hs : j ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ nu g
      · have hc := source_original_B26_RAW_shared_copy434 P J ell m hmJ nu
          mu s t sigma tau hLaw g j hs
        apply Or.inl
        apply hS
        apply (source_original_B26_RAW_inventory_mem434 P J ell s p).mpr
        exact ⟨g,sigma g j,(congrArg Subtype.val hc).symm.trans (by simpa only [hj] using he)⟩
      · apply Or.inr
        apply (source_original_B26_RAW_birth_mem434 P J ell m hmJ nu tau t p).mpr
        exact ⟨g,j,hs,by simpa only [hj] using he⟩

/-- Freshness makes the selected probes visible in the actual numerical
history, rather than in an independently sampled copy of the endpoint. -/
theorem source_original_B26_RAW_selected_iff_unseen434
    (nu : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ) (s t : A) (sigma tau : Perm)
    (S : Finset ℕ) (hS : sourceOriginalB26RawInventory434 P J ell s ⊆ S)
    (hLaw : sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau ≠ 0)
    (hFresh : Disjoint S (sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t))
    (g : G) (j : Fin m) :
    ((g,j) ∈ nu.1 ∨ (g,j) ∈ nu.2) ↔
      (t g (tau g ((j.castLE hmJ).castAdd ell))).val ∉ S := by
  constructor
  · intro hj hp
    have hb := (source_original_B26_RAW_birth_mem434 P J ell m hmJ nu tau t _).mpr
      ⟨g,(j.castLE hmJ).castAdd ell,
        source_original_probe_freed_membership434 J ell m hmJ nu g j hj,rfl⟩
    exact Finset.disjoint_left.mp hFresh hp hb
  · intro hj
    by_contra hn
    have hf : j.castLE hmJ ∉ sourceOriginalProbeFreedSlots434 J m hmJ nu g :=
      fun h => hn ((source_original_probe_freed_first_m_iff434 J m hmJ nu g j).mp h)
    have hs : (j.castLE hmJ).castAdd ell ∈
        sourceOriginalProbeSharedSlots434 J ell m hmJ nu g :=
      (source_original_shared_slot_mem434 J ell _ (j.castLE hmJ)).mpr hf
    have hc := source_original_B26_RAW_shared_copy434 P J ell m hmJ nu
      mu s t sigma tau hLaw g _ hs
    apply hj
    rw [hc]
    exact hS ((source_original_B26_RAW_inventory_mem434 P J ell s _).mpr
      ⟨g,sigma g ((j.castLE hmJ).castAdd ell),rfl⟩)

/-- At fixed actual endpoints and source history at most one disjoint
two-block pattern is live and fresh. This is support uniqueness,
not a signed arithmetic saving. -/
theorem source_original_B26_RAW_live_pattern_unique434
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (nu eta : SourceOriginalProbePattern434 G m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (heta : eta ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (mu : (g : G) → BP g → ℝ) (s t : A) (sigma tau : Perm)
    (S : Finset ℕ) (hS : sourceOriginalB26RawInventory434 P J ell s ⊆ S)
    (hn : sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau ≠ 0)
    (he : sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ eta) s t sigma tau ≠ 0)
    (hfn : Disjoint S (sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t))
    (hfe : Disjoint S (sourceOriginalB26RawBirth434 P J ell m hmJ eta tau t)) :
    nu=eta := by
  have hnM := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hnu
  have heM := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp heta
  have hu (g : G) (j : Fin m) :
      ((g,j) ∈ nu.1 ∨ (g,j) ∈ nu.2) ↔ ((g,j) ∈ eta.1 ∨ (g,j) ∈ eta.2) :=
    (source_original_B26_RAW_selected_iff_unseen434 P J ell m hmJ nu
      mu s t sigma tau S hS hn hfn g j).trans
    (source_original_B26_RAW_selected_iff_unseen434 P J ell m hmJ eta
      mu s t sigma tau S hS he hfe g j).symm
  apply Prod.ext
  · ext z
    constructor
    · intro hz
      rcases (hu z.1 z.2).mp (Or.inl hz) with hz' | hz'
      · exact hz'
      · exact False.elim (Finset.disjoint_left.mp hBlocks
          (Finset.mem_product.mp (hnM.2.1 hz)).1 (Finset.mem_product.mp (heM.2.2.2 hz')).1)
    · intro hz
      rcases (hu z.1 z.2).mpr (Or.inl hz) with hz' | hz'
      · exact hz'
      · exact False.elim (Finset.disjoint_left.mp hBlocks
          (Finset.mem_product.mp (heM.2.1 hz)).1 (Finset.mem_product.mp (hnM.2.2.2 hz')).1)
  · ext z
    constructor
    · intro hz
      rcases (hu z.1 z.2).mp (Or.inr hz) with hz' | hz'
      · exact False.elim (Finset.disjoint_left.mp hBlocks
          (Finset.mem_product.mp (heM.2.1 hz')).1 (Finset.mem_product.mp (hnM.2.2.2 hz)).1)
      · exact hz'
    · intro hz
      rcases (hu z.1 z.2).mpr (Or.inr hz) with hz' | hz'
      · exact False.elim (Finset.disjoint_left.mp hBlocks
          (Finset.mem_product.mp (hnM.2.1 hz')).1 (Finset.mem_product.mp (heM.2.2.2 hz)).1)
      · exact hz'

/-- The full RAW continuation, simultaneously in the true divisor and
numerical history, has a common argument for the whole probe family.
F may contain all genuine SMALL and OLD shifts and an arbitrary future. -/
theorem source_original_B26_RAW_common_continuation434
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (nu : SourceOriginalProbePattern434 G m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (dsmall : ℕ) (mu : (g : G) → BP g → ℝ)
    (s t : A) (sigma tau : Perm) (S : Finset ℕ)
    (hS : sourceOriginalB26RawInventory434 P J ell s ⊆ S)
    (F : ℕ → Finset ℕ → ℂ) :
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
      F (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall s t sigma tau)
        (S ∪ sourceOriginalB26RawBirth434 P J ell m hmJ nu tau t) =
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
      F (sourceOriginalB26RawCommonDivisor434 P blockA J ell dsmall s t sigma tau)
        (S ∪ sourceOriginalB26RawInventory434 P J ell t) := by
  by_cases hz : sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau = 0
  · simp only [hz,zero_mul]
  · rw [source_original_B26_RAW_common_divisor434 P blockA blockB hBlocks
      J ell m hmJ nu hnu dsmall mu s t sigma tau hz,
      source_original_B26_RAW_common_seen434 P J ell m hmJ nu
      mu s t sigma tau S hS hz]

end Green64Analytic.CorrelationSquare

end

end

