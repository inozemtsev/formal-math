module

public import Green64.Library.Correlation.Part023

@[expose] public section

/-!
# Correlation / MemoryB2WeightedRawJoint

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryB2WeightedRawJoint -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- A finite support comparison with no loss of zero-weight witnesses. -/
private theorem sum_eq_of_nz_membership_iff
    {α : Type*} [DecidableEq α] (s t : Finset α) (w : α → ℂ)
    (h : ∀ a, w a ≠ 0 → (a ∈ s ↔ a ∈ t)) :
    (∑ a ∈ s, w a) = ∑ a ∈ t, w a := by
  have hst : ∀ a ∈ s, a ∉ s ∩ t → w a = 0 := by
    intro a ha hnot
    by_contra hw
    exact hnot (Finset.mem_inter.mpr ⟨ha, (h a hw).mp ha⟩)
  have hts : ∀ a ∈ t, a ∉ s ∩ t → w a = 0 := by
    intro a ha hnot
    by_contra hw
    exact hnot (Finset.mem_inter.mpr ⟨(h a hw).mpr ha,ha⟩)
  calc
    (∑ a ∈ s, w a) = ∑ a ∈ s ∩ t, w a :=
      (Finset.sum_subset Finset.inter_subset_left hst).symm
    _ = ∑ a ∈ t, w a :=
      Finset.sum_subset Finset.inter_subset_right hts

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 800000

/-- ACTUAL source-specific weighted support equality, comparing the full
fourfold nested fibre (as a raw dependent indexed sigma set) with the
TRUE chronological G/E legal carrier. The result includes every zero-G
and zero-E branch with its full original complex coefficient. -/
theorem memory_source_nested_weight_eq_original_raw_joint
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0)
    (i : Fin (2*R)) :
    (let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn);
    let G := physicalOrientedGEIndexedCarrier SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val);
    let T := G.filter (fun ab =>
      (ab.1.2.1,ab.1.2.2) ∈ memoryPrimitiveGFixedInputFibre
        SP smallMod BP bigMod J ell cap
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val ab.1.1 ∧
      ab.2.2 ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod
        J ell m cap patterns
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val ab.2.1
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k hs i.succ)
        (physicalAlternatingSign i.val) k (ω.2.2 i));
    let W := physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho (2*R) i.val Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hd.cap_saturated true i.castSucc));
    (∑ ab ∈ memorySourceNestedCanonicalGECarrier SP smallMod BP bigMod
      J ell m cap patterns k R hd.cap_saturated ω life hs i, W ab) =
      ∑ ab ∈ T, W ab) := by
  dsimp only
  apply sum_eq_of_nz_membership_iff
  intro ab hw
  have hgnz : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) i.val Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      ab.1.1 ab.1.2.1 ab.1.2.2 ≠ 0 := by
    intro hg0
    apply hw
    unfold physicalOrientedGEIndexedWeight
    rw [hg0]
    ring
  exact memory_source_nested_iff_original_joint_nonzero
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R hd ω life
    (memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn))
    (left_ne_zero_of_mul hn) i ab hgnz
end Green64FullPhysicalE

end

end

