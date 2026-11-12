module

public import Green64.Library.Correlation.MemoryB2WeightedRawJoint
public import Green64.Library.Correlation.Part012

@[expose] public section

/-!
# Correlation / Part024

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryB2SubtypeFubini -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Rewrite the ORIGINAL legal indexed GE subtype into its raw
dependent source G/E sigma carrier, preserving every index once. -/
theorem source_subtype_filter_sum
    {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] (w : α → ℂ) :
    (∑ a ∈ (Finset.univ : Finset (↥s)).filter (fun a => p a.val), w a.val) =
    ∑ a ∈ s.filter p, w a := by
  rw [Finset.sum_filter, Finset.sum_filter]
  simpa only [Finset.attach_eq_univ] using
    (Finset.sum_attach s (fun a => if p a then w a else 0))
end Green64FullPhysicalE

end

end

/-! ## MemoryB2HeadNestedExact -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 800000

/-- The source-correct original fitting head, with both truly conditional
Hilbert orbit measures and original numerical seen, has precisely the raw
nested G/E support and weight. This is the missing source subtype bridge. -/
theorem memory_source_fitting_head_eq_original_nested_GE_weight
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
    let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
        J ell m cap patterns ω life k hd.cap_saturated true i.castSucc)
    memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod
      J ell m cap patterns ω life hd.cap_saturated q rho Vsmall Vbig
      mu Knu zeta theta k i =
    ∑ ab ∈ memorySourceNestedCanonicalGECarrier SP smallMod BP bigMod
      J ell m cap patterns k R hd.cap_saturated ω life hs i,
      physicalOrientedGEIndexedWeight SP smallMod BP bigMod J ell m cap patterns
        q rho (2*R) i.val Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k y ab := by
  dsimp only
  rw [memory_source_actual_fitting_head_mass_eq_original_joint_GE_sum
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn i]
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
      J ell m cap patterns ω life k hd.cap_saturated true i.castSucc)
  let S := physicalOrientedGEIndexedCarrier SP smallMod BP bigMod
    J ell m cap patterns (physicalAlternatingSign i.val) k y
    (memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) i.val)
  let P := fun (ab : Σ g : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod
        J ell cap, PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
          J ell m cap patterns) =>
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
      (physicalAlternatingSign i.val) k (ω.2.2 i)
  let W := physicalOrientedGEIndexedWeight SP smallMod BP bigMod
    J ell m cap patterns q rho (2*R) i.val Vsmall Vbig mu
    (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
    zeta theta (physicalAlternatingSign i.val) k y
  change (∑ ab ∈ (Finset.univ : Finset (↥S)).filter
      (fun ab => P ab.val), W ab.val) =
    ∑ ab ∈ memorySourceNestedCanonicalGECarrier SP smallMod BP bigMod
      J ell m cap patterns k R hd.cap_saturated ω life hs i, W ab
  rw [source_subtype_filter_sum S P W]
  exact (memory_source_nested_weight_eq_original_raw_joint
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn i).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryB2DependentFourfold -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 500000

/-- Dependent Fubini for the ACTUAL source witness shape:
G input x, conditional G output/ghost witness, E input,
conditional E oriented choice. No symmetric quotient or identification. -/
theorem source_dependent_fourfold_weighted_fubini
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {C : X → Type*} [∀ x, Fintype (C x)]
    {D : Z → Type*} [∀ z, Fintype (D z)]
    (p : X → Prop)
    (q : (x : X) → (Σ _ : Y, C x) → Prop)
    (r : Y → Z → Prop)
    (s : (z : Z) → D z → Prop)
    (w : (Σ g : (Σ x : X, Σ _ : Y, C x), Σ z : Z, D z) → ℂ) :
    (∑ ab : Σ g : (Σ x : X, Σ _ : Y, C x), Σ z : Z, D z,
      if p ab.1.1 ∧ q ab.1.1 ab.1.2 ∧
          r ab.1.2.1 ab.2.1 ∧ s ab.2.1 ab.2.2
      then w ab else 0) =
    ∑ x ∈ (Finset.univ : Finset X).filter p,
      ∑ yc ∈ (Finset.univ : Finset (Y × C x)).filter (fun yc => q x ⟨yc.1,yc.2⟩),
        ∑ z ∈ (Finset.univ : Finset Z).filter (r yc.1),
          ∑ c ∈ (Finset.univ : Finset (D z)).filter (s z),
            w ⟨⟨x,⟨yc.1,yc.2⟩⟩,⟨z,c⟩⟩ := by
  classical
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : p x
  · simp only [hp, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro yc _
    by_cases hq : q x ⟨y,yc⟩
    · simp only [hq, true_and, ite_true]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hr : r y z
      · simp [hr]
      · simp [hr]
    · simp [hq]
  · simp [hp]
end Green64FullPhysicalE

end

end

/-! ## MemoryB2NestedFourfoldSource -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 600000

theorem memory_source_nested_GE_eq_original_fourfold_sum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))

    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin (2*R)) :
    (let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩;
     let L := fun g p => life ⟨g,p⟩;
     let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k;
     let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
       ω life k hs i.succ;
     let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig;
     let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
       (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
         J ell m cap patterns ω life k hd.cap_saturated true i.castSucc);
     let W := physicalOrientedGEIndexedWeight SP smallMod BP bigMod
       J ell m cap patterns q rho (2*R) i.val Vsmall Vbig mu
       (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
       zeta theta (physicalAlternatingSign i.val) k y;
     (∑ ab ∈ memorySourceNestedCanonicalGECarrier SP smallMod BP bigMod
       J ell m cap patterns k R hd.cap_saturated ω life hs i, W ab) =

     ∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod
         (J+ell) cap)).filter (fun x =>
         physicalFockProjection SP smallMod BP bigMod (J+ell) cap x = y),
       ∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod
           J ell cap A L offset i.val x,
         ∑ xe ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod
           (J+ell) cap)).filter (fun xe =>
           physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
             physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1),
           ∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod
             J ell m cap patterns A L offset i.val xe iy
             (physicalAlternatingSign i.val) k (ω.2.2 i),
             W ⟨⟨x,yc.1,yc.2⟩,⟨xe,z⟩⟩) := by
  dsimp only
  unfold memorySourceNestedCanonicalGECarrier
  rw [Finset.sum_filter]
  convert source_dependent_fourfold_weighted_fubini
    (p := fun x => physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hd.cap_saturated true i.castSucc))

    (q := fun x yc => (yc.1, yc.2) ∈ memoryPrimitiveGFixedInputFibre
      SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val x)
    (r := fun yg xe => physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap yg)
    (s := fun xe z => z ∈ memoryPrimitiveEFixedFrameFibre
      SP smallMod BP bigMod J ell m cap patterns
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val xe
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.succ)
      (physicalAlternatingSign i.val) k (ω.2.2 i))
    (w := physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho (2*R) i.val Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k

      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hd.cap_saturated true i.castSucc))) using 1
  · apply Fintype.sum_congr
    intro ab
    split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr
    · ext yc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro yc _
      apply Finset.sum_congr rfl
      intro xe _
      apply Finset.sum_congr
      · ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro z _
        rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryB2HeadGEProduct -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 800000

/-- The source original weighted head equals the complete literal ordered
G/E primitive product, with actual conditional orbit measures and
chronological source register, under unchanged frozen nonzero coefficient. -/
theorem memory_source_fitting_head_eq_original_primitive_GE_product
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
    let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.castSucc
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.succ
    memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod
      J ell m cap patterns ω life hd.cap_saturated q rho Vsmall Vbig
      mu Knu zeta theta k i =
    memoryPrimitiveGUnorderedCoefficient BP bigMod A L offset i.val q rho (2*R) Vbig mu *
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val ix iy q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i) := by
  have hhead := memory_source_fitting_head_eq_original_nested_GE_weight
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn i
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
  have hfour := memory_source_nested_GE_eq_original_fourfold_sum
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hs i
  have hcoeff := memory_frozen_source_actual_GE_indexed_weight_sum
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hs (left_ne_zero_of_mul hn) i
  dsimp only at hhead hfour hcoeff ⊢
  exact hhead.trans (hfour.trans hcoeff)
end Green64FullPhysicalE

end

end

/-! ## MemoryB2GlobalPrimitiveProduct -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 500000

/-- The COMPLETE original indexed source root fibre is exactly its genuine
original initial Hilbert mass, the full product of ORIGINAL conditional
indexed-G/E fitting head sums, and the FINAL ORIGINAL terminal G_N sum.
No new equality to the frozen RHS is assumed: that precise coefficient
evaluation remains B1's nontrivial local obligation. -/
theorem memory_source_nonzero_root_fibre_exact_original_primitive_GE_product
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
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
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
    (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩) : ℂ) *
    (∏ i : Fin (2*R),
      memoryPrimitiveGUnorderedCoefficient BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) *
      memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k (memory_frozen_source_profile_support SP smallMod BP bigMod
            J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)) i.castSucc)
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k (memory_frozen_source_profile_support SP smallMod BP bigMod
            J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)) i.succ)
        q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)) *
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hd.cap_saturated q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k ⟨2*R,Nat.lt_succ_self (2*R)⟩ := by
  have hroot := memory_source_nonzero_root_fibre_exact_GE_product
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  rw [hroot]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact memory_source_fitting_head_eq_original_primitive_GE_product
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn i
end Green64FullPhysicalE

end

end

/-! ## MemoryB2TerminalOriginalSlice -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 550000

/-- Actual final source G_N indexed weighted fibre, including the
true chronological seen at N, full original Hilbert conditional input
mass and original terminal vacuum. The filter uses original projected
post-G output, not an arbitrary proxy for terminal normalization. -/
theorem memory_source_actual_terminal_G_N_raw_slice
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1)) :

    (let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig;
     let x := memoryFrozenSourcePhysicalState SP smallMod BP bigMod
       J ell m cap patterns ω life k hd.cap_saturated true
         ⟨2*R,Nat.lt_succ_self (2*R)⟩;
     let z := memoryFrozenSourcePhysicalState SP smallMod BP bigMod
       J ell m cap patterns ω life k hd.cap_saturated false
         ⟨2*R,Nat.lt_succ_self (2*R)⟩;
     let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap x;
     let t := physicalFockProjection SP smallMod BP bigMod (J+ell) cap z;
     let seen := memorySeenBeforeGValues BP bigMod
       (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
       (fun g p => life ⟨g,p⟩) (2*R);
     memorySourceCanonicalFittingTail SP smallMod BP bigMod
       J ell m cap patterns ω life hd.cap_saturated q rho Vsmall Vbig mu
       Knu zeta theta k ⟨2*R,Nat.lt_succ_self (2*R)⟩ =
       ∑ a ∈ (physicalGIndexedEligibleFibre SP smallMod BP bigMod
         J ell cap y seen).filter (fun a =>
           physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1 = t),
         physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
           J ell cap q rho Vsmall Vbig mu (2*R) (2*R) y a) := by
  dsimp only
  unfold memorySourceCanonicalFittingTail
  simp only [Nat.sub_self]
  change memorySourceFittingTraceSum SP smallMod BP bigMod J ell m cap patterns
    ω life hd.cap_saturated q rho Vsmall Vbig
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    Knu zeta theta k 0 (2*R)
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
        J ell m cap patterns ω life k hd.cap_saturated true
          ⟨2*R,Nat.lt_succ_self (2*R)⟩))
    (memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) (2*R)) = _

  letI := physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
    J ell m cap patterns 1 k 0 (2*R)
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨2*R,Nat.lt_succ_self (2*R)⟩))
    (memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) (2*R))
  unfold memorySourceFittingTraceSum
  dsimp only [memoryFrozenSourceIndexedTraceFits, memorySourceIndexedTraceWeight]
  simp only [eq_self_iff_true, true_and]
  -- Indexed terminal subtype is the original physical G_N fibre, not a
  -- replacement carrier. This is the exact source-specific subtype identity.
  have h := source_subtype_filter_sum
    (physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
          patterns ω life k hd.cap_saturated true ⟨2*R,Nat.lt_succ_self (2*R)⟩))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (2*R)))
    (fun a => physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
          patterns ω life k hd.cap_saturated false ⟨2*R,Nat.lt_succ_self (2*R)⟩))
    (physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
      J ell cap q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (2*R) (2*R)
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
          patterns ω life k hd.cap_saturated true ⟨2*R,Nat.lt_succ_self (2*R)⟩)))
  rw [Finset.sum_filter] at h
  convert h using 1
  apply Fintype.sum_congr
  intro a
  split_ifs <;> simp_all
end Green64FullPhysicalE

end

end

/-! ## MemoryB2TerminalVacuumExact -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The original terminal vacuum is exactly one on every actual
indexed final G branch whose projected output matches the genuine
frozen terminal state; no substitute vacuum is postulated. -/
theorem memory_source_final_frozen_output_vacuum
    (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (a : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod J ell cap)

    (h : physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap false
          ⟨2*R,Nat.lt_succ_self (2*R)⟩)) :
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1) = 1 := by
  rw [h]
  apply if_pos
  intro g
  exact (memory_frozen_source_physical_vacua SP smallMod BP bigMod
    J ell m cap patterns ω life k hcap).2 g
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalPostToG -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- On the true original FINAL G_N fibre, matching the genuine
frozen projected post-G output implies exactly the predecessor
canonical G fixed-input support, WITHOUT assuming nonzero G weight.
The old pending Fock multiset is retained, not collapsed into a set. -/
theorem memory_terminal_original_post_implies_canonical_G_fibre
    (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (x yg : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hElig : (⟨x,yg,c⟩ : PhysicalOrientedGWitnessIndex SP smallMod
      BP bigMod J ell cap) ∈ physicalGIndexedEligibleFibre SP smallMod
        BP bigMod J ell cap
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
            J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩))
        (memorySeenBeforeGValues BP bigMod
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩) (2*R)))
    (hPost : physicalFockProjection SP smallMod BP bigMod (J+ell) cap yg =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap false ⟨2*R,by omega⟩)) :
    (yg,c) ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (2*R) x := by
  unfold memoryPrimitiveGFixedInputFibre
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · have hx := (Finset.mem_filter.mp hElig).2.1
    rw [← hx] at hElig
    exact hElig
  · intro g
    have h := congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).2) hPost
    have hp := memory_frozen_source_physical_pending SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap false ⟨2*R,by omega⟩ g
    exact (Multiset.coe_eq_coe.mp h).trans (List.Perm.of_eq hp)
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalGToPost -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Conversely, a TRUE original canonical G_N fixed-input branch with
nonzero source G_N weight has exactly the original frozen projected
post-G state. We recover physical SMALL and active BIG marks from the
actual original nonzero G operation and the full OLD Fock multiset from
the canonical original source G fibre. No terminal kernel is postulated. -/
theorem memory_terminal_canonical_G_nonzero_implies_exact_post
    (q rho : ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (x yg : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩))
    (hm : (yg,c) ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (2*R) x)
    (hn : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) (2*R) Vbig mu x yg c ≠ 0) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap yg =
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap false ⟨2*R,by omega⟩) := by
  have hop := (physical_nonzero_ghost_witness_is_operational SP smallMod BP bigMod
    (J+ell) cap q rho (2*R) (2*R) Vbig mu x yg c hn).1
  apply Prod.ext
  · change yg.1 = ω.1 ⟨2*R,by omega⟩
    exact hop.1.symm.trans (congrArg Prod.fst hx)
  · funext g
    apply Prod.ext
    · exact (hop.2 g).symm.trans
        (congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
          (yy.2 g).1) hx)
    · have hp := (Finset.mem_filter.mp hm).2.2 g
      have htarget := memory_frozen_source_physical_pending SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap false ⟨2*R,by omega⟩ g
      exact Multiset.coe_eq_coe.mpr (hp.trans (List.Perm.of_eq htarget.symm))
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalIff -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- On a genuinely eligible ORIGINAL G_N indexed witness with nonzero
ORIGINAL source G_N coefficient, the full frozen post-G projection is
equivalent to membership in the original canonical fixed-input G_N
fibre. This is not a new root/G kernel law, and keeps original ordered
G ghost OLD indices and full post-G Fock multiset. -/
theorem memory_terminal_source_nonzero_post_iff_original_G_fibre
    (q rho : ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (a : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod J ell cap)
    (hElig : a ∈ physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (2*R)))
    (hn : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) (2*R) Vbig mu a.1 a.2.1 a.2.2 ≠ 0) :
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap false ⟨2*R,by omega⟩)) ↔
    (a.2.1,a.2.2) ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (2*R) a.1 := by
  constructor
  · intro hh
    exact memory_terminal_original_post_implies_canonical_G_fibre SP smallMod
      BP bigMod J ell m cap patterns k R ω life hcap a.1 a.2.1 a.2.2 hElig hh
  · intro hh
    have hx := (Finset.mem_filter.mp hElig).2.1
    exact memory_terminal_canonical_G_nonzero_implies_exact_post SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k R ω life hcap a.1 a.2.1 a.2.2 hx hh hn
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalWeightedMask -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 500000

/-- The ACTUAL source terminal indexed G_N weighted summand with its
true input Hilbert conditional orbit ratio and final output vacuum is
exactly the original canonical G_N slice weighted summand, on every
genuinely eligible ordered G_N witness. Actual zero-G branches are zero
on BOTH sides; all OLD and ghost orderings remain indexed. -/
theorem memory_source_terminal_actual_weighted_mask_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (a : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod J ell cap)
    (hElig : a ∈ physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (2*R))) :
    let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩)
    let t := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap false ⟨2*R,by omega⟩)
    (if physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1 = t then
      physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod J ell cap
        q rho Vsmall Vbig mu (2*R) (2*R) y a
     else 0) =
    (if (a.2.1,a.2.2) ∈ memoryPrimitiveGFixedInputFibre SP smallMod
        BP bigMod J ell cap
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        (2*R) a.1 then
      (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu a.1 : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) *
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho (2*R) (2*R) Vbig mu a.1 a.2.1 a.2.2
     else 0) := by
  classical
  dsimp only
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩)
  let t := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap false ⟨2*R,by omega⟩)
  let hG := physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) (2*R) Vbig mu a.1 a.2.1 a.2.2
  let ratio : ℂ := (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
    Vsmall mu a.1 : ℂ) /
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ)
  change (if physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      a.2.1 = t then
      physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod J ell cap
        q rho Vsmall Vbig mu (2*R) (2*R) y a else 0) =
    (if (a.2.1,a.2.2) ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod
      J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (2*R) a.1 then ratio*hG else 0)
  by_cases hn : hG ≠ 0
  · have hh := memory_terminal_source_nonzero_post_iff_original_G_fibre
      SP smallMod BP bigMod J ell m cap patterns q rho Vbig mu k R
      ω life hcap a hElig hn
    by_cases ht : physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap a.2.1 = t
    · have hg := hh.mp ht
      have hv := memory_source_final_frozen_output_vacuum SP smallMod BP bigMod
        J ell m cap patterns k R ω life hcap a ht
      rw [if_pos ht, if_pos hg]
      change ratio * hG * physicalVacuum SP smallMod BP bigMod
        J ell (physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1) =
        ratio * hG
      rw [hv,mul_one]
    · have hg : ¬ (a.2.1,a.2.2) ∈ memoryPrimitiveGFixedInputFibre
          SP smallMod BP bigMod J ell cap
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          (2*R) a.1 := fun h => ht (hh.mpr h)
      rw [if_neg ht, if_neg hg]
  · have hzero : hG=0 := not_ne_iff.mp hn
    have hz : physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod J ell cap
        q rho Vsmall Vbig mu (2*R) (2*R) y a = 0 := by
      change ratio*hG*physicalVacuum SP smallMod BP bigMod J ell
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1) = 0
      rw [hzero]
      ring
    simp only [hz,hzero,mul_zero,ite_self]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bGenericGFubini -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Exact finite Fubini for a source-like ACTUAL dependent G witness
Sigma x, Sigma yg, Ghost x. Full conditional x weight and ghost
multiplicity preserved. No independent product law for the kernel. -/
theorem memory_B1b_dependent_G_weighted_Fubini
    {X Y : Type} [Fintype X] [Fintype Y]
    (Ghost : X → Type) [∀ x, Fintype (Ghost x)]
    (P : X → Prop)
    (R : (x : X) → Y → Ghost x → Prop)
    (C : (x : X) → Y → Ghost x → Prop)
    (hCR : ∀ x y c, C x y c → R x y c)
    (u : X → ℂ) (w : (x : X) → Y → Ghost x → ℂ) :
    (∑ a : (Σ x : X, Σ y : Y, Ghost x),
      if P a.1 ∧ R a.1 a.2.1 a.2.2 then
        if C a.1 a.2.1 a.2.2 then
          u a.1 * w a.1 a.2.1 a.2.2 else 0
      else 0) =
    ∑ x ∈ (Finset.univ : Finset X).filter P,
      u x * (∑ yz : (Y × Ghost x),
        if C x yz.1 yz.2 then w x yz.1 yz.2 else 0) := by
  classical
  simp only [Finset.sum_filter, Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : P x
  · simp only [hp, true_and, ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hcUniv
    by_cases hc : C x y c
    · have hr : R x y c := hCR x y c hc
      simp only [hr,hc,ite_true]
    · simp only [hc,ite_false,mul_zero,ite_self]
  · simp [hp]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalIndexedSlice -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 450000

/-- ORIGINAL source terminal G_N scalar indexed over the true eligible
G_N carrier and the frozen output is EXACTLY the G canonical old/ghost
fibre scalar, with BOTH sides using the true Hilbert conditional input
mass. All zero-weight raw G branches remain present in the finite sums. -/
theorem memory_source_terminal_original_weighted_indexed_slice
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g) :
    let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩)
    let t := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap false ⟨2*R,by omega⟩)
    let seen := memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) (2*R)
    (∑ a ∈ (physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
        y seen).filter (fun a =>
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1 = t),
      physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod J ell cap
        q rho Vsmall Vbig mu (2*R) (2*R) y a) =
    ∑ a ∈ (physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
        y seen).filter (fun a =>
          (a.2.1,a.2.2) ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod
            J ell cap
            (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
            (fun g p => life ⟨g,p⟩)
            (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
            (2*R) a.1),
      (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu a.1 : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) *
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho (2*R) (2*R) Vbig mu a.1 a.2.1 a.2.2 := by
  classical
  dsimp only
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have hm := memory_source_terminal_actual_weighted_mask_exact SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig mu k R ω life hcap a ha
  let tp := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap false ⟨2*R,by omega⟩)
  let C : Prop := (a.2.1,a.2.2) ∈ memoryPrimitiveGFixedInputFibre SP
    smallMod BP bigMod J ell cap
    (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun g p => life ⟨g,p⟩)
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    (2*R) a.1
  by_cases hp : physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1 = tp
  · by_cases hc : C
    · dsimp only [tp,C] at hp hc
      simpa only [hp,hc,ite_true] using hm
    · dsimp only [tp,C] at hp hc
      simpa only [hp,hc,ite_true,ite_false] using hm
  · by_cases hc : C
    · dsimp only [tp,C] at hp hc
      simpa only [hp,hc,ite_false,ite_true] using hm
    · dsimp only [tp,C] at hp hc
      simpa only [hp,hc,ite_false] using hm
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bGenericGFinset -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Source-shaped nested finite filters on the actual DEPENDENT indexed
G witness are exactly the source-shaped pair-of-conditional-fibre sum.
Original input x and original G ghost c (dependent on x) remain distinct,
and the ordered G output y is never treated as a probabilistic constant. -/
theorem memory_B1b_dependent_G_finset_fubini
    {X Y : Type} [Fintype X] [Fintype Y]
    (Ghost : X → Type) [∀ x, Fintype (Ghost x)]
    (P : X → Prop) (R C : (x : X) → Y → Ghost x → Prop)
    (hCR : ∀ x y c, C x y c → R x y c)
    (u : X → ℂ) (w : (x : X) → Y → Ghost x → ℂ) :
    (∑ a ∈ (Finset.univ : Finset (Σ x : X, Σ y : Y, Ghost x)).filter
        (fun a => P a.1 ∧ R a.1 a.2.1 a.2.2) |>.filter
          (fun a => C a.1 a.2.1 a.2.2),
      u a.1 * w a.1 a.2.1 a.2.2) =
    ∑ x ∈ (Finset.univ : Finset X).filter P,
      u x * (∑ yc ∈ (Finset.univ : Finset (Y × Ghost x)).filter
        (fun yc => C x yc.1 yc.2), w x yc.1 yc.2) := by
  classical
  calc
    _ = ∑ a : (Σ x : X, Σ y : Y, Ghost x),
        if P a.1 ∧ R a.1 a.2.1 a.2.2 then
          if C a.1 a.2.1 a.2.2 then u a.1 * w a.1 a.2.1 a.2.2 else 0
        else 0 := by
          rw [Finset.sum_filter, Finset.sum_filter]
    _ = ∑ x ∈ (Finset.univ : Finset X).filter P,
        u x * (∑ yz : Y × Ghost x,
          if C x yz.1 yz.2 then w x yz.1 yz.2 else 0) :=
            memory_B1b_dependent_G_weighted_Fubini Ghost P R C hCR u w
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_filter]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalTwofold -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 650000

/-- Original source indexed final G_N fibre with exact source Fock input
ratios and true ordered G old/ghost witnesses has the original twofold
conditional Hilbert/Fock disintegration. This is a specialization of a
proved dependent source G sigma Fubini, NOT an assumed G kernel or a
uniform Hilbert representative measure. -/
theorem memory_source_terminal_exact_canonical_G_twofold
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g) :
    let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
        J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩)
    let seen := memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) (2*R)
    (∑ a ∈ (physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
        y seen).filter (fun a =>
          (a.2.1,a.2.2) ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod
            J ell cap
            (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
            (fun g p => life ⟨g,p⟩)
            (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
            (2*R) a.1),
      (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu a.1 : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) *
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho (2*R) (2*R) Vbig mu a.1 a.2.1 a.2.2) =
    ∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod
        (J+ell) cap)).filter (fun x =>
        physicalFockProjection SP smallMod BP bigMod (J+ell) cap x = y),
      (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) *
      (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        (2*R) x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
          q rho (2*R) (2*R) Vbig mu x yc.1 yc.2) := by
  classical
  dsimp only
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap true ⟨2*R,by omega⟩)
  let seen := memorySeenBeforeGValues BP bigMod
    (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun g p => life ⟨g,p⟩) (2*R)
  let C := fun (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (yg : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
      (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x) =>
    (yg,c) ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (2*R) x
  have hCR : ∀ x yg c, C x yg c →
      physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap x seen c := by
    intro x yg c hc
    have hh := (Finset.mem_filter.mp hc).2.1
    exact (Finset.mem_filter.mp hh).2.2
  convert memory_B1b_dependent_G_finset_fubini
    (Ghost:=fun x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap =>
      FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (P:=fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x = y)
    (R:=fun x yg c => physicalGhostBatchEligible SP smallMod BP bigMod
      (J+ell) cap x seen c)
    (C:=C) hCR
    (u:=fun x => (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
      Vsmall mu x : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ))
    (w:=fun x yg c => physicalGBranchTerm SP smallMod BP bigMod
      (J+ell) cap q rho (2*R) (2*R) Vbig mu x yg c) using 1
  · apply Finset.sum_congr
    · ext a
      simp only [physicalGIndexedEligibleFibre, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rfl
    · intro a ha
      rfl
  · apply Finset.sum_congr rfl
    intro x hx
    congr 1
    apply Finset.sum_congr
    · ext yc
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rfl
    · intro yc hy
      rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalFullScalar -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 700000

/-- Source terminal G_N weighted scalar on the actual indexed witness. -/
theorem memory_source_terminal_G_N_full_weighted_scalar
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp)) :
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hd.cap_saturated q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k ⟨2*R,Nat.lt_succ_self (2*R)⟩ =
    memoryPrimitiveGUnorderedCoefficient BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (2*R) q rho (2*R) Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) := by
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m
    cap patterns ω life k hd.cap_saturated true ⟨2*R,by omega⟩
  have hmu (g : BG) (p : BP g) : 0 < mu g p :=
    physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one)
      (hd.Vbig_pos g) (hd.big_above_visits g p)
  have hOld : ∀ g, (Green64Fock.fockToList ((x0.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g)
        (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        true (2*R)) := by
    intro g
    exact List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod BP
      bigMod J ell m cap patterns ω life k hd.cap_saturated true
      ⟨2*R,by omega⟩ g)
  have ha := memory_source_actual_terminal_G_N_raw_slice SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life
  have hb := memory_source_terminal_original_weighted_indexed_slice SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig mu k R
    ω life hd.cap_saturated
  have hc := memory_source_terminal_exact_canonical_G_twofold SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig mu k R
    ω life hd.cap_saturated
  have hd' := memory_source_primitive_G_orbit_weighted_fibre SP smallMod BP bigMod
    J ell cap
    (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun g p => life ⟨g,p⟩)
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    (2*R) hd.big_injective (fun g p => hs ⟨g,p⟩)
    hd.cap_saturated q rho (2*R) Vsmall Vbig mu
    hd.Vsmall_pos hmu x0 hOld
  dsimp only at ha hb hc hd' ⊢
  exact ha.trans (hb.trans (hc.trans hd'))
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bFullOriginalPrimitiveProduct -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 500000

/-- The COMPLETE original indexed source root fibre is exactly its genuine
original initial Hilbert mass, the full product of ORIGINAL conditional
indexed-G/E fitting head sums, and the FINAL ORIGINAL terminal G_N sum.
No new equality to the frozen RHS is assumed: that precise coefficient
evaluation remains B1's nontrivial local obligation. -/
theorem memory_source_nonzero_root_fibre_exact_complete_GN_product
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
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
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
    (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩) : ℂ) *
    (∏ i : Fin (2*R),
      memoryPrimitiveGUnorderedCoefficient BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) *
      memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k (memory_frozen_source_profile_support SP smallMod BP bigMod
            J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)) i.castSucc)
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k (memory_frozen_source_profile_support SP smallMod BP bigMod
            J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)) i.succ)
        q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)) *
    memoryPrimitiveGUnorderedCoefficient BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (2*R) q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) := by
  have hroot := memory_source_nonzero_root_fibre_exact_original_primitive_GE_product
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  have hprime : (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q hprime
  have hterminal := memory_source_terminal_G_N_full_weighted_scalar SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hs
  rw [hroot, hterminal]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalSchedule -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (N : ℕ)
variable (A : P → Finset ℕ) (life : P → MemoryLifespanChoice (N+1))
variable (offset : ℕ → ℤ)

/-- Under the unchanged source finite-lifespan support, a ghost cannot
first be born at the final visit N: its death would also be N, forcing
an active birth there by the original equal-endpoint rule. -/
theorem memory_source_terminal_ghost_births_empty
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p)) :
    memoryGhostBirthSet A life N = ∅ := by
  ext p
  constructor
  · intro hp
    exfalso
    have hb := (Finset.mem_filter.mp hp).2
    cases hl : life p with
    | none => simp [memoryScheduleGhostBirth,hl] at hb
    | some jd =>
      simp only [memoryScheduleGhostBirth,hl] at hb
      have hsp := hs p
      simp only [hl,MemoryFrozenScheduleSupport] at hsp
      have hend : jd.1.val = jd.2.val := by omega
      have ha : N ∈ A p := by simpa only [hb.1] using hsp.2.2.2 hend
      exact hb.2 ha
  · intro hp
    simp at hp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalNoContinuing -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (N : ℕ)
variable (A : P → Finset ℕ)
variable (life : P → MemoryLifespanChoice (N+1))

/-- At the genuine source FINAL visit the ORIGINAL canonical memory
cannot continue beyond its finite-index end; every still-pending
OLD particle must terminate. This is an exact lifespan-index bound,
independent of q, rho, positivity, or a probabilistic G law. -/
theorem memory_terminal_before_implies_terminate (p : P)
    (h : memoryScheduleBefore (A p) (life p) N) :
    memoryScheduleTerminate (A p) (life p) N := by
  cases hl : life p with
  | none => simp [memoryScheduleBefore,hl] at h
  | some jd =>
    simp only [memoryScheduleBefore,hl] at h
    simp only [memoryScheduleTerminate,hl]
    exact ⟨by have hb := jd.2.isLt; omega,h.2.2⟩

/-- Every zero-residue canonical OLD atom at final G_N is a terminal
death. The continuing-zero original source set is identically empty,
including any roots with zero physical weight. -/
theorem memory_terminal_continuing_zero_empty
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    (offset : ℕ → ℤ) :
    memoryContinuingZeroSet modulus A life offset N = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    have h := Finset.mem_sdiff.mp hp
    have hb := (Finset.mem_filter.mp h.1).2.1
    exact False.elim (h.2 (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,memory_terminal_before_implies_terminate N A life p hb⟩))
  · intro hp
    simp at hp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalDeathScalar -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (N : ℕ)
variable (A : (g : BG) → BP g → Finset ℕ)
variable (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
variable (offset : ℕ → ℤ)

/-- The ORIGINAL unordered physical terminal G_N scalar has no ghost
births and no continuing zero atoms; it is EXACTLY the death scalar
at true q_N. This follows from finite lifespan support (no extra
assumption on q, rho, mu, Vbig), including the source G birth
factorial and all original ordered OLD witnesses. -/
theorem memory_source_terminal_G_unordered_death_scalar
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (q rho : ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) :
    memoryPrimitiveGUnorderedCoefficient BP bigMod A life offset
      N q rho N Vbig mu =
    ∏ g : BG,
      (-((sourceVisitEta q N N : ℝ) : ℂ) / (rho : ℂ)) ^
        (memoryGhostDeathSet (A g) (life g) N).card := by
  unfold memoryPrimitiveGUnorderedCoefficient
  apply Finset.prod_congr rfl
  intro g hg
  have hbirth := memory_source_terminal_ghost_births_empty
    (bigMod g) N (A g) (life g) offset (hs g)
  have hcont := memory_terminal_continuing_zero_empty
    N (A g) (life g) (bigMod g) offset
  rw [hbirth,hcont]
  simp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTerminalTailDeath -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The TRUE original terminal G_N full Fock/Hilbert weighted fibre is
the original per-group ghost DEATH product, with exact half-endpoint
visit eta_N and rho. This combines exact G_N source orbit disintegration
and finite lifespan last-visit support, with no forgotten V/mu birth
or surviving-memory terms. -/
theorem memory_source_terminal_fitting_tail_death_scalar
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp)) :
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hd.cap_saturated q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k ⟨2*R,Nat.lt_succ_self (2*R)⟩ =
    ∏ g : BG,
      (-((sourceVisitEta q (2*R) (2*R) : ℝ) : ℂ) / (rho : ℂ)) ^
        (memoryGhostDeathSet
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) (2*R)).card := by
  rw [memory_source_terminal_G_N_full_weighted_scalar SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
      k R hd ω life hs]
  exact memory_source_terminal_G_unordered_death_scalar BP bigMod (2*R)
    (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun g p => life ⟨g,p⟩)
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    (fun g p => hs ⟨g,p⟩) q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bFullOriginalTerminalDeath -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 500000

/-- The COMPLETE original indexed source root fibre is exactly its genuine
original initial Hilbert mass, the full product of ORIGINAL conditional
indexed-G/E fitting head sums, and the FINAL ORIGINAL terminal G_N sum.
No new equality to the frozen RHS is assumed: that precise coefficient
evaluation remains B1's nontrivial local obligation. -/
theorem memory_source_nonzero_root_fibre_exact_terminal_death_product
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
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
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
    (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩) : ℂ) *
    (∏ i : Fin (2*R),
      memoryPrimitiveGUnorderedCoefficient BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) *
      memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k (memory_frozen_source_profile_support SP smallMod BP bigMod
            J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)) i.castSucc)
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
          ω life k (memory_frozen_source_profile_support SP smallMod BP bigMod
            J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)) i.succ)
        q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)) *
    (∏ g : BG,
      (-((sourceVisitEta q (2*R) (2*R) : ℝ) : ℂ) / (rho : ℂ)) ^
        (memoryGhostDeathSet
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) (2*R)).card) := by
  have hroot := memory_source_nonzero_root_fibre_exact_original_primitive_GE_product
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  have hprime : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q hprime
  have hterminal := memory_source_terminal_fitting_tail_death_scalar SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hs
  rw [hroot, hterminal]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bPrimeGFactor -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- A finite ORIGINAL per-prime G factor identity. Three disjoint or
overlapping source event sets are handled without any cancellation or
symmetry quotient; the group birth-mu product is preserved exactly. -/
theorem memory_finite_ghost_G_factor_over_primes
    {P : Type} [Fintype P] [DecidableEq P]
    (S T U : Finset P) (a b c : ℂ) (mu : P → ℂ) :
    a ^ S.card * b ^ T.card * c ^ U.card *
      (∏ p ∈ U, mu p) =
    ∏ p : P, (if p ∈ S then a else 1) *
      (if p ∈ T then b else 1) *
      (if p ∈ U then c * mu p else 1) := by
  classical
  have filt (U : Finset P) (k : P → ℂ) :
      (∏ p : P, if p ∈ U then k p else 1) = ∏ p ∈ U, k p := by
    rw [← Finset.prod_filter]
    congr 1
    ext p
    simp
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [filt S (fun _ => a), filt T (fun _ => b),
    filt U (fun p => c * mu p)]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const]
  ring

end Green64FullPhysicalE

end

end

/-! ## MemoryB1bPrimitiveGPrimeFactor -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- Literal source prime-level G scalar retaining deaths, zero
continuations and initial ghost births with their ORIGINAL mu/V factors.
Its product over primes equals the genuine unordered G group scalar. -/
def memoryPrimitiveGPerPrimeFactor
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (gp : PhysicalSourcePrime BP) : ℂ :=
  (if gp.2 ∈ memoryGhostDeathSet (A gp.1) (life gp.1) i
      then -(sourceVisitEta q N i : ℂ) / (rho : ℂ) else 1) *
  (if gp.2 ∈ memoryContinuingZeroSet (bigMod gp.1) (A gp.1)
      (life gp.1) offset i
      then (sourceVisitQ q N i : ℂ) / (rho : ℂ)^2 else 1) *
  (if gp.2 ∈ memoryGhostBirthSet (A gp.1) (life gp.1) i
      then (-(sourceVisitEta q N i : ℂ) * (Vbig gp.1 : ℂ) /
        (rho : ℂ)) * (mu gp.1 gp.2 : ℂ) else 1)

/-- Source-correct exact disintegration of EVERY primitive G row into
its original per-prime schedule factors, including zero G branches.
No source positivity or lifespan-support hypothesis is used: it is a
finite algebraic identity of the ACTUAL unordered source G coefficient. -/
theorem memory_original_G_unordered_eq_true_prime_product
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) :
    memoryPrimitiveGUnorderedCoefficient BP bigMod A life offset
      i q rho N Vbig mu =
    ∏ gp : PhysicalSourcePrime BP,
      memoryPrimitiveGPerPrimeFactor BP bigMod A life offset i
        q rho N Vbig mu gp := by
  unfold memoryPrimitiveGUnorderedCoefficient
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  change _ = ∏ p : BP g, _
  unfold memoryPrimitiveGPerPrimeFactor
  exact memory_finite_ghost_G_factor_over_primes
    (memoryGhostDeathSet (A g) (life g) i)
    (memoryContinuingZeroSet (bigMod g) (A g) (life g) offset i)
    (memoryGhostBirthSet (A g) (life g) i)
    (-(sourceVisitEta q N i : ℂ) / (rho : ℂ))
    ((sourceVisitQ q N i : ℂ) / (rho : ℂ)^2)
    (-(sourceVisitEta q N i : ℂ) * (Vbig g : ℂ) / (rho : ℂ))
    (fun p => (mu g p : ℂ))
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bPrimitiveGTimeProduct -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ)

/-- Separate the real source G_i contribution at every GE visit and the
last G_N coefficient into ONE product of original per-prime G factors.
The E_i scalars are kept completely arbitrary, so the proof cannot
accidentally double-count an E V or rho normalization. This is the
exact source G product, not a surrogate independent prime law. -/
theorem memory_source_all_primitive_G_as_per_prime_rows
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (E : Fin N → ℂ) :
    (∏ i : Fin N,
      memoryPrimitiveGUnorderedCoefficient BP bigMod A life offset
        i.val q rho N Vbig mu * E i) *
      memoryPrimitiveGUnorderedCoefficient BP bigMod A life offset
        N q rho N Vbig mu =
    (∏ gp : PhysicalSourcePrime BP,
      (∏ i : Fin N,
        memoryPrimitiveGPerPrimeFactor BP bigMod A life offset
          i.val q rho N Vbig mu gp) *
      memoryPrimitiveGPerPrimeFactor BP bigMod A life offset
        N q rho N Vbig mu gp) *
    (∏ i : Fin N, E i) := by
  have hg (i : Fin N) :=
    memory_original_G_unordered_eq_true_prime_product
      BP bigMod A life offset i.val q rho N Vbig mu
  have hn :=
    memory_original_G_unordered_eq_true_prime_product
      BP bigMod A life offset N q rho N Vbig mu
  rw [Finset.prod_mul_distrib]
  simp_rw [hg]
  rw [hn]
  have hcomm :
      (∏ i : Fin N, ∏ gp : PhysicalSourcePrime BP,
        memoryPrimitiveGPerPrimeFactor BP bigMod A life offset
          i.val q rho N Vbig mu gp) =
      ∏ gp : PhysicalSourcePrime BP, ∏ i : Fin N,
        memoryPrimitiveGPerPrimeFactor BP bigMod A life offset
          i.val q rho N Vbig mu gp := Finset.prod_comm
  rw [hcomm]
  rw [Finset.prod_mul_distrib]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bTargetSlotReindex -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- On the ORIGINAL oriented BIG target slots, a target prime satisfying
any schedule predicate is counted exactly once, despite the endpoint
permutation. The image is the true active-target prime carrier. -/
theorem memory_B1b_permuted_target_slot_image
    {P : Type} [DecidableEq P] (M : ℕ)
    (target : Fin M → P)
    (tau : Equiv.Perm (Fin M))
    (pred : P → Prop) :
    (Finset.univ.filter (fun j : Fin M => pred (target (tau j)))).image
      (fun j => target (tau j)) =
    (Finset.univ.image target).filter pred := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp hp
    have hpred : pred (target (tau j)) := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · exact Finset.mem_image.mpr ⟨tau j,Finset.mem_univ _,hjp⟩
    · simpa [hjp] using hpred
  · intro hp
    have htarget := (Finset.mem_filter.mp hp).1
    have hpred := (Finset.mem_filter.mp hp).2
    obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp htarget
    refine Finset.mem_image.mpr ⟨tau.symm j,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simpa [Equiv.apply_symm_apply,hjp] using hpred
    · simpa only [Equiv.apply_symm_apply] using hjp

/-- The genuine original source promotion-slot cardinality equals
the cardinality of the distinct target-active primes selected by the
same original schedule predicate. There is no factorial or multiplicity
from the endpoint permutation. -/
theorem memory_B1b_permuted_target_slot_card
    {P : Type} [DecidableEq P] (M : ℕ)
    (target : Fin M → P) (htarget : Function.Injective target)
    (tau : Equiv.Perm (Fin M)) (pred : P → Prop) :
    (Finset.univ.filter (fun j : Fin M => pred (target (tau j)))).card =
    ((Finset.univ.image target).filter pred).card := by
  classical
  rw [← memory_B1b_permuted_target_slot_image M target tau pred]
  exact (Finset.card_image_of_injective _
    (htarget.comp tau.injective)).symm

/-- The ORIGINAL source E fresh/promoted target-slot `mu` factors
are EXACTLY one product over their distinct target-active prime labels,
without any slot-to-prime surjectivity hypothesis. -/
theorem memory_B1b_permuted_target_slot_prod
    {P : Type} [DecidableEq P] (M : ℕ)
    (target : Fin M → P) (htarget : Function.Injective target)
    (tau : Equiv.Perm (Fin M)) (pred : P → Prop)
    (mu : P → ℂ) :
    (∏ j ∈ Finset.univ.filter (fun j : Fin M => pred (target (tau j))),
        mu (target (tau j))) =
    ∏ p ∈ (Finset.univ.image target).filter pred, mu p := by
  classical
  rw [← memory_B1b_permuted_target_slot_image M target tau pred]
  exact (Finset.prod_image
    (s := Finset.univ.filter (fun j : Fin M => pred (target (tau j))))
    (g := fun j => target (tau j))
    (f := mu)
    (fun x hx y hy hxy => tau.injective (htarget hxy))).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bEPromotionPrimes -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (M : ℕ) (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (i : ℕ)

/-- In the actual source E_i transition, every scheduled promotion
prime is among the actual i+1 active target labels, so the original
permuted promote-slot image equals the TRUE global schedule-promotion
prime set. No fictitious bijection between arbitrary slot occupations
and primes is introduced. -/
theorem memory_B1b_E_promotion_image_exact
    (target : Fin M → P) (tau : Equiv.Perm (Fin M))
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p) :
    (Finset.univ.filter (fun j : Fin M =>
      memorySchedulePromote (A (target (tau j))) (life (target (tau j))) i)).image
        (fun j => target (tau j)) =
    (Finset.univ : Finset P).filter (fun p =>
      memorySchedulePromote (A p) (life p) i) := by
  rw [memory_B1b_permuted_target_slot_image M target tau
    (fun p => memorySchedulePromote (A p) (life p) i)]
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hp
    exact hp.2
  · intro hp
    have ha : i+1 ∈ A p := by
      cases hl : life p with
      | none => simp [memorySchedulePromote, hl] at hp
      | some az =>
        simp only [memorySchedulePromote,hl] at hp
        exact hp.2.1
    obtain ⟨j,hj⟩ := (hA1 p).mp ha
    exact ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩,hp⟩

/-- Genuine original BIG source E promotion count equals the count of
prime-level lifespan promotions. -/
theorem memory_B1b_E_promotion_count_exact
    (target : Fin M → P) (htarget : Function.Injective target)
    (tau : Equiv.Perm (Fin M))
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p) :
    (memoryEPromoteSlots M A life i target tau).card =
      ((Finset.univ : Finset P).filter (fun p =>
        memorySchedulePromote (A p) (life p) i)).card := by
  unfold memoryEPromoteSlots
  rw [← memory_B1b_E_promotion_image_exact M A life i target tau hA1]
  exact (Finset.card_image_of_injective _
    (htarget.comp tau.injective)).symm

/-- ORIGINAL E promotion V denominator is one factor per actual
promoted BIG prime, independent of its endpoint ordering. -/
theorem memory_B1b_E_promotion_V_exact
    (target : Fin M → P) (htarget : Function.Injective target)
    (tau : Equiv.Perm (Fin M))
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (V : ℂ) :
    (1 / V) ^ (memoryEPromoteSlots M A life i target tau).card =
      ∏ p : P, if memorySchedulePromote (A p) (life p) i
        then (1 / V) else 1 := by
  rw [memory_B1b_E_promotion_count_exact M A life i target htarget tau hA1]
  rw [← Finset.prod_filter]
  rw [Finset.prod_const]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bEFreshPrimes -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (M : ℕ) (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (i : ℕ)

/-- The ORIGINAL oriented E_i fresh slot image is the TRUE global
prime-level fresh set whenever the source old/store/continuation
inverse has established exact fresh membership for its actual
permutation. Every source fresh prime is active at i+1, so none
may occur outside the original target slots. -/
theorem memory_B1b_E_fresh_image_exact
    (target : Fin M → P) (tau : Equiv.Perm (Fin M))
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (shared : Finset (Fin M))
    (hFresh : ∀ j : Fin M,
      j ∈ orientedFresh M shared (memoryEPromoteSlots M A life i target tau) ↔
        memoryScheduleFresh (A (target (tau j)))
          (life (target (tau j))) i) :
    (orientedFresh M shared (memoryEPromoteSlots M A life i target tau)).image
      (fun j => target (tau j)) =
    (Finset.univ : Finset P).filter (fun p =>
      memoryScheduleFresh (A p) (life p) i) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [hjp] using (hFresh j).mp hj
  · intro hp
    have hsp := (Finset.mem_filter.mp hp).2
    have ha : i+1 ∈ A p := by
      cases hl : life p with
      | none => simp [memoryScheduleFresh,hl] at hsp
      | some az =>
        simp only [memoryScheduleFresh,hl] at hsp
        exact hsp.2.1
    obtain ⟨j,hj⟩ := (hA1 p).mp ha
    refine Finset.mem_image.mpr ⟨tau.symm j,?_,?_⟩
    · apply (hFresh (tau.symm j)).mpr
      simpa only [Equiv.apply_symm_apply,hj] using hsp
    · simpa only [Equiv.apply_symm_apply] using hj

/-- Every TRUE original E fresh BIG prime has exactly one actual
oriented source target slot. No factorial or lost multiplicity. -/
theorem memory_B1b_E_fresh_count_exact
    (target : Fin M → P) (htarget : Function.Injective target)
    (tau : Equiv.Perm (Fin M))
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (shared : Finset (Fin M))
    (hFresh : ∀ j : Fin M,
      j ∈ orientedFresh M shared (memoryEPromoteSlots M A life i target tau) ↔
        memoryScheduleFresh (A (target (tau j)))
          (life (target (tau j))) i) :
    (orientedFresh M shared (memoryEPromoteSlots M A life i target tau)).card =
    ((Finset.univ : Finset P).filter
      (fun p => memoryScheduleFresh (A p) (life p) i)).card := by
  rw [← memory_B1b_E_fresh_image_exact M A life i target tau hA1 shared hFresh]
  exact (Finset.card_image_of_injective _
    (htarget.comp tau.injective)).symm

/-- ORIGINAL E fresh-mu slot product = exactly one mu per BIG prime
whose lifespan really starts ACTIVE at this source step. -/
theorem memory_B1b_E_fresh_mu_exact
    (target : Fin M → P) (htarget : Function.Injective target)
    (tau : Equiv.Perm (Fin M))
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (shared : Finset (Fin M))
    (hFresh : ∀ j : Fin M,
      j ∈ orientedFresh M shared (memoryEPromoteSlots M A life i target tau) ↔
        memoryScheduleFresh (A (target (tau j)))
          (life (target (tau j))) i)
    (mu : P → ℂ) :
    (∏ j ∈ orientedFresh M shared
        (memoryEPromoteSlots M A life i target tau), mu (target (tau j))) =
    ∏ p ∈ (Finset.univ : Finset P).filter (fun p =>
      memoryScheduleFresh (A p) (life p) i), mu p := by
  classical
  rw [← memory_B1b_E_fresh_image_exact M A life i target tau hA1 shared hFresh]
  exact (Finset.prod_image
    (s := orientedFresh M shared (memoryEPromoteSlots M A life i target tau))
    (g := fun j => target (tau j)) (f := mu)
    (fun a ha b hb heq => tau.injective (htarget heq))).symm

/-- The combined true E promotion V^{-1} and E fresh mu factors
are the ORIGINAL prime-level schedule product; neither source
endpoint permutation contributes extra multiplicity. -/
theorem memory_B1b_E_V_mu_exact
    (target : Fin M → P) (htarget : Function.Injective target)
    (tau : Equiv.Perm (Fin M))
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (shared : Finset (Fin M))
    (hFresh : ∀ j : Fin M,
      j ∈ orientedFresh M shared (memoryEPromoteSlots M A life i target tau) ↔
        memoryScheduleFresh (A (target (tau j)))
          (life (target (tau j))) i)
    (V : ℂ) (mu : P → ℂ) :
    (1 / V) ^ (memoryEPromoteSlots M A life i target tau).card *
      (∏ j ∈ orientedFresh M shared
        (memoryEPromoteSlots M A life i target tau), mu (target (tau j))) =
    ∏ p : P,
      (if memorySchedulePromote (A p) (life p) i then (1 / V) else 1) *
      (if memoryScheduleFresh (A p) (life p) i then mu p else 1) := by
  rw [memory_B1b_E_promotion_V_exact M A life i
    target htarget tau hA1 V]
  rw [memory_B1b_E_fresh_mu_exact M A life i
    target htarget tau hA1 shared hFresh mu]
  rw [Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bFrozenEPromoteV -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 550000

/-- The ORIGINAL frozen E_i BIG promotion V factor, for all BIG
groups and the exact target active labels of the genuine source
frozen independent-residue lift, equals the per-prime promotion
schedule product. Every original target permutation is preserved,
but its slot multiplicity cancels exactly once. No made-up V. -/
theorem memory_source_frozen_E_promote_V_prime_product {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ)
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin N)
    (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (Vbig : BG → ℝ) :
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    (∏ g : BG,
      (1/(Vbig g : ℂ)) ^
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)).card) =
    ∏ gp : PhysicalSourcePrime BP,
      if memorySchedulePromote
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (life gp) i.val then (1/(Vbig gp.1 : ℂ)) else 1 := by
  dsimp only
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  exact memory_B1b_E_promotion_V_exact (J+ell)
    (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun p => life ⟨g,p⟩) i.val
    (Green64SmallHaar.marks (bigMod g) (J+ell)
      ((memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
        patterns ω life k hs i.succ).2 g))
    (Green64SmallHaar.marks_injective _ _ _)
    (f.2.2.1 g)
    (fun p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns
      ω i.succ g p)
    (Vbig g : ℂ)
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bFrozenEFreshSchedule -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 900000

/-- For an ORIGINAL nonzero frozen source profile, an oriented E_i
fresh BIG slot is precisely a true prime with a fresh ACTIVE lifespan
start at that visit. This is derived from the actual source edge
allowedness (with Nu/aux and permutation compatibility), not postulated
from an arbitrary shared-slots model. -/
theorem memory_source_frozen_E_fresh_slot_iff_schedule
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
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
    (i : Fin (2*R)) (g : BG) (j : Fin (J+ell)) :
    let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    let f := ω.2.2 i
    let target := Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
    j ∈ orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns f.1.1) g)
      (memoryEPromoteSlots (J+ell)
        (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun p => life ⟨g,p⟩) i.val target (f.2.2.1 g)) ↔
      memoryScheduleFresh
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω
          ⟨g,target (f.2.2.1 g j)⟩)
        (life ⟨g,target (f.2.2.1 g j)⟩) i.val := by
  dsimp only
  have hp : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
          ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q hp
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
    patterns ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
    patterns ω life k hs i.succ
  let f := ω.2.2 i
  have hf := memory_frozen_source_lift_frame_compatible SP smallMod BP bigMod
    J ell m patterns ω life k hs q Vsmall Vbig Knu zeta theta
    (left_ne_zero_of_mul hn) i
  have hA0 (g : BG) (p : BP g) :
      i.val ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩ ↔
      ∃ l, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) l = p :=
    memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.castSucc g p
  have hA1 (g : BG) (p : BP g) :
      i.val+1 ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩ ↔
      ∃ l, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) l = p :=
    memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.succ g p
  have hshared : ∀ j, j ∈ sourceBigShared J ell m (patterns f.1.1) g →
      Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) (f.2.1 g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (f.2.2.1 g j) := by
    intro j hj
    exact ((Finset.mem_filter.mp hf).2.2.2.2.1 g).2 j hj
  have hcont : ∀ j l,
      Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) (f.2.1 g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (f.2.2.1 g l) →
      j ∈ sourceBigShared J ell m (patterns f.1.1) g ∧ l = j := by
    intro j l he
    exact memory_source_active_continuation_is_shared SP smallMod BP bigMod
      J ell m hd.small_prime hd.big_prime hd.big_injective hd.disjoint
      (patterns f.1.1) f.1.2 ix iy
      (Finset.mem_filter.mp hf).2.2.1
      f.2.1 f.2.2.1 f.2.2.2.1
      (physicalAlternatingSign i.val) k (Finset.mem_filter.mp hf).2.1
      hd.k_ne hd.big_above_k (Finset.mem_filter.mp hf).2.2.2.2.1 g j l he
  exact memory_E_fresh_slot_iff (J+ell) (bigMod g)
    (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun p => life ⟨g,p⟩)
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    i.val (fun p => hs ⟨g,p⟩)
    (Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
    (f.2.1 g) (f.2.2.1 g) (hA0 g) (hA1 g)
    (sourceBigShared J ell m (patterns f.1.1) g)
    hshared hcont j
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bFrozenEVmuPrimes -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 900000

/-- For the ORIGINAL nonzero frozen source profile, the complete BIG
E_i factor consisting of the promotion V denominators and FRESH
mu_tilde integrations equals the exact product of the corresponding
prime-level lifespan schedule factors. Every original endpoint
permutation and its actual target active state is present in the LHS.
No extra V or permutation factorial is introduced. -/
theorem memory_source_frozen_E_V_mu_prime_product
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
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
    (mu : (g : BG) → BP g → ℝ) (i : Fin (2*R)) :
    let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
      J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    let f := ω.2.2 i
    (∏ g : BG,
      (1 / (Vbig g : ℂ)) ^
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)).card *
      (∏ j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns f.1.1) g)
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)),
        (mu g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
          (f.2.2.1 g j)) : ℂ))) =
    (∏ gp : PhysicalSourcePrime BP,
      (if memorySchedulePromote
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (life gp) i.val then (1/(Vbig gp.1 : ℂ)) else 1) *
      (if memoryScheduleFresh
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (life gp) i.val then (mu gp.1 gp.2 : ℂ) else 1)) := by
  dsimp only
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
    patterns ω life k hs i.succ
  let f := ω.2.2 i
  conv_rhs => rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  let target := Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
  have hA1 : ∀ p : BP g,
      i.val+1 ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩ ↔
      ∃ j, target j = p :=
    fun p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.succ g p
  have hFresh (j : Fin (J+ell)) :
      j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns f.1.1) g)
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val target (f.2.2.1 g)) ↔
      memoryScheduleFresh
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω
          ⟨g,target (f.2.2.1 g j)⟩)
        (life ⟨g,target (f.2.2.1 g j)⟩) i.val := by
    exact memory_source_frozen_E_fresh_slot_iff_schedule SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
      k R hd ω life hn i g j
  exact memory_B1b_E_V_mu_exact (J+ell)
    (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun p => life ⟨g,p⟩) i.val target
    (Green64SmallHaar.marks_injective _ _ _)
    (f.2.2.1 g) hA1
    (sourceBigShared J ell m (patterns f.1.1) g)
    hFresh (Vbig g : ℂ) (fun p => (mu g p : ℂ))
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bPendingZeroCounts -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Counting a property on an ORIGINAL finite prime list is exactly the
cardinality of the corresponding original finite prime subset. The
source Fock atoms remain labelled by actual primes, not by a count proxy. -/
theorem memory_B1b_finset_list_countP_eq_card
    {P : Type} [DecidableEq P] (s : Finset P)
    (pred : P → Prop) [DecidablePred pred] :
    (s.toList.countP pred) = (s.filter pred).card := by
  rw [← Multiset.coe_countP pred s.toList]
  change Multiset.countP pred (↑(s.val.toList)) = _
  rw [Multiset.coe_toList]
  exact Multiset.countP_eq_card_filter pred s.val

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ)

/-- The zero-residue OLD Fock atom counter in the ORIGINAL canonical
memory list is literally the number of distinct true prime labels
which are scheduled pending and have zero residue, before/after G_i.
No quotient/collision/extra cardinality assumption is used. -/
theorem memory_B1b_canonical_pending_zero_count
    (before : Bool) (i : ℕ) :
    (memoryCanonicalPendingList modulus A life offset before i).countP
      (fun z => z.2 = 0) =
    ((Finset.univ : Finset P).filter (fun p =>
      (if before then memoryScheduleBefore (A p) (life p) i
        else memoryScheduleAfter (A p) (life p) i) ∧
      memoryScheduleResidue (modulus p)
        (fun t => (offset t : ZMod (modulus p))) (life p) i = 0)).card := by
  unfold memoryCanonicalPendingList
  rw [List.countP_map]
  simp only [Function.comp_def]
  rw [memory_B1b_finset_list_countP_eq_card]
  rw [Finset.filter_filter]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bERhoPrimeFactor -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- The ORIGINAL E_i rho power for the pending OLD zero atoms is an
exact product of two TRUE per-prime pending-residue indicators. Unlike
a cardinality proxy, this contains BOTH the post-G_i and pre-G_(i+1)
zero-residue tests and their actual time-indexed source offsets. -/
def memoryPrimitiveERhoPerPrimeFactor (rho : ℝ) (p : P) : ℂ :=
  (if memoryScheduleAfter (A p) (life p) i ∧
      memoryScheduleResidue (modulus p)
        (fun t => (offset t : ZMod (modulus p))) (life p) i = 0
    then (rho : ℂ) else 1) *
  (if memoryScheduleBefore (A p) (life p) (i+1) ∧
      memoryScheduleResidue (modulus p)
        (fun t => (offset t : ZMod (modulus p))) (life p) (i+1) = 0
    then (rho : ℂ) else 1)

/-- Exact source identity for the complete pair of E OLD rho factors;
there is no omitted OLD index and no change of the source orientation. -/
theorem memory_source_E_rho_canonical_pending_as_prime_product (rho : ℝ) :
    (rho : ℂ) ^
      ((memoryCanonicalPendingList modulus A life offset false i).countP
        (fun z => z.2 = 0) +
       (memoryCanonicalPendingList modulus A life offset true (i+1)).countP
        (fun z => z.2 = 0)) =
    ∏ p : P, memoryPrimitiveERhoPerPrimeFactor modulus A life offset i rho p := by
  rw [memory_B1b_canonical_pending_zero_count modulus A life offset false i]
  rw [memory_B1b_canonical_pending_zero_count modulus A life offset true (i+1)]
  simp only [Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true]
  rw [pow_add]
  have hcount (Q : P → Prop) [DecidablePred Q] :
      (rho : ℂ) ^ ((Finset.univ : Finset P).filter Q).card =
      ∏ p : P, if Q p then (rho : ℂ) else 1 := by
    rw [← Finset.prod_filter]
    rw [Finset.prod_const]
  rw [hcount (fun p => memoryScheduleAfter (A p) (life p) i ∧
      memoryScheduleResidue (modulus p)
        (fun t => (offset t : ZMod (modulus p))) (life p) i = 0)]
  rw [hcount (fun p => memoryScheduleBefore (A p) (life p) (i+1) ∧
      memoryScheduleResidue (modulus p)
        (fun t => (offset t : ZMod (modulus p))) (life p) (i+1) = 0)]
  rw [← Finset.prod_mul_distrib]
  rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryB1bOriginalERhoPrime -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The EXACT two original OLD rho powers of each literal frozen E_i
scalar (post G_i and pre G_(i+1)) are the original per-prime
zero-residue schedule factors. No extra G/E orbit mass, no independent
probabilistic factor and NO normalization of rho is assumed. -/
theorem memory_source_frozen_E_rho_group_prime_product {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ) (rho : ℝ) (i : Fin N) :
    (∏ g : BG,
      (rho : ℂ) ^
        ((memoryCanonicalPendingList (bigMod g)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          false i.val).countP (fun z => z.2 = 0) +
         (memoryCanonicalPendingList (bigMod g)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          true (i.val+1)).countP (fun z => z.2 = 0))) =
    (∏ gp : PhysicalSourcePrime BP,
      memoryPrimitiveERhoPerPrimeFactor
        (bigMod gp.1)
        (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨gp.1,p⟩)
        (fun p => life ⟨gp.1,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val rho gp.2) := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  exact memory_source_E_rho_canonical_pending_as_prime_product
    (bigMod g)
    (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun p => life ⟨g,p⟩)
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    i.val rho
end Green64FullPhysicalE

end

end

