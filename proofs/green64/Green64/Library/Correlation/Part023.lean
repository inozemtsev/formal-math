module

public import Green64.Library.Correlation.Part022
public import Green64.Library.Correlation.Part018
public import Green64.Library.Correlation.Part012
public import Green64.Library.Correlation.Part013
public import Green64.Library.Correlation.Part019

@[expose] public section

/-!
# Correlation / Part023

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryFrozenSourceLifeRecovery -/

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

theorem memory_frozen_source_contributing_fitting_root_life
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod J ell m cap patterns k R)
    (hx : xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨0,by omega⟩)
    (hf : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2)
    (hn : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0) :
    let w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hn⟩
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    ∀ l : (g : BG) → BP g → MemoryLifespanChoice (2*R+1),
      (∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H g)
        (2*R+1) (fun p => memoryFiniteLifeErase (l g p))) →
      ∀ g p, l g p = life ⟨g,p⟩ := by
  dsimp only
  let w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hn⟩
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  have hy : physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true ⟨0,by omega⟩) := congrArg _ hx
  have hseen : (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset =
      memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) 0 := by
    rw [hx]
    exact memory_frozen_source_initial_seen SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated hs
  have hG (i : Fin (2*R+1)) := memory_frozen_source_fitting_trace_G_readout SP smallMod BP
    bigMod J ell m cap patterns ω life k hd.cap_saturated (2*R) 0 (by omega)
    _ _ xt.2 hy hseen hf i
  have hbefore (i : Fin (2*R+1)) : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap (H.before i.val) = physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
          patterns ω life k hd.cap_saturated true i) := by
    simpa only [H,w,memory_source_root_to_actual_witness_path,Nat.mod_eq_of_lt i.isLt,
      Nat.zero_add] using (hG i).1
  have hafter (i : Fin (2*R+1)) : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap (H.afterG i.val) = physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap
          patterns ω life k hd.cap_saturated false i) := by
    let jg : Fin (2*R+1) := ⟨i.val % (2*R+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
    have hjg : jg = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    change physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
        k (2*R) 0 _ _ xt.2 jg).2.1 = _
    rw [hjg]
    simpa only [Nat.zero_add] using (hG i).2.1
  have hω := memory_frozen_source_contributing_fitting_root_omega SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs xt hx hf hn
  intro l hl g p
  have hVac := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod J ell m cap
    patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let A := fun p : BP g => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  have hA : memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H g = A := by
    funext p
    rw [← memory_actual_frozen_visits_exact SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H g p]
    rw [hω]
  have hsl := memory_actual_finite_schedule_support SP smallMod BP bigMod J ell m cap
    patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H
    hd.big_injective hVac g (l g) (hl g) p
  rw [hA] at hsl
  apply memory_schedule_life_determined (bigMod g p) _ _ (A p) _ _ hsl (hs ⟨g,p⟩)
  all_goals
    intro i hi
    have hiN : i ≤ 2*R := by omega
    have hc := memory_actual_canonical_pending_readout SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H
      hd.big_injective hVac g (l g) (hl g) i hiN
    rw [hA] at hc
  · have hm := congrArg (fun out : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
        (out.2 g).2) (hbefore ⟨i,hi⟩)
    have ho : (Green64Fock.fockToList (((H.before i).2 g).2)).Perm
        (memoryCanonicalPendingList (bigMod g) A (fun p => life ⟨g,p⟩) offset true i) := by
      apply (Multiset.coe_eq_coe.mp hm).trans
      exact List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod BP bigMod
        J ell m cap patterns ω life k hd.cap_saturated true ⟨i,hi⟩ g)
    have hp := ((hc.1.symm.trans ho).map (fun z => z.1)).mem_iff (a := p)
    simpa only [memoryCanonicalPendingList,List.map_map,Function.comp_def,
      List.mem_map,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,
      Bool.true_eq_false,if_false,if_true,exists_eq_right] using hp
  · have hm := congrArg (fun out : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
        (out.2 g).2) (hafter ⟨i,hi⟩)
    have ho : (Green64Fock.fockToList (((H.afterG i).2 g).2)).Perm
        (memoryCanonicalPendingList (bigMod g) A (fun p => life ⟨g,p⟩) offset false i) := by
      apply (Multiset.coe_eq_coe.mp hm).trans
      exact List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod BP bigMod
        J ell m cap patterns ω life k hd.cap_saturated false ⟨i,hi⟩ g)
    have hp := ((hc.2.1.symm.trans ho).map (fun z => z.1)).mem_iff (a := p)
    simpa only [memoryCanonicalPendingList,List.map_map,Function.comp_def,
      List.mem_map,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,
      Bool.false_eq_true,if_false,if_true,exists_eq_right] using hp
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceProfileImage -/

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

theorem memory_frozen_source_nonzero_profile_in_forward_image
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
    ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod J ell m cap patterns k R,
      memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0 ∧
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) := by
  obtain ⟨xt,hbirth,hvac,hx,hf,hwt⟩ :=
    memory_frozen_source_nonzero_profile_contributing_root_exists SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hn
  have hp : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t :
          ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod J ell m patterns
    ω life k q hp
  have hω := memory_frozen_source_contributing_fitting_root_omega SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs xt hx hf hwt
  have hL := memory_frozen_source_contributing_fitting_root_life SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs xt hx hf hwt
  refine ⟨xt,hwt,?_⟩
  unfold memorySourceRootFrozenProfile
  rw [dif_pos hwt]
  apply congrArg some
  apply Prod.ext
  · exact hω
  · funext gp
    exact hL _ (Classical.choose_spec (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective ⟨xt,hwt⟩)) gp.1 gp.2

/-- Profiles outside the original forward image have ZERO literal scalar.
This is proved from nonzero reconstruction, not postulated as a support restriction. -/
theorem memory_frozen_source_profile_outside_image_zero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (hnot : ∀ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt ≠ some a) :
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 *
    (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (2*R+1) (a.2 gp) : ℝ) = 0 := by
  by_contra hn
  obtain ⟨xt,hwt,hprofile⟩ := memory_frozen_source_nonzero_profile_in_forward_image
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd a.1 a.2 hn
  exact hnot xt hprofile
end Green64FullPhysicalE

end

end

/-! ## MemoryGlobalActualFibreWeight -/

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
/-- The unchanged assignment target, NOT a proved theorem. Quantification
includes every true terminal profile, including profiles absent from the
actual contributing-root image. No reconstruction or mass premise is added. -/
def MemoryGlobalActualFibreWeight
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : Prop :=
  ∀ hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R,
  ∀ a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R,
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 *
    (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (2*R+1) (a.2 gp) : ℝ)
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFittingProfileSound -/

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

/-- Soundness, for EVERY nonzero ORIGINAL source root in the fitting carrier.
The original canonical lifespan choose is recovered, not replaced by an
arbitrary alternate frozen life. All such roots map to EXACTLY their claimed
omega/life profile; no wrong-profile contribution in this fitted sector. -/
theorem memory_source_fitting_root_profile_sound
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
          (2*R+1) (life gp) : ℝ) ≠ 0)
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod J ell m cap patterns k R)
    (hx : xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨0,by omega⟩)
    (hf : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2)
    (hw : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0) :
    memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) := by
  have hp : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod J ell m patterns
    ω life k q hp
  have hω := memory_frozen_source_contributing_fitting_root_omega SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs xt hx hf hw
  have hL := memory_frozen_source_contributing_fitting_root_life SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs xt hx hf hw
  unfold memorySourceRootFrozenProfile
  rw [dif_pos hw]
  apply congrArg some
  apply Prod.ext
  · exact hω
  · funext gp
    exact hL _ (Classical.choose_spec (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective ⟨xt,hw⟩)) gp.1 gp.2
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFittingProfileFilter -/

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

/-- Under an ORIGINAL nonzero frozen scalar, the entire fixed-initial
fitting-weight sum may be intersected with the ACTUAL source root forward
profile, with exact equality. This is one-way soundness; it does NOT say
every original source root of that profile is fitting. -/
theorem memory_source_fitting_root_mass_has_correct_original_profile
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
    let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨0,by omega⟩
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
        J ell m cap patterns k R
    memorySourceFixedInitialFittingRootSum SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R ω life hd.cap_saturated x0 =
    ∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        if xt.1 = x0 ∧
          memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
            ω life k hd.cap_saturated (2*R) 0
            (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
            (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2
        then memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0
      else 0 := by
  dsimp only
  classical
  unfold memorySourceFixedInitialFittingRootSum
  apply Finset.sum_congr rfl
  intro xt hxt
  by_cases hf : xt.1 =
        memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true ⟨0,by omega⟩ ∧
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2
  · by_cases hw : memorySourceRootIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0
    · have hs := memory_source_fitting_root_profile_sound SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hn
        xt hf.1 hf.2 hw
      simp only [hf, hs, ite_true]
    · have hz : memorySourceRootIndexedWeight SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R xt = 0 :=
        not_ne_iff.mp hw
      simp only [hf, hz, ite_self]
  · simp only [hf, ite_false]
    split_ifs <;> rfl
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFittingNoDoubleCount -/

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

/-- A nonzero ORIGINAL root cannot belong to two different genuine fitting
omega/life profiles whose literal frozen coefficients are nonzero.
This is uniqueness on the fitting sector, not yet exhaustiveness of the sector. -/
theorem memory_source_fitting_nonzero_profile_no_double_count
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω₁ ω₂ : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life₁ life₂ : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn₁ : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω₁ *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω₁ k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω₁ gp)
          (2*R+1) (life₁ gp) : ℝ) ≠ 0)
    (hn₂ : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω₂ *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω₂ k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω₂ gp)
          (2*R+1) (life₂ gp) : ℝ) ≠ 0)
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod J ell m cap patterns k R)
    (hw : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0)
    (hx₁ : xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω₁ life₁ k hd.cap_saturated true ⟨0,by omega⟩)
    (hx₂ : xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω₂ life₂ k hd.cap_saturated true ⟨0,by omega⟩)
    (hf₁ : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω₁ life₁ k hd.cap_saturated (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2)
    (hf₂ : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω₂ life₂ k hd.cap_saturated (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2) :
    (ω₁, life₁) = (ω₂, life₂) := by
  have h1 := memory_source_fitting_root_profile_sound SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω₁ life₁ hn₁ xt hx₁ hf₁ hw
  have h2 := memory_source_fitting_root_profile_sound SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω₂ life₂ hn₂ xt hx₂ hf₂ hw
  have h : some (ω₁,life₁) = some (ω₂,life₂) := h1.symm.trans h2
  exact Option.some.inj h
end Green64FullPhysicalE

end

end

/-! ## MemorySourceFittingResidualDecomposition -/

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

/-- The precise SOURCE root debt excluded by the canonical fitting filter.
This is an ACTUAL finite root sum, not a postulated multiplicity or weight.
It includes all original non-fitting indexed paths of the claimed omega/life
profile, with their unchanged complex scalar (possibly zero). -/
noncomputable def memorySourceRootUnfittedResidualAt
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1)) : ℂ :=
  letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated true ⟨0,by omega⟩
  ∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
    if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
       q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) ∧
       ¬ (xt.1 = x0 ∧
          memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
            ω life k hd.cap_saturated (2*R) 0
            (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
            (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2)
    then memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt else 0

/-- The unproved global fibre can be split WITHOUT LOSS, even for an arbitrary
complex-valued original source coefficient. The first term is recursively
disintegrated above, and the second is the exact remaining SOURCE debt. -/
theorem memory_source_original_fibre_fitting_plus_actual_residual
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
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
        J ell m cap patterns k R
    let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨0,by omega⟩
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
          memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
            q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    memorySourceFixedInitialFittingRootSum SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R ω life hd.cap_saturated x0 +
    memorySourceRootUnfittedResidualAt SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd ω life := by
  classical
  dsimp only
  rw [memory_source_fitting_root_mass_has_correct_original_profile SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hn]
  unfold memorySourceRootUnfittedResidualAt
  dsimp only
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro xt hxt
  by_cases hp : memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life)
  · by_cases hf : xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod
      J ell m cap patterns ω life k hd.cap_saturated true ⟨0,by omega⟩ ∧
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2
    · simp [hp,hf]
    · simp only [hp, ite_true, hf, ite_false, zero_add]
      simp
  · simp [hp]
end Green64FullPhysicalE

end

end

/-! ## MemoryBActualCanonicalProjection -/

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

/-- For the ACTUAL dependent original G/E path, its full projected
G-input and G-output agree with its own original frozen omega and finite
life at every visit. This carries all OLD Fock atoms, not merely active
prime sets. -/
theorem memory_actual_frozen_both_G_projections
    (q rho : ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N)
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap (H.afterG N)) = 1)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hl : ∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g) (N+1)
      (fun p => memoryFiniteLifeErase (life ⟨g,p⟩)))
    (i : Fin (N+1)) :
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap (H.before i.val) =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap true i) ∧
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap (H.afterG i.val) =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap false i) := by
  dsimp only
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig mu k N H
  have hOff (t : ℕ) (ht : t < N+1) :
      physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H t =
      memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t :=
    (memory_actual_frozen_offset_exact SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H t (by omega)).symm
  have hA (g : BG) :
      memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H g =
      (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩) := by
    funext p
    exact (memory_actual_frozen_visits_exact SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H g p).symm
  have hFock (g : BG) :
      (Green64Fock.fockToList (((H.before i.val).2 g).2)).Perm
        (memoryCanonicalPendingList (bigMod g)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          true i.val) ∧
      (Green64Fock.fockToList (((H.afterG i.val).2 g).2)).Perm
        (memoryCanonicalPendingList (bigMod g)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          false i.val) := by
    have hp := memory_actual_canonical_pending_readout SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H hnum hVac g
      (fun p => life ⟨g,p⟩) (hl g) i.val (by omega)
    dsimp only at hp
    rw [hA g] at hp
    have hb := memory_canonical_pending_offset_congr (bigMod g)
      (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun p => life ⟨g,p⟩)
      (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      hOff true i.val i.isLt
    have ha := memory_canonical_pending_offset_congr (bigMod g)
      (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun p => life ⟨g,p⟩)
      (physicalActualOffset SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      hOff false i.val i.isLt
    exact ⟨hp.1.trans (List.Perm.of_eq hb), hp.2.1.trans (List.Perm.of_eq ha)⟩
  have hop := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod (J+ell) cap q rho N i.val Vbig mu
    (H.before i.val) (H.afterG i.val) (H.ghost i.val)
    (H.G_nonzero i.val (by omega))).1
  constructor
  · apply Prod.ext
    · rfl
    · funext g
      apply Prod.ext
      · rfl
      · exact Multiset.coe_eq_coe.mpr
          ((hFock g).1.trans (List.Perm.of_eq
            (memory_frozen_source_physical_pending SP smallMod BP bigMod J ell m
              cap patterns ω life k hcap true i g).symm))
  · apply Prod.ext
    · exact hop.1.symm
    · funext g
      apply Prod.ext
      · exact (hop.2 g).symm
      · exact Multiset.coe_eq_coe.mpr
          ((hFock g).2.trans (List.Perm.of_eq
            (memory_frozen_source_physical_pending SP smallMod BP bigMod J ell m
              cap patterns ω life k hcap false i g).symm))
end Green64FullPhysicalE

end

end

/-! ## MemoryBForwardFitsFromReadout -/

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

/-- Reverse of canonical fitting readout: all ACTUAL indexed trace data
at each visit imply membership in the original recursively dependent Fits
predicate. This neither assumes a weighted fibre equality nor changes
the original indexed path carrier. -/
theorem memory_source_full_readouts_imply_original_fits {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ) (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (remaining start : ℕ) (heq : start+remaining=N)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (hBefore : ∀ j : Fin (remaining+1),
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
          k remaining start y seen t j).1) =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true ⟨start+j.val,by omega⟩))
    (hAfter : ∀ j : Fin (remaining+1),
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
          k remaining start y seen t j).2.1) =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap false ⟨start+j.val,by omega⟩))
    (hFrame : ∀ j : Fin remaining,
      let e := physicalOrientedTraceEWitness SP smallMod BP bigMod J ell m cap patterns
        k remaining start y seen t j
      memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns e.1 e.2 =
        ω.2.2 ⟨start+j.val,by omega⟩)
    (hSeen : ∀ j : Fin (remaining+1),
      physicalOrientedTraceSeen SP smallMod BP bigMod J ell m cap patterns
        k remaining start y seen t j =
      memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (start+j.val))
    (hy : y = physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap true ⟨start,by omega⟩))
    (hs : seen = memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) start) :
    memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap remaining start y seen t := by
  induction remaining generalizing start y seen with
  | zero =>
    have he : start = N := by omega
    have hh := hAfter (0 : Fin (0+1))
    dsimp only [memoryFrozenSourceIndexedTraceFits]
    exact ⟨he, by simpa [physicalOrientedTraceGWitness, Fin.val_zero,he] using hh⟩
  | succ r ih =>
    rcases t with ⟨ab,tail⟩
    have hi : start < N := by omega
    have hG := hAfter (0 : Fin (r+2))
    have hF := hFrame (0 : Fin (r+1))
    have hOut0 := physical_oriented_trace_all_E_outputs SP smallMod BP bigMod
      J ell m cap patterns k (r+1) start y seen ⟨ab,tail⟩ (0 : Fin (r+1))
    have hB1 := hBefore (Fin.succ (0 : Fin (r+1)))
    have hS1 := hSeen (Fin.succ (0 : Fin (r+1)))
    have hOut :
      physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign start) k ab.val =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true ⟨start+1,by omega⟩) := by
      calc
        _ = physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          ((physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
            k (r+1) start y seen ⟨ab,tail⟩ (Fin.succ (0 : Fin (r+1)))).1) :=
              hOut0.symm
        _ = _ := by simpa only [Fin.val_succ,Fin.val_zero,Nat.add_zero] using hB1
    have hNext :
      physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
        seen ab.val =
      memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (start+1) := by
      have hh := hS1
      simp only [physicalOrientedTraceSeen,Fin.cases_succ,Fin.val_succ,
        Fin.val_zero] at hh
      have hz : physicalOrientedTraceSeen SP smallMod BP bigMod
          J ell m cap patterns k r (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
            J ell m cap patterns (physicalAlternatingSign start) k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val) tail (0 : Fin (r+1)) =
          physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val := by
        cases r <;> rfl
      exact hz.symm.trans hh
    have hBt (j : Fin (r+1)) :
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
          k r (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
            (physicalAlternatingSign start) k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val) tail j).1) =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true ⟨start+1+j.val,by omega⟩) := by
      have hh := hBefore (Fin.succ j)
      simpa only [physicalOrientedTraceGWitness,Fin.cases_succ,Fin.val_succ,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    have hAt (j : Fin (r+1)) :
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        ((physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
          k r (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
            (physicalAlternatingSign start) k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val) tail j).2.1) =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap false ⟨start+1+j.val,by omega⟩) := by
      have hh := hAfter (Fin.succ j)
      simpa only [physicalOrientedTraceGWitness,Fin.cases_succ,Fin.val_succ,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    have hFt (j : Fin r) :
      let e := physicalOrientedTraceEWitness SP smallMod BP bigMod J ell m cap patterns
        k r (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
          (physicalAlternatingSign start) k ab.val)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
          seen ab.val) tail j
      memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns e.1 e.2 =
        ω.2.2 ⟨start+1+j.val,by omega⟩ := by
      have hh := hFrame (Fin.succ j)
      simpa only [physicalOrientedTraceEWitness, Fin.cases_succ,Fin.val_succ,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    have hSt (j : Fin (r+1)) :
      physicalOrientedTraceSeen SP smallMod BP bigMod J ell m cap patterns
        k r (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
          (physicalAlternatingSign start) k ab.val)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
          J ell m cap patterns seen ab.val) tail j =
      memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (start+1+j.val) := by
      have hh := hSeen (Fin.succ j)
      simpa only [physicalOrientedTraceSeen,Fin.cases_succ,Fin.val_succ,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    refine ⟨hi,?_,?_,hOut,hNext,?_⟩
    · simpa only [physicalOrientedTraceGWitness,Fin.cases_zero,Fin.val_zero,
        Nat.add_zero] using hG
    · simpa only [physicalOrientedTraceEWitness,Fin.cases_zero,Fin.val_zero,
        Nat.add_zero] using hF
    · exact ih (start+1) (by omega) _ _ tail hBt hAt hFt hSt hOut hNext
end Green64FullPhysicalE

end

end

/-! ## MemoryBOriginalRootFits -/

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

/-- SOURCE-ROOT EXHAUSTIVENESS for the ORIGINAL recursively dependent Fits
predicate: every nonzero original root lies in the canonical fitting trace
of its OWN literal original omega and Classical.choose finite lifespan. No
additional support assumption or alternative profile is imposed. -/
theorem memory_source_contributing_root_actual_fits
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R) :
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k (2*R) H
    let l := Classical.choose (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective w)
    let life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1) :=
      fun gp => l gp.1 gp.2
    memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
      w.val.2 := by
  dsimp only
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig mu k (2*R) H
  let l := Classical.choose (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  let life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1) :=
    fun gp => l gp.1 gp.2
  have hl : ∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H g) (2*R+1)
      (fun p => memoryFiniteLifeErase (life ⟨g,p⟩)) :=
    Classical.choose_spec (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective w)
  have hv := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  have hFull (i : Fin (2*R+1)) :=
    memory_actual_frozen_both_G_projections SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H
      hd.cap_saturated hd.big_injective hv life hl i
  have hIndexG (i : Fin (2*R+1)) :
      (⟨i.val % (2*R+1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (2*R+1)) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hIndexE (i : Fin (2*R)) :
      (⟨i.val % (2*R), Nat.mod_lt _ (by have h := hd.R_pos; omega)⟩ :
        Fin (2*R)) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hBefore (i : Fin (2*R+1)) :
      H.before i.val = (physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap
          w.val.1).toFinset w.val.2 i).1 := by
    change (physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2
      ⟨i.val % (2*R+1), Nat.mod_lt _ (Nat.succ_pos _)⟩).1 = _
    rw [hIndexG i]
  have hAfterG (i : Fin (2*R+1)) :
      H.afterG i.val = (physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap
          w.val.1).toFinset w.val.2 i).2.1 := by
    change (physicalOrientedTraceGWitness SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2
      ⟨i.val % (2*R+1), Nat.mod_lt _ (Nat.succ_pos _)⟩).2.1 = _
    rw [hIndexG i]
  have hB (i : Fin (2*R+1)) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
        k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap
          w.val.1).toFinset w.val.2 i).1) =
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true i) := by
    have hh := (hFull i).1
    rw [hBefore i] at hh
    exact hh
  have hA (i : Fin (2*R+1)) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ((physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
        k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap
          w.val.1).toFinset w.val.2 i).2.1) =
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated false i) := by
    have hh := (hFull i).2
    rw [hAfterG i] at hh
    exact hh
  have hEInput (i : Fin (2*R)) :
      H.beforeE i.val = (physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap
          w.val.1).toFinset w.val.2 i).1 := by
    change (physicalOrientedTraceEWitness SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2
      ⟨i.val % (2*R), Nat.mod_lt _ (by have h := hd.R_pos; omega)⟩).1 = _
    rw [hIndexE i]
  have hEPair (i : Fin (2*R)) :
      (⟨H.beforeE i.val,H.edge i.val⟩ :
        PhysicalOrientedEWitnessIndex SP smallMod BP bigMod J ell m cap patterns) =
      physicalOrientedTraceEWitness SP smallMod BP bigMod
        J ell m cap patterns k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap
          w.val.1).toFinset w.val.2 i := by
    change (physicalOrientedTraceEWitness SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2
      ⟨i.val % (2*R), Nat.mod_lt _ (by have h := hd.R_pos; omega)⟩) = _
    rw [hIndexE i]
  have hF (i : Fin (2*R)) :
    let e := physicalOrientedTraceEWitness SP smallMod BP bigMod J ell m cap patterns
      k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2 i
    memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns e.1 e.2 =
      ω.2.2 i := by
    change _ = memoryPrimitiveEFrameOf SP smallMod BP bigMod
      J ell m cap patterns (H.beforeE i.val) (H.edge i.val)
    exact (congrArg (fun e : PhysicalOrientedEWitnessIndex
        SP smallMod BP bigMod J ell m cap patterns =>
      memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns
        e.1 e.2) (hEPair i)).symm
  have hSeenIndex (i : Fin (2*R+1)) :
      H.seen i.val = physicalOrientedTraceSeen SP smallMod BP bigMod
        J ell m cap patterns k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap
          w.val.1).toFinset w.val.2 i := by
    change physicalOrientedTraceSeen SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2
      ⟨i.val % (2*R+1), Nat.mod_lt _ (Nat.succ_pos _)⟩ = _
    rw [hIndexG i]
  have hSeen (i : Fin (2*R+1)) :
    physicalOrientedTraceSeen SP smallMod BP bigMod J ell m cap patterns
      k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2 i =
    memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) i.val := by
    have hh := memory_actual_global_seenG_exact SP smallMod BP bigMod J ell m
      cap patterns q rho Vbig mu k (2*R) H hd.big_injective
      (fun g p => life ⟨g,p⟩) hl i.val (by omega)
    have hVisits :
        (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m
          cap patterns q rho Vbig mu k (2*R) H) =
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns
          ω ⟨g,p⟩) := by
      funext g p
      exact (memory_actual_frozen_visits_exact SP smallMod BP bigMod J ell m
        cap patterns q rho Vbig mu k (2*R) H g p).symm
    rw [hVisits] at hh
    rw [hSeenIndex i] at hh
    exact hh
  have hy :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1 =
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩) := by
    have hfirst := physical_oriented_trace_first_G_projection
      SP smallMod BP bigMod J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2
    have h0 : (⟨0,by omega⟩ : Fin (2*R+1)) = (0 : Fin (2*R+1)) :=
      Fin.ext (by simp)
    have hb0 := hB (⟨0,by omega⟩ : Fin (2*R+1))
    rw [h0] at hb0
    have hh := hfirst.symm.trans hb0
    simpa only [← h0] using hh
  have hs :
    (physicalInitialBirths SP smallMod BP bigMod J ell cap
      w.val.1).toFinset =
    memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns
        ω ⟨g,p⟩) (fun g p => life ⟨g,p⟩) 0 := by
    have hfirst := physical_oriented_trace_first_seen
      SP smallMod BP bigMod J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2
    have h0 : (⟨0,by omega⟩ : Fin (2*R+1)) = (0 : Fin (2*R+1)) :=
      Fin.ext (by simp)
    have hs0 := hSeen (⟨0,by omega⟩ : Fin (2*R+1))
    rw [h0] at hs0
    have hh := hfirst.symm.trans hs0
    simpa only [Fin.val_zero,Nat.zero_add] using hh
  exact memory_source_full_readouts_imply_original_fits SP smallMod BP bigMod
    J ell m cap patterns ω life k hd.cap_saturated (2*R) 0 (by omega)
    _ _ w.val.2 (by simpa only [Nat.zero_add] using hB)
    (by simpa only [Nat.zero_add] using hA)
    (by simpa only [Nat.zero_add] using hF)
    (by simpa only [Nat.zero_add] using hSeen) hy hs
end Green64FullPhysicalE

end

end

/-! ## MemoryBOriginalRootInitial -/

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

/-- The original full ordered Hilbert/Fock initial state equals the
canonical actual frozen state. This is stronger than equality of the
Fock projection: the genuine root vacuum makes its ordered representative
unique. No uniform orbit assertion or extra initial mass assumption. -/
theorem memory_source_contributing_root_canonical_initial_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R) :
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k (2*R) H
    let l := Classical.choose (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective w)
    let life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1) :=
      fun gp => l gp.1 gp.2
    w.val.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m
      cap patterns ω life k hd.cap_saturated true ⟨0,by omega⟩ := by
  dsimp only
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig mu k (2*R) H
  let l := Classical.choose (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  let life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1) :=
    fun gp => l gp.1 gp.2
  have hl : ∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H g) (2*R+1)
      (fun p => memoryFiniteLifeErase (life ⟨g,p⟩)) :=
    Classical.choose_spec (memory_source_root_finite_life_readout SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd.R_pos hd.big_injective w)
  have hv := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  have hh := (memory_actual_frozen_both_G_projections SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k (2*R) H
    hd.cap_saturated hd.big_injective hv life hl (⟨0,by omega⟩ : Fin (2*R+1))).1
  have he : H.before 0 = w.val.1 :=
    memory_source_root_first_G_state_exact SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R w
  rw [he] at hh
  exact (memory_source_root_first_Fock_unique SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    w.val w.property
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨0,by omega⟩) hh.symm).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryBOriginalFibreExhaustive -/

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

/-- NO NON-FITTING ORIGINAL ROOTS: every genuinely nonzero root of every
original profile, INCLUDING profiles with zero frozen coefficient,
has exactly its canonical initial ordered Fock state and satisfies
the original recursively dependent frozen Fits predicate.

The profile is exactly memorySourceRootFrozenProfile, with the SOURCE
Classical.choose lifespan, unchanged source coefficients and source weight. -/
theorem memory_source_original_nonzero_profile_exhaustive
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R)
    (hw : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0)
    (hp : memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd xt = some a) :
    let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      a.1 a.2 k hd.cap_saturated true ⟨0,by omega⟩
    xt.1 = x0 ∧
    memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      a.1 a.2 k hd.cap_saturated (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset
      xt.2 := by
  dsimp only
  let w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hw⟩
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig mu k (2*R) H
  let l := Classical.choose (memory_source_root_finite_life_readout SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd.R_pos hd.big_injective w)
  let life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1) :=
    fun gp => l gp.1 gp.2
  have hpf : memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) := by
    unfold memorySourceRootFrozenProfile
    rw [dif_pos hw]
  have heq : (ω,life) = a := Option.some.inj (hpf.symm.trans hp)
  have hInitial := memory_source_contributing_root_canonical_initial_exact
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R hd w
  have hFits := memory_source_contributing_root_actual_fits
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R hd w
  change xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m
    cap patterns a.1 a.2 k hd.cap_saturated true ⟨0,by omega⟩ ∧
    memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      a.1 a.2 k hd.cap_saturated (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2
  rw [← heq]
  exact ⟨hInitial,hFits⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryBUnfittedResidualZero -/

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

/-- The previous EXACT-source non-fitting residual vanishes for EVERY
original frozen profile, whether its RHS frozen scalar is zero or nonzero.
Proof is POINTWISE on original indexed-root witnesses, no positivity,
absolute values, cancellation assumption or invented surrogate carrier. -/
theorem memory_source_original_unfitted_residual_zero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1)) :
    memorySourceRootUnfittedResidualAt SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd ω life = 0 := by
  classical
  unfold memorySourceRootUnfittedResidualAt
  dsimp only
  apply Finset.sum_eq_zero
  intro xt hxt
  split_ifs with h
  · by_cases hz : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m
        cap patterns q rho Vsmall Vbig Knu zeta theta k R xt = 0
    · exact hz
    · have hf := memory_source_original_nonzero_profile_exhaustive
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd (ω,life) xt hz h.1
      exact False.elim (h.2 hf)
  · rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryBActualFibreFittingExact -/

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

/-- EXACT full original root fibre equals original fixed-initial true
dependent fitting trace mass for every nonzero literal source profile.
There is NO omitted physical root branch and no artificial normalization
factor; the remaining task is evaluation of this fully indexed mass. -/
theorem memory_source_original_nonzero_profile_fibre_eq_actual_fitting
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
    memorySourceFixedInitialFittingRootSum SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R ω life hd.cap_saturated
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩) := by
  rw [memory_source_original_fibre_fitting_plus_actual_residual SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd
    ω life hn]
  rw [memory_source_original_unfitted_residual_zero SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life]
  simp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1OriginalRootGEProduct -/

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
theorem memory_source_nonzero_root_fibre_exact_GE_product
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
      memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod J ell m cap patterns
        ω life hd.cap_saturated q rho Vsmall Vbig
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        Knu zeta theta k i) *
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hd.cap_saturated q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k ⟨2*R,Nat.lt_succ_self (2*R)⟩ := by
  classical
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m
    cap patterns ω life k hd.cap_saturated true ⟨0,by omega⟩
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  have hprime : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q hprime
  have hSeen := memory_frozen_source_initial_seen SP smallMod BP bigMod
    J ell m cap patterns ω life k hd.cap_saturated hs
  have hBirth := memory_frozen_source_initial_births_nodup SP smallMod
    BP bigMod J ell m cap patterns ω life k hd.cap_saturated hd.big_injective
  have hBirth0 : (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).Nodup :=
    hBirth
  have hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) = 1 := by
    apply if_pos
    exact (memory_frozen_source_physical_vacua SP smallMod BP bigMod
      J ell m cap patterns ω life k hd.cap_saturated).1
  have hRoot := memory_source_original_nonzero_profile_fibre_eq_actual_fitting
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  have hInitial := memory_source_fixed_initial_fitting_root_factorization
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R ω life hd.cap_saturated x0
  have hProd := memory_source_full_canonical_fitting_trace_product SP smallMod
    BP bigMod J ell m cap patterns ω life hd.cap_saturated
    q rho Vsmall Vbig mu Knu zeta theta k
  rw [hRoot, hInitial]
  simp only [hVac, star_one, mul_one, hBirth0, ite_true]
  rw [hSeen]
  change (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
    (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x0 : ℂ) *
    memorySourceCanonicalFittingTail SP smallMod BP bigMod J ell m cap patterns
      ω life hd.cap_saturated q rho Vsmall Vbig mu Knu zeta theta k
      (0 : Fin (2*R+1)) = _
  rw [hProd]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1CanonicalEOutput -/

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

/-- Original source E canonical output built from literal independent
residue lift is EXACTLY the frozen physical Fock output at the next
visit, with all repeated Fock atoms/multiplicities retained. This is a
source-specific identity, not a transition-coefficient hypothesis. -/
theorem memory_source_frozen_E_output_is_true_next_projection {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ) (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin N) :
    memoryPrimitiveECanonicalOutput SP smallMod BP bigMod J ell
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.succ) =
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap true i.succ) := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · have hh := congrArg
        (fun v : List (Green64Fock.Atom (BP g) (bigMod g)) =>
          (v : Multiset (Green64Fock.Atom (BP g) (bigMod g))))
        (memory_frozen_source_physical_pending SP smallMod BP bigMod
          J ell m cap patterns ω life k hcap true i.succ g)
      simpa only [memoryPrimitiveECanonicalOutput, physicalFockProjection,
        Green64Fock.fockMultiset, Green64Fock.fockToList,
        Fin.val_succ] using hh.symm
end Green64FullPhysicalE

end

end

/-! ## MemoryB1MatchingHeadG -/

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

/-- A matching HEAD of the ACTUAL original dependent GE indexed carrier
is automatically in the ORIGINAL canonical fixed-input G fibre. There is
no assumption that its G coefficient is nonzero: all eligible zero heads
are retained, and no independent/uniform Fock orbit is substituted. -/
theorem memory_source_matching_head_in_primitive_G_fibre {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (k : ℤ) (i : Fin N)
    (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val))
    (hh : memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap i.val
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val) ab) :
    (ab.val.1.2.1, ab.val.1.2.2) ∈
      memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val ab.val.1.1 := by
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap true i.castSucc)
  let seen := memorySeenBeforeGValues BP bigMod
    (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun g p => life ⟨g,p⟩) i.val
  obtain ⟨hi, hpost, hframe, hout, hnext⟩ := hh
  have hGleg := (Finset.mem_sigma.mp ab.property).1
  have hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap ab.val.1.1 =
      y := (Finset.mem_filter.mp hGleg).2.1
  have hb := (Finset.mem_filter.mp hGleg).2.2
  unfold memoryPrimitiveGFixedInputFibre
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rfl
    · exact hb
  · intro g
    have he := congrArg (fun z : FullPhysicalOutput SP smallMod BP bigMod
      (J+ell) => (z.2 g).2) hpost
    have hF : (Green64Fock.fockToList ((ab.val.1.2.1.2 g).2)).Perm
        (Green64Fock.fockToList (((memoryFrozenSourcePhysicalState
          SP smallMod BP bigMod J ell m cap patterns ω life k hcap
          false i.castSucc).2 g).2)) :=
      Multiset.coe_eq_coe.mp he
    have hp := memory_frozen_source_physical_pending SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap false i.castSucc g
    exact hF.trans (List.Perm.of_eq hp)
end Green64FullPhysicalE

end

end

/-! ## MemoryB1MatchingHeadGE -/

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

set_option maxHeartbeats 750000

/-- On a NONZERO actual original G branch of a fitting source GE head,
the TRUE dependent E witness belongs to the predecessor exact original
fixed-frame E fibre. This recovers the intermediate ghost seen register
from the source G inverse; the final output is the actual E output, not a
surrogate independent Fock sample. All old-index injections and original
Nu/auxiliary/four endpoint permutations are preserved by the membership. -/
theorem memory_source_matching_head_G_nonzero_in_original_E_fibre
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
    (i : Fin (2*R))
    (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val))
    (hh : memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated i.val
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val) ab)
    (hGnz : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) i.val Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      ab.val.1.1 ab.val.1.2.1 ab.val.1.2.2 ≠ 0) :
    ab.val.2.2 ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod
      J ell m cap patterns
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val ab.val.2.1
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k
        (memory_frozen_source_profile_support SP smallMod BP bigMod
          J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn))
        i.succ)
      (physicalAlternatingSign i.val) k (ω.2.2 i) := by
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true i.castSucc)
  let seen := memorySeenBeforeGValues BP bigMod
    (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun g p => life ⟨g,p⟩) i.val
  have hcarrier := Finset.mem_sigma.mp ab.property
  have hGmem := memory_source_matching_head_in_primitive_G_fibre
    SP smallMod BP bigMod J ell m cap patterns
    ω life hd.cap_saturated k i ab hh
  have hxin : physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ab.val.1.1 = y := (Finset.mem_filter.mp hcarrier.1).2.1
  have hGread := memory_frozen_source_actual_G_slice_readout
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hs
    (left_ne_zero_of_mul hn) i ab.val.1.1 hxin
    (ab.val.1.2.1,ab.val.1.2.2) hGmem hGnz
  have hEraw := hcarrier.2
  have hEproj := (Finset.mem_filter.mp hEraw).2.1
  obtain ⟨hi,hpost,hframe,hout,hnext⟩ := hh
  unfold memoryPrimitiveEFixedFrameFibre
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · rw [hEproj, ← hGread.2]
    exact hEraw
  · exact hframe
  · change physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign i.val) k ab.val = _
    rw [hout]
    exact (memory_source_frozen_E_output_is_true_next_projection SP smallMod BP
      bigMod J ell m cap patterns ω life k hd.cap_saturated hs i).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryB1ESeenExact -/

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

/-- True original E fresh-birth register, for every actual E witness in
its ORIGINAL canonical fixed-frame source fibre, is exactly the source
chronological next-seen register. The ordered E OLD injections are
recovered through the SOURCE full inverse, not by assuming uniqueness. -/
theorem memory_source_actual_E_fixed_frame_seen_exact
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
    (i : Fin (2*R))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated false i.castSucc))
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (hz : z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod
      J ell m cap patterns
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val x
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k
        (memory_frozen_source_profile_support SP smallMod BP bigMod
          J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn))
        i.succ)
      (physicalAlternatingSign i.val) k (ω.2.2 i)) :
    memoryBornBeforeValues BP bigMod (fun g p => life ⟨g,p⟩) (i.val+1) ∪
      (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset =
    memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) (i.val+1) := by
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  have hact (g : BG) : (x.2 g).1 =
      Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) := by
    exact congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).1) hx
  have hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset false i.val) := by
    intro g
    have hm := congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).2) hx
    exact (Multiset.coe_eq_coe.mp hm).trans (List.Perm.of_eq
      (memory_frozen_source_physical_pending SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated false i.castSucc g))
  have hA0 : ∀ g p, i.val ∈ A g p ↔ ∃ j, (x.2 g).1 j = p := by
    intro g p
    rw [hact g]
    exact memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.castSucc g p
  have hA1 : ∀ g p, i.val+1 ∈ A g p ↔
      ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.succ g p
  have hxin : ∀ g, Function.Injective (x.2 g).1 := by
    intro g; rw [hact g]; exact Green64SmallHaar.marks_injective _ _ _
  have hcanonical := (memory_source_primitive_E_fixed_frame_mem_iff SP smallMod
    BP bigMod J ell m cap patterns A L offset i.val
    (fun g p => hs ⟨g,p⟩) x hxin hA0 hOld iy hA1
    (physicalAlternatingSign i.val) k (ω.2.2 i) z).mp hz
  have hf := memory_frozen_source_lift_frame_compatible SP smallMod BP bigMod
    J ell m patterns ω life k hs q Vsmall Vbig Knu zeta theta
    (left_ne_zero_of_mul hn) i
  have hshared : ∀ g j, j ∈ sourceBigShared J ell m
      (patterns (ω.2.2 i).1.1) g →
      (x.2 g).1 ((ω.2.2 i).2.1 g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
        ((ω.2.2 i).2.2.1 g j) := by
    intro g j hj
    rw [hact g]
    exact ((Finset.mem_filter.mp hf).2.2.2.2.1 g).2 j hj
  have hcont : ∀ g j l, (x.2 g).1 ((ω.2.2 i).2.1 g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
        ((ω.2.2 i).2.2.1 g l) →
      j ∈ sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g ∧ l = j := by
    intro g j l he
    rw [hact g] at he
    exact memory_source_active_continuation_is_shared SP smallMod BP bigMod J ell m
      hd.small_prime hd.big_prime hd.big_injective hd.disjoint
      (patterns (ω.2.2 i).1.1) (ω.2.2 i).1.2 ix iy
      (Finset.mem_filter.mp hf).2.2.1
      (ω.2.2 i).2.1 (ω.2.2 i).2.2.1 (ω.2.2 i).2.2.2.1
      (physicalAlternatingSign i.val) k (Finset.mem_filter.mp hf).2.1
      hd.k_ne hd.big_above_k (Finset.mem_filter.mp hf).2.2.2.2.1 g j l he
  rw [hcanonical.1]
  exact memory_primitive_E_seen_update SP smallMod BP bigMod
    J ell m cap patterns A L offset i (fun g p => hs ⟨g,p⟩)
    x hOld iy hA0 hA1 (ω.2.2 i).1.1 (ω.2.2 i).1.2
    (ω.2.2 i).2.1 (ω.2.2 i).2.2.1
    (ω.2.2 i).2.2.2.1 (ω.2.2 i).2.2.2.2
    hshared hcont
end Green64FullPhysicalE

end

end

/-! ## MemoryB1MatchingHeadConverse -/

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

/-- Reverse source GE identification: on a TRUE nonzero original G branch,
membership of the ACTUAL G and E witnesses in BOTH original canonical
fixed-source fibres implies that the SAME original GE-indexed witness
satisfies the full recursive frozen fitting-head predicate. The original
source output, frame and chronological seen are derived, not assumed. -/
theorem memory_source_canonical_GE_slices_nonzero_imply_matching_head
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
    (i : Fin (2*R))
    (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val))
    (hGmem : (ab.val.1.2.1,ab.val.1.2.2) ∈
      memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val ab.val.1.1)
    (hEmem : ab.val.2.2 ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod
      J ell m cap patterns
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val ab.val.2.1
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k
        (memory_frozen_source_profile_support SP smallMod BP bigMod
          J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn))
        i.succ)
      (physicalAlternatingSign i.val) k (ω.2.2 i))
    (hGnz : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) i.val Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      ab.val.1.1 ab.val.1.2.1 ab.val.1.2.2 ≠ 0) :
    memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated i.val
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val) ab := by
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true i.castSucc)
  have hcarrier := Finset.mem_sigma.mp ab.property
  have hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ab.val.1.1 = y := (Finset.mem_filter.mp hcarrier.1).2.1
  have hGread := memory_frozen_source_actual_G_slice_readout
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hs (left_ne_zero_of_mul hn) i
    ab.val.1.1 hx (ab.val.1.2.1,ab.val.1.2.2) hGmem hGnz
  have hEfields := (Finset.mem_filter.mp hEmem).2
  have hEproj := (Finset.mem_filter.mp hcarrier.2).2.1
  have hxe : physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      ab.val.2.1 = physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated false i.castSucc) := hEproj.trans hGread.1
  have hEseen := memory_source_actual_E_fixed_frame_seen_exact
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn i ab.val.2.1 hxe
    ab.val.2.2 hEmem
  refine ⟨i.isLt,hGread.1,hEfields.2.1,?_,?_⟩
  · calc
      physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
          (physicalAlternatingSign i.val) k ab.val =
        memoryPrimitiveECanonicalOutput SP smallMod BP bigMod J ell
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          i.val
          (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
            ω life k hs i.succ) := hEfields.2.2
      _ = physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
            J ell m cap patterns ω life k hd.cap_saturated true i.succ) :=
        memory_source_frozen_E_output_is_true_next_projection SP smallMod BP bigMod
          J ell m cap patterns ω life k hd.cap_saturated hs i
  · change (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val ∪
        (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap
          ab.val.1.1 ab.val.1.2.2).toFinset) ∪
        (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns
          ab.val.2.2).toFinset = _
    rw [hGread.2]
    exact hEseen
end Green64FullPhysicalE

end

end

/-! ## MemoryB1TrueJointGECarrier -/

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

/-- The exact intersection of the TRUE original indexed G/E carrier and
the TWO ORIGINAL canonical fixed-input G/E fibres at a source frozen
profile. Both original G and E ordered Fock input representatives survive
as separate original indices; no new product carrier or uniform measure. -/
def memorySourceOriginalCanonicalJointGECarrier
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
    (i : Fin (2*R)) :
    Finset (PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val)) :=
  let hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q (by exact_mod_cast right_ne_zero_of_mul hn)
  Finset.univ.filter (fun ab =>
    (ab.val.1.2.1,ab.val.1.2.2) ∈
      memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val ab.val.1.1 ∧
    ab.val.2.2 ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod
      J ell m cap patterns
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      i.val ab.val.2.1
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.succ)
      (physicalAlternatingSign i.val) k (ω.2.2 i))

/-- A TRUE original G/E witness with nonzero G coefficient is a matching
frozen head IF AND ONLY IF it belongs to both original primitive local
source fibres. In particular this includes the original next-seen register,
the actual conditional E input orbit and every endpoint permutation. -/
theorem memory_source_nonzero_canonical_head_iff_original_joint_GE
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
    (i : Fin (2*R))
    (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val))
    (hGnz : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) i.val Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      ab.val.1.1 ab.val.1.2.1 ab.val.1.2.2 ≠ 0) :
    memorySourceFittingHead SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated i.val
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val) ab ↔
    ab ∈ memorySourceOriginalCanonicalJointGECarrier SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hn i := by
  unfold memorySourceOriginalCanonicalJointGECarrier
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hh
    exact ⟨memory_source_matching_head_in_primitive_G_fibre
      SP smallMod BP bigMod J ell m cap patterns
      ω life hd.cap_saturated k i ab hh,
      memory_source_matching_head_G_nonzero_in_original_E_fibre
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd ω life hn i ab hh hGnz⟩
  · rintro ⟨hG,hE⟩
    exact memory_source_canonical_GE_slices_nonzero_imply_matching_head
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd ω life hn i ab hG hE hGnz
end Green64FullPhysicalE

end

end

/-! ## MemoryB1HeadMassJointGEExact -/

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

set_option maxHeartbeats 750000

/-- The FULL original FittingHead weighted source scalar, with every
original conditional Fock orbit weight and full G/E coefficients intact,
equals the actual source INDEXED legal GE sum restricted to the two
original primitive frozen G/E fibres. Zero-G branches contribute zero,
even if their fitting predicates differ. No head mass is assumed. -/
theorem memory_source_actual_fitting_head_mass_eq_original_joint_GE_sum
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
    (i : Fin (2*R)) :
    memorySourceCanonicalFittingHeadMass SP smallMod BP bigMod
      J ell m cap patterns ω life hd.cap_saturated q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k i =
    ∑ ab ∈ memorySourceOriginalCanonicalJointGECarrier
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd ω life hn i,
      physicalOrientedGEIndexedWeight SP smallMod BP bigMod J ell m cap patterns
        q rho (2*R) i.val Vsmall Vbig
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
            J ell m cap patterns ω life k hd.cap_saturated true i.castSucc))
        ab.val := by
  unfold memorySourceCanonicalFittingHeadMass memorySourceOriginalCanonicalJointGECarrier
  dsimp only
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ab hab
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true i.castSucc)
  by_cases hG : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) i.val Vbig mu
      ab.val.1.1 ab.val.1.2.1 ab.val.1.2.2 ≠ 0
  · have hiff := memory_source_nonzero_canonical_head_iff_original_joint_GE
      SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R hd ω life hn i ab hG
    have hspec := hiff
    simp only [memorySourceOriginalCanonicalJointGECarrier, Finset.mem_filter,
      Finset.mem_univ, true_and] at hspec
    rw [hspec]
    split_ifs <;> simp_all
  · have hG0 : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho (2*R) i.val Vbig mu
        ab.val.1.1 ab.val.1.2.1 ab.val.1.2.2 = 0 := not_ne_iff.mp hG
    have hW0 : physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho (2*R) i.val Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k y ab.val = 0 := by
      unfold physicalOrientedGEIndexedWeight
      rw [hG0]
      ring
    change (if _ then physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho (2*R) i.val Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k y ab.val else 0) =
      (if _ then physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho (2*R) i.val Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k y ab.val else 0)
    simp only [hW0, ite_self]
end Green64FullPhysicalE

end

end

/-! ## MemoryB2RawJointSupport -/

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

/-- Nested fourfold source G/E support, indexed by the original dependent
raw G/E sigma witness; no Hilbert quotient or new source transition. -/
def memorySourceNestedCanonicalGECarrier
    (k : ℤ) (R : ℕ)
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin (2*R)) :    Finset (Σ g : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod J ell cap,
      PhysicalOrientedEWitnessIndex SP smallMod BP bigMod J ell m cap patterns) :=
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap
    (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
      J ell m cap patterns ω life k hcap true i.castSucc)
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  Finset.univ.filter (fun ab =>
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap ab.1.1 = y ∧
    (ab.1.2.1, ab.1.2.2) ∈ memoryPrimitiveGFixedInputFibre
      SP smallMod BP bigMod J ell cap A L offset i.val ab.1.1 ∧
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap ab.2.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap ab.1.2.1 ∧
    ab.2.2 ∈ memoryPrimitiveEFixedFrameFibre
      SP smallMod BP bigMod J ell m cap patterns A L offset i.val
      ab.2.1 iy (physicalAlternatingSign i.val) k (ω.2.2 i))

/-- Source-specific TWO-SIDED G/E support, not a mere inclusion:
on a nonzero genuine G branch, the fourfold nested primitive support
is identical to the original chronological dependent legal GE carrier
cut by both original canonical fibres. -/
theorem memory_source_nested_iff_original_joint_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin (2*R))
    (ab : Σ g : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod J ell cap,
      PhysicalOrientedEWitnessIndex SP smallMod BP bigMod J ell m cap patterns)
    (hGnz : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho (2*R) i.val Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      ab.1.1 ab.1.2.1 ab.1.2.2 ≠ 0) :
    ab ∈ memorySourceNestedCanonicalGECarrier SP smallMod BP bigMod
      J ell m cap patterns k R hd.cap_saturated ω life hs i ↔
    ab ∈ (physicalOrientedGEIndexedCarrier SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod
          J ell m cap patterns ω life k hd.cap_saturated true i.castSucc))
      (memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) i.val)).filter (fun ab =>        (ab.1.2.1,ab.1.2.2) ∈ memoryPrimitiveGFixedInputFibre
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
          (physicalAlternatingSign i.val) k (ω.2.2 i)) := by
  unfold memorySourceNestedCanonicalGECarrier
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hx,hy,hxe,hz⟩
    have hcar := memory_frozen_source_actual_GE_slice_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd ω life hs hw i
      ab.1.1 hx (ab.1.2.1, ab.1.2.2) hy hGnz ab.2.1 hxe ab.2.2 hz
    exact ⟨hcar,hy,hz⟩
  · rintro ⟨hcar,hy,hz⟩
    have hgs := (Finset.mem_sigma.mp hcar).1
    have hes := (Finset.mem_sigma.mp hcar).2
    exact ⟨(Finset.mem_filter.mp hgs).2.1, hy,
      (Finset.mem_filter.mp hes).2.1, hz⟩
end Green64FullPhysicalE

end

end

