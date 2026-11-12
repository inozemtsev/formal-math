module

public import Green64.Library.Correlation.Part018
public import Green64.Library.Correlation.Part012
public import Green64.Library.Correlation.Part010
public import Green64.Library.Correlation.Part009
public import Green64.Library.Correlation.Part005
public import Green64.Library.Correlation.Part008

@[expose] public section

/-!
# Correlation / Part019

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryFrozenSourceJointFibre -/

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

/-- Literal fixed-frame source E fibre; its genuine conditional orbit average. -/
theorem memory_frozen_source_actual_E_orbit_sum
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
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin (2*R))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated false i.castSucc)) :
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.castSucc
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.succ
    (∑ xe ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun xe => physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig) xe : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall
          (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x) : ℂ)) *
      (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
          A L offset i.val xe iy (physicalAlternatingSign i.val) k (ω.2.2 i),
        sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
          (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
          zeta theta (physicalAlternatingSign i.val) k xe z)) =
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val ix iy q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i) := by
  dsimp only
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  have hsmall : x.1 = ix.1 := congrArg Prod.fst hx
  have hactive : ∀ g, (x.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) :=
    fun g => congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).1) hx
  have hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset false i.val) := by
    intro g
    have hm := congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).2) hx
    exact (Multiset.coe_eq_coe.mp hm).trans (List.Perm.of_eq
      (memory_frozen_source_physical_pending SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated false i.castSucc g))
  have hA0 : ∀ g p, i.val ∈ A g p ↔
      ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.castSucc g p
  have hA1 : ∀ g p, i.val+1 ∈ A g p ↔
      ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.succ g p
  exact memory_source_primitive_E_orbit_weighted_fibre SP smallMod BP bigMod
    J ell m cap patterns A L offset i.val (fun g p => hs ⟨g,p⟩)
    q rho Vsmall Vbig k R hd ix iy x hsmall hactive hOld hA0 hA1
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    (fun g p => physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g) (hd.big_above_visits g p))
    (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
    zeta theta (physicalAlternatingSign i.val) (ω.2.2 i)
    (memory_frozen_source_lift_frame_compatible SP smallMod BP bigMod J ell m patterns
      ω life k hs q Vsmall Vbig Knu zeta theta hw i)

/-- Every nonzero G branch in the literal frozen slice supplies the exact
post-G orbit and chronological E register. Zero G branches need no cancellation. -/
theorem memory_frozen_source_actual_G_slice_readout
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
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin (2*R))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
    (yc : FullPhysicalState SP smallMod BP bigMod (J+ell) cap ×
      FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hyc : yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val x)
    (ht : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x yc.1 yc.2 ≠ 0) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated false i.castSucc) ∧
    memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) i.val ∪
      (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x yc.2).toFinset =
      memoryBornBeforeValues BP bigMod (fun g p => life ⟨g,p⟩) (i.val+1) := by
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  have hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset true i.val) := by
    intro g
    have hm := congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).2) hx
    exact (Multiset.coe_eq_coe.mp hm).trans (List.Perm.of_eq
      (memory_frozen_source_physical_pending SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true i.castSucc g))
  have hspec := (Finset.mem_filter.mp hyc).2
  obtain ⟨e,he,hu⟩ := memory_source_primitive_G_unique_inverse SP smallMod BP bigMod
    J ell cap A L offset i.val (fun g p => hs ⟨g,p⟩) hd.cap_saturated
    q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    x yc.1 yc.2 hOld hspec.2 hspec.1 ht
  constructor
  · apply Prod.ext
    · rw [he.2]
      change x.1 = ω.1 i.castSucc
      exact congrArg Prod.fst hx
    · funext g
      apply Prod.ext
      · rw [he.2]
        change (x.2 g).1 = (ω.2.1 i.castSucc g).val
        exact congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
          (yy.2 g).1) hx
      · change (Green64Fock.fockToList ((yc.1.2 g).2) :
          Multiset (Green64Fock.Atom (BP g) (bigMod g))) = _
        rw [Multiset.coe_eq_coe.mpr (hspec.2 g)]
        exact (memory_canonical_Fock_multiset_exact (bigMod g) (A g) (L g) offset
          false i.val (cap g) (hd.cap_saturated g)).symm
  · rw [he.1]
    exact memory_primitive_G_seen_update SP smallMod BP bigMod J ell cap A L offset i.val
      (fun g p => hs ⟨g,p⟩) x hOld hd.cap_saturated e

/-- New source coefficient bridge: joint dependent G→E slice with BOTH
literal conditional orbit ratios. The E input and denominator depend on the
actual G output, and no ghost coefficient or kernel constancy is assumed. -/
theorem memory_frozen_source_actual_GE_two_orbit_sum
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
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin (2*R))
 :
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true i.castSucc
    let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.castSucc
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.succ
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let E := memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val ix iy q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)
    (∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)) *
      (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap A L offset i.val x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig mu x yc.1 yc.2 *
        (∑ xe ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
            (fun xe => physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
              physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1),
          ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu xe : ℂ) /
            (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
              (physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1) : ℂ)) *
          (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
              A L offset i.val xe iy (physicalAlternatingSign i.val) k (ω.2.2 i),
            sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
              q rho Vsmall Vbig mu
              (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
              zeta theta (physicalAlternatingSign i.val) k xe z)))) =
    memoryPrimitiveGUnorderedCoefficient BP bigMod A L offset i.val q rho (2*R) Vbig mu * E := by
  dsimp only
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated true i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let E := memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
    A L offset i.val ix iy q rho Vsmall Vbig mu
    (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
    zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)
  let S := (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
    (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
  let ratio := fun x => (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)
  have hG := memory_source_primitive_G_orbit_weighted_fibre SP smallMod BP bigMod J ell cap
    A L offset i.val hd.big_injective (fun g p => hs ⟨g,p⟩) hd.cap_saturated
    q rho (2*R) Vsmall Vbig mu hd.Vsmall_pos
    (fun g p => physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g) (hd.big_above_visits g p))
    x0 (fun g => List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod BP bigMod
      J ell m cap patterns ω life k hd.cap_saturated true i.castSucc g))
  have hreduce :
      (∑ x ∈ S, ratio x * (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod
          J ell cap A L offset i.val x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig mu x yc.1 yc.2 *
        (∑ xe ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
            (fun xe => physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
              physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1),
          ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu xe : ℂ) /
            (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
              (physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1) : ℂ)) *
          (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
              A L offset i.val xe iy (physicalAlternatingSign i.val) k (ω.2.2 i),
            sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
              q rho Vsmall Vbig mu
              (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
              zeta theta (physicalAlternatingSign i.val) k xe z)))) =
      (∑ x ∈ S, ratio x * (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod
          J ell cap A L offset i.val x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig mu x yc.1 yc.2)) * E := by
    simp_rw [Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro x hx
    apply congrArg (fun z : ℂ => ratio x * z)
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro yc hyc
    by_cases ht : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho (2*R) i.val Vbig mu x yc.1 yc.2 = 0
    · rw [ht, zero_mul, zero_mul]
    · have hr := memory_frozen_source_actual_G_slice_readout SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs hw i
        x (Finset.mem_filter.mp hx).2 yc hyc ht
      rw [memory_frozen_source_actual_E_orbit_sum SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd ω life hs hw i yc.1 hr.1]
  exact hreduce.trans (congrArg (fun z : ℂ => z * E) hG)

/-- The joint source slice sums the literal indexed weight, not a surrogate. -/
theorem memory_frozen_source_actual_GE_indexed_weight_sum
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
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin (2*R))
 :
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true i.castSucc
    let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.castSucc
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.succ
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let E := memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val ix iy q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)
    (∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0),
      ∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap A L offset i.val x,
        ∑ xe ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
            (fun xe => physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
              physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1),
          ∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
              A L offset i.val xe iy (physicalAlternatingSign i.val) k (ω.2.2 i),
            physicalOrientedGEIndexedWeight SP smallMod BP bigMod J ell m cap patterns
              q rho (2*R) i.val Vsmall Vbig mu
              (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
              zeta theta (physicalAlternatingSign i.val) k
              (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
              ⟨⟨x,yc.1,yc.2⟩,⟨xe,z⟩⟩) =
    memoryPrimitiveGUnorderedCoefficient BP bigMod A L offset i.val q rho (2*R) Vbig mu * E := by
  have h := memory_frozen_source_actual_GE_two_orbit_sum SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs hw i
  dsimp only at h ⊢
  simpa only [physicalOrientedGEIndexedWeight, Finset.mul_sum, mul_assoc] using h

/-- Nonzero branches of the computed slice belong to the ACTUAL dependent
GE carrier with its inherited chronological register. This is not a new law. -/
theorem memory_frozen_source_actual_GE_slice_mem
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
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin (2*R))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
    (yc : FullPhysicalState SP smallMod BP bigMod (J+ell) cap ×
      FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hyc : yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val x)
    (ht : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x yc.1 yc.2 ≠ 0)
    (xe : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hxe : physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns xe)
    (hz : z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val xe
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns ω life k hs i.succ)
      (physicalAlternatingSign i.val) k (ω.2.2 i)) :
    (⟨⟨x,yc.1,yc.2⟩,⟨xe,z⟩⟩ : Σ g : PhysicalOrientedGWitnessIndex SP smallMod BP bigMod J ell cap,
      PhysicalOrientedEWitnessIndex SP smallMod BP bigMod J ell m cap patterns) ∈
      physicalOrientedGEIndexedCarrier SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign i.val) k
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
            ω life k hd.cap_saturated true i.castSucc))
        (memorySeenBeforeGValues BP bigMod
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩) i.val) := by
  have hr := memory_frozen_source_actual_G_slice_readout SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs hw i x hx yc hyc ht
  apply Finset.mem_sigma.mpr
  constructor
  · have hG := (Finset.mem_filter.mp hyc).2.1
    rw [hx] at hG
    exact hG
  · dsimp only
    rw [hr.2]
    have hE := (Finset.mem_filter.mp hz).2.1
    rw [hxe] at hE
    exact hE
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceLocalNonzero -/

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

/-- Strict source visit coefficients, including both square-root boundaries. -/
theorem memory_source_visit_strict (q : ℝ) (N i : ℕ)
    (hq : 0 < q) (hq1 : q < 1) :
    0 < sourceVisitQ q N i ∧ 0 < sourceVisitEta q N i := by
  unfold sourceVisitEta sourceVisitQ
  split_ifs
  · have h0 := Real.sqrt_pos.2 hq
    have h1 : Real.sqrt q < 1 := by
      nlinarith [Real.sq_sqrt (le_of_lt hq)]
    constructor <;> linarith
  · constructor <;> linarith

/-- Each ordered canonical G branch has a nonzero ORIGINAL source scalar.
The ghost factorial and all prime masses are retained. -/
theorem memory_source_canonical_G_branch_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R i : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (A : (g : BG) → BP g → Finset ℕ)
    (life : (g : BG) → BP g → MemoryLifespanChoice (2*R+1))
    (offset : ℕ → ℤ)
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) :
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x
      (memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap A life offset i x
        hOld hd.cap_saturated e)
      (memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i hs x
        hOld hd.cap_saturated e) ≠ 0 := by
  rw [memory_primitive_G_branch_coefficient_exact]
  have hv := memory_source_visit_strict q (2*R) i hd.q_pos hd.q_lt_one
  have hq : (sourceVisitQ q (2*R) i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv.1
  have heta : (sourceVisitEta q (2*R) i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv.2
  have hrho : (rho : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd.rho_pos
  apply Finset.prod_ne_zero_iff.mpr
  intro g hg
  have hV : (Vbig g : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hd.Vbig_pos g)
  have hfac : (Nat.factorial (memoryGhostBirthSet (A g) (life g) i).card : ℂ) ≠ 0 :=
    by exact_mod_cast Nat.factorial_ne_zero _
  have hmu : ∀ p : BP g, (physicalSourceMuTilde BP bigMod q (2*R) Vbig g p : ℂ) ≠ 0 := by
    intro p
    exact_mod_cast ne_of_gt (physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R)
      Vbig g p (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g)
      (hd.big_above_visits g p))
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr heta) hrho))
          (pow_ne_zero _ (div_ne_zero hq (pow_ne_zero _ hrho))))
        (div_ne_zero one_ne_zero hfac))
      (pow_ne_zero _ (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr heta) hV) hrho)))
    (Finset.prod_ne_zero_iff.mpr (fun p _ => hmu p))
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceEFrameNonzero -/

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

/-- Nonzero frozen edge gives a nonzero complete physical E frame scalar.
BIG residue support is derived separately, and every original coefficient is kept. -/
theorem memory_frozen_source_E_frame_nonzero
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
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin (2*R)) :
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.succ)
      q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i) ≠ 0 := by
  have hep : (∏ j : Fin (2*R), memoryFrozenSourceEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω j) ≠ 0 := right_ne_zero_of_mul hw
  have he := (Finset.prod_ne_zero_iff.mp hep) i (Finset.mem_univ i)
  have ha : memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i := by
    by_contra h
    simp [memoryFrozenSourceEdgeWeight,h] at he
  simp only [memoryFrozenSourceEdgeWeight, ha, if_true] at he
  have hbase := left_ne_zero_of_mul (left_ne_zero_of_mul he)
  have hker := right_ne_zero_of_mul he
  unfold memoryPrimitiveEFrameCoefficient
  dsimp only [memoryIndependentD, memoryFrozenSourceIndependentLift, Green64SmallHaar.marks]
  apply mul_ne_zero
  · apply mul_ne_zero hbase
    apply Finset.prod_ne_zero_iff.mpr
    intro g hg
    have hr : (rho : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd.rho_pos
    have hV : (Vbig g : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hd.Vbig_pos g)
    apply mul_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ hr) (div_ne_zero one_ne_zero (pow_ne_zero _ hV))
    · apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact_mod_cast ne_of_gt (physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R)
        Vbig g _ (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g)
        (hd.big_above_visits g _))
  · exact hker
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceGEPairNonzero -/

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

/-- A true frozen profile produces an actual original dependent GE index,
with the literal frame, canonical next physical orbit, and the exact next
global numerical seen register. Arbitrary ordered ghost batches are retained. -/
theorem memory_frozen_source_actual_GE_pair_nonzero
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
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin (2*R))
    (e : (g : BG) →
      Fin (memoryGhostBirthSet
        (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun p => life ⟨g,p⟩) i.val).card ≃
      ↥(memoryGhostBirthSet
        (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun p => life ⟨g,p⟩) i.val)) :
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true i.castSucc
    let x1 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true i.succ
    ∃ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign i.val) k
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
        (memorySeenBeforeGValues BP bigMod A L i.val),
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap ab.val.1.2.1 =
        physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
            ω life k hd.cap_saturated false i.castSucc) ∧
      memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns
        ab.val.2.1 ab.val.2.2 = ω.2.2 i ∧
      physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
        (physicalAlternatingSign i.val) k ab.val =
        physicalFockProjection SP smallMod BP bigMod (J+ell) cap x1 ∧
      physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
        (memorySeenBeforeGValues BP bigMod A L i.val) ab.val =
        memorySeenBeforeGValues BP bigMod A L (i.val+1) ∧
      physicalOrientedGEIndexedWeight SP smallMod BP bigMod J ell m cap patterns
        q rho (2*R) i.val Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) ab.val ≠ 0 := by
  dsimp only
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated true i.castSucc
  let xe := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated false i.castSucc
  let x1 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated true i.succ
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  have hb : ∀ g, (Green64Fock.fockToList ((x0.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset true i.val) :=
    fun g => List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod BP bigMod
      J ell m cap patterns ω life k hd.cap_saturated true i.castSucc g)
  have he : ∀ g, (Green64Fock.fockToList ((xe.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset false i.val) :=
    fun g => List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod BP bigMod
      J ell m cap patterns ω life k hd.cap_saturated false i.castSucc g)
  let yg := memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap A L offset i.val
    x0 hb hd.cap_saturated e
  let c := memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A L offset i.val
    (fun g p => hs ⟨g,p⟩) x0 hb hd.cap_saturated e
  have hg := memory_primitive_G_indexed_eligible SP smallMod BP bigMod J ell cap
    A L offset i.val hd.big_injective (fun g p => hs ⟨g,p⟩)
    x0 hb hd.cap_saturated e
  have hgs := memory_primitive_G_seen_update SP smallMod BP bigMod J ell cap
    A L offset i.val (fun g p => hs ⟨g,p⟩) x0 hb hd.cap_saturated e
  have hgp : physicalFockProjection SP smallMod BP bigMod (J+ell) cap yg =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe := by
    apply Prod.ext
    · rfl
    · funext g
      apply Prod.ext
      · rfl
      · change (Green64Fock.fockToList ((yg.2 g).2) :
          Multiset (Green64Fock.Atom (BP g) (bigMod g))) = _
        dsimp only [yg,memoryPrimitiveGOutput]
        rw [memory_ghost_output_list_exact]
        rw [Multiset.coe_eq_coe.mpr (memory_ghost_after_perm_canonical (bigMod g)
          (A g) (L g) offset i.val (fun p => hs ⟨g,p⟩) _ (hb g) (e g))]
        exact (memory_canonical_Fock_multiset_exact (bigMod g) (A g) (L g) offset
          false i.val (cap g) (hd.cap_saturated g)).symm
  obtain ⟨z,hz,hframe,hout,hcoef⟩ := memory_frozen_source_actual_E_lift
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω life hs hw i xe rfl
  have hf := memory_frozen_source_lift_frame_compatible SP smallMod BP bigMod
    J ell m patterns ω life k hs q Vsmall Vbig Knu zeta theta hw i
  have hA0 : ∀ g p, i.val ∈ A g p ↔ ∃ j, (xe.2 g).1 j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.castSucc g p
  have hA1 : ∀ g p, i.val+1 ∈ A g p ↔
      ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.succ g p
  have hlegal := (Finset.mem_filter.mp hz).2.2.1
  have hcanonical : z = memoryPrimitiveESourceChoice SP smallMod BP bigMod
      J ell m cap patterns A L offset i.val (fun g p => hs ⟨g,p⟩) xe he iy
      (ω.2.2 i).1.1 (ω.2.2 i).1.2 (ω.2.2 i).2.1 (ω.2.2 i).2.2.1
      (ω.2.2 i).2.2.2.1 (ω.2.2 i).2.2.2.2 := by
    have hout' : sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns
        xe (physicalAlternatingSign i.val) k z =
        memoryPrimitiveECanonicalOutput SP smallMod BP bigMod J ell A L offset i.val iy := by
      rw [hout]
      unfold memoryPrimitiveECanonicalOutput physicalFockProjection
      dsimp only [x1,memoryFrozenSourcePhysicalState,iy,memoryFrozenSourceIndependentLift,
        Green64SmallHaar.marks]
      congr 1
      funext g
      congr 1
      exact memory_canonical_Fock_multiset_exact (bigMod g) (A g) (L g) offset
        true (i.val+1) (cap g) (hd.cap_saturated g)
    have hh := memory_source_primitive_E_full_inverse SP smallMod BP bigMod J ell m cap
      patterns A L offset i.val (fun g p => hs ⟨g,p⟩) xe
      (fun g => (ω.2.1 i.castSucc g).property) hA0 he iy hA1
      (physicalAlternatingSign i.val) k z hlegal hout'
    change z = memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
      A L offset i.val (fun g p => hs ⟨g,p⟩) xe he iy
      (memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns xe z) at hh
    rw [hframe] at hh
    exact hh
  have hshared : ∀ g j, j ∈ sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g →
      (xe.2 g).1 ((ω.2.2 i).2.1 g j) =
        Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) ((ω.2.2 i).2.2.1 g j) :=
    fun g j hj => ((Finset.mem_filter.mp hf).2.2.2.2.1 g).2 j hj
  have hcont : ∀ g j l, (xe.2 g).1 ((ω.2.2 i).2.1 g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) ((ω.2.2 i).2.2.1 g l) →
      j ∈ sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g ∧ l = j := by
    exact memory_source_active_continuation_is_shared SP smallMod BP bigMod J ell m
      hd.small_prime hd.big_prime hd.big_injective hd.disjoint (patterns (ω.2.2 i).1.1)
      (ω.2.2 i).1.2 ix iy (Finset.mem_filter.mp hf).2.2.1
      (ω.2.2 i).2.1 (ω.2.2 i).2.2.1 (ω.2.2 i).2.2.2.1
      (physicalAlternatingSign i.val) k (Finset.mem_filter.mp hf).2.1
      hd.k_ne hd.big_above_k (Finset.mem_filter.mp hf).2.2.2.2.1
  have hes : memoryBornBeforeValues BP bigMod L (i.val+1) ∪
      (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset =
      memorySeenBeforeGValues BP bigMod A L (i.val+1) := by
    rw [hcanonical]
    exact memory_primitive_E_seen_update SP smallMod BP bigMod J ell m cap patterns
      A L offset i.val (fun g p => hs ⟨g,p⟩) xe he iy hA0 hA1
      (ω.2.2 i).1.1 (ω.2.2 i).1.2 (ω.2.2 i).2.1 (ω.2.2 i).2.2.1
      (ω.2.2 i).2.2.2.1 (ω.2.2 i).2.2.2.2 hshared hcont
  let ab := (⟨⟨x0,yg,c⟩,⟨xe,z⟩⟩ : Σ a : PhysicalOrientedGWitnessIndex
    SP smallMod BP bigMod J ell cap,
      PhysicalOrientedEWitnessIndex SP smallMod BP bigMod J ell m cap patterns)
  have hab : ab ∈ physicalOrientedGEIndexedCarrier SP smallMod BP bigMod J ell m cap patterns
      (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
      (memorySeenBeforeGValues BP bigMod A L i.val) := by
    apply Finset.mem_sigma.mpr
    refine ⟨hg,?_⟩
    dsimp only [ab]
    rw [hgs,hgp]
    exact hz
  have hmu : ∀ g p, 0 < physicalSourceMuTilde BP bigMod q (2*R) Vbig g p := by
    intro g p
    exact physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g)
      (hd.big_above_visits g p)
  have hm (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
      (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (fullPhysicalMass_pos SP smallMod BP bigMod (J+ell) cap
      Vsmall (physicalSourceMuTilde BP bigMod q (2*R) Vbig) hd.Vsmall_pos hmu x)
  have ho (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (physicalOrbitMass_pos SP smallMod BP bigMod (J+ell) cap
      Vsmall (physicalSourceMuTilde BP bigMod q (2*R) Vbig) hd.Vsmall_pos hmu _
      (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩))
  have hG := memory_source_canonical_G_branch_nonzero SP smallMod BP bigMod J ell cap
    q rho Vsmall Vbig k R i.val hd A L offset (fun g p => hs ⟨g,p⟩) x0 hb e
  have hE : sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k xe z ≠ 0 := by
    rw [hcoef]
    exact memory_frozen_source_E_frame_nonzero SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd ω life hs hw i
  have hwab : physicalOrientedGEIndexedWeight SP smallMod BP bigMod J ell m cap patterns
      q rho (2*R) i.val Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) ab ≠ 0 := by
    unfold physicalOrientedGEIndexedWeight
    dsimp only [ab]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero (hm x0) (ho x0)) hG)
      (mul_ne_zero (div_ne_zero (hm xe) (ho yg)) hE)
  refine ⟨⟨ab,hab⟩,hgp,hframe,hout,?_,hwab⟩
  change (memorySeenBeforeGValues BP bigMod A L i.val ∪
    (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x0 c).toFinset) ∪
      (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset = _
  rw [hgs]
  exact hes
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceNonzeroProfileReconstruction -/

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

/-- Terminal partial theorem: every nonzero literal frozen omega/life mass
has an original legal complete indexed physical trace, preserving all source
frames and canonical lifespan atom multisets at G/E. Support and compatibility
are derived, not assumed. No assertion about its weight or complete fibre mass
is made; MemoryGlobalActualFibreWeight and MemoryIdentityTarget remain open. -/
theorem memory_frozen_source_nonzero_profile_indexed_trace
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn :
      memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨0,by omega⟩
    (∀ g, Green64Fock.fockMultiset ((x0.2 g).2) = 0) ∧
    ∃ t : physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
        1 k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
        (memorySeenBeforeGValues BP bigMod
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩) 0),
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated (2*R) 0 _ _ t := by
  have hw := left_ne_zero_of_mul hn
  have hp : (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod J ell m patterns
    ω life k q hp
  refine ⟨(memory_frozen_source_physical_vacua SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated).1,?_⟩
  exact memory_frozen_source_indexed_reconstruction SP smallMod BP bigMod J ell m cap patterns
    k q rho Vsmall Vbig Knu zeta theta R hd ω life hs hw (2*R) 0 (by omega)
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceNonzeroTrace -/

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
theorem memory_frozen_source_indexed_nonzero_reconstruction
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (R : ℕ)
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
    (remaining start : ℕ) (heq : start+remaining = 2*R) :
    let hstart : start < 2*R+1 := by omega
    let x := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨start,hstart⟩
    ∃ t : physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
        1 k remaining start
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
        (memorySeenBeforeGValues BP bigMod
          (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun g p => life ⟨g,p⟩) start),
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated remaining start _ _ t ∧
      memorySourceIndexedTraceWeight SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) Knu
        zeta theta k (2*R) remaining start _ _ t ≠ 0 := by
  induction remaining generalizing start with
  | zero =>
    have hsN : start = 2*R := by omega
    subst start
    dsimp only
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let x := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true ⟨2*R,by omega⟩
    have hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
        (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset true (2*R)) :=
      fun g => List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod BP bigMod
        J ell m cap patterns ω life k hd.cap_saturated true ⟨2*R,by omega⟩ g)
    let e := fun g => (Fintype.equivFinOfCardEq
      (Fintype.card_coe (memoryGhostBirthSet (A g) (L g) (2*R)))).symm
    let yg := memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap A L offset (2*R)
      x hOld hd.cap_saturated e
    let c := memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A L offset (2*R)
      (fun g p => hs ⟨g,p⟩) x hOld hd.cap_saturated e
    have hg := memory_primitive_G_indexed_eligible SP smallMod BP bigMod J ell cap
      A L offset (2*R) hd.big_injective (fun g p => hs ⟨g,p⟩)
      x hOld hd.cap_saturated e
    have hproj : physicalFockProjection SP smallMod BP bigMod (J+ell) cap yg =
        physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
            ω life k hd.cap_saturated false ⟨2*R,by omega⟩) := by
      apply Prod.ext
      · rfl
      · funext g
        apply Prod.ext
        · rfl
        · change (Green64Fock.fockToList ((yg.2 g).2) :
            Multiset (Green64Fock.Atom (BP g) (bigMod g))) = _
          dsimp only [yg,memoryPrimitiveGOutput]
          rw [memory_ghost_output_list_exact]
          rw [Multiset.coe_eq_coe.mpr (memory_ghost_after_perm_canonical (bigMod g)
            (A g) (L g) offset (2*R) (fun p => hs ⟨g,p⟩) _ (hOld g) (e g))]
          exact (memory_canonical_Fock_multiset_exact (bigMod g) (A g) (L g) offset
            false (2*R) (cap g) (hd.cap_saturated g)).symm
    have hG := memory_source_canonical_G_branch_nonzero SP smallMod BP bigMod J ell cap
      q rho Vsmall Vbig k R (2*R) hd A L offset (fun g p => hs ⟨g,p⟩) x hOld e
    have hmu : ∀ g p, 0 < physicalSourceMuTilde BP bigMod q (2*R) Vbig g p := by
      intro g p
      exact physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
        (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g)
        (hd.big_above_visits g p)
    have hm : (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (fullPhysicalMass_pos SP smallMod BP bigMod (J+ell) cap
        Vsmall (physicalSourceMuTilde BP bigMod q (2*R) Vbig) hd.Vsmall_pos hmu x)
    have ho : (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (physicalOrbitMass_pos SP smallMod BP bigMod (J+ell) cap
        Vsmall (physicalSourceMuTilde BP bigMod q (2*R) Vbig) hd.Vsmall_pos hmu _
        (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩))
    have hvac : physicalVacuum SP smallMod BP bigMod J ell
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap yg) = 1 := by
      rw [hproj]
      apply if_pos
      exact (memory_frozen_source_physical_vacua SP smallMod BP bigMod J ell m cap
        patterns ω life k hd.cap_saturated).2
    refine ⟨⟨⟨x,yg,c⟩,hg⟩,⟨rfl,hproj⟩,?_⟩
    change physicalOrientedIndexedTerminalWeight SP smallMod BP bigMod
      J ell cap q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (2*R) (2*R) (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
      ⟨x,yg,c⟩ ≠ 0
    unfold physicalOrientedIndexedTerminalWeight
    dsimp only
    rw [hvac,mul_one]
    exact mul_ne_zero (div_ne_zero hm ho) hG

  | succ r ih =>
    have hi : start < 2*R := by omega
    dsimp only
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let e := fun g => (Fintype.equivFinOfCardEq
      (Fintype.card_coe (memoryGhostBirthSet (A g) (L g) start))).symm
    obtain ⟨ab,hG,hframe,hout,hseen,hwab⟩ := memory_frozen_source_actual_GE_pair_nonzero
      SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd ω life hs hw ⟨start,hi⟩ e
    have hn : start+1+r = 2*R := by omega
    obtain ⟨t,ht,hwt⟩ := ih (start+1) hn
    have hx : ∃ t' : physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
        1 k r (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
          (physicalAlternatingSign start) k ab.val)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
          (memorySeenBeforeGValues BP bigMod A L start) ab.val),
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated r (start+1) _ _ t' ∧
      memorySourceIndexedTraceWeight SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) Knu
        zeta theta k (2*R) r (start+1) _ _ t' ≠ 0 := by
      rw [hout,hseen]
      exact ⟨t,ht,hwt⟩
    obtain ⟨t',ht',hwt'⟩ := hx
    refine ⟨⟨ab,t'⟩,⟨hi,hG,hframe,hout,hseen,ht'⟩,?_⟩
    exact mul_ne_zero hwab hwt' 
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceRootReconstruction -/

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

theorem memory_frozen_source_initial_seen {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp)) :
    (physicalInitialBirths SP smallMod BP bigMod J ell cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap true ⟨0,Nat.succ_pos N⟩)).toFinset =
    memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) 0 := by
  ext v
  simp only [physicalInitialBirths,memoryFrozenSourcePhysicalState,List.mem_toFinset,
    List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,List.mem_map,
    memorySeenBeforeGValues,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨g,j,hv⟩
    let gp : PhysicalSourcePrime BP := ⟨g,(ω.2.1 ⟨0,Nat.succ_pos N⟩ g).val j⟩
    have ha : 0 ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp :=
      (memory_frozen_source_visits_at SP smallMod BP J ell m patterns
        ω ⟨0,Nat.succ_pos N⟩ g gp.2).mpr ⟨j,rfl⟩
    refine ⟨gp,?_,hv⟩
    have hh := hs gp
    cases hl : life gp with
    | none => simp only [hl,MemoryFrozenScheduleSupport] at hh; simp [hh] at ha
    | some az =>
      simp only [hl,MemoryFrozenScheduleSupport] at hh
      have hlo := (hh.2.1 0 ha).1
      simp only [hl]
      exact Or.inr ⟨by omega,ha⟩
  · rintro ⟨⟨g,p⟩,hp,hv⟩
    cases hl : life ⟨g,p⟩ with
    | none => simp [hl] at hp
    | some az =>
      simp only [hl] at hp
      have ha := hp.resolve_left (by omega)
      obtain ⟨j,hj⟩ := (memory_frozen_source_visits_at SP smallMod BP J ell m patterns
        ω ⟨0,Nat.succ_pos N⟩ g p).mp ha.2
      exact ⟨g,j,by rw [hj]; exact hv⟩

theorem memory_frozen_source_initial_births_nodup {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (hinj : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2)) :
    (physicalInitialBirths SP smallMod BP bigMod J ell cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap true ⟨0,Nat.succ_pos N⟩)).Nodup := by
  unfold physicalInitialBirths
  dsimp only [memoryFrozenSourcePhysicalState]
  apply List.nodup_flatMap.mpr
  constructor
  · intro g hg
    apply List.Nodup.map
    · intro j l he
      have hh : (⟨g,(ω.2.1 ⟨0,Nat.succ_pos N⟩ g).val j⟩ : Sigma BP) =
          ⟨g,(ω.2.1 ⟨0,Nat.succ_pos N⟩ g).val l⟩ := hinj he
      exact (ω.2.1 ⟨0,Nat.succ_pos N⟩ g).property
        (eq_of_heq (Sigma.mk.inj_iff.mp hh).2)
    · exact Finset.nodup_toList _
  · apply (Finset.univ : Finset BG).nodup_toList.imp
    intro g h hne v hv hw
    obtain ⟨j,hj,hjv⟩ := List.mem_map.mp hv
    obtain ⟨l,hl,hlv⟩ := List.mem_map.mp hw
    have hh : (⟨g,(ω.2.1 ⟨0,Nat.succ_pos N⟩ g).val j⟩ : Sigma BP) =
        ⟨h,(ω.2.1 ⟨0,Nat.succ_pos N⟩ h).val l⟩ := hinj (hjv.trans hlv.symm)
    exact hne (congrArg Sigma.fst hh)

/-- An actual original root INDEX exists at every nonzero literal profile.
This does not yet assert its spectral weight is nonzero, nor identify its
forward extracted profile, nor evaluate the sum of all such indices. -/
theorem memory_frozen_source_nonzero_profile_raw_root_exists
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
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).Nodup ∧
      (∀ g, Green64Fock.fockMultiset ((xt.1.2 g).2) = 0) ∧
      xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩ ∧
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2 := by
  have hp : (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod J ell m patterns
    ω life k q hp
  have hseen := memory_frozen_source_initial_seen SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated hs
  obtain ⟨hv,t,ht⟩ := memory_frozen_source_nonzero_profile_indexed_trace SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hn
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated true ⟨0,by omega⟩
  have hh : ∃ t : physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
      1 k (2*R) 0 (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).toFinset,
    memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated (2*R) 0 _ _ t := by
    rw [hseen]
    exact ⟨t,ht⟩
  obtain ⟨t',ht'⟩ := hh
  exact ⟨⟨x0,t'⟩,memory_frozen_source_initial_births_nodup SP smallMod BP bigMod
    J ell m cap patterns ω life k hd.cap_saturated hd.big_injective,hv,rfl,ht'⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceContributingRoot -/

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

theorem memory_frozen_source_nonzero_profile_contributing_root_exists
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
      (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).Nodup ∧
      (∀ g, Green64Fock.fockMultiset ((xt.1.2 g).2) = 0) ∧
      xt.1 = memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true ⟨0,by omega⟩ ∧
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap xt.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap xt.1).toFinset xt.2 ∧
      memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0 := by
  have hp : (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod J ell m patterns
    ω life k q hp
  have hseen := memory_frozen_source_initial_seen SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated hs
  have hv := (memory_frozen_source_physical_vacua SP smallMod BP bigMod J ell m cap
    patterns ω life k hd.cap_saturated).1
  obtain ⟨t,ht,hwt⟩ := memory_frozen_source_indexed_nonzero_reconstruction SP smallMod BP bigMod
    J ell m cap patterns (k := k) q rho Vsmall Vbig Knu zeta theta R hd ω life hs
    (left_ne_zero_of_mul hn) (2*R) 0 (by omega)
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated true ⟨0,by omega⟩
  have hh : ∃ t : physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
      1 k (2*R) 0 (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).toFinset,
    memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated (2*R) 0 _ _ t ∧
    memorySourceIndexedTraceWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) Knu
      zeta theta k (2*R) (2*R) 0 _ _ t ≠ 0 := by
    rw [hseen]
    exact ⟨t,ht,hwt⟩
  obtain ⟨t',ht',hwt'⟩ := hh
  have hbirth := memory_frozen_source_initial_births_nodup SP smallMod BP bigMod
    J ell m cap patterns ω life k hd.cap_saturated hd.big_injective
  refine ⟨⟨x0,t'⟩,hbirth,hv,rfl,ht',?_⟩
  have hmu : ∀ g p, 0 < physicalSourceMuTilde BP bigMod q (2*R) Vbig g p := by
    intro g p
    exact physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g)
      (hd.big_above_visits g p)
  have hm : (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x0 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (fullPhysicalMass_pos SP smallMod BP bigMod (J+ell) cap
      Vsmall (physicalSourceMuTilde BP bigMod q (2*R) Vbig) hd.Vsmall_pos hmu x0)
  have hb : (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) ≠ 0 := by
    have hp : 0 < physicalSourceBaselineProduct BP bigMod q (2*R) := by
      unfold physicalSourceBaselineProduct
      apply Finset.prod_pos
      intro g hg
      apply Finset.prod_pos
      intro p hp
      exact physicalSourceBaseline_positive_above_visits BP bigMod q (2*R) g p
        (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.big_above_visits g p)
    exact_mod_cast ne_of_gt hp
  have hvac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) = 1 := by
    apply if_pos
    exact hv
  have hbirth0 : (physicalInitialBirths SP smallMod BP bigMod J ell cap x0).Nodup := hbirth
  simp only [memorySourceRootIndexedWeight,hvac,star_one,mul_one,hbirth0,if_true]
  exact mul_ne_zero (mul_ne_zero hb hm) hwt' 
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceFittingTraceReadout -/

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
/-- Every original G representative and chronological seen register in a
fitting dependent trace has its literal canonical profile, at every visit. -/
theorem memory_frozen_source_fitting_trace_G_readout
    {N : ℕ} (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (remaining start : ℕ) (heq : start+remaining = N)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
      1 k remaining start y seen)
    (hy : y = physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap true ⟨start,by omega⟩))
    (hseen : seen = memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) start)
    (hf : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap remaining start y seen t)
    (j : Fin (remaining+1)) :
    let a := physicalOrientedTraceGWitness SP smallMod BP bigMod J ell m cap patterns
      k remaining start y seen t j
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap true ⟨start+j.val,by omega⟩) ∧
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hcap false ⟨start+j.val,by omega⟩) ∧
    physicalOrientedTraceSeen SP smallMod BP bigMod J ell m cap patterns
      k remaining start y seen t j = memorySeenBeforeGValues BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩) (start+j.val) := by
  induction remaining generalizing start y seen with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    have hs : start = N := by omega
    have hin := (Finset.mem_filter.mp t.property).2.1
    dsimp only [physicalOrientedTraceGWitness,physicalOrientedTraceSeen]
    simp only [Fin.val_zero,Nat.add_zero]
    exact ⟨hin.trans hy, by simpa only [hs] using hf.2, hseen⟩
  | succ r ih =>
    rcases t with ⟨ab,tail⟩
    obtain ⟨hi,hG,hframe,hout,hnext,ht⟩ := hf
    cases j using Fin.cases with
    | zero =>
      have hin := (Finset.mem_filter.mp (Finset.mem_sigma.mp ab.property).1).2.1
      exact ⟨hin.trans hy,hG,hseen⟩
    | succ j =>
      have hh := ih (start+1) (by omega) _ _ tail hout hnext ht j
      simpa only [physicalOrientedTraceGWitness,physicalOrientedTraceSeen,
        Fin.cases_succ,Fin.val_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Readout of the genuine Nu/aux and four permutation families at ALL edges. -/
theorem memory_frozen_source_fitting_trace_E_readout
    {N : ℕ} (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (remaining start : ℕ) (heq : start+remaining = N)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
      1 k remaining start y seen)
    (hf : memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
      ω life k hcap remaining start y seen t)
    (j : Fin remaining) :
    let e := physicalOrientedTraceEWitness SP smallMod BP bigMod J ell m cap patterns
      k remaining start y seen t j
    memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns e.1 e.2 =
      ω.2.2 ⟨start+j.val,by omega⟩ := by
  induction remaining generalizing start y seen with
  | zero => exact j.elim0
  | succ r ih =>
    rcases t with ⟨ab,tail⟩
    obtain ⟨hi,hG,hframe,hout,hnext,ht⟩ := hf
    cases j using Fin.cases with
    | zero => exact hframe
    | succ j =>
      have hh := ih (start+1) (by omega) _ _ tail ht j
      simpa only [physicalOrientedTraceEWitness,Fin.cases_succ,Fin.val_succ,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalFrozenCoordinates -/

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

/-- Read out the UNCHANGED original omega from a genuine sequence
of independent residue/Fock-free states and original six-field
Nu/aux/BIG+SMALL permutation frames. Retains every SMALL Haar state
and every injective ordered BIG active zero-list, but drops the
full BIG residue coordinate only after it has been recorded as the
independent initial Haar anchor. No new artificial omega type. -/
def memoryIndOriginalFrozenPathOf {N : ℕ}
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    MemoryFrozenSourcePath SP smallMod BP J ell m patterns N :=
  (fun t => (states t).1,
   fun t g => ⟨Green64SmallHaar.marks (bigMod g) (J+ell)
      ((states t).2 g),
      Green64SmallHaar.marks_injective (bigMod g) (J+ell) ((states t).2 g)⟩,
   frames)

/-- ORIGINAL independent source divisor D_i, including repeated
auxiliary draws, the original permuted BIG shared marks, and original
permuted SMALL shared marks, is literally the same natural divisor
as the frozen source D_i read out from the independent state/frame
sequence. Not a numerical approximation or divisibility reduction. -/
theorem memory_ind_original_D_eq_frozen_D {N : ℕ}
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (i : Fin N) :
    memoryIndependentD SP smallMod BP bigMod J ell m
      (patterns (frames i).1.1) (frames i).1.2
      (states i.castSucc) (frames i).2.1 (frames i).2.2.2.1 =
    memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns
      (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
        states frames) i := by
  rfl

/-- The ORIGINAL frozen source integer position is exactly the
chronological sum of actual independent source Markov BIG+SMALL D_i,
with its original alternating orientation k, and zero starting point.
Every prime modulus and all four sampled endpoint permutations are
retained in the divisor and its signed steps. -/
theorem memory_ind_original_offset_eq_ind_steps {N : ℕ}
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (k : ℤ) (t : ℕ) :
    memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
      (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
        states frames) k t =
    ∑ i : Fin N, if i.val < t then
      physicalAlternatingSign i.val * k *
        (memoryIndependentD SP smallMod BP bigMod J ell m
          (patterns (frames i).1.1) (frames i).1.2
          (states i.castSucc) (frames i).2.1 (frames i).2.2.2.1 : ℤ)
      else 0 := by
  unfold memoryFrozenSourceOffset
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ht : i.val < t
  · simp only [ht,if_true]
    rw [memory_ind_original_D_eq_frozen_D]
  · simp only [ht,if_false]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndFullRowFrozen -/

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
set_option maxHeartbeats 800000

/-- Actual BIG residue translation, not a new transition kernel. -/
def memoryIndOriginalBIGRowTransport {N : ℕ}
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (k : ℤ) (i : Fin N) : Prop :=
  ∀ g, Green64SmallHaar.residues (bigMod g) (J+ell) ((states i.succ).2 g) =
    Green64SmallHaar.translate (bigMod g)
      (physicalAlternatingSign i.val*k*(memoryIndependentD SP smallMod BP bigMod
        J ell m (patterns (frames i).1.1) (frames i).1.2
        (states i.castSucc) (frames i).2.1 (frames i).2.2.2.1 : ℤ))
      (Green64SmallHaar.residues (bigMod g) (J+ell) ((states i.castSucc).2 g))

/-- Full original row = frozen edge times BIG endpoint damping, gated
only by genuine residue translation. Holds also for every zero row;
SMALL kernel, Fourier factor, Nu/aux and all four permutations survive. -/
theorem memory_ind_original_full_row_eq_frozen_edge {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (i : Fin N) :
    memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta (physicalAlternatingSign i.val) k
      (states i.castSucc) (states i.succ) (frames i).1.1 (frames i).1.2
      (frames i).2.1 (frames i).2.2.1 (frames i).2.2.2.1 (frames i).2.2.2.2 =
    if memoryIndOriginalBIGRowTransport SP smallMod BP bigMod J ell m patterns
        states frames k i then
      memoryFrozenSourceEdgeWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k
        (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
          states frames) i *
      (∏ g : BG, ((Green64SmallHaar.endpointDamping (bigMod g) (J+ell)
        q ((states i.castSucc).2 g) *
        Green64SmallHaar.endpointDamping (bigMod g) (J+ell)
          q ((states i.succ).2 g) : ℝ) : ℂ))
    else 0 := by
  let f := frames i
  let x := states i.castSucc
  let y := states i.succ
  let o := physicalAlternatingSign i.val
  let D := memoryIndependentD SP smallMod BP bigMod J ell m
    (patterns f.1.1) f.1.2 x f.2.1 f.2.2.2.1
  let omega := memoryIndOriginalFrozenPathOf SP smallMod BP bigMod
    J ell m patterns states frames
  let U : Prop := (o=1 ∨ o = -1) ∧ k ≠ 0 ∧
    memoryIndependentAuxBan SP smallMod BP bigMod J ell m (patterns f.1.1) f.1.2 x y
  let H : Prop := Green64SmallHaar.groupEdgeAllowedPerm BP bigMod (J+ell)
    (sourceBigShared J ell m (patterns f.1.1)) (o*k*(D:ℤ)) f.2.1 f.2.2.1 x.2 y.2
  let T : Prop := memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
    J ell m patterns states frames k i
  let G : Prop := memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns omega k i
  have hguard : G ∧ T ↔ U ∧ H := by
    constructor
    · rintro ⟨hg,ht⟩
      change (o=1 ∨ o = -1) ∧ k ≠ 0 ∧
        memoryIndependentAuxBan SP smallMod BP bigMod J ell m
          (patterns f.1.1) f.1.2 x y ∧ _ at hg
      exact ⟨⟨hg.1,hg.2.1,hg.2.2.1⟩,
        fun g => ⟨ht g,hg.2.2.2 g⟩⟩
    · rintro ⟨hu,hh⟩
      refine ⟨?_, fun g => (hh g).1⟩
      change (o=1 ∨ o = -1) ∧ k ≠ 0 ∧
        memoryIndependentAuxBan SP smallMod BP bigMod J ell m
          (patterns f.1.1) f.1.2 x y ∧ _
      exact ⟨hu.1,hu.2.1,hu.2.2,fun g => (hh g).2⟩
  let A : ℂ := (sourceAuxMass BP bigMod J m Vbig (patterns f.1.1) f.1.2 : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ)
  let VB : ℂ := ∏ g : BG, 1 / (Vbig g : ℂ)^
    Green64SmallHaar.unsharedSlots (J+ell) (sourceBigShared J ell m (patterns f.1.1) g)
  let E : ℂ := ∏ g : BG,
    ((Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (x.2 g) *
      Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (y.2 g) : ℝ) : ℂ)
  let K : ℂ := Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vsmall
    (sourceSmallShared J ell) (o*k*(D:ℤ))
    (fun _ _ => originalEdgeScalar
      (memoryOrientationK BP J ell m patterns Knu o f.1.1 f.1.2
        (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (f.2.1 g j))
        (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (f.2.2.1 g j)))
      zeta theta D o k) f.2.2.2.1 f.2.2.2.2 x.1 y.1
  have hVB : (∏ g : BG, (((1:ℝ)/(Vbig g)^
      Green64SmallHaar.unsharedSlots (J+ell)
        (sourceBigShared J ell m (patterns f.1.1) g) : ℝ) : ℂ)) = VB := by
    simp only [VB, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow]
  have hk := memory_ind_BIG_true_kernel_V_and_endpoint_damping
    BP bigMod (J+ell) q Vbig (sourceBigShared J ell m (patterns f.1.1))
    (o*k*(D:ℤ)) f.2.1 f.2.2.1 x.2 y.2
  rw [hVB] at hk
  change (if U then A *
    Green64SmallHaar.groupPermutedKernel BP bigMod (J+ell) q Vbig
      (sourceBigShared J ell m (patterns f.1.1)) (o*k*(D:ℤ))
      (fun _ _ => 1) f.2.1 f.2.2.1 x.2 y.2 * K else 0) =
    if T then (if G then A * VB * K else 0) * E else 0
  rw [hk]
  change (if U then A * (if H then VB * E else 0) * K else 0) =
    if T then (if G then A * VB * K else 0) * E else 0
  by_cases ht : T
  · rw [if_pos ht]
    by_cases hg : G
    · obtain ⟨hu,hh⟩ := hguard.mp ⟨hg,ht⟩
      rw [if_pos hg,if_pos hu,if_pos hh]
      ac_rfl
    · rw [if_neg hg,zero_mul]
      by_cases hu : U
      · have hh : ¬ H := fun hh => hg (hguard.mpr ⟨hu,hh⟩).1
        rw [if_pos hu,if_neg hh,mul_zero,zero_mul]
      · rw [if_neg hu]
  · rw [if_neg ht]
    by_cases hu : U
    · have hh : ¬ H := fun hh => ht (hguard.mpr ⟨hu,hh⟩).2
      rw [if_pos hu,if_neg hh,mul_zero,zero_mul]
    · rw [if_neg hu]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndFullArrayFrozen -/

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
set_option maxHeartbeats 700000

/-- Actual all-visit BIG source damping, including the two half-endpoints. -/
def memoryIndOriginalVisitDamping {N : ℕ} (q : ℝ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell) : ℂ :=
  ∏ t : Fin (N+1), ∏ g : BG, ((sourceVisitQ q N t.val ^
    (Green64SmallHaar.omega (bigMod g)
      (Green64SmallHaar.residues (bigMod g) (J+ell) ((states t).2 g))
        - (J+ell)) : ℝ) : ℂ)

/-- Every genuine row coefficient, not just BIG, factors over the frozen
path with a single exact transport guard. Zero paths are retained. -/
theorem memory_ind_original_all_rows_full_frozen
    (q : ℝ) (hq : 0 ≤ q) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (n : ℕ)
    (states : Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    (∏ i : Fin (n+1),
      memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta (physicalAlternatingSign i.val) k
        (states i.castSucc) (states i.succ) (frames i).1.1 (frames i).1.2
        (frames i).2.1 (frames i).2.2.1 (frames i).2.2.2.1 (frames i).2.2.2.2) =
    if ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod J ell m patterns
        states frames k i then
      (∏ i : Fin (n+1), memoryFrozenSourceEdgeWeight SP smallMod BP bigMod
        J ell m patterns q Vsmall Vbig Knu zeta theta k
        (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
          states frames) i) *
      memoryIndOriginalVisitDamping SP smallMod BP bigMod J ell q states
    else 0 := by
  by_cases ht : ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
      J ell m patterns states frames k i
  · rw [if_pos ht]
    let E (i : Fin (n+1)) : ℂ := ∏ g : BG,
      ((Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q ((states i.castSucc).2 g) *
        Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q ((states i.succ).2 g) : ℝ) : ℂ)
    have hqv : (∏ i : Fin (n+1), E i) =
        memoryIndOriginalVisitDamping SP smallMod BP bigMod J ell q states :=
      memory_ind_BIG_Fin_pair_sourceQ_complex BP bigMod q hq n (J+ell) (fun t => (states t).2)
    calc
      _ = ∏ i : Fin (n+1),
        memoryFrozenSourceEdgeWeight SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k
          (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
            states frames) i * E i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [memory_ind_original_full_row_eq_frozen_edge,if_pos (ht i)]
      _ = _ := by rw [Finset.prod_mul_distrib,hqv]
  · rw [if_neg ht]
    obtain ⟨i,hi⟩ := not_forall.mp ht
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [memory_ind_original_full_row_eq_frozen_edge,if_neg hi]

/-- Actual root mass times the entire array product. No transition
Haar cost is introduced: BIG Haar occurs only once at the initial state. -/
def memoryIndOriginalArrayWeight {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) : ℂ :=
  (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
  (Green64SmallHaar.groupStateMass BP bigMod (J+ell) Vbig : ℂ) *
  ∏ i : Fin N, memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
    q Vsmall Vbig Knu zeta theta (physicalAlternatingSign i.val) k
    (states i.castSucc) (states i.succ) (frames i).1.1 (frames i).1.2
    (frames i).2.1 (frames i).2.2.1 (frames i).2.2.2.1 (frames i).2.2.2.2

/-- Full weighted source summand, including zeros, all Haar/V masses,
original Nu/aux, SMALL kernels, Fourier factors and four permutations. -/
theorem memory_ind_original_full_array_weight_frozen
    (q : ℝ) (hq : 0 ≤ q) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (n : ℕ)
    (states : Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k states frames =
    (∏ g : BG, (Green64SmallHaar.haarAtomMass (bigMod g) : ℂ)) *
    (if ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod J ell m patterns
        states frames k i then
      memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k
        (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
          states frames) *
      memoryIndOriginalVisitDamping SP smallMod BP bigMod J ell q states
    else 0) := by
  unfold memoryIndOriginalArrayWeight
  rw [memory_ind_original_all_rows_full_frozen SP smallMod BP bigMod
    J ell m patterns q hq Vsmall Vbig Knu zeta theta k n states frames]
  by_cases ht : ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
    J ell m patterns states frames k i
  · rw [if_pos ht,if_pos ht]
    have hm := memory_ind_BIG_true_group_mass_split BP bigMod (J+ell) Vbig
    simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow] at hm
    rw [hm]
    unfold memoryFrozenSourceWeight
    ac_rfl
  · rw [if_neg ht,if_neg ht,mul_zero,mul_zero]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalPathReadout -/

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

/-- One ORIGINAL independent row's COMPLETE original frozen E frame,
including its dependent nu/aux and both BIG + both SMALL permutations. -/
def memoryIndOriginalFrameOf
    (a : MemoryIndependentOriginalRowIndex SP smallMod BP bigMod
      J ell m patterns) :
    MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns :=
  (⟨a.1,a.2.1⟩,a.2.2.1,a.2.2.2.1,a.2.2.2.2.1,a.2.2.2.2.2.1)

/-- Recover the genuine ORIGINAL independent source row record at
each position of a complete indexed path. -/
def memoryIndOriginalPathRow :
    (n : ℕ) → memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n →
      Fin n → MemoryIndependentOriginalRowIndex SP smallMod BP bigMod J ell m patterns
  | 0, _, i => i.elim0
  | n+1, ⟨a,tail⟩, i =>
    Fin.cases a (fun j => memoryIndOriginalPathRow n tail j) i

/-- Exact ORIGINAL source frame readout of all ν/aux/4perms from
the true independent ordered Markov row records. -/
def memoryIndOriginalPathFrames
    (n : ℕ) (p : memoryIndOriginalPathIndex SP smallMod BP bigMod
      J ell m patterns n) :
    Fin n → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns :=
  fun i => memoryIndOriginalFrameOf SP smallMod BP bigMod J ell m patterns
    (memoryIndOriginalPathRow SP smallMod BP bigMod J ell m patterns n p i)

/-- The true independent source state array includes the actual
initial SMALL and BIG physical state and then each row's exact y
output. No fictitious independent state is inserted between steps. -/
def memoryIndOriginalPathStates
    (x : MemoryIndependentState SP smallMod BP bigMod J ell) :
    (n : ℕ) → memoryIndOriginalPathIndex SP smallMod BP bigMod
      J ell m patterns n → Fin (n+1) →
      MemoryIndependentState SP smallMod BP bigMod J ell
  | 0, _, _ => x
  | n+1, ⟨a,tail⟩, i =>
    Fin.cases x
      (fun j => memoryIndOriginalPathStates
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        n tail j) i

/-- The SOURCE frozen path from each true independent Markov path
contains its actual SMALL states, ordered BIG marked zero labels,
and Nu/aux/BIG/SMALL permutations at EVERY step. -/
def memoryIndOriginalPathFrozenSource
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (n : ℕ) (p : memoryIndOriginalPathIndex SP smallMod BP bigMod
      J ell m patterns n) :
    MemoryFrozenSourcePath SP smallMod BP J ell m patterns n :=
  memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
    (memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns x n p)
    (memoryIndOriginalPathFrames SP smallMod BP bigMod J ell m patterns n p)

/-- Original path initial state remains exactly the given x. -/
theorem memory_ind_original_path_initial
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (n : ℕ) (p : memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n) :
    memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns
      x n p ⟨0, Nat.succ_pos n⟩ = x := by
  cases n with
  | zero => rfl
  | succ n => cases p; rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryIndB7PathRowArrayEquiv -/

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

/-- Reassemble the EXACT original independent chronological
Nu/aux/4-permutation + next physical-state path index from its
pointwise Fin(n) row array. No quotient, ordering erasure,
factorial normalization or extra stochastic path is introduced. -/
def memoryIndOriginalPathFromRows :
    (n : ℕ) →
    (Fin n → MemoryIndependentOriginalRowIndex SP smallMod BP bigMod
      J ell m patterns) →
    memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n
  | 0, _ => PUnit.unit
  | n+1, f =>
    (f ⟨0, Nat.succ_pos n⟩,
      memoryIndOriginalPathFromRows n (fun j => f j.succ))

/-- Original path row-array readout is a LEFT inverse to the
complete original path reconstruction. This retains row order. -/
theorem memory_ind_original_readout_from_rows
    (n : ℕ)
    (rows : Fin n → MemoryIndependentOriginalRowIndex SP smallMod
      BP bigMod J ell m patterns) :
    memoryIndOriginalPathRow SP smallMod BP bigMod J ell m patterns n
      (memoryIndOriginalPathFromRows SP smallMod BP bigMod
        J ell m patterns n rows) = rows := by
  induction n with
  | zero =>
    funext i
    exact i.elim0
  | succ n ih =>
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      change memoryIndOriginalPathRow SP smallMod BP bigMod J ell m
        patterns n
        (memoryIndOriginalPathFromRows SP smallMod BP bigMod
          J ell m patterns n (fun k => rows k.succ)) j =
        rows j.succ
      exact congrFun (ih (fun j => rows j.succ)) j

/-- Conversely, the original chronological source path is
reconstructed verbatim from ALL its Nu/aux/permutation/target-state
row records. Therefore every row-array corresponds to exactly one
original path; there is no invented path multiplicity. -/
theorem memory_ind_original_from_rows_readout
    (n : ℕ)
    (p : memoryIndOriginalPathIndex SP smallMod BP bigMod
      J ell m patterns n) :
    memoryIndOriginalPathFromRows SP smallMod BP bigMod
      J ell m patterns n
      (memoryIndOriginalPathRow SP smallMod BP bigMod
        J ell m patterns n p) = p := by
  induction n with
  | zero =>
    cases p
    rfl
  | succ n ih =>
    rcases p with ⟨a,tail⟩
    change (a, memoryIndOriginalPathFromRows SP smallMod BP bigMod
      J ell m patterns n
      (fun j => memoryIndOriginalPathRow SP smallMod BP bigMod
        J ell m patterns n tail j)) = (a,tail)
    rw [ih tail]

/-- Bijective original Markov path ⇔ array of original row records:
each record retains its dependent nu/aux, both BIG and both SMALL
permutations, and true target state. No independent root theorem
is assumed. -/
def memoryIndOriginalPathRowsEquiv (n : ℕ) :
    memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n ≃
    (Fin n → MemoryIndependentOriginalRowIndex SP smallMod
      BP bigMod J ell m patterns) where
  toFun := memoryIndOriginalPathRow SP smallMod BP bigMod
    J ell m patterns n
  invFun := memoryIndOriginalPathFromRows SP smallMod BP bigMod
    J ell m patterns n
  left_inv := memory_ind_original_from_rows_readout SP smallMod BP bigMod
    J ell m patterns n
  right_inv := memory_ind_original_readout_from_rows SP smallMod BP bigMod
    J ell m patterns n
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalPathStateOutput -/

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

/-- The complete ORIGINAL independent finite Markov path readout uses
EXACTLY the real indexed row output for its next state. Thus the
frozen omega path can be recovered without phantom intermediate
states or an unproved source transition consistency constraint. -/
theorem memory_ind_original_path_next_state
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (n : ℕ)
    (p : memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n)
    (i : Fin n) :
    memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns
      x n p i.succ =
    memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns
      (memoryIndOriginalPathRow SP smallMod BP bigMod J ell m patterns n p i) := by
  induction n generalizing x with
  | zero => exact i.elim0
  | succ n ih =>
    rcases p with ⟨a,tail⟩
    cases i using Fin.cases with
    | zero =>
      change memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        n tail ⟨0,Nat.succ_pos n⟩ =
        memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a
      exact memory_ind_original_path_initial SP smallMod BP bigMod
        J ell m patterns _ n tail
    | succ j =>
      change memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        n tail j.succ =
        memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns
          (memoryIndOriginalPathRow SP smallMod BP bigMod J ell m patterns n tail j)
      exact ih _ tail j

/-- Each source original frame read out from independent path records
is EXACTLY the frame of that particular original row; not a freely
chosen independent endpoint permutation family. -/
theorem memory_ind_original_path_frame_is_row
    (n : ℕ)
    (p : memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n)
    (i : Fin n) :
    memoryIndOriginalPathFrames SP smallMod BP bigMod J ell m patterns n p i =
      memoryIndOriginalFrameOf SP smallMod BP bigMod J ell m patterns
        (memoryIndOriginalPathRow SP smallMod BP bigMod J ell m patterns n p i) := rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryIndFullArrayEquiv -/

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
set_option maxHeartbeats 700000

/-- Reassemble a literal source row, retaining its dependent auxiliary draw. -/
def memoryIndRowFromFrameOutput
    (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (y : MemoryIndependentState SP smallMod BP bigMod J ell) :
    MemoryIndependentOriginalRowIndex SP smallMod BP bigMod J ell m patterns :=
  ⟨f.1.1, f.1.2, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2, y⟩

/-- Actual independent source initial state and complete path, with no
support restriction, biject to all state arrays and all original frames. -/
def memoryIndOriginalFullArrayEquiv (N : ℕ) :
    (MemoryIndependentState SP smallMod BP bigMod J ell ×
      memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns N) ≃
    ((Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell) ×
      (Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)) where
  toFun xp :=
    (memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns xp.1 N xp.2,
     memoryIndOriginalPathFrames SP smallMod BP bigMod J ell m patterns N xp.2)
  invFun sf :=
    (sf.1 0, memoryIndOriginalPathFromRows SP smallMod BP bigMod J ell m patterns N
      (fun i => memoryIndRowFromFrameOutput SP smallMod BP bigMod J ell m patterns
        (sf.2 i) (sf.1 i.succ)))
  left_inv := by
    rintro ⟨x,p⟩
    apply Prod.ext
    · exact memory_ind_original_path_initial SP smallMod BP bigMod J ell m patterns x N p
    · change memoryIndOriginalPathFromRows SP smallMod BP bigMod J ell m patterns N
        (fun i => memoryIndRowFromFrameOutput SP smallMod BP bigMod J ell m patterns
          (memoryIndOriginalPathFrames SP smallMod BP bigMod J ell m patterns N p i)
          (memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns x N p i.succ)) = p
      have he : (fun i => memoryIndRowFromFrameOutput SP smallMod BP bigMod J ell m patterns
          (memoryIndOriginalPathFrames SP smallMod BP bigMod J ell m patterns N p i)
          (memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns x N p i.succ)) =
          memoryIndOriginalPathRow SP smallMod BP bigMod J ell m patterns N p := by
        funext i
        rw [memory_ind_original_path_next_state]
        rfl
      rw [he]
      exact memory_ind_original_from_rows_readout SP smallMod BP bigMod J ell m patterns N p
  right_inv := by
    rintro ⟨states,frames⟩
    let rows := fun i => memoryIndRowFromFrameOutput SP smallMod BP bigMod
      J ell m patterns (frames i) (states i.succ)
    let p := memoryIndOriginalPathFromRows SP smallMod BP bigMod J ell m patterns N rows
    have hr : memoryIndOriginalPathRow SP smallMod BP bigMod J ell m patterns N p = rows :=
      memory_ind_original_readout_from_rows SP smallMod BP bigMod J ell m patterns N rows
    apply Prod.ext
    · change memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns
        (states 0) N p = states
      funext t
      cases t using Fin.cases with
      | zero =>
        exact memory_ind_original_path_initial SP smallMod BP bigMod
          J ell m patterns (states 0) N p
      | succ i =>
        rw [memory_ind_original_path_next_state,hr]
        rfl
    · change memoryIndOriginalPathFrames SP smallMod BP bigMod J ell m patterns N p = frames
      funext i
      unfold memoryIndOriginalPathFrames
      rw [hr]
      rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalPathRowWitness -/

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

/-- The EXACT original independent source row coefficient at
the i-th member of an ACTUAL independent full Markov path. Both
source and target independent states are recovered from the
original path, not sampled afresh at the next step. -/
def memoryIndOriginalPathRowScalar
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (start : ℕ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (n : ℕ) (p : memoryIndOriginalPathIndex SP smallMod BP bigMod
      J ell m patterns n) (i : Fin n) : ℂ :=
  let a := memoryIndOriginalPathRow SP smallMod BP bigMod
    J ell m patterns n p i
  let st := memoryIndOriginalPathStates SP smallMod BP bigMod
    J ell m patterns x n p
  memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
    q Vsmall Vbig Knu zeta theta
    (physicalAlternatingSign (start+i.val)) k
    (st i.castSucc) (st i.succ)
    a.1 a.2.1 a.2.2.1 a.2.2.2.1
    a.2.2.2.2.1 a.2.2.2.2.2.1

/-- On the ORIGINAL chronological path prefix, nonzero path weight
implies its REAL first Markov row source scalar is nonzero, and
its entire ORIGINAL tail path weight is nonzero too. -/
theorem memory_ind_original_path_first_nonzero
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (start : ℕ)
    (F : MemoryIndependentState SP smallMod BP bigMod J ell → ℂ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (n : ℕ)
    (a : MemoryIndependentOriginalRowIndex SP smallMod BP bigMod
      J ell m patterns)
    (tail : memoryIndOriginalPathIndex SP smallMod BP bigMod
      J ell m patterns n)
    (hn : memoryIndOriginalPathTerm SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k start F x (n+1) ⟨a,tail⟩ ≠ 0) :
    memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta
      (physicalAlternatingSign start) k x
      (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
      a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1
      a.2.2.2.2.2.1 ≠ 0 ∧
    memoryIndOriginalPathTerm SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k (start+1) F
      (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
      n tail ≠ 0 := by
  exact mul_ne_zero_iff.mp hn
end Green64FullPhysicalE

end

end

/-! ## MemoryIndChronologicalReadoutBridge -/

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

/-- The source ORIGINAL chronological row at every position of a
genuine independent source path is EXACTLY the row scalar recovered
from its unchanged finite state/frame arrays. This bridges the
nonzero-product induction to the true source array transport lemmas,
without any new Markov law, independent time sampling, omitted
Nu/aux choices, or altered permutation orientations. -/
theorem memory_ind_original_chronological_step_eq_readout
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (n start : ℕ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (p : memoryIndOriginalPathIndex SP smallMod BP bigMod
      J ell m patterns n) (i : Fin n) :
    memoryIndOriginalChronologicalStep SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k n start x p i =
    memoryIndOriginalPathRowScalar SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k start x n p i := by
  induction n generalizing start x with
  | zero => exact i.elim0
  | succ n ih =>
    rcases p with ⟨a,tail⟩
    let y := memoryIndependentOriginalRowOutput SP smallMod BP bigMod
      J ell m patterns a
    cases i using Fin.cases with
    | zero =>
      unfold memoryIndOriginalPathRowScalar
      change _ =
        memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta
          (physicalAlternatingSign (start+0)) k x
          (memoryIndOriginalPathStates SP smallMod BP bigMod J ell m patterns
            y n tail ⟨0,Nat.succ_pos n⟩)
          a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1
          a.2.2.2.2.2.1
      rw [memory_ind_original_path_initial]
      simp only [Nat.add_zero]
      rfl
    | succ j =>
      have h := ih (start+1) y tail j
      unfold memoryIndOriginalPathRowScalar at h ⊢
      change memoryIndOriginalChronologicalStep SP smallMod BP bigMod
          J ell m patterns q Vsmall Vbig Knu zeta theta k
          n (start+1) y tail j = _
      dsimp only [memoryIndOriginalPathRow, memoryIndOriginalPathStates,
        Fin.cases_succ, Fin.val_succ]
      have ht : start + (j.val + 1) = (start+1) + j.val := by omega
      rw [ht]
      exact h
end Green64FullPhysicalE

end

end

/-! ## MemoryIndRootArraySum -/

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
set_option maxHeartbeats 700000
local instance : Fintype (MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) := by
  classical
  unfold MemoryPrimitiveEFrame
  infer_instance

/-- Exact chronological product for the unchanged independent path, including zeros. -/
theorem memory_ind_original_path_term_eq_chronological_product
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (n start : ℕ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (p : memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n) :
    memoryIndOriginalPathTerm SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k start (fun _ => 1) x n p =
    ∏ i : Fin n, memoryIndOriginalChronologicalStep SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k n start x p i := by
  induction n generalizing start x with
  | zero => simp only [memoryIndOriginalPathTerm, Fin.prod_univ_zero]
  | succ n ih =>
    rcases p with ⟨a,tail⟩
    rw [Fin.prod_univ_succ]
    simp only [memoryIndOriginalPathTerm, memoryIndOriginalChronologicalStep,
      Fin.cases_zero, Fin.cases_succ]
    rw [ih]

/-- Full original independent root is the unrestricted state/frame array sum.
The bijection retains each Nu/aux and four-permutation witness exactly once. -/
theorem memory_independent_root_exact_full_array_sum
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :    memoryIndependentRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R =
    ∑ states : Fin (2*R+1) → MemoryIndependentState SP smallMod BP bigMod J ell,
      ∑ frames : Fin (2*R) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns,
        memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k states frames := by
  let XP := MemoryIndependentState SP smallMod BP bigMod J ell ×
    memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns (2*R)
  let SF := (Fin (2*R+1) → MemoryIndependentState SP smallMod BP bigMod J ell) ×
    (Fin (2*R) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
  let mass : ℂ := (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
    (Green64SmallHaar.groupStateMass BP bigMod (J+ell) Vbig : ℂ)
  let F (xp : XP) : ℂ := mass *
    memoryIndOriginalPathTerm SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k 0 (fun _ => 1) xp.1 (2*R) xp.2
  let G (sf : SF) : ℂ := memoryIndOriginalArrayWeight SP smallMod BP bigMod
    J ell m patterns q Vsmall Vbig Knu zeta theta k sf.1 sf.2
  have he : (∑ xp : XP, F xp) = ∑ sf : SF, G sf := by
    apply Fintype.sum_equiv (memoryIndOriginalFullArrayEquiv SP smallMod BP bigMod
      J ell m patterns (2*R)) F G
    intro xp
    unfold F G memoryIndOriginalArrayWeight
    rw [memory_ind_original_path_term_eq_chronological_product]
    apply congrArg (fun v : ℂ => mass * v)
    apply Finset.prod_congr rfl
    intro i hi
    rw [memory_ind_original_chronological_step_eq_readout]
    unfold memoryIndOriginalPathRowScalar
    simp only [Nat.zero_add]
    rfl
  rw [memory_independent_root_exact_true_original_path_sum]
  calc
    _ = ∑ xp : XP, F xp := by
      conv_rhs => rw [Fintype.sum_prod_type]
      simp only [F]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ sf : SF, G sf := he
    _ = _ := by rw [Fintype.sum_prod_type]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndTransportAnchor -/

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

/-- The exact BIG transport guard alone determines one original initial torus
at all visits. No nonzero-row hypothesis or new source assumption is required. -/
theorem memory_ind_transport_array_BIG_one_anchor {N : ℕ}
    (k : ℤ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i : Fin N, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
      J ell m patterns states frames k i) :
    let ω := memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m
      patterns states frames
    let C (i : Fin (N+1)) : MemoryIndependentBIGTorus BP bigMod :=
      fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states i).2 g)
    ∀ i : Fin (N+1),
      C i = memoryIndBIGTorusTranslate BP bigMod
        (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k i.val) (C 0) := by
  let ω := memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m
    patterns states frames
  let C (i : Fin (N+1)) : MemoryIndependentBIGTorus BP bigMod :=
    fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states i).2 g)
  have hstep (i : Fin N) : C i.succ =
      memoryIndBIGTorusTranslate BP bigMod
        (physicalAlternatingSign i.val*k*
          (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ))
        (C i.castSucc) := by
    funext g
    exact ht i g
  have hzero := memory_frozen_source_offset_zero SP smallMod BP bigMod
    J ell m patterns ω k
  dsimp only
  intro t
  induction t using Fin.induction with
  | zero =>
    change C 0 = memoryIndBIGTorusTranslate BP bigMod
      (memoryFrozenSourceOffset SP smallMod BP bigMod
        J ell m patterns ω k 0) (C 0)
    rw [hzero]
    exact (memory_ind_BIG_torus_translate_zero BP bigMod (C 0)).symm
  | succ i ih =>
    have hdelta := memory_frozen_source_offset_step SP smallMod BP bigMod
      J ell m patterns ω k i.val i.isLt
    have hfin : (⟨i.val,i.isLt⟩ : Fin N) = i := Fin.eta i i.isLt
    simp only [hfin] at hdelta
    let d : ℤ := physicalAlternatingSign i.val*k*
      (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ)
    have htotal :
      memoryFrozenSourceOffset SP smallMod BP bigMod
        J ell m patterns ω k (i.val+1) =
      memoryFrozenSourceOffset SP smallMod BP bigMod
        J ell m patterns ω k i.val + d := by
      dsimp only [d]
      omega
    change C i.succ =
      memoryIndBIGTorusTranslate BP bigMod
        (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k (i.val+1)) (C 0)
    calc
      C i.succ = memoryIndBIGTorusTranslate BP bigMod d
          (C i.castSucc) := hstep i
      _ = memoryIndBIGTorusTranslate BP bigMod d
          (memoryIndBIGTorusTranslate BP bigMod
            (memoryFrozenSourceOffset SP smallMod BP bigMod
              J ell m patterns ω k i.val) (C 0)) := by
            change C i.castSucc =
              memoryIndBIGTorusTranslate BP bigMod
                (memoryFrozenSourceOffset SP smallMod BP bigMod
                  J ell m patterns ω k i.val) (C 0) at ih
            rw [ih]
      _ = memoryIndBIGTorusTranslate BP bigMod
          (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k i.val + d) (C 0) := by
        exact memory_ind_BIG_torus_translate_comp BP bigMod
          d (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k i.val) (C 0)
      _ = _ := by rw [htotal]
end Green64FullPhysicalE

end

end

