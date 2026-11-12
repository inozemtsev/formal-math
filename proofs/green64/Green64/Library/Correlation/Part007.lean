module

public import Green64.Library.Correlation.Part006
public import Green64.Library.Weights.Part022
public import Green64.Library.Correlation.Part005
public import Green64.Library.Correlation.Part001
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

/-!
# Correlation / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalActualIndependentAnchorFrame -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Literal signed displacement of the actual oriented E witness,
including the source sigma frame and the SMALL/BIG divisor D. -/
noncomputable def physicalActualEdgeDelta (i : ℕ) : ℤ :=
  sourceOrientedStep SP smallMod BP bigMod J ell m cap
    (patterns (H.edge i).1) (H.edge i).2.1 (H.beforeE i)
    (H.edge i).2.2.1.sigmaBig (H.edge i).2.2.2.1
    (physicalAlternatingSign i) k

/-- Exact source offset h_i, not a postulated Markov position. -/
noncomputable def physicalActualOffset (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range i,
    physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H j

theorem physical_actual_offset_succ (i : ℕ) :
    physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1) =
    physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i +
    physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  simp only [physicalActualOffset, Finset.sum_range_succ]

/-- Independent initial residue ANCHORS are required at EVERY BIG
prime, including a prime never born in the physical witness.
The source h_i evolves via corrected E steps; a_p is not replaced
by zero for absent primes. -/
noncomputable def physicalActualAnchorResidue
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (g : BG) (p : BP g) : ZMod (bigMod g p) :=
  (physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (bigMod g p)) - anchor g p

theorem physical_actual_anchor_residue_transport
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (g : BG) (p : BP g) :
    physicalActualAnchorResidue SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      anchor (i+1) g p =
    physicalActualAnchorResidue SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      anchor i g p +
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (bigMod g p)) := by
  unfold physicalActualAnchorResidue
  rw [physical_actual_offset_succ SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i]
  push_cast
  abel

/-- At a genuine G ghost or fresh active birth, the anchor matches
the actual hit offset. This gives the required zero test. -/
theorem physical_actual_anchor_residue_at_birth
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (g : BG) (p : BP g)
    (hborn : anchor g p =
      (physicalActualOffset SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (bigMod g p))) :
    physicalActualAnchorResidue SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      anchor i g p = 0 := by
  simp [physicalActualAnchorResidue, hborn]

/-- An actual store moves the anchored hit to the next visit:
the residue becomes precisely the signed edge displacement. -/
theorem physical_actual_anchor_residue_store_reset
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (g : BG) (p : BP g)
    (hborn : anchor g p =
      (physicalActualOffset SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (bigMod g p))) :
    physicalActualAnchorResidue SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      anchor (i+1) g p =
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (bigMod g p)) := by
  rw [physical_actual_anchor_residue_transport
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H anchor i g p]
  rw [physical_actual_anchor_residue_at_birth
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H anchor i g p hborn]
  simp

/-- An unrepresented prime starts at -a_p, not necessarily zero,
and follows the exact signed source offsets. -/
theorem physical_actual_anchor_initial
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (g : BG) (p : BP g) :
    physicalActualAnchorResidue SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      anchor 0 g p = -(anchor g p) := by
  simp [physicalActualAnchorResidue, physicalActualOffset]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralCanonicalFrames -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Physical BIG source at the CANONICAL pattern slot j.
This is the actual independently sampled sigma, not a raw-index
copy. Global literal labels retain the group through Sigma BP. -/
noncomputable def actualLiteralCanonicalSourceSlot
    (i : ℕ) (g : BG) (j : Fin (J+ell)) :
    PhysicalSourcePrime BP :=
  ⟨g, ((H.beforeE i).2 g).1 (((H.edge i).2.2.1.sigmaBig g) j)⟩

/-- Physical BIG target at the CANONICAL pattern slot j.
The actual sampled tau is independent of source sigma. -/
noncomputable def actualLiteralCanonicalTargetSlot
    (i : ℕ) (g : BG) (j : Fin (J+ell)) :
    PhysicalSourcePrime BP :=
  ⟨g, (((H.edge i).2.2.1.bigChoice g).1)
    (((H.edge i).2.2.1.tauBig g) j)⟩

/-- The row's canonical shared-copy field follows from the corrected
legal source E witness, with independently permuted endpoints. -/
theorem physical_actual_literal_shared_canonical_copy
    (i : ℕ) (hi : i < N) (g : BG) (j : Fin (J+ell))
    (hj : j ∈ sourceBigShared J ell m (patterns (H.edge i).1) g) :
    actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j =
    actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j := by
  have hBig := (H.E_legal i hi).2.2.2.1 g
  have hc := hBig.shared_copy j hj
  exact congrArg (fun p : BP g => (⟨g, p⟩ : PhysicalSourcePrime BP)) hc

/-- Original sampled sigma can be recovered: first canonicalize,
then apply its inverse. No source index information is discarded. -/
theorem physical_actual_literal_source_inverse_frame
    (i : ℕ) (g : BG) (j : Fin (J+ell)) :
    (actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      i g (((H.edge i).2.2.1.sigmaBig g).symm j)).2 =
    ((H.beforeE i).2 g).1 j := by
  simp [actualLiteralCanonicalSourceSlot]

/-- Corresponding reconstruction of the genuinely independent
target frame from canonical source-pattern coordinates. -/
theorem physical_actual_literal_target_inverse_frame
    (i : ℕ) (g : BG) (j : Fin (J+ell)) :
    (actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      i g (((H.edge i).2.2.1.tauBig g).symm j)).2 =
    ((H.edge i).2.2.1.bigChoice g).1 j := by
  simp [actualLiteralCanonicalTargetSlot]

/-- Each literal source and target label carries its true BIG group. -/
theorem physical_actual_literal_canonical_groups
    (i : ℕ) (g : BG) (j : Fin (J+ell)) :
    (actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j).1 = g ∧
    (actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j).1 = g := by
  exact ⟨rfl, rfl⟩

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralEndpointNodup -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- The source row can preserve the PHYSICAL raw endpoint order:
choose canonical active slots x(sigma j) and record sigma^{-1}
as its row permutation. This avoids assuming sigma=tau and
does not change the actual source array or its Knu input. -/
theorem physical_actual_literal_source_raw_reconstruction
    (i : ℕ) :
    (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
      (fun a => actualLiteralCanonicalSourceSlot SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H
        i a.1 (((H.edge i).2.2.1.sigmaBig a.1).symm a.2)) =
    (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
      (fun a => (⟨a.1, ((H.beforeE i).2 a.1).1 a.2⟩ :
        PhysicalSourcePrime BP)) := by
  congr 1
  funext a
  cases a with
  | mk g j => simp [actualLiteralCanonicalSourceSlot]

/-- Independently sampled target tau likewise survives in
literal targetPerm=tau^{-1}, with no source/target identification. -/
theorem physical_actual_literal_target_raw_reconstruction
    (i : ℕ) :
    (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
      (fun a => actualLiteralCanonicalTargetSlot SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H
        i a.1 (((H.edge i).2.2.1.tauBig a.1).symm a.2)) =
    (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
      (fun a => (⟨a.1, ((H.edge i).2.2.1.bigChoice a.1).1 a.2⟩ :
        PhysicalSourcePrime BP)) := by
  congr 1
  funext a
  cases a with
  | mk g j => simp [actualLiteralCanonicalTargetSlot]

/-- Uniform injectivity of Sigma-valued endpoint labels from
group-local injection; distinct groups cannot collide in the
literal prime carrier even before assuming numerical injectivity. -/
theorem physical_literal_sigma_group_slots_injective
    {M : ℕ} (f : (g : BG) → Fin M → BP g)
    (hinj : ∀ g, Function.Injective (f g)) :
    Function.Injective (fun a : Σ _ : BG, Fin M =>
      (⟨a.1, f a.1 a.2⟩ : PhysicalSourcePrime BP)) := by
  intro a b h
  cases a with
  | mk g j =>
    cases b with
    | mk g' t =>
      change (⟨g, f g j⟩ : PhysicalSourcePrime BP) =
        (⟨g', f g' t⟩ : PhysicalSourcePrime BP) at h
      have gh : g = g' := congrArg Sigma.fst h
      subst g'
      have vv : f g j = f g t := by
        exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have jt : j = t := hinj g vv
      cases jt
      rfl

/-- Every actual G_i witness preserves BIG active slot injectivity
in the E_i input orbit, even when its Fock representative is reordered. -/
theorem physical_actual_beforeE_big_slots_injective
    (i : ℕ) (hi : i < N) (g : BG) :
    Function.Injective (((H.beforeE i).2 g).1) := by
  have hBefore := physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)
  have hG := actual_G_preserves_physical_good_orbit
    SP smallMod BP bigMod (J+ell) cap q rho N i
    Vbig muBig (H.before i) (H.afterG i) (H.ghost i)
    (H.seen i) hBefore (H.G_nonzero i (Nat.le_of_lt hi))
    (H.G_birth_eligible i (Nat.le_of_lt hi))
  have hGood : PhysicalGoodOrbit SP smallMod BP bigMod (J+ell)
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.beforeE i))
      (H.seen i ∪ (physicalGhostFreshBirths
        SP smallMod BP bigMod (J+ell) cap
        (H.before i) (H.ghost i)).toFinset) := by
    rw [H.E_orbit_input i hi]
    exact hG
  exact (hGood g).1

/-- Corrected E_i target active array coincides with the next real
physical witness state; its injectivity is a checked path invariant. -/
theorem physical_actual_edge_target_big_slots_injective
    (i : ℕ) (hi : i < N) (g : BG) :
    Function.Injective (((H.edge i).2.2.1.bigChoice g).1) := by
  have hNext := physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H (i+1) (Nat.succ_le_of_lt hi)
  have hh := congrArg
    (fun z : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      ((z.2 g).1)) (H.E_output i hi)
  change ((H.before (i+1)).2 g).1 =
    ((H.edge i).2.2.1.bigChoice g).1 at hh
  rw [← hh]
  exact (hNext g).1

/-- The actual global BIG source list has no repeated prime carrier
labels; this is the literal RowValid.source_nodup obligation. -/
theorem physical_actual_literal_source_slot_injective
    (i : ℕ) (hi : i < N) :
    Function.Injective (fun a : Σ _ : BG, Fin (J+ell) =>
      actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        i a.1 a.2) := by
  apply physical_literal_sigma_group_slots_injective BP
    (fun g j => ((H.beforeE i).2 g).1
      (((H.edge i).2.2.1.sigmaBig g) j))
  intro g
  exact (physical_actual_beforeE_big_slots_injective
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g).comp
      (((H.edge i).2.2.1.sigmaBig g).injective)

/-- The actual global BIG target list is also Nodup even across
different groups, not merely within each physical group. -/
theorem physical_actual_literal_target_slot_injective
    (i : ℕ) (hi : i < N) :
    Function.Injective (fun a : Σ _ : BG, Fin (J+ell) =>
      actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        i a.1 a.2) := by
  apply physical_literal_sigma_group_slots_injective BP
    (fun g j => (((H.edge i).2.2.1.bigChoice g).1)
      (((H.edge i).2.2.1.tauBig g) j))
  intro g
  exact (physical_actual_edge_target_big_slots_injective
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g).comp
      (((H.edge i).2.2.1.tauBig g).injective)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralSharedPattern -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Exact global set of shared labels, in source-pattern canonical
coordinates, with the genuine independent sigma frame retained. -/
noncomputable def physicalActualLiteralSharedPatternValues
    (i : ℕ) : Finset (PhysicalSourcePrime BP) :=
  ((Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).filter
    (fun a => a.2 ∈ sourceBigShared J ell m
      (patterns (H.edge i).1) a.1)).image
    (fun a => actualLiteralCanonicalSourceSlot SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H
      i a.1 a.2)

/-- This is precisely the original RowValid.shared_source_pattern
membership bi-implication: no unshared canonical source slot can
accidentally have a shared numerical/group label. -/
theorem physical_actual_literal_shared_source_pattern
    (i : ℕ) (hi : i < N) (g : BG) (j : Fin (J+ell)) :
    actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j ∈
      physicalActualLiteralSharedPatternValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H i
    ↔ j ∈ sourceBigShared J ell m (patterns (H.edge i).1) g := by
  classical
  constructor
  · intro hh
    rcases Finset.mem_image.mp hh with ⟨a, ha, heq⟩
    have heqidx : a = (⟨g,j⟩ : Σ _ : BG, Fin (J+ell)) := by
      apply physical_actual_literal_source_slot_injective
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi
      exact heq
    subst a
    exact (Finset.mem_filter.mp ha).2
  · intro hj
    apply Finset.mem_image.mpr
    refine ⟨⟨g,j⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩

/-- The source and target shared prime sets coincide in EVERY
BIG group under the actual corrected E edge; this uses BOTH
sigma and tau and real sourceOrientedPhysicalLegal. -/
theorem physical_actual_literal_shared_target_image
    (i : ℕ) (hi : i < N) :
    physicalActualLiteralSharedPatternValues SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i =
    ((Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).filter
      (fun a => a.2 ∈ sourceBigShared J ell m
        (patterns (H.edge i).1) a.1)).image
      (fun a => actualLiteralCanonicalTargetSlot SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H
        i a.1 a.2) := by
  unfold physicalActualLiteralSharedPatternValues
  apply Finset.image_congr
  intro a ha
  exact physical_actual_literal_shared_canonical_copy
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi a.1 a.2
    (Finset.mem_filter.mp ha).2

/-- Literal RowValid.shared_target_pattern: a target canonical
slot is shared IF AND ONLY IF its pattern index is shared, even
when source and target permutations are unrelated. -/
theorem physical_actual_literal_shared_target_pattern
    (i : ℕ) (hi : i < N) (g : BG) (j : Fin (J+ell)) :
    actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j ∈
      physicalActualLiteralSharedPatternValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H i
    ↔ j ∈ sourceBigShared J ell m (patterns (H.edge i).1) g := by
  rw [physical_actual_literal_shared_target_image
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi]
  constructor
  · intro hh
    rcases Finset.mem_image.mp hh with ⟨a, ha, heq⟩
    have heqidx : a = (⟨g,j⟩ : Σ _ : BG, Fin (J+ell)) := by
      apply physical_actual_literal_target_slot_injective
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi
      exact heq
    subst a
    exact (Finset.mem_filter.mp ha).2
  · intro hj
    apply Finset.mem_image.mpr
    refine ⟨⟨g,j⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralSharedIndices -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- TRUE raw source order, carrying sigma inverse. -/
noncomputable def physicalActualLiteralRawSourceList (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
    (fun a => actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1
      (((H.edge i).2.2.1.sigmaBig a.1).symm a.2))

/-- TRUE raw target order, carrying independent tau inverse. -/
noncomputable def physicalActualLiteralRawTargetList (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).toList.map
    (fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1
      (((H.edge i).2.2.1.tauBig a.1).symm a.2))

/-- Index the literal list by membership, never by a quotient multiset. -/
noncomputable def literalIndicesFor {P : Type} [DecidableEq P]
    (xs : List P) (S : Finset P) : Finset (Fin xs.length) :=
  Finset.univ.filter (fun j => xs.get j ∈ S)

theorem literal_indices_for_exact {P : Type} [DecidableEq P]
    (xs : List P) (S : Finset P) (j : Fin xs.length) :
    j ∈ literalIndicesFor xs S ↔ xs.get j ∈ S := by
  simp [literalIndicesFor]

theorem literal_indices_for_image {P : Type} [DecidableEq P]
    (xs : List P) (S : Finset P) (h : S ⊆ xs.toFinset) :
    (literalIndicesFor xs S).image xs.get = S := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hp
    rw [← heq]
    exact (literal_indices_for_exact xs S j).mp hj
  · intro hp
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp
      (List.mem_toFinset.mp (h hp))
    exact Finset.mem_image.mpr
      ⟨j, (literal_indices_for_exact xs S j).mpr (hj ▸ hp), hj⟩

/-- Every actual shared label occurs at a LITERAL raw source-list index. -/
theorem physical_actual_shared_values_in_raw_source
    (i : ℕ) :
    physicalActualLiteralSharedPatternValues SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i ⊆
    (physicalActualLiteralRawSourceList SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  intro p hp
  unfold physicalActualLiteralSharedPatternValues at hp
  obtain ⟨⟨g,j⟩, _, rfl⟩ := Finset.mem_image.mp hp
  apply List.mem_toFinset.mpr
  unfold physicalActualLiteralRawSourceList
  apply List.mem_map.mpr
  refine ⟨⟨g, ((H.edge i).2.2.1.sigmaBig g) j⟩, ?_, ?_⟩
  · simp
  · simp [actualLiteralCanonicalSourceSlot]

/-- The original RowValid.sharedIndices lives in the FINITE INDEX
type of the global raw source list, not an abstract set of primes. -/
noncomputable def physicalActualLiteralSharedIndices (i : ℕ) :
    Finset (Fin (physicalActualLiteralRawSourceList SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i).length) :=
  literalIndicesFor
    (physicalActualLiteralRawSourceList SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i)
    (physicalActualLiteralSharedPatternValues SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i)

theorem physical_actual_literal_shared_index_image (i : ℕ) :
    (physicalActualLiteralSharedIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawSourceList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get =
    physicalActualLiteralSharedPatternValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  exact literal_indices_for_image _ _
    (physical_actual_shared_values_in_raw_source
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i)

theorem physical_actual_literal_shared_index_source_pattern
    (i : ℕ) (hi : i < N) (g : BG) (j : Fin (J+ell)) :
    actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j ∈
    (physicalActualLiteralSharedIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawSourceList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get ↔
    j ∈ sourceBigShared J ell m (patterns (H.edge i).1) g := by
  rw [physical_actual_literal_shared_index_image]
  exact physical_actual_literal_shared_source_pattern
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g j

/-- Raw source list is Nodup, using the real G/E witness invariant. -/
theorem physical_actual_literal_raw_source_nodup
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  unfold physicalActualLiteralRawSourceList
  rw [physical_actual_literal_source_raw_reconstruction
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i]
  apply List.Nodup.map
    (physical_literal_sigma_group_slots_injective BP
      (fun g j => ((H.beforeE i).2 g).1 j)
      (physical_actual_beforeE_big_slots_injective
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi))
  exact Finset.nodup_toList _

/-- Target list is Nodup under the genuine independent tau. -/
theorem physical_actual_literal_raw_target_nodup
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  unfold physicalActualLiteralRawTargetList
  rw [physical_actual_literal_target_raw_reconstruction
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i]
  apply List.Nodup.map
    (physical_literal_sigma_group_slots_injective BP
      (fun g j => ((H.edge i).2.2.1.bigChoice g).1 j)
      (physical_actual_edge_target_big_slots_injective
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi))
  exact Finset.nodup_toList _

end Green64FullPhysicalE

end

/-! ## PhysicalActualPathSetTransition -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- On a genuine complete physical history, all next-visit BIG
active labels are exactly the preceding oriented E_i shared,
OLD promoted and fresh slots. The next pending orbit is exactly
its nonpromoted OLD survivor and freshly stored source slots. -/
theorem actual_physical_path_big_E_set_update
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let z := H.edge i
    let b := z.2.2.1
    let x := H.beforeE i
    let pat := patterns z.1
    ((Finset.univ : Finset (Fin (J+ell))).image
        (((physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap (H.before (i+1))).2 g).1) =
      trueBigSharedValues (bigMod g) (J+ell) (cap g)
        (x.2 g) (sourceBigShared J ell m pat g) (b.sigmaBig g) ∪
      trueBigPromotedValues (bigMod g) (J+ell) (cap g)
        (x.2 g) (b.bigChoice g).2 ∪
      trueBigFreshValues (J+ell) (b.bigChoice g).1
        (sourceBigShared J ell m pat g)
        ((b.bigChoice g).2.2.1) (b.tauBig g)) ∧
    (((((physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap (H.before (i+1))).2 g).2).map
          (fun a => a.1)).toFinset =
      trueBigSurvivorValues (bigMod g) (J+ell) (cap g)
        (x.2 g) (b.bigChoice g).2 ∪
      trueBigStoredValues (bigMod g) (J+ell) (cap g)
        (x.2 g) (b.sigmaBig g) (b.bigChoice g).2) := by
  have hEdge := full_oriented_source_E_actual_set_conservation
    SP smallMod BP bigMod J ell m cap patterns
    (H.beforeE i) (physicalAlternatingSign i) k
    (H.edge i) (H.E_legal i hi) g
  dsimp only at hEdge ⊢
  rw [H.E_output i hi]
  exact hEdge

end Green64FullPhysicalE

end

/-! ## PhysicalActualPathSourceFlow -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Prime value support of an actual physical state, BEFORE the
physical G_i operation or AFTER an E_i edge. -/
noncomputable def actualPhysicalPendingSet
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (g : BG) : Finset (BP g) :=
  ((Green64Fock.fockToList ((x.2 g).2)).map
    (fun a => a.1)).toFinset

/-- Reordering the true symmetric pending Fock representative
cannot change the set of numerical OLD prime labels. -/
theorem actualPhysicalPendingSet_orbit_eq
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (h : physicalFockProjection SP smallMod BP bigMod
       (J+ell) cap x =
       physicalFockProjection SP smallMod BP bigMod
       (J+ell) cap y) (g : BG) :
    actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap x g =
    actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap y g := by
  have hh := congrArg (fun z : FullPhysicalOutput SP smallMod
    BP bigMod (J+ell) =>
      (((z.2 g).2).map (fun a => a.1)).toFinset) h
  simpa [actualPhysicalPendingSet, physicalFockProjection,
    Green64Fock.fockMultiset, Green64Fock.fockToList,
    Multiset.map_coe] using hh

end Green64FullPhysicalE

end

/-! ## PhysicalActualEValueSetFlow -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- For a real physical G/E witness history, the E_i pending prime
support is the current OLD pending support minus OLD promotions
plus newly stored source active primes. All duplicate exclusions
come from the checked global birth invariant, not extra premises. -/
theorem actual_physical_path_E_pending_difference
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    actualPhysicalPendingSet SP smallMod BP bigMod J ell cap
      (H.before (i+1)) g =
    (actualPhysicalPendingSet SP smallMod BP bigMod J ell cap
      (H.beforeE i) g \
       trueBigPromotedValues (bigMod g) (J+ell) (cap g)
          ((H.beforeE i).2 g) ((H.edge i).2.2.1.bigChoice g).2) ∪
    trueBigStoredValues (bigMod g) (J+ell) (cap g)
      ((H.beforeE i).2 g)
      ((H.edge i).2.2.1.sigmaBig g)
      ((H.edge i).2.2.1.bigChoice g).2 := by
  have hbefore := physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)
  have hG := actual_G_preserves_physical_good_orbit
    SP smallMod BP bigMod (J+ell) cap q rho N i Vbig muBig
    (H.before i) (H.afterG i) (H.ghost i) (H.seen i)
    hbefore (H.G_nonzero i (Nat.le_of_lt hi))
    (H.G_birth_eligible i (Nat.le_of_lt hi))
  have hBeforeE : PhysicalGoodOrbit SP smallMod BP bigMod
      (J+ell)
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (H.beforeE i))
      (H.seen i ∪ (physicalGhostFreshBirths SP smallMod BP
        bigMod (J+ell) cap (H.before i) (H.ghost i)).toFinset) := by
    rw [H.E_orbit_input i hi]
    exact hG
  have hOldNodup :
      ((Green64Fock.fockMultiset (((H.beforeE i).2 g).2)).map
         (fun a => a.1)).Nodup := (hBeforeE g).2.1
  have hOldInjective := sourceFock_old_prime_injective
    (bigMod g) (cap g) (((H.beforeE i).2 g).2) hOldNodup
  have hSurv := physical_E_survivors_equal_set_difference
    (bigMod g) (J+ell) (cap g) ((H.beforeE i).2 g)
    ((H.edge i).2.2.1.bigChoice g).2 hOldInjective
  have hIndex := bigFock_old_index_prime_support
    (bigMod g) (J+ell) (cap g) ((H.beforeE i).2 g)
  have hPath := (actual_physical_path_big_E_set_update
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g).2
  have hNext :
      actualPhysicalPendingSet SP smallMod BP bigMod J ell cap
        (H.before (i+1)) g =
      trueBigSurvivorValues (bigMod g) (J+ell) (cap g)
        ((H.beforeE i).2 g) ((H.edge i).2.2.1.bigChoice g).2 ∪
      trueBigStoredValues (bigMod g) (J+ell) (cap g)
        ((H.beforeE i).2 g)
        ((H.edge i).2.2.1.sigmaBig g)
        ((H.edge i).2.2.1.bigChoice g).2 := by
    simpa [actualPhysicalPendingSet, physicalFockProjection,
      Green64Fock.fockMultiset, Green64Fock.fockToList,
      Multiset.map_coe] using hPath
  rw [hSurv, hIndex] at hNext
  exact hNext

end Green64FullPhysicalE

end

/-! ## PhysicalActualBIGSourceRecursion -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- TRUE physical source recursion for each BIG group's pending
PRIME SET, including original G OLD termination, independent
ghost births, physical Fock orbit identification, then E OLD
promotions and newly stored active source primes. -/
theorem actual_physical_BIG_pending_source_recursion
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let terminated : Finset (BP g) :=
      ((H.ghost i g).1.1).image
        (fun j => ((Green64Fock.fockToList
          (((H.before i).2 g).2)).get j).1)
    let ghostBorn : Finset (BP g) :=
      (Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
        (fun j => ((H.ghost i g).2.2 j).1)
    let promoted : Finset (BP g) :=
      trueBigPromotedValues (bigMod g) (J+ell) (cap g)
        ((H.beforeE i).2 g) ((H.edge i).2.2.1.bigChoice g).2
    let stored : Finset (BP g) :=
      trueBigStoredValues (bigMod g) (J+ell) (cap g)
        ((H.beforeE i).2 g) ((H.edge i).2.2.1.sigmaBig g)
        ((H.edge i).2.2.1.bigChoice g).2
    actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.before (i+1)) g =
    (((actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.before i) g \ terminated) ∪
      ghostBorn) \ promoted) ∪ stored := by
  dsimp only
  have hE := actual_physical_path_E_pending_difference
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g
  have hFiber := actualPhysicalPendingSet_orbit_eq
    SP smallMod BP bigMod J ell cap
    (H.beforeE i) (H.afterG i) (H.E_orbit_input i hi) g
  have hG := actual_physical_path_big_G_value_conservation
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H (Nat.le_of_lt hi) g
  calc
    _ = (actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.beforeE i) g \
        trueBigPromotedValues (bigMod g) (J+ell) (cap g)
          ((H.beforeE i).2 g) ((H.edge i).2.2.1.bigChoice g).2) ∪
        trueBigStoredValues (bigMod g) (J+ell) (cap g)
          ((H.beforeE i).2 g) ((H.edge i).2.2.1.sigmaBig g)
          ((H.edge i).2.2.1.bigChoice g).2 := hE
    _ = (actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.afterG i) g \
        trueBigPromotedValues (bigMod g) (J+ell) (cap g)
          ((H.beforeE i).2 g) ((H.edge i).2.2.1.bigChoice g).2) ∪
        trueBigStoredValues (bigMod g) (J+ell) (cap g)
          ((H.beforeE i).2 g) ((H.edge i).2.2.1.sigmaBig g)
          ((H.edge i).2.2.1.bigChoice g).2 := by rw [hFiber]
    _ = _ := by
      have hG' :
          actualPhysicalPendingSet SP smallMod BP bigMod
            J ell cap (H.afterG i) g =
          (actualPhysicalPendingSet SP smallMod BP bigMod
            J ell cap (H.before i) g \
            ((H.ghost i g).1.1).image
              (fun j => ((Green64Fock.fockToList
                (((H.before i).2 g).2)).get j).1)) ∪
          ((Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
            (fun j => ((H.ghost i g).2.2 j).1)) := by
        simpa only [actualPhysicalPendingSet] using hG
      rw [hG']

end Green64FullPhysicalE

end

/-! ## PhysicalActualBIGSourceSubsets -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- EXACT source subset conditions for an actual physical
BIG G_i E_i transition: all shared prime values are current
active, all stored values are active but unshared, and every
OLD promotion belongs to the genuine G-output pending set. -/
theorem actual_physical_BIG_source_subset_laws
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let x := H.beforeE i
    let b := (H.edge i).2.2.1
    let shared := sourceBigShared J ell m (patterns (H.edge i).1) g
    let S := trueBigSharedValues (bigMod g) (J+ell) (cap g)
      (x.2 g) shared (b.sigmaBig g)
    let K := trueBigStoredValues (bigMod g) (J+ell) (cap g)
      (x.2 g) (b.sigmaBig g) (b.bigChoice g).2
    let R := trueBigPromotedValues (bigMod g) (J+ell) (cap g)
      (x.2 g) (b.bigChoice g).2
    let A := (Finset.univ : Finset (Fin (J+ell))).image
      (((H.before i).2 g).1)
    S ⊆ A ∧ K ⊆ A \ S ∧
    R ⊆ actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.afterG i) g := by
  dsimp only
  have hleg := (H.E_legal i hi).2.2.2.1 g
  have hBefore := physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)
  have hGgood := actual_G_preserves_physical_good_orbit
    SP smallMod BP bigMod (J+ell) cap q rho N i Vbig muBig
    (H.before i) (H.afterG i) (H.ghost i) (H.seen i)
    hBefore (H.G_nonzero i (Nat.le_of_lt hi))
    (H.G_birth_eligible i (Nat.le_of_lt hi))
  have hGoodE : PhysicalGoodOrbit SP smallMod BP bigMod
      (J+ell)
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (H.beforeE i))
      (H.seen i ∪ (physicalGhostFreshBirths SP smallMod BP
        bigMod (J+ell) cap (H.before i) (H.ghost i)).toFinset) := by
    rw [H.E_orbit_input i hi]
    exact hGgood
  have hActive :
      ((H.beforeE i).2 g).1 = ((H.before i).2 g).1 := by
    have hEq := congrArg
      (fun z : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
         ((z.2 g).1)) (H.E_orbit_input i hi)
    change ((H.beforeE i).2 g).1 = ((H.afterG i).2 g).1 at hEq
    have hg := (physical_nonzero_ghost_witness_is_operational
      SP smallMod BP bigMod (J+ell) cap q rho N i
      Vbig muBig (H.before i) (H.afterG i) (H.ghost i)
      (H.G_nonzero i (Nat.le_of_lt hi))).1.2 g
    exact hEq.trans hg.symm
  have hK := trueBigStoredValues_subset_active
    (bigMod g) (J+ell) (cap g) ((H.beforeE i).2 g)
    ((H.edge i).2.2.1.sigmaBig g)
    ((H.edge i).2.2.1.bigChoice g).2
  have hS := trueBigSharedValues_subset_active
    (bigMod g) (J+ell) (cap g) ((H.beforeE i).2 g)
    (sourceBigShared J ell m (patterns (H.edge i).1) g)
    ((H.edge i).2.2.1.sigmaBig g)
  have hDisj := trueBigStored_disjoint_shared
    (bigMod g) (J+ell) (cap g) ((H.beforeE i).2 g)
    ((H.edge i).2.2.1.bigChoice g).1
    (sourceBigShared J ell m (patterns (H.edge i).1) g)
    ((H.edge i).2.2.1.sigmaBig g)
    ((H.edge i).2.2.1.tauBig g)
    (sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap (patterns (H.edge i).1) (H.edge i).2.1
      (H.beforeE i) ((H.edge i).2.2.1.sigmaBig)
      ((H.edge i).2.2.2.1))
    (sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns (H.edge i).1) (H.edge i).2.1
      (H.beforeE i) ((H.edge i).2.2.1.sigmaBig)
      ((H.edge i).2.2.2.1) (physicalAlternatingSign i) k)
    ((H.edge i).2.2.1.bigChoice g).2 hleg (hGoodE g).1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hActive] using hS
  · intro p hp
    apply Finset.mem_sdiff.mpr
    constructor
    · have ha := hK hp
      simpa only [hActive] using ha
    · exact Finset.disjoint_left.mp hDisj hp
  · have hR := trueBigPromotedValues_subset_OLD
      (bigMod g) (J+ell) (cap g)
      ((H.beforeE i).2 g) ((H.edge i).2.2.1.bigChoice g).2
    have hFiber := actualPhysicalPendingSet_orbit_eq
      SP smallMod BP bigMod J ell cap
      (H.beforeE i) (H.afterG i) (H.E_orbit_input i hi) g
    rw [← hFiber]
    simpa only [actualPhysicalPendingSet] using hR

end Green64FullPhysicalE

end

/-! ## PhysicalActualBIGLocalSourceRows -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Original SOURCE set conservation rules, now derived for EVERY
BIG GROUP and every actual physical G_i/E_i witness pair.
This is the exact set-level step premise of Green64OrderedLift's
source_set_lifespans, not a declared abstract transition law. -/
theorem physical_actual_BIG_local_source_rows
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let x := H.beforeE i
    let b := (H.edge i).2.2.1
    let shared := sourceBigShared J ell m (patterns (H.edge i).1) g
    let S := trueBigSharedValues (bigMod g) (J+ell) (cap g)
      (x.2 g) shared (b.sigmaBig g)
    let K := trueBigStoredValues (bigMod g) (J+ell) (cap g)
      (x.2 g) (b.sigmaBig g) (b.bigChoice g).2
    let R := trueBigPromotedValues (bigMod g) (J+ell) (cap g)
      (x.2 g) (b.bigChoice g).2
    let Fnext := trueBigFreshValues (J+ell) (b.bigChoice g).1
      shared (b.bigChoice g).2.2.1 (b.tauBig g)
    let T := ((H.ghost i g).1.1).image
      (fun j => ((Green64Fock.fockToList
        (((H.before i).2 g).2)).get j).1)
    let G := (Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
      (fun j => ((H.ghost i g).2.2 j).1)
    let A := (Finset.univ : Finset (Fin (J+ell))).image
      (((H.before i).2 g).1)
    let M := actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.before i) g
    let Anext := (Finset.univ : Finset (Fin (J+ell))).image
      (((H.before (i+1)).2 g).1)
    let Mnext := actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.before (i+1)) g
    S ⊆ A ∧ K ⊆ A \ S ∧
      R ⊆ ((M \ T) ∪ G) ∧
      Anext = S ∪ R ∪ Fnext ∧
      Mnext = (((M \ T) ∪ G) \ R) ∪ K := by
  dsimp only
  have hS := actual_physical_BIG_source_subset_laws
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g
  have hA := (actual_physical_path_big_E_set_update
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g).1
  have hM := actual_physical_BIG_pending_source_recursion
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g
  have hG := actual_physical_path_big_G_value_conservation
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H (Nat.le_of_lt hi) g
  have hGset :
      actualPhysicalPendingSet SP smallMod BP bigMod
        J ell cap (H.afterG i) g =
      (actualPhysicalPendingSet SP smallMod BP bigMod
        J ell cap (H.before i) g \
        ((H.ghost i g).1.1).image (fun j =>
          ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1)) ∪
        ((Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
          (fun j => ((H.ghost i g).2.2 j).1)) := by
    simpa only [actualPhysicalPendingSet] using hG
  refine ⟨hS.1, hS.2.1, ?_, ?_, hM⟩
  · have hR := hS.2.2
    rw [hGset] at hR
    exact hR
  · simpa [physicalFockProjection] using hA

end Green64FullPhysicalE

end

/-! ## PhysicalActualBIGBirthExclusions -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Numerically fresh ghost births cannot collide with the actual
source active or OLD pending particles: they all have a prior
registered birth; this uses the original G witness seen check. -/
theorem physical_actual_G_ghost_disjoint_old_pool
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i ≤ N) (g : BG) :
    Disjoint
      ((Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
        (fun j => ((H.ghost i g).2.2 j).1))
      (((Finset.univ : Finset (Fin (J+ell))).image
        (((H.before i).2 g).1)) ∪
        actualPhysicalPendingSet SP smallMod BP bigMod
          J ell cap (H.before i) g) := by
  classical
  have hGood := (physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi) g
  have hSeenPending (p : BP g)
      (hp : p ∈ actualPhysicalPendingSet SP smallMod BP bigMod
        J ell cap (H.before i) g) :
      bigMod g p ∈ H.seen i := by
    apply hGood.2.2.2.2 p
    simpa [actualPhysicalPendingSet, physicalOutputPendingValues,
      physicalFockProjection, Green64Fock.fockMultiset,
      Green64Fock.fockToList, Multiset.map_coe] using hp
  apply Finset.disjoint_left.mpr
  intro p hp hOld
  rcases Finset.mem_image.mp hp with ⟨j, _, hpj⟩
  have hNotSeen := physical_G_fresh_group_not_seen
    SP smallMod BP bigMod (J+ell) cap
    (H.before i) (H.ghost i) (H.seen i)
    (H.G_birth_eligible i hi) g j
  apply hNotSeen
  rcases Finset.mem_union.mp hOld with ha | hm
  · rcases Finset.mem_image.mp ha with ⟨t, _, ht⟩
    have hSeen : bigMod g (((H.before i).2 g).1 t) ∈ H.seen i :=
      hGood.2.2.2.1 t
    rw [ht] at hSeen
    simpa only [hpj] using hSeen
  · simpa only [hpj] using hSeenPending p hm

end Green64FullPhysicalE

end

/-! ## PhysicalActualBIGFreshExclusions -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- An actual fresh source E_i active target birth is never
an old active prime, never an old pending prime, and never
a ghost prime born earlier in the same G_i/E_i step.
The original GLOBAL numerical birth marker enforces this. -/
theorem physical_actual_E_fresh_disjoint_old_and_ghost
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let z := H.edge i
    let B := trueBigFreshValues (J+ell) (z.2.2.1.bigChoice g).1
      (sourceBigShared J ell m (patterns z.1) g)
      ((z.2.2.1.bigChoice g).2.2.1) (z.2.2.1.tauBig g)
    let A := (Finset.univ : Finset (Fin (J+ell))).image
      (((H.before i).2 g).1)
    let M := actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.before i) g
    let G := (Finset.univ : Finset
      (Fin ((H.ghost i g).2.1.val))).image
      (fun j => ((H.ghost i g).2.2 j).1)
    Disjoint B ((A ∪ M) ∪ G) := by
  dsimp only
  classical
  have hGood := (physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)) g
  let ghostNums := (physicalGhostFreshBirths SP smallMod
    BP bigMod (J+ell) cap (H.before i) (H.ghost i)).toFinset
  have hSeenPending (p : BP g)
      (hp : p ∈ actualPhysicalPendingSet SP smallMod BP bigMod
        J ell cap (H.before i) g) :
      bigMod g p ∈ H.seen i := by
    apply hGood.2.2.2.2 p
    simpa [actualPhysicalPendingSet, physicalOutputPendingValues,
      physicalFockProjection, Green64Fock.fockMultiset,
      Green64Fock.fockToList, Multiset.map_coe] using hp
  have hFreshNoSeen (p : BP g)
      (hp : p ∈ trueBigFreshValues (J+ell)
        ((H.edge i).2.2.1.bigChoice g).1
        (sourceBigShared J ell m (patterns (H.edge i).1) g)
        (((H.edge i).2.2.1.bigChoice g).2.2.1)
        ((H.edge i).2.2.1.tauBig g)) :
      bigMod g p ∉ H.seen i ∪ ghostNums := by
    rcases Finset.mem_image.mp hp with ⟨j, hj, hjp⟩
    have h := oriented_E_fresh_not_seen
      SP smallMod BP bigMod J ell m cap patterns
      (H.beforeE i) (H.edge i)
      (H.seen i ∪ ghostNums) (H.E_birth_eligible i hi)
      g j hj
    intro hpSeen
    exact h (by simpa only [hjp] using hpSeen)
  apply Finset.disjoint_left.mpr
  intro p hp hPrior
  have hnot := hFreshNoSeen p hp
  apply hnot
  rcases Finset.mem_union.mp hPrior with hAM | hG
  · rcases Finset.mem_union.mp hAM with ha | hm
    · rcases Finset.mem_image.mp ha with ⟨t, _, ht⟩
      have hs : bigMod g (((H.before i).2 g).1 t) ∈
          H.seen i := hGood.2.2.2.1 t
      rw [ht] at hs
      exact Finset.mem_union_left _ hs
    · exact Finset.mem_union_left _ (hSeenPending p hm)
  · rcases Finset.mem_image.mp hG with ⟨j, _, hjp⟩
    have hm := physical_G_fresh_group_mem
      SP smallMod BP bigMod (J+ell) cap
      (H.before i) (H.ghost i) g j
    have hm' : bigMod g p ∈ ghostNums := by
      simpa only [ghostNums, hjp] using List.mem_toFinset.mpr hm
    exact Finset.mem_union_right _ hm'

end Green64FullPhysicalE

end

/-! ## PhysicalActualBIGNumericalBirthFrontier -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The original global numerical seen-prime set, restricted to a
BIG group: this is not a new probability measure or proxy prime
carrier, just a finite preimage of the actual recorded birth set. -/
noncomputable def actualNumericalSeenGroup
    (seen : Finset ℕ) (g : BG) : Finset (BP g) :=
  Finset.univ.filter (fun p : BP g => bigMod g p ∈ seen)

/-- At every ORIGINAL corrected physical G_i/E_i step the real
ghost births avoid ALL earlier numerical prime births (not just
currently active/pending ones), while target fresh E births
avoid all earlier births AND the current ghost batch. -/
theorem physical_actual_BIG_birth_frontier_disjoint
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let ghostNums := (physicalGhostFreshBirths SP smallMod
      BP bigMod (J+ell) cap (H.before i) (H.ghost i)).toFinset
    let ghostValues : Finset (BP g) :=
      (Finset.univ : Finset (Fin ((H.ghost i g).2.1.val))).image
        (fun j => ((H.ghost i g).2.2 j).1)
    let eBirths : Finset (BP g) :=
      trueBigFreshValues (J+ell) ((H.edge i).2.2.1.bigChoice g).1
        (sourceBigShared J ell m (patterns (H.edge i).1) g)
        (((H.edge i).2.2.1.bigChoice g).2.2.1)
        ((H.edge i).2.2.1.tauBig g)
    Disjoint ghostValues
      (actualNumericalSeenGroup BP bigMod (H.seen i) g) ∧
    Disjoint eBirths
      (actualNumericalSeenGroup BP bigMod
        (H.seen i ∪ ghostNums) g) := by
  dsimp only
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hpSeen
    rcases Finset.mem_image.mp hp with ⟨j, _, hjp⟩
    have hnot := physical_G_fresh_group_not_seen
      SP smallMod BP bigMod (J+ell) cap
      (H.before i) (H.ghost i) (H.seen i)
      (H.G_birth_eligible i (Nat.le_of_lt hi)) g j
    apply hnot
    have hSeen : bigMod g p ∈ H.seen i := by
      simpa only [actualNumericalSeenGroup,
        Finset.mem_filter, Finset.mem_univ, true_and] using hpSeen
    simpa only [hjp] using hSeen
  · apply Finset.disjoint_left.mpr
    intro p hp hpSeen
    rcases Finset.mem_image.mp hp with ⟨j, hj, hjp⟩
    have hnot := oriented_E_fresh_not_seen
      SP smallMod BP bigMod J ell m cap patterns
      (H.beforeE i) (H.edge i)
      (H.seen i ∪ (physicalGhostFreshBirths SP smallMod
        BP bigMod (J+ell) cap (H.before i) (H.ghost i)).toFinset)
      (H.E_birth_eligible i hi) g j hj
    apply hnot
    have hSeen : bigMod g p ∈ H.seen i ∪
        (physicalGhostFreshBirths SP smallMod BP bigMod
          (J+ell) cap (H.before i) (H.ghost i)).toFinset := by
      simpa only [actualNumericalSeenGroup, Finset.mem_filter,
        Finset.mem_univ, true_and] using hpSeen
    simpa only [hjp] using hSeen

end Green64FullPhysicalE

end

/-! ## PhysicalActualGroupBirthFibre -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Original DISJOINT numerical-prime groups make the global
G birth list's numerical support restrict back to EXACTLY the
corresponding genuine group Fock-ghost birth labels. -/
theorem actual_G_numeric_birth_group_fibre
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    actualNumericalSeenGroup BP bigMod
      (physicalGhostFreshBirths SP smallMod BP bigMod
        (J+ell) cap x c).toFinset g =
    physicalGhostGroupBornSet SP smallMod BP bigMod
      J ell cap x c g := by
  unfold actualNumericalSeenGroup
  rw [physicalGhostAllGroupNumbers_exact SP smallMod BP bigMod
    J ell cap x c]
  exact global_big_numeric_batch_group_fibre BP bigMod
    (physicalGhostGroupBornSet SP smallMod BP bigMod J ell cap x c)
    hnum g

/-- The corresponding ORIGINAL E birth statement, with the
auxiliary divisor labels and OLD promotions correctly excluded. -/
theorem actual_E_numeric_birth_group_fibre
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    actualNumericalSeenGroup BP bigMod
      (orientedEFreshBirths SP smallMod BP bigMod
        J ell m cap patterns z).toFinset g =
    trueBigFreshValues (J+ell) (z.2.2.1.bigChoice g).1
      (sourceBigShared J ell m (patterns z.1) g)
      ((z.2.2.1.bigChoice g).2.2.1)
      (z.2.2.1.tauBig g) := by
  unfold actualNumericalSeenGroup
  rw [physicalEAllGroupNumbers_exact SP smallMod BP bigMod
    J ell m cap patterns x z]
  exact global_big_numeric_batch_group_fibre BP bigMod
    (fun gg => trueBigFreshValues (J+ell)
      (z.2.2.1.bigChoice gg).1
      (sourceBigShared J ell m (patterns z.1) gg)
      ((z.2.2.1.bigChoice gg).2.2.1)
      (z.2.2.1.tauBig gg)) hnum g

end Green64FullPhysicalE

end

/-! ## PhysicalActualGroupBirthSeenUpdate -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Numerical seen-set restriction preserves unions, using the
actual source group prime maps, not a surrogate birth-state law. -/
theorem actualNumericalSeenGroup_union
    (s t : Finset ℕ) (g : BG) :
    actualNumericalSeenGroup BP bigMod (s ∪ t) g =
    actualNumericalSeenGroup BP bigMod s g ∪
      actualNumericalSeenGroup BP bigMod t g := by
  classical
  ext p
  simp [actualNumericalSeenGroup, Finset.mem_union]
/-- The recorded global birth ledger in the full physical
path obeys EXACT source per-group everBorn recursion:
all previous births + genuine ghost births at visit i
+ the independently sampled fresh E target births. -/
theorem physical_actual_BIG_group_seen_update
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hi : i < N) (g : BG) :
    actualNumericalSeenGroup BP bigMod (H.seen (i+1)) g =
      (actualNumericalSeenGroup BP bigMod (H.seen i) g ∪
        physicalGhostGroupBornSet SP smallMod BP bigMod
          J ell cap (H.before i) (H.ghost i) g) ∪
        trueBigFreshValues (J+ell) ((H.edge i).2.2.1.bigChoice g).1
          (sourceBigShared J ell m (patterns (H.edge i).1) g)
          (((H.edge i).2.2.1.bigChoice g).2.2.1)
          ((H.edge i).2.2.1.tauBig g) := by
  rw [H.seen_update i hi]
  rw [actualNumericalSeenGroup_union]
  rw [actualNumericalSeenGroup_union]
  rw [actual_G_numeric_birth_group_fibre
    SP smallMod BP bigMod J ell cap
    (H.before i) (H.ghost i) hnum g]
  rw [actual_E_numeric_birth_group_fibre
    SP smallMod BP bigMod J ell m cap patterns
    (H.beforeE i) (H.edge i) hnum g]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralStoresPromotions -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Exact globally tagged source values selected by real E store indices. -/
noncomputable def physicalActualLiteralStoreValues (i : ℕ) :
    Finset (PhysicalSourcePrime BP) :=
  ((Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).filter
    (fun a => a.2 ∈ (((H.edge i).2.2.1.bigChoice a.1).2).1)).image
    (fun a => actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2)

/-- Exact globally tagged target values supplied by OLD promotions. -/
noncomputable def physicalActualLiteralPromotionValues (i : ℕ) :
    Finset (PhysicalSourcePrime BP) :=
  ((Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).filter
    (fun a => a.2 ∈ (((H.edge i).2.2.1.bigChoice a.1).2).2.1)).image
    (fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2)

/-- These indexes point into the ACTUAL flattened lists, not sets. -/
noncomputable def physicalActualLiteralStoreIndices (i : ℕ) :
    Finset (Fin (physicalActualLiteralRawSourceList SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i).length) :=
  literalIndicesFor
    (physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (physicalActualLiteralStoreValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)

noncomputable def physicalActualLiteralPromotionIndices (i : ℕ) :
    Finset (Fin (physicalActualLiteralRawTargetList SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i).length) :=
  literalIndicesFor
    (physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (physicalActualLiteralPromotionValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)

theorem physical_actual_literal_source_slot_mem_raw
    (i : ℕ) (g : BG) (j : Fin (J+ell)) :
    actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j ∈
    (physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  apply List.mem_toFinset.mpr
  unfold physicalActualLiteralRawSourceList
  apply List.mem_map.mpr
  refine ⟨⟨g, ((H.edge i).2.2.1.sigmaBig g) j⟩, ?_, ?_⟩
  · simp
  · simp [actualLiteralCanonicalSourceSlot]

theorem physical_actual_literal_target_slot_mem_raw
    (i : ℕ) (g : BG) (j : Fin (J+ell)) :
    actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j ∈
    (physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  apply List.mem_toFinset.mpr
  unfold physicalActualLiteralRawTargetList
  apply List.mem_map.mpr
  refine ⟨⟨g, ((H.edge i).2.2.1.tauBig g) j⟩, ?_, ?_⟩
  · simp
  · simp [actualLiteralCanonicalTargetSlot]

theorem physical_actual_literal_store_values_in_raw_source (i : ℕ) :
    physicalActualLiteralStoreValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ⊆
    (physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  intro p hp
  obtain ⟨⟨g,j⟩, _, rfl⟩ := Finset.mem_image.mp hp
  exact physical_actual_literal_source_slot_mem_raw
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig k N H i g j

theorem physical_actual_literal_promotion_values_in_raw_target (i : ℕ) :
    physicalActualLiteralPromotionValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ⊆
    (physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  intro p hp
  obtain ⟨⟨g,j⟩, _, rfl⟩ := Finset.mem_image.mp hp
  exact physical_actual_literal_target_slot_mem_raw
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig k N H i g j

theorem physical_actual_literal_store_index_image (i : ℕ) :
    (physicalActualLiteralStoreIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawSourceList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get =
    physicalActualLiteralStoreValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  exact literal_indices_for_image _ _
    (physical_actual_literal_store_values_in_raw_source
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i)

theorem physical_actual_literal_promotion_index_image (i : ℕ) :
    (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawTargetList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get =
    physicalActualLiteralPromotionValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  exact literal_indices_for_image _ _
    (physical_actual_literal_promotion_values_in_raw_target
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i)

/-- Authentic E legality forbids storing ANY shared canonical prime. -/
theorem physical_actual_literal_stores_disjoint_shared
    (i : ℕ) (hi : i < N) :
    Disjoint
      (physicalActualLiteralSharedPatternValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralStoreValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i) := by
  apply Finset.disjoint_left.mpr
  intro p hpS hpK
  obtain ⟨⟨g,j⟩, hj, heq⟩ := Finset.mem_image.mp hpK
  have hcanon : actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j ∈
      physicalActualLiteralSharedPatternValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i := by
    rw [heq]
    exact hpS
  have hjS := (physical_actual_literal_shared_source_pattern
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g j).mp hcanon
  have hleg := (H.E_legal i hi).2.2.2.1 g
  have hjK := (Finset.mem_filter.mp hj).2
  have hnot : j ∉ sourceBigShared J ell m (patterns (H.edge i).1) g := by
    simpa [orientedUnshared] using hleg.stores_unshared hjK
  exact hnot hjS

/-- The exact original RowValid.shared_store disjointness on the
same FLATTENED source-index type, with source permutations intact. -/
theorem physical_actual_literal_shared_store_indices_disjoint
    (i : ℕ) (hi : i < N) :
    Disjoint
      (physicalActualLiteralSharedIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralStoreIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i) := by
  apply Finset.disjoint_left.mpr
  intro j hS hK
  have hvals := physical_actual_literal_stores_disjoint_shared
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  apply Finset.disjoint_left.mp hvals
    ((literal_indices_for_exact _ _ j).mp hS)
    ((literal_indices_for_exact _ _ j).mp hK)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralPromotionOld -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- An injective selection of distinct TARGET slots into an arbitrary
literal OLD list, with equality of labels on each selected index. -/
noncomputable def literalSelectedOldInjection
    {P : Type} [DecidableEq P] (ys ms : List P)
    (S : Finset (Fin ys.length)) (hY : ys.Nodup)
    (hmem : ∀ j : S, ys.get j.1 ∈ ms) :
    S ↪ Fin ms.length := by
  let chosen (j : S) : Fin ms.length :=
    Classical.choose (List.mem_iff_get.mp (hmem j))
  have hc (j : S) : ms.get (chosen j) = ys.get j.1 :=
    (Classical.choose_spec (List.mem_iff_get.mp (hmem j)))
  exact ⟨chosen, by
    intro a b hab
    apply Subtype.ext
    apply (List.nodup_iff_injective_get.mp hY)
    exact (hc a).symm.trans ((congrArg ms.get hab).trans (hc b))⟩

theorem literal_selected_old_injection_matches
    {P : Type} [DecidableEq P] (ys ms : List P)
    (S : Finset (Fin ys.length)) (hY : ys.Nodup)
    (hmem : ∀ j : S, ys.get j.1 ∈ ms) (j : S) :
    ms.get (literalSelectedOldInjection ys ms S hY hmem j) =
      ys.get j.1 := by
  exact (Classical.choose_spec
    (List.mem_iff_get.mp (hmem j)))

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- The TRUE G_i-output Fock memory, flattened groupwise with all
OLD occurrence information in the underlying list. -/
noncomputable def physicalActualLiteralPendingAfterG (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ.toList : List BG).flatMap (fun g =>
    (Green64Fock.fockToList (((H.afterG i).2 g).2)).map
      (fun a => (⟨g, a.1⟩ : PhysicalSourcePrime BP)))

theorem physical_actual_literal_afterG_membership
    (i : ℕ) (g : BG) (p : BP g)
    (hp : p ∈ actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.afterG i) g) :
    (⟨g,p⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  unfold physicalActualLiteralPendingAfterG
  apply List.mem_flatMap.mpr
  refine ⟨g, Finset.mem_toList.mpr (Finset.mem_univ g), ?_⟩
  simpa [actualPhysicalPendingSet, List.mem_map] using
    (List.mem_toFinset.mp hp)

/-- A genuine corrected E promotion target is found in the actual
previous G-output memory. No synthetic set-based transition. -/
theorem physical_actual_literal_promoted_in_afterG
    (i : ℕ) (hi : i < N) :
    physicalActualLiteralPromotionValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ⊆
    (physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  intro p hp
  obtain ⟨⟨g,j⟩, hj, rfl⟩ := Finset.mem_image.mp hp
  have hjP := (Finset.mem_filter.mp hj).2
  let c := ((H.edge i).2.2.1.bigChoice g).2
  have hleg := (H.E_legal i hi).2.2.2.1 g
  have hmatch := hleg.promoted_matches ⟨j,hjP⟩
  have hpR :
      ((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j) ∈
      trueBigPromotedValues (bigMod g) (J+ell) (cap g)
        ((H.beforeE i).2 g) c := by
    apply Finset.mem_image.mpr
    refine ⟨⟨j,hjP⟩, Finset.mem_attach _ _, ?_⟩
    exact hmatch.symm
  have hR := (actual_physical_BIG_source_subset_laws
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g).2.2
  have hG : ((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j) ∈
      actualPhysicalPendingSet SP smallMod BP bigMod
        J ell cap (H.afterG i) g := hR hpR
  exact List.mem_toFinset.mpr (physical_actual_literal_afterG_membership
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i g _ hG)

/-- The actual RowValid.promotionOld INDEX INJECTION into the global
G-output Fock list. A chosen occurrence cannot represent two
different promoted target slots since target labels are Nodup. -/
noncomputable def physicalActualLiteralPromotionOld
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) ↪
    Fin (physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).length := by
  apply literalSelectedOldInjection _ _ _
    (physical_actual_literal_raw_target_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
  intro j
  have hj := (literal_indices_for_exact _ _ j.1).mp j.2
  have hp := physical_actual_literal_promoted_in_afterG
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi hj
  exact List.mem_toFinset.mp hp

theorem physical_actual_literal_promotion_old_matches
    (i : ℕ) (hi : i < N)
    (j : physicalActualLiteralPromotionIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    (physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).get
        (physicalActualLiteralPromotionOld SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i hi j) =
    (physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).get j.1 := by
  exact literal_selected_old_injection_matches _ _ _ _ _ _

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralGhostIndices -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Literal pre-G pending list with ORIGINAL Fock indices and group order. -/
noncomputable def physicalActualLiteralPendingBefore (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ.toList : List BG).flatMap (fun g =>
    (Green64Fock.fockToList (((H.before i).2 g).2)).map
      (fun a => (⟨g, a.1⟩ : PhysicalSourcePrime BP)))

/-- Exactly the selected OLD G terminations, with no deduplication
at the point of selecting Fock indices. -/
noncomputable def physicalActualLiteralEndedValues (i : ℕ) :
    Finset (PhysicalSourcePrime BP) :=
  (Finset.univ : Finset BG).biUnion (fun g =>
    ((H.ghost i g).1.1).image (fun j =>
      (⟨g,
        ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1⟩
        : PhysicalSourcePrime BP)))

/-- The literal original RowValid.termIndices on the flattened
pre-G pending list. -/
noncomputable def physicalActualLiteralTermIndices (i : ℕ) :
    Finset (Fin (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).length) :=
  literalIndicesFor
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (physicalActualLiteralEndedValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)

/-- Precisely the original fresh G atoms in each physical BIG group. -/
noncomputable def physicalActualLiteralGhostGroup (i : ℕ) (g : BG) :
    List (PhysicalSourcePrime BP) :=
  (List.ofFn ((H.ghost i g).2.2)).map
    (fun a => (⟨g, a.1⟩ : PhysicalSourcePrime BP))

/-- Genuine G birth list in group order; still an ordered list. -/
noncomputable def physicalActualLiteralGhostBatch (i : ℕ) :
    List (PhysicalSourcePrime BP) :=
  (Finset.univ.toList : List BG).flatMap
    (physicalActualLiteralGhostGroup SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)

theorem physical_actual_literal_ended_in_pending_before (i : ℕ) :
    physicalActualLiteralEndedValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ⊆
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  intro p hp
  obtain ⟨g, _, hpG⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpG
  apply List.mem_toFinset.mpr
  unfold physicalActualLiteralPendingBefore
  apply List.mem_flatMap.mpr
  refine ⟨g, Finset.mem_toList.mpr (Finset.mem_univ g), ?_⟩
  apply List.mem_map.mpr
  exact ⟨_, List.get_mem _ j, rfl⟩

theorem physical_actual_literal_term_index_image (i : ℕ) :
    (physicalActualLiteralTermIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).image
      (physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).get =
    physicalActualLiteralEndedValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  exact literal_indices_for_image _ _
    (physical_actual_literal_ended_in_pending_before
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i)

/-- Original source G ghosts are listed first by BIG group, then
by their genuine ordered fresh slot in that group. -/
theorem physical_actual_literal_ghost_group_order (i : ℕ) :
    physicalActualLiteralGhostBatch SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    (Finset.univ.toList : List BG).flatMap
      (physicalActualLiteralGhostGroup SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i) := rfl

theorem physical_actual_literal_ghost_group_labels (i : ℕ)
    (g : BG) (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralGhostGroup SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g) :
    physicalSourcePrimeGroup BP p = g := by
  unfold physicalActualLiteralGhostGroup at hp
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
  rfl

/-- Flattened tag-preserving G batch maps to exactly the
numeric original global birth ledger. -/
theorem physical_actual_literal_ghost_numeric_order (i : ℕ) :
    (physicalActualLiteralGhostBatch SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).map
      (physicalSourcePrimeValue BP bigMod) =
    physicalGhostFreshBirths SP smallMod BP bigMod
      (J+ell) cap (H.before i) (H.ghost i) := by
  simp [physicalActualLiteralGhostBatch, physicalActualLiteralGhostGroup,
    physicalGhostFreshBirths, physicalSourcePrimeValue, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem physical_actual_literal_ghost_nodup
    (i : ℕ) (hi : i ≤ N) :
    (physicalActualLiteralGhostBatch SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  apply List.Nodup.of_map (physicalSourcePrimeValue BP bigMod)
  rw [physical_actual_literal_ghost_numeric_order]
  exact (H.G_birth_eligible i hi).1

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryPendingRebase -/

section

open Classical

namespace Green64Literal

variable {P G : Type} [DecidableEq P] [Fintype G] {slots : G → ℕ}

/-- Ordered memory immediately after G, with the same ghost birth order. -/
noncomputable def pendingAfterRebase
    (f : SourceRow (P := P) G slots) (xs : List P) : List P :=
  xs.filter (fun p => p ∉ ended f) ++ f.ghostBatch

/-- Ordered memory after E, while retaining original physical
promotion/store sets and the TRUE original source index picks. -/
noncomputable def pendingNextRebase
    (f : SourceRow (P := P) G slots) (xs : List P) : List P :=
  (pendingAfterRebase f xs).filter (fun p => p ∉ promoted f) ++
    pick f.sourceEndpoint f.storeIndices

theorem pending_after_rebase_perm
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    (pendingAfterRebase f xs).Perm f.pendingAfter := by
  rw [h.ghost_operation]
  exact (hp.filter _).append_right _


theorem pending_next_rebase_perm
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    (pendingNextRebase f xs).Perm f.pendingNext := by
  rw [h.pending_operation]
  exact ((pending_after_rebase_perm f h xs hp).filter _).append_right _

/-- Every target OLD slot has a matching occurrence in the new
chronologically ordered after-G list. -/
theorem pending_rebase_promotion_mem
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore)
    (j : f.promotionSlots) :
    f.targetEndpoint.get j.1 ∈ pendingAfterRebase f xs := by
  apply (pending_after_rebase_perm f h xs hp).mem_iff.mpr
  rw [h.promotion_matches j]
  exact List.get_mem _ _

/-- Transport OLD-term indices and promotionOld to the new list,
without changing tau, sigma, arithmetic, residues or coefficients. -/
noncomputable def pendingRebaseRow
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    SourceRow (P := P) G slots :=
  { f with
    pendingBefore := xs
    termIndices := Green64FullPhysicalE.literalIndicesFor xs (ended f)
    pendingAfter := pendingAfterRebase f xs
    pendingNext := pendingNextRebase f xs
    promotionOld := Green64FullPhysicalE.literalSelectedOldInjection
      f.targetEndpoint (pendingAfterRebase f xs) f.promotionSlots
        h.target_nodup (pending_rebase_promotion_mem f h xs hp) }


/-- Ended OLD labels are unchanged although their literal Fin
indices are transported to the new list. -/
theorem pending_rebase_ended
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    ended (pendingRebaseRow f h xs hp) = ended f := by
  change
    (Green64FullPhysicalE.literalIndicesFor xs (ended f)).image xs.get =
      ended f
  apply Green64FullPhysicalE.literal_indices_for_image
  intro p hEnd
  apply List.mem_toFinset.mpr
  apply hp.mem_iff.mpr
  exact List.mem_toFinset.mp (ended_subset f hEnd)

theorem pending_rebase_promoted
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    promoted (pendingRebaseRow f h xs hp) = promoted f := rfl

theorem row_valid_pending_rebase
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    RowValid (pendingRebaseRow f h xs hp) := by
  classical
  have hEnd := pending_rebase_ended f h xs hp
  have hProm := pending_rebase_promoted f h xs hp
  have hAfter := pending_after_rebase_perm f h xs hp
  have hNext := pending_next_rebase_perm f h xs hp

  have hTerm : ∀ j ∈ Green64FullPhysicalE.literalIndicesFor
      xs (ended f), f.residueBefore (xs.get j) = 0 := by
    intro j hj
    have hjEnd :=
      (Green64FullPhysicalE.literal_indices_for_exact xs (ended f) j).mp hj
    obtain ⟨old, hOld, hEq⟩ := Finset.mem_image.mp hjEnd
    rw [← hEq]
    exact h.term_zero old hOld
  have hOld : ∀ p ∈ xs, p ∉ ended f →
      f.residueAfter p = f.residueBefore p := by
    intro p hm hn
    exact h.old_pending_unchanged p (hp.mem_iff.mp hm) hn
  have hSurv : ∀ p ∈ (pendingAfterRebase f xs).toFinset \
      promoted f,
      f.residueNext p = f.residueAfter p +
        ((f.offsetAfter - f.offsetBefore : ℤ) : ZMod (f.value p)) := by
    intro p hp'
    have hp'' : p ∈ f.pendingAfter.toFinset \ promoted f := by
      rcases Finset.mem_sdiff.mp hp' with ⟨hpIn, hpNot⟩
      apply Finset.mem_sdiff.mpr
      exact ⟨List.mem_toFinset.mpr
        (hAfter.mem_iff.mp (List.mem_toFinset.mp hpIn)), hpNot⟩
    exact h.surviving_translation p hp''
  have hPromo : ∀ j : f.promotionSlots,
      f.targetEndpoint.get j.1 =
      (pendingAfterRebase f xs).get
        (Green64FullPhysicalE.literalSelectedOldInjection
          f.targetEndpoint (pendingAfterRebase f xs) f.promotionSlots
            h.target_nodup (pending_rebase_promotion_mem f h xs hp) j) := by
    intro j
    symm
    exact Green64FullPhysicalE.literal_selected_old_injection_matches
      _ _ _ _ _ j

  refine {
    numerical_prime := h.numerical_prime
    numerical_injective := h.numerical_injective
    source_order := h.source_order
    target_order := h.target_order
    source_groups := h.source_groups
    target_groups := h.target_groups
    ghost_group_order := h.ghost_group_order
    ghost_group_labels := h.ghost_group_labels
    shared_canonical_copy := h.shared_canonical_copy
    shared_source_pattern := h.shared_source_pattern
    shared_target_pattern := h.shared_target_pattern
    source_perm := h.source_perm
    target_perm := h.target_perm
    source_nodup := h.source_nodup
    target_nodup := h.target_nodup
    active_nodup := h.active_nodup
    pending_nodup := hp.nodup_iff.mpr h.pending_nodup
    pendingAfter_nodup := hAfter.nodup_iff.mpr h.pendingAfter_nodup
    pendingNext_nodup := hNext.nodup_iff.mpr h.pendingNext_nodup
    ghost_nodup := h.ghost_nodup
    fresh_nodup := h.fresh_nodup
    shared_store := h.shared_store
    term_zero := hTerm
    ghost_operation := by
      simp only [hEnd]
      rfl
    promotion_matches := hPromo
    promotion_zero := h.promotion_zero
    target_operation := h.target_operation

    pending_operation := by
      simp only [hProm]
      rfl
    fresh_before_active := h.fresh_before_active
    fresh_before_unused := h.fresh_before_unused
    ghost_new := h.ghost_new
    next_fresh_unused := h.next_fresh_unused
    ever_update := h.ever_update
    auxiliary_ban := h.auxiliary_ban
    nondividing_store := h.nondividing_store
    nondividing_promotion := h.nondividing_promotion
    signed_orientation := h.signed_orientation
    divisor_from_groups := h.divisor_from_groups
    offset_update := h.offset_update
    ghost_birth_zero := h.ghost_birth_zero
    old_pending_unchanged := by
      intro p hp' hn
      change f.residueAfter p = f.residueBefore p
      change p ∈ xs at hp'
      rw [hEnd] at hn
      exact hOld p hp' hn
    store_reset := h.store_reset
    surviving_translation := by
      intro p hp'
      change f.residueNext p = f.residueAfter p +
        ((f.offsetAfter - f.offsetBefore : ℤ) : ZMod (f.value p))
      change p ∈ (pendingAfterRebase f xs).toFinset \
        promoted (pendingRebaseRow f h xs hp) at hp'
      rw [hProm] at hp'
      exact hSurv p hp'
    shared_congruence := h.shared_congruence
  }

end Green64Literal

end

/-! ## PhysicalActualLiteralHistoryPendingChain -/

section

open Classical

namespace Green64Literal

variable {P G : Type} [DecidableEq P] [Fintype G] {slots : G → ℕ}

/-- Deterministic chronological OLD-particle list. In particular, it is
not the Fock representative's independently chosen order. -/
noncomputable def coherentPending
    (rows : ℕ → SourceRow (P := P) G slots) : ℕ → List P
  | 0 => (rows 0).pendingBefore
  | i+1 => pendingNextRebase (rows i) (coherentPending rows i)

/-- The new chronological list describes exactly the same actual
physical pending atoms as the original independently ordered row. -/
theorem coherent_pending_perm
    (N : ℕ) (rows : ℕ → SourceRow (P := P) G slots)
    (hvalid : ∀ i, i < N → RowValid (rows i))
    (hstep : ∀ i, i < N →
      (rows i).pendingNext.Perm (rows (i+1)).pendingBefore)
    (i : ℕ) (hi : i ≤ N) :
    (coherentPending rows i).Perm (rows i).pendingBefore := by
  induction i with
  | zero => exact List.Perm.refl _
  | succ j ih =>
      have hj : j < N := by omega
      have hprev := ih (Nat.le_of_lt hj)
      exact (pending_next_rebase_perm (rows j)
        (hvalid j hj) (coherentPending rows j) hprev).trans
          (hstep j hj)

/-- Original source rows with a coherent OLD-list chronology, using
the real OLD term/promotion indices transported by the row lemma. -/
noncomputable def coherentPendingRow
    (N : ℕ) (rows : ℕ → SourceRow (P := P) G slots)
    (hvalid : ∀ i, i < N → RowValid (rows i))
    (hstep : ∀ i, i < N →
      (rows i).pendingNext.Perm (rows (i+1)).pendingBefore)
    (i : ℕ) (hi : i < N) :
    SourceRow (P := P) G slots :=
  pendingRebaseRow (rows i) (hvalid i hi) (coherentPending rows i)
    (coherent_pending_perm N rows hvalid hstep i (Nat.le_of_lt hi))

theorem coherent_pending_row_valid
    (N : ℕ) (rows : ℕ → SourceRow (P := P) G slots)
    (hvalid : ∀ i, i < N → RowValid (rows i))
    (hstep : ∀ i, i < N →
      (rows i).pendingNext.Perm (rows (i+1)).pendingBefore)
    (i : ℕ) (hi : i < N) :
    RowValid (coherentPendingRow N rows hvalid hstep i hi) := by
  exact row_valid_pending_rebase _ (hvalid i hi) _
    (coherent_pending_perm N rows hvalid hstep i (Nat.le_of_lt hi))

/-- Crucial exact LIST equality with the next chronological visit.
No conversion through Finset takes place in this statement. -/
theorem coherent_pending_next_eq
    (N : ℕ) (rows : ℕ → SourceRow (P := P) G slots)
    (hvalid : ∀ i, i < N → RowValid (rows i))
    (hstep : ∀ i, i < N →
      (rows i).pendingNext.Perm (rows (i+1)).pendingBefore)
    (i : ℕ) (hi : i < N) :
    (coherentPendingRow N rows hvalid hstep i hi).pendingNext =
      coherentPending rows (i+1) := by
  rfl


theorem coherent_pending_before_eq
    (N : ℕ) (rows : ℕ → SourceRow (P := P) G slots)
    (hvalid : ∀ i, i < N → RowValid (rows i))
    (hstep : ∀ i, i < N →
      (rows i).pendingNext.Perm (rows (i+1)).pendingBefore)
    (i : ℕ) (hi : i < N) :
    (coherentPendingRow N rows hvalid hstep i hi).pendingBefore =
      coherentPending rows i := by
  rfl

end Green64Literal

end

/-! ## PhysicalActualResidueTransport -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Exact source E pending-residue transport at the ATOM level.
Unlike a set-of-primes statement, this remembers the old residue
and its translation, and checks that a stored prime is reset at
the current signed step. Each OLD promotion is removed by its
actual indexed injection; nothing is deduplicated. -/
theorem physical_oriented_E_pending_atom_iff
    (x : BigState modulus M B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (a : Green64Fock.Atom P modulus) :
    a ∈ physicalPendingMultiset modulus M B x sigma step c ↔
      (∃ j ∈ survivorIndices modulus M B x c,
        Green64PhysicalEdge.translateAtom step (x.2.2 j) = a) ∨
      (∃ j ∈ c.1,
        (⟨x.1 (sigma j), (step : ZMod (modulus (x.1 (sigma j))))⟩
          : Green64Fock.Atom P modulus) = a) := by
  simp [physicalPendingMultiset, physicalPendingOutput,
    survivors, newlyStored, List.mem_append, List.mem_map]

/-- The literal G row preserves OLD residues exactly and introduces
fresh ghost residues at zero. All genuinely indexed OLD deletions
and ordered fresh particles are retained, including repeated atoms. -/
theorem physical_G_pending_atom_iff
    {U : Type} [DecidableEq U]
    (old : List U) (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → U) (a : U) :
    a ∈ Green64MemoryGhostOp.afterGhost old A fresh ↔
      (∃ j : Fin old.length, j ∉ A ∧ old.get j = a) ∨
      (∃ j : Fin b, fresh j = a) := by
  simp [Green64MemoryGhostOp.afterGhost, List.mem_append,
    List.mem_map, List.mem_ofFn]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The real G-to-E orbit reordering preserves ALL prime-residue
atoms, including their multiplicities. This is stronger than the
previously certified prime-set clock conservation. -/
theorem physical_actual_GE_orbit_preserves_atoms
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG)
    (a : Green64Fock.Atom (BP g) (bigMod g)) :
    a ∈ Green64Fock.fockMultiset (((H.beforeE i).2 g).2) ↔
    a ∈ Green64Fock.fockMultiset (((H.afterG i).2 g).2) := by
  have hh := congrArg
    (fun o : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
       ((o.2 g).2)) (H.E_orbit_input i hi)
  simp only [physicalFockProjection] at hh
  rw [hh]

/-- A real G_i witness has exactly the old surviving residue atoms
and the independently drawn zero-residue ghosts; its OLD deletion
choice is restricted by the original zeroOld predicate. -/
theorem physical_actual_G_pending_atoms_exact
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i ≤ N) (g : BG)
    (a : Green64Fock.Atom (BP g) (bigMod g)) :
    a ∈ Green64Fock.fockMultiset (((H.afterG i).2 g).2) ↔
      (∃ j : Fin (Green64Fock.fockToList
          (((H.before i).2 g).2)).length,
        j ∉ ((H.ghost i g).1.1) ∧
        (Green64Fock.fockToList (((H.before i).2 g).2)).get j = a) ∨
      (∃ j : Fin ((H.ghost i g).2.1.val),
        (H.ghost i g).2.2 j = a) := by
  have hG := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod (J+ell) cap q rho N i
    Vbig muBig (H.before i) (H.afterG i) (H.ghost i)
    (H.G_nonzero i hi)).2 g
  change a ∈ (Green64Fock.fockToList (((H.afterG i).2 g).2)
    : Multiset _) ↔ _
  rw [← hG]
  exact physical_G_pending_atom_iff
    (Green64Fock.fockToList (((H.before i).2 g).2))
    ((H.ghost i g).1.1) ((H.ghost i g).2.2) a

/-- Exact E_i residue-valued transition on the TRUE oriented
physical witness path. The new-visit incoming Fock MULTISET is
the translated surviving OLD atoms together with freshly stored
atoms anchored at the signed Δ. This is not the set-level clock. -/
theorem physical_actual_oriented_E_pending_atoms_exact
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG)
    (a : Green64Fock.Atom (BP g) (bigMod g)) :
    let x := (H.beforeE i).2 g
    let b := (H.edge i).2.2.1
    let c := (b.bigChoice g).2
    let step := sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns (H.edge i).1) (H.edge i).2.1
      (H.beforeE i) b.sigmaBig (H.edge i).2.2.2.1
      (physicalAlternatingSign i) k
    a ∈ Green64Fock.fockMultiset (((H.before (i+1)).2 g).2) ↔
      (∃ j ∈ survivorIndices (bigMod g) (J+ell) (cap g) x c,
        Green64PhysicalEdge.translateAtom step (x.2.2 j) = a) ∨
      (∃ j ∈ c.1,
        (⟨x.1 (b.sigmaBig g j),
           (step : ZMod (bigMod g (x.1 (b.sigmaBig g j))))⟩
           : Green64Fock.Atom (BP g) (bigMod g)) = a) := by
  dsimp only
  have h := congrArg
    (fun o : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (o.2 g).2) (H.E_output i hi)
  have hh :
      Green64Fock.fockMultiset (((H.before (i+1)).2 g).2) =
      physicalPendingMultiset (bigMod g) (J+ell) (cap g)
        ((H.beforeE i).2 g) ((H.edge i).2.2.1.sigmaBig g)
        (sourceOrientedStep SP smallMod BP bigMod
          J ell m cap (patterns (H.edge i).1) (H.edge i).2.1
          (H.beforeE i) (H.edge i).2.2.1.sigmaBig
          (H.edge i).2.2.2.1 (physicalAlternatingSign i) k)
        ((H.edge i).2.2.1.bigChoice g).2 := by
    simpa [physicalFockProjection, sourceOrientedPhysicalOutput,
      fullPhysicalBranchOutput, bigGroupBranchOutput,
      physicalBranchOutput] using h
  rw [hh]
  exact physical_oriented_E_pending_atom_iff
    (bigMod g) (J+ell) (cap g) ((H.beforeE i).2 g)
    ((H.edge i).2.2.1.sigmaBig g)
    (sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns (H.edge i).1) (H.edge i).2.1
      (H.beforeE i) (H.edge i).2.2.1.sigmaBig
      (H.edge i).2.2.2.1 (physicalAlternatingSign i) k)
    ((H.edge i).2.2.1.bigChoice g).2 a

end Green64FullPhysicalE

end

/-! ## PhysicalActualFockReindex -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- A symmetric Fock orbit with distinct physical atoms canonically
identifies each OLD slot of one ordering with its exact atom in
every other ordering. This is a bijection of INDICES, not a
replacement of ordered memory by its set of prime values. -/
theorem physical_nodup_fock_reindex
    {U : Type} [DecidableEq U]
    (left right : List U)
    (heq : (left : Multiset U) = (right : Multiset U))
    (hl : left.Nodup) :
    ∃ e : Fin left.length ≃ Fin right.length,
      ∀ j, left.get j = right.get (e j) := by
  have hr : right.Nodup := by
    apply Multiset.coe_nodup.mp
    rw [← heq]
    exact Multiset.coe_nodup.mpr hl
  have hmem (a : U) : a ∈ left ↔ a ∈ right := by
    have hh := congrArg (fun m : Multiset U => a ∈ m) heq
    simpa using hh
  let eMem : {a : U // a ∈ left} ≃ {a : U // a ∈ right} :=
    { toFun := fun a => ⟨a.1, (hmem a.1).mp a.2⟩
      invFun := fun a => ⟨a.1, (hmem a.1).mpr a.2⟩
      left_inv := by intro a; cases a; rfl
      right_inv := by intro a; cases a; rfl }
  let e : Fin left.length ≃ Fin right.length :=
    ((hl.getEquiv left).trans eMem).trans (hr.getEquiv right).symm
  refine ⟨e, ?_⟩
  intro j
  have hh : (hr.getEquiv right) (e j) =
      eMem ((hl.getEquiv left) j) := by
    simp [e]
  have hv := congrArg Subtype.val hh
  simpa [List.Nodup.getEquiv, eMem] using hv.symm

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Physical G -> E Fock quotient supplies an actual permutation
of OLD INDICES. Consequently a source E promotion injection into
beforeE can be moved to the literal G-output order, with exact
prime-residue atoms (and therefore exact zero/divisor tests)
unchanged. The permutation is derived from the physical orbit and
distinct-birth invariant rather than postulated as a transition. -/
theorem physical_actual_GE_old_index_promotion_transport
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let oldG := Green64Fock.fockToList (((H.afterG i).2 g).2)
    let oldE := Green64Fock.fockToList (((H.beforeE i).2 g).2)
    let c := ((H.edge i).2.2.1.bigChoice g).2
    ∃ equiv : Fin oldG.length ≃ Fin oldE.length,
      (∀ j, oldG.get j = oldE.get (equiv j)) ∧
      ∃ lift : (↥c.2.1) ↪ Fin oldG.length,
        ∀ j, oldG.get (lift j) =
          (((H.beforeE i).2 g).2.2 (c.2.2 j)) := by
  dsimp only
  let oldG := Green64Fock.fockToList (((H.afterG i).2 g).2)
  let oldE := Green64Fock.fockToList (((H.beforeE i).2 g).2)
  let c := ((H.edge i).2.2.1.bigChoice g).2
  have hPrev := physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)
  have hG := actual_G_preserves_physical_good_orbit
    SP smallMod BP bigMod (J+ell) cap q rho N i Vbig muBig
    (H.before i) (H.afterG i) (H.ghost i) (H.seen i)
    hPrev (H.G_nonzero i (Nat.le_of_lt hi))
    (H.G_birth_eligible i (Nat.le_of_lt hi))
  have hprime : ((Green64Fock.fockMultiset
       (((H.afterG i).2 g).2)).map (fun a => a.1)).Nodup :=
    (hG g).2.1
  have hn : oldG.Nodup := by
    apply List.Nodup.of_map
      (fun a : Green64Fock.Atom (BP g) (bigMod g) => a.1)
    simpa [oldG, Green64Fock.fockMultiset,
      Green64Fock.fockToList, Multiset.map_coe,
      Multiset.coe_nodup] using hprime
  have hproj := congrArg
    (fun o : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (o.2 g).2) (H.E_orbit_input i hi)
  have hm : (oldG : Multiset (Green64Fock.Atom (BP g) (bigMod g))) =
      (oldE : Multiset (Green64Fock.Atom (BP g) (bigMod g))) := by
    simpa [oldG, oldE, physicalFockProjection,
      Green64Fock.fockMultiset, Green64Fock.fockToList]
      using hproj.symm
  obtain ⟨equiv, he⟩ :=
    physical_nodup_fock_reindex oldG oldE hm hn
  refine ⟨equiv, he, ?_⟩
  have hlen : oldE.length =
      (((H.beforeE i).2 g).2).1.val := by
    simp [oldE, Green64Fock.fockToList]
  let lift : (↥c.2.1) ↪ Fin oldG.length :=
    ⟨fun j => equiv.symm (Fin.cast hlen.symm (c.2.2 j)),
      by
        intro a b hab
        apply c.2.2.injective
        apply Fin.cast_injective hlen.symm
        exact equiv.symm.injective hab⟩
  refine ⟨lift, ?_⟩
  intro j
  have hp := he (lift j)
  have hidx : equiv (lift j) =
      Fin.cast hlen.symm (c.2.2 j) := by
    change equiv (equiv.symm (Fin.cast hlen.symm (c.2.2 j))) = _
    exact equiv.apply_symm_apply _
  rw [hidx] at hp
  simpa [oldG, oldE, Green64Fock.fockToList, Fin.cast] using hp

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralResidueWitness -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Distinct Fock prime labels determine a UNIQUE stored residue
at each prime, even before quotienting by Fock permutation. -/
theorem physical_literal_fock_residue_unique
    {P : Type} [DecidableEq P] (modulus : P → ℕ)
    (xs : List (Green64Fock.Atom P modulus))
    (hN : (xs.map fun a => a.1).Nodup)
    (p : P) (r s : ZMod (modulus p))
    (hr : (⟨p,r⟩ : Green64Fock.Atom P modulus) ∈ xs)
    (hs : (⟨p,s⟩ : Green64Fock.Atom P modulus) ∈ xs) :
    r = s := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
  obtain ⟨l, hl⟩ := List.mem_iff_get.mp hs
  have hElem : xs.get j = xs.get l := by
    apply List.inj_on_of_nodup_map hN
      (List.get_mem xs j) (List.get_mem xs l)
    simp only [hj, hl]
  have hAtom : (⟨p,r⟩ : Green64Fock.Atom P modulus) =
      (⟨p,s⟩ : Green64Fock.Atom P modulus) :=
    hj.symm.trans (hElem.trans hl)
  exact eq_of_heq (Sigma.mk.inj_iff.mp hAtom).2

/-- Residue in a physical BIG pending Fock memory at p, chosen from
an ACTUAL prime/residue atom when present; 0 when absent. -/
noncomputable def physicalLiteralFockResidue
    {BG : Type} (BP : BG → Type)
    (bigMod : (g : BG) → BP g → ℕ)
    {M : ℕ} (cap : BG → ℕ)
    {SG : Type} (SP : SG → Type)
    (smallMod : (g : SG) → SP g → ℕ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (p : PhysicalSourcePrime BP) :
    ZMod (physicalSourcePrimeValue BP bigMod p) :=
  if h : ∃ r : ZMod (bigMod p.1 p.2),
      (⟨p.2,r⟩ : Green64Fock.Atom (BP p.1) (bigMod p.1)) ∈
        Green64Fock.fockMultiset (((x.2 p.1).2)) then
    Classical.choose h
  else 0

theorem physical_literal_fock_residue_of_atom
    {BG : Type} (BP : BG → Type)
    (bigMod : (g : BG) → BP g → ℕ)
    {M : ℕ} (cap : BG → ℕ)
    {SG : Type} (SP : SG → Type)
    (smallMod : (g : SG) → SP g → ℕ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (p : PhysicalSourcePrime BP)
    (hN : ((Green64Fock.fockToList (((x.2 p.1).2))).map
      (fun a => a.1)).Nodup)
    (r : ZMod (bigMod p.1 p.2))
    (hr : (⟨p.2,r⟩ : Green64Fock.Atom (BP p.1) (bigMod p.1)) ∈
      Green64Fock.fockMultiset (((x.2 p.1).2))) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod x p = r := by
  let h : ∃ r' : ZMod (bigMod p.1 p.2),
      (⟨p.2,r'⟩ : Green64Fock.Atom (BP p.1) (bigMod p.1)) ∈
        Green64Fock.fockMultiset (((x.2 p.1).2)) := ⟨r,hr⟩
  have hc : (⟨p.2,Classical.choose h⟩ :
      Green64Fock.Atom (BP p.1) (bigMod p.1)) ∈
      Green64Fock.fockMultiset (((x.2 p.1).2)) :=
    Classical.choose_spec h
  have hcl : (⟨p.2,Classical.choose h⟩ :
      Green64Fock.Atom (BP p.1) (bigMod p.1)) ∈
      Green64Fock.fockToList (((x.2 p.1).2)) := by
    simpa [Green64Fock.fockMultiset, Green64Fock.fockToList] using hc
  have hrl : (⟨p.2,r⟩ :
      Green64Fock.Atom (BP p.1) (bigMod p.1)) ∈
      Green64Fock.fockToList (((x.2 p.1).2)) := by
    simpa [Green64Fock.fockMultiset, Green64Fock.fockToList] using hr
  have hu := physical_literal_fock_residue_unique (bigMod p.1)
    (Green64Fock.fockToList (((x.2 p.1).2)))
    hN p.2 (Classical.choose h) r hcl hrl
  unfold physicalLiteralFockResidue
  rw [dif_pos h]
  exact hu

end Green64FullPhysicalE

end

/-! ## PhysicalActualPromotionResidueLaw -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The OLD promotion zero condition on the literal G-output order.
The true E input is independently permuted. Transporting its
indexed OLD injection back through the physical Fock orbit gives
the exact same prime-residue zero check, without an assumption
on an abstract or merely set-valued transition. -/
theorem physical_actual_literal_old_promotion_zero
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let oldG := Green64Fock.fockToList (((H.afterG i).2 g).2)
    let c := ((H.edge i).2.2.1.bigChoice g).2
    let step := sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns (H.edge i).1)
      (H.edge i).2.1 (H.beforeE i)
      (H.edge i).2.2.1.sigmaBig (H.edge i).2.2.2.1
      (physicalAlternatingSign i) k
    ∃ lift : (↥c.2.1) ↪ Fin oldG.length,
      ∀ j, (oldG.get (lift j)).2 +
        (step : ZMod (bigMod g (oldG.get (lift j)).1)) = 0 := by
  dsimp only
  obtain ⟨equiv, hPerm, ⟨lift, hAtom⟩⟩ :=
    physical_actual_GE_old_index_promotion_transport
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hi g
  have hbig := ((H.E_legal i hi).2.2.2.1 g)
  refine ⟨lift, ?_⟩
  intro j
  have hz := hbig.promoted_zero j
  have hEq := hAtom j
  rw [hEq]
  exact hz

/-- Source literal store-reset law, at an ACTUAL oriented E branch:
a chosen SMALL/BIG source OLD-active prime is stored as a genuine
physical Fock atom with residue equal to the global signed step.
No set-level approximation, arbitrary independent sigma is retained. -/
theorem physical_actual_literal_store_residue_delta
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let x := (H.beforeE i).2 g
    let b := (H.edge i).2.2.1
    let c := (b.bigChoice g).2
    let step := sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns (H.edge i).1)
      (H.edge i).2.1 (H.beforeE i)
      b.sigmaBig (H.edge i).2.2.2.1
      (physicalAlternatingSign i) k
    ∀ j ∈ c.1,
      (⟨x.1 (b.sigmaBig g j),
        (step : ZMod (bigMod g (x.1 (b.sigmaBig g j))))⟩
        : Green64Fock.Atom (BP g) (bigMod g)) ∈
      Green64Fock.fockMultiset (((H.before (i+1)).2 g).2) := by
  dsimp only
  intro j hj
  have hiff := physical_actual_oriented_E_pending_atoms_exact
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g
    (⟨((H.beforeE i).2 g).1 ((H.edge i).2.2.1.sigmaBig g j),
      (sourceOrientedStep SP smallMod BP bigMod J ell m cap
        (patterns (H.edge i).1) (H.edge i).2.1
        (H.beforeE i) (H.edge i).2.2.1.sigmaBig
        (H.edge i).2.2.2.1 (physicalAlternatingSign i) k
        : ZMod (bigMod g (((H.beforeE i).2 g).1
          ((H.edge i).2.2.1.sigmaBig g j))))⟩)
  exact hiff.mpr (Or.inr ⟨j, hj, rfl⟩)

/-- Source literal surviving-residue translation: the actual OLD
Fock atom moves from r to r + signed Delta on an oriented E row.
This is the genuine list-indexed survivor, not an image of a set. -/
theorem physical_actual_literal_survivor_residue_translation
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let x := (H.beforeE i).2 g
    let b := (H.edge i).2.2.1
    let c := (b.bigChoice g).2
    let step := sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns (H.edge i).1)
      (H.edge i).2.1 (H.beforeE i)
      b.sigmaBig (H.edge i).2.2.2.1
      (physicalAlternatingSign i) k
    ∀ j ∈ survivorIndices (bigMod g) (J+ell) (cap g) x c,
      Green64PhysicalEdge.translateAtom step (x.2.2 j) ∈
        Green64Fock.fockMultiset (((H.before (i+1)).2 g).2) := by
  dsimp only
  intro j hj
  have hiff := physical_actual_oriented_E_pending_atoms_exact
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g
    (Green64PhysicalEdge.translateAtom
      (sourceOrientedStep SP smallMod BP bigMod J ell m cap
        (patterns (H.edge i).1) (H.edge i).2.1
        (H.beforeE i) (H.edge i).2.2.1.sigmaBig
        (H.edge i).2.2.2.1 (physicalAlternatingSign i) k)
      (((H.beforeE i).2 g).2.2 j))
  exact hiff.mpr (Or.inl ⟨j, hj, rfl⟩)

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostScalarExact -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- A nonzero ORIGINAL physical G witness cannot create a ghost
particle with nonzero residue. This derives birth-at-zero from
the raw complex coefficient, without a synthetic birth hypothesis. -/
theorem physical_actual_nonzero_G_ghost_birth_zero
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (hterm : physicalGBranchTerm SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c ≠ 0)
    (g : BG) (j : Fin ((c g).2.1.val)) :
    ((c g).2.2 j).2 = 0 := by
  have hstate := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod M cap q rho N i Vbig muBig
    x y c hterm).1
  have hprod : (∏ g : BG,
      ghostWitnessTerm
        (Green64Fock.fockToList ((x.2 g).2))
        (Green64Fock.fockToList ((y.2 g).2))
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
        (cap g)
        (-(sourceVisitEta q N i : ℂ) / (rho : ℂ))
        ((sourceVisitQ q N i : ℂ) / (rho : ℂ)^2)
        (-(sourceVisitEta q N i : ℂ) * (Vbig g : ℂ) / (rho : ℂ))
        (Green64Fock.sourceBirthNu (fun p : BP g => (muBig g p : ℂ)))
        (c g)) ≠ 0 := by
    simpa only [physicalGBranchTerm, if_pos hstate] using hterm
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) g (Finset.mem_univ g)
  by_contra hbad
  have hzero := Green64Fock.sourceG_wrong_residue_birth_vanishes
    (Green64Fock.fockToList ((x.2 g).2)) (c g).1.1
    (c g).2.2 j hbad
    (-(sourceVisitEta q N i : ℂ) / (rho : ℂ))
    ((sourceVisitQ q N i : ℂ) / (rho : ℂ)^2)
    (-(sourceVisitEta q N i : ℂ) * (Vbig g : ℂ) / (rho : ℂ))
    (fun p : BP g => (muBig g p : ℂ))
  have : ghostWitnessTerm
      (Green64Fock.fockToList ((x.2 g).2))
      (Green64Fock.fockToList ((y.2 g).2))
      (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
      (cap g)
      (-(sourceVisitEta q N i : ℂ) / (rho : ℂ))
      ((sourceVisitQ q N i : ℂ) / (rho : ℂ)^2)
      (-(sourceVisitEta q N i : ℂ) * (Vbig g : ℂ) / (rho : ℂ))
      (Green64Fock.sourceBirthNu (fun p : BP g => (muBig g p : ℂ)))
      (c g) = 0 := by
    unfold ghostWitnessTerm
    split_ifs with hmatch
    · convert hzero using 1 <;> ring
    · rfl
  exact hfactor this

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostWeight -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- The literal expansion of one ORIGINAL G_i witness in one BIG group.
It is a scalar extracted from the raw indexed G, not a new operator.
No zero-residue 1/p, no added Fock j!, one original ghost 1/b!. -/
noncomputable def physicalActualGhostFactor
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (g : BG) : ℂ :=
  let old := Green64Fock.fockToList ((x.2 g).2)
  let A := (c g).1.1
  let b := (c g).2.1.val
  let fresh := (c g).2.2
  (-(sourceVisitEta q N i : ℂ) / (rho : ℂ)) ^ A.card *
  ((sourceVisitQ q N i : ℂ) / (rho : ℂ)^2) ^
    ((Green64MemoryGhostOp.zeroOld old
      (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)).card - A.card) *
  (1 / (Nat.factorial b : ℂ)) *
  (-(sourceVisitEta q N i : ℂ) * (Vbig g : ℂ) / (rho : ℂ)) ^ b *
  (∏ j : Fin b, (muBig g (fresh j).1 : ℂ))

/-- Every contributing raw G witness has precisely the independent-
residue ghost-row multiplier from the source, with the actual old
zero indices and independently sampled zero-residue fresh ghosts. -/
theorem physical_actual_G_group_weight_exact
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (hterm : physicalGBranchTerm SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c ≠ 0)
    (g : BG) :
    ghostWitnessTerm
      (Green64Fock.fockToList ((x.2 g).2))
      (Green64Fock.fockToList ((y.2 g).2))
      (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
      (cap g)
      (-(sourceVisitEta q N i : ℂ) / (rho : ℂ))
      ((sourceVisitQ q N i : ℂ) / (rho : ℂ)^2)
      (-(sourceVisitEta q N i : ℂ) * (Vbig g : ℂ) / (rho : ℂ))
      (Green64Fock.sourceBirthNu (fun p : BP g => (muBig g p : ℂ)))
      (c g) =
    physicalActualGhostFactor SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x c g := by
  have hout := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod M cap
    q rho N i Vbig muBig x y c hterm).2 g
  have hnu (j : Fin ((c g).2.1.val)) :
      Green64Fock.sourceBirthNu
        (fun p : BP g => (muBig g p : ℂ)) ((c g).2.2 j) =
        (muBig g ((c g).2.2 j).1 : ℂ) := by
    have hz := physical_actual_nonzero_G_ghost_birth_zero
      SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c hterm g j
    simp [Green64Fock.sourceBirthNu, Green64Fock.birthMass, hz]
  simp only [ghostWitnessTerm, if_pos hout]
  unfold physicalActualGhostFactor Green64MemoryGhostOp.sourceGhostTerm
  dsimp only
  simp_rw [hnu]

end Green64FullPhysicalE

end

