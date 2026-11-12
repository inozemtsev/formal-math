module

public import Green64.Library.Correlation.Part014
public import Green64.Library.Correlation.Part005
public import Green64.Library.Weights.Part022
public import Green64.Library.Correlation.Part007
public import Green64.Library.Correlation.Part008

@[expose] public section

/-!
# Correlation / Part015

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalActualLiteralRowFrame -/

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

noncomputable abbrev literalRowFrameAux
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (hi : i < N) :=
  physicalActualLiteralSourceRow SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor i hi

/-- Source hypotheses are actual numerical prime and distinctness
conditions; no bogus conclusion from nonzero moduli. -/
theorem physical_actual_literal_row_prime_fields
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (hi : i < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod)) :
    (∀ p, Nat.Prime ((literalRowFrameAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).value p)) ∧
    Function.Injective ((literalRowFrameAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).value) := by
  constructor
  · intro p
    exact hprime p.1 p.2
  · exact hnum
/-- Certified source/target frames, independent inverse sigma/tau,
active and pending nodup, chronological exact operations, and
original source group labels. -/
theorem physical_actual_literal_row_frame_fields
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (hi : i < N) :
    let f := literalRowFrameAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
    (f.sourceEndpoint =
      (Finset.univ : Finset (Σ g : BG, Fin (J+ell))).toList.map
        (fun a => f.activeSlots a.1 (f.sourcePerm a.1 a.2))) ∧
    (f.targetEndpoint =
      (Finset.univ : Finset (Σ g : BG, Fin (J+ell))).toList.map
        (fun a => f.nextSlots a.1 (f.targetPerm a.1 a.2))) ∧
    (∀ g j, f.labelGroup (f.activeSlots g j) = g) ∧
    (∀ g j, f.labelGroup (f.nextSlots g j) = g) ∧
    (f.ghostBatch = (Finset.univ.toList : List BG).flatMap f.ghostBatches) ∧
    (∀ g p, p ∈ f.ghostBatches g → f.labelGroup p = g) ∧
    (∀ g j, j ∈ f.patternShared g →
      f.activeSlots g j = f.nextSlots g j) ∧
    (∀ g j, f.activeSlots g j ∈ Green64Literal.shared f ↔
      j ∈ f.patternShared g) ∧
    (∀ g j, f.nextSlots g j ∈ Green64Literal.shared f ↔
      j ∈ f.patternShared g) ∧
    f.sourceEndpoint.Perm f.active ∧
    f.targetEndpoint.Perm f.nextActive ∧
    f.sourceEndpoint.Nodup ∧ f.targetEndpoint.Nodup ∧
    f.active.Nodup ∧ f.pendingBefore.Nodup ∧
    f.pendingAfter.Nodup ∧ f.pendingNext.Nodup ∧
    f.ghostBatch.Nodup ∧
    Disjoint f.sharedIndices f.storeIndices ∧
    (f.pendingAfter = f.pendingBefore.filter
        (fun p => p ∉ Green64Literal.ended f) ++ f.ghostBatch) ∧
    (∀ j : f.promotionSlots,
      f.targetEndpoint.get j.val = f.pendingAfter.get (f.promotionOld j)) ∧
    (f.pendingNext = f.pendingAfter.filter
        (fun p => p ∉ Green64Literal.promoted f) ++
      Green64Literal.pick f.sourceEndpoint f.storeIndices) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact physical_actual_literal_source_order SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i
  · exact physical_actual_literal_target_order SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i
  · intro g j; rfl
  · intro g j; rfl
  · rfl
  · intro g p hp
    exact physical_actual_literal_ghost_group_labels
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i g p hp
  · intro g j hj
    exact physical_actual_literal_shared_canonical_copy
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g j hj
  · intro g j
    change actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j ∈
      (physicalActualLiteralSharedIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawSourceList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get ↔
      j ∈ sourceBigShared J ell m (patterns (H.edge i).1) g
    exact physical_actual_literal_shared_index_source_pattern
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g j
  · intro g j
    change actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g j ∈
      (physicalActualLiteralSharedIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawSourceList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get ↔
      j ∈ sourceBigShared J ell m (patterns (H.edge i).1) g
    rw [physical_actual_literal_shared_index_image]
    exact physical_actual_literal_shared_target_pattern
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g j
  · exact physical_actual_literal_source_perm SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i hi
  · exact physical_actual_literal_target_perm SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i hi
  · exact physical_actual_literal_raw_source_nodup SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i hi
  · exact physical_actual_literal_raw_target_nodup SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i hi
  · exact physical_actual_literal_canonical_source_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi
  · exact physical_actual_literal_pending_before_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi)
  · exact physical_actual_literal_chrono_afterG_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi)
  · exact physical_actual_literal_chrono_next_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi
  · exact physical_actual_literal_ghost_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi)
  · exact physical_actual_literal_shared_store_indices_disjoint
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi
  · exact physical_actual_literal_chronological_ghost_operation
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i
  · intro j
    exact physical_actual_literal_chronological_promotion_matches
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi j
  · exact physical_actual_literal_chrono_next_pending_operation
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowResidues -/

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
variable (Vsmall : SG → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
variable (i : ℕ) (hi : i < N)

noncomputable abbrev literalRowResiduesAux :=
  physicalActualLiteralSourceRow SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor i hi
/-- On every actually present OLD particle, the literal residue
is exactly the measured Fock residue. The independent anchor
is only used for labels not present in this Fock memory. -/
theorem physical_actual_literal_row_residue_before_of_mem
    (p : PhysicalSourcePrime BP)
    (hp : p ∈ (literalRowResiduesAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).pendingBefore) :
    (literalRowResiduesAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).residueBefore p =
    physicalLiteralFockResidue BP bigMod cap SP smallMod (H.before i) p := by
  cases p with
  | mk g v =>
    have hmem := (physical_actual_literal_before_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i g v).mp hp
    change (if v ∈
      (Green64Fock.fockToList (((H.before i).2 g).2)).map
        (fun a => a.1) then
      physicalLiteralFockResidue BP bigMod cap SP smallMod
        (H.before i) (⟨g,v⟩ : PhysicalSourcePrime BP)
      else physicalActualAnchorResidue SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H anchor i g v) =
      physicalLiteralFockResidue BP bigMod cap SP smallMod
        (H.before i) (⟨g,v⟩ : PhysicalSourcePrime BP)
    simp [hmem]

/-- After-G residue readout is exact even if the physical E input
Fock representative is independently permuted. -/
theorem physical_actual_literal_row_residue_after_of_mem
    (p : PhysicalSourcePrime BP)
    (hp : p ∈ (literalRowResiduesAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).pendingAfter) :
    (literalRowResiduesAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).residueAfter p =
    physicalLiteralFockResidue BP bigMod cap SP smallMod (H.afterG i) p := by
  cases p with
  | mk g v =>
    have hsupport := congrArg
      (fun s : Finset (PhysicalSourcePrime BP) => (⟨g,v⟩ : PhysicalSourcePrime BP) ∈ s)
      (physical_actual_literal_chrono_afterG_support
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i (Nat.le_of_lt hi))
    simp only [List.mem_toFinset] at hsupport
    have hmem := (physical_actual_literal_afterG_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i g v).mp (hsupport.mp hp)
    change (if v ∈
      (Green64Fock.fockToList (((H.afterG i).2 g).2)).map
        (fun a => a.1) then
      physicalLiteralFockResidue BP bigMod cap SP smallMod
        (H.afterG i) (⟨g,v⟩ : PhysicalSourcePrime BP)
      else physicalActualAnchorResidue SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H anchor i g v) =
      physicalLiteralFockResidue BP bigMod cap SP smallMod
        (H.afterG i) (⟨g,v⟩ : PhysicalSourcePrime BP)
    simp [hmem]
/-- Every chronological pendingNext label has exactly its real
next-visit physical residue, not merely the same prime support. -/
theorem physical_actual_literal_row_residue_next_of_mem
    (p : PhysicalSourcePrime BP)
    (hp : p ∈ (literalRowResiduesAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).pendingNext) :
    (literalRowResiduesAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).residueNext p =
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before (i+1)) p := by
  cases p with
  | mk g v =>
    have hsupport := congrArg
      (fun s : Finset (PhysicalSourcePrime BP) => (⟨g,v⟩ : PhysicalSourcePrime BP) ∈ s)
      (physical_actual_literal_chrono_next_support
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi)
    simp only [List.mem_toFinset] at hsupport
    have hmem := (physical_actual_literal_before_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H (i+1) g v).mp (hsupport.mp hp)
    change (if v ∈
      (Green64Fock.fockToList (((H.before (i+1)).2 g).2)).map
        (fun a => a.1) then
      physicalLiteralFockResidue BP bigMod cap SP smallMod
        (H.before (i+1)) (⟨g,v⟩ : PhysicalSourcePrime BP)
      else physicalActualAnchorResidue SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H anchor (i+1) g v) =
      physicalLiteralFockResidue BP bigMod cap SP smallMod
        (H.before (i+1)) (⟨g,v⟩ : PhysicalSourcePrime BP)
    simp [hmem]
/-- On an absent BIG prime, retain exactly the independent
uniform anchor a_p and the original cumulative signed Fourier
offset, including never-born primes. -/
theorem physical_actual_literal_row_residue_before_absent
    (p : PhysicalSourcePrime BP)
    (habs : p.2 ∉
      (Green64Fock.fockToList (((H.before i).2 p.1).2)).map
        (fun a => a.1)) :
    (literalRowResiduesAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).residueBefore p =
    (physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (bigMod p.1 p.2)) - anchor p.1 p.2 := by
  cases p with
  | mk g v =>
    change (if v ∈
      (Green64Fock.fockToList (((H.before i).2 g).2)).map
        (fun a => a.1) then
      physicalLiteralFockResidue BP bigMod cap SP smallMod
        (H.before i) (⟨g,v⟩ : PhysicalSourcePrime BP)
      else physicalActualAnchorResidue SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H anchor i g v) = _
    simp [habs, physicalActualAnchorResidue, physicalSourcePrimeValue]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowResidueLaws -/

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
variable (Vsmall : SG → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
variable (i : ℕ) (hi : i < N)

noncomputable abbrev literalRowResidueLawsAux :=
  physicalActualLiteralSourceRow SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor i hi

/-- Genuine full-source G zero-hit, birth-zero, OLD survivor and
signed-E promotion/store residue laws of the concrete literal row. -/
theorem physical_actual_literal_row_local_residue_laws :
    let row := literalRowResidueLawsAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
    (∀ j ∈ row.termIndices,
      row.residueBefore (row.pendingBefore.get j) = 0) ∧
    (∀ p ∈ row.ghostBatch, row.residueAfter p = 0) ∧
    (∀ j : row.promotionSlots,
      row.residueAfter (row.targetEndpoint.get j.val) +
        ((row.offsetAfter - row.offsetBefore : ℤ) :
          ZMod (row.value (row.targetEndpoint.get j.val))) = 0) ∧
    (∀ p ∈ row.pendingBefore, p ∉ Green64Literal.ended row →
      row.residueAfter p = row.residueBefore p) ∧
    (∀ p ∈ Green64Literal.stored row,
      row.residueNext p =
        ((row.offsetAfter - row.offsetBefore : ℤ) :
          ZMod (row.value p))) ∧
    row.offsetAfter = row.offsetBefore + row.orientation * row.k * row.divisorD ∧
    (row.orientation = 1 ∨ row.orientation = -1) := by
  dsimp only
  have hdelta :
      (literalRowResidueLawsAux SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).offsetAfter -
      (literalRowResidueLawsAux SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).offsetBefore =
      physicalActualEdgeDelta SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i := by
    change physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1) -
      physicalActualOffset SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i = _
    rw [physical_actual_offset_succ]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hmem := List.get_mem
      (literalRowResidueLawsAux SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).pendingBefore j
    rw [physical_actual_literal_row_residue_before_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
      _ hmem]
    exact physical_actual_literal_term_zero
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi) j hj
  · intro p hp
    have hm : p ∈ physicalActualLiteralChronologicalAfterG
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i := by
      rw [physical_actual_literal_chronological_ghost_operation]
      exact List.mem_append.mpr (Or.inr hp)
    rw [physical_actual_literal_row_residue_after_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi p hm]
    exact physical_actual_literal_ghost_birth_zero
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi) p hp
  · intro j
    have hp : (literalRowResidueLawsAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).targetEndpoint.get j.val ∈
      physicalActualLiteralPromotionValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
      exact (literal_indices_for_exact _ _
        j.val).mp j.2
    have hm := physical_actual_literal_promoted_in_chrono_afterG
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi hp
    have hres := physical_actual_literal_row_residue_after_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
      _ (List.mem_toFinset.mp hm)
    rw [hres, hdelta]
    exact physical_actual_literal_promotion_zero
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi _ hp
  · intro p hp hnot
    have hm : p ∈ physicalActualLiteralChronologicalAfterG
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i := by
      rw [physical_actual_literal_chronological_ghost_operation]
      apply List.mem_append.mpr
      apply Or.inl
      have hnot' : p ∉
          (physicalActualLiteralTermIndices SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H i).image
            (physicalActualLiteralPendingBefore SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig muBig k N H i).get := hnot
      exact List.mem_filter.mpr ⟨hp,
        by simpa only [decide_eq_true_eq] using hnot'⟩
    rw [physical_actual_literal_row_residue_after_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi p hm]
    rw [physical_actual_literal_row_residue_before_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi p hp]
    exact physical_actual_literal_old_pending_unchanged
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi) p hp hnot
  · intro p hp
    have hmStore : p ∈ physicalActualLiteralStoreValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H i := by
      rw [← physical_actual_literal_store_index_image]
      exact hp
    have hm : p ∈ physicalActualLiteralChronologicalNext
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i := by
      rw [physical_actual_literal_chrono_next_pending_operation]
      apply List.mem_append.mpr
      apply Or.inr
      exact (Green64Literal.pick_mem _ _ p).mpr
        (Finset.mem_image.mp hp)
    rw [physical_actual_literal_row_residue_next_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi p hm]
    rw [hdelta]
    exact physical_actual_literal_store_reset
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi p hmStore
  · change physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1) =
      physicalActualOffset SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i +
      physicalAlternatingSign i * k *
        (physicalActualLiteralDivisor SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i : ℤ)
    exact physical_actual_offset_succ SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i
  · change physicalAlternatingSign i = 1 ∨ physicalAlternatingSign i = -1
    simp only [physicalAlternatingSign]
    split_ifs <;> simp

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralFreshTargetProof -/

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
/-- Real E_i fresh slot batch has globally pairwise distinct
BIG tagged prime labels. The exact tau frame is preserved. -/
theorem physical_actual_literal_fresh_target_nodup
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralFreshTarget SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  let xs : (g : BG) → List (BP g) := fun g =>
    (orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns (H.edge i).1) g)
      (((H.edge i).2.2.1.bigChoice g).2.2.1)).toList.map
      (fun j => ((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j))
  have hn : ∀ g, (xs g).Nodup := by
    intro g
    unfold xs
    apply List.Nodup.map
      ((physical_actual_edge_target_big_slots_injective
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi g).comp
        (((H.edge i).2.2.1.tauBig g).injective))
    exact Finset.nodup_toList _
  have hh := physical_literal_sigma_flatten_nodup BP xs hn
  simpa only [physicalActualLiteralFreshTarget,
    actualLiteralCanonicalTargetSlot, xs, List.map_map,
    Function.comp_def] using hh

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralSigmaBirthSets -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]

/-- Sigma-tagged birth supports; group tags distinguish labels,
while numerical injection is separately assumed where needed. -/
noncomputable def literalPhysicalSigmaSet
    (s : (g : BG) → Finset (BP g)) :
    Finset (PhysicalSourcePrime BP) :=
  Finset.univ.filter (fun p => p.2 ∈ s p.1)

theorem literal_physical_sigma_set_mem (s : (g : BG) → Finset (BP g))
    (p : PhysicalSourcePrime BP) :
    p ∈ literalPhysicalSigmaSet BP s ↔ p.2 ∈ s p.1 := by
  simp [literalPhysicalSigmaSet]

theorem literal_physical_sigma_flatten_mem
    (xs : (g : BG) → List (BP g))
    (p : PhysicalSourcePrime BP) :
    p ∈ (Finset.univ.toList : List BG).flatMap (fun g =>
      (xs g).map (fun a => (⟨g,a⟩ : PhysicalSourcePrime BP))) ↔
    p.2 ∈ xs p.1 := by
  constructor
  · intro hp
    obtain ⟨g, _, hmap⟩ := List.mem_flatMap.mp hp
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmap
    cases heq
    exact ha
  · intro hp
    exact List.mem_flatMap.mpr ⟨p.1,
      Finset.mem_toList.mpr (Finset.mem_univ p.1),
      List.mem_map.mpr ⟨p.2, hp, rfl⟩⟩

theorem literal_physical_sigma_flatten_toFinset
    (xs : (g : BG) → List (BP g)) :
    ((Finset.univ.toList : List BG).flatMap (fun g =>
      (xs g).map (fun a => (⟨g,a⟩ : PhysicalSourcePrime BP)))).toFinset =
    literalPhysicalSigmaSet BP (fun g => (xs g).toFinset) := by
  ext p
  rw [List.mem_toFinset, literal_physical_sigma_flatten_mem,
    literal_physical_sigma_set_mem, List.mem_toFinset]

theorem literal_physical_sigma_set_subset
    (s t : (g : BG) → Finset (BP g))
    (h : ∀ g, s g ⊆ t g) :
    literalPhysicalSigmaSet BP s ⊆ literalPhysicalSigmaSet BP t := by
  intro p hp
  rw [literal_physical_sigma_set_mem] at hp ⊢
  exact h p.1 hp

theorem literal_physical_sigma_set_disjoint
    (s t : (g : BG) → Finset (BP g))
    (h : ∀ g, Disjoint (s g) (t g)) :
    Disjoint (literalPhysicalSigmaSet BP s)
      (literalPhysicalSigmaSet BP t) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rw [literal_physical_sigma_set_mem] at hp hq
  exact Finset.disjoint_left.mp (h p.1) hp hq

theorem literal_physical_sigma_set_union
    (s t : (g : BG) → Finset (BP g)) :
    literalPhysicalSigmaSet BP (fun g => s g ∪ t g) =
      literalPhysicalSigmaSet BP s ∪ literalPhysicalSigmaSet BP t := by
  ext p
  simp only [literal_physical_sigma_set_mem, Finset.mem_union]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralBirthSupport -/

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

/-- The row's freshBefore list is exactly the true source F_i
sigma-tagged first-active-birth set. -/
theorem physical_actual_literal_fresh_before_support (i : ℕ) :
    (physicalActualLiteralFreshBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    literalPhysicalSigmaSet BP
      (fun g => physicalGroupFreshVisit SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H g i) := by
  simpa only [physicalActualLiteralFreshBefore,
    Finset.toList_toFinset] using
    literal_physical_sigma_flatten_toFinset BP
      (fun g => (physicalGroupFreshVisit SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H g i).toList)
/-- The independent tau fresh target batch equals the actual
physical source E_i next-visit first-birth F_(i+1) support. -/
theorem physical_actual_literal_fresh_target_support (i : ℕ) :
    (physicalActualLiteralFreshTarget SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    literalPhysicalSigmaSet BP (fun g =>
      trueBigFreshValues (J+ell) ((H.edge i).2.2.1.bigChoice g).1
        (sourceBigShared J ell m (patterns (H.edge i).1) g)
        ((H.edge i).2.2.1.bigChoice g).2.2.1
        ((H.edge i).2.2.1.tauBig g)) := by
  let xs : (g : BG) → List (BP g) := fun g =>
    (orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns (H.edge i).1) g)
      ((H.edge i).2.2.1.bigChoice g).2.2.1).toList.map
      (fun j => ((H.edge i).2.2.1.bigChoice g).1
        ((H.edge i).2.2.1.tauBig g j))
  have ht := literal_physical_sigma_flatten_toFinset BP xs
  have hg (g : BG) :
      (xs g).toFinset =
      trueBigFreshValues (J+ell) ((H.edge i).2.2.1.bigChoice g).1
        (sourceBigShared J ell m (patterns (H.edge i).1) g)
        ((H.edge i).2.2.1.bigChoice g).2.2.1
        ((H.edge i).2.2.1.tauBig g) := by
    ext p
    simp [xs, trueBigFreshValues]
  simpa only [physicalActualLiteralFreshTarget,
    actualLiteralCanonicalTargetSlot, xs, List.map_map,
    Function.comp_def, hg] using ht
/-- The raw ordered ghost batch's support is exactly each
actual group ghost-birth set, without merging Fock residues. -/
theorem physical_actual_literal_ghost_batch_support (i : ℕ) :
    (physicalActualLiteralGhostBatch SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    literalPhysicalSigmaSet BP (fun g =>
      physicalGhostGroupBornSet SP smallMod BP bigMod
        J ell cap (H.before i) (H.ghost i) g) := by
  let xs : (g : BG) → List (BP g) := fun g =>
    (List.ofFn ((H.ghost i g).2.2)).map (fun a => a.1)
  have ht := literal_physical_sigma_flatten_toFinset BP xs
  have hg (g : BG) :
      (xs g).toFinset =
      physicalGhostGroupBornSet SP smallMod BP bigMod
        J ell cap (H.before i) (H.ghost i) g := by
    ext p
    simp [xs, physicalGhostGroupBornSet, List.mem_ofFn]
  change ((Finset.univ.toList : List BG).flatMap (fun g =>
    (List.ofFn ((H.ghost i g).2.2)).map
      (fun a => (⟨g,a.1⟩ : PhysicalSourcePrime BP)))).toFinset =
    literalPhysicalSigmaSet BP (fun g =>
      physicalGhostGroupBornSet SP smallMod BP bigMod
        J ell cap (H.before i) (H.ghost i) g)
  simpa only [xs, List.map_map, Function.comp_def, hg] using ht

/-- U_i row field is literally the physical seen-prime group
minus the current active first-birth set F_i. -/
theorem physical_actual_literal_ever_before_support (i : ℕ) :
    physicalActualLiteralEverBornBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    literalPhysicalSigmaSet BP
      (fun g => physicalGroupPastVisit SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H g i) := rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowBirthLaws -/

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

/-- Physical G_i changes OLD, not active labels; the exact E_i
input active slots still equal those at the current visit. -/
theorem physical_actual_literal_active_beforeE_eq_before
    (i : ℕ) (hi : i < N) (g : BG) :
    ((H.beforeE i).2 g).1 = ((H.before i).2 g).1 := by
  have hE := congrArg
    (fun y : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      ((y.2 g).1)) (H.E_orbit_input i hi)
  change ((H.beforeE i).2 g).1 = ((H.afterG i).2 g).1 at hE
  have hG := (physical_nonzero_ghost_witness_is_operational
    SP smallMod BP bigMod (J+ell) cap q rho N i
    Vbig muBig (H.before i) (H.afterG i) (H.ghost i)
    (H.G_nonzero i (Nat.le_of_lt hi))).1.2 g
  exact hE.trans hG.symm

/-- F_i source birthdays are truly among active sampled BIG
source slots in the original independent sigma frame. -/
theorem physical_actual_literal_fresh_before_active
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralFreshBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset ⊆
    (physicalActualLiteralCanonicalSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset := by
  intro p hp
  cases p with
  | mk g v =>
    rw [physical_actual_literal_fresh_before_support,
      literal_physical_sigma_set_mem] at hp
    have hv := physicalGroupFreshVisit_subset_active
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H (Nat.le_of_lt hi) g hp
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hv
    have hAct := physical_actual_literal_active_beforeE_eq_before
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g
    rw [← hAct] at hj
    apply List.mem_toFinset.mpr
    unfold physicalActualLiteralCanonicalSourceList
    apply List.mem_map.mpr
    refine ⟨⟨g, ((H.edge i).2.2.1.sigmaBig g).symm j⟩, by simp, ?_⟩
    simpa [actualLiteralCanonicalSourceSlot] using hj
/-- Every source F_i/G_i first birth uses a genuinely unregistered
numerical BIG prime; the groupwise global seen marker is preserved. -/
theorem physical_actual_literal_row_birth_laws
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (i : ℕ) (hi : i < N) :
    let row := physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi
    row.freshTarget.Nodup ∧
    row.freshBefore.toFinset ⊆ row.active.toFinset ∧
    Disjoint row.freshBefore.toFinset row.everBornBefore ∧
    Disjoint row.ghostBatch.toFinset
      (row.everBornBefore ∪ row.freshBefore.toFinset) ∧
    Disjoint row.freshTarget.toFinset row.everBornAfter ∧
    row.everBornAfter =
      (row.everBornBefore ∪ row.freshBefore.toFinset) ∪
      row.ghostBatch.toFinset := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact physical_actual_literal_fresh_target_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi
  · exact physical_actual_literal_fresh_before_active
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi
  · have h := literal_physical_sigma_set_disjoint BP
        (fun g => physicalGroupFreshVisit SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H g i)
        (fun g => physicalGroupPastVisit SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H g i)
        (fun g => physicalGroupFreshPast_disjoint
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N i H g)
    change Disjoint
      (physicalActualLiteralFreshBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).toFinset
      (physicalActualLiteralEverBornBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
    rw [physical_actual_literal_fresh_before_support,
      physical_actual_literal_ever_before_support]
    exact h
  · have h := literal_physical_sigma_set_disjoint BP
        (fun g => physicalGhostGroupBornSet
          SP smallMod BP bigMod J ell cap
            (H.before i) (H.ghost i) g)
        (fun g => physicalGroupPastVisit SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H g i ∪
          physicalGroupFreshVisit SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H g i)
        (fun g => physicalGroupGhost_disjoint_past_fresh
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N i H hnum hi g)
    change Disjoint
      (physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).toFinset
      (physicalActualLiteralEverBornBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ∪
       (physicalActualLiteralFreshBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).toFinset)
    rw [physical_actual_literal_ghost_batch_support,
      physical_actual_literal_ever_before_support,
      physical_actual_literal_fresh_before_support,
      ← literal_physical_sigma_set_union]
    exact h
  · apply Finset.disjoint_left.mpr
    intro p hpFresh hpBorn
    cases p with
    | mk g v =>
      have hFresh :
          v ∈ physicalGroupFreshVisit SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H g (i+1) := by
        change (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
          (physicalActualLiteralFreshTarget SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H i).toFinset at hpFresh
        rw [physical_actual_literal_fresh_target_support,
          literal_physical_sigma_set_mem] at hpFresh
        simpa only [physicalGroupFreshVisit, if_pos hi]
          using hpFresh
      have hBorn :
          v ∈ physicalGroupPastVisit SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H g (i+1) := by
        change (⟨g,v⟩ : PhysicalSourcePrime BP) ∈
          (physicalActualLiteralEverBornBefore SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H i ∪
           (physicalActualLiteralFreshBefore SP smallMod BP bigMod
             J ell m cap patterns q rho Vbig muBig k N H i).toFinset) ∪
           (physicalActualLiteralGhostBatch SP smallMod BP bigMod
             J ell m cap patterns q rho Vbig muBig k N H i).toFinset at hpBorn
        rw [physical_actual_literal_ever_before_support,
          physical_actual_literal_fresh_before_support,
          physical_actual_literal_ghost_batch_support,
          ← literal_physical_sigma_set_union,
          ← literal_physical_sigma_set_union,
          literal_physical_sigma_set_mem] at hpBorn
        have hPast := physicalGroupPastVisit_succ
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N i H hnum hi g
        exact hPast.symm ▸ hpBorn
      exact Finset.disjoint_left.mp
        (physicalGroupFreshPast_disjoint
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N (i+1) H g)
        hFresh hBorn
  · rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowLegal -/

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
variable (Vsmall : SG → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
variable (i : ℕ) (hi : i < N)

noncomputable abbrev literalRowLegalAux :=
  physicalActualLiteralSourceRow SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor i hi

/-- The independently sampled free C_g factors are absent from
BOTH real active endpoints. Auxiliary repeats are allowed. -/
theorem physical_actual_literal_row_auxiliary_ban :
    ∀ p ∈ (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).auxiliaryPrimes,
    p ∉ (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).active ∧
    p ∉ (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).nextActive := by
  intro p hp
  change p ∈ physicalActualLiteralAuxiliaryPrimes SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i at hp
  unfold physicalActualLiteralAuxiliaryPrimes at hp
  obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, _, hvalue⟩ := List.mem_map.mp hg
  have heq : p = (⟨g,(H.edge i).2.1 g j⟩ : PhysicalSourcePrime BP) :=
    hvalue.symm
  subst p
  have haux := (H.E_legal i hi).2.2.1
  constructor
  · intro hmem
    change (⟨g,(H.edge i).2.1 g j⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralCanonicalSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i at hmem
    unfold physicalActualLiteralCanonicalSourceList at hmem
    obtain ⟨⟨gg,t⟩,_,ht⟩ := List.mem_map.mp hmem
    change (⟨gg, ((H.beforeE i).2 gg).1
      (((H.edge i).2.2.1.sigmaBig gg) t)⟩ : PhysicalSourcePrime BP) =
      ⟨g, (H.edge i).2.1 g j⟩ at ht
    have hg : gg = g := congrArg Sigma.fst ht
    subst gg
    have hv : ((H.beforeE i).2 g).1
      (((H.edge i).2.2.1.sigmaBig g) t) = (H.edge i).2.1 g j :=
      eq_of_heq (Sigma.mk.inj_iff.mp ht).2
    exact (haux g j (((H.edge i).2.2.1.sigmaBig g) t)).1 hv.symm
  · intro hmem
    change (⟨g,(H.edge i).2.1 g j⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralCanonicalTargetList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i at hmem
    unfold physicalActualLiteralCanonicalTargetList at hmem
    obtain ⟨⟨gg,t⟩,_,ht⟩ := List.mem_map.mp hmem
    change (⟨gg, ((H.edge i).2.2.1.bigChoice gg).1
      (((H.edge i).2.2.1.tauBig gg) t)⟩ : PhysicalSourcePrime BP) =
      ⟨g, (H.edge i).2.1 g j⟩ at ht
    have hg : gg = g := congrArg Sigma.fst ht
    subst gg
    have hv : ((H.edge i).2.2.1.bigChoice g).1
      (((H.edge i).2.2.1.tauBig g) t) = (H.edge i).2.1 g j :=
      eq_of_heq (Sigma.mk.inj_iff.mp ht).2
    exact (haux g j (((H.edge i).2.2.1.tauBig g) t)).2 hv.symm
/-- Corrected OrientedBigEdgeLegal gives literal store and
OLD-promotion bans for TRUE D, not its fictitious unpermuted
predecessor. -/
theorem physical_actual_literal_row_divisibility_bans :
    (∀ p ∈ Green64Literal.stored
        (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi),
      ¬ (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).value p ∣
        (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).divisorD) ∧
    (∀ p ∈ Green64Literal.promoted
        (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi),
      ¬ (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).value p ∣
        (literalRowLegalAux SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi).divisorD) := by
  constructor
  · intro p hp
    have hp' : p ∈ physicalActualLiteralStoreValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i := by
      change p ∈ (physicalActualLiteralStoreIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawSourceList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get at hp
      rw [physical_actual_literal_store_index_image] at hp
      exact hp
    obtain ⟨⟨g,j⟩,hj,heq⟩ := Finset.mem_image.mp hp'
    have hbig := (H.E_legal i hi).2.2.2.1 g
    have hstore := hbig.stored_not_dividing j (Finset.mem_filter.mp hj).2
    change ¬ physicalSourcePrimeValue BP bigMod p ∣
      physicalActualLiteralDivisor SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i
    rw [← heq]
    exact hstore
  · intro p hp
    have hp' : p ∈ physicalActualLiteralPromotionValues SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i := by
      change p ∈ (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawTargetList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get at hp
      rw [physical_actual_literal_promotion_index_image] at hp
      exact hp
    obtain ⟨⟨g,j⟩,hj,heq⟩ := Finset.mem_image.mp hp'
    have hbig := (H.E_legal i hi).2.2.2.1 g
    let jj : ↥(((H.edge i).2.2.1.bigChoice g).2.2.1) :=
      ⟨j,(Finset.mem_filter.mp hj).2⟩
    have hnot := hbig.promoted_not_dividing jj
    have hmatch := hbig.promoted_matches jj
    change ¬ physicalSourcePrimeValue BP bigMod p ∣
      physicalActualLiteralDivisor SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i
    rw [← heq]
    change ¬ bigMod g
      (((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j)) ∣ _
    rw [hmatch]
    exact hnot

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowSharedCongruence -/

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
variable (Vsmall : SG → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
variable (i : ℕ) (hi : i < N)

/-- For actual shared BIG source coordinates, true oriented D
kills the physical edge displacement modulo p, hence the
exact literal offset is preserved in ZMod(p). -/
theorem physical_actual_literal_row_shared_congruence :
    let f := physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi
    ∀ p ∈ Green64Literal.shared f,
      (f.offsetBefore : ZMod (f.value p)) =
        (f.offsetAfter : ZMod (f.value p)) := by
  dsimp only
  intro p hp
  change p ∈
    (physicalActualLiteralSharedIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).image
        (physicalActualLiteralRawSourceList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get at hp
  rw [physical_actual_literal_shared_index_image] at hp
  obtain ⟨⟨g,j⟩,hj,heq⟩ := Finset.mem_image.mp hp
  have hjShared : j ∈ sourceBigShared J ell m
    (patterns (H.edge i).1) g := (Finset.mem_filter.mp hj).2
  have hz := oriented_big_shared_displacement_zero
    SP smallMod BP bigMod J ell m cap
    (patterns (H.edge i).1) (H.edge i).2.1 (H.beforeE i)
    (H.edge i).2.2.1.sigmaBig (H.edge i).2.2.2.1
    (physicalAlternatingSign i) k g j hjShared
  have hOffset := physical_actual_offset_succ
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i
  change
    (physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (physicalSourcePrimeValue BP bigMod p)) =
    (physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1) :
        ZMod (physicalSourcePrimeValue BP bigMod p))
  rw [hOffset]
  subst p
  have hz' :
      (physicalActualEdgeDelta SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (physicalSourcePrimeValue BP bigMod
          (actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H i g j))) = 0 := hz
  push_cast
  rw [hz']
  simp

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralProductArithmetic -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- The product of values of a finset represented as a list is
the original finset product, with no assumption of distinct values. -/
theorem literal_nat_prod_toList_map
    {A : Type} [DecidableEq A] (s : Finset A) (f : A → ℕ) :
    (s.toList.map f).prod = ∏ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.prod_insert ha, ih]

/-- Finite products distribute over an actual groupwise flatMap. -/
theorem literal_nat_prod_flatMap
    {A : Type} (xs : List A) (f : A → List ℕ) :
    (xs.flatMap f).prod = (xs.map fun a => (f a).prod).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.prod_append, ih]

/-- A genuine dependent product over all source group-pattern
slots is the product over their Sigma-tagged global indices. -/
theorem literal_nat_sigma_pattern_product
    {G : Type} [Fintype G] [DecidableEq G]
    (M : ℕ) (pattern : G → Finset (Fin M))
    (f : (g : G) → Fin M → ℕ) :
    (((Finset.univ : Finset (Σ _ : G, Fin M)).filter
      (fun a => a.2 ∈ pattern a.1)).toList.map
      (fun a => f a.1 a.2)).prod =
      ∏ g : G, ∏ j ∈ pattern g, f g j := by
  rw [literal_nat_prod_toList_map]
  have hs :
      (Finset.univ : Finset (Σ _ : G, Fin M)).filter
        (fun a => a.2 ∈ pattern a.1) =
      (Finset.univ : Finset G).sigma pattern := by
    ext ⟨g,j⟩
    simp
  rw [hs]
  exact Finset.prod_sigma (Finset.univ : Finset G) pattern
    (fun a : Σ _ : G, Fin M => f a.1 a.2)

/-- The actual independent groupwise chronological list product
of numerical labels is the dependent source group product. -/
theorem literal_nat_group_flatMap_product
    {G : Type} [Fintype G] [DecidableEq G]
    (values : G → List ℕ) :
    ((Finset.univ.toList : List G).flatMap values).prod =
      ∏ g : G, (values g).prod := by
  rw [literal_nat_prod_flatMap]
  exact literal_nat_prod_toList_map (Finset.univ : Finset G)
    (fun g => (values g).prod)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowDivisor -/

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

/-- Original SMALL Haar shared-prime factors, with independent
sigmaSmall as actually sampled in the true oriented E. -/
theorem physical_actual_literal_small_shared_product (i : ℕ) :
    (physicalActualLiteralSmallSharedPrimes SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).prod =
    ∏ g : SG, ∏ j ∈ sourceSmallShared J ell g,
      smallMod g (Green64SmallHaar.marks (smallMod g) (J+ell)
        ((H.beforeE i).1 g) ((H.edge i).2.2.2.1 g j)) := by
  unfold physicalActualLiteralSmallSharedPrimes
  rw [literal_nat_group_flatMap_product]
  apply Finset.prod_congr rfl
  intro g hg
  exact literal_nat_prod_toList_map _ _
/-- All original BIG auxiliary draws are multiplied even when
the same numerical prime occurs in distinct C_g slots. -/
theorem physical_actual_literal_auxiliary_product (i : ℕ) :
    ((physicalActualLiteralAuxiliaryPrimes SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).map
        (physicalSourcePrimeValue BP bigMod)).prod =
    ∏ g : BG, ∏ j : ↥((patterns (H.edge i).1).free g),
      bigMod g ((H.edge i).2.1 g j) := by
  unfold physicalActualLiteralAuxiliaryPrimes
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    physicalSourcePrimeValue]
  rw [literal_nat_group_flatMap_product]
  apply Finset.prod_congr rfl
  intro g hg
  exact literal_nat_prod_toList_map _ _

/-- The selected raw SOURCE shared indices give exactly the
product over original canonical shared pattern slots, not an
unpermuted old surrogate D. -/
theorem physical_actual_literal_shared_product
    (i : ℕ) (hi : i < N) :
    ((Green64Literal.pick
      (physicalActualLiteralRawSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralSharedIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)).map
        (physicalSourcePrimeValue BP bigMod)).prod =
    ∏ g : BG, ∏ j ∈ sourceBigShared J ell m
        (patterns (H.edge i).1) g,
      bigMod g (((H.beforeE i).2 g).1
        ((H.edge i).2.2.1.sigmaBig g j)) := by
  let xs := physicalActualLiteralRawSourceList SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  let S := physicalActualLiteralSharedIndices SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  have h0 :
      ((Green64Literal.pick xs S).map
        (physicalSourcePrimeValue BP bigMod)).prod =
      ∏ j ∈ S, physicalSourcePrimeValue BP bigMod (xs.get j) := by
    simp only [Green64Literal.pick, List.map_map, Function.comp_def]
    exact literal_nat_prod_toList_map S _
  have inj : Set.InjOn xs.get (S : Set (Fin xs.length)) := by
    intro x hx y hy heq
    exact (List.nodup_iff_injective_get.mp
      (physical_actual_literal_raw_source_nodup
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi)) heq
  have h1 :
      (∏ j ∈ S, physicalSourcePrimeValue BP bigMod (xs.get j)) =
      ∏ p ∈ physicalActualLiteralSharedPatternValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H i,
          physicalSourcePrimeValue BP bigMod p := by
    rw [← physical_actual_literal_shared_index_image]
    exact (Finset.prod_image (f := physicalSourcePrimeValue BP bigMod)
      (s := S) (g := xs.get) inj).symm
  rw [h0, h1]
  unfold physicalActualLiteralSharedPatternValues
  have hinj := physical_actual_literal_source_slot_injective
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  rw [Finset.prod_image (f := physicalSourcePrimeValue BP bigMod)
    (g := fun a : Σ _ : BG, Fin (J+ell) =>
      actualLiteralCanonicalSourceSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2)
    (fun a ha b hb heq => hinj heq)]
  have hs :
      (Finset.univ : Finset (Σ _ : BG, Fin (J+ell))).filter
        (fun a => a.2 ∈ sourceBigShared J ell m
          (patterns (H.edge i).1) a.1) =
      (Finset.univ : Finset BG).sigma
        (sourceBigShared J ell m (patterns (H.edge i).1)) := by
    ext ⟨g,j⟩
    simp
  rw [hs, Finset.prod_sigma]
  simp [actualLiteralCanonicalSourceSlot, physicalSourcePrimeValue]
/-- Exact RowValid.divisor_from_groups for the fully oriented
original D, SMALL+BIG+auxiliary products with no made-up
small auxiliary factors and no loss of independent permutations. -/
theorem physical_actual_literal_row_divisor_from_groups
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (hi : i < N) :
    let row := physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi
    row.divisorD =
      (row.smallSharedPrimes.prod * row.smallAuxiliaryPrimes.prod) *
      ((Green64Literal.pick row.sourceEndpoint row.sharedIndices).map
        row.value).prod *
      (row.auxiliaryPrimes.map row.value).prod := by
  dsimp only
  change
    physicalActualLiteralDivisor SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    ((physicalActualLiteralSmallSharedPrimes SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).prod * ([] : List ℕ).prod) *
    ((Green64Literal.pick
      (physicalActualLiteralRawSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralSharedIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)).map
        (physicalSourcePrimeValue BP bigMod)).prod *
    ((physicalActualLiteralAuxiliaryPrimes SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).map
        (physicalSourcePrimeValue BP bigMod)).prod
  rw [physical_actual_literal_small_shared_product,
    physical_actual_literal_shared_product
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi,
    physical_actual_literal_auxiliary_product]
  unfold physicalActualLiteralDivisor sourceOrientedPhysicalD
  rw [Finset.prod_mul_distrib]
  simp only [List.prod_nil, mul_one]
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralPartitionArithmetic -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

theorem literal_three_finset_toList_perm
    {A : Type} [DecidableEq A]
    (S R F : Finset A)
    (hSR : Disjoint S R) (hSF : Disjoint S F) (hRF : Disjoint R F) :
    (S ∪ R ∪ F).toList.Perm (S.toList ++ R.toList ++ F.toList) := by
  have hSRl : S.toList.Disjoint R.toList := by
    apply List.disjoint_left.mpr
    intro a ha hb
    exact Finset.disjoint_left.mp hSR
      (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb)
  have hSFl : S.toList.Disjoint F.toList := by
    apply List.disjoint_left.mpr
    intro a ha hb
    exact Finset.disjoint_left.mp hSF
      (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb)
  have hRFl : R.toList.Disjoint F.toList := by
    apply List.disjoint_left.mpr
    intro a ha hb
    exact Finset.disjoint_left.mp hRF
      (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb)
  have hSRFl : (S.toList ++ R.toList).Disjoint F.toList := by
    apply List.disjoint_left.mpr
    intro a ha hb
    rcases List.mem_append.mp ha with ha | ha
    · exact List.disjoint_left.mp hSFl ha hb
    · exact List.disjoint_left.mp hRFl ha hb
  have hn : (S.toList ++ R.toList ++ F.toList).Nodup :=
    List.Nodup.append
      (List.Nodup.append (Finset.nodup_toList S)
        (Finset.nodup_toList R) hSRl)
      (Finset.nodup_toList F) hSRFl
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hn).mpr
  intro a
  simp only [Finset.mem_toList, Finset.mem_union, List.mem_append]

theorem literal_finset_image_list_nodup
    {A P : Type} [DecidableEq A]
    (S : Finset A) (f : A → P) (hf : Function.Injective f) :
    (S.toList.map f).Nodup := by
  exact List.Nodup.map hf (Finset.nodup_toList _)

theorem literal_finset_image_perm_list
    {A P : Type} [DecidableEq A] [DecidableEq P]
    (S : Finset A) (f : A → P) (hf : Function.Injective f)
    (ys : List P) (hn : ys.Nodup)
    (hs : ys.toFinset = S.image f) :
    (S.toList.map f).Perm ys := by
  apply (List.perm_ext_iff_of_nodup
    (literal_finset_image_list_nodup S f hf) hn).mpr
  intro p
  simp only [List.mem_map, Finset.mem_toList]
  rw [← List.mem_toFinset, hs]
  simp only [Finset.mem_image]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralTargetIndices -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (M : ℕ)
variable (shared promote : BG → Finset (Fin M))

noncomputable def literalTargetAllIndices : Finset (Σ _ : BG, Fin M) :=
  Finset.univ
noncomputable def literalTargetCommon : Finset (Σ _ : BG, Fin M) :=
  (literalTargetAllIndices M).filter (fun a => a.2 ∈ shared a.1)
noncomputable def literalTargetPromoted : Finset (Σ _ : BG, Fin M) :=
  (literalTargetAllIndices M).filter (fun a => a.2 ∈ promote a.1)
noncomputable def literalTargetFresh : Finset (Σ _ : BG, Fin M) :=
  (literalTargetAllIndices M).filter (fun a =>
    a.2 ∈ orientedFresh M (shared a.1) (promote a.1))

/-- Every independent tau target coordinate is either canonical
shared, literalTargetPromoted OLD, or a new birth; original pattern classes
are disjoint because promotions are only on unshared indices. -/
theorem literal_oriented_sigma_target_partition
    (h : ∀ g, Disjoint (shared g) (promote g)) :
    literalTargetAllIndices M =
      literalTargetCommon M shared ∪ literalTargetPromoted M promote ∪ literalTargetFresh M shared promote ∧
    Disjoint (literalTargetCommon M shared) (literalTargetPromoted M promote) ∧
    Disjoint (literalTargetCommon M shared) (literalTargetFresh M shared promote) ∧
    Disjoint (literalTargetPromoted M promote) (literalTargetFresh M shared promote) := by
  have hCover : literalTargetAllIndices M =
      literalTargetCommon M shared ∪ literalTargetPromoted M promote ∪ literalTargetFresh M shared promote := by
    ext ⟨g,j⟩
    by_cases hs : j ∈ shared g
    · simp [literalTargetAllIndices, literalTargetCommon, literalTargetPromoted, literalTargetFresh, hs,
          orientedFresh, orientedUnshared]
    · by_cases hp : j ∈ promote g
      · simp [literalTargetAllIndices, literalTargetCommon, literalTargetPromoted, literalTargetFresh, hs, hp,
            orientedFresh, orientedUnshared]
      · simp [literalTargetAllIndices, literalTargetCommon, literalTargetPromoted, literalTargetFresh, hs, hp,
            orientedFresh, orientedUnshared]
  refine ⟨hCover, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro ⟨g,j⟩ hs hp
    exact Finset.disjoint_left.mp (h g)
      (by simpa [literalTargetCommon, literalTargetAllIndices] using hs)
      (by simpa [literalTargetPromoted, literalTargetAllIndices] using hp)
  · apply Finset.disjoint_left.mpr
    intro ⟨g,j⟩ hs hf
    have hj : j ∈ shared g := by simpa [literalTargetCommon, literalTargetAllIndices] using hs
    have hn : j ∉ shared g := by
      exact (by simpa [literalTargetFresh, literalTargetAllIndices, orientedFresh, orientedUnshared] using hf : j ∉ shared g ∧ j ∉ promote g).1
    exact hn hj
  · apply Finset.disjoint_left.mpr
    intro ⟨g,j⟩ hp hf
    have hj : j ∈ promote g := by simpa [literalTargetPromoted, literalTargetAllIndices] using hp
    have hn : j ∉ promote g := by
      exact (by simpa [literalTargetFresh, literalTargetAllIndices, orientedFresh, orientedUnshared] using hf : j ∉ shared g ∧ j ∉ promote g).2
    exact hn hj
end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralTargetPartition -/

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

noncomputable def literalPhysicalSharedPattern (i : ℕ) : BG → Finset (Fin (J+ell)) :=
  sourceBigShared J ell m (patterns (H.edge i).1)
noncomputable def literalPhysicalPromotionPattern (i : ℕ) (g : BG) :
    Finset (Fin (J+ell)) :=
  ((H.edge i).2.2.1.bigChoice g).2.2.1

/-- Original physical E legality ensures that OLD promotion slots
are outside the shared canonical target pattern. -/
theorem physical_literal_target_pattern_disjoint
    (i : ℕ) (hi : i < N) (g : BG) :
    Disjoint (literalPhysicalSharedPattern SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i g)
      (literalPhysicalPromotionPattern SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i g) := by
  apply Finset.disjoint_left.mpr
  intro j hs hp
  have hleg := (H.E_legal i hi).2.2.2.1 g
  have hnot : j ∉ sourceBigShared J ell m (patterns (H.edge i).1) g := by
    simpa [orientedUnshared] using hleg.promotes_unshared hp
  exact hnot hs

/-- Exact target-label list permutation induced by partitioning
the original independent tau pattern into shared, OLD, fresh slots. -/
theorem physical_actual_literal_target_partition_perm
    (i : ℕ) (hi : i < N) :
    let sh := literalPhysicalSharedPattern SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i
    let pr := literalPhysicalPromotionPattern SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i
    let t : (Σ _ : BG, Fin (J+ell)) → PhysicalSourcePrime BP :=
      fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2
    (physicalActualLiteralCanonicalTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Perm
      ((literalTargetCommon (J+ell) sh).toList.map t ++
       (literalTargetPromoted (J+ell) pr).toList.map t ++
       (literalTargetFresh (J+ell) sh pr).toList.map t) := by
  dsimp only
  let sh := literalPhysicalSharedPattern SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  let pr := literalPhysicalPromotionPattern SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  let t : (Σ _ : BG, Fin (J+ell)) → PhysicalSourcePrime BP :=
    fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2
  obtain ⟨hcover,hsr,hsf,hrf⟩ :=
    literal_oriented_sigma_target_partition (J+ell) sh pr
      (physical_literal_target_pattern_disjoint
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i hi)
  have hp := literal_three_finset_toList_perm
    (literalTargetCommon (J+ell) sh)
    (literalTargetPromoted (J+ell) pr)
    (literalTargetFresh (J+ell) sh pr)
    hsr hsf hrf
  rw [← hcover] at hp
  have hm := hp.map t
  simpa only [literalTargetAllIndices,
    physicalActualLiteralCanonicalTargetList,
    sh,pr,t, List.map_append] using hm

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralTargetImageSupport -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]

/-- The actual group-tagged target images of independent tau
indices agree with the groupwise Finset source images. -/
theorem literal_sigma_index_image_support
    (M : ℕ) (s : BG → Finset (Fin M))
    (target : (g : BG) → Fin M → BP g) :
    ((Finset.univ : Finset (Σ _ : BG, Fin M)).filter
      (fun a => a.2 ∈ s a.1)).image
      (fun a => (⟨a.1,target a.1 a.2⟩ : PhysicalSourcePrime BP)) =
    literalPhysicalSigmaSet BP
      (fun g => (s g).image (target g)) := by
  ext ⟨g,v⟩
  rw [literal_physical_sigma_set_mem]
  constructor
  · intro hp
    obtain ⟨⟨gg,j⟩,hj,heq⟩ := Finset.mem_image.mp hp
    have hg : gg = g := congrArg Sigma.fst heq
    subst gg
    have hv : target g j = v :=
      eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    exact Finset.mem_image.mpr
      ⟨j,(Finset.mem_filter.mp hj).2,hv⟩
  · intro hp
    obtain ⟨j,hj,hv⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr
      ⟨⟨g,j⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,
        by simp only [hv]⟩
end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralTargetParts -/

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

/-- The physical SOURCE shared-index pick and the canonical
TARGET shared-partition sublist have identical labelled supports,
by corrected source/target shared-copy under independent sigma/tau. -/
theorem physical_actual_literal_target_shared_part
    (i : ℕ) (hi : i < N) :
    ((Green64Literal.pick
      (physicalActualLiteralRawSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralSharedIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i))).toFinset =
    (literalTargetCommon (J+ell)
      (literalPhysicalSharedPattern SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)).image
      (fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2) := by
  rw [Green64Literal.pick_toFinset,
    physical_actual_literal_shared_index_image,
    physical_actual_literal_shared_target_image
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi]
  rfl

/-- Independent target tau PROMOTION slot pick is exactly the
OLD-labelled canonical target promotion support. -/
theorem physical_actual_literal_target_promoted_part
    (i : ℕ) :
    ((Green64Literal.pick
      (physicalActualLiteralRawTargetList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i))).toFinset =
    (literalTargetPromoted (J+ell)
      (literalPhysicalPromotionPattern SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)).image
      (fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2) := by
  rw [Green64Literal.pick_toFinset,
    physical_actual_literal_promotion_index_image]
  rfl

/-- Physical independently sampled tau fresh-target batch has the
same exact labelled support as the canonical fresh index sublist. -/
theorem physical_actual_literal_target_fresh_part
    (i : ℕ) :
    (physicalActualLiteralFreshTarget SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    (literalTargetFresh (J+ell)
      (literalPhysicalSharedPattern SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (literalPhysicalPromotionPattern SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)).image
      (fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2) := by
  rw [physical_actual_literal_fresh_target_support]
  unfold literalTargetFresh literalPhysicalSharedPattern
    literalPhysicalPromotionPattern literalTargetAllIndices
    actualLiteralCanonicalTargetSlot trueBigFreshValues
  rw [← literal_sigma_index_image_support BP (J+ell)]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowTargetOperation -/

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

/-- Each original indexed shared pick is a genuinely nodup
sublists of physical SOURCE endpoints, not the canonical
target coordinate enumeration. -/
theorem physical_actual_literal_shared_pick_nodup
    (i : ℕ) (hi : i < N) :
    (Green64Literal.pick
      (physicalActualLiteralRawSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralSharedIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)).Nodup := by
  unfold Green64Literal.pick
  apply List.Nodup.map
    (List.nodup_iff_injective_get.mp
      (physical_actual_literal_raw_source_nodup SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i hi))
  exact Finset.nodup_toList _

theorem physical_actual_literal_promoted_pick_nodup
    (i : ℕ) (hi : i < N) :
    (Green64Literal.pick
      (physicalActualLiteralRawTargetList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)).Nodup := by
  unfold Green64Literal.pick
  apply List.Nodup.map
    (List.nodup_iff_injective_get.mp
      (physical_actual_literal_raw_target_nodup SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i hi))
  exact Finset.nodup_toList _

/-- Full physical source E target-list permutation: the shared
source OLD pick, target OLD promotion pick and independent fresh
tau batch reproduce the original ordered canonical target up
to a real permutation. No set equality substituted for Perm. -/
theorem physical_actual_literal_target_operation
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralCanonicalTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Perm
      (Green64Literal.pick
        (physicalActualLiteralRawSourceList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i)
        (physicalActualLiteralSharedIndices SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i) ++
       Green64Literal.pick
        (physicalActualLiteralRawTargetList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i)
        (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i) ++
       physicalActualLiteralFreshTarget SP smallMod BP bigMod
         J ell m cap patterns q rho Vbig muBig k N H i) := by
  let sh := literalPhysicalSharedPattern SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  let pr := literalPhysicalPromotionPattern SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  let t : (Σ _ : BG, Fin (J+ell)) → PhysicalSourcePrime BP :=
    fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2
  have ht : Function.Injective t :=
    physical_actual_literal_target_slot_injective
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi
  have hS := literal_finset_image_perm_list
    (literalTargetCommon (J+ell) sh) t ht
    (Green64Literal.pick
      (physicalActualLiteralRawSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralSharedIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i))
    (physical_actual_literal_shared_pick_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
    (physical_actual_literal_target_shared_part
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
  have hR := literal_finset_image_perm_list
    (literalTargetPromoted (J+ell) pr) t ht
    (Green64Literal.pick
      (physicalActualLiteralRawTargetList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i))
    (physical_actual_literal_promoted_pick_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
    (physical_actual_literal_target_promoted_part
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i)
  have hF := literal_finset_image_perm_list
    (literalTargetFresh (J+ell) sh pr) t ht
    (physicalActualLiteralFreshTarget SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (physical_actual_literal_fresh_target_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
    (physical_actual_literal_target_fresh_part
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i)
  have hp := physical_actual_literal_target_partition_perm
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  exact hp.trans (by simpa only [List.append_assoc] using
    (hS.append (hR.append hF)))

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowSurviving -/

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

/-- A source OLD prime surviving the original target promotion
has its *actual* next Fock residue shifted by the physical E step. -/
theorem physical_actual_literal_surviving_fock_translation
    (i : ℕ) (hi : i < N) (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (hnot : p ∉ physicalActualLiteralPromotionValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before (i+1)) p =
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.afterG i) p +
    (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (physicalSourcePrimeValue BP bigMod p)) := by
  rcases p with ⟨g,v⟩
  have hmem := (physical_actual_literal_afterG_group_mem
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i g v).mp hp
  obtain ⟨a, ha, hav⟩ := List.mem_map.mp hmem
  subst v
  let x := (H.beforeE i).2 g
  let c := ((H.edge i).2.2.1.bigChoice g).2
  have haG : a ∈ Green64Fock.fockMultiset (((H.afterG i).2 g).2) := by
    simpa [Green64Fock.fockMultiset, Green64Fock.fockToList] using ha
  have haE : a ∈ Green64Fock.fockMultiset (x.2) := by
    exact (physical_actual_GE_orbit_preserves_atoms
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hi g a).mpr (by simpa [x] using haG)

  have haList : a ∈ List.ofFn x.2.2 := by
    simpa [x, Green64Fock.fockMultiset, Green64Fock.fockToList] using haE
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp haList
  have hjNot : j ∉ selectedOld (bigMod g) (J+ell) (cap g) x c := by
    intro hSel
    have hProm : a.1 ∈ trueBigPromotedValues
        (bigMod g) (J+ell) (cap g) x c := by
      rw [← selectedOld_values_eq_promoted]
      exact Finset.mem_image.mpr ⟨j, hSel, by rw [hj]⟩
    exact hnot ((physical_actual_literal_promotion_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g a.1).mpr
      (by simpa [x,c] using hProm))
  have hjSurv : j ∈ survivorIndices (bigMod g) (J+ell) (cap g) x c :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjNot⟩
  have hTranslated := physical_actual_literal_survivor_residue_translation
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g j
    (by simpa [x, c] using hjSurv)
  have haNext :
      (⟨a.1, a.2 + (physicalActualEdgeDelta SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :
          ZMod (bigMod g a.1))⟩ :
        Green64Fock.Atom (BP g) (bigMod g)) ∈
      Green64Fock.fockMultiset (((H.before (i+1)).2 g).2) := by
    change Green64PhysicalEdge.translateAtom
      (physicalActualEdgeDelta SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i)
      (x.2.2 j) ∈ _ at hTranslated
    rw [hj] at hTranslated
    simpa only [Green64PhysicalEdge.translateAtom] using hTranslated

  have hnNext := physical_actual_literal_before_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H (i+1) (Nat.succ_le_of_lt hi) g
  have hnG := physical_actual_literal_afterG_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi) g
  have hNext := physical_literal_fock_residue_of_atom
    BP bigMod cap SP smallMod (H.before (i+1))
    (⟨g,a.1⟩ : PhysicalSourcePrime BP) hnNext
    (a.2 + (physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
        ZMod (bigMod g a.1))) haNext
  have hG := physical_literal_fock_residue_of_atom
    BP bigMod cap SP smallMod (H.afterG i)
    (⟨g,a.1⟩ : PhysicalSourcePrime BP) hnG a.2 haG
  rw [hNext, hG]
  rfl

/-- The exact surviving_translation field of the original RowValid,
with its literal after/next residue readouts and physical signed offset. -/
theorem physical_actual_literal_row_surviving_translation
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (hi : i < N) :
    let row := physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi
    ∀ p ∈ row.pendingAfter.toFinset \ Green64Literal.promoted row,
      row.residueNext p = row.residueAfter p +
        ((row.offsetAfter - row.offsetBefore : ℤ) :
          ZMod (row.value p)) := by
  dsimp only
  intro p hp
  have hpA : p ∈ (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).pendingAfter :=
    List.mem_toFinset.mp (Finset.mem_sdiff.mp hp).1
  have hn : p ∉ physicalActualLiteralPromotionValues
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i := by
    have hn' := (Finset.mem_sdiff.mp hp).2
    change p ∉ (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).image
      (physicalActualLiteralRawTargetList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).get at hn'
    rwa [physical_actual_literal_promotion_index_image] at hn'

  have hpG : p ∈ physicalActualLiteralPendingAfterG SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i := by
    have hsupport := congrArg (fun s : Finset (PhysicalSourcePrime BP) => p ∈ s)
      (physical_actual_literal_chrono_afterG_support
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i (Nat.le_of_lt hi))
    exact List.mem_toFinset.mp
      (hsupport.mp (List.mem_toFinset.mpr hpA))
  have hpN : p ∈ (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).pendingNext := by
    change p ∈ physicalActualLiteralChronologicalNext
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i
    unfold physicalActualLiteralChronologicalNext
    exact List.mem_append.mpr (Or.inl
      (List.mem_filter.mpr ⟨hpA, by simpa only [decide_eq_true_eq] using hn⟩))
  rw [physical_actual_literal_row_residue_next_of_mem
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi p hpN]
  rw [physical_actual_literal_row_residue_after_of_mem
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi p hpA]

  have hD : (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).offsetAfter -
    (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).offsetBefore =
    physicalActualEdgeDelta SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
    change physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1) -
      physicalActualOffset SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i = _
    rw [physical_actual_offset_succ]
    omega
  rw [hD]
  exact physical_actual_literal_surviving_fock_translation
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi p hpG hn

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralRowValid -/

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

/-- The complete *original* source RowValid, instantiated at the
genuine physical witness row. The only extra assumptions say that
all original numerical BIG labels are prime and globally distinct. -/
theorem physical_actual_literal_source_row_valid
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    Green64Literal.RowValid (physicalActualLiteralSourceRow
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi) := by
  have ⟨hPrime, hInject⟩ := physical_actual_literal_row_prime_fields
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    i hi hprime hnum
  obtain ⟨hSOrder, hTOrder, hSGroups, hTGroups, hGhostOrder,
      hGhostLabels, hSharedCopy, hSharedSource, hSharedTarget,
      hSPerm, hTPerm, hSNodup, hTNodup, hActiveNodup,
      hPendingNodup, hAfterNodup, hNextNodup, hGhostNodup,
      hSharedStore, hGhostOp, hPromotionMatches, hPendingOp⟩ :=
    physical_actual_literal_row_frame_fields
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi

  obtain ⟨hTermZero, hGhostZero, hPromotionZero, hOldUnchanged,
      hStoreReset, hOffset, hSign⟩ :=
    physical_actual_literal_row_local_residue_laws
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
  have hGNum : Function.Injective (globalSigmaPrime BP bigMod) := by
    exact hnum
  obtain ⟨hFreshNodup, hFreshActive, hFreshUnused,
      hGhostNew, hNextFreshUnused, hEverUpdate⟩ :=
    physical_actual_literal_row_birth_laws
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hGNum i hi
  obtain ⟨hNonDivStore, hNonDivPromote⟩ :=
    physical_actual_literal_row_divisibility_bans
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
  have hAux := physical_actual_literal_row_auxiliary_ban
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
  have hDiv := physical_actual_literal_row_divisor_from_groups
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
  have hTarget := physical_actual_literal_target_operation
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi

  have hSurv := physical_actual_literal_row_surviving_translation
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
  have hSharedCong := physical_actual_literal_row_shared_congruence
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
  refine {
    numerical_prime := hPrime
    numerical_injective := hInject
    source_order := hSOrder
    target_order := hTOrder
    source_groups := hSGroups
    target_groups := hTGroups
    ghost_group_order := hGhostOrder
    ghost_group_labels := hGhostLabels
    shared_canonical_copy := hSharedCopy
    shared_source_pattern := hSharedSource
    shared_target_pattern := hSharedTarget
    source_perm := hSPerm
    target_perm := hTPerm
    source_nodup := hSNodup
    target_nodup := hTNodup
    active_nodup := hActiveNodup
    pending_nodup := hPendingNodup
    pendingAfter_nodup := hAfterNodup
    pendingNext_nodup := hNextNodup
    ghost_nodup := hGhostNodup
    fresh_nodup := hFreshNodup
    shared_store := hSharedStore
    term_zero := hTermZero

    ghost_operation := hGhostOp
    promotion_matches := hPromotionMatches
    promotion_zero := hPromotionZero
    target_operation := hTarget
    pending_operation := hPendingOp
    fresh_before_active := hFreshActive
    fresh_before_unused := hFreshUnused
    ghost_new := hGhostNew
    next_fresh_unused := hNextFreshUnused
    ever_update := hEverUpdate
    auxiliary_ban := hAux
    nondividing_store := hNonDivStore
    nondividing_promotion := hNonDivPromote
    signed_orientation := hSign
    divisor_from_groups := hDiv
    offset_update := hOffset
    ghost_birth_zero := hGhostZero
    old_pending_unchanged := hOldUnchanged
    store_reset := hStoreReset
    surviving_translation := hSurv
    shared_congruence := hSharedCong
  }

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryLinks -/

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

/-- A genuine inter-visit LIST permutation of pending labels,
not an equality of independently ordered Fock representatives.
Both sides are nodup by the physical path birth invariant. -/
theorem physical_actual_literal_interrow_pending_perm
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralChronologicalNext SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Perm
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1)) := by
  exact List.perm_of_nodup_nodup_toFinset_eq
    (physical_actual_literal_chrono_next_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)
    (physical_actual_literal_pending_before_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H (i+1) (Nat.succ_le_of_lt hi))
    (physical_actual_literal_chrono_next_support
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi)

/-- The literal residue functions already glue pointwise from one
visit to the next, including independent anchors at absent labels. -/
theorem physical_actual_literal_interrow_residue_eq
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (hi : i < N) (hnext : i+1 < N)
    (p : PhysicalSourcePrime BP) :
    (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).residueNext p =
    (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor (i+1) hnext).residueBefore p := by
  rfl

/-- The integer Fourier offsets glue without any reindexing. -/
theorem physical_actual_literal_interrow_offset_eq
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (i : ℕ) (hi : i < N) (hnext : i+1 < N) :
    (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).offsetAfter =
    (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor (i+1) hnext).offsetBefore := by
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryActiveLink -/

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

/-- Between physical visits, the unsampled target active array of
the previous E edge equals the next unsampled source active array.
This is an exact LIST equality, despite independent sigma/tau. -/
theorem physical_actual_literal_interrow_raw_active_eq
    (i : ℕ) (hi : i < N) (hnext : i+1 < N) :
    physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1) := by
  have hActive (g : BG) :
      (((H.edge i).2.2.1.bigChoice g).1) =
        ((H.beforeE (i+1)).2 g).1 := by
    have hO := congrArg
      (fun z : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
        ((z.2 g).1)) (H.E_output i hi)
    change ((H.before (i+1)).2 g).1 =
      (((H.edge i).2.2.1.bigChoice g).1) at hO
    have hG := physical_actual_literal_active_beforeE_eq_before
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H (i+1) hnext g
    exact hO.symm.trans hG.symm
  unfold physicalActualLiteralRawTargetList
    physicalActualLiteralRawSourceList
  apply List.map_congr_left
  intro a ha
  rcases a with ⟨g,j⟩
  simpa only [actualLiteralCanonicalTargetSlot,
    actualLiteralCanonicalSourceSlot,
    Equiv.apply_symm_apply] using
    congrArg (fun f : Fin (J+ell) → BP g =>
      (⟨g, f j⟩ : PhysicalSourcePrime BP)) (hActive g)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryScalarRow -/

section

open Classical
open scoped BigOperators

namespace Green64Literal

/-- RowValid does not constrain the source visit factor q. Changing
only q preserves all original operational and arithmetic obligations. -/
theorem row_valid_update_q
    {P G : Type} [DecidableEq P] [Fintype G]
    {slotCount : G → ℕ}
    (f : SourceRow (P := P) G slotCount)
    (h : RowValid f) (q' : ℝ) :
    RowValid {f with q := q'} := by
  cases f
  cases h
  constructor <;> assumption

end Green64Literal

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
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))

/-- Correct per-visit scalar q_i for the literal history; it is
sqrt(q) at the initial visit and q at internal E visits. -/
noncomputable def physicalActualLiteralHistoryScalarRow
    (i : ℕ) (hi : i < N) :
    Green64Literal.SourceRow (P := PhysicalSourcePrime BP) BG
      (fun _ => J+ell) :=
  { physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi with
    q := sourceVisitQ q N i }

theorem physical_actual_literal_history_scalar_row_valid
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    Green64Literal.RowValid
      (physicalActualLiteralHistoryScalarRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi) := by
  exact Green64Literal.row_valid_update_q _
    (physical_actual_literal_source_row_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta
      anchor hprime hnum i hi) (sourceVisitQ q N i)

theorem physical_actual_literal_history_scalar_row_q
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralHistoryScalarRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).q =
      if i = 0 then Real.sqrt q else q := by
  simp [physicalActualLiteralHistoryScalarRow, sourceVisitQ,
    Nat.ne_of_lt hi]

theorem physical_actual_literal_history_scalar_row_eta
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralHistoryScalarRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).eta =
    1 - (physicalActualLiteralHistoryScalarRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).q := by
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryActiveGlue -/

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
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))

/-- Truly ordered active lists, independent of sigma and tau:
the source frame and all operational fields remain unchanged. -/
noncomputable def physicalActualLiteralHistoryEndpointRow (i : ℕ) (hi : i < N) :
    Green64Literal.SourceRow (P := PhysicalSourcePrime BP) BG
      (fun _ => J+ell) :=
  Green64Literal.endpointActiveRow
    (physicalActualLiteralHistoryScalarRow SP smallMod BP bigMod
       J ell m cap patterns q rho Vbig muBig k N H
       Vsmall Knu zeta theta anchor i hi)


theorem physical_actual_literal_history_endpoint_row_valid
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    Green64Literal.RowValid
      (physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi) := by
  exact Green64Literal.row_valid_endpoint_active _
    (physical_actual_literal_history_scalar_row_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hprime hnum i hi)

/-- The original LiteralHistory.links_active holds ON THE NOSE on
successive physical E edges: the two independently sampled Haar
permutations are retained, while raw ordered endpoints glue. -/
theorem physical_actual_literal_history_endpoint_active_link
    (i : ℕ) (hi : i < N) (hn : i+1 < N) :
    (physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).nextActive =
    (physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor (i+1) hn).active := by
  change physicalActualLiteralRawTargetList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i =
    physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1)
  exact physical_actual_literal_interrow_raw_active_eq
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi hn

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryBirthGlue -/

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

/-- Fresh E births and the next source visit agree as tagged PRIME SETS.
No LIST equality is inferred from this theorem. -/
theorem physical_actual_literal_interrow_fresh_support
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralFreshTarget SP smallMod BP bigMod
       J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    (physicalActualLiteralFreshBefore SP smallMod BP bigMod
       J ell m cap patterns q rho Vbig muBig k N H (i+1)).toFinset := by
  rw [physical_actual_literal_fresh_target_support,
    physical_actual_literal_fresh_before_support]
  congr 1
  funext g
  simp [physicalGroupFreshVisit, hi]

/-- The entire tagged U-history glues exactly, using the physical
seen ledger and the actual G/E first-birth exclusions. -/
theorem physical_actual_literal_interrow_ever
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralEverBornBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i ∪
      (physicalActualLiteralFreshBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).toFinset) ∪
      (physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    physicalActualLiteralEverBornBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1) := by
  rw [physical_actual_literal_ever_before_support,
    physical_actual_literal_fresh_before_support,
    physical_actual_literal_ghost_batch_support,
    ← literal_physical_sigma_set_union,
    ← literal_physical_sigma_set_union,
    physical_actual_literal_ever_before_support]
  congr 1
  funext g
  exact (physicalGroupPastVisit_succ SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N i H hnum hi g).symm

/-- Genuinely distinct initial/next-visit first-birth labels. -/
theorem physical_actual_literal_fresh_before_nodup (i : ℕ) :
    (physicalActualLiteralFreshBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Nodup := by
  let xs : (g : BG) → List (BP g) := fun g =>
    (physicalGroupFreshVisit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g i).toList
  have hn : ∀ g, (xs g).Nodup := fun g => Finset.nodup_toList _
  have h := physical_literal_sigma_flatten_nodup BP xs hn
  simpa only [xs, physicalActualLiteralFreshBefore, List.map_map,
    Function.comp_def] using h

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryTerminal -/

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

/-- Vacuum after the genuine final G_N makes every incoming OLD atom
a selected termination, rather than postulating zero residues. -/
theorem physical_actual_terminal_pending_is_ended
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
       J ell m cap patterns q rho Vbig muBig k N H N).toFinset ⊆
    physicalActualLiteralEndedValues SP smallMod BP bigMod
       J ell m cap patterns q rho Vbig muBig k N H N := by
  intro p hp
  have hh : p ∈ physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H N :=
    List.mem_toFinset.mp hp
  unfold physicalActualLiteralPendingBefore at hh
  obtain ⟨g, _, hpG⟩ := List.mem_flatMap.mp hh
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hpG
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
  apply Finset.mem_biUnion.mpr
  refine ⟨g, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨j, ?_, ?_⟩
  · rw [(physical_actual_terminal_vacuum_excludes_ghost_births
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H hVac g).1]
    simp
  · simpa only [hj]

/-- Source final vacuum, combined with the actual G_N OLD zero test,
forces the measured Fock residue to vanish on all terminal OLD labels. -/
theorem physical_actual_terminal_literal_fock_zero
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H N) :
    physicalLiteralFockResidue BP bigMod cap SP smallMod
      (H.before N) p = 0 := by
  exact physical_actual_literal_ended_zero
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H N (Nat.le_refl N) p
    (physical_actual_terminal_pending_is_ended
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H hVac (List.mem_toFinset.mpr hp))

/-- The genuine residue function at the terminal physical visit,
including independent anchors on absent labels, is zero on OLD. -/
theorem physical_actual_terminal_anchored_pending_zero
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (p : PhysicalSourcePrime BP)
    (hp : p ∈ physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H N) :
    physicalActualLiteralAnchoredResidue SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      anchor N (H.before N) p = 0 := by
  cases p with
  | mk g v =>
      have hGroup := (physical_actual_literal_before_group_mem
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H N g v).mp hp
      have hEq :
          physicalActualLiteralAnchoredResidue SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig muBig k N H
              anchor N (H.before N) (⟨g,v⟩ : PhysicalSourcePrime BP) =
          physicalLiteralFockResidue BP bigMod cap SP smallMod
              (H.before N) (⟨g,v⟩ : PhysicalSourcePrime BP) := by
        unfold physicalActualLiteralAnchoredResidue
        exact if_pos hGroup
      exact hEq.trans
        (physical_actual_terminal_literal_fock_zero
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H hVac
          (⟨g,v⟩ : PhysicalSourcePrime BP) hp)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryInitial -/

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
/-- The literal OLD list at physical visit zero is exactly empty,
without quotienting through its finite support. -/
theorem physical_actual_literal_initial_pending_nil :
    physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0 = [] := by
  have hNil (g : BG) :
      Green64Fock.fockToList (((H.before 0).2 g).2) = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    have hcard := congrArg Multiset.card (H.initial_vacuum g)
    simpa [Green64Fock.fockMultiset, Green64Fock.fockToList] using hcard
  simp [physicalActualLiteralPendingBefore, hNil]

/-- The true per-prime historical past set U_0 is empty. -/
theorem physical_actual_literal_initial_ever_empty
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod)) :
    physicalActualLiteralEverBornBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0 = ∅ := by
  rw [physical_actual_literal_ever_before_support]
  ext p
  rw [literal_physical_sigma_set_mem]
  rw [physicalGroupPastVisit_zero SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H hnum p.1]
  simp

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryInitialSupport -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]

/-- A raw, group-tagged source list has the actual group-slot image
as its support. No sampling permutation or group quotient appears. -/
theorem literal_group_slot_list_toFinset (M : ℕ)
    (f : (g : BG) → Fin M → BP g) :
    ((Finset.univ : Finset (Σ _ : BG, Fin M)).toList.map
      (fun a => (⟨a.1, f a.1 a.2⟩ : PhysicalSourcePrime BP))).toFinset =
    literalPhysicalSigmaSet BP
      (fun g => (Finset.univ : Finset (Fin M)).image (f g)) := by
  ext p
  cases p with
  | mk g v =>
    simp only [List.mem_toFinset, List.mem_map,
      Finset.mem_toList, Finset.mem_univ, true_and,
      literal_physical_sigma_set_mem, Finset.mem_image]
    constructor
    · rintro ⟨⟨g',j⟩, h⟩
      have hg : g' = g := congrArg Sigma.fst h
      subst g'
      exact ⟨j, eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
    · rintro ⟨j, hv⟩
      exact ⟨⟨g,j⟩, congrArg (fun x : BP g =>
        (⟨g,x⟩ : PhysicalSourcePrime BP)) hv⟩

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
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

/-- Original first-visit F_0 is exactly the physical raw source
active PRIME SET. The list order may differ and is not identified. -/
theorem physical_actual_literal_initial_fresh_raw_support
    (hN : 0 < N) :
    (physicalActualLiteralFreshBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0).toFinset =
    (physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0).toFinset := by
  rw [physical_actual_literal_fresh_before_support]
  unfold physicalActualLiteralRawSourceList
  rw [physical_actual_literal_source_raw_reconstruction
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H 0]
  rw [literal_group_slot_list_toFinset BP (J+ell)
    (fun g j => ((H.beforeE 0).2 g).1 j)]
  apply congrArg (literalPhysicalSigmaSet BP)
  funext g
  change (Finset.univ : Finset (Fin (J+ell))).image
      (((H.before 0).2 g).1) =
    (Finset.univ : Finset (Fin (J+ell))).image
      (((H.beforeE 0).2 g).1)
  rw [physical_actual_literal_active_beforeE_eq_before
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H 0 hN g]

end Green64FullPhysicalE

end

