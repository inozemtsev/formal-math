module

public import Green64.Library.Correlation.Part017
public import Green64.Library.Correlation.Part012
public import Green64.Library.Correlation.Part010
public import Green64.Library.Correlation.Part014

@[expose] public section

/-!
# Correlation / Part018

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalActualELiteralRhoVisitSource -/

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
/-- The physical G-output Fock representation and its chronological
literal pendingAfter list differ only by a permutation of tagged
prime OCCURRENCES; no residue information is discarded. -/
theorem physical_actual_E_afterG_pending_perm
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).Perm
    (physicalActualLiteralPendingAfterG SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i) := by
  apply (List.perm_ext_iff_of_nodup
    (physical_actual_literal_chrono_afterG_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi))
    (physical_actual_literal_pending_afterG_nodup
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi))).mpr
  intro p
  have h := congrArg (fun s : Finset (PhysicalSourcePrime BP) => p ∈ s)
    (physical_actual_literal_chrono_afterG_support
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi))
  exact Iff.of_eq (by simpa only [List.mem_toFinset] using h)

/-- Exact original residue of each G-output Fock atom read from
the physical source row, indexed by the ACTUAL Fock occurrence. -/
theorem physical_actual_E_afterG_fock_residue_exact
    (i : ℕ) (hi : i < N) (g : BG)
    (j : Fin (Green64Fock.fockToList (((H.afterG i).2 g).2)).length) :
    let xs := Green64Fock.fockToList (((H.afterG i).2 g).2)
    (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).residueAfter
      (⟨g, (xs.get j).1⟩ : PhysicalSourcePrime BP) =
      (xs.get j).2 := by
  dsimp only
  let xs := Green64Fock.fockToList (((H.afterG i).2 g).2)
  have hn := physical_actual_literal_afterG_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i (Nat.le_of_lt hi) g
  have ha : (⟨(xs.get j).1, (xs.get j).2⟩ :
    Green64Fock.Atom (BP g) (bigMod g)) ∈
    Green64Fock.fockMultiset (((H.afterG i).2 g).2) := by
      simpa [xs, Green64Fock.fockMultiset,
        Green64Fock.fockToList] using List.get_mem xs j
  have hpPhysical : (⟨g,(xs.get j).1⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralPendingAfterG SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i := by
    apply (physical_actual_literal_afterG_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i g (xs.get j).1).mpr
    exact List.mem_map.mpr ⟨xs.get j,List.get_mem xs j,rfl⟩
  have hpChrono : (⟨g,(xs.get j).1⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :=
    (physical_actual_E_afterG_pending_perm
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi).mem_iff.mpr hpPhysical
  exact (physical_actual_literal_row_residue_after_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
      _ hpChrono).trans
    (physical_literal_fock_residue_of_atom BP bigMod cap SP smallMod
      (H.afterG i) (⟨g,(xs.get j).1⟩ : PhysicalSourcePrime BP)
      hn (xs.get j).2 ha)
/-- The genuine source visit-zero index cardinal is a sum over
all actual BIG group G-output Fock zero occurrences, with no
deduplication of numerical prime labels. -/
theorem physical_actual_E_source_visit_zero_group_sum
    (i : ℕ) (hi : i < N) :
    (Green64Literal.visitZeroIndices
      (physicalActualLiteralSourceRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi)).card =
    ∑ g : BG, Green64PhysicalEdge.oldZeroCount (((H.afterG i).2 g).2) := by
  let f := physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi
  have hp := physical_actual_E_afterG_pending_perm
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  have hSource :
      (Green64Literal.visitZeroIndices f).card =
      ((Finset.univ : Finset
        (Fin (physicalActualLiteralPendingAfterG SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).length)).filter
        (fun j => f.residueAfter
          ((physicalActualLiteralPendingAfterG SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get j) = 0)).card := by
    change ((Finset.univ : Finset
      (Fin (physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).length)).filter
      (fun j => f.residueAfter
        ((physicalActualLiteralChronologicalAfterG SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get j) = 0)).card = _
    exact Green64Literal.literal_perm_index_filter_card
      _ _ hp (fun p => f.residueAfter p = 0)
      (physical_actual_literal_pending_afterG_nodup
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i (Nat.le_of_lt hi))
  rw [hSource]
  have hGroup := physical_old_index_sigma_flatMap_card
    (Finset.univ.toList : List BG)
    (fun g => Green64Fock.fockToList (((H.afterG i).2 g).2))
    (fun g a => (⟨g,a.1⟩ : PhysicalSourcePrime BP))
    (fun p => f.residueAfter p = 0)
  unfold physicalActualLiteralPendingAfterG
  rw [hGroup]
  rw [physical_big_group_list_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change
      ((Finset.univ : Finset
        (Fin (Green64Fock.fockToList (((H.afterG i).2 g).2)).length)).filter
        (fun j => f.residueAfter
          (⟨g,((Green64Fock.fockToList (((H.afterG i).2 g).2)).get j).1⟩) = 0)).card =
      Green64PhysicalEdge.oldZeroCount (((H.afterG i).2 g).2)
  rw [← physical_E_fock_list_zero_indices (bigMod g) (((H.afterG i).2 g).2)]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [physical_actual_E_afterG_fock_residue_exact
      SP smallMod BP bigMod J ell m cap patterns q rho Vbig
      muBig k N H Vsmall Knu zeta theta anchor i hi g j]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralRhoTargetSource -/

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
/-- Literal target-zero residues refer to actual next-visit physical
Fock atoms after the REAL E move, including newly stored particles.
No OLD index or sigma/tau occurrence is forgotten. -/
theorem physical_actual_E_next_fock_residue_exact
    (i : ℕ) (hi : i < N) (g : BG)
    (j : Fin (Green64Fock.fockToList
      (((H.before (i+1)).2 g).2)).length) :
    let xs := Green64Fock.fockToList (((H.before (i+1)).2 g).2)
    (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).residueNext
      (⟨g, (xs.get j).1⟩ : PhysicalSourcePrime BP) =
      (xs.get j).2 := by
  dsimp only
  let xs := Green64Fock.fockToList (((H.before (i+1)).2 g).2)
  have hn := physical_actual_literal_before_pending_nodup
    SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H (i+1) (Nat.succ_le_of_lt hi) g
  have ha : (⟨(xs.get j).1, (xs.get j).2⟩ :
    Green64Fock.Atom (BP g) (bigMod g)) ∈
    Green64Fock.fockMultiset (((H.before (i+1)).2 g).2) := by
      simpa [xs, Green64Fock.fockMultiset,
        Green64Fock.fockToList] using List.get_mem xs j
  have hpPhysical : (⟨g,(xs.get j).1⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H (i+1) := by
    apply (physical_actual_literal_before_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H (i+1) g (xs.get j).1).mpr
    exact List.mem_map.mpr ⟨xs.get j,List.get_mem xs j,rfl⟩
  have hpChrono : (⟨g,(xs.get j).1⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralChronologicalNext SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :=
    (physical_actual_literal_interrow_pending_perm
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi).mem_iff.mpr hpPhysical
  exact (physical_actual_literal_row_residue_next_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
      _ hpChrono).trans
    (physical_literal_fock_residue_of_atom BP bigMod cap SP smallMod
      (H.before (i+1))
      (⟨g,(xs.get j).1⟩ : PhysicalSourcePrime BP)
      hn (xs.get j).2 ha)
/-- Full E target-zero exponent counted on the original output Fock
atom INDEX SET across every BIG group. -/
theorem physical_actual_E_source_target_zero_group_sum
    (i : ℕ) (hi : i < N) :
    (Green64Literal.targetZeroIndices
      (physicalActualLiteralSourceRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi)).card =
    ∑ g : BG, Green64PhysicalEdge.oldZeroCount
      (((H.before (i+1)).2 g).2) := by
  let f := physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi
  have hp := physical_actual_literal_interrow_pending_perm
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  have hSource :
      (Green64Literal.targetZeroIndices f).card =
      ((Finset.univ : Finset
        (Fin (physicalActualLiteralPendingBefore SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H (i+1)).length)).filter
        (fun j => f.residueNext
          ((physicalActualLiteralPendingBefore SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H (i+1)).get j) = 0)).card := by
    change ((Finset.univ : Finset
      (Fin (physicalActualLiteralChronologicalNext SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).length)).filter
      (fun j => f.residueNext
        ((physicalActualLiteralChronologicalNext SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get j) = 0)).card = _
    exact Green64Literal.literal_perm_index_filter_card
      _ _ hp (fun p => f.residueNext p = 0)
      (physical_actual_literal_pending_before_nodup
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H (i+1) (Nat.succ_le_of_lt hi))
  rw [hSource]
  have hGroup := physical_old_index_sigma_flatMap_card
    (Finset.univ.toList : List BG)
    (fun g => Green64Fock.fockToList (((H.before (i+1)).2 g).2))
    (fun g a => (⟨g,a.1⟩ : PhysicalSourcePrime BP))
    (fun p => f.residueNext p = 0)
  unfold physicalActualLiteralPendingBefore
  rw [hGroup]
  rw [physical_big_group_list_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change
      ((Finset.univ : Finset
        (Fin (Green64Fock.fockToList
          (((H.before (i+1)).2 g).2)).length)).filter
        (fun j => f.residueNext
          (⟨g,((Green64Fock.fockToList
            (((H.before (i+1)).2 g).2)).get j).1⟩) = 0)).card =
      Green64PhysicalEdge.oldZeroCount (((H.before (i+1)).2 g).2)
  rw [← physical_E_fock_list_zero_indices (bigMod g)
    (((H.before (i+1)).2 g).2)]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [physical_actual_E_next_fock_residue_exact
      SP smallMod BP bigMod J ell m cap patterns q rho Vbig
      muBig k N H Vsmall Knu zeta theta anchor i hi g j]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralFockZeroOrbit -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Genuine symmetric Fock MULTISET equality preserves every indexed
zero-residue occurrence even when the same atom occurs repeatedly.
The orbit quotient does not replace particles by a set of primes. -/
theorem physical_E_fock_zero_count_orbit
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    {B : ℕ}
    (x y : Green64Fock.FockState (Green64Fock.Atom P modulus) B)
    (hm : Green64Fock.fockMultiset x =
      Green64Fock.fockMultiset y) :
    Green64PhysicalEdge.oldZeroCount x =
      Green64PhysicalEdge.oldZeroCount y := by
  have hh : (Green64Fock.fockToList x :
      Multiset (Green64Fock.Atom P modulus)) =
    (Green64Fock.fockToList y :
      Multiset (Green64Fock.Atom P modulus)) := by
    simpa only [Green64Fock.fockMultiset, Green64Fock.fockToList] using hm
  have hp : (Green64Fock.fockToList x).Perm
      (Green64Fock.fockToList y) := Multiset.coe_eq_coe.mp hh
  let z : Green64Fock.Atom P modulus → Prop := fun a => a.2 = 0
  calc
    Green64PhysicalEdge.oldZeroCount x =
        (Green64Fock.fockToList x).countP
          (fun a => decide (z a)) := by
      rw [← physical_E_fock_list_zero_indices modulus x]
      exact physical_old_index_card_eq_countP
        (Green64Fock.fockToList x) z
    _ = (Green64Fock.fockToList y).countP
          (fun a => decide (z a)) := hp.countP_eq _
    _ = Green64PhysicalEdge.oldZeroCount y := by
      rw [← physical_E_fock_list_zero_indices modulus y]
      exact (physical_old_index_card_eq_countP
        (Green64Fock.fockToList y) z).symm

end Green64FullPhysicalE

end

/-! ## MemoryPrimitiveEFrameCoefficient -/

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
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- The complete source E coefficient written without an OLD representative.
The two original rho counts, promotion V denominators, fresh mu integrations,
Nu/free-D mass, both BIG and SMALL permutation masses and original K/phase
are retained. The SMALL Haar quotient is not canceled by this definition. -/
def memoryPrimitiveEFrameCoefficient
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) : ℂ :=
  let D := memoryIndependentD SP smallMod BP bigMod J ell m (patterns f.1.1)
    f.1.2 ix f.2.1 f.2.2.2.1
  let delta := o*k*(D : ℤ)
  (sourceAuxMass BP bigMod J m Vbig (patterns f.1.1) f.1.2 : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    (∏ g : BG,
      (rho : ℂ)^((memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i).countP
          (fun z => z.2 = 0) +
        (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true (i+1)).countP
          (fun z => z.2 = 0)) *
      (1 / (Vbig g : ℂ)^(memoryEPromoteSlots (J+ell) (A g) (life g) i
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)) (f.2.2.1 g)).card) *
      (∏ j ∈ orientedFresh (J+ell) (sourceBigShared J ell m (patterns f.1.1) g)
          (memoryEPromoteSlots (J+ell) (A g) (life g) i
            (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)) (f.2.2.1 g)),
        (mu g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (f.2.2.1 g j)) : ℂ))) *
    Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vsmall
      (sourceSmallShared J ell) delta
      (fun _ _ => originalEdgeScalar
        (Knu f.1.1 f.1.2
          (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) (f.2.1 g j))
          (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (f.2.2.1 g j)))
        zeta theta D o k) f.2.2.2.1 f.2.2.2.2 ix.1 iy.1

/-- Evaluation of the literal E scalar. OLD ordering independence is a
conclusion, not an added uniform-weight hypothesis. -/
theorem memory_source_primitive_E_frame_coefficient_exact
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hsmall : x.1 = ix.1)
    (hactive : ∀ g, (x.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (hoff : o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns f.1.1)
      f.1.2 ix f.2.1 f.2.2.2.1 : ℤ) = offset (i+1)-offset i) :
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig mu Knu zeta theta o k x
      (memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
        A life offset i hs x hOld iy f) =
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A life offset i ix iy q rho Vsmall Vbig mu Knu zeta theta o k f := by
  let D := memoryIndependentD SP smallMod BP bigMod J ell m (patterns f.1.1)
    f.1.2 ix f.2.1 f.2.2.2.1
  let delta := o*k*(D : ℤ)
  have hD : sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      (patterns f.1.1) f.1.2 x f.2.1 f.2.2.2.1 = D := by
    simp only [D, sourceOrientedPhysicalD, memoryIndependentD, hsmall, hactive]
  have hstep : sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns f.1.1) f.1.2 x f.2.1 f.2.2.2.1 o k = delta := by
    simp only [sourceOrientedStep, hD, delta]
  have hx (g : BG) : Function.Injective (x.2 g).1 := by
    rw [hactive g]; exact Green64SmallHaar.marks_injective _ _ _
  have hA0x : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p := by
    intro g p; rw [hactive g]; exact hA0 g p
  have holdzero (g : BG) : Green64PhysicalEdge.oldZeroCount ((x.2 g).2) =
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i).countP
        (fun z => z.2 = 0) := by
    calc
      _ = (Green64Fock.fockToList ((x.2 g).2)).countP (fun z => z.2 = 0) := by
        rw [← physical_E_fock_list_zero_indices (bigMod g) ((x.2 g).2)]
        exact physical_old_index_card_eq_countP (Green64Fock.fockToList ((x.2 g).2))
          (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
      _ = _ := (hOld g).countP_eq _
  have houtzero (g : BG) : outputZeroCount (bigMod g) (J+ell) (cap g) (x.2 g)
      (f.2.1 g) delta
      (memoryPrimitiveEChoice (bigMod g) (J+ell) (cap g) (A g) (life g) offset i
        (hs g) (x.2 g) (hOld g) (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
        (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (iy.2 g))
        (f.2.1 g) (f.2.2.1 g)) =
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true (i+1)).countP
        (fun z => z.2 = 0) := by
    exact (memory_E_output_perm_canonical (bigMod g) (J+ell) (cap g) (A g) (life g)
      offset i (hs g) (x.2 g) (hx g) (hA0x g) (hOld g)
      (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
      (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (iy.2 g)) (hA1 g)
      (f.2.1 g) (f.2.2.1 g) delta hoff).countP_eq _
  have hbig (g : BG) : orientedBigBranchCoefficient (bigMod g) (J+ell) (cap g)
      (mu g) (Vbig g) rho (x.2 g)
      (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
      (sourceBigShared J ell m (patterns f.1.1) g) (f.2.1 g) (f.2.2.1 g) delta
      (memoryPrimitiveEChoice (bigMod g) (J+ell) (cap g) (A g) (life g) offset i
        (hs g) (x.2 g) (hOld g) (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
        (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (iy.2 g))
        (f.2.1 g) (f.2.2.1 g)) =
      (rho : ℂ)^((memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i).countP
          (fun z => z.2 = 0) +
        (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true (i+1)).countP
          (fun z => z.2 = 0)) *
      (1 / (Vbig g : ℂ)^(memoryEPromoteSlots (J+ell) (A g) (life g) i
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)) (f.2.2.1 g)).card) *
      (∏ j ∈ orientedFresh (J+ell) (sourceBigShared J ell m (patterns f.1.1) g)
          (memoryEPromoteSlots (J+ell) (A g) (life g) i
            (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)) (f.2.2.1 g)),
        (mu g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (f.2.2.1 g j)) : ℂ)) := by
    unfold orientedBigBranchCoefficient
    rw [holdzero g, houtzero g]
    rfl
  unfold sourceOrientedPhysicalCoefficient memoryPrimitiveEFrameCoefficient
  dsimp only [memoryPrimitiveEFrameChoice, memoryPrimitiveESourceChoice]
  rw [hD, hstep, hsmall]
  simp_rw [hbig, hactive]
  rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEOrbitFibre -/

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
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- This finite subset retains all original Nu, auxiliary and permutation
coordinates satisfying the literal frozen source edge and integer displacement.
It is a local edge condition, not an assumed global reconstruction. -/
def memoryPrimitiveECompatibleFrames
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell) (o k : ℤ) :
    Finset (MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :=
  Finset.univ.filter (fun f =>
    (o = 1 ∨ o = -1) ∧
    memoryIndependentAuxBan SP smallMod BP bigMod J ell m (patterns f.1.1) f.1.2 ix iy ∧
    Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell) (sourceSmallShared J ell)
      (o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns f.1.1)
        f.1.2 ix f.2.1 f.2.2.2.1 : ℤ)) f.2.2.2.1 f.2.2.2.2 ix.1 iy.1 ∧
    Green64SmallHaar.groupEdgeAllowedPerm BP bigMod (J+ell)
      (sourceBigShared J ell m (patterns f.1.1))
      (o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns f.1.1)
        f.1.2 ix f.2.1 f.2.2.2.1 : ℤ)) f.2.1 f.2.2.1 ix.2 iy.2 ∧
    o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns f.1.1)
      f.1.2 ix f.2.1 f.2.2.2.1 : ℤ) = offset (i+1)-offset i)

/-- Forward inclusion uses original source arithmetic, global chronological
birth eligibility and the checked canonical E output. -/
theorem memory_source_primitive_E_canonical_frame_mem
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hdomain : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hsmall : x.1 = ix.1)
    (hactive : ∀ g, (x.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (o : ℤ) (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (hf : f ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod J ell m patterns
      offset i ix iy o k) :
    memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
        A life offset i hs x hOld iy f ∈
      memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
        A life offset i x iy o k f := by
  obtain ⟨ho, hban, hsmallleg, hbigleg, hoff⟩ := (Finset.mem_filter.mp hf).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · exact memory_source_primitive_E_indexed_eligible SP smallMod BP bigMod J ell m cap
      patterns A life offset i hs q rho Vsmall Vbig k R hdomain ix iy x hsmall hactive
      hOld hA0 hA1 f.1.1 f.1.2 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2 o ho
      hban hsmallleg hbigleg hoff.symm
  · rfl
  · have hx : ∀ g, Function.Injective (x.2 g).1 := by
      intro g; rw [hactive g]; exact Green64SmallHaar.marks_injective _ _ _
    have hA0x : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p := by
      intro g p; rw [hactive g]; exact hA0 g p
    apply memory_source_primitive_E_output_exact SP smallMod BP bigMod J ell m cap
      patterns A life offset i hs x hx hOld iy hA0x hA1 f.1.1 f.1.2
      f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2 o k
    simp only [sourceOrientedStep, sourceOrientedPhysicalD, memoryIndependentD,
      hsmall, hactive] at hoff ⊢
    exact hoff

/-- Full conditional OLD Fock representative average, with its ORIGINAL
mass ratios. No uniform representative law is assumed. This cancels only the
input orbit total; all original E sampling masses remain in the coefficient. -/
theorem memory_source_primitive_E_orbit_weighted_fibre
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hdomain : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (x0 : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hsmall0 : x0.1 = ix.1)
    (hactive0 : ∀ g, (x0.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (hOld0 : ∀ g, (Green64Fock.fockToList ((x0.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p, 0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o : ℤ) (f : MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (hf : f ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod J ell m patterns
      offset i ix iy o k) :
    (∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)) *
      (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
          A life offset i x iy o k f,
        sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig mu Knu zeta theta o k x z)) =
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A life offset i ix iy q rho Vsmall Vbig mu Knu zeta theta o k f := by
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0
  let S := (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
    (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x = y)
  have hrep : ∀ x ∈ S, x.1 = ix.1 ∧
      (∀ g, (x.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g)) ∧
      (∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
        (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i)) := by
    intro x hx
    have he := (Finset.mem_filter.mp hx).2
    refine ⟨(congrArg Prod.fst he).trans hsmall0, ?_, ?_⟩
    · intro g
      exact (congrArg (fun out : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
        (out.2 g).1) he).trans (hactive0 g)
    · intro g
      have hm := congrArg (fun out : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
        (out.2 g).2) he
      exact (Multiset.coe_eq_coe.mp hm).trans (hOld0 g)
  have hy : y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap :=
    Finset.mem_image.mpr ⟨x0, Finset.mem_univ _, rfl⟩
  have hm : (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (physicalOrbitMass_pos SP smallMod BP bigMod (J+ell) cap
      Vsmall mu hdomain.Vsmall_pos hmu y hy)
  have hnorm : (∑ x ∈ S, (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ)) = 1 := by
    rw [← Finset.sum_div]
    have hmass : (∑ x ∈ S, (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ)) =
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) := by
      simp only [physicalOrbitMass, Complex.ofReal_sum]
      rfl
    rw [hmass, div_self hm]
  have hfixed : ∀ x ∈ S,
      (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
          A life offset i x iy o k f,
        sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig mu Knu zeta theta o k x z) =
      memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
        A life offset i ix iy q rho Vsmall Vbig mu Knu zeta theta o k f := by
    intro x hx
    obtain ⟨hsmall, hactive, hOld⟩ := hrep x hx
    have hinj : ∀ g, Function.Injective (x.2 g).1 := by
      intro g; rw [hactive g]; exact Green64SmallHaar.marks_injective _ _ _
    have hA0x : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p := by
      intro g p; rw [hactive g]; exact hA0 g p
    rw [memory_source_primitive_E_fixed_frame_weighted_sum SP smallMod BP bigMod
      J ell m cap patterns A life offset i hs x hinj hA0x hOld iy hA1 q rho Vsmall Vbig
      mu Knu zeta theta o k f,
      if_pos (memory_source_primitive_E_canonical_frame_mem SP smallMod BP bigMod
        J ell m cap patterns A life offset i hs q rho Vsmall Vbig k R hdomain
        ix iy x hsmall hactive hOld hA0 hA1 o f hf)]
    exact memory_source_primitive_E_frame_coefficient_exact SP smallMod BP bigMod
      J ell m cap patterns A life offset i hs ix iy x hsmall hactive hOld hA0 hA1
      q rho Vsmall Vbig mu Knu zeta theta o k f (Finset.mem_filter.mp hf).2.2.2.2.2
  change (∑ x ∈ S, _ * _) = _
  calc
    _ = ∑ x ∈ S, ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ)) *
        memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
          A life offset i ix iy q rho Vsmall Vbig mu Knu zeta theta o k f := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hfixed x hx]
    _ = _ := by rw [← Finset.sum_mul, hnorm, one_mul]
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEFullSampling -/

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
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- The literal full E-choice slice, without a separately sampled frame.
Its Nu and auxiliaries live on the original dependent carrier. -/
def memoryPrimitiveEFullSamplingFibre
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell) (o k : ℤ) :
    Finset (FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x) :=
  Finset.univ.filter (fun z =>
    (⟨x, z⟩ : Σ xx : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns xx) ∈
      physicalOrientedEIndexedLegalFibre SP smallMod BP bigMod J ell m cap patterns o k
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
        (memoryBornBeforeValues BP bigMod life (i+1)) ∧
    sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z =
      memoryPrimitiveECanonicalOutput SP smallMod BP bigMod J ell A life offset i iy ∧
    memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns x z ∈
      memoryPrimitiveECompatibleFrames SP smallMod BP bigMod J ell m patterns offset i ix iy o k)

/-- Actual Nu/auxiliary/permutation partition of the complete E slice. It
is not a permutation of outputs and does not multiply by an orbit cardinality. -/
theorem memory_source_primitive_E_full_sampling_partition
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell) (o k : ℤ)
    (F : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x → ℂ) :
    (∑ z ∈ memoryPrimitiveEFullSamplingFibre SP smallMod BP bigMod J ell m cap patterns
      A life offset i x ix iy o k, F z) =
    ∑ f ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod J ell m patterns offset i ix iy o k,
      ∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
        A life offset i x iy o k f, F z := by
  unfold memoryPrimitiveEFullSamplingFibre memoryPrimitiveEFixedFrameFibre
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hidx : (⟨x, z⟩ : Σ xx : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns xx) ∈
      physicalOrientedEIndexedLegalFibre SP smallMod BP bigMod J ell m cap patterns o k
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
        (memoryBornBeforeValues BP bigMod life (i+1))
  · by_cases hout : sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k z =
        memoryPrimitiveECanonicalOutput SP smallMod BP bigMod J ell A life offset i iy
    · simp [hidx, hout, eq_comm]
    · simp [hidx, hout]
  · simp [hidx]

/-- FULL weighted E-fibre sum over every original Nu, auxiliary, BIG/SMALL
endpoint permutation and OLD Fock representative in one frozen source edge.
The independent target BIG residue torus is not resampled: only its marks are
read. The source SMALL state and its genuine pair mass remain literal. -/
theorem memory_source_primitive_E_full_sampling_weighted_fibre
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hdomain : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (x0 : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hsmall0 : x0.1 = ix.1)
    (hactive0 : ∀ g, (x0.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (hOld0 : ∀ g, (Green64Fock.fockToList ((x0.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p, 0 < mu g p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o : ℤ) :
    (∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)) *
      (∑ z ∈ memoryPrimitiveEFullSamplingFibre SP smallMod BP bigMod J ell m cap patterns
          A life offset i x ix iy o k,
        sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig mu Knu zeta theta o k x z)) =
    ∑ f ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod J ell m patterns offset i ix iy o k,
      memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
        A life offset i ix iy q rho Vsmall Vbig mu Knu zeta theta o k f := by
  simp_rw [memory_source_primitive_E_full_sampling_partition SP smallMod BP bigMod J ell m cap
    patterns A life offset i, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  simpa only [Finset.mul_sum] using memory_source_primitive_E_orbit_weighted_fibre SP smallMod BP bigMod J ell m cap
    patterns A life offset i hs q rho Vsmall Vbig k R hdomain ix iy x0 hsmall0 hactive0
    hOld0 hA0 hA1 mu hmu Knu zeta theta o f hf
end Green64FullPhysicalE

end

end

/-! ## MemorySourceEWeightedFibre -/

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

/-- Literal source specialization of the FULL frozen E sampling sum.
All schedule support and mu positivity are DERIVED from original domain and
literal nonzero frozen lifespan factors. The spectral adaptor reads fixed
zeta and K(target,source) on reverse edges; no start*zeta is introduced.
This remains a one-edge fibre result, not MemoryIdentityTarget. -/
theorem memory_source_canonical_E_full_weighted_fibre
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R i : ℕ)
    (hdomain : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (A : (g : BG) → BP g → Finset ℕ)
    (life : (g : BG) → BP g → MemoryLifespanChoice (2*R+1))
    (offset : ℕ → ℤ)
    (hn : ∀ g p, memoryFrozenPrimeTerm (bigMod g p) (sourceVisitEta q (2*R))
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (2*R+1) (life g p) ≠ 0)
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (x0 : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hsmall0 : x0.1 = ix.1)
    (hactive0 : ∀ g, (x0.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (hOld0 : ∀ g, (Green64Fock.fockToList ((x0.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o : ℤ) :
    (∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
          (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall
          (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)) *
      (∑ z ∈ memoryPrimitiveEFullSamplingFibre SP smallMod BP bigMod J ell m cap patterns
          A life offset i x ix iy o k,
        sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
          (memoryOrientationK BP J ell m patterns Knu o) zeta theta o k x z)) =
    ∑ f ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod J ell m patterns offset i ix iy o k,
      memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
        A life offset i ix iy q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (memoryOrientationK BP J ell m patterns Knu o) zeta theta o k f := by
  apply memory_source_primitive_E_full_sampling_weighted_fibre SP smallMod BP bigMod
    J ell m cap patterns A life offset i
  · intro g p
    exact memory_frozen_nonzero_schedule_support (bigMod g p) (sourceVisitEta q (2*R))
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (2*R+1) (life g p) (hn g p)
  · exact hdomain
  · exact hsmall0
  · exact hactive0
  · exact hOld0
  · exact hA0
  · exact hA1
  · intro g p
    exact physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hdomain.q_pos) (le_of_lt hdomain.q_lt_one)
      (hdomain.Vbig_pos g) (hdomain.big_above_visits g p)
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceCoordinates -/

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

/-- Original frozen coordinates: every actual SMALL Haar state at each
visit, every ordered injective BIG active list, and the unchanged dependent
Nu/auxiliary/four-permutation frame at each edge. No Fock choices, BIG
residue anchors, lifespans, or invented occurrence multiplicities. -/
abbrev MemoryFrozenSourcePath (N : ℕ) :=
  (Fin (N+1) → Green64SmallHaar.GroupState SP smallMod (J+ell)) ×
  (Fin (N+1) → (g : BG) → {f : Fin (J+ell) → BP g // Function.Injective f}) ×
  (Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)

noncomputable instance (N : ℕ) :
    Fintype (MemoryFrozenSourcePath SP smallMod BP J ell m patterns N) :=
  by
    classical
    letI : Fintype (Green64SmallHaar.GroupState SP smallMod (J+ell)) := inferInstance
    letI : Fintype ((g : BG) → {f : Fin (J+ell) → BP g // Function.Injective f}) := inferInstance
    letI : Fintype (MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) := inferInstance
    unfold MemoryFrozenSourcePath
    infer_instance

def memoryFrozenSourceD {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N) (i : Fin N) : ℕ :=
  let f := ω.2.2 i
  (∏ g : SG, ∏ j ∈ sourceSmallShared J ell g,
    smallMod g (Green64SmallHaar.marks (smallMod g) (J+ell) (ω.1 i.castSucc g)
      (f.2.2.2.1 g j))) *
  (∏ g : BG,
    (∏ j ∈ sourceBigShared J ell m (patterns f.1.1) g,
      bigMod g ((ω.2.1 i.castSucc g).val (f.2.1 g j))) *
    (∏ j : ↥((patterns f.1.1).free g), bigMod g (f.1.2 g j)))

/-- Literal signed integer position, with zero initial offset. -/
def memoryFrozenSourceOffset {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N) (k : ℤ)
    (t : ℕ) : ℤ :=
  ∑ i : Fin N, if i.val < t then
    physicalAlternatingSign i.val * k *
      (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ)
    else 0

def memoryFrozenSourceVisits {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (p : PhysicalSourcePrime BP) : Finset ℕ :=
  (Finset.univ : Finset (Fin (N+1))).filter
    (fun i => ∃ j, (ω.2.1 i p.1).val j = p.2) |>.image Fin.val

/-- BIG compatibility retains both endpoint bans and every prescribed
shared slot. Congruences for active/ghost prime hits belong to the prime
terms, not to this coefficient. SMALL congruences remain in the literal
original SMALL kernel below. -/
def memoryFrozenSourceEdgeAllowed {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (k : ℤ) (i : Fin N) : Prop :=
  let f := ω.2.2 i
  (physicalAlternatingSign i.val = 1 ∨ physicalAlternatingSign i.val = -1) ∧
  k ≠ 0 ∧
  (∀ (g : BG) (j : ↥((patterns f.1.1).free g)) (a : Fin (J+ell)),
    f.1.2 g j ≠ (ω.2.1 i.castSucc g).val a ∧ f.1.2 g j ≠ (ω.2.1 i.succ g).val a) ∧
  (∀ (g : BG) (j : Fin (J+ell)), j ∈ sourceBigShared J ell m (patterns f.1.1) g →
    (ω.2.1 i.castSucc g).val (f.2.1 g j) = (ω.2.1 i.succ g).val (f.2.2.1 g j))

/-- One original frozen edge coefficient without BIG endpoint damping.
Its V^-t target normalization and all source sampling masses are literal.
Fixed zeta and endpoint-swapped K on reverse edges are preserved. -/
def memoryFrozenSourceEdgeWeight {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (i : Fin N) : ℂ :=
  let f := ω.2.2 i
  let D := memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i
  let o := physicalAlternatingSign i.val
  if memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i then
    (sourceAuxMass BP bigMod J m Vbig (patterns f.1.1) f.1.2 : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    (∏ g : BG, (1 / (Vbig g : ℂ) ^
      Green64SmallHaar.unsharedSlots (J+ell) (sourceBigShared J ell m (patterns f.1.1) g))) *
    Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vsmall
      (sourceSmallShared J ell) (o*k*(D : ℤ))
      (fun _ _ => originalEdgeScalar
        (memoryOrientationK BP J ell m patterns Knu o f.1.1 f.1.2
          (fun g j => (ω.2.1 i.castSucc g).val (f.2.1 g j))
          (fun g j => (ω.2.1 i.succ g).val (f.2.2.1 g j)))
        zeta theta D o k)
      f.2.2.2.1 f.2.2.2.2 (ω.1 i.castSucc) (ω.1 i.succ)
  else 0

/-- W_frozen includes the original initial SMALL Haar mass and BIG
V^-M mark mass. The product of prime terms separately supplies reciprocal
prime/Haar costs, boundary sqrt(q), internal q, and all orphan sectors. -/
def memoryFrozenSourceWeight {N : ℕ}
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N) : ℂ :=
  (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
    (∏ g : BG, 1 / (Vbig g : ℂ)^(J+ell)) *
    ∏ i : Fin N, memoryFrozenSourceEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω i

local instance memory_global_prime_nezero (p : PhysicalSourcePrime BP) :
    NeZero (physicalSourcePrimeValue BP bigMod p) :=
  inferInstanceAs (NeZero (bigMod p.1 p.2))

/-- Source independent BIG Haar sum AFTER freezing every original path
coordinate. Relating it to memoryIndependentRoot is a separate obligation. -/
def memoryFrozenSourceHaarRoot
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  ∑ ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R),
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω *
    (memoryFrozenHaarExpectation (physicalSourcePrimeValue BP bigMod)
      (sourceVisitEta q (2*R))
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω) (2*R+1) : ℂ)

/-- Explicit full original frozen omega/life sum, with UNNORMALIZED literal
memoryFrozenPrimeTerm. Baselines are already in the actual indexed root
weight and must cancel against baseline-relative local prime costs. -/
def memoryFrozenSourceLifespanRoot
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  ∑ ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R),
    ∑ life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1),
      memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ p : PhysicalSourcePrime BP, memoryFrozenPrimeTerm (bigMod p.1 p.2)
        (sourceVisitEta q (2*R))
        (fun i => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k i : ZMod (bigMod p.1 p.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω p)
        (2*R+1) (life p) : ℝ)

end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceHaarExpansion -/

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

theorem memory_frozen_source_visits_subset {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (p : PhysicalSourcePrime BP) :
    memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω p ⊆ Finset.range (N+1) := by
  intro t ht
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_range.mpr i.isLt

theorem memory_frozen_source_offset_zero {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N) (k : ℤ) :
    memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k 0 = 0 := by
  simp [memoryFrozenSourceOffset]

theorem memory_frozen_source_offset_step {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N) (k : ℤ)
    (t : ℕ) (ht : t < N) :
    memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k (t+1) -
      memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t =
    physicalAlternatingSign t * k *
      (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω ⟨t, ht⟩ : ℤ) := by
  let F := fun i : Fin N => physicalAlternatingSign i.val * k *
    (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ)
  have hmask (i : Fin N) :
      (if i.val < t+1 then F i else 0) =
      (if i.val < t then F i else 0) +
      (if i = ⟨t, ht⟩ then F i else 0) := by
    by_cases he : i = ⟨t, ht⟩
    · subst i
      simp
    · have hne : i.val ≠ t := fun h => he (Fin.ext h)
      have heq : i.val < t+1 ↔ i.val < t := by omega
      simp [he, heq]
  have hh : memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k (t+1) =
      memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t + F ⟨t, ht⟩ := by
    unfold memoryFrozenSourceOffset
    change (∑ i : Fin N, if i.val < t+1 then F i else 0) = _
    simp_rw [hmask]
    rw [Finset.sum_add_distrib]
    simp [F]
  rw [hh]
  simp [F]

local instance (p : PhysicalSourcePrime BP) :
    NeZero (physicalSourcePrimeValue BP bigMod p) :=
  inferInstanceAs (NeZero (bigMod p.1 p.2))

/-- The already checked independent BIG product expansion, now applied to
every literal frozen source path with its FULL original source coefficient.
This is not the physical root comparison or the independent-row reindex. -/
theorem memory_frozen_source_Haar_lifespan_exact
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    memoryFrozenSourceHaarRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R =
    memoryFrozenSourceLifespanRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R := by
  unfold memoryFrozenSourceHaarRoot memoryFrozenSourceLifespanRoot
  apply Finset.sum_congr rfl
  intro ω hω
  rw [memory_frozen_Haar_all_lifespans (physicalSourcePrimeValue BP bigMod)
    (sourceVisitEta q (2*R))
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω) (2*R+1)
    (memory_frozen_source_visits_subset SP smallMod BP J ell m patterns ω)]
  rw [Complex.ofReal_sum, Finset.mul_sum]
  rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceResidueLift -/

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

/-- An absent prime receives an arbitrary fixed anchor zero. A represented
prime receives its actual lifespan birth visit. No extra random draw. -/
def memoryFrozenLifeAnchor {n : ℕ} (l : MemoryLifespanChoice n) : ℕ :=
  match l with | none => 0 | some az => az.1.val

/-- Genuine BIG independent-residue state, constructed from the literal
frozen omega/life profile. Residues for ALL primes translate together;
every active mark is zero by derived lifespan support. -/
def memoryFrozenSourceIndependentLift {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin (N+1)) : MemoryIndependentState SP smallMod BP bigMod J ell :=
  (ω.1 i, fun g =>
    ⟨(fun p => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k i.val :
          ZMod (bigMod g p)) -
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
          (memoryFrozenLifeAnchor (life ⟨g,p⟩)) : ZMod (bigMod g p)),
      (ω.2.1 i g).val),
      (ω.2.1 i g).property, by
        intro j
        have ha : i.val ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns
            ω (⟨g,(ω.2.1 i g).val j⟩ : PhysicalSourcePrime BP) := by
          apply Finset.mem_image.mpr
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j,rfl⟩⟩, rfl⟩
        have hh := memory_schedule_active_anchor (bigMod g ((ω.2.1 i g).val j))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod g ((ω.2.1 i g).val j))))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω
            ⟨g,(ω.2.1 i g).val j⟩) (life ⟨g,(ω.2.1 i g).val j⟩)
          (hs _) i.val ha
        cases he : life ⟨g,(ω.2.1 i g).val j⟩ with
        | none =>
          have hem := hs ⟨g,(ω.2.1 i g).val j⟩
          simp only [he, MemoryFrozenScheduleSupport] at hem
          rw [hem] at ha
          simpa using ha
        | some az =>
          simpa only [he, memoryFrozenLifeAnchor, memoryScheduleResidue] using hh⟩)

theorem memory_frozen_source_lift_marks {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin (N+1)) (g : BG) :
    Green64SmallHaar.marks (bigMod g) (J+ell)
      ((memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i).2 g) = (ω.2.1 i g).val := rfl

/-- All BIG residues, including unmarked and absent primes, obey the exact
source integer translation. This is needed to instantiate the existing
physical E inverses on arbitrary supported terminal profiles. -/
theorem memory_frozen_source_lift_BIG_edge {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin N)
    (ha : memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i) :
    let f := ω.2.2 i
    Green64SmallHaar.groupEdgeAllowedPerm BP bigMod (J+ell)
      (sourceBigShared J ell m (patterns f.1.1))
      (physicalAlternatingSign i.val * k *
        (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ))
      f.2.1 f.2.2.1
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.castSucc).2
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
        ω life k hs i.succ).2 := by
  dsimp only
  intro g
  constructor
  · funext p
    change (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k (i.val+1) : ZMod (bigMod g p)) -
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
        (memoryFrozenLifeAnchor (life ⟨g,p⟩)) : ZMod (bigMod g p)) =
      ((memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k i.val : ZMod (bigMod g p)) -
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
          (memoryFrozenLifeAnchor (life ⟨g,p⟩)) : ZMod (bigMod g p))) + _
    rw [← memory_frozen_source_offset_step SP smallMod BP bigMod J ell m
      patterns ω k i.val i.isLt]
    push_cast
    ring
  · exact ha.2.2.2 g
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceCompatibleLift -/

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
variable {N : ℕ}
variable (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
variable (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)

/-- Derived from the actual nonzero frozen prime product, with no new
regularity or reconstruction assumption. -/
theorem memory_frozen_source_profile_support
    (q : ℝ)
    (hn : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q N)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (N+1) (life gp) : ℝ) ≠ 0) :
    ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp) := by
  intro gp
  exact memory_frozen_nonzero_schedule_support _ _ _ _ _ _
    ((Finset.prod_ne_zero_iff.mp hn) gp (Finset.mem_univ gp))

/-- Literal frozen frame is compatible with the genuine lifted residues.
Nu, repeated auxiliaries, BIG sigma/tau and SMALL sigma/tau stay unchanged.
The SMALL translation condition is extracted from its actual source kernel. -/
theorem memory_frozen_source_lift_frame_compatible
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (hw : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω ≠ 0)
    (i : Fin N) :
    ω.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
      J ell m patterns
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.succ)
      (physicalAlternatingSign i.val) k := by
  have hep : (∏ j : Fin N, memoryFrozenSourceEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω j) ≠ 0 :=
    right_ne_zero_of_mul hw
  have he := (Finset.prod_ne_zero_iff.mp hep) i (Finset.mem_univ i)
  have ha : memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i := by
    by_contra h
    simp [memoryFrozenSourceEdgeWeight, h] at he
  have hsmall :
      Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
        (sourceSmallShared J ell)
        (physicalAlternatingSign i.val*k*
          (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ))
        (ω.2.2 i).2.2.2.1 (ω.2.2 i).2.2.2.2 (ω.1 i.castSucc) (ω.1 i.succ) := by
    simp only [memoryFrozenSourceEdgeWeight, ha, if_true] at he
    have hker := right_ne_zero_of_mul he
    by_contra h
    simp [Green64SmallHaar.groupPermutedKernel, h] at hker
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ha.1, ?_, ?_, ?_, ?_⟩
  · exact ha.2.2.1
  · simpa only [memoryIndependentD, memoryFrozenSourceD,
      memoryFrozenSourceIndependentLift, Green64SmallHaar.marks] using hsmall
  · simpa only [memoryIndependentD, memoryFrozenSourceD,
      memoryFrozenSourceIndependentLift, Green64SmallHaar.marks] using
      memory_frozen_source_lift_BIG_edge SP smallMod BP bigMod J ell m
        patterns ω life k hs i ha
  · simpa only [memoryIndependentD, memoryFrozenSourceD,
      memoryFrozenSourceIndependentLift, Green64SmallHaar.marks] using
      (memory_frozen_source_offset_step SP smallMod BP bigMod J ell m
        patterns ω k i.val i.isLt).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceOperationalPrimeProduct -/

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

/-- Complete prime-side coefficient assembly for the actual frozen profile.
The full dependent root fibre remains a separate unproved reindexing debt. -/
theorem memory_frozen_source_operational_prime_product_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t :
            ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ) *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeOperationalScalar BP bigMod q rho (2*R) Vbig gp.1 gp.2
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t :
            ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp)) =
    (∏ gp : PhysicalSourcePrime BP,
      (1/(Vbig gp.1 : ℂ))^(memoryFrozenPrimeRuns
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (2*R))) *
    (∏ gp : PhysicalSourcePrime BP,
      (memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t :
          ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℂ)) := by
  have hn' := right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod J ell m patterns
    ω life k q (by exact_mod_cast hn')
  unfold physicalSourceBaselineProduct
  push_cast
  rw [← Fintype.prod_sigma (fun gp : PhysicalSourcePrime BP =>
    (physicalSourceBaseline BP bigMod q (2*R) gp.1 gp.2 : ℂ))]
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro gp hgp
  apply memory_frozen_prime_operational_scalar_exact BP bigMod q rho (2*R) Vbig gp.1 gp.2
  · exact hs gp
  · exact ne_of_gt hd.rho_pos
  · exact ne_of_gt (hd.Vbig_pos gp.1)
  · exact ne_of_gt (physicalSourceBaseline_positive_above_visits BP bigMod q (2*R)
      gp.1 gp.2 (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.big_above_visits gp.1 gp.2))
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourcePhysicalStates -/

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
variable {N : ℕ}
variable (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
variable (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)

/-- Full source physical representative, with genuine bounded Fock atom
lists; no new occurrence state or assumed product bijection. -/
def memoryFrozenSourcePhysicalState
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g) (before : Bool) (i : Fin (N+1)) :
    FullPhysicalState SP smallMod BP bigMod (J+ell) cap :=
  (ω.1 i, fun g => ((ω.2.1 i g).val,
    memoryCanonicalPendingFock (bigMod g)
      (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      before i.val (cap g) (hcap g)))

theorem memory_frozen_source_physical_pending
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g) (before : Bool) (i : Fin (N+1))
    (g : BG) :
    Green64Fock.fockToList
      (((memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap before i).2 g).2) =
    memoryCanonicalPendingList (bigMod g)
      (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) before i.val := by
  exact memory_canonical_Fock_list_exact (bigMod g)
    (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun p => life ⟨g,p⟩)
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    before i.val (cap g) (hcap g)

theorem memory_frozen_source_visits_at (i : Fin (N+1)) (g : BG) (p : BP g) :
    i.val ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩ ↔
      ∃ j, (ω.2.1 i g).val j = p := by
  constructor
  · intro ht
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp ht
    have hh : t = i := Fin.ext he
    subst t
    exact (Finset.mem_filter.mp ht).2
  · intro ht
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,rfl⟩

/-- Both actual Fock boundary vacua, for every finite lifespan assignment. -/
theorem memory_frozen_source_physical_vacua
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g) :
    (∀ g, Green64Fock.fockMultiset
      (((memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap true ⟨0,Nat.succ_pos N⟩).2 g).2) = 0) ∧
    (∀ g, Green64Fock.fockMultiset
      (((memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
        ω life k hcap false ⟨N,Nat.lt_succ_self N⟩).2 g).2) = 0) := by
  constructor
  all_goals
    intro g
    dsimp only [memoryFrozenSourcePhysicalState]
    rw [memory_canonical_Fock_multiset_exact]
  · rw [(memory_canonical_pending_vacua (bigMod g)
      (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)).1]
    rfl
  · rw [(memory_canonical_pending_vacua (bigMod g)
      (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)).2]
    rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceActualELift -/

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

/-- Exact reverse E lift on an arbitrary genuine physical Fock representative
of a supported true frozen profile. The original frame is preserved literally,
and the original scalar is evaluated using the checked local inverse. -/
theorem memory_frozen_source_actual_E_lift
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
    ∃ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x,
      (⟨x,z⟩ : Σ xx : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns xx) ∈
        physicalOrientedEIndexedLegalFibre SP smallMod BP bigMod J ell m cap patterns
          (physicalAlternatingSign i.val) k
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
          (memoryBornBeforeValues BP bigMod L (i.val+1)) ∧
      memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns x z = ω.2.2 i ∧
      sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x
        (physicalAlternatingSign i.val) k z =
        physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
            ω life k hd.cap_saturated true i.succ) ∧
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
        zeta theta (physicalAlternatingSign i.val) k x z =
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
  let f := ω.2.2 i
  have hf := memory_frozen_source_lift_frame_compatible SP smallMod BP bigMod
    J ell m patterns ω life k hs q Vsmall Vbig Knu zeta theta hw i
  have hsmall : x.1 = ix.1 := congrArg Prod.fst hx
  have hactive : ∀ g, (x.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) :=
    fun g => congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).1) hx
  have hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset false i.val) := by
    intro g
    have hm := congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).2) hx
    have hh := Multiset.coe_eq_coe.mp hm
    exact hh.trans (List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod
      BP bigMod J ell m cap patterns ω life k hd.cap_saturated false i.castSucc g))
  have hA0 : ∀ g p, i.val ∈ A g p ↔
      ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns
      ω i.castSucc g p
  have hA1 : ∀ g p, i.val+1 ∈ A g p ↔
      ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns
      ω i.succ g p
  let z := memoryPrimitiveEFrameChoice SP smallMod BP bigMod J ell m cap patterns
    A L offset i.val (fun g p => hs ⟨g,p⟩) x hOld iy f
  have hz := memory_source_primitive_E_canonical_frame_mem SP smallMod BP bigMod
    J ell m cap patterns A L offset i.val (fun g p => hs ⟨g,p⟩)
    q rho Vsmall Vbig k R hd ix iy x hsmall hactive hOld hA0 hA1
    (physicalAlternatingSign i.val) f hf
  have hzs := (Finset.mem_filter.mp hz).2
  refine ⟨z,hzs.1,hzs.2.1,?_,?_⟩
  · rw [hzs.2.2]
    unfold memoryPrimitiveECanonicalOutput physicalFockProjection
    dsimp only [memoryFrozenSourcePhysicalState, iy, memoryFrozenSourceIndependentLift, Green64SmallHaar.marks]
    congr 1
    funext g
    congr 1
    exact (memory_canonical_Fock_multiset_exact (bigMod g) (A g) (L g) offset
      true (i.val+1) (cap g) (hd.cap_saturated g)).symm
  · exact memory_source_primitive_E_frame_coefficient_exact SP smallMod BP bigMod
      J ell m cap patterns A L offset i.val (fun g p => hs ⟨g,p⟩)
      ix iy x hsmall hactive hOld hA0 hA1 q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k f
      (Finset.mem_filter.mp hf).2.2.2.2.2
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceGSeenUpdate -/

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
variable (J ell : ℕ) (cap : BG → ℕ)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

/-- The actual ordered ghost batch is precisely the scheduled ghost-birth
set as numerical values. No auxiliary or OLD transfer is counted as birth. -/
theorem memory_primitive_G_fresh_values_mem
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) (v : ℕ) :
    v ∈ (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x
      (memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i
        hs x hOld hcap e)).toFinset ↔
    ∃ gp : Sigma BP, memoryScheduleGhostBirth (A gp.1 gp.2) (life gp.1 gp.2) i ∧
      bigMod gp.1 gp.2 = v := by
  rw [memory_primitive_G_fresh_list_exact]
  simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_toList,
    Finset.mem_univ, true_and, List.mem_ofFn]
  constructor
  · rintro ⟨g,j,hj⟩
    exact ⟨⟨g,(e g j).val⟩,(Finset.mem_filter.mp (e g j).property).2,hj⟩
  · rintro ⟨⟨g,p⟩,hp,hv⟩
    let p' : ↥(memoryGhostBirthSet (A g) (life g) i) :=
      ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
    refine ⟨g,(e g).symm p',?_⟩
    simpa only [Equiv.apply_symm_apply] using hv

/-- Exact chronological register between the composed G and E operations,
derived on the original ordered witness carrier. -/
theorem memory_primitive_G_seen_update
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) :
    memorySeenBeforeGValues BP bigMod A life i ∪
      (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x
        (memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i
          hs x hOld hcap e)).toFinset =
    memoryBornBeforeValues BP bigMod life (i+1) := by
  ext v
  rw [Finset.mem_union, memory_primitive_G_fresh_values_mem SP smallMod BP bigMod
    J ell cap A life offset i hs x hOld hcap e]
  simp only [memorySeenBeforeGValues, memoryBornBeforeValues, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨gp,hgp,hv⟩ | ⟨gp,hgp,hv⟩)
    · refine ⟨gp,?_,hv⟩
      cases hl : life gp.1 gp.2 with
      | none => simp [hl] at hgp
      | some az => simp only [hl] at hgp ⊢; omega
    · refine ⟨gp,?_,hv⟩
      cases hl : life gp.1 gp.2 with
      | none => simp [hl,memoryScheduleGhostBirth] at hgp
      | some az =>
        simp only [hl,memoryScheduleGhostBirth] at hgp
        simp only [hl]
        omega
  · rintro ⟨gp,hgp,hv⟩
    cases hl : life gp.1 gp.2 with
    | none => simp [hl] at hgp
    | some az =>
      simp only [hl] at hgp
      by_cases hb : az.1.val < i
      · exact Or.inl ⟨gp,by simp only [hl]; exact Or.inl hb,hv⟩
      · have he : az.1.val = i := by omega
        by_cases ha : i ∈ A gp.1 gp.2
        · exact Or.inl ⟨gp,by simp only [hl]; exact Or.inr ⟨he,ha⟩,hv⟩
        · exact Or.inr ⟨gp,by simp only [memoryScheduleGhostBirth,hl]; exact ⟨he,ha⟩,hv⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceESeenUpdate -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]

theorem memory_E_fresh_slot_iff
    (M : ℕ) (modulus : P → ℕ) (A : P → Finset ℕ) {n : ℕ}
    (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (source target : Fin M → P) (sigma tau : Equiv.Perm (Fin M))
    (hA0 : ∀ p, i ∈ A p ↔ ∃ j, source j = p)
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (shared : Finset (Fin M))
    (hshared : ∀ j ∈ shared, source (sigma j) = target (tau j))
    (hcont : ∀ j l, source (sigma j) = target (tau l) → j ∈ shared ∧ l = j)
    (j : Fin M) :
    j ∈ orientedFresh M shared (memoryEPromoteSlots M A life i target tau) ↔
      memoryScheduleFresh (A (target (tau j))) (life (target (tau j))) i := by
  constructor
  · exact memory_E_fresh_slot_birth_exact M A life i modulus offset hs source target
      sigma tau hA0 hA1 shared hcont j
  · intro hf
    have hn : j ∉ shared := by
      intro hj
      have ha := (hA0 _).mpr ⟨sigma j,hshared j hj⟩
      cases hl : life (target (tau j)) with
      | none => simp [hl,memoryScheduleFresh] at hf
      | some az =>
        simp only [hl,memoryScheduleFresh] at hf
        exact hf.1 ha
    have hp : j ∉ memoryEPromoteSlots M A life i target tau := by
      intro hj
      have hh := (Finset.mem_filter.mp hj).2
      cases hl : life (target (tau j)) with
      | none => simp [hl,memoryScheduleFresh] at hf
      | some az =>
        simp only [hl,memoryScheduleFresh] at hf
        simp only [hl,memorySchedulePromote] at hh
        omega
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩,hp⟩

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

theorem memory_primitive_E_fresh_values_mem
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j,
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (hshared : ∀ g j, j ∈ sourceBigShared J ell m (patterns nu) g →
      (x.2 g).1 (bs g j) =
        Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j))
    (hcont : ∀ g j l, (x.2 g).1 (bs g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g l) →
      j ∈ sourceBigShared J ell m (patterns nu) g ∧ l = j)
    (v : ℕ) :
    v ∈ (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns
      (memoryPrimitiveESourceChoice SP smallMod BP bigMod J ell m cap patterns
        A life offset i hs x hOld iy nu aux bs bt ss st)).toFinset ↔
    ∃ gp : Sigma BP, memoryScheduleFresh (A gp.1 gp.2) (life gp.1 gp.2) i ∧
      bigMod gp.1 gp.2 = v := by
  unfold orientedEFreshBirths
  dsimp only [memoryPrimitiveESourceChoice, memoryPrimitiveEChoice]
  simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_toList,
    Finset.mem_univ, true_and, List.mem_map]
  constructor
  · rintro ⟨g,j,hj,hv⟩
    exact ⟨⟨g,Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j)⟩,
      (memory_E_fresh_slot_iff (J+ell) (bigMod g) (A g) (life g) offset i (hs g)
        (x.2 g).1 _ (bs g) (bt g) (hA0 g) (hA1 g) _ (hshared g) (hcont g) j).mp hj,hv⟩
  · rintro ⟨⟨g,p⟩,hf,hv⟩
    have ha : i+1 ∈ A g p := by
      cases hl : life g p with
      | none => simp [hl,memoryScheduleFresh] at hf
      | some az =>
        simp only [hl,memoryScheduleFresh] at hf
        exact hf.2.1
    obtain ⟨j,hj⟩ := (hA1 g p).mp ha
    refine ⟨g,(bt g).symm j,?_,?_⟩
    · apply (memory_E_fresh_slot_iff (J+ell) (bigMod g) (A g) (life g) offset i (hs g)
        (x.2 g).1 _ (bs g) (bt g) (hA0 g) (hA1 g) _ (hshared g) (hcont g) _).mpr
      simpa only [Equiv.apply_symm_apply,hj] using hf
    · simpa only [Equiv.apply_symm_apply,hj] using hv

theorem memory_primitive_E_seen_update
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j,
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (hshared : ∀ g j, j ∈ sourceBigShared J ell m (patterns nu) g →
      (x.2 g).1 (bs g j) =
        Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j))
    (hcont : ∀ g j l, (x.2 g).1 (bs g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g l) →
      j ∈ sourceBigShared J ell m (patterns nu) g ∧ l = j) :
    memoryBornBeforeValues BP bigMod life (i+1) ∪
      (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns
        (memoryPrimitiveESourceChoice SP smallMod BP bigMod J ell m cap patterns
          A life offset i hs x hOld iy nu aux bs bt ss st)).toFinset =
    memorySeenBeforeGValues BP bigMod A life (i+1) := by
  ext v
  rw [Finset.mem_union, memory_primitive_E_fresh_values_mem SP smallMod BP bigMod
    J ell m cap patterns A life offset i hs x hOld iy hA0 hA1 nu aux bs bt ss st
    hshared hcont]
  simp only [memorySeenBeforeGValues, memoryBornBeforeValues, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨gp,hgp,hv⟩ | ⟨gp,hgp,hv⟩)
    · refine ⟨gp,?_,hv⟩
      cases hl : life gp.1 gp.2 with
      | none => simp [hl] at hgp
      | some az => simp only [hl] at hgp ⊢; exact Or.inl hgp
    · refine ⟨gp,?_,hv⟩
      cases hl : life gp.1 gp.2 with
      | none => simp [hl,memoryScheduleFresh] at hgp
      | some az =>
        simp only [hl,memoryScheduleFresh] at hgp
        simp only [hl]
        exact Or.inr ⟨hgp.2.2,hgp.2.1⟩
  · rintro ⟨gp,hgp,hv⟩
    cases hl : life gp.1 gp.2 with
    | none => simp [hl] at hgp
    | some az =>
      simp only [hl] at hgp
      rcases hgp with hb | ⟨hb,ha⟩
      · exact Or.inl ⟨gp,by simpa only [hl],hv⟩
      · have hn : i ∉ A gp.1 gp.2 := by
          intro hi
          have hh := hs gp.1 gp.2
          rw [hl] at hh
          have hlo := (hh.2.1 i hi).1
          omega
        exact Or.inr ⟨gp,by simpa only [memoryScheduleFresh,hl] using
          (show i ∉ A gp.1 gp.2 ∧ i+1 ∈ A gp.1 gp.2 ∧ az.1.val = i+1 from
            ⟨hn,ha,hb⟩),hv⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceActualGEPair -/

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
theorem memory_frozen_source_actual_GE_pair
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
        memorySeenBeforeGValues BP bigMod A L (i.val+1) := by
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
  exact ⟨⟨ab,hab⟩,hgp,hframe,hout,by
    change (memorySeenBeforeGValues BP bigMod A L i.val ∪
      (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x0 c).toFinset) ∪
        (orientedEFreshBirths SP smallMod BP bigMod J ell m cap patterns z).toFinset = _
    rw [hgs]
    exact hes⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryFrozenSourceIndexedReconstruction -/

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
variable {N : ℕ}
variable (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
variable (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1)) (k : ℤ)
variable (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)

/-- Auditable reconstruction certificate on the ORIGINAL recursively indexed
trace. It records all frozen frames, post-G canonical atom multisets,
next canonical physical orbits and chronological numerical seen registers.
It is not a mass normalization premise or an augmented-history bijection. -/
def memoryFrozenSourceIndexedTraceFits :
    (remaining start : ℕ) →
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) →
    (seen : Finset ℕ) →
    physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
      1 k remaining start y seen → Prop
  | 0, start, _, _, a =>
      start = N ∧
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.val.2.1 =
        physicalFockProjection SP smallMod BP bigMod (J+ell) cap
          (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
            ω life k hcap false ⟨N,Nat.lt_succ_self N⟩)
  | r+1, start, _, seen, ⟨ab,tail⟩ =>
      ∃ hi : start < N,
        physicalFockProjection SP smallMod BP bigMod (J+ell) cap ab.val.1.2.1 =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap
            (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
              ω life k hcap false ⟨start,Nat.lt_succ_of_lt hi⟩) ∧
        memoryPrimitiveEFrameOf SP smallMod BP bigMod J ell m cap patterns
          ab.val.2.1 ab.val.2.2 = ω.2.2 ⟨start,hi⟩ ∧
        physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
          (physicalAlternatingSign start) k ab.val =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap
            (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
              ω life k hcap true ⟨start+1,Nat.succ_lt_succ hi⟩) ∧
        physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
          seen ab.val =
          memorySeenBeforeGValues BP bigMod
            (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
            (fun g p => life ⟨g,p⟩) (start+1) ∧
        memoryFrozenSourceIndexedTraceFits r (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
            (physicalAlternatingSign start) k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
            seen ab.val) tail

/-- Global existence of a source-faithful physical trace, not evaluation or
exhaustive summation of its fibre. All original dependent indices remain. -/
theorem memory_frozen_source_indexed_reconstruction
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
        ω life k hd.cap_saturated remaining start _ _ t := by
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
    refine ⟨⟨⟨x,yg,c⟩,hg⟩,rfl,?_⟩
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
  | succ r ih =>
    have hi : start < 2*R := by omega
    dsimp only
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let e := fun g => (Fintype.equivFinOfCardEq
      (Fintype.card_coe (memoryGhostBirthSet (A g) (L g) start))).symm
    obtain ⟨ab,hG,hframe,hout,hseen⟩ := memory_frozen_source_actual_GE_pair
      SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd ω life hs hw ⟨start,hi⟩ e
    have hn : start+1+r = 2*R := by omega
    obtain ⟨t,ht⟩ := ih (start+1) hn
    have hx : ∃ t' : physicalOrientedIndexedTrace SP smallMod BP bigMod J ell m cap patterns
        1 k r (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod J ell m cap patterns
          (physicalAlternatingSign start) k ab.val)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod J ell m cap patterns
          (memorySeenBeforeGValues BP bigMod A L start) ab.val),
      memoryFrozenSourceIndexedTraceFits SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated r (start+1) _ _ t' := by
      rw [hout,hseen]
      exact ⟨t,ht⟩
    obtain ⟨t',ht'⟩ := hx
    exact ⟨⟨ab,t'⟩,hi,hG,hframe,hout,hseen,ht'⟩
end Green64FullPhysicalE

end

end

