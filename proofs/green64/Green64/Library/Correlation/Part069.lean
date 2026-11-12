module

public import Green64.Library.Correlation.PhysicalSlotLift
public import Green64.Library.Correlation.Part034
public import Green64.Library.Weights.BigPatternLift

@[expose] public section

/-!
# Correlation / Part069

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualCanonicalKernelLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Both true original independent-prime cell probabilities survive
the actual BIG probe lift, with every labelled coordinate and V atom. -/
theorem b604_actual_probe_cell_lift434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (P : sourceOriginalPAllGroupType r L → Finset ℕ)
    (V : sourceOriginalPAllGroupType r L → ℝ) (h : ℝ) :
    sourceOriginalProbeCellA434 m P V (b604ActualLiftedPattern434 r L m nu) h =
      sourceOriginalProbeCellA434 m (fun g=>P (sourceNativeOriginalBigToAll434 r L g))
        (fun g=>V (sourceNativeOriginalBigToAll434 r L g)) nu h ∧
    sourceOriginalProbeCellB434 m P V (b604ActualLiftedPattern434 r L m nu) h =
      sourceOriginalProbeCellB434 m (fun g=>P (sourceNativeOriginalBigToAll434 r L g))
        (fun g=>V (sourceNativeOriginalBigToAll434 r L g)) nu h := by
  constructor
  · funext j
    exact (b607_actual_cell_probability_reindex434 (b604ActualProbeSubtypeEquiv434 r L m nu.1)
      (fun z=>P z.val.1) (fun z=>sourcePrimeSharedAtom434 (V z.val.1)) h j).symm
  · funext j
    exact (b607_actual_cell_probability_reindex434 (b604ActualProbeSubtypeEquiv434 r L m nu.2)
      (fun z=>P z.val.1) (fun z=>sourcePrimeSharedAtom434 (V z.val.1)) h j).symm

/-- The precise finite active log-cell families are identical, without
changing xi, truncating conductors or enlarging the candidate set. -/
theorem b604_actual_active_cells_lift434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (P : sourceOriginalPAllGroupType r L → Finset ℕ)
    (V : sourceOriginalPAllGroupType r L → ℝ) (h xi : ℝ) :
    sourceOriginalProbeActiveCellsA434 m P V (b604ActualLiftedPattern434 r L m nu) h xi =
      sourceOriginalProbeActiveCellsA434 m (fun g=>P (sourceNativeOriginalBigToAll434 r L g))
        (fun g=>V (sourceNativeOriginalBigToAll434 r L g)) nu h xi ∧
    sourceOriginalProbeActiveCellsB434 m P V (b604ActualLiftedPattern434 r L m nu) h xi =
      sourceOriginalProbeActiveCellsB434 m (fun g=>P (sourceNativeOriginalBigToAll434 r L g))
        (fun g=>V (sourceNativeOriginalBigToAll434 r L g)) nu h xi := by
  constructor
  · exact (b607_finite_active_log_cells_reindex434 (b604ActualProbeSubtypeEquiv434 r L m nu.1)
      (fun z=>P z.val.1) (fun z=>sourcePrimeSharedAtom434 (V z.val.1)) h xi).symm
  · exact (b607_finite_active_log_cells_reindex434 (b604ActualProbeSubtypeEquiv434 r L m nu.2)
      (fun z=>P z.val.1) (fun z=>sourcePrimeSharedAtom434 (V z.val.1)) h xi).symm

/-- Literal signed canonical Knu equality at the exact physical marks.
Both independent global columns and their actual masses are unchanged. -/
theorem b604_actual_canonical_Knu_lift434
    (r : ℕ) (L : ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (Q : ℕ) (hA hB xi : ℝ)
    (P : sourceOriginalPAllGroupType r L → Finset ℕ)
    (V : sourceOriginalPAllGroupType r L → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (b604ActualLiftedPattern434 r L m nu) g) → ℕ) :
    sourceOriginalProbeCanonicalKnu434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      Q hA hB xi P V (b604ActualLiftedAux434 r L m nu aux) a b =
    sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi
      (fun g=>P (sourceNativeOriginalBigToAll434 r L g))
      (fun g=>V (sourceNativeOriginalBigToAll434 r L g)) aux
      (b604ActualBigMarkRestriction434 r L J ell m hmJ nu a)
      (b604ActualBigMarkRestriction434 r L J ell m hmJ nu b) := by
  unfold sourceOriginalProbeCanonicalKnu434 sourceOriginalProbeConcreteKnu434
    sourceAuxiliaryOriginalComparisonKnu434
  rw [(b604_actual_probe_cell_lift434 r L m nu P V hA).1,
    (b604_actual_probe_cell_lift434 r L m nu P V hB).2,
    (b604_actual_active_cells_lift434 r L m nu P V hA xi).1,
    (b604_actual_active_cells_lift434 r L m nu P V hB xi).2,
    (b604_actual_aux_products_lift434 r L m nu aux).1,
    (b604_actual_aux_products_lift434 r L m nu aux).2,
    (b604_actual_physical_probe_products_lift434 r L J ell m hmJ nu a b).1,
    (b604_actual_physical_probe_products_lift434 r L J ell m hmJ nu a b).2,
    (b604_actual_lifted_pattern_cards434 r L m nu).1,
    (b604_actual_lifted_pattern_cards434 r L m nu).2]

/-- The FULL auxiliary-banned canonical kernel is exactly the original
BIG kernel after restriction. Hidden auxiliary collisions remain in the
same predicate; no clean-endpoint restriction is introduced. -/
theorem b604_actual_full_ban_Knu_lift434
    (r : ℕ) (L : ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (Q : ℕ) (hA hB xi : ℝ)
    (P : sourceOriginalPAllGroupType r L → Finset ℕ)
    (V : sourceOriginalPAllGroupType r L → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (b604ActualLiftedPattern434 r L m nu) g) → ℕ) :
    sourceB574CanonicalFreeKernel434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      Q hA hB xi P V (b604ActualLiftedAux434 r L m nu aux) a b =
    sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi
      (fun g=>P (sourceNativeOriginalBigToAll434 r L g))
      (fun g=>V (sourceNativeOriginalBigToAll434 r L g)) aux
      (b604ActualBigMarkRestriction434 r L J ell m hmJ nu a)
      (b604ActualBigMarkRestriction434 r L J ell m hmJ nu b) := by
  unfold sourceB574CanonicalFreeKernel434
  rw [b604_actual_full_ban_lift434,b604_actual_canonical_Knu_lift434]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualCompleteCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The actual B578 SMALL/BIG sum carrier has exactly the original full
P union, by application of the existing complete-family equivalence. -/
theorem b604_actual_B578_group_union434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) (hL : 1<L) :
    Finset.univ.biUnion (sourceB578ActualAllGroups434 L hS)=sourceNativeOriginalG434 6 L := by
  unfold sourceB578ActualAllGroups434 sourceNativeOriginalG434
  rw [source_native_original_complete_family434 6 L hS hL]
  exact source_native_original_union_reindex434
    (sourceNativeOriginalCompleteEquiv434 6 L hS hL) (sourceOriginalPAllActualBands 6 L)

/-- The literal ordinary Q core uses the same P-stripped integer after
the actual complete-family transport. Every coefficient is retained. -/
theorem b604_actual_B578_prime_core434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) (hL : 1<L)
    (F : PrimeSlotCore) (n : ℕ) :
    primeSlotCoreValue (sourceB578ActualAllGroups434 L hS) F n =
      primeSlotCoreValue (sourceOriginalPAllActualBands 6 L) F n := by
  unfold primeSlotCoreValue
  rw [b604_actual_B578_group_union434 L hS hL]
  rfl

/-- Actual all-P 1/p masses and the inherited BIG reciprocal masses
are exactly the same numbers, with no new normalizing constants. -/
theorem b604_actual_BIG_mass_pullback434 (r : ℕ) (L : ℝ) :
    (fun g=>sourceNativeOriginalAllPMass434 r L (sourceNativeOriginalBigToAll434 r L g)) =
      sourceNativeOriginalVbig434 r L := by
  funext g
  simp only [sourceNativeOriginalAllPMass434,sourceNativeOriginalVbig434,
    sourceNativeOriginalTb434,one_div]
end Green64Analytic.SourceBlockSieve

end

end

