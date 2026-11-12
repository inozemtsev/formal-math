module

public import Green64.Library.Weights.AuxiliaryLift

@[expose] public section

/-!
# Correlation / PhysicalSlotLift

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualPhysicalSlotLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Restrict an all-P full marked tuple to its literal BIG groups.
Only the necessary equal-count cast is used, with each index retained. -/
def b604ActualBigMarkRestriction434
    (r : ℕ) (L : ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (a : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (b604ActualLiftedPattern434 r L m nu) g) → ℕ) :
    ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ :=
  fun g i => a (sourceNativeOriginalBigToAll434 r L g)
    (Fin.cast (b604_actual_free_count_big434 r L J ell m hmJ nu g).symm i)

private theorem free_slot_value_eq (J ell : ℕ) (S T : Finset (Fin J))
    (h : S=T) (i : Fin (J+ell))
    (hs : i∉sourceOriginalSharedSlots434 J ell S)
    (ht : i∉sourceOriginalSharedSlots434 J ell T) :
    ((sourceOriginalFreeSlotEquiv434 J ell S).symm ⟨i,hs⟩).val =
      ((sourceOriginalFreeSlotEquiv434 J ell T).symm ⟨i,ht⟩).val := by
  cases h
  rfl

/-- The same original physical first-J probe has the same free index
under the exact count transport. No arbitrary enumeration is substituted. -/
theorem b604_actual_physical_free_index_lift434
    (r : ℕ) (L : ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (g : sourceNativeOriginalBigType434 r L) (j : Fin m)
    (hj : (g,j)∈nu.1 ∨ (g,j)∈nu.2)
    (hj' : (sourceNativeOriginalBigToAll434 r L g,j)∈(b604ActualLiftedPattern434 r L m nu).1 ∨
      (sourceNativeOriginalBigToAll434 r L g,j)∈(b604ActualLiftedPattern434 r L m nu).2) :
    Fin.cast (b604_actual_free_count_big434 r L J ell m hmJ nu g).symm
      (sourceOriginalProbeFreeIndex434 J ell m hmJ nu g j hj) =
    sourceOriginalProbeFreeIndex434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      (sourceNativeOriginalBigToAll434 r L g) j hj' := by
  apply Fin.ext
  simp only [Fin.val_cast,sourceOriginalProbeFreeIndex434,sourceOriginalProbeFreeMarkEquiv434]
  exact free_slot_value_eq J ell _ _
    (b604_actual_freed_slots_big434 r L J m hmJ nu g).symm _ _ _

/-- Both actual endpoint products use exactly their original physical slots. -/
theorem b604_actual_physical_probe_products_lift434
    (r : ℕ) (L : ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (a b : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (b604ActualLiftedPattern434 r L m nu) g) → ℕ) :
    sourceOriginalProbeFreeTargetX434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu) b =
      sourceOriginalProbeFreeTargetX434 J ell m hmJ nu
        (b604ActualBigMarkRestriction434 r L J ell m hmJ nu b) ∧
    sourceOriginalProbeFreeSourceX434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu) a =
      sourceOriginalProbeFreeSourceX434 J ell m hmJ nu
        (b604ActualBigMarkRestriction434 r L J ell m hmJ nu a) := by
  constructor
  · symm
    apply Fintype.prod_equiv (b604ActualProbeSubtypeEquiv434 r L m nu.1)
    intro z
    change b (sourceNativeOriginalBigToAll434 r L z.val.1) _ =
      b (sourceNativeOriginalBigToAll434 r L z.val.1) _
    congr 1
    exact b604_actual_physical_free_index_lift434 r L J ell m hmJ nu z.val.1 z.val.2 _ _
  · symm
    apply Fintype.prod_equiv (b604ActualProbeSubtypeEquiv434 r L m nu.2)
    intro z
    change a (sourceNativeOriginalBigToAll434 r L z.val.1) _ =
      a (sourceNativeOriginalBigToAll434 r L z.val.1) _
    congr 1
    exact b604_actual_physical_free_index_lift434 r L J ell m hmJ nu z.val.1 z.val.2 _ _

/-- The full original auxiliary ban is unchanged: it still checks every
free mark in the selected BIG group, including all hidden coordinates. -/
theorem b604_actual_full_ban_lift434
    (r : ℕ) (L : ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (b604ActualLiftedPattern434 r L m nu) g) → ℕ) :
    sourceB574FreeAuxBan434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      (b604ActualLiftedAux434 r L m nu aux) a b ↔
    sourceB574FreeAuxBan434 J ell m hmJ nu aux
      (b604ActualBigMarkRestriction434 r L J ell m hmJ nu a)
      (b604ActualBigMarkRestriction434 r L J ell m hmJ nu b) := by
  constructor
  · intro h z i
    have hz := h (b604ActualAuxEquiv434 r L m nu z)
    have hz' : ∀i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
        (b604ActualLiftedPattern434 r L m nu)
        (sourceNativeOriginalBigToAll434 r L (sourceOriginalProbeAuxGroup434 m nu z))),
        aux z ≠ a (sourceNativeOriginalBigToAll434 r L (sourceOriginalProbeAuxGroup434 m nu z)) i ∧
        aux z ≠ b (sourceNativeOriginalBigToAll434 r L (sourceOriginalProbeAuxGroup434 m nu z)) i := by
      have hgroup := congrArg
        (fun g => ∀i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
          (b604ActualLiftedPattern434 r L m nu) g),aux z ≠ a g i ∧ aux z ≠ b g i)
        (b604_actual_aux_group_lift434 r L m nu z)
      apply Eq.mp hgroup
      simpa only [b604_actual_lifted_aux_apply434] using hz
    exact hz' (Fin.cast (b604_actual_free_count_big434 r L J ell m hmJ nu _).symm i)
  · intro h z
    obtain ⟨z,rfl⟩ := (b604ActualAuxEquiv434 r L m nu).surjective z
    have hz' : ∀i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
        (b604ActualLiftedPattern434 r L m nu)
        (sourceNativeOriginalBigToAll434 r L (sourceOriginalProbeAuxGroup434 m nu z))),
        aux z ≠ a (sourceNativeOriginalBigToAll434 r L (sourceOriginalProbeAuxGroup434 m nu z)) i ∧
        aux z ≠ b (sourceNativeOriginalBigToAll434 r L (sourceOriginalProbeAuxGroup434 m nu z)) i := by
      intro i
      have hi := h z (Fin.cast (b604_actual_free_count_big434 r L J ell m hmJ nu _) i)
      have hc : Fin.cast (b604_actual_free_count_big434 r L J ell m hmJ nu _).symm
          (Fin.cast (b604_actual_free_count_big434 r L J ell m hmJ nu _) i)=i := Fin.ext rfl
      simpa only [b604ActualBigMarkRestriction434,hc] using hi
    have hgroup := congrArg
      (fun g => ∀i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
        (b604ActualLiftedPattern434 r L m nu) g),aux z ≠ a g i ∧ aux z ≠ b g i)
      (b604_actual_aux_group_lift434 r L m nu z)
    have hh := Eq.mpr hgroup hz'
    simpa only [b604_actual_lifted_aux_apply434] using hh
end Green64Analytic.SourceBlockSieve

end

end

