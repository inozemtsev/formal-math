module

public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.Part042

@[expose] public section

/-!
# Weights / ObservedSlots

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualObservedSlots -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

variable {G : Type} [DecidableEq G]

/-- The two selected ORIGINAL blocks are disjoint as labelled probe sets,
derived from their actual disjoint group blocks and pattern membership. -/
theorem b598_actual_probe_blocks_disjoint434
    (A B : Finset G) (hAB : Disjoint A B) (m : ℕ)
    (nu : SourceOriginalProbePattern434 G m)
    (hnu : nu∈sourceOriginalTwoBlockProbePatterns434 A B m) :
    Disjoint nu.1 nu.2 := by
  have h := (source_original_two_block_probe_pattern_mem434 A B m nu.1 nu.2).mp hnu
  apply Finset.disjoint_left.mpr
  intro z hA hB
  have ha : z.1∈A := (Finset.mem_product.mp (h.2.1 hA)).1
  have hb : z.1∈B := (Finset.mem_product.mp (h.2.2.2 hB)).1
  exact Finset.disjoint_left.mp hAB ha hb

/-- Exact count of the true original free slots: all ell base slots plus
both selected probe blocks, with no discarded opposite-block marks. -/
theorem b598_original_free_mark_count434
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m) (hnu : Disjoint nu.1 nu.2) (g : G) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g =
      ell+sourceOriginalProbeChosenGroupCount434 m nu.1 g+
        sourceOriginalProbeChosenGroupCount434 m nu.2 g := by
  let SA := (Finset.univ : Finset (Fin m)).filter (fun i => (g,i)∈nu.1)
  let SB := (Finset.univ : Finset (Fin m)).filter (fun i => (g,i)∈nu.2)
  have hdisj : Disjoint SA SB := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hnu (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hA : SA.card=sourceOriginalProbeChosenGroupCount434 m nu.1 g := by
    simp [SA,sourceOriginalProbeChosenGroupCount434,Fintype.card_subtype]
  have hB : SB.card=sourceOriginalProbeChosenGroupCount434 m nu.2 g := by
    simp [SB,sourceOriginalProbeChosenGroupCount434,Fintype.card_subtype]
  have hu : (Finset.univ.filter (fun i : Fin m => (g,i)∈nu.1 ∨ (g,i)∈nu.2))=SA∪SB := by
    ext i
    simp [SA,SB]
  have hinj : Function.Injective (fun i : Fin m => i.castLE hmJ) := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin J => z.val) h)
  unfold sourceOriginalProbeFreeMarkCount434 sourceOriginalProbeFreedSlots434
  rw [Finset.card_image_of_injective _ hinj,hu,Finset.card_union_of_disjoint hdisj,hA,hB]
  omega

/-- The exact original free count is at most ell+m in every group.
This follows from its selected-label carrier, not a replacement tmax. -/
theorem b598_original_chosen_count_sum_le434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (hnu : Disjoint nu.1 nu.2) (g : G) :
    sourceOriginalProbeChosenGroupCount434 m nu.1 g+
      sourceOriginalProbeChosenGroupCount434 m nu.2 g ≤ m := by
  let SA := (Finset.univ : Finset (Fin m)).filter (fun i => (g,i)∈nu.1)
  let SB := (Finset.univ : Finset (Fin m)).filter (fun i => (g,i)∈nu.2)
  have hdisj : Disjoint SA SB := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hnu (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hc : (SA∪SB).card ≤ m := by simpa using (SA∪SB).card_le_univ
  rw [Finset.card_union_of_disjoint hdisj] at hc
  simpa [SA,SB,sourceOriginalProbeChosenGroupCount434,Fintype.card_subtype] using hc

/-- The original chosen labelled position in group g, enumerated by the
canonical finite equivalence already used in the native probe carrier. -/
def b598ProbeGroupIndex434 (m : ℕ) (A : Finset (G×Fin m)) (g : G)
    (i : Fin (sourceOriginalProbeChosenGroupCount434 m A g)) : Fin m :=
  ((Fintype.equivFin {j : Fin m // (g,j)∈A}).symm i).val

theorem b598_probe_group_index_mem434
    (m : ℕ) (A : Finset (G×Fin m)) (g : G)
    (i : Fin (sourceOriginalProbeChosenGroupCount434 m A g)) :
    (g,b598ProbeGroupIndex434 m A g i)∈A :=
  ((Fintype.equivFin {j : Fin m // (g,j)∈A}).symm i).property

private theorem b598_probe_group_index_injective
    (m : ℕ) (A : Finset (G×Fin m)) (g : G) :
    Function.Injective (b598ProbeGroupIndex434 m A g) := by
  intro i j h
  exact (Fintype.equivFin {j : Fin m // (g,j)∈A}).symm.injective (Subtype.ext h)

/-- Literal target A selected position inside the original free array. -/
def b598OriginalObservedASlot434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m) (g : G)
    (i : Fin (sourceOriginalProbeChosenGroupCount434 m nu.1 g)) :
    Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) :=
  sourceOriginalProbeFreeIndex434 J ell m hmJ nu g
    (b598ProbeGroupIndex434 m nu.1 g i) (Or.inl (b598_probe_group_index_mem434 m nu.1 g i))

/-- Literal source B selected position inside the original free array. -/
def b598OriginalObservedBSlot434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m) (g : G)
    (i : Fin (sourceOriginalProbeChosenGroupCount434 m nu.2 g)) :
    Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) :=
  sourceOriginalProbeFreeIndex434 J ell m hmJ nu g
    (b598ProbeGroupIndex434 m nu.2 g i) (Or.inr (b598_probe_group_index_mem434 m nu.2 g i))

theorem b598_original_observed_A_slot_injective434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m) (g : G) :
    Function.Injective (b598OriginalObservedASlot434 J ell m hmJ nu g) := by
  intro i j h
  apply b598_probe_group_index_injective m nu.1 g
  exact source_original_probe_free_index_injective434 J ell m hmJ nu g _ _ _ _ h

theorem b598_original_observed_B_slot_injective434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m) (g : G) :
    Function.Injective (b598OriginalObservedBSlot434 J ell m hmJ nu g) := by
  intro i j h
  apply b598_probe_group_index_injective m nu.2 g
  exact source_original_probe_free_index_injective434 J ell m hmJ nu g _ _ _ _ h
end Green64Analytic.CorrelationSquare

end

end

