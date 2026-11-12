module

public import Green64.Library.Sieve.Foundations.PhysicalPathCRT
public import Green64.Library.Correlation.MemoryActualDomain

@[expose] public section

/-!
# Sieve / Foundations / MarkedPathCRT

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualMarkedPathCRT -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Literal numerical prime set marked at one visit by ALL original
SMALL and BIG ordered lists. Out-of-range visits are empty. -/
def b645ActualActiveAt434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M N : ℕ)
    (sm : Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
      Fin M → SourceNativeMemorySP434 20 L hS g)
    (bm : Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
      Fin M → SourceNativeMemoryBP434 20 L g) (i : ℕ) : Finset ℕ :=
  if hi : i < N+1 then
    (Finset.univ.biUnion (fun g : SourceNativeMemorySG434 20 L hS =>
      Finset.univ.image (fun j : Fin M => (sm ⟨i,hi⟩ g j).val))) ∪
    (Finset.univ.biUnion (fun g : sourceNativeOriginalBigType434 20 L =>
      Finset.univ.image (fun j : Fin M => (bm ⟨i,hi⟩ g j).val)))
  else ∅

private theorem small_mem_G (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g : SourceNativeMemorySG434 20 L hS) (p : SourceNativeMemorySP434 20 L hS g) :
    p.val ∈ sourceNativeOriginalG434 20 L := by
  rw [source_native_original_G_identity434 20 L hS hL]
  cases g with
  | none => exact Finset.mem_union_left _ (Finset.mem_union_left _ p.property)
  | some i =>
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,p.property⟩))

private theorem big_mem_G (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g : sourceNativeOriginalBigType434 20 L) (p : SourceNativeMemoryBP434 20 L g) :
    p.val ∈ sourceNativeOriginalG434 20 L := by
  rw [source_native_original_G_identity434 20 L hS hL]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,p.property⟩)

/-- Every actual marked numerical prime lies in the original complete P. -/
theorem b645_actual_marked_visit_subset434 (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M N : ℕ)
    (sm : Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
      Fin M → SourceNativeMemorySP434 20 L hS g)
    (bm : Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
      Fin M → SourceNativeMemoryBP434 20 L g) (i : ℕ) :
    b645ActualActiveAt434 L hS M N sm bm i ⊆ sourceNativeOriginalG434 20 L := by
  unfold b645ActualActiveAt434
  split_ifs with hi
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨g,_,hg⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hg
      exact small_mem_G L hL hS g (sm ⟨i,hi⟩ g j)
    · obtain ⟨g,_,hg⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hg
      exact big_mem_G L hL hS g (bm ⟨i,hi⟩ g j)
  · exact Finset.empty_subset _

/-- Complete actual active budget, derived from all marked lists and
the exact SMALL+BIG group partition; no cardinality hypothesis is assumed. -/
theorem b645_actual_marked_visit_card434 (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M N : ℕ)
    (sm : Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
      Fin M → SourceNativeMemorySP434 20 L hS g)
    (bm : Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
      Fin M → SourceNativeMemoryBP434 20 L g) (i : ℕ) :
    (b645ActualActiveAt434 L hS M N sm bm i).card ≤
      M*(sourceOriginalPAllGroupIndices 20 L).card := by
  have hall : (sourceOriginalPAllGroupIndices 20 L).card =
      Fintype.card (SourceNativeMemorySG434 20 L hS) +
      Fintype.card (sourceNativeOriginalBigType434 20 L) := by
    simpa only [SourceNativeMemorySG434, Fintype.card_option] using
      source_native_original_all_card434 20 L hS hL
  unfold b645ActualActiveAt434
  split_ifs with hi
  · have hs : (Finset.univ.biUnion (fun g : SourceNativeMemorySG434 20 L hS =>
        Finset.univ.image (fun j : Fin M => (sm ⟨i,hi⟩ g j).val))).card ≤
        M*Fintype.card (SourceNativeMemorySG434 20 L hS) := by
      calc
        _ ≤ ∑ g : SourceNativeMemorySG434 20 L hS,
            (Finset.univ.image (fun j : Fin M => (sm ⟨i,hi⟩ g j).val)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _g : SourceNativeMemorySG434 20 L hS, M :=
          by
            apply Finset.sum_le_sum
            intro g hg
            have hc : (Finset.univ.image (fun j : Fin M => (sm ⟨i,hi⟩ g j).val)).card ≤
                (Finset.univ : Finset (Fin M)).card := Finset.card_image_le
            simpa only [Finset.card_univ, Fintype.card_fin] using hc
        _ = _ := by simp [Nat.mul_comm]
    have hb : (Finset.univ.biUnion (fun g : sourceNativeOriginalBigType434 20 L =>
        Finset.univ.image (fun j : Fin M => (bm ⟨i,hi⟩ g j).val))).card ≤
        M*Fintype.card (sourceNativeOriginalBigType434 20 L) := by
      calc
        _ ≤ ∑ g : sourceNativeOriginalBigType434 20 L,
            (Finset.univ.image (fun j : Fin M => (bm ⟨i,hi⟩ g j).val)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _g : sourceNativeOriginalBigType434 20 L, M :=
          by
            apply Finset.sum_le_sum
            intro g hg
            have hc : (Finset.univ.image (fun j : Fin M => (bm ⟨i,hi⟩ g j).val)).card ≤
                (Finset.univ : Finset (Fin M)).card := Finset.card_image_le
            simpa only [Finset.card_univ, Fintype.card_fin] using hc
        _ = _ := by simp [Nat.mul_comm]
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add hs hb).trans_eq (by rw [hall]; ring))
  · simp

/-- B641 with ALL actual source marks and its active-prime/cardinality
premises fully discharged, for the exact source half-endpoint schedule. -/
theorem b645_eventually_actual_all_marked_path_CRT434
    (E gamma : ℝ) (hE : 0 ≤ E) (hgamma : 0 < gamma) (M : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
    ∀ hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty,
    let N := 2*Nat.ceil (L^(13/25:ℝ))
    ∀ (sm : Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
        Fin M → SourceNativeMemorySP434 20 L hS g)
      (bm : Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
        Fin M → SourceNativeMemoryBP434 20 L g)
      (lo hi : ℕ), Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
    ∀ offset : ℕ → ℤ,
    let visits := Finset.range (N+1)
    let activeAt := b645ActualActiveAt434 L hS M N sm bm
    let eta := sourceVisitQ (1/2:ℝ) N
    let model := ∏ p ∈ sourceNativeOriginalG434 20 L,
      (∑ r ∈ Finset.range p,b641PathPrimeWeight434 visits activeAt eta offset p r)/(p:ℝ)
    |(∑ n ∈ Finset.Ico lo hi, ∏ p ∈ sourceNativeOriginalG434 20 L, ∏ i ∈ visits,
        if p ∈ activeAt i then (if (p:ℤ) ∣ (n:ℤ)+offset i then 1 else 0)
        else (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1)) -
        ((hi-lo:ℕ):ℝ)*model| ≤ (((hi-lo:ℕ):ℝ)*model)*L^(-E*(N:ℝ)) := by
  filter_upwards [b641_eventually_actual_parity_physical_path_CRT434 E gamma hE hgamma M,
    eventually_source_native_original_group_masses434 20 (by norm_num)] with L hcrt hmass
  refine ⟨hmass.2.1, ?_⟩
  intro hS
  dsimp only
  intro sm bm lo hi hH offset
  exact hcrt (b645ActualActiveAt434 L hS M _ sm bm)
    (fun i _ => b645_actual_marked_visit_subset434 L hmass.1 hS M _ sm bm i)
    (fun i _ => b645_actual_marked_visit_card434 L hmass.1 hS M _ sm bm i)
    lo hi hH offset
end Green64Analytic.SourceBlockSieve

end

end

