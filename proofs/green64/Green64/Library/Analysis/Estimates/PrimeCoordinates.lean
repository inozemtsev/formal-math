module

public import Green64.Library.Sieve.Foundations.MarkedPathCRT

@[expose] public section

/-!
# Analysis / Estimates / PrimeCoordinates

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualPrimeCoordinates -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 1500000

abbrev B645ActualGroup434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) :=
  SourceNativeMemorySG434 20 L hS ⊕ sourceNativeOriginalBigType434 20 L

def b645ActualBand434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) :
    B645ActualGroup434 L hS → Finset ℕ :=
  Sum.elim (SourceNativeMemorySmallSet434 20 L hS) (sourceNativeOriginalTb434 20 L)

private theorem band_eq (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (g : B645ActualGroup434 L hS) :
    b645ActualBand434 L hS g = sourceOriginalPAllActualBands 20 L
      (sourceNativeOriginalFullEquiv434 20 L hS hL g) := by
  rcases g with g | g
  · cases g <;> rfl
  · rfl

private theorem group_unique (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g h : B645ActualGroup434 L hS) (p : ℕ)
    (hp : p ∈ b645ActualBand434 L hS g) (hq : p ∈ b645ActualBand434 L hS h) : g = h := by
  apply (sourceNativeOriginalFullEquiv434 20 L hS hL).injective
  apply source_original_P_actual_all_disjoint 20 L (by norm_num) (by linarith) _ _ p
  · simpa only [← band_eq L hL hS g] using hp
  · simpa only [← band_eq L hL hS h] using hq

/-- A prime in an actual SMALL group is globally active exactly at its
own marked visits. Cross-group or BIG collisions are ruled out by the
proved original numerical prime-band disjointness. -/
theorem b645_actual_small_active_iff434 (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M N : ℕ)
    (sm : Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
      Fin M → SourceNativeMemorySP434 20 L hS g)
    (bm : Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
      Fin M → SourceNativeMemoryBP434 20 L g)
    (i : Fin (N+1)) (g : SourceNativeMemorySG434 20 L hS)
    (p : SourceNativeMemorySP434 20 L hS g) :
    p.val ∈ b645ActualActiveAt434 L hS M N sm bm i.val ↔ ∃ j, sm i g j = p := by
  unfold b645ActualActiveAt434
  rw [dite_eq_left i.isLt]
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨g',_,hgp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hgp
      have hg : (Sum.inl g' : B645ActualGroup434 L hS) = Sum.inl g :=
        group_unique L hL hS (Sum.inl g') (Sum.inl g) p.val
          (by rw [← hj]; exact (sm i g' j).property) p.property
      have hgg : g' = g := Sum.inl.inj hg
      subst g'
      exact ⟨j, Subtype.ext hj⟩
    · obtain ⟨g',_,hgp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hgp
      have hg : (Sum.inr g' : B645ActualGroup434 L hS) = Sum.inl g :=
        group_unique L hL hS (Sum.inr g') (Sum.inl g) p.val
          (by rw [← hj]; exact (bm i g' j).property) p.property
      cases hg
  · rintro ⟨j,hj⟩
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ _, Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
    exact congrArg Subtype.val hj

theorem b645_actual_big_active_iff434 (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M N : ℕ)
    (sm : Fin (N+1) → (g : SourceNativeMemorySG434 20 L hS) →
      Fin M → SourceNativeMemorySP434 20 L hS g)
    (bm : Fin (N+1) → (g : sourceNativeOriginalBigType434 20 L) →
      Fin M → SourceNativeMemoryBP434 20 L g)
    (i : Fin (N+1)) (g : sourceNativeOriginalBigType434 20 L)
    (p : SourceNativeMemoryBP434 20 L g) :
    p.val ∈ b645ActualActiveAt434 L hS M N sm bm i.val ↔ ∃ j, bm i g j = p := by
  unfold b645ActualActiveAt434
  rw [dite_eq_left i.isLt]
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨g',_,hgp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hgp
      have hg : (Sum.inl g' : B645ActualGroup434 L hS) = Sum.inr g :=
        group_unique L hL hS (Sum.inl g') (Sum.inr g) p.val
          (by rw [← hj]; exact (sm i g' j).property) p.property
      cases hg
    · obtain ⟨g',_,hgp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hgp
      have hg : (Sum.inr g' : B645ActualGroup434 L hS) = Sum.inr g :=
        group_unique L hL hS (Sum.inr g') (Sum.inr g) p.val
          (by rw [← hj]; exact (bm i g' j).property) p.property
      have hgg : g' = g := Sum.inr.inj hg
      subst g'
      exact ⟨j, Subtype.ext hj⟩
  · rintro ⟨j,hj⟩
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ _, Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
    exact congrArg Subtype.val hj

/-- Exact finite product over EVERY actual numerical prime equals both
original family products. This is only the carrier conversion for the
physical CRT model; it is not a cancellation or RMS estimate. -/
theorem b645_actual_full_prime_product434
    {A : Type} [CommMonoid A] (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (F : ℕ → A) :
    (∏ p ∈ sourceNativeOriginalG434 20 L, F p) =
      (∏ g : SourceNativeMemorySG434 20 L hS, ∏ p : SourceNativeMemorySP434 20 L hS g, F p.val) *
      (∏ g : sourceNativeOriginalBigType434 20 L, ∏ p : SourceNativeMemoryBP434 20 L g, F p.val) := by
  have hd : Set.PairwiseDisjoint (Finset.univ : Finset (sourceOriginalPAllGroupType 20 L))
      (sourceOriginalPAllActualBands 20 L) := by
    intro g hg h hh hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact hne (source_original_P_actual_all_disjoint 20 L (by norm_num) (by linarith) g h p hp hq)
  rw [sourceNativeOriginalG434, Finset.prod_biUnion hd]
  rw [source_native_original_band_product434 20 L hS hL (fun P => ∏ p ∈ P, F p)]
  have hs : (∏ g : SourceNativeMemorySG434 20 L hS,
      ∏ p : SourceNativeMemorySP434 20 L hS g, F p.val) =
      (∏ p ∈ sourceNativeOriginalS434 20 L hS, F p) *
        ∏ g : sourceNativeOriginalTsType434 20 L hS,
          ∏ p ∈ sourceNativeOriginalTs434 20 L hS g, F p := by
    simp only [SourceNativeMemorySG434, Fintype.prod_option, SourceNativeMemorySP434,
      Finset.prod_coe_sort]
  have hb : (∏ g : sourceNativeOriginalBigType434 20 L,
      ∏ p : SourceNativeMemoryBP434 20 L g, F p.val) =
      ∏ g : sourceNativeOriginalBigType434 20 L,
        ∏ p ∈ sourceNativeOriginalTb434 20 L g, F p := by
    simp only [SourceNativeMemoryBP434, Finset.prod_coe_sort]
  rw [hs,hb]
end Green64Analytic.SourceBlockSieve

end

end

