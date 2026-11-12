module

public import Green64.Library.Correlation.Part044
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-!
# Correlation / MemoryOldFockDisintegration

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOldFockDisintegration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

def sourceOriginalMemorySurvivorSet434
    {A : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) : Finset (Fin j) :=
  Finset.univ \ (Finset.univ.image f)

def sourceOriginalMemoryRemainder434
    {A U : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) (x : Fin j → U) : Multiset U :=
  (sourceOriginalMemorySurvivorSet434 j f).val.map x

private def oldComplementEquiv
    {A : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) :
    Fin (j-Fintype.card A) ≃ ↥(sourceOriginalMemorySurvivorSet434 j f) := by
  classical
  apply Fintype.equivOfCardEq
  have him : (Finset.univ.image f).card=Fintype.card A := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact fun a _ b _ h => f.injective h
  have hc : Fintype.card ↥(sourceOriginalMemorySurvivorSet434 j f) =
      (sourceOriginalMemorySurvivorSet434 j f).card := by
    convert Fintype.card_coe (sourceOriginalMemorySurvivorSet434 j f) using 1 <;>
      congr <;> exact Subsingleton.elim _ _
  rw [Fintype.card_fin,hc]
  unfold sourceOriginalMemorySurvivorSet434
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ,Finset.card_univ,Fintype.card_fin,him]

private def oldRawSplitEquiv
    {A : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) :
    A ⊕ ↥(sourceOriginalMemorySurvivorSet434 j f) ≃ Fin j :=
  Equiv.ofBijective (Sum.elim f Subtype.val) (by
    constructor
    · intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (f.injective h)
        | inr b =>
          exfalso
          have hb := (Finset.mem_sdiff.mp b.property).2
          exact hb (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,h⟩)
      | inr a =>
        cases b with
        | inl b =>
          exfalso
          have ha := (Finset.mem_sdiff.mp a.property).2
          exact ha (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,h.symm⟩)
        | inr b => exact congrArg Sum.inr (Subtype.ext h)
    · intro i
      by_cases hi : i ∈ Finset.univ.image f
      · obtain ⟨a,ha,hfa⟩ := Finset.mem_image.mp hi
        exact ⟨Sum.inl a,hfa⟩
      · exact ⟨Sum.inr ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩⟩,rfl⟩)

private def oldSplitEquiv
    {A : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) :
    A ⊕ Fin (j-Fintype.card A) ≃ Fin j :=
  (Equiv.sumCongr (Equiv.refl A) (oldComplementEquiv j f)).trans (oldRawSplitEquiv j f)

private theorem oldSplitEquiv_inl
    {A : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) (a : A) :
    oldSplitEquiv j f (Sum.inl a)=f a := rfl

private theorem oldSplitEquiv_inr
    {A : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) (i : Fin (j-Fintype.card A)) :
    oldSplitEquiv j f (Sum.inr i)=(oldComplementEquiv j f i).val := rfl

private theorem remainder_split
    {A U : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) (x : Fin j → U) :
    sourceOriginalMemoryRemainder434 j f x =
      (Finset.univ : Finset (Fin (j-Fintype.card A))).val.map
        (fun i => x (oldSplitEquiv j f (Sum.inr i))) := by
  classical
  have hh := congrArg (fun s : Finset ↥(sourceOriginalMemorySurvivorSet434 j f) =>
    s.val.map (fun i => x i.val)) (Finset.map_univ_equiv (oldComplementEquiv j f))
  simp only [Finset.map_val,Multiset.map_map,Function.comp_def] at hh
  have he :
      (Finset.univ : Finset ↥(sourceOriginalMemorySurvivorSet434 j f)).val.map
        (fun i => x i.val) = sourceOriginalMemoryRemainder434 j f x := by
    have ht := Finset.univ_val_map_subtype_restrict x
      (fun i => i ∈ sourceOriginalMemorySurvivorSet434 j f)
    simp only [Subtype.restrict_def,Function.comp_def,Finset.filter_univ_mem] at ht
    convert ht using 1 <;> congr <;> exact Subsingleton.elim _ _
  rw [he] at hh
  exact hh.symm

/-- Reindex the ACTUAL OLD coordinates for a fixed retrieval injection.
The remaining atom multiset and the entire ordered promoted vector stay
jointly inside H. No distinct-atom or factorization assumption is used. -/
theorem source_original_memory_OLD_fixed_injection_disintegration434
    {A U : Type} [Fintype A] [Fintype U] (j : ℕ)
    (f : A ↪ Fin j) (mu : U → ℝ)
    (H : Multiset U → (A → U) → ℝ) :
    (∑ x : Fin j → U,(∏ i : Fin j,mu (x i))*
      H (sourceOriginalMemoryRemainder434 j f x) (fun a => x (f a))) =
    ∑ v : A → U,∑ u : Fin (j-Fintype.card A) → U,
      (∏ a : A,mu (v a))*(∏ i : Fin (j-Fintype.card A),mu (u i))*
      H ((Finset.univ : Finset (Fin (j-Fintype.card A))).val.map u) v := by
  classical
  let e := oldSplitEquiv j f
  let ef : (Fin j → U) ≃ (A → U) × (Fin (j-Fintype.card A) → U) :=
    (Equiv.arrowCongr e.symm (Equiv.refl U)).trans
      (Equiv.sumArrowEquivProdArrow A (Fin (j-Fintype.card A)) U)
  rw [← Fintype.sum_prod_type (fun z : (A → U) × (Fin (j-Fintype.card A) → U) =>
    (∏ a : A,mu (z.1 a))*(∏ i : Fin (j-Fintype.card A),mu (z.2 i))*
      H ((Finset.univ : Finset (Fin (j-Fintype.card A))).val.map z.2) z.1)]
  apply Fintype.sum_equiv ef
  intro x
  have hp : (∏ i : Fin j,mu (x i)) =
      (∏ a : A,mu ((ef x).1 a))*
      (∏ i : Fin (j-Fintype.card A),mu ((ef x).2 i)) := by
    rw [← e.prod_comp (fun i => mu (x i)),Fintype.prod_sum_type]
    rfl
  rw [hp,remainder_split]
  rfl

/-- Complete weighted OLD-index sum, now at the actual source 1/j!
measure. Every injection is counted by its positions even when atom
values coincide; its factorial cancels to 1/(j-a)! under the integral. -/
theorem source_original_memory_OLD_FOCK_injection_disintegration434
    {A U : Type} [Fintype A] [Fintype U] (j : ℕ) (ha : Fintype.card A ≤ j)
    (mu : U → ℝ) (H : Multiset U → (A → U) → ℝ) :
    (∑ x : Fin j → U,∑ f : A ↪ Fin j,
      ((∏ i : Fin j,mu (x i))/(j.factorial:ℝ))*
      H (sourceOriginalMemoryRemainder434 j f x) (fun a => x (f a))) =
    (1/((j-Fintype.card A).factorial:ℝ))*
      ∑ v : A → U,∑ u : Fin (j-Fintype.card A) → U,
        (∏ a : A,mu (v a))*(∏ i : Fin (j-Fintype.card A),mu (u i))*
        H ((Finset.univ : Finset (Fin (j-Fintype.card A))).val.map u) v := by
  classical
  let T := ∑ v : A → U,∑ u : Fin (j-Fintype.card A) → U,
    (∏ a : A,mu (v a))*(∏ i : Fin (j-Fintype.card A),mu (u i))*
    H ((Finset.univ : Finset (Fin (j-Fintype.card A))).val.map u) v
  have hf (f : A ↪ Fin j) :
      (∑ x : Fin j → U,((∏ i : Fin j,mu (x i))/(j.factorial:ℝ))*
        H (sourceOriginalMemoryRemainder434 j f x) (fun a => x (f a))) =
      T/(j.factorial:ℝ) := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,source_original_memory_OLD_fixed_injection_disintegration434]
  rw [Finset.sum_comm]
  simp_rw [hf]
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_embedding_eq,
    Fintype.card_fin,Nat.descFactorial_eq_factorial_mul_choose]
  have hc := Green64PhysicalEdge.old_injections_over_fock_factorial j (Fintype.card A) ha
  calc
    _ = (((Nat.choose j (Fintype.card A)*(Fintype.card A).factorial:ℕ):ℝ)/
        (j.factorial:ℝ))*T := by push_cast;ring
    _ = _ := by rw [hc]

/-- Literal physical survivor-plus-store output, expressed in the same
multiset variables as the exact weighted OLD disintegration. -/
theorem source_original_memory_actual_output_remainder434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (M B : ℕ) (x : BigState modulus M B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M)) (f : ↥promote ↪ Fin x.2.1.val) :
    physicalPendingMultiset modulus M B x sigma step ⟨stores,promote,f⟩ =
      (sourceOriginalMemoryRemainder434 x.2.1.val f x.2.2).map
        (Green64PhysicalEdge.translateAtom step) +
      stores.val.map (fun i => (⟨x.1 (sigma i),
        (step : ZMod (modulus (x.1 (sigma i))))⟩ : Green64Fock.Atom P modulus)) := by
  classical
  simp only [physicalPendingMultiset,physicalPendingOutput,survivors,newlyStored,
    survivorIndices,selectedOld,sourceOriginalMemoryRemainder434,
    sourceOriginalMemorySurvivorSet434,← Multiset.coe_add,← Multiset.map_coe,
    Finset.coe_toList,Multiset.map_map,Function.comp_def]
end Green64Analytic.CorrelationSquare

end

end

