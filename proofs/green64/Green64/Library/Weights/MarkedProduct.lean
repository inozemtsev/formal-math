module

public import Green64.Library.Weights.Part025
public import Green64.Library.Analysis.Estimates.PrimeCoordinates
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Weights.Part073

@[expose] public section

/-!
# Weights / MarkedProduct

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualMarkedProduct -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option linter.unusedSectionVars false

abbrev B657MarkSlots434 (SG BG : Type) (M : ℕ) := (SG × Fin M) ⊕ (BG × Fin M)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]

def b657MarkSlotPrime434 (M : ℕ) (s : B657OrderedMarks434 SP BP M) :
    B657MarkSlots434 SG BG M → ℕ :=
  Sum.elim (fun t => sm t.1 (s.1 t.1 t.2)) (fun t => bm t.1 (s.2 t.1 t.2))

theorem b657_mark_product_eq_slots434 (M : ℕ) (s : B657OrderedMarks434 SP BP M) :
    b657OrderedMarkProduct434 SP sm BP bm M s =
      ∏ t : B657MarkSlots434 SG BG M, b657MarkSlotPrime434 SP sm BP bm M s t := by
  simp [b657OrderedMarkProduct434,b657MarkSlotPrime434,B657MarkSlots434,
    Fintype.prod_sum_type,Fintype.prod_prod_type]

/-- Distinct numerical primes dividing n have their complete product
dividing n. Distinct labels alone would not suffice; the actual family
below supplies numerical injectivity from the original disjoint bands. -/
theorem b657_distinct_prime_product_divides434
    {I : Type} [Fintype I] [DecidableEq I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (n : ℕ) (hd : ∀ i, p i∣n) : (∏ i, p i)∣n := by
  have hall (s : Finset I) : (∏ i ∈ s, p i)∣n := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have hc : Nat.Coprime (p i) (∏ j ∈ s, p j) := by
        apply Nat.Coprime.symm
        apply Nat.Coprime.prod_left
        intro j hj
        apply (Nat.coprime_primes (hp j) (hp i)).mpr
        intro he
        exact hi ((hinj he) ▸ hj)
      exact hc.mul_dvd_of_dvd_of_dvd (hd i) ih
  exact hall Finset.univ

end Green64FullPhysicalE
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000

private theorem b657_actual_band_eq (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (g : B645ActualGroup434 L hS) :
    b645ActualBand434 L hS g = sourceOriginalPAllActualBands 20 L
      (sourceNativeOriginalFullEquiv434 20 L hS hL g) := by
  rcases g with g | g
  · cases g <;> rfl
  · rfl

private theorem b657_actual_group_unique (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g h : B645ActualGroup434 L hS) (p : ℕ)
    (hp : p ∈ b645ActualBand434 L hS g) (hq : p ∈ b645ActualBand434 L hS h) : g=h := by
  apply (sourceNativeOriginalFullEquiv434 20 L hS hL).injective
  apply source_original_P_actual_all_disjoint 20 L (by norm_num) (zero_lt_one.trans hL) _ _ p
  · simpa only [←b657_actual_band_eq L hL hS g] using hp
  · simpa only [←b657_actual_band_eq L hL hS h] using hq

private theorem b657_actual_band_mem (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g : B645ActualGroup434 L hS) (p : ℕ) (hp : p ∈ b645ActualBand434 L hS g) :
    p ∈ sourceNativeOriginalG434 20 L := by
  change p ∈ Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  apply Finset.mem_biUnion.mpr
  refine ⟨sourceNativeOriginalFullEquiv434 20 L hS hL g,Finset.mem_univ _,?_⟩
  simpa only [←b657_actual_band_eq L hL hS g] using hp

/-- Every selected actual numerical prime lies in the literal original
full P alphabet, before taking any product or norm. -/
theorem b657_actual_mark_slot_mem434 (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M : ℕ)
    (s : B657OrderedMarks434 (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L) M)
    (t : B657MarkSlots434 (SourceNativeMemorySG434 20 L hS) (sourceNativeOriginalBigType434 20 L) M) :
    b657MarkSlotPrime434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) M s t ∈ sourceNativeOriginalG434 20 L := by
  rcases t with ⟨g,j⟩ | ⟨g,j⟩
  · exact b657_actual_band_mem L hL hS (Sum.inl g) _ (s.1 g j).property
  · exact b657_actual_band_mem L hL hS (Sum.inr g) _ (s.2 g j).property

/-- Numerical, cross-group injectivity of the full marked prime list.
It uses the actual original prime-band disjointness and both independent
ordered-label injections, with no assumption on the number of marks. -/
theorem b657_actual_mark_slots_injective434 (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (M : ℕ)
    (s : B657OrderedMarks434 (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L) M) :
    Function.Injective (b657MarkSlotPrime434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) M s) := by
  intro a b hab
  rcases a with ⟨g,i⟩ | ⟨g,i⟩ <;> rcases b with ⟨h,j⟩ | ⟨h,j⟩
  · change (s.1 g i).val=(s.1 h j).val at hab
    have hg : g=h := Sum.inl.inj (b657_actual_group_unique L hL hS (Sum.inl g) (Sum.inl h)
      (s.1 g i).val (s.1 g i).property (by rw [hab]; exact (s.1 h j).property))
    subst h
    have hj : i=j := (s.1 g).injective (Subtype.ext hab)
    subst j
    rfl
  · change (s.1 g i).val=(s.2 h j).val at hab
    have hg := b657_actual_group_unique L hL hS (Sum.inl g) (Sum.inr h)
      (s.1 g i).val (s.1 g i).property (by rw [hab]; exact (s.2 h j).property)
    cases hg
  · change (s.2 g i).val=(s.1 h j).val at hab
    have hg := b657_actual_group_unique L hL hS (Sum.inr g) (Sum.inl h)
      (s.2 g i).val (s.2 g i).property (by rw [hab]; exact (s.1 h j).property)
    cases hg
  · change (s.2 g i).val=(s.2 h j).val at hab
    have hg : g=h := Sum.inr.inj (b657_actual_group_unique L hL hS (Sum.inr g) (Sum.inr h)
      (s.2 g i).val (s.2 g i).property (by rw [hab]; exact (s.2 h j).property))
    subst h
    have hj : i=j := (s.2 g).injective (Subtype.ext hab)
    subst j
    rfl

/-- The complete actual marked product at a physical state, with every
original SMALL and BIG mark and exactly its original multiplicity. -/
def b657ActualMarkProduct434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions) : ℕ :=
  b657OrderedMarkProduct434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) (J+1)
    (b657PhysicalMarkReadout434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 positions x)

/-- Both hypotheses required for removing the ordinary part are derived
from the literal actual prime lists, not supplied as density premises. -/
theorem b657_actual_mark_product_support434 (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions) :
    b657ActualMarkProduct434 L hS J positions x ≠ 0 ∧
      (b657ActualMarkProduct434 L hS J positions x).primeFactors ⊆ sourceNativeOriginalG434 20 L := by
  let s := b657PhysicalMarkReadout434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 positions x
  let p := b657MarkSlotPrime434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) (J+1) s
  have hmem (t) : p t ∈ sourceNativeOriginalG434 20 L := b657_actual_mark_slot_mem434 L hL hS (J+1) s t
  have hp (t) : (p t).Prime := (b638_actual_full_P_range434 L hL.le (p t) (hmem t)).1
  have hh := b656_P_prime_product_support434 (sourceNativeOriginalG434 20 L) p hp hmem
  rw [←b657_mark_product_eq_slots434] at hh
  exact hh

/-- The WHOLE actual marked prime product divides the physical integer.
The proof is precisely where the original disjoint numerical bands and
ordered distinct marks are used; no product-divisibility premise remains. -/
theorem b657_actual_mark_product_divides434 (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
    (hx : 0 ≤ x.val.1.val) :
    b657ActualMarkProduct434 L hS J positions x ∣ x.val.1.val.toNat := by
  let s := b657PhysicalMarkReadout434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 positions x
  let p := b657MarkSlotPrime434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) (J+1) s
  have hp (t) : (p t).Prime := (b638_actual_full_P_range434 L hL.le (p t)
    (b657_actual_mark_slot_mem434 L hL hS (J+1) s t)).1
  have hm := b657_physical_mark_divides434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 positions x hx
  have hd : ∀ t, p t ∣ x.val.1.val.toNat := by
    intro t
    rcases t with ⟨g,j⟩ | ⟨g,j⟩
    · exact hm.1 g j
    · exact hm.2 g j
  have hh := b657_distinct_prime_product_divides434 p hp
    (b657_actual_mark_slots_injective434 L hL hS (J+1) s) x.val.1.val.toNat hd
  rw [←b657_mark_product_eq_slots434] at hh
  exact hh
end Green64Analytic.SourceBlockSieve

end

end

