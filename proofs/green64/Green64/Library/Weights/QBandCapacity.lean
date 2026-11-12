module

public import Green64.Library.Weights.SourceQSkipActualResidual
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
# Weights / QBandCapacity

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualQBandCapacity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Total prime multiplicity in one literal Q band, including repetitions. -/
def b613QBandMultiplicity434 (Q : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ Q, n.factorization p

private theorem band_multiplicity_product
    {I B : Type} [Fintype I] [Fintype B] [DecidableEq B]
    (Q : B → Finset ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b=c)
    (band : I → B) (value : I → ℕ)
    (hmem : ∀ i, value i ∈ Q (band i)) (g : B) :
    b613QBandMultiplicity434 (Q g) (∏ i, value i) =
      Fintype.card {i : I // band i=g} := by
  have hp (i : I) := hPrime (band i) (value i) (hmem i)
  have hx (i : I) :
      b613QBandMultiplicity434 (Q g) (value i) =
        if band i=g then 1 else 0 := by
    have he : value i ∈ Q g ↔ band i=g := by
      constructor
      · exact hDisj _ _ _ (hmem i)
      · intro h; simpa only [h] using hmem i
    simp [b613QBandMultiplicity434,(hp i).factorization,Finsupp.single_apply,he]
  calc
    _ = ∑ i, b613QBandMultiplicity434 (Q g) (value i) := by
      simp only [b613QBandMultiplicity434,
        Nat.factorization_prod (fun i _ => (hp i).ne_zero),
        Finsupp.finsetSum_apply]
      exact Finset.sum_comm
    _ = ∑ i, if band i=g then 1 else 0 := by simp_rw [hx]
    _ = Fintype.card {i : I // band i=g} := by
      rw [Fintype.card_subtype,Finset.card_filter]

def b613FullLabel434
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (s : B → ℝ) (b : B) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r s b slot).length → Bool) :
    Option {z : Fin (sourceOrderedLabels r s b slot).length // ¬δ z=true} →
      B × Fin r
  | none => (b,slot)
  | some z => (sourceSortedLabelEquiv r s b slot z.val).val

private theorem b613FullLabel_injective
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (s : B → ℝ) (b : B) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r s b slot).length → Bool) :
    Function.Injective (b613FullLabel434 r s b slot δ) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      exact False.elim ((sourceSortedLabelEquiv r s b slot y.val).property h.symm)
  | some x =>
    cases y with
    | none =>
      exact False.elim ((sourceSortedLabelEquiv r s b slot x.val).property h)
    | some y =>
      congr 1
      apply Subtype.ext
      apply (sourceSortedLabelEquiv r s b slot).injective
      exact Subtype.ext h

/-- Exact multiplicity in the original designated-Q-prime plus literal
OrderedQSkip product. Taken slots disappear; the designated slot is restored
exactly once. No squarefree or injective-prime assumption is present. -/
theorem b613_actual_QSlot_QSkip_band_count434
    (r d : ℕ) (L : ℝ) (hr : 1≤ r) (hL : 0<L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (p : ℕ) (hp : p∈sourceOriginalQActualBands r d L b)
    (a : OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)
    (g : Fin (d+1)) :
    b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g)
        (p*orderedSkipProduct a) =
      Fintype.card {z :
        Option {z : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
          ¬δ z=true} //
        (b613FullLabel434 r (sourceActualSortedScales r d L) b slot δ z).1=g} := by
  let I := {z : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
    ¬δ z=true}
  let label := b613FullLabel434 r (sourceActualSortedScales r d L) b slot δ
  let value : Option I → ℕ := fun z => z.elim p (fun z => (a z).val)
  have hmem (z : Option I) :
      value z ∈ sourceOriginalQActualBands r d L (label z).1 := by
    cases z with
    | none => exact hp
    | some z => exact (a z).property
  have he := band_multiplicity_product
    (sourceOriginalQActualBands r d L)
    (sourceOriginalQActualBands_prime434 r d L)
    (source_original_Q_actual_all_disjoint434 r d L hr hL)
    (fun z : Option I => (label z).1) value hmem g
  simpa only [Fintype.prod_option,value,Option.elim_none,Option.elim_some,
    orderedSkipProduct] using he

/-- The actual designated-prime plus QSkip product has at most r prime
factors with multiplicity in EACH numerical Q band, for every original
allocation and every repeated-draw tuple. In particular the r=6 cap is six. -/
theorem b613_actual_QSlot_QSkip_band_capacity434
    (r d : ℕ) (L : ℝ) (hr : 1≤ r) (hL : 0<L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (p : ℕ) (hp : p∈sourceOriginalQActualBands r d L b)
    (a : OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)
    (g : Fin (d+1)) :
    b613QBandMultiplicity434 (sourceOriginalQActualBands r d L g)
        (p*orderedSkipProduct a) ≤ r := by
  rw [b613_actual_QSlot_QSkip_band_count434 r d L hr hL b slot δ p hp a g]
  let I := Option {z : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
    ¬δ z=true}
  let label := b613FullLabel434 r (sourceActualSortedScales r d L) b slot δ
  have hinj : Function.Injective label :=
    b613FullLabel_injective r (sourceActualSortedScales r d L) b slot δ
  have hc := Fintype.card_le_of_injective
    (fun z : {z : I // (label z).1=g} => (label z.val).2)
    (by
      intro x y he
      apply Subtype.ext
      apply hinj
      exact Prod.ext (x.property.trans y.property.symm) he)
  simpa only [Fintype.card_fin] using hc

/-- Every prime factor of an actual designated-Q-prime plus QSkip product
belongs to an actual Q band. This is support, with no size heuristic. -/
theorem b613_actual_QSlot_QSkip_prime_support434
    (r d : ℕ) (L : ℝ)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (p : ℕ) (hp : p∈sourceOriginalQActualBands r d L b)
    (a : OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)
    (q : ℕ) (hq : q.Prime) (hqd : q∣p*orderedSkipProduct a) :
    ∃ g : Fin (d+1), q∈sourceOriginalQActualBands r d L g := by
  rcases hq.dvd_mul.mp hqd with hqp | hqa
  · have he : q=p := (Nat.prime_dvd_prime_iff_eq hq
      (sourceOriginalQActualBands_prime434 r d L b p hp)).mp hqp
    exact ⟨b,he.symm ▸ hp⟩
  · obtain ⟨z,_,hz⟩ := (hq.prime.dvd_finsetProd_iff (fun z => (a z).val)).mp hqa
    let g := (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot z.val).val.1
    have hmem : (a z).val∈sourceOriginalQActualBands r d L g := (a z).property
    have he : q=(a z).val := (Nat.prime_dvd_prime_iff_eq hq
      (sourceOriginalQActualBands_prime434 r d L g _ hmem)).mp hz
    exact ⟨g,he.symm ▸ hmem⟩
end Green64Analytic.ShiftTwoTerminal

end

end

