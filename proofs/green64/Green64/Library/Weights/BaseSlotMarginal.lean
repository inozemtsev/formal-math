module

public import Green64.Library.Weights.SelectedActiveEnergy

@[expose] public section

/-!
# Weights / BaseSlotMarginal

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalBaseSlotMarginal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000

private theorem b579_ordered_cons_mem
    (P : Finset ℕ) (c n b : ℕ) (a : Fin c → ℕ) :
    Fin.cons b a ∈ orderedBigMarks P (c+1) n ↔
      a ∈ orderedBigMarks P c n ∧
        b ∈ smallPrimeSupport P n \ Finset.univ.image a := by
  constructor
  · intro h
    have hp := (Finset.mem_filter.mp h).1
    have hi := Fin.cons_injective_iff.mp (Finset.mem_filter.mp h).2
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Fintype.mem_piFinset.mpr ?_,hi.2⟩
      intro i
      simpa only [Fin.cons_succ] using Fintype.mem_piFinset.mp hp i.succ
    · apply Finset.mem_sdiff.mpr
      constructor
      · simpa only [Fin.cons_zero] using Fintype.mem_piFinset.mp hp 0
      · intro hb
        obtain ⟨i,_,he⟩ := Finset.mem_image.mp hb
        exact hi.1 ⟨i,he⟩
  · rintro ⟨ha,hb⟩
    have haP := (Finset.mem_filter.mp ha).1
    have haI := (Finset.mem_filter.mp ha).2
    have hbP := (Finset.mem_sdiff.mp hb).1
    have hbN := (Finset.mem_sdiff.mp hb).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using hbP
      · simpa only [Fin.cons_succ] using Fintype.mem_piFinset.mp haP j
    · apply Fin.cons_injective_iff.mpr
      refine ⟨?_,haI⟩
      rintro ⟨i,he⟩
      exact hbN (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩)

variable {G : Type} [Fintype G] [DecidableEq G]

private theorem b579_all_cons_mem
    (P : G → Finset ℕ) (c : G → ℕ) (n : ℕ)
    (a : ∀ g,Fin (c g) → ℕ) (b : G → ℕ) :
    (fun g => Fin.cons (b g) (a g)) ∈
        bigMarkLists P (fun g => c g+1) n ↔
      a ∈ bigMarkLists P c n ∧
      b ∈ Fintype.piFinset
        (fun g => smallPrimeSupport (P g) n \ Finset.univ.image (a g)) := by
  constructor
  · intro h
    have hp (g : G) := (b579_ordered_cons_mem (P g) (c g) n (b g) (a g)).mp
      (Fintype.mem_piFinset.mp h g)
    exact ⟨Fintype.mem_piFinset.mpr (fun g => (hp g).1),
      Fintype.mem_piFinset.mpr (fun g => (hp g).2)⟩
  · rintro ⟨ha,hb⟩
    apply Fintype.mem_piFinset.mpr
    intro g
    exact (b579_ordered_cons_mem (P g) (c g) n (b g) (a g)).mpr
      ⟨Fintype.mem_piFinset.mp ha g,Fintype.mem_piFinset.mp hb g⟩

/-- Exact all-group summation of the base slot on the EXISTING full
ordered/injective marked carrier. The retained test may couple all
selected coordinates arbitrarily. Empty and overfull carriers are kept. -/
theorem b579_original_all_group_base_slot_sum
    (P : G → Finset ℕ) (c : G → ℕ) (n : ℕ)
    (f : (∀ g,Fin (c g) → ℕ) → ℂ) :
    (∑ a ∈ bigMarkLists P (fun g => c g+1) n,
      f (fun g => Fin.tail (a g))) =
      ((∏ g,(smallPrimeCount (P g) n-c g):ℕ):ℂ) *
        ∑ a ∈ bigMarkLists P c n,f a := by
  let S := bigMarkLists P c n
  let B (a : ∀ g,Fin (c g) → ℕ) :=
    Fintype.piFinset
      (fun g => smallPrimeSupport (P g) n \ Finset.univ.image (a g))
  have hbij :
      (∑ z ∈ S.sigma B,f z.1) =
      ∑ a ∈ bigMarkLists P (fun g => c g+1) n,
        f (fun g => Fin.tail (a g)) := by
    apply Finset.sum_bij (fun z _ => fun g => Fin.cons (z.2 g) (z.1 g))
    · intro z hz
      exact (b579_all_cons_mem P c n z.1 z.2).mpr (Finset.mem_sigma.mp hz)
    · intro z hz y hy hzy
      have ha : z.1=y.1 := by
        funext g
        exact (Fin.cons_inj.mp (congrFun hzy g)).2
      have hb : z.2=y.2 := by
        funext g
        exact (Fin.cons_inj.mp (congrFun hzy g)).1
      exact Sigma.ext ha (heq_of_eq hb)
    · intro a ha
      let a0 : ∀ g,Fin (c g) → ℕ := fun g => Fin.tail (a g)
      let b0 : G → ℕ := fun g => a g 0
      have he : (fun g => Fin.cons (b0 g) (a0 g))=a := by
        funext g
        exact Fin.cons_self_tail (a g)
      have hm := (b579_all_cons_mem P c n a0 b0).mp (he.symm ▸ ha)
      exact ⟨⟨a0,b0⟩,Finset.mem_sigma.mpr hm,he⟩
    · intro z hz
      simp only [Fin.tail_cons]
  have hcard (a : ∀ g,Fin (c g) → ℕ) (ha : a ∈ S) :
      (B a).card=∏ g,(smallPrimeCount (P g) n-c g) := by
    unfold B
    rw [Fintype.card_piFinset]
    apply Finset.prod_congr rfl
    intro g _
    have hga := Fintype.mem_piFinset.mp ha g
    have hinj := (Finset.mem_filter.mp hga).2
    have hsub : Finset.univ.image (a g) ⊆ smallPrimeSupport (P g) n := by
      intro p hp
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hga).1 i
    rw [Finset.card_sdiff_of_subset hsub,
      Finset.card_image_of_injective _ hinj]
    simp [smallPrimeCount]
  calc
    _ = ∑ z ∈ S.sigma B,f z.1 := hbij.symm
    _ = ∑ a ∈ S,((∏ g,(smallPrimeCount (P g) n-c g):ℕ):ℂ)*f a := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro a ha
      change (∑ _s ∈ B a,f a) = _
      rw [Finset.sum_const,nsmul_eq_mul,hcard a ha]
    _ = _ := by rw [Finset.mul_sum]

/-- Exact literal marked decoration after summing only the base slot.
The remaining selected lists retain their distinctness and original
normalization. No physical or Fourier coefficient is replaced. -/
theorem b579_original_marked_base_slot_marginal
    (P : G → Finset ℕ) (c : G → ℕ) (V : G → ℝ)
    (q : ℝ) (n : ℕ)
    (f : (∀ g,Fin (c g) → ℕ) → ℂ) :
    actualBigMarkDecoration P (fun g => c g+1) q V
      (fun a => f (fun g => Fin.tail (a g))) n =
      (b579SelectedBaseFactor q c (fun g => smallPrimeCount (P g) n) V:ℂ) *
        (∑ a ∈ bigMarkLists P c n,f a) /
          ((∏ g,(V g)^(c g):ℝ):ℂ) := by
  unfold actualBigMarkDecoration
  rw [b579_original_all_group_base_slot_sum]
  have hp :
      bigMarkPrefactor P (fun g => c g+1) q V n *
        ((∏ g,(smallPrimeCount (P g) n-c g):ℕ):ℂ) =
      (b579SelectedBaseFactor q c (fun g => smallPrimeCount (P g) n) V:ℂ) /
        ((∏ g,(V g)^(c g):ℝ):ℂ) := by
    unfold bigMarkPrefactor b579SelectedBaseFactor
    push_cast
    rw [←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro g _
    rw [pow_succ]
    ring
  rw [←mul_assoc,hp]
  ring
end Green64Analytic.CorrelationSquare

end

end

