module

public import Green64.Library.Weights.Part087

@[expose] public section

/-!
# Weights / UnfilteredEvolutionGhostZeroDisintegration

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredEvolutionGhostZeroDisintegration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {U : Type} [Fintype U] [DecidableEq U]

private theorem bag_card {I : Type} [Fintype I] (x : I → U) :
    (memoryTupleBag x).card=Fintype.card I := by simp [memoryTupleBag,Multiset.card_sum]

/-- The zero-only deletion filter and survivor damping are actual product
laws on the two index sets, without any assumption that values are distinct. -/
theorem source_original_evolution_ghost_zero_product434
    (j : ℕ) (x : Fin j → U) (A : Finset (Fin j))
    (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ) (alpha chi : ℝ)
    (H : Multiset U → Multiset U → ℝ) :
    (if A ⊆ Finset.univ.filter (fun i => zero (x i)) then
      (∏ i,mu (x i))*alpha^A.card*
        chi^((Finset.univ.filter (fun i => zero (x i))).card-A.card)*
          H (memoryTupleBag x) (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val))
      else 0) =
    (∏ i : ↥A,if zero (x i.val) then mu (x i.val) else 0) *
      (∏ i : {i : Fin j // i ∉ A},mu (x i.val)*(if zero (x i.val) then chi else 1)) *
      (alpha^(memoryTupleBag (fun i : ↥A => x i.val)).card *
        H (memoryTupleBag (fun i : ↥A => x i.val) +
          memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val))
          (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val))) := by
  classical
  let Z := Finset.univ.filter (fun i : Fin j => zero (x i))
  by_cases hA : A ⊆ Z
  · rw [if_pos hA]
    have hd : (∏ i : ↥A,if zero (x i.val) then mu (x i.val) else 0) =
        ∏ i : ↥A,mu (x i.val) := by
      apply Finset.prod_congr rfl
      intro i _
      exact if_pos (Finset.mem_filter.mp (hA i.property)).2
    have hs : (∏ i : {i : Fin j // i ∉ A},if zero (x i.val) then chi else 1) =
        chi^(Z.card-A.card) := by
      rw [memory_source_survivor_zero_count x zero A hA]
      rw [←Finset.prod_filter]
      simp only [Finset.prod_const,Fintype.card_subtype]
    rw [hd,Finset.prod_mul_distrib,hs,bag_card]
    simp only [Fintype.card_coe]
    have hb : memoryTupleBag (fun i : ↥A => x i.val) +
        memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val)=memoryTupleBag x := by
      convert memory_tuple_bag_split (fun i : Fin j => i ∈ A) x using 1 <;>
        congr 2 <;> exact Subsingleton.elim _ _
    rw [hb]
    have hp : (∏ i : ↥A,mu (x i.val))*(∏ i : {i : Fin j // i ∉ A},mu (x i.val)) =
        ∏ i : Fin j,mu (x i) := by
      convert Fintype.prod_subtype_mul_prod_subtype (fun i : Fin j => i ∈ A)
        (fun i => mu (x i)) using 1 <;> congr 2 <;> ext z <;> simp
    rw [←hp]
    ring
  · rw [if_neg hA]
    have hex : ∃ i : Fin j,i ∈ A ∧ ¬zero (x i) := by
      by_contra hh
      apply hA
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_contra hz
      exact hh ⟨i,hi,hz⟩
    obtain ⟨i,hi,hz⟩ := hex
    have hd : (∏ i : ↥A,if zero (x i.val) then mu (x i.val) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ (⟨i,hi⟩:↥A)) (by simp [hz])
    rw [hd,zero_mul,zero_mul]

/-- The actual indexed-zero-deletion and survivor-damping sum in one Fock
sector, disintegrated with its true factorial. Both endpoint tests stay joint. -/
theorem source_original_evolution_ghost_zero_FOCK_disintegration434
    (j : ℕ) (zero : U → Prop) [DecidablePred zero]
    (mu : U → ℝ) (alpha chi : ℝ) (H : Multiset U → Multiset U → ℝ) :
    (∑ x : Fin j → U,(∏ i,mu (x i))/(j.factorial:ℝ) *
      ∑ A ∈ (Finset.univ.filter (fun i : Fin j => zero (x i))).powerset,
        alpha^A.card*chi^((Finset.univ.filter (fun i : Fin j => zero (x i))).card-A.card)*
          H (memoryTupleBag x)
            (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val))) =
    ∑ a ∈ Finset.range (j+1),
      (1/((a.factorial:ℝ)*((j-a).factorial:ℝ)))*
      (∑ v : Fin a → U,∑ u : Fin (j-a) → U,
        (∏ i,if zero (v i) then mu (v i) else 0)*
          (∏ i,mu (u i)*(if zero (u i) then chi else 1))*
          (alpha^a*H (memoryTupleBag v+memoryTupleBag u) (memoryTupleBag u))) := by
  have hh := source_original_evolution_ghost_FOCK_subset_disintegration434 j
    (fun u => if zero u then mu u else 0)
    (fun u => mu u*(if zero u then chi else 1))
    (fun d s => alpha^d.card*H (d+s) s)
  simp only [bag_card,Fintype.card_fin] at hh
  rw [←hh]
  apply Finset.sum_congr rfl
  intro x _
  have hz : (Finset.univ.filter (fun i : Fin j => zero (x i))).powerset =
      (Finset.univ : Finset (Finset (Fin j))).filter
        (fun A => A ⊆ Finset.univ.filter (fun i => zero (x i))) := by
    ext A;simp
  rw [hz,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  have hp := source_original_evolution_ghost_zero_product434 j x A zero mu alpha chi H
  have hp' := congrArg (fun r : ℝ => r/(j.factorial:ℝ)) hp
  by_cases hA : A ⊆ Finset.univ.filter (fun i : Fin j => zero (x i))
  · simp only [if_pos hA,bag_card] at hp' ⊢
    convert hp' using 1 <;> ring
  · simp only [if_neg hA,zero_div,mul_zero,bag_card] at hp' ⊢
    exact hp'
end Green64Analytic.CorrelationSquare

end

end

