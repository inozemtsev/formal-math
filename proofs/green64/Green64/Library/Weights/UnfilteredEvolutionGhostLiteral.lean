module

public import Green64.Library.Weights.UnfilteredEvolutionGhostZeroDisintegration
public import Green64.Library.Weights.Part087

@[expose] public section

/-!
# Weights / UnfilteredEvolutionGhostLiteral

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredEvolutionGhostLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {U : Type} [Fintype U] [DecidableEq U]

private theorem bag_card {I : Type} [Fintype I] (x : I → U) :
    (memoryTupleBag x).card=Fintype.card I := by simp [memoryTupleBag,Multiset.card_sum]

private theorem cast_subset_sum (n j : ℕ) (hn : n=j) (x : Fin j → U)
    (zero : U → Prop) [DecidablePred zero] (f : ℕ → ℕ → Multiset U → ℝ) :
    (∑ A ∈ (Finset.univ.filter (fun i : Fin n => zero (x (Fin.cast hn i)))).powerset,
      f A.card (Finset.univ.filter (fun i : Fin n => zero (x (Fin.cast hn i)))).card
        (memoryTupleBag (fun i : {i : Fin n // i ∉ A} => x (Fin.cast hn i.val)))) =
    ∑ A ∈ (Finset.univ.filter (fun i : Fin j => zero (x i))).powerset,
      f A.card (Finset.univ.filter (fun i : Fin j => zero (x i))).card
        (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val)) := by
  subst j
  rfl

/-- Literal coefficient and output conversion for a fixed original birth
tuple. The actual output-size gate remains inside the same OLD subset sum. -/
theorem source_original_evolution_GHOST_literal_birth_tuple434
    (j B b : ℕ) (x : Fin j → U) (fresh : Fin b → U)
    (zero : U → Prop) [DecidablePred zero]
    (alpha chi gamma : ℂ) (nu : U → ℂ)
    (F H : Multiset U → ℝ) :
    (∑ A ∈ (zeroOld (List.ofFn x) zero).powerset,
      if (afterGhost (List.ofFn x) A fresh).length ≤ B then
        ‖sourceGhostTerm (List.ofFn x) zero A fresh alpha chi gamma nu‖ *
          F (List.ofFn x : Multiset U) * H (afterGhost (List.ofFn x) A fresh : Multiset U)
      else 0) =
    (‖gamma‖^b/(b.factorial:ℝ)*(∏ i,‖nu (fresh i)‖))*
      ∑ A ∈ (Finset.univ.filter (fun i : Fin j => zero (x i))).powerset,
        ‖alpha‖^A.card * ‖chi‖^((Finset.univ.filter (fun i : Fin j => zero (x i))).card-A.card) *
          (if j-A.card+b ≤ B then
            F (memoryTupleBag x) *
              H (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val)+memoryTupleBag fresh)
            else 0) := by
  simp_rw [source_original_evolution_ghost_length434,memory_source_afterGhost_bag]
  simp only [sourceGhostTerm,norm_mul,norm_pow,norm_div,norm_one,norm_prod,
    Complex.norm_natCast,zeroOld,List.length_ofFn,List.get_ofFn,Fin.cast_eq_self]
  rw [←memory_tuple_bag_ofFn x,Finset.mul_sum]
  rw [cast_subset_sum (List.ofFn x).length j (List.length_ofFn (f := x)) x zero
    (fun a z u => if j-a+b ≤ B then
      (‖alpha‖^a*‖chi‖^(z-a)*(1/(b.factorial:ℝ))*‖gamma‖^b*
        (∏ i,‖nu (fresh i)‖))*F (memoryTupleBag x)*H (u+memoryTupleBag fresh) else 0)]
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> ring

/-- Fixed OLD sector and fixed birth tuple of the original positive witness
kernel: exact 1/(k! a! b!) disintegration, including its true endpoint cap. -/
theorem source_original_evolution_GHOST_literal_FOCK_disintegration434
    (j B b : ℕ) (fresh : Fin b → U)
    (zero : U → Prop) [DecidablePred zero]
    (mu : U → ℝ) (alpha chi gamma : ℂ) (nu : U → ℂ)
    (F H : Multiset U → ℝ) :
    (∑ x : Fin j → U,(∏ i,mu (x i))/(j.factorial:ℝ) *
      ∑ A ∈ (zeroOld (List.ofFn x) zero).powerset,
        if (afterGhost (List.ofFn x) A fresh).length ≤ B then
          ‖sourceGhostTerm (List.ofFn x) zero A fresh alpha chi gamma nu‖ *
            F (List.ofFn x : Multiset U) * H (afterGhost (List.ofFn x) A fresh : Multiset U)
        else 0) =
    (‖gamma‖^b/(b.factorial:ℝ)*(∏ i,‖nu (fresh i)‖))*
      ∑ a ∈ Finset.range (j+1),1/((a.factorial:ℝ)*((j-a).factorial:ℝ))*
        (∑ v : Fin a → U,∑ u : Fin (j-a) → U,
          (∏ i,if zero (v i) then mu (v i) else 0)*
            (∏ i,mu (u i)*(if zero (u i) then ‖chi‖ else 1))*
            (‖alpha‖^a*(if j-a+b ≤ B then
              F (memoryTupleBag v+memoryTupleBag u) *
                H (memoryTupleBag u+memoryTupleBag fresh) else 0))) := by
  simp_rw [source_original_evolution_GHOST_literal_birth_tuple434]
  let f (d s : Multiset U) :=
    if s.card+b ≤ B then F d*H (s+memoryTupleBag fresh) else 0
  have hh := source_original_evolution_ghost_zero_FOCK_disintegration434
    j zero mu ‖alpha‖ ‖chi‖ f
  have hcard (A : Finset (Fin j)) (x : Fin j → U) :
      (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val)).card=j-A.card := by
    simp [bag_card,Fintype.card_subtype_compl]
  simp only [f,hcard,bag_card,Fintype.card_fin] at hh
  rw [Finset.mul_sum]
  calc
    _ = (‖gamma‖^b/(b.factorial:ℝ)*(∏ i,‖nu (fresh i)‖)) *
        (∑ x : Fin j → U,(∏ i,mu (x i))/(j.factorial:ℝ) *
          ∑ A ∈ (Finset.univ.filter (fun i : Fin j => zero (x i))).powerset,
            ‖alpha‖^A.card * ‖chi‖^((Finset.univ.filter (fun i : Fin j => zero (x i))).card-A.card) *
              (if j-A.card+b ≤ B then F (memoryTupleBag x) *
                H (memoryTupleBag (fun i : {i : Fin j // i ∉ A} => x i.val)+memoryTupleBag fresh)
              else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hh,Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

end

