module

public import Green64.Library.Weights.Part088
public import Green64.Library.Correlation.PhysicalGhostWitnessCollapse

@[expose] public section

/-!
# Weights / UnfilteredEvolutionGhostKernel

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredEvolutionGhostKernel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {U : Type} [Fintype U] [DecidableEq U]

private theorem fock_sum (B : ℕ) (f : (j : ℕ) → (Fin j → U) → ℝ) :
    (∑ x : FockState U B,f x.1.val x.2) =
    ∑ j ∈ Finset.range (B+1),∑ x : Fin j → U,f j x := by
  change (∑ x : Σ j : Fin (B+1),Fin j.val → U,f x.1.val x.2)=_
  rw [Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range (fun j => ∑ x : Fin j → U,f j x) (B+1)

/-- The sum of norms of the original ordered ghost witnesses, before any
cancellation. This is not the norm of their sum. -/
def sourceOriginalUnfilteredEvolutionGhostPositive434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero]
    (alpha chi gamma : ℂ) (nu : U → ℂ) (x y : FockState U B) : ℝ :=
  ∑ c : GhostWitnessChoice (fockToList x) zero B,
    ‖ghostWitnessTerm (fockToList x) (fockToList y) zero B alpha chi gamma nu c‖

theorem source_original_evolution_GHOST_one_output434
    (B : ℕ) (old : List U) (zero : U → Prop) [DecidablePred zero]
    (alpha chi gamma : ℂ) (nu : U → ℂ)
    (c : GhostWitnessChoice old zero B) (H : Multiset U → ℝ) :
    (∑ y : FockState U B,
      ‖ghostWitnessTerm old (fockToList y) zero B alpha chi gamma nu c‖ *
        H (fockMultiset y)) =
    if (afterGhost old c.1.1 c.2.2).length ≤ B then
      ‖sourceGhostTerm old zero c.1.1 c.2.2 alpha chi gamma nu‖ *
        H (afterGhost old c.1.1 c.2.2 : Multiset U)
    else 0 := by
  let out := afterGhost old c.1.1 c.2.2
  by_cases hc : out.length ≤ B
  · let y0 := sourceOriginalFockFromList434 out hc
    have hy : fockToList y0=out := source_original_fock_to_from_list434 out hc
    have he (y : FockState U B) : out=fockToList y ↔ y=y0 := by
      constructor
      · intro h
        apply source_original_fock_to_list_injective434
        exact h.symm.trans hy.symm
      · intro h
        subst y
        exact hy.symm
    simp only [show (afterGhost old c.1.1 c.2.2).length ≤ B from hc,if_true,
      ghostWitnessTerm]
    change (∑ y : FockState U B,
      ‖if out=fockToList y then sourceGhostTerm old zero c.1.1 c.2.2 alpha chi gamma nu else 0‖ *
        H (fockMultiset y)) = _
    simp only [he,apply_ite,norm_zero,ite_mul,zero_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ,if_true]
    have hbag : fockMultiset y0=(out : Multiset U) := congrArg (fun l : List U => (l : Multiset U)) hy
    rw [hbag]
  · have he (y : FockState U B) : out ≠ fockToList y := by
      intro h
      apply hc
      rw [h,fockToList_length]
      exact Nat.le_of_lt_succ y.1.isLt
    simp only [show ¬(afterGhost old c.1.1 c.2.2).length ≤ B from hc,if_false]
    apply Finset.sum_eq_zero
    intro y _
    simp only [ghostWitnessTerm,show afterGhost old c.1.1 c.2.2 ≠ fockToList y from he y,
      if_false,norm_zero,zero_mul]

theorem source_original_evolution_GHOST_positive_output434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero]
    (alpha chi gamma : ℂ) (nu : U → ℂ) (x : FockState U B)
    (H : Multiset U → ℝ) :
    (∑ y : FockState U B,
      sourceOriginalUnfilteredEvolutionGhostPositive434 B zero alpha chi gamma nu x y *
        H (fockMultiset y)) =
    ∑ c : GhostWitnessChoice (fockToList x) zero B,
      if (afterGhost (fockToList x) c.1.1 c.2.2).length ≤ B then
        ‖sourceGhostTerm (fockToList x) zero c.1.1 c.2.2 alpha chi gamma nu‖ *
          H (afterGhost (fockToList x) c.1.1 c.2.2 : Multiset U)
      else 0 := by
  unfold sourceOriginalUnfilteredEvolutionGhostPositive434
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [source_original_evolution_GHOST_one_output434]

/-- Exact equality to the original factorial Fock-state positive kernel. -/
theorem source_original_evolution_GHOST_joint_kernel434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (alpha chi gamma : ℂ) (F H : Multiset U → ℝ) :
    sourceOriginalUnfilteredEvolutionGhostJoint434 B zero mu alpha chi gamma F H =
    ∑ x : FockState U B,fockMass mu x*F (fockMultiset x)*
      ∑ y : FockState U B,
        sourceOriginalUnfilteredEvolutionGhostPositive434 B zero alpha chi gamma
          (fun u => ((if zero u then mu u else 0:ℝ):ℂ)) x y * H (fockMultiset y) := by
  simp_rw [source_original_evolution_GHOST_positive_output434]
  rw [source_original_evolution_GHOST_joint_row_expression434]
  simp only [fockMass,fockMultiset,fockToList]
  exact (fock_sum B
    (fun j (x : Fin j → U) =>
      (∏ i,mu (x i))/(j.factorial:ℝ)*F (List.ofFn x : Multiset U)*
        ∑ c : GhostWitnessChoice (List.ofFn x) zero B,
          if (afterGhost (List.ofFn x) c.1.1 c.2.2).length ≤ B then
            ‖sourceGhostTerm (List.ofFn x) zero c.1.1 c.2.2 alpha chi gamma
              (fun u => ((if zero u then mu u else 0:ℝ):ℂ))‖ *
              H (afterGhost (List.ofFn x) c.1.1 c.2.2 : Multiset U) else 0)
    ).symm

/-- True density column for the original positive kernel, tested on arbitrary
nonnegative symmetric targets. The source and target use the same 1/j! law. -/
theorem source_original_evolution_GHOST_kernel_column434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (hmu : ∀ u,0 ≤ mu u) (alpha chi gamma : ℂ)
    (w : ℝ) (hw : 0<w) (hc : ‖gamma‖/w+‖chi‖ ≤ 1)
    (H : Multiset U → ℝ) (hH : ∀ m,0 ≤ H m) :
    (∑ x : FockState U B,fockMass mu x*w^x.1.val*
      ∑ y : FockState U B,
        sourceOriginalUnfilteredEvolutionGhostPositive434 B zero alpha chi gamma
          (fun u => ((if zero u then mu u else 0:ℝ):ℂ)) x y * H (fockMultiset y)) ≤
    Real.exp (‖alpha‖*w*(∑ u : U,if zero u then mu u else 0)) *
      (∑ y : FockState U B,fockMass mu y*H (fockMultiset y)*w^y.1.val) := by
  have hh := source_original_evolution_GHOST_joint_column434 B zero mu hmu
    alpha chi gamma w hw hc H hH
  rw [source_original_evolution_GHOST_joint_kernel434] at hh
  simp only [fockMultiset,Multiset.coe_card,List.length_ofFn] at hh
  have he : (∑ y : FockState U B,fockMass mu y*H (fockMultiset y)*w^y.1.val) =
      ∑ j ∈ Finset.range (B+1),∑ x : Fin j → U,
        (∏ i,mu (x i))/(j.factorial:ℝ)*H (List.ofFn x : Multiset U)*w^j := by
    simp only [fockMass,fockMultiset]
    exact fock_sum B
      (fun j x => (∏ i,mu (x i))/(j.factorial:ℝ)*H (List.ofFn x : Multiset U)*w^j)
  rw [←he] at hh
  exact hh
end Green64Analytic.CorrelationSquare

end

end

