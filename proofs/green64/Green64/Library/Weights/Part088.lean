module

public import Green64.Library.Weights.UnfilteredEvolutionGhostLiteral

@[expose] public section

/-!
# Weights / Part088

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredEvolutionGhostJoint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {U : Type} [Fintype U] [DecidableEq U]

/-- Canonical survivor/deletion/birth integral, used only through its exact
equality to the original factorial witness sum below. -/
def sourceOriginalUnfilteredEvolutionGhostSector434
    (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (alpha chi gamma : ℂ) (F H : Multiset U → ℝ) (k a b : ℕ) : ℝ :=
  ∑ v : Fin a → U, ∑ u : Fin k → U, ∑ z : Fin b → U,
    (∏ i,if zero (v i) then mu (v i) else 0) *
    (∏ i,mu (u i)*(if zero (u i) then ‖chi‖ else 1)) *
    (∏ i,if zero (z i) then mu (z i) else 0) *
    (‖alpha‖^a*‖gamma‖^b/((a.factorial:ℝ)*(k.factorial:ℝ)*(b.factorial:ℝ))) *
    F (memoryTupleBag v+memoryTupleBag u) *
    H (memoryTupleBag u+memoryTupleBag z)

theorem source_original_evolution_GHOST_sector_reverse434
    (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (alpha chi gamma : ℂ) (F H : Multiset U → ℝ) (k a b : ℕ) :
    sourceOriginalUnfilteredEvolutionGhostSector434 zero mu alpha chi gamma F H k a b =
    sourceOriginalUnfilteredEvolutionGhostSector434 zero mu gamma chi alpha H F k b a := by
  unfold sourceOriginalUnfilteredEvolutionGhostSector434
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [add_comm (memoryTupleBag z),add_comm (memoryTupleBag u) (memoryTupleBag v)]
  ring

/-- Literal original positive ghost pairing, with source 1/j! mass and
the original afterGhost output cap. No orbit representatives are removed. -/
def sourceOriginalUnfilteredEvolutionGhostJoint434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (alpha chi gamma : ℂ) (F H : Multiset U → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (B+1), ∑ b ∈ Finset.range (B+1), ∑ fresh : Fin b → U,
    ∑ x : Fin j → U,(∏ i,mu (x i))/(j.factorial:ℝ) *
      ∑ A ∈ (zeroOld (List.ofFn x) zero).powerset,
        if (afterGhost (List.ofFn x) A fresh).length ≤ B then
          ‖sourceGhostTerm (List.ofFn x) zero A fresh alpha chi gamma
            (fun u => ((if zero u then mu u else 0:ℝ):ℂ))‖ *
            F (List.ofFn x : Multiset U) * H (afterGhost (List.ofFn x) A fresh : Multiset U)
        else 0

theorem source_original_evolution_GHOST_joint_disintegration434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (hmu : ∀ u,0 ≤ mu u) (alpha chi gamma : ℂ) (F H : Multiset U → ℝ) :
    sourceOriginalUnfilteredEvolutionGhostJoint434 B zero mu alpha chi gamma F H =
    ∑ j ∈ Finset.range (B+1),∑ a ∈ Finset.range (B+1),∑ b ∈ Finset.range (B+1),
      if a ≤ j ∧ j-a+b ≤ B then
        sourceOriginalUnfilteredEvolutionGhostSector434 zero mu alpha chi gamma F H (j-a) a b
      else 0 := by
  have hn (u : U) : ‖((if zero u then mu u else 0:ℝ):ℂ)‖ =
      if zero u then mu u else 0 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    split_ifs
    · exact hmu u
    · exact le_rfl
  unfold sourceOriginalUnfilteredEvolutionGhostJoint434
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm (s := Finset.range (B+1)) (t := Finset.range (B+1))]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [source_original_evolution_GHOST_literal_FOCK_disintegration434,hn]
  conv_lhs => arg 2; ext fresh; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsector (a : ℕ) :
      (∑ fresh : Fin b → U,
        (‖gamma‖^b/(b.factorial:ℝ)*(∏ i,if zero (fresh i) then mu (fresh i) else 0))*
          (1/((a.factorial:ℝ)*((j-a).factorial:ℝ))*
            (∑ v : Fin a → U,∑ u : Fin (j-a) → U,
              (∏ i,if zero (v i) then mu (v i) else 0)*
                (∏ i,mu (u i)*(if zero (u i) then ‖chi‖ else 1))*
                (‖alpha‖^a*(if j-a+b ≤ B then
                  F (memoryTupleBag v+memoryTupleBag u)*
                  H (memoryTupleBag u+memoryTupleBag fresh) else 0))))) =
        if j-a+b ≤ B then
          sourceOriginalUnfilteredEvolutionGhostSector434 zero mu alpha chi gamma F H (j-a) a b
        else 0 := by
    by_cases hc : j-a+b ≤ B
    · simp only [if_pos hc]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext v; rw [Finset.sum_comm]
      unfold sourceOriginalUnfilteredEvolutionGhostSector434
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro fresh _
      ring
    · simp [hc]
  simp_rw [hsector]
  calc
    _ = ∑ a ∈ Finset.range (j+1),
        if a ≤ j ∧ j-a+b ≤ B then
          sourceOriginalUnfilteredEvolutionGhostSector434 zero mu alpha chi gamma F H (j-a) a b
        else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Nat.le_of_lt_succ (Finset.mem_range.mp ha),true_and]
    _ = _ := by
      apply Finset.sum_subset
      · intro a ha
        simp only [Finset.mem_range] at *
        omega
      · intro a ha hnot
        have hn : ¬a ≤ j := by simp only [Finset.mem_range] at hnot; omega
        simp [hn]

/-- Exact symmetric joint reversal of the ACTUAL positive ghost witness
pairing. Both endpoint caps and all multiplicity factorials are retained. -/
theorem source_original_evolution_GHOST_joint_reverse434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (hmu : ∀ u,0 ≤ mu u) (alpha chi gamma : ℂ) (F H : Multiset U → ℝ) :
    sourceOriginalUnfilteredEvolutionGhostJoint434 B zero mu alpha chi gamma F H =
    sourceOriginalUnfilteredEvolutionGhostJoint434 B zero mu gamma chi alpha H F := by
  rw [source_original_evolution_GHOST_joint_disintegration434 B zero mu hmu,
    source_original_evolution_GHOST_joint_disintegration434 B zero mu hmu]
  rw [source_original_evolution_GHOST_sector_exchange434]
  simp_rw [source_original_evolution_GHOST_sector_reverse434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostColumn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {U : Type} [Fintype U] [DecidableEq U]

theorem source_original_evolution_GHOST_witness_reindex434
    (old : List U) (zero : U → Prop) [DecidablePred zero] (B : ℕ)
    (f : (A : Finset (Fin old.length)) → (b : ℕ) → (Fin b → U) → ℝ) :
    (∑ c : GhostWitnessChoice old zero B,f c.1.1 c.2.1.val c.2.2) =
    ∑ b ∈ Finset.range (B+1),∑ fresh : Fin b → U,
      ∑ A ∈ (zeroOld old zero).powerset,f A b fresh := by
  simp only [GhostWitnessChoice,Fintype.sum_sigma]
  have hfin (A : Finset (Fin old.length)) :
      (∑ b : Fin (B+1),∑ fresh : Fin b.val → U,f A b.val fresh) =
      ∑ b ∈ Finset.range (B+1),∑ fresh : Fin b → U,f A b fresh :=
    Fin.sum_univ_eq_sum_range (fun b => ∑ fresh : Fin b → U,f A b fresh) (B+1)
  simp_rw [hfin]
  rw [←Finset.sum_subtype (zeroOld old zero).powerset (fun A => Iff.rfl)
    (fun A => ∑ b ∈ Finset.range (B+1),∑ fresh : Fin b → U,f A b fresh)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

/-- Exact source pairing as the original indexed ghost witness row. -/
theorem source_original_evolution_GHOST_joint_row_expression434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (alpha chi gamma : ℂ) (F H : Multiset U → ℝ) :
    sourceOriginalUnfilteredEvolutionGhostJoint434 B zero mu alpha chi gamma F H =
    ∑ j ∈ Finset.range (B+1),∑ x : Fin j → U,
      (∏ i,mu (x i))/(j.factorial:ℝ)*F (List.ofFn x : Multiset U)*
        ∑ c : GhostWitnessChoice (List.ofFn x) zero B,
          if (afterGhost (List.ofFn x) c.1.1 c.2.2).length ≤ B then
            ‖sourceGhostTerm (List.ofFn x) zero c.1.1 c.2.2 alpha chi gamma
              (fun u => ((if zero u then mu u else 0:ℝ):ℂ))‖ *
              H (afterGhost (List.ofFn x) c.1.1 c.2.2 : Multiset U)
          else 0 := by
  unfold sourceOriginalUnfilteredEvolutionGhostJoint434
  apply Finset.sum_congr rfl
  intro j _
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [source_original_evolution_GHOST_witness_reindex434 (List.ofFn x) zero B
    (fun A b fresh => if (afterGhost (List.ofFn x) A fresh).length ≤ B then
      ‖sourceGhostTerm (List.ofFn x) zero A fresh alpha chi gamma
        (fun u => ((if zero u then mu u else 0:ℝ):ℂ))‖ *
      H (afterGhost (List.ofFn x) A fresh : Multiset U) else 0)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro fresh _
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> ring

/-- True source factorial-density weighted row bound, tested against every
nonnegative symmetric source function. Repeated OLD atoms are unrestricted. -/
theorem source_original_evolution_GHOST_joint_row434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (hmu : ∀ u,0 ≤ mu u) (alpha chi gamma : ℂ)
    (w : ℝ) (hw : 0<w) (hc : ‖alpha‖/w+‖chi‖ ≤ 1)
    (F : Multiset U → ℝ) (hF : ∀ m,0 ≤ F m) :
    sourceOriginalUnfilteredEvolutionGhostJoint434 B zero mu alpha chi gamma F
      (fun m => w^m.card) ≤
    Real.exp (‖gamma‖*w*(∑ u : U,if zero u then mu u else 0)) *
      (∑ j ∈ Finset.range (B+1),∑ x : Fin j → U,
        (∏ i,mu (x i))/(j.factorial:ℝ)*F (List.ofFn x : Multiset U)*w^j) := by
  have hn (u : U) : ‖((if zero u then mu u else 0:ℝ):ℂ)‖ =
      if zero u then mu u else 0 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    split_ifs
    · exact hmu u
    · exact le_rfl
  rw [source_original_evolution_GHOST_joint_row_expression434,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hr := source_original_evolution_GHOST_weighted_row434
    (List.ofFn x) zero B alpha chi gamma
    (fun u => ((if zero u then mu u else 0:ℝ):ℂ)) w hw hc
  simp only [hn,List.length_ofFn] at hr
  have hcap :
      (∑ c : GhostWitnessChoice (List.ofFn x) zero B,
        if (afterGhost (List.ofFn x) c.1.1 c.2.2).length ≤ B then
          ‖sourceGhostTerm (List.ofFn x) zero c.1.1 c.2.2 alpha chi gamma
            (fun u => ((if zero u then mu u else 0:ℝ):ℂ))‖ *
            w^(afterGhost (List.ofFn x) c.1.1 c.2.2).length
        else 0) ≤
      Real.exp (‖gamma‖*w*(∑ u : U,if zero u then mu u else 0))*w^j := by
    apply le_trans _ hr
    apply Finset.sum_le_sum
    intro c _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (norm_nonneg _) (pow_nonneg hw.le _)
  have hm : 0 ≤ (∏ i,mu (x i))/(j.factorial:ℝ)*F (List.ofFn x : Multiset U) :=
    mul_nonneg (div_nonneg (Finset.prod_nonneg (fun i _ => hmu _))
      (Nat.cast_nonneg _)) (hF _)
  simpa only [Multiset.coe_card,mul_assoc,mul_left_comm,mul_comm] using
    mul_le_mul_of_nonneg_left hcap hm

/-- True source-density column bound. It is derived by reversing the
complete joint factorial kernel, not by reversing ordered append lists. -/
theorem source_original_evolution_GHOST_joint_column434
    (B : ℕ) (zero : U → Prop) [DecidablePred zero] (mu : U → ℝ)
    (hmu : ∀ u,0 ≤ mu u) (alpha chi gamma : ℂ)
    (w : ℝ) (hw : 0<w) (hc : ‖gamma‖/w+‖chi‖ ≤ 1)
    (H : Multiset U → ℝ) (hH : ∀ m,0 ≤ H m) :
    sourceOriginalUnfilteredEvolutionGhostJoint434 B zero mu alpha chi gamma
      (fun m => w^m.card) H ≤
    Real.exp (‖alpha‖*w*(∑ u : U,if zero u then mu u else 0)) *
      (∑ j ∈ Finset.range (B+1),∑ x : Fin j → U,
        (∏ i,mu (x i))/(j.factorial:ℝ)*H (List.ofFn x : Multiset U)*w^j) := by
  rw [source_original_evolution_GHOST_joint_reverse434 B zero mu hmu]
  exact source_original_evolution_GHOST_joint_row434 B zero mu hmu gamma chi alpha
    w hw hc H hH
end Green64Analytic.CorrelationSquare

end

end

