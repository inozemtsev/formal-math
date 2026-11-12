module

public import Green64.Library.Weights.IndependentRowMass
public import Green64.Library.Weights.IntegerNativeRow
public import Green64.Library.Correlation.Part041

@[expose] public section

/-!
# Correlation / PhysicalRowBudget

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalRowBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
open Green64Analytic.CorrelationSquare Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local instance b661PhysicalRowFrameFintype434 :
    Fintype (MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) := by
  unfold MemoryPrimitiveEFrame
  infer_instance

/-- On one fixed actual integer position, projection to the full native
residue-and-mark state is injective. Hence a physical target sum is a
subsum of the genuine native target sum, with no mark-count multiplier. -/
theorem b661_fixed_position_native_sum_le434 (positions : Finset ℤ) (n : ℤ)
    (F : MemoryIndependentState SP sm BP bm J ell → ℝ) (hF : ∀ y, 0 ≤ F y) :
    (∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      if y.val.1.val=n then F y.val.2 else 0) ≤
      ∑ y : MemoryIndependentState SP sm BP bm J ell, F y := by
  classical
  let S := Finset.univ.filter (fun y :
    B650IntegerPhysicalState434 SP sm BP bm J ell positions => y.val.1.val=n)
  have hi : ∀ a ∈ S, ∀ b ∈ S, a.val.2=b.val.2 → a=b := by
    intro a ha b hb hab
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  calc
    _ = ∑ y ∈ S, F y.val.2 := by
      simp only [S,Finset.sum_filter]
    _ = ∑ t ∈ S.image (fun y => y.val.2), F t := by
      rw [Finset.sum_image]
      exact hi
    _ ≤ ∑ y : MemoryIndependentState SP sm BP bm J ell, F y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => hF y)

/-- The actual signed position guard fixes the target position for each
source/frame. The complete physical frame row is bounded by the SAME
native row, retaining all factors and all real frequencies. -/
theorem b661_physical_frame_absolute_row434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    (∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      ‖b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions
        q Vs Vb Knu zeta o k x y f‖) ≤
    ∑ y : MemoryIndependentState SP sm BP bm J ell,
      ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
        zeta 0 o k x.val.2 y f.1.1 f.1.2 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2‖ := by
  let n := x.val.1.val+o*k*(b650NativeFrameD434 SP sm BP bm J ell m patterns x.val.2 f:ℤ)
  let F := fun y : MemoryIndependentState SP sm BP bm J ell =>
    ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
      zeta 0 o k x.val.2 y f.1.1 f.1.2 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2‖
  calc
    _ = ∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
        if y.val.1.val=n then F y.val.2 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [b650_integer_frame_native434]
      by_cases hp : y.val.1.val=n <;>
        simp only [n] at hp ⊢ <;> simp only [hp,ite_true,ite_false,norm_zero,F]
    _ ≤ _ := b661_fixed_position_native_sum_le434 SP sm BP bm J ell positions n F
      (fun _ => norm_nonneg _)

/-- Full physical absolute row. The original auxiliary law, all four
permutation averages and the complete Knu are paid exactly once through
the proved original native row budget. No Haar mass is added. -/
theorem b661_physical_matrix_absolute_row434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hHarmonic : ∀ g, ∑ p : BP g, 1/(bm g p:ℝ)=Vb g)
    (Knu : SourcePatternK BP J ell m patterns)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu, 0 ≤ Kcap nu)
    (hK : ∀ nu aux s t, ‖Knu nu aux s t‖ ≤ Kcap nu)
    (zeta : ℝ) (o k : ℤ)
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    (∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      ‖b650IntegerPhysicalMatrix434 SP sm BP bm J ell m patterns positions
        q Vs Vb Knu zeta o k x y‖) ≤
    b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap := by
  calc
    _ ≤ ∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
        ∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
          ‖b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions
            q Vs Vb Knu zeta o k x y f‖ := by
      apply Finset.sum_le_sum
      intro y hy
      exact norm_sum_le _ _
    _ = ∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
        ∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
          ‖b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions
            q Vs Vb Knu zeta o k x y f‖ := Finset.sum_comm
    _ ≤ ∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
        ∑ y : MemoryIndependentState SP sm BP bm J ell,
          ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
            zeta 0 o k x.val.2 y f.1.1 f.1.2 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2‖ := by
      apply Finset.sum_le_sum
      intro f hf
      exact b661_physical_frame_absolute_row434 SP sm BP bm J ell m patterns
        positions q Vs Vb Knu zeta o k x f
    _ = ∑ a : MemoryIndependentOriginalRowIndex SP sm BP bm J ell m patterns,
        ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
          zeta 0 o k x.val.2
          (memoryIndependentOriginalRowOutput SP sm BP bm J ell m patterns a)
          a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1‖ := by
      simp only [MemoryPrimitiveEFrame,MemoryIndependentOriginalRowIndex,
        memoryIndependentOriginalRowOutput,Fintype.sum_prod_type,Fintype.sum_sigma]
    _ ≤ _ := b644_original_independent_absolute_row434 SP sm BP bm J ell m patterns
      q Vs Vb hq hq1 hVs hVb hHarmonic Knu Kcap hK0 hK zeta 0 o k x.val.2

/-- Full physical column bound via the proved ACTUAL reversed adjoint.
No symmetry assumption on Knu, and no second global cap, is introduced. -/
theorem b661_physical_matrix_absolute_column434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hHarmonic : ∀ g, ∑ p : BP g, 1/(bm g p:ℝ)=Vb g)
    (Knu : SourcePatternK BP J ell m patterns)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu, 0 ≤ Kcap nu)
    (hK : ∀ nu aux s t, ‖Knu nu aux s t‖ ≤ Kcap nu)
    (zeta : ℝ) (k : ℤ)
    (y : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    (∑ x : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      ‖b650IntegerPhysicalMatrix434 SP sm BP bm J ell m patterns positions
        q Vs Vb Knu zeta 1 k x y‖) ≤
    b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap := by
  have ha := b650_integer_matrix_adjoint434 SP sm BP bm J ell m patterns
    positions q Vs Vb Knu zeta k
  calc
    _ = ∑ x : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
        ‖b650IntegerPhysicalMatrix434 SP sm BP bm J ell m patterns positions
          q Vs Vb Knu zeta (-1) k y x‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [ha]
      simp only [Matrix.conjTranspose_apply,norm_star]
    _ ≤ _ := b661_physical_matrix_absolute_row434 SP sm BP bm J ell m patterns
      positions q Vs Vb hq hq1 hVs hVb hHarmonic Knu Kcap hK0 hK zeta (-1) k y
end Green64FullPhysicalE

end

end

