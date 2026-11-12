module

public import Green64.Library.Correlation.Part008
public import Green64.Library.Correlation.Part046
public import Green64.Library.Correlation.Part044
public import Green64.Library.Weights.Part054

@[expose] public section

/-!
# Weights / IndependentRowMass

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## IndependentRowMass -/

section

open scoped Classical
open scoped BigOperators
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The exact row cost keeps the complete Nu family and its actual shared-slot counts. -/
def b644IndependentRowBudget434 (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Kcap : Nu → ℝ) : ℝ :=
  ∑ nu : Nu, Kcap nu * (∏ g : SG, memorySmallRowConstant q (Vs g) ell) *
    ∏ g : BG, memorySmallRowConstant q (Vb g)
      (unsharedSlots (J+ell) (sourceBigShared J ell m (patterns nu) g))

private theorem row_constant_nonneg (q V : ℝ) (t : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hV : 0 < V) :
    0 ≤ memorySmallRowConstant q V t := by
  have hs : Real.sqrt q < 1 := by
    nlinarith only [Real.sq_sqrt hq.le, Real.sqrt_nonneg q, hq1]
  have hd : 0 < 1 - Real.sqrt q := sub_pos.mpr hs
  unfold memorySmallRowConstant
  positivity

omit [DecidableEq SG] [DecidableEq BG] in
theorem b644_independent_row_budget_nonneg434
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0 < q) (hq1 : q < 1)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu, 0 ≤ Kcap nu) :
    0 ≤ b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap := by
  apply Finset.sum_nonneg
  intro nu hnu
  exact mul_nonneg (mul_nonneg (hK0 nu)
    (Finset.prod_nonneg (fun g _ => row_constant_nonneg q (Vs g) ell hq hq1 (hVs g))))
    (Finset.prod_nonneg (fun g _ => row_constant_nonneg q (Vb g) _ hq hq1 (hVb g)))

omit [Fintype Nu] in
private theorem original_packet_bound
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0 < q) (hq1 : q < 1)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (Knu : SourcePatternK BP J ell m patterns)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu, 0 ≤ Kcap nu)
    (hK : ∀ nu aux s t, ‖Knu nu aux s t‖ ≤ Kcap nu)
    (zeta theta : ℝ) (o k : ℤ)
    (x : MemoryIndependentState SP sm BP bm J ell)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : GroupPermFamily (G := SG) (J+ell)) :
    (∑ y : MemoryIndependentState SP sm BP bm J ell,
      ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
        zeta theta o k x y nu aux bs bt ss st‖) ≤
    ‖(sourceAuxMass BP bm J m Vb (patterns nu) aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      (groupPermutationPairMass (G := SG) (J+ell) : ℂ)‖ *
    (Kcap nu * (∏ g : SG, memorySmallRowConstant q (Vs g) ell) *
      ∏ g : BG, memorySmallRowConstant q (Vb g)
        (unsharedSlots (J+ell) (sourceBigShared J ell m (patterns nu) g))) := by
  classical
  let D := memoryIndependentD SP sm BP bm J ell m (patterns nu) aux x bs ss
  let delta := o*k*(D : ℤ)
  let W := ‖(sourceAuxMass BP bm J m Vb (patterns nu) aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      (groupPermutationPairMass (G := SG) (J+ell) : ℂ)‖
  let Cs := ∏ g : SG, memorySmallRowConstant q (Vs g) ell
  let Cb := ∏ g : BG, memorySmallRowConstant q (Vb g)
    (unsharedSlots (J+ell) (sourceBigShared J ell m (patterns nu) g))
  have hCs : 0 ≤ Cs :=
    Finset.prod_nonneg (fun g _ => row_constant_nonneg q (Vs g) ell hq hq1 (hVs g))
  have hCb : 0 ≤ Cb :=
    Finset.prod_nonneg (fun g _ => row_constant_nonneg q (Vb g) _ hq hq1 (hVb g))
  have hW : 0 ≤ W := norm_nonneg _
  change _ ≤ W * (Kcap nu * Cs * Cb)
  by_cases ho : o = 1 ∨ o = -1
  · let scalar := fun yb : GroupState BP bm (J+ell) =>
      originalEdgeScalar (memoryOrientationK BP J ell m patterns Knu o nu aux
        (fun g i => marks (bm g) (J+ell) (x.2 g) (bs g i))
        (fun g i => marks (bm g) (J+ell) (yb g) (bt g i))) zeta theta D o k
    let bk := fun yb : GroupState BP bm (J+ell) =>
      groupPermutedKernel BP bm (J+ell) q Vb
        (sourceBigShared J ell m (patterns nu)) delta (fun _ _ => 1) bs bt x.2 yb
    let sk := fun (yb : GroupState BP bm (J+ell)) (ys : GroupState SP sm (J+ell)) =>
      groupPermutedKernel SP sm (J+ell) q Vs (sourceSmallShared J ell)
        delta (fun _ _ => scalar yb) ss st x.1 ys
    have hs (yb) : ‖scalar yb‖ ≤ Kcap nu := by
      dsimp only [scalar]
      rw [source_original_edge_scalar_norm434 _ _ _ _ _ _ ho]
      unfold memoryOrientationK
      split_ifs <;> exact hK _ _ _ _
    have hsk (yb) : (∑ ys : GroupState SP sm (J+ell), ‖sk yb ys‖) ≤
        Kcap nu * Cs :=
      (source_original_memory_SOURCE_SMALL_group_kernel_row434 SP sm J ell
        q Vs hq hq1 hVs delta (fun _ _ => scalar yb) ss st x.1).trans
        (mul_le_mul_of_nonneg_right (hs yb) hCs)
    have hbk : (∑ yb : GroupState BP bm (J+ell), ‖bk yb‖) ≤ Cb := by
      simpa only [norm_one, one_mul] using
        source_original_memory_SMALL_group_kernel_row434 BP bm (J+ell)
          q Vb hq hq1 hVb (sourceBigShared J ell m (patterns nu))
          delta (fun _ _ => 1) bs bt x.2
    have hp (ys : GroupState SP sm (J+ell)) (yb : GroupState BP bm (J+ell)) :
        ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
          zeta theta o k x (ys,yb) nu aux bs bt ss st‖ ≤ W * ‖bk yb‖ * ‖sk yb ys‖ := by
      unfold memoryIndependentRowScalar
      dsimp only
      split_ifs
      · dsimp only [W, bk, sk, scalar, D, delta]
        simp only [norm_mul]
        exact le_rfl
      · rw [norm_zero]
        positivity
    calc
      _ = ∑ yb : GroupState BP bm (J+ell), ∑ ys : GroupState SP sm (J+ell),
          ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
            zeta theta o k x (ys,yb) nu aux bs bt ss st‖ := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ ≤ ∑ yb : GroupState BP bm (J+ell), (W * ‖bk yb‖) * (Kcap nu * Cs) := by
        apply Finset.sum_le_sum
        intro yb hyb
        calc
          _ ≤ ∑ ys : GroupState SP sm (J+ell), (W * ‖bk yb‖) * ‖sk yb ys‖ :=
            Finset.sum_le_sum (fun ys _ => hp ys yb)
          _ = (W * ‖bk yb‖) * ∑ ys : GroupState SP sm (J+ell), ‖sk yb ys‖ :=
            (Finset.mul_sum _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (hsk yb) (mul_nonneg hW (norm_nonneg _))
      _ = (W * (Kcap nu * Cs)) * ∑ yb : GroupState BP bm (J+ell), ‖bk yb‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro yb hyb
        ring
      _ ≤ (W * (Kcap nu * Cs)) * Cb :=
        mul_le_mul_of_nonneg_left hbk (mul_nonneg hW (mul_nonneg (hK0 nu) hCs))
      _ = _ := by ring
  · have hz (y : MemoryIndependentState SP sm BP bm J ell) :
        memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
          zeta theta o k x y nu aux bs bt ss st = 0 := by
      simp [memoryIndependentRowScalar, ho]
    simp only [hz, norm_zero, Finset.sum_const_zero]
    exact mul_nonneg hW (mul_nonneg (mul_nonneg (hK0 nu) hCs) hCb)

/-- Complete original independent row, with the actual auxiliary law, all four
permutation averages, signed Knu, physical bans and both genuine kernels. -/
theorem b644_original_independent_absolute_row434
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0 < q) (hq1 : q < 1)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hHarmonic : ∀ g, ∑ p : BP g, 1/(bm g p : ℝ) = Vb g)
    (Knu : SourcePatternK BP J ell m patterns)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu, 0 ≤ Kcap nu)
    (hK : ∀ nu aux s t, ‖Knu nu aux s t‖ ≤ Kcap nu)
    (zeta theta : ℝ) (o k : ℤ)
    (x : MemoryIndependentState SP sm BP bm J ell) :
    (∑ a : MemoryIndependentOriginalRowIndex SP sm BP bm J ell m patterns,
      ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
        zeta theta o k x
        (memoryIndependentOriginalRowOutput SP sm BP bm J ell m patterns a)
        a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1‖) ≤
    b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap := by
  classical
  simp only [MemoryIndependentOriginalRowIndex, Fintype.sum_sigma,
    Fintype.sum_prod_type, memoryIndependentOriginalRowOutput,
    b644IndependentRowBudget434]
  apply Finset.sum_le_sum
  intro nu hnu
  let C := Kcap nu * (∏ g : SG, memorySmallRowConstant q (Vs g) ell) *
    ∏ g : BG, memorySmallRowConstant q (Vb g)
      (unsharedSlots (J+ell) (sourceBigShared J ell m (patterns nu) g))
  calc
    _ ≤ ∑ aux : SourceBigAux BP J m (patterns nu),
      ∑ bs : BigGroupPerm (BG := BG) (J+ell),
      ∑ bt : BigGroupPerm (BG := BG) (J+ell),
      ∑ ss : GroupPermFamily (G := SG) (J+ell),
      ∑ st : GroupPermFamily (G := SG) (J+ell),
        ‖(sourceAuxMass BP bm J m Vb (patterns nu) aux : ℂ) *
          (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
          (groupPermutationPairMass (G := SG) (J+ell) : ℂ)‖ * C := by
      apply Finset.sum_le_sum; intro aux haux
      apply Finset.sum_le_sum; intro bs hbs
      apply Finset.sum_le_sum; intro bt hbt
      apply Finset.sum_le_sum; intro ss hss
      apply Finset.sum_le_sum; intro st hst
      simpa only [Fintype.sum_prod_type] using original_packet_bound SP sm BP bm J ell m patterns
        q Vs Vb hq hq1 hVs hVb Knu Kcap hK0 hK zeta theta o k x nu aux bs bt ss st
    _ = 1 * C := by
      simp only [← Finset.sum_mul]
      congr 1
      exact source_original_memory_ALL_OUTER_total_mass434
        (SG := SG) BP bm J ell m Vb hVb hHarmonic (patterns nu)
    _ = _ := one_mul C
end Green64Analytic.CorrelationSquare

end

end

