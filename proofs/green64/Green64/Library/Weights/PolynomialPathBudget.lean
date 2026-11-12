module

public import Green64.Library.Weights.IndependentRowMass
public import Green64.Library.Correlation.Part045

@[expose] public section

/-!
# Weights / PolynomialPathBudget

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PolynomialPathBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Fixed slot cost only; it does not count prime choices or physical states. -/
def b644FiniteSlotCost434 (q v : ℝ) (M : ℕ) : ℝ :=
  1 + ∑ t ∈ Finset.range (M+1), memorySmallRowConstant q v t

private theorem rc_nonneg (q V : ℝ) (t : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hV : 0 < V) :
    0 ≤ memorySmallRowConstant q V t := by
  have hs : Real.sqrt q < 1 := by
    nlinarith only [Real.sq_sqrt hq.le, Real.sqrt_nonneg q, hq1]
  have hd : 0 < 1 - Real.sqrt q := sub_pos.mpr hs
  unfold memorySmallRowConstant
  positivity

private theorem slot_cost_one (q v : ℝ) (M : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hv : 0 < v) :
    1 ≤ b644FiniteSlotCost434 q v M := by
  have hs := Finset.sum_nonneg (s := Finset.range (M+1))
    (fun t _ => rc_nonneg q v t hq hq1 hv)
  dsimp [b644FiniteSlotCost434]
  linarith

private theorem row_le_slot_cost (q v V : ℝ) (M t : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hv : 0 < v) (hV : v ≤ V) (ht : t ≤ M) :
    memorySmallRowConstant q V t ≤ b644FiniteSlotCost434 q v M := by
  have hs : Real.sqrt q < 1 := by
    nlinarith only [Real.sq_sqrt hq.le, Real.sqrt_nonneg q, hq1]
  have hd : 0 < 1 - Real.sqrt q := sub_pos.mpr hs
  have hmono : memorySmallRowConstant q V t ≤ memorySmallRowConstant q v t := by
    apply mul_le_mul_of_nonneg_right
    · exact one_div_le_one_div_of_le (pow_pos hv t) (pow_le_pow_left₀ hv.le hV t)
    · positivity
  have hsum := Finset.single_le_sum (fun i _ => rc_nonneg q v i hq hq1 hv)
    (show t ∈ Finset.range (M+1) from Finset.mem_range.mpr (by omega))
  dsimp only [b644FiniteSlotCost434]
  linarith

/-- All original groups, including varying shared-slot counts, cost a
fixed power of L. The constant is chosen before L and every path. -/
theorem b644_group_absolute_row_polynomial434
    {G : Type} [Fintype G] (q v C0 L : ℝ) (M : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hv : 0 < v) (hL : 1 ≤ L)
    (V : G → ℝ) (hV : ∀ g, v ≤ V g)
    (t : G → ℕ) (ht : ∀ g, t g ≤ M)
    (hGroups : (Fintype.card G : ℝ) ≤ C0*Real.log L) :
    (∏ g : G, memorySmallRowConstant q (V g) (t g)) ≤
      L^(C0*Real.log (b644FiniteSlotCost434 q v M)) := by
  let C := b644FiniteSlotCost434 q v M
  have hC1 : 1 ≤ C := slot_cost_one q v M hq hq1 hv
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  calc
    _ ≤ ∏ _g : G, C := Finset.prod_le_prod₀
      (fun g _ => rc_nonneg q (V g) (t g) hq hq1 (hv.trans_le (hV g)))
      (fun g _ => row_le_slot_cost q v (V g) M (t g) hq hq1 hv (hV g) (ht g))
    _ = C^(Fintype.card G) := by simp only [Finset.prod_const, Finset.card_univ]
    _ ≤ L^(C0*Real.log C) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hC, Real.rpow_def_of_pos hL0]
      apply Real.exp_le_exp.mpr
      calc
        Real.log C * (Fintype.card G : ℝ) ≤ Real.log C * (C0*Real.log L) :=
          mul_le_mul_of_nonneg_left hGroups hlogC
        _ = Real.log L * (C0*Real.log C) := by ring

def b644RawComparisonExponent434 (M m Cq Cxi : ℕ) (q v C0 : ℝ) : ℝ :=
  (m : ℝ)*(2*C0)*Real.log 2 + ((4*Cq+2*Cxi : ℕ) : ℝ) + 1 +
    2*(C0*Real.log (b644FiniteSlotCost434 q v M))

/-- Full RAW and complete two-block comparison budget; both SMALL and
BIG are the original independent kernels, with arbitrary full physical Knu
to be instantiated by its proved canonical cap. -/
theorem b644_raw_comparison_absolute_row_polynomial434
    {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]
    (blockA blockB : Finset BG) (J ell m Q Cq Cxi : ℕ) (hmJ : m ≤ J)
    (q v C0 L xi : ℝ) (hq : 0 < q) (hq1 : q < 1) (hv : 0 < v)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hxi : 0 < xi)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (hVs : ∀ g, v ≤ Vs g) (hVb : ∀ g, v ≤ Vb g)
    (hGs : (Fintype.card SG : ℝ) ≤ C0*Real.log L)
    (hGb : (Fintype.card BG : ℝ) ≤ C0*Real.log L)
    (hQ : (Q : ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi) :
    b644IndependentRowBudget434 J ell m
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ) q Vs Vb
      (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi) ≤
    L^(b644RawComparisonExponent434 (J+ell) m Cq Cxi q v C0) := by
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let cap := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
  let G : ℝ := C0*Real.log (b644FiniteSlotCost434 q v (J+ell))
  let B : ℝ := (m:ℝ)*(2*C0)*Real.log 2 + ((4*Cq+2*Cxi:ℕ):ℝ)+1
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hblocks : (((blockA.card+blockB.card : ℕ) : ℝ)) ≤ (2*C0)*Real.log L := by
    have ha : (blockA.card : ℝ) ≤ (Fintype.card BG : ℝ) := by exact_mod_cast Finset.card_le_univ blockA
    have hb : (blockB.card : ℝ) ≤ (Fintype.card BG : ℝ) := by exact_mod_cast Finset.card_le_univ blockB
    rw [Nat.cast_add]
    nlinarith
  have hsum : (∑ nu, cap nu) ≤ L^B :=
    source_original_memory_RAW_COMPARISON_cap_budget434 blockA blockB m Q L (2*C0)
      xi Cq Cxi hL (by positivity) hxi hblocks hQ hXi
  have hs : (∏ g : SG, memorySmallRowConstant q (Vs g) ell) ≤ L^G :=
    b644_group_absolute_row_polynomial434 q v C0 L (J+ell)
      hq hq1 hv hL1 Vs hVs (fun _ => ell) (fun _ => by omega) hGs
  have hb (nu) : (∏ g : BG, memorySmallRowConstant q (Vb g)
      (unsharedSlots (J+ell) (sourceBigShared J ell m (pats nu) g))) ≤ L^G :=
    b644_group_absolute_row_polynomial434 q v C0 L (J+ell)
      hq hq1 hv hL1 Vb hVb
      (fun g => unsharedSlots (J+ell) (sourceBigShared J ell m (pats nu) g))
      (fun _ => Nat.sub_le _ _) hGb
  have hcap (nu) : 0 ≤ cap nu :=
    source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu
  have hcb (nu) : 0 ≤ ∏ g : BG, memorySmallRowConstant q (Vb g)
      (unsharedSlots (J+ell) (sourceBigShared J ell m (pats nu) g)) :=
    Finset.prod_nonneg (fun g _ => rc_nonneg q (Vb g) _ hq hq1 (hv.trans_le (hVb g)))
  change (∑ nu, cap nu * _ * _) ≤ _
  calc
    _ ≤ ∑ nu, cap nu * L^G * L^G := by
      apply Finset.sum_le_sum
      intro nu hnu
      exact mul_le_mul (mul_le_mul_of_nonneg_left hs (hcap nu)) (hb nu)
        (hcb nu) (mul_nonneg (hcap nu) (Real.rpow_nonneg hL0.le _))
    _ = (∑ nu, cap nu) * L^G * L^G := by simp only [Finset.sum_mul]
    _ ≤ L^B * L^G * L^G := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hL0.le _)) (Real.rpow_nonneg hL0.le _)
    _ = L^(b644RawComparisonExponent434 (J+ell) m Cq Cxi q v C0) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1
      dsimp [B, G, b644RawComparisonExponent434]
      ring
end Green64Analytic.CorrelationSquare

end

end

