module

public import Green64.Library.Weights.Part064
public import Green64.Library.Correlation.Part051

@[expose] public section

/-!
# Weights / ActualPositiveChainCost

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualPositiveChainCost -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 24000000

private theorem positiveG_mono434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (M : ℕ) (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (A B : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ)
    (hAB : ∀ out st,A out st ≤ B out st) :
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V mu y seen A ≤
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V mu y seen B := by
  unfold sourceOriginalAbsoluteUnseenPrimeG434
  apply Finset.sum_le_sum
  intro d hd
  split_ifs
  · exact mul_le_mul_of_nonneg_left (hAB _ _) (norm_nonneg _)
  · rfl

private theorem positiveG_const434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (M : ℕ) (q rho c : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ) :
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V mu y seen (fun _ _ => c) =
    c*sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V mu y seen (fun _ _ => 1) := by
  unfold sourceOriginalAbsoluteUnseenPrimeG434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> ring

private theorem positive_chain_cost434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (J ell m : ℕ) (cap : BG → ℕ)
    {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (Cg Ce : ℝ) (hCg : 0 ≤ Cg) (hCe : 0 ≤ Ce)
    (hG : ∀ i y seen,
      sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell) q 1 N i V
        (fun g p => u*mu g p) y seen (fun _ _ => 1) ≤ Cg)
    (hE : ∀ i (x : FullPhysicalState SP sm BP bm (J+ell) cap) seen,
      (∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
        sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns q 1 Vs V mu
          (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
          zeta theta (physicalAlternatingSign i) k x seen r (fun _ _ => 1)) ≤ Ce)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,A out st ≤ 1)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
      q u Vs V mu K zeta theta k N n start A y seen ≤ Cg^(n+1)*Ce^n := by
  induction n generalizing start y seen with
  | zero =>
      dsimp only [sourceOriginalAbsoluteGEChain434]
      simpa only [zero_add,pow_one,pow_zero,mul_one] using
        (positiveG_mono434 SP sm BP bm (J+ell) q 1 N start V
          (fun g p => u*mu g p) y seen A (fun _ _ => 1) hA).trans (hG start y seen)
  | succ n ih =>
      let C := Cg^(n+1)*Ce^n
      have hC : 0 ≤ C := mul_nonneg (pow_nonneg hCg _) (pow_nonneg hCe _)
      have hcont (yg : FullPhysicalOutput SP sm BP bm (J+ell)) (sg : Finset ℕ) :
          (∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
            sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns q 1 Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg r
              (sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
                q u Vs V mu K zeta theta k N n (start+1) A)) ≤ C*Ce := by
        calc
          _ ≤ ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
              sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns q 1 Vs V mu
                (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
                zeta theta (physicalAlternatingSign start) k
                (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg r
                (fun _ _ => C*1) := by
            apply Finset.sum_le_sum
            intro r hr
            apply source_original_ABSOLUTE_E_mono434
            intro out st
            simpa only [mul_one] using ih (start+1) out st
          _ = C*(∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
              sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns q 1 Vs V mu
                (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
                zeta theta (physicalAlternatingSign start) k
                (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg r
                (fun _ _ => 1)) := by
            simp_rw [source_original_ABSOLUTE_E_smul434]
            rw [Finset.mul_sum]
          _ ≤ C*Ce := mul_le_mul_of_nonneg_left (hE start _ sg) hC
      dsimp only [sourceOriginalAbsoluteGEChain434]
      apply (positiveG_mono434 SP sm BP bm (J+ell) q 1 N start V
        (fun g p => u*mu g p) y seen _ (fun _ _ => C*Ce) hcont).trans
      rw [positiveG_const434]
      calc
        _ ≤ (C*Ce)*Cg := mul_le_mul_of_nonneg_left (hG start y seen) (mul_nonneg hC hCe)
        _ = _ := by dsimp only [C];simp only [pow_succ];ring

/-- Uniform cost of the complete original positive G/E chain for the
actual RAW/comparison family. Every row premise is discharged by the
source-box bounds. The terminal observable is the literal vacuum. -/
theorem eventually_source_original_ACTUAL_RAW_COMPARISON_chain_cost434
    (c vmin : ℝ) (hc : 0 < c) (hv : 0 < vmin) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
      (hi : Function.Injective (fun x : Sigma (fun g => {p : ℕ // p ∈ P g}) => x.2.val))
      (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
      (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
      (V : G → ℝ) (hV : ∀ g,vmin ≤ V g)
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ P g},1/(p.val:ℝ)=V g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ P g}),Real.exp (L^c) ≤ (p.val:ℝ))
      (hmax : ∀ g (p : {p : ℕ // p ∈ P g}),(p.val:ℝ) ≤ Real.exp (Real.sqrt L))
      (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
      (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (zeta theta : ℝ) (k : ℤ) (u : ℝ) (hu : 1 ≤ u)
      (n start : ℕ)
      (y : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) (J+ell))
      (seen : Finset ℕ),
      let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
      let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
      let N := 2*Nat.ceil (L^(0.52:ℝ))
      sourceOriginalAbsoluteGEChain434 SP sm (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) J ell m (fun g => Fintype.card {p : ℕ // p ∈ P g}) patterns
        q u Vs V (physicalSourceMuTilde (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) q N V)
        K zeta theta k N n start
        (fun out _ => ‖physicalVacuum SP sm (fun g => {p : ℕ // p ∈ P g})
          (fun _ p => p.val) J ell out‖) y seen ≤
      Real.exp (2*u*(n+1)*(1+Real.sqrt L)) *
      ((∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
          sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) *
        (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
        (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card G))^n := by
  filter_upwards [eventually_source_original_ACTUAL_RAW_COMPARISON_full_E_source_box434 c vmin hc hv,
    eventually_source_original_ABSOLUTE_UNSEEN_G_source_box434 c hc] with L hE hG
  intro SG _ _ SP _ _ sm _ G _ _ P _ hi q hq hq1 Vs hVs V hV hHarmonic hmin hmax
    blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta k u hu n start y seen
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm := fun (g : G) (p : BP g) => p.val
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
  let mu := physicalSourceMuTilde BP bm q N V
  let Cg := Real.exp (2*u*(1+Real.sqrt L))
  let Ce := (∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
      sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) *
    (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card G)
  have hCe : 0 ≤ Ce := by
    have hcap0 := Finset.sum_nonneg (fun nu (_ : nu ∈ Finset.univ) =>
      source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu)
    have hsqrt : Real.sqrt q < 1 := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    have hs : 0 < 1-Real.sqrt q := sub_pos.mpr hsqrt
    have hCs : 0 ≤ ∏ g : SG,memorySmallRowConstant q (Vs g) ell := by
      apply Finset.prod_nonneg
      intro g hg
      have hv' := hVs g
      dsimp only [memorySmallRowConstant]
      positivity
    dsimp only [Ce]
    exact mul_nonneg (mul_nonneg hcap0 hCs) (by positivity)
  have hg (i : ℕ) (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) :
      sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell) q 1 N i V
        (fun g p => u*mu g p) out st (fun _ _ => 1) ≤ Cg := by
    apply (hG SP sm BP bm hi q hq.le hq1.le V (fun g => hv.trans_le (hV g))
      hmin hmax (J+ell) out st i u hu).trans
    apply Real.exp_le_exp.mpr
    have he := (source_original_B26_visit_eta_unit434 q hq.le hq1.le N i).2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ 2*u))
      (by positivity : 0 ≤ 1+Real.sqrt L)
    dsimp only [N] at hh ⊢
    nlinarith only [hh]
  have he (i : ℕ) (x : FullPhysicalState SP sm BP bm (J+ell) (fun g => Fintype.card (BP g)))
      (st : Finset ℕ) :
      (∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
        sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m (fun g => Fintype.card (BP g))
          patterns q 1 Vs V mu
          (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
          zeta theta (physicalAlternatingSign i) k x st r (fun _ _ => 1)) ≤ Ce := by
    have ho : physicalAlternatingSign i=1 ∨ physicalAlternatingSign i= -1 := by
      unfold physicalAlternatingSign
      split_ifs <;> simp
    exact hE SP sm P q hq hq1 Vs hVs V hV hHarmonic hmin hmax
      blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta
      (physicalAlternatingSign i) k ho x st
  have hA (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) :
      ‖physicalVacuum SP sm BP bm J ell out‖ ≤ 1 := by
    unfold physicalVacuum
    split_ifs <;> simp
  have hb := positive_chain_cost434 SP sm BP bm J ell m (fun g => Fintype.card (BP g))
    patterns q u Vs V mu K zeta theta k N Cg Ce (Real.exp_pos _).le hCe hg he
    (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖) hA n start y seen
  apply hb.trans_eq
  dsimp only [Cg]
  rw [←Real.exp_nat_mul]
  congr 2
  push_cast
  ring
end Green64Analytic.CorrelationSquare

end

end

