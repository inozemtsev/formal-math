module

public import Green64.Library.Weights.ActualPositiveChainCost

@[expose] public section

/-!
# Correlation / ActualPositiveRootCost

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualPositiveRootCost -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 24000000


variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The exact initial vacuum mass, including the original baseline,
orbit measure and global initial numerical distinctness. It has no
history or E/G operator in its definition. -/
def sourceOriginalActualInitialVacuumMass434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (R : ℕ) : ℝ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  ‖(physicalSourceBaselineProduct BP bm q N : ℂ)‖ *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ)‖ *
      ‖physicalVacuum SP sm BP bm J ell y‖ *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then 1 else 0)

variable (m : ℕ) {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

private theorem common_root_cost434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (C : ℝ)
    (hC : ∀ y seen,sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
      q u Vs V (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k (2*R) (2*R) 0
      (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖) y seen ≤ C) :
    sourceOriginalAbsoluteCommonMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R ≤
    sourceOriginalActualInitialVacuumMass434 SP sm BP bm J ell cap q Vs V R * C := by
  unfold sourceOriginalAbsoluteCommonMemoryRoot434 sourceOriginalActualInitialVacuumMass434
  dsimp only
  rw [mul_assoc,Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro y hy
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · rw [if_pos hn,if_pos hn,mul_one,←source_original_ABSOLUTE_GE_history_sum434]
    exact mul_le_mul_of_nonneg_left
      (hC y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · simp only [if_neg hn,mul_zero,zero_mul,le_refl]

theorem eventually_source_original_ACTUAL_RAW_COMPARISON_root_birth_cost434
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
      (H : ℕ),

      let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
      let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
      let R := Nat.ceil (L^(0.52:ℝ))
      let N := 2*R
      ‖sourceOriginalBackgroundBirthTailMemoryRoot434 SP sm
        (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) J ell m
        (fun g => Fintype.card {p : ℕ // p ∈ P g}) patterns
        q H Vs V K zeta theta k R‖ ≤
      (u^H)⁻¹ *
      sourceOriginalActualInitialVacuumMass434 SP sm
        (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) J ell
        (fun g => Fintype.card {p : ℕ // p ∈ P g}) q Vs V R *
      (Real.exp (2*u*(N+1)*(1+Real.sqrt L)) *
        ((∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
            sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) *
          (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
          (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card G))^N) := by
  filter_upwards [eventually_source_original_ACTUAL_RAW_COMPARISON_chain_cost434 c vmin hc hv] with L hL
  intro SG _ _ SP _ _ sm _ G _ _ P _ hi q hq hq1 Vs hVs V hV hHarmonic hmin hmax
    blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta k u hu H
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm := fun (g : G) (p : BP g) => p.val
  let R := Nat.ceil (L^(0.52:ℝ))
  let N := 2*R
  let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
  have ht := source_original_ACTUAL_ROOT_birth_tail_common434
    SP sm BP bm J ell m (fun g => Fintype.card (BP g)) patterns hi (fun _ => le_refl _)
    q u hu H Vs V K zeta theta k R
  apply ht.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (by linarith : 0 ≤ u) H))
  apply common_root_cost434
  intro y seen
  exact hL SP sm P hi q hq hq1 Vs hVs V hV hHarmonic hmin hmax
    blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta k u hu N 0 y seen
end Green64Analytic.CorrelationSquare

end

end

