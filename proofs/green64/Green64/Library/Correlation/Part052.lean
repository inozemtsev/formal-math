module

public import Green64.Library.Weights.ActualInitialVacuumFactor
public import Green64.Library.Weights.Part065
public import Green64.Library.Correlation.Part051
public import Green64.Library.Weights.Part028
public import Green64.Library.Correlation.Part049
public import Green64.Library.Correlation.Part048
public import Green64.Library.Correlation.Part047
public import Green64.Library.Weights.Part064
public import Green64.Library.Weights.Part059
public import Green64.Library.Correlation.Part030
public import Green64.Library.Weights.ActualFrameFilteredLiteral

@[expose] public section

/-!
# Correlation / Part052

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualPositiveRootExplicitCost -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Complete explicit initial boundary cost, with the original baseline,
global initial distinctness and every vacuum Fock fibre assembled. -/
theorem source_original_ACTUAL_initial_mass_explicit_bound434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (J ell : ℕ) (cap : BG → ℕ) (q : ℝ)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (R : ℕ) (hb : ∀ g p,0 < physicalSourceBaseline BP bm q (2*R) g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q (2*R) g p ≤ 1) :
    sourceOriginalActualInitialVacuumMass434 SP sm BP bm J ell cap q Vs V R ≤
      ∏ g,((Fintype.card (SP g):ℝ)/Vs g)^(J+ell) :=
  (source_original_ACTUAL_initial_mass_le_SMALL_mass434 SP sm BP bm J ell cap q
    Vs hVs V hV hHarmonic R hb hb1).trans
      (source_original_ACTUAL_SMALL_GROUP_initial_mass_bound434 SP sm (J+ell) Vs hVs)


/-- Full actual birth-tail root with every positive-chain and initial-boundary
cost explicit. This is an absolute growth envelope, not C191/C6 saving.
The source threshold precedes every moving finite family, all labels,
J, depth parameters and u,H. No operator norm or saving is assumed. -/
theorem eventually_source_original_ACTUAL_RAW_COMPARISON_root_explicit_birth_cost434
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
      (∏ g : SG,((Fintype.card (SP g):ℝ)/Vs g)^(J+ell)) *
      (Real.exp (2*u*(N+1)*(1+Real.sqrt L)) *
        ((∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
            sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) *
          (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
          (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card G))^N) := by
  filter_upwards [eventually_source_original_ACTUAL_RAW_COMPARISON_root_birth_cost434 c vmin hc hv,
    eventually_source_original_B26_visits_below_BIG434 c hc] with L hL hBase
  intro SG _ _ SP _ _ sm _ G _ _ P _ hi q hq hq1 Vs hVs V hV hHarmonic hmin hmax
    blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta k u hu H
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm := fun (g : G) (p : BP g) => p.val
  let R := Nat.ceil (L^(0.52:ℝ))
  let N := 2*R
  have hV0 (g : G) : 0 < V g := hv.trans_le (hV g)
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p ∧
      physicalSourceBaseline BP bm q N g p ≤ 1 :=
    source_original_B26_physical_baseline_half434 BP bm q hq.le hq1.le N g p
      (hBase p.val (hmin g p))
  have hb0 (g : G) (p : BP g) : 0 < physicalSourceBaseline BP bm q N g p := by
    have hh := (hb g p).1
    linarith
  have hm := source_original_ACTUAL_initial_mass_explicit_bound434 SP sm BP bm
    J ell (fun g => Fintype.card (BP g)) q Vs hVs V hV0 hHarmonic R hb0
    (fun g p => (hb g p).2)
  have ht := hL SP sm P hi q hq hq1 Vs hVs V hV hHarmonic hmin hmax
    blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta k u hu H
  apply ht.trans
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hu) H)))
  apply mul_nonneg (Real.exp_pos _).le
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualCommonPositiveRootCost -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

/- Public finite-sum interface to the already used positive root assembly.
This exposes the actual positive envelope needed for temporal mask errors. -/
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

variable (m : ℕ) {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_ACTUAL_common_root_finite_cost434
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

/-- The complete POSITIVE common-root cost, with initial SMALL mass.
This controls absolute path weights; the left side is not a signed norm. -/
theorem eventually_source_original_ACTUAL_common_positive_root_explicit_cost434
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
      (u^H)⁻¹ * sourceOriginalAbsoluteCommonMemoryRoot434 SP sm
        (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) J ell m
        (fun g => Fintype.card {p : ℕ // p ∈ P g}) patterns
        q u Vs V K zeta theta k R ≤
      (u^H)⁻¹ *
      (∏ g : SG,((Fintype.card (SP g):ℝ)/Vs g)^(J+ell)) *
      (Real.exp (2*u*(N+1)*(1+Real.sqrt L)) *
        ((∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
            sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) *
          (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
          (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card G))^N) := by
  filter_upwards [eventually_source_original_ACTUAL_RAW_COMPARISON_chain_cost434 c vmin hc hv,
    eventually_source_original_B26_visits_below_BIG434 c hc] with L hL hBase
  intro SG _ _ SP _ _ sm _ G _ _ P _ hi q hq hq1 Vs hVs V hV hHarmonic hmin hmax
    blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta k u hu H
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm := fun (g : G) (p : BP g) => p.val
  let R := Nat.ceil (L^(0.52:ℝ))
  let N := 2*R
  have hV0 (g : G) : 0 < V g := hv.trans_le (hV g)
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p ∧
      physicalSourceBaseline BP bm q N g p ≤ 1 :=
    source_original_B26_physical_baseline_half434 BP bm q hq.le hq1.le N g p
      (hBase p.val (hmin g p))
  have hb0 (g : G) (p : BP g) : 0 < physicalSourceBaseline BP bm q N g p := by
    have hh := (hb g p).1
    linarith
  have hm := source_original_ACTUAL_initial_mass_explicit_bound434 SP sm BP bm
    J ell (fun g => Fintype.card (BP g)) q Vs hVs V hV0 hHarmonic R hb0
    (fun g p => (hb g p).2)
  let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
  let C : ℝ := Real.exp (2*u*((N:ℝ)+1)*(1+Real.sqrt L)) *
    ((∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
      sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) *
    (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card G))^N
  have hc : sourceOriginalAbsoluteCommonMemoryRoot434 SP sm BP bm J ell m
      (fun g => Fintype.card (BP g)) patterns q u Vs V K zeta theta k R ≤
      sourceOriginalActualInitialVacuumMass434 SP sm BP bm J ell
        (fun g => Fintype.card (BP g)) q Vs V R*C := by
    apply source_original_ACTUAL_common_root_finite_cost434
    intro y seen
    exact hL SP sm P hi q hq hq1 Vs hVs V hV hHarmonic hmin hmax
      blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta k u hu N 0 y seen
  have hC : 0 ≤ C := by
    apply mul_nonneg (Real.exp_pos _).le
    dsimp only [N]
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  calc
    _ ≤ (u^H)⁻¹ *
      (sourceOriginalActualInitialVacuumMass434 SP sm BP bm J ell
        (fun g => Fintype.card (BP g)) q Vs V R*C) :=
      mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hu) H))
    _ ≤ _ := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm
          (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hu) H))) hC
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedOneStepHistory -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The true source E frame is its original keep=True filtered row. -/
theorem source_original_ACTUAL_E_frame_true434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F =
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K zeta theta o k x seen F := by
  classical
  unfold sourceOriginalSourceEFrameRow434 sourceOriginalSourceEFrameFilteredRow434
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f
  · simp only [dif_pos h, if_pos trivial]
  · simp only [dif_neg h]

/-- One TRUE G/E visit, with both OLD endpoint projectors. -/
def sourceOriginalActualProjectedOneStep434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℂ :=
  sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
    q rho N i V mu y seen (fun yg sg =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu (memoryOrientationK BP J ell m patterns
            K (physicalAlternatingSign i))
          zeta theta (physicalAlternatingSign i) k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
          (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0)
      else 0)

/-- Absolute companion on the SAME G/E carrier, keeping both
OLD projector masks and the exact maximum over chronological histories.
There is no factor equal to the number of histories. -/
def sourceOriginalActualProjectedOneStepPositive434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℝ :=
  let hist := (sourceOriginalMemoryBirthPool434 BP bm).powerset
  let hnonempty := source_original_ACTUAL_history_pool_nonempty434 BP bm
  let tail := fun out st =>
    if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0
  sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
    q rho N i V mu y seen (fun yg _ =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        hist.sup' hnonempty (fun sg =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell tail))
      else 0)

/-- A one-step fully physical PEP estimate: both P masks,
the true chronological birth-history gate and its maximal continuation
are propagated without multiplying by the history cardinality. -/
theorem source_original_ACTUAL_projected_one_step_history_bound434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalActualProjectedOneStep434 SP sm BP bm J ell m cap patterns
      q rho N i T Vs V mu K zeta theta k F y seen‖ ≤
    sourceOriginalActualProjectedOneStepPositive434 SP sm BP bm J ell m cap patterns
      q rho N i T Vs V mu K zeta theta k F y seen := by
  classical
  let hist := (sourceOriginalMemoryBirthPool434 BP bm).powerset
  let hnonempty := source_original_ACTUAL_history_pool_nonempty434 BP bm
  let tail : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0
  let KE := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i)
  let ETest : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun yg sg =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu KE zeta theta (physicalAlternatingSign i) k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg tail
      else 0
  have hE (yg : FullPhysicalOutput SP sm BP bm (J+ell)) :
      sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell ETest yg ≤
      (if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        hist.sup' hnonempty (fun sg =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu KE
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell tail))
      else 0) := by
    apply (source_original_ACTUAL_history_sup_le_iff434
      SP sm BP bm J ell ETest yg _).2
    intro sg hsg
    by_cases hy : (∑ g : BG,(yg.2 g).2.card) ≤ T
    · simp only [ETest, if_pos hy]
      rw [source_original_ACTUAL_E_frame_true434]
      exact (source_original_ACTUAL_E_history_sup_majorant434
        SP sm BP bm J ell m cap patterns (fun _ _ => True)
        q rho Vs V mu KE zeta theta (physicalAlternatingSign i) k
        tail (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg)
        sg hsg).trans
        (Finset.le_sup' (fun st =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu KE
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) st
            (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell tail)) hsg)
    · simp only [ETest, if_neg hy, norm_zero, le_refl]
  have hG := source_original_ACTUAL_G_history_sup_majorant434
    SP sm BP bm J ell q rho N i V mu ETest y seen hseen
  change ‖sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
    q rho N i V mu y seen ETest‖ ≤ _
  calc
    _ ≤ sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
        q rho N i V mu y seen
        (fun yg _ => sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell ETest yg) := hG
    _ ≤ _ := by
      unfold sourceOriginalAbsoluteUnseenPrimeG434
        sourceOriginalActualProjectedOneStepPositive434
      dsimp only [hist,hnonempty,tail,KE]
      apply Finset.sum_le_sum
      intro d hd
      by_cases hg : ∀ g, ∀ p ∈ (d g).2, bm g p ∉ seen
      · simp only [if_pos hg]
        exact mul_le_mul_of_nonneg_left (hE _) (norm_nonneg _)
      · simp only [if_neg hg, le_refl]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualHistoryPositiveMono -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Exact monotonicity of the original positive G row, retaining the
global numerical no-rebirth indicator and all original witnesses. -/
theorem source_original_ACTUAL_absolute_G_history_mono434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (A B : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hAB : ∀ out st, A out st ≤ B out st) :
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
      q rho N i V mu y seen A ≤
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
      q rho N i V mu y seen B := by
  unfold sourceOriginalAbsoluteUnseenPrimeG434
  apply Finset.sum_le_sum
  intro d hd
  by_cases hg : ∀ g, ∀ p ∈ (d g).2, bm g p ∉ seen
  · simp only [if_pos hg]
    exact mul_le_mul_of_nonneg_left (hAB _ _) (norm_nonneg _)
  · simp only [if_neg hg, le_refl]

/-- Exact monotonicity of the original absolute E frame with actual
admissible OLD injections, joint K and chronological birth masks. -/
theorem source_original_ACTUAL_absolute_E_history_mono434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (A B : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ)
    (hAB : ∀ out, A out ≤ B out) :
    sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen A ≤
    sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen B := by
  classical
  unfold sourceOriginalAbsoluteFilteredEFrameHistory434
  apply Finset.sum_le_sum
  intro r hr
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f
  · simp only [dif_pos h]
    let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r
      (Classical.choose h)
    change (if keep x z then
      ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z‖ *
        A (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z) else 0) ≤
      (if keep x z then
      ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z‖ *
        B (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z) else 0)
    by_cases hk : keep x z
    · simp only [if_pos hk]
      exact mul_le_mul_of_nonneg_left (hAB _) (norm_nonneg _)
    · simp only [if_neg hk, le_refl]
  · simp only [dif_neg h, le_refl]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedSuffixPositiveStep -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- At ANY remaining length the successor of the original PEP chain
is the original projected one-G/one-E step acting on the TRUE future,
not an invented independent continuation. -/
theorem source_original_ACTUAL_projected_chain_succ_is_step434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T (n+1) start F y seen =
    sourceOriginalActualProjectedOneStep434 SP sm BP bm J ell m cap patterns
      q rho N start T Vs V mu K zeta theta k
      (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F) y seen := by
  rfl

/-- Recursive exact-suffix envelope inequality at EVERY chronological
PEP visit, with an arbitrary genuine finite terminal test. -/
theorem source_original_ACTUAL_projected_chain_succ_history_bound434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T (n+1) start F y seen‖ ≤
    sourceOriginalActualProjectedOneStepPositive434 SP sm BP bm J ell m cap patterns
      q rho N start T Vs V mu K zeta theta k
      (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F) y seen := by
  rw [source_original_ACTUAL_projected_chain_succ_is_step434]
  exact source_original_ACTUAL_projected_one_step_history_bound434
    SP sm BP bm J ell m cap patterns q rho N start T Vs V mu K zeta theta k
    (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n (start+1) F) y seen hseen

/-- The least TRUE continuation envelope after n+1 remaining
chronological visits is bounded by the maximum of the genuine positive
one-step G/E costs. This is a supremum, NOT a history-count sum. -/
theorem source_original_ACTUAL_projected_chain_succ_history_sup434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell
      (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T (n+1) start F) y ≤
    ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
      (source_original_ACTUAL_history_pool_nonempty434 BP bm)
      (fun seen =>
        sourceOriginalActualProjectedOneStepPositive434 SP sm BP bm J ell m cap patterns
          q rho N start T Vs V mu K zeta theta k
          (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N T n (start+1) F) y seen) := by
  apply (source_original_ACTUAL_history_sup_le_iff434
    SP sm BP bm J ell _ y _).2
  intro seen hs
  exact (source_original_ACTUAL_projected_chain_succ_history_bound434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k
    N T n start F y seen hs).trans
    (Finset.le_sup' (fun st =>
      sourceOriginalActualProjectedOneStepPositive434 SP sm BP bm J ell m cap patterns
        q rho N start T Vs V mu K zeta theta k
        (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T n (start+1) F) y st) hs)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedPositiveRecursion -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
/-- One-visit positive PEP operator on real output envelopes,
with both OLD masks and supremum over numerical histories. -/
def sourceOriginalActualProjectedPositiveOp434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℝ :=
  let hist := (sourceOriginalMemoryBirthPool434 BP bm).powerset
  let hnonempty := source_original_ACTUAL_history_pool_nonempty434 BP bm
  sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
    q rho N i V mu y seen (fun yg _ =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        hist.sup' hnonempty (fun sg =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then A out else 0))
      else 0)

/-- Positive dynamic-programming envelope for every remaining
stage of the ORIGINAL projected chain. No history count or saving
hypothesis enters this definition. -/
def sourceOriginalActualProjectedPositiveChain434
    (q rho : ℝ) (N T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    (n start : ℕ) → FullPhysicalOutput SP sm BP bm (J+ell) → ℝ
  | 0,start,y =>
      ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
        (source_original_ACTUAL_history_pool_nonempty434 BP bm)
        (fun seen => sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
          q rho N start V mu y seen
          (fun out _ => sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F out))
  | n+1,start,y =>
      ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
        (source_original_ACTUAL_history_pool_nonempty434 BP bm)
        (fun seen => sourceOriginalActualProjectedPositiveOp434 SP sm BP bm J ell m cap patterns
          q rho N start T Vs V mu K zeta theta k
          (sourceOriginalActualProjectedPositiveChain434 q rho N T Vs V mu
            K zeta theta k F n (start+1)) y seen)

/-- A REAL bound for every chronological continuation is propagated
through the true projected one-step G/E positive envelope.
The birth-history supremum is paid once, without |powerset|. -/
theorem source_original_ACTUAL_projected_positive_step_envelope434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ)
    (hA : ∀ out st, st ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset →
       ‖F out st‖ ≤ A out)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalActualProjectedOneStepPositive434 SP sm BP bm J ell m cap patterns
      q rho N i T Vs V mu K zeta theta k F y seen ≤
    sourceOriginalActualProjectedPositiveOp434 SP sm BP bm J ell m cap patterns
      q rho N i T Vs V mu K zeta theta k A y seen := by
  classical
  let hist := (sourceOriginalMemoryBirthPool434 BP bm).powerset
  let hn := source_original_ACTUAL_history_pool_nonempty434 BP bm
  let tail : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0
  have ht (out : FullPhysicalOutput SP sm BP bm (J+ell)) :
      sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell tail out ≤
        (if (∑ g : BG,(out.2 g).2.card) ≤ T then A out else 0) := by
    apply (source_original_ACTUAL_history_sup_le_iff434
      SP sm BP bm J ell tail out _).2
    intro st hst
    by_cases ho : (∑ g : BG,(out.2 g).2.card) ≤ T
    · simpa only [tail,if_pos ho] using hA out st hst
    · simp only [tail,if_neg ho,norm_zero,le_refl]
  let KE := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i)
  have he (yg : FullPhysicalOutput SP sm BP bm (J+ell)) :
      (if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        hist.sup' hn (fun sg =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu KE
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell tail))
       else 0) ≤
      (if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        hist.sup' hn (fun sg =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu KE
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then A out else 0))
       else 0) := by
    by_cases hy : (∑ g : BG,(yg.2 g).2.card) ≤ T
    · simp only [if_pos hy]
      apply Finset.sup'_le
      intro sg hsg
      exact (source_original_ACTUAL_absolute_E_history_mono434 SP sm BP bm J ell m
        cap patterns (fun _ _ => True) q rho Vs V mu KE zeta theta
        (physicalAlternatingSign i) k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
        (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell tail)
        (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then A out else 0)
        ht).trans (Finset.le_sup' (fun st =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu KE
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) st
            (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then A out else 0)) hsg)
    · simp only [if_neg hy,le_refl]
  have hg := source_original_ACTUAL_absolute_G_history_mono434
    SP sm BP bm J ell q rho N i V mu y seen
    (fun yg _ =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        hist.sup' hn (fun sg =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu KE
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell tail))
      else 0)
    (fun yg _ =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        hist.sup' hn (fun sg =>
          sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
            (fun _ _ => True) q rho Vs V mu KE
            zeta theta (physicalAlternatingSign i) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then A out else 0))
      else 0) (by intro yg sg; exact he yg)
  simpa only [sourceOriginalActualProjectedOneStepPositive434,
    sourceOriginalActualProjectedPositiveOp434] using hg

/-- FULL finite-n bound for the original PEP physical G/E chain by
the explicitly recursive positive chronological operator. There is
NO hypothesis about norms of suffixes, no factor |Hist|, and both
OLD endpoint projectors are retained at every E visit. -/
theorem source_original_ACTUAL_projected_positive_chain_bounds434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T : ℕ) (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ) (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen‖ ≤
    sourceOriginalActualProjectedPositiveChain434 SP sm BP bm J ell m cap patterns
      q rho N T Vs V mu K zeta theta k F n start y := by
  induction n generalizing start y seen with
  | zero =>
      have hG := source_original_ACTUAL_G_history_sup_majorant434
        SP sm BP bm J ell q rho N start V mu F y seen hseen
      change ‖sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
        q rho N start V mu y seen F‖ ≤ _
      exact hG.trans (Finset.le_sup' (fun st =>
        sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
          q rho N start V mu y st
          (fun out _ => sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F out)) hseen)
  | succ n ih =>
      have hstep := source_original_ACTUAL_projected_chain_succ_history_bound434
        SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k
        N T n start F y seen hseen
      have hEnv (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ)
          (hs : st ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
          ‖sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N T n (start+1) F out st‖ ≤
          sourceOriginalActualProjectedPositiveChain434 SP sm BP bm J ell m cap patterns
            q rho N T Vs V mu K zeta theta k F n (start+1) out :=
        ih (start+1) out st hs
      have hmono := source_original_ACTUAL_projected_positive_step_envelope434
        SP sm BP bm J ell m cap patterns q rho N start T Vs V mu K zeta theta k
        (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T n (start+1) F)
        (sourceOriginalActualProjectedPositiveChain434 SP sm BP bm J ell m cap patterns
          q rho N T Vs V mu K zeta theta k F n (start+1)) hEnv y seen
      calc
        _ ≤ sourceOriginalActualProjectedOneStepPositive434 SP sm BP bm J ell m cap patterns
            q rho N start T Vs V mu K zeta theta k
            (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T n (start+1) F) y seen := hstep
        _ ≤ sourceOriginalActualProjectedPositiveOp434 SP sm BP bm J ell m cap patterns
            q rho N start T Vs V mu K zeta theta k
            (sourceOriginalActualProjectedPositiveChain434 SP sm BP bm J ell m cap patterns
              q rho N T Vs V mu K zeta theta k F n (start+1)) y seen := hmono
        _ ≤ _ := Finset.le_sup' (fun st =>
            sourceOriginalActualProjectedPositiveOp434 SP sm BP bm J ell m cap patterns
              q rho N start T Vs V mu K zeta theta k
              (sourceOriginalActualProjectedPositiveChain434 SP sm BP bm J ell m cap patterns
                q rho N T Vs V mu K zeta theta k F n (start+1)) y st) hseen
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedPositiveRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- All ACTUAL initially born active BIG prime labels are in the
very same finite numerical history pool used by the G/E recursion.
No disjointness, vacuum support or injected active labels assumed. -/
theorem source_original_ACTUAL_initial_seen_in_history_pool434
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset ∈
      (sourceOriginalMemoryBirthPool434 BP bm).powerset := by
  classical
  apply Finset.mem_powerset.mpr
  intro p hp
  simp only [physicalOutputInitialBirths,List.mem_toFinset,List.mem_flatMap,
    List.mem_map,Finset.mem_toList] at hp
  rcases hp with ⟨g,hg,j,hj,rfl⟩
  exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,
    Finset.mem_image.mpr ⟨(y.2 g).1 j,Finset.mem_univ _,rfl⟩⟩

/-- Genuine scalar positive dynamic-root envelope after the
physical Fock/vacuum initial disintegration. No replacement of S+Ts
with Ts, no normalization of vacuum mass to one. -/
def sourceOriginalActualProjectedPositiveRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) : ℝ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  ‖(physicalSourceBaselineProduct BP bm q N : ℂ)‖ *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ)‖ *
      ‖physicalVacuum SP sm BP bm J ell y‖ *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalActualProjectedPositiveChain434 SP sm BP bm J ell m cap patterns
          q rho N T Vs V mu K zeta theta k
          (fun out _ => physicalVacuum SP sm BP bm J ell out) N 0 y else 0)

/-- The exact ORIGINAL projected frame vacuum root has a fully
explicit positive recursive majorant. Every initial Fock mass and
vacuum, numerical birth history and OLD gate is retained. -/
theorem source_original_ACTUAL_FRAME_projected_positive_root_bound434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) :
    ‖sourceOriginalOLDProjectedFrameMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T‖ ≤
    sourceOriginalActualProjectedPositiveRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  classical
  unfold sourceOriginalOLDProjectedFrameMemoryRoot434
    sourceOriginalActualProjectedPositiveRoot434
  dsimp only
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs
          (physicalSourceMuTilde BP bm q (2*R) V) y : ℂ) *
          star (physicalVacuum SP sm BP bm J ell y) *
          (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
            sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
              K zeta theta k (2*R) T (2*R) 0
              (fun out _ => physicalVacuum SP sm BP bm J ell out)
              y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
          else 0)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
      · simp only [if_pos hn,norm_mul,norm_star]
        have hChain := source_original_ACTUAL_projected_positive_chain_bounds434
          SP sm BP bm J ell m cap patterns q rho Vs V
          (physicalSourceMuTilde BP bm q (2*R) V)
          K zeta theta k (2*R) T
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          (2*R) 0 y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
          (source_original_ACTUAL_initial_seen_in_history_pool434
            SP sm BP bm J ell y)
        exact mul_le_mul_of_nonneg_left hChain
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      · simp only [if_neg hn,mul_zero,norm_zero,le_refl]

/-- A root bound for the original physical PEP Memory root, not a
surrogate frame root. On the reachable original support the frame and
physical roots are IDENTICAL by the already checked orbit theorem. -/
theorem source_original_ACTUAL_PROJECTED_positive_root_bound434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    ‖sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T‖ ≤
    sourceOriginalActualProjectedPositiveRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  rw [source_original_MEMORY_OLD_projected_root_frame_exact434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V K zeta theta k R T hVs hmu]
  exact source_original_ACTUAL_FRAME_projected_positive_root_bound434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedSuffixEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The true maximal chronological PEP continuation is bounded by
the same real positive recursion at EACH physical output, without
counting histories or assuming a continuation norm. -/
theorem source_original_ACTUAL_projected_history_sup_le_positive434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell
      (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n start F) y ≤
    sourceOriginalActualProjectedPositiveChain434 SP sm BP bm J ell m cap patterns
      q rho N T Vs V mu K zeta theta k F n start y := by
  apply (source_original_ACTUAL_history_sup_le_iff434 SP sm BP bm J ell _ y _).2
  intro seen hseen
  exact source_original_ACTUAL_projected_positive_chain_bounds434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k
    N T F n start y seen hseen

/-- Exact weighted Fock/sector energy of the recursively constructed
positive history-envelope. All original SMALL= S+Ts factors and OLD
Fock densities are charged, not normalized away. -/
def sourceOriginalActualProjectedPositiveEnergy434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) : ℝ :=
  sourceOriginalMemorySelectorEnergy434 SP sm BP bm J ell cap Vs V mu
    (fun y => ((sourceOriginalActualProjectedPositiveChain434
      SP sm BP bm J ell m cap patterns
      q rho N T Vs V mu K zeta theta k F n start y):ℂ))

/-- Unconditional exact energy comparison for a genuine chronological
PEP suffix: local DIRTY target energy is dominated by an explicitly
defined positive recursive energy, with no history-cardinality loss.
This is NOT a claimed bound on that positive energy's magnitude. -/
theorem source_original_ACTUAL_projected_suffix_energy_le_positive434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g)
    (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemorySelectorEnergy434 SP sm BP bm J ell cap Vs V mu
      (sourceOriginalActualHistoryComplexEnvelope434 SP sm BP bm J ell
        (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T n start F)) ≤
    sourceOriginalActualProjectedPositiveEnergy434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F := by
  classical
  unfold sourceOriginalMemorySelectorEnergy434
    sourceOriginalActualProjectedPositiveEnergy434
    sourceOriginalMemorySelectorEnergy434
  apply Finset.sum_le_sum
  intro y hy
  let Tail := sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta k N T n start F
  let a := sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell Tail y
  let b := sourceOriginalActualProjectedPositiveChain434 SP sm BP bm J ell m cap patterns
    q rho N T Vs V mu K zeta theta k F n start y
  have ha : 0 ≤ a := source_original_ACTUAL_history_sup_nonneg434
    SP sm BP bm J ell Tail y
  have hab : a ≤ b := source_original_ACTUAL_projected_history_sup_le_positive434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k N T n start F y
  have hb : 0 ≤ b := ha.trans hab
  have hnorma :
      ‖sourceOriginalActualHistoryComplexEnvelope434 SP sm BP bm J ell Tail y‖ = a :=
    source_original_ACTUAL_history_complex_envelope_norm434 SP sm BP bm J ell Tail y
  have hnormb : ‖(b:ℂ)‖=b := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
  rw [hnorma,hnormb]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2)
    (source_original_memory_FULL_density_orbit_nonneg434
      SP sm BP bm J ell cap Vs V mu hVs hV hmu y)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFrameProjectedEnvelope -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Projected original physical E-frame controlled by a prescribed
true-history-uniform envelope, with BOTH endpoint OLD projectors.
This is a finite implication, not a global energy saving hypothesis. -/
theorem source_original_ACTUAL_projected_E_frame_envelope434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ)
    (hA : ∀ out st, st ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset →
       ‖F out st‖ ≤ A out)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen
      (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0)‖ ≤
    sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen
      (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then A out else 0) := by
  classical
  let PF : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0
  let PA : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ :=
    fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then A out else 0
  have hPF (out : FullPhysicalOutput SP sm BP bm (J+ell)) :
      sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell PF out ≤ PA out := by
    apply (source_original_ACTUAL_history_sup_le_iff434 SP sm BP bm J ell PF out _).2
    intro st hs
    by_cases ht : (∑ g : BG,(out.2 g).2.card) ≤ T
    · simpa only [PF,PA,if_pos ht] using hA out st hs
    · simp only [PF,PA,if_neg ht,norm_zero,le_refl]
  have hl := source_original_ACTUAL_E_history_sup_majorant434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k
    PF x seen hseen
  have hm := source_original_ACTUAL_absolute_E_history_mono434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k
    x seen (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell PF)
    PA hPF
  exact hl.trans hm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveInsertionChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal finite positive first-DIRTY insertion companion:
before insertion the original CLEAN branch, at insertion DIRTY,
and afterwards the full projected PEP continuation. The same G/E
carrier, K, OLD gates and chronological histories are used. -/
def sourceOriginalActualPositiveDIRTYInsertionChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T : ℕ) (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    (n start : ℕ) → FullPhysicalOutput SP sm BP bm (J+ell) → ℝ
  | 0,_,_ => 0
  | n+1,start,y =>
      let Hist := (sourceOriginalMemoryBirthPool434 BP bm).powerset
      let hn := source_original_ACTUAL_history_pool_nonempty434 BP bm
      let KE := memoryOrientationK BP J ell m patterns
        K (physicalAlternatingSign start)
      Hist.sup' hn (fun seen =>
        sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
          q rho N start V mu y seen (fun yg _ =>
            if (∑ g : BG,(yg.2 g).2.card) ≤ T then
              Hist.sup' hn (fun sg =>
                sourceOriginalAbsoluteFilteredEFrameHistory434
                  SP sm BP bm J ell m cap patterns
                  (fun x z => ¬ sourceOriginalCleanChoice434
                    SP sm BP bm J ell m cap patterns x z)
                  q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
                  (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
                  (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                    sourceOriginalActualProjectedPositiveChain434
                      SP sm BP bm J ell m cap patterns q rho N T Vs V mu
                      K zeta theta k F n (start+1) out else 0) +
                sourceOriginalAbsoluteFilteredEFrameHistory434
                  SP sm BP bm J ell m cap patterns
                  (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
                  q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
                  (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
                  (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                    sourceOriginalActualPositiveDIRTYInsertionChain434
                      q rho Vs V mu K zeta theta k N T F n (start+1) out else 0))
            else 0))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveInsertionStep -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- TRUE first-DIRTY E insertion, with two projected continuations:
all DIRTY E choices followed by full PEP, or CLEAN E choices followed
by a further insertion, has the corresponding ORIGINAL positive-frame
bound. It is valid for real history-dependent Fock continuations. -/
theorem source_original_ACTUAL_E_dirty_clean_positive_step434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (T : ℕ) (FF FI : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (AF AI : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ)
    (hf : ∀ out st, st ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset → ‖FF out st‖ ≤ AF out)
    (hi : ∀ out st, st ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset → ‖FI out st‖ ≤ AI out)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ)
    (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen
      (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then FF out st else 0) +
      sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen
      (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then FI out st else 0)‖ ≤
    sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta o k x seen
      (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then AF out else 0) +
    sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k x seen
      (fun out => if (∑ g : BG,(out.2 g).2.card) ≤ T then AI out else 0) := by
  have hd := source_original_ACTUAL_projected_E_frame_envelope434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta o k T FF AF hf x seen hs
  have hc := source_original_ACTUAL_projected_E_frame_envelope434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta o k T FI AI hi x seen hs
  change ‖_+_‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add hd hc)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGUniformEnvelope -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ)

/-- The actual G ghost row transports any proven envelope uniform in
all admissible chronological birth histories without summing over
histories. The only loss is the TRUE absolute G row. -/
theorem source_original_ACTUAL_G_uniform_history_envelope434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ)
    (hA : ∀ out st, st ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset →
      ‖F out st‖ ≤ A out)
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen F‖ ≤
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (fun out _ => A out) := by
  have hE (out : FullPhysicalOutput SP sm BP bm (J+ell)) :
      sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F out ≤ A out :=
    (source_original_ACTUAL_history_sup_le_iff434 SP sm BP bm J ell F out _).2
      (hA out)
  have hg := source_original_ACTUAL_G_history_sup_majorant434
    SP sm BP bm J ell q rho N i V mu F y seen hseen
  have hm := source_original_ACTUAL_absolute_G_history_mono434
    SP sm BP bm J ell q rho N i V mu y seen
    (fun out _ => sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F out)
    (fun out _ => A out) (fun out _ => hE out)
  exact hg.trans hm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveInsertionBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 30000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The full first-DIRTY chronological frame chain, with TRUE G/E
operators, two OLD endpoint masks, exact joint K and numeric seen,
is pointwise dominated by the explicit positive first-insertion
recursion for every remaining length n and every admissible history.
No hypothesis about suffix or prefix norm is introduced. -/
theorem source_original_ACTUAL_DIRTY_insertion_positive_chain_bound434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen‖ ≤
    sourceOriginalActualPositiveDIRTYInsertionChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T F n start y := by
  induction n generalizing start y seen with
  | zero =>
      simp only [sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434,
        sourceOriginalActualPositiveDIRTYInsertionChain434,norm_zero,le_refl]
  | succ n ih =>
      classical
      let Hist := (sourceOriginalMemoryBirthPool434 BP bm).powerset
      let hHist := source_original_ACTUAL_history_pool_nonempty434 BP bm
      let KE := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start)
      let FF := sourceOriginalOLDProjectedFrameGEChain434
        SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k N T n (start+1) F
      let FI := sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
        SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k N T n (start+1) F
      let AF := sourceOriginalActualProjectedPositiveChain434
        SP sm BP bm J ell m cap patterns q rho N T Vs V mu
        K zeta theta k F n (start+1)
      let AI := sourceOriginalActualPositiveDIRTYInsertionChain434
        SP sm BP bm J ell m cap patterns q rho Vs V mu
        K zeta theta k N T F n (start+1)
      let P : FullPhysicalOutput SP sm BP bm (J+ell) → Prop :=
        fun out => (∑ g : BG,(out.2 g).2.card) ≤ T
      let DIRTY := fun x z => ¬ sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z
      let CLEAN := sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns
      have hFF (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ)
          (hs : st ∈ Hist) : ‖FF out st‖ ≤ AF out :=
        source_original_ACTUAL_projected_positive_chain_bounds434
          SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k
          N T F n (start+1) out st hs
      have hFI (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ)
          (hs : st ∈ Hist) : ‖FI out st‖ ≤ AI out :=
        ih (start+1) out st hs
      let ETest : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
        fun yg sg => if P yg then
          sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (fun out st => if P out then FF out st else 0) +
          sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (fun out st => if P out then FI out st else 0)
          else 0
      let EPos : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ :=
        fun yg => if P yg then Hist.sup' hHist (fun sg =>
          sourceOriginalAbsoluteFilteredEFrameHistory434
            SP sm BP bm J ell m cap patterns DIRTY
            q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (fun out => if P out then AF out else 0) +
          sourceOriginalAbsoluteFilteredEFrameHistory434
            SP sm BP bm J ell m cap patterns CLEAN
            q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
            (fun out => if P out then AI out else 0))
          else 0
      have hE (yg : FullPhysicalOutput SP sm BP bm (J+ell)) (sg : Finset ℕ)
          (hs : sg ∈ Hist) : ‖ETest yg sg‖ ≤ EPos yg := by
        by_cases hy : P yg
        · simp only [ETest,EPos,if_pos hy]
          have hh := source_original_ACTUAL_E_dirty_clean_positive_step434
            SP sm BP bm J ell m cap patterns q rho Vs V mu KE
            zeta theta (physicalAlternatingSign start) k T FF FI AF AI
            hFF hFI
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg hs
          exact hh.trans (Finset.le_sup' (fun st =>
            sourceOriginalAbsoluteFilteredEFrameHistory434
              SP sm BP bm J ell m cap patterns DIRTY
              q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) st
              (fun out => if P out then AF out else 0) +
            sourceOriginalAbsoluteFilteredEFrameHistory434
              SP sm BP bm J ell m cap patterns CLEAN
              q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) st
              (fun out => if P out then AI out else 0)) hs)
        · simp only [ETest,EPos,if_neg hy,norm_zero,le_refl]
      have hG := source_original_ACTUAL_G_uniform_history_envelope434
        SP sm BP bm J ell q rho N start V mu ETest EPos
        hE y seen hseen
      change ‖sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
        q rho N start V mu y seen ETest‖ ≤ _
      calc
        _ ≤ sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
          q rho N start V mu y seen (fun yg _ => EPos yg) := hG
        _ ≤ _ := by
          change sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
            q rho N start V mu y seen (fun yg _ => EPos yg) ≤
            Hist.sup' hHist (fun st =>
              sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
                q rho N start V mu y st (fun yg _ => EPos yg))
          exact Finset.le_sup' (fun st =>
            sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
              q rho N start V mu y st (fun yg _ => EPos yg)) hseen
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveInsertionRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Positive first-insertion vacuum root on the EXACT original Fock
carrier. Signed G/E kernels, OLD projectors, numerical seen, joint K,
initial Nodup and source baseline are retained in the positive bound. -/
def sourceOriginalActualPositiveDIRTYInsertionRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) : ℝ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  ‖(physicalSourceBaselineProduct BP bm q N : ℂ)‖ *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ)‖ *
      ‖physicalVacuum SP sm BP bm J ell y‖ *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalActualPositiveDIRTYInsertionChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T
          (fun out _ => physicalVacuum SP sm BP bm J ell out) N 0 y else 0)

/-- The exact ORIGINAL projected frame vacuum root has a fully
explicit positive recursive majorant. Every initial Fock mass and
vacuum, numerical birth history and OLD gate is retained. -/
theorem source_original_ACTUAL_FRAME_DIRTY_insertion_positive_root_bound434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) :
    ‖sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T‖ ≤
    sourceOriginalActualPositiveDIRTYInsertionRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  classical
  unfold sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
    sourceOriginalActualPositiveDIRTYInsertionRoot434
  dsimp only
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs
          (physicalSourceMuTilde BP bm q (2*R) V) y : ℂ) *
          star (physicalVacuum SP sm BP bm J ell y) *
          (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
            sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
              K zeta theta k (2*R) T (2*R) 0
              (fun out _ => physicalVacuum SP sm BP bm J ell out)
              y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
          else 0)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
      · simp only [if_pos hn,norm_mul,norm_star]
        have hChain := source_original_ACTUAL_DIRTY_insertion_positive_chain_bound434
          SP sm BP bm J ell m cap patterns q rho Vs V
          (physicalSourceMuTilde BP bm q (2*R) V)
          K zeta theta k (2*R) T
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          (2*R) 0 y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
          (source_original_ACTUAL_initial_seen_in_history_pool434
            SP sm BP bm J ell y)
        exact mul_le_mul_of_nonneg_left hChain
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      · simp only [if_neg hn,mul_zero,norm_zero,le_refl]

/-- The original PHYSICAL single-DIRTY insertion root (with weighted
Fock orbit averaging, not an abstract frame surrogate) has the same
positive first-insertion majorant by the genuine reachable-sector
physical/frame identity. No saving or energy hypothesis is assumed. -/
theorem source_original_ACTUAL_PHYSICAL_DIRTY_insertion_positive_root_bound434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T‖ ≤
    sourceOriginalActualPositiveDIRTYInsertionRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  have hframe := source_original_MEMORY_PEP_PCLEAN_root_telescoping_of_mass434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V
    K zeta theta k R T hVs hmu
  have hphys := source_original_MEMORY_PEP_PCLEAN_physical_DIRTY_general434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V
    K zeta theta k R T hVs hmu
  have hEq : sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T =
      sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
        SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T :=
    hframe.symm.trans hphys
  rw [←hEq]
  exact source_original_ACTUAL_FRAME_DIRTY_insertion_positive_root_bound434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYRootSum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 26000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The complete original signed Fock/vacuum/baseline root with one
DIRTY insertion at EXACT chronological position j, all earlier visits
CLEAN and all later visits full PEP. All signs and masks remain. -/
def sourceOriginalSignedDIRTYAtMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (R T j : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalSignedDIRTYAt434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0 j
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- The genuine ORIGINAL projected first-DIRTY signed root is EXACTLY
the sum over all possible chronological insertion positions.
There is no loss of signs, Fock/vacuum normalisations, total OLD
projectors or the common numerical no-rebirth history. -/
theorem source_original_SIGNED_DIRTY_frame_root_sum434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) :
    sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    ∑ j ∈ Finset.range (2*R),
      sourceOriginalSignedDIRTYAtMemoryRoot434
        SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T j := by
  classical
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let Base : ℂ := physicalSourceBaselineProduct BP bm q N
  let Support := physicalFockOrbitSupport SP sm BP bm (J+ell) cap
  let W : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ :=
    fun y => (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y)
  let F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out _ => physicalVacuum SP sm BP bm J ell out
  let Term : ℕ → FullPhysicalOutput SP sm BP bm (J+ell) → ℂ :=
    fun j y => if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
      sourceOriginalSignedDIRTYAt434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T N 0 j F y
        (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0
  have hterm (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0 F y
          (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0) =
      ∑ j ∈ Finset.range N, Term j y := by
    by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [Term,if_pos hn]
      exact (source_original_SIGNED_first_DIRTY_position_sum434
        SP sm BP bm J ell m cap patterns q rho Vs V mu
        K zeta theta k N T N 0 F y
        (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset).symm
    · simp only [Term,if_neg hn,Finset.sum_const_zero]
  change Base * (∑ y ∈ Support, W y *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0 F y
          (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
        else 0)) =
    ∑ j ∈ Finset.range N, Base * (∑ y ∈ Support, W y * Term j y)
  calc
    Base * (∑ y ∈ Support, W y * (if
        (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
          sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
            SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N T N 0 F y
            (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
        else 0)) =
      Base * (∑ y ∈ Support, W y * ∑ j ∈ Finset.range N, Term j y) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        rw [hterm]
    _ = Base * (∑ y ∈ Support,
        ∑ j ∈ Finset.range N, W y * Term j y) := by
          congr 1
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
    _ = Base * (∑ j ∈ Finset.range N,
        ∑ y ∈ Support, W y * Term j y) := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range N,
        Base * (∑ y ∈ Support, W y * Term j y) := by
          rw [Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYPhysicalRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- EXACT sum over chronological first-DIRTY positions for the
ORIGINAL physical projected marked-E Memory root with true Fock orbit
average, the original two endpoint OLD projectors, numerical seen,
vacuum, baseline, q/rho, signed joint K and alternating orientations.
No absolute value/triangle inequality has been applied. -/
theorem source_original_SIGNED_DIRTY_physical_root_sum434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T =
    ∑ j ∈ Finset.range (2*R),
      sourceOriginalSignedDIRTYAtMemoryRoot434
        SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T j := by
  have hframe := source_original_MEMORY_PEP_PCLEAN_root_telescoping_of_mass434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V
    K zeta theta k R T hVs hmu
  have hphysical := source_original_MEMORY_PEP_PCLEAN_physical_DIRTY_general434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V
    K zeta theta k R T hVs hmu
  have heq :
      sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
        SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T =
      sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
        SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T :=
    hframe.symm.trans hphysical
  rw [←heq]
  exact source_original_SIGNED_DIRTY_frame_root_sum434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedHistoryState -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 19000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The exact FINITE physical Fock/orbit and chronological-history
carrier, restricted to genuinely reachable numerical sectors.
FullPhysicalOutput itself is NOT finite (pending multisets are
unbounded); no invalid global Fintype instance is introduced. -/
def sourceOriginalActualSignedHistoryCarrierFinset434 :
    Finset (FullPhysicalOutput SP sm BP bm (J+ell) × Finset ℕ) :=
  ((physicalFockOrbitSupport SP sm BP bm (J+ell) cap).product
      ((sourceOriginalMemoryBirthPool434 BP bm).powerset)).filter
    (fun z => sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) z.1 z.2)

/-- A finite state is an authentic original reachable Fock output
PLUS its actual numerical seen history, never merely the Fock output. -/
def sourceOriginalActualSignedHistoryState434 :=
  {z : FullPhysicalOutput SP sm BP bm (J+ell) × Finset ℕ //
    z ∈ sourceOriginalActualSignedHistoryCarrierFinset434 SP sm BP bm J ell cap}

noncomputable instance :
    Fintype (sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :=
  Finset.fintypeCoeSort (sourceOriginalActualSignedHistoryCarrierFinset434
    SP sm BP bm J ell cap)

noncomputable instance :
    DecidableEq (sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :=
  Classical.decEq _

theorem source_original_ACTUAL_signed_history_mem_iff434
    (out : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    (out,seen) ∈ sourceOriginalActualSignedHistoryCarrierFinset434
      SP sm BP bm J ell cap ↔
    out ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap ∧
      seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset ∧
      sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out seen := by
  classical
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hp,hr⟩
    rcases Finset.mem_product.mp hp with ⟨ho,hs⟩
    exact ⟨ho,hs,hr⟩
  · rintro ⟨ho,hs,hr⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨ho,hs⟩,hr⟩

/-- The REAL reachable numerical state enters the finite carrier
provided its initial seen set is in the genuine prime-pool history
and the original BIG Fock capacities cover all distinct labels. -/
theorem source_original_ACTUAL_signed_history_contains_reachable434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (out : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out seen)
    (hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    (out,seen) ∈ sourceOriginalActualSignedHistoryCarrierFinset434
      SP sm BP bm J ell cap := by
  apply (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap out seen).2
  exact ⟨source_original_REACHABLE_orbit_support434
    SP sm BP bm (J+ell) cap hcap out seen hr,hs,hr⟩

/-- Restriction of the true full physical terminal test to the finite
Fock/HISTORY carrier, without dropping seen or merging histories. -/
def sourceOriginalActualSignedHistoryRestrict434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ :=
  fun z => F z.val.1 z.val.2

/-- A finite-state test becomes a full physical continuation, zero
outside the genuine reachable finite Fock/history carrier. -/
def sourceOriginalActualSignedHistoryLift434
    (f : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ) :
    FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
  fun out seen =>
    if h : (out,seen) ∈ sourceOriginalActualSignedHistoryCarrierFinset434
        SP sm BP bm J ell cap then f ⟨(out,seen),h⟩ else 0

theorem source_original_ACTUAL_signed_history_lift_valid434
    (f : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ)
    (out : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (h : (out,seen) ∈ sourceOriginalActualSignedHistoryCarrierFinset434
      SP sm BP bm J ell cap) :
    sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f out seen =
      f ⟨(out,seen),h⟩ := by
  simp only [sourceOriginalActualSignedHistoryLift434,dif_pos h]

/-- On EVERY REAL reachable physical Fock/history state, lifting a
restricted signed continuation changes NOTHING. The chronological
seen mask is preserved, not maximised away or reset. -/
theorem source_original_ACTUAL_signed_history_lift_restrict434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (out : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (h : (out,seen) ∈ sourceOriginalActualSignedHistoryCarrierFinset434
      SP sm BP bm J ell cap) :
    sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
      (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F)
        out seen = F out seen := by
  exact (source_original_ACTUAL_signed_history_lift_valid434
    SP sm BP bm J ell cap
    (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F)
    out seen h).trans rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedHistoryClosure -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 19000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Finite numerical history restriction, keeping Fock outputs and
complex source signs unchanged; no supremum over seen histories. -/
def sourceOriginalActualSignedHistoryMask434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
  fun out st => if st ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset
    then F out st else 0

/-- The original signed G row does not see terminal history values
outside the actual finite numerical birth pool, when its input seen
is genuinely admissible. This is exact equality, not an L2 estimate. -/
theorem source_original_ACTUAL_SIGNED_G_history_mask_exact434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen
      (sourceOriginalActualSignedHistoryMask434 SP sm BP bm J ell F) =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen F := by
  classical
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
    sourceOriginalActualSignedHistoryMask434
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hg : ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen
  · simp only [if_pos hg]
    have hs : seen ∪
        sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm (J+ell) y d ∈
        (sourceOriginalMemoryBirthPool434 BP bm).powerset := by
      apply Finset.mem_powerset.mpr
      exact Finset.union_subset (Finset.mem_powerset.mp hseen)
        (source_original_ACTUAL_ghost_births_subset_pool434
          SP sm BP bm J ell y d)
    simp only [if_pos hs]
  · simp only [if_neg hg]

/-- The ORIGINAL signed source E-frame, with any literal CLEAN/dirty
restriction and the full joint source K, depends only on terminal
values with an admissible numerical seen history. No history maxima
or positive comparison kernels are introduced. -/
theorem source_original_ACTUAL_SIGNED_E_history_mask_exact434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen
      (sourceOriginalActualSignedHistoryMask434 SP sm BP bm J ell F) =
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F := by
  classical
  unfold sourceOriginalSourceEFrameFilteredRow434
    sourceOriginalActualSignedHistoryMask434
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434
      SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns
        x seen o k r f
  · simp only [dif_pos h]
    let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns
      x r (Classical.choose h)
    have hs : seen ∪
        (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset ∈
        (sourceOriginalMemoryBirthPool434 BP bm).powerset :=
      source_original_memory_E_history_closed434
        SP sm BP bm J ell m cap patterns seen hseen x z
    dsimp only [z] at hs
    change (if keep x z then _ else 0) = (if keep x z then _ else 0)
    by_cases hk : keep x z
    · simp only [if_pos hk, if_pos hs]
    · simp only [if_neg hk]
  · simp only [dif_neg h]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedFiniteCarrier -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Full signed terminal tests and their finite reachable Fock/history
restrictions agree ON each genuinely reachable physical state with a
numerical history in the original BIG prime pool. -/
theorem source_original_ACTUAL_signed_history_mask_lift_eq434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (out : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out seen) :
    sourceOriginalActualSignedHistoryMask434 SP sm BP bm J ell F out seen =
    sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
      (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F)
        out seen := by
  classical
  by_cases hs : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset
  · have hc := source_original_ACTUAL_signed_history_contains_reachable434
      SP sm BP bm J ell cap hcap out seen hr hs
    rw [source_original_ACTUAL_signed_history_lift_restrict434
      SP sm BP bm J ell cap F out seen hc]
    simp only [sourceOriginalActualSignedHistoryMask434,if_pos hs]
  · have hc : (out,seen) ∉ sourceOriginalActualSignedHistoryCarrierFinset434
        SP sm BP bm J ell cap := by
      intro hh
      exact hs ((source_original_ACTUAL_signed_history_mem_iff434
        SP sm BP bm J ell cap out seen).mp hh).2.1
    simp only [sourceOriginalActualSignedHistoryMask434,
      sourceOriginalActualSignedHistoryLift434,if_neg hs,dif_neg hc]

/-- Exact original G operator on the FINITE Fock×seen state carrier.
This is not a history-supremum or a surrogate matrix kernel. -/
def sourceOriginalActualSignedFiniteG434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (f : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) : ℂ :=
  sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
    q rho N i V mu a.val.1 a.val.2
    (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f)

/-- All physical values of the ORIGINAL ghost G operator on reachable
Fock/history states are recovered exactly from this finite operator.
No chronological mask reset is allowed. -/
theorem source_original_ACTUAL_signed_finite_G_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu a.val.1 a.val.2 F =
    sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap
      q rho N i V mu
      (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F)
      a := by
  classical
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  have hMask := source_original_ACTUAL_SIGNED_G_history_mask_exact434
    SP sm BP bm J ell q rho N i V mu F a.val.1 a.val.2 ha.2.1
  have hL := source_original_G_unseen_reachable_congr434
    SP sm BP bm J ell cap hi hcap
    q rho N i Vs V mu hVs hmu a.val.1 a.val.2 ha.2.2
    (sourceOriginalActualSignedHistoryMask434 SP sm BP bm J ell F)
    (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
      (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F))
    (by
      intro out seen hr
      exact source_original_ACTUAL_signed_history_mask_lift_eq434
        SP sm BP bm J ell cap hcap F out seen hr)
  exact hMask.symm.trans hL
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedFiniteE -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Original oriented signed E-frame, with its literal CLEAN/DIRTY
predicate and full joint K, as a map on the finite reachable
Fock-output × chronological numerical history space. -/
def sourceOriginalActualSignedFiniteE434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ)
    (f : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) : ℂ :=
  sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
    keep q rho Vs V mu K zeta theta o k
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
    a.val.2
    (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f)

/-- The true physical signed E-frame is recovered EXACTLY from its
finite state action for any reachable Fock output and original seen
history, with no positivity or summation over histories. -/
theorem source_original_ACTUAL_signed_finite_E_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
      a.val.2 F =
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k
      (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F)
      a := by
  classical
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1
  have hp := source_original_REACHABLE_canonical_projection434
    SP sm BP bm (J+ell) cap hcap a.val.1 a.val.2 ha.2.2
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) a.val.2 := by
    simpa only [x,hp] using ha.2.2
  have hMask := source_original_ACTUAL_SIGNED_E_history_mask_exact434
    SP sm BP bm J ell m cap patterns keep
    q rho Vs V mu K zeta theta o k F x a.val.2 ha.2.1
  have hLift := source_original_ACTUAL_FILTERED_E_reachable_congr434
    SP sm BP bm J ell m cap patterns keep
    q rho Vs V mu K zeta theta o k
    x a.val.2 hx
    (sourceOriginalActualSignedHistoryMask434 SP sm BP bm J ell F)
    (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
      (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F))
    (by
      intro out st hr
      exact source_original_ACTUAL_signed_history_mask_lift_eq434
        SP sm BP bm J ell cap hcap F out st hr)
  calc
    _ = sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k x a.val.2
        (sourceOriginalActualSignedHistoryMask434 SP sm BP bm J ell F) := hMask.symm
    _ = sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k x a.val.2
        (sourceOriginalActualSignedHistoryMask434 SP sm BP bm J ell F) :=
      (source_original_SOURCE_MARKED_FILTERED_E_frame_row434
        SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k
        x a.val.2 hx _).symm
    _ = sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k x a.val.2
        (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
          (sourceOriginalActualSignedHistoryRestrict434 SP sm BP bm J ell cap F)) := hLift
    _ = _ := by
      exact source_original_SOURCE_MARKED_FILTERED_E_frame_row434
        SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k
        x a.val.2 hx _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedFiniteLiftLinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Linear terminal HISTORY restriction lift: sums retain their true
Fock output and chronological seen, without an auxiliary history sum. -/
theorem source_original_ACTUAL_signed_lift_add434
    (f g : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ) :
    sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap (fun z => f z+g z) =
      (fun out st =>
        sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f out st +
        sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap g out st) := by
  classical
  funext out st
  unfold sourceOriginalActualSignedHistoryLift434
  split_ifs <;> ring

theorem source_original_ACTUAL_signed_lift_smul434
    (c : ℂ) (f : sourceOriginalActualSignedHistoryState434
      SP sm BP bm J ell cap → ℂ) :
    sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap (fun z => c*f z) =
      (fun out st =>
        c*sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f out st) := by
  classical
  funext out st
  unfold sourceOriginalActualSignedHistoryLift434
  split_ifs <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedEScalar -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 14000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

variable (m : ℕ) {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Complex scalar linearity of the literal oriented and filtered
signed source E frame; all phases and joint K remain unchanged. -/
theorem source_original_ACTUAL_SIGNED_FILTERED_E_smul434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (c : ℂ) (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen
      (fun out st => c*F out st) =
    c*sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F := by
  classical
  unfold sourceOriginalSourceEFrameFilteredRow434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434
      SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434
        SP sm BP bm J ell m cap patterns x seen o k r f
  · simp only [dif_pos h]
    by_cases hk : keep x (sourceOriginalSourceEFrameLift434
        SP sm BP bm J ell m cap patterns x r (Classical.choose h))
    · simp only [if_pos hk]
      ring
    · simp only [if_neg hk, mul_zero]
  · simp only [dif_neg h,mul_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedFiniteEAdd -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 4500000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

variable (m : ℕ) {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

theorem source_original_ACTUAL_finite_E_add434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (f g : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k (fun z => f z+g z) a =
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k f a +
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k g a := by
  unfold sourceOriginalActualSignedFiniteE434
  rw [source_original_ACTUAL_signed_lift_add434]
  exact source_original_ACTUAL_SIGNED_FILTERED_E_add434
    SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1) a.val.2 _ _


end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedFiniteESmul -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 4500000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

variable (m : ℕ) {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

theorem source_original_ACTUAL_finite_E_smul434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (c : ℂ)
    (f : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k (fun z => c*f z) a =
    c*sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k f a := by
  classical
  unfold sourceOriginalActualSignedFiniteE434 sourceOriginalSourceEFrameFilteredRow434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1
  by_cases h : ∃ z : SourceOriginalSourceEFrameInjections434
      SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434
        SP sm BP bm J ell m cap patterns x a.val.2 o k r z
  · dsimp only [x] at h
    simp only [dif_pos h]
    let z := sourceOriginalSourceEFrameLift434
      SP sm BP bm J ell m cap patterns x r (Classical.choose h)
    by_cases hk : keep x z
    · dsimp only [x,z] at hk
      simp only [if_pos hk]
      unfold sourceOriginalActualSignedHistoryLift434
      split_ifs <;> ring
    · dsimp only [x,z] at hk
      simp only [if_neg hk,mul_zero]
  · dsimp only [x] at h
    simp only [dif_neg h,mul_zero]



end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedGScalar -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 14000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Complex scalar linearity of the true ghost G with its original
no-rebirth gate, Fock output and chronological numeric history. -/
theorem source_original_ACTUAL_SIGNED_G_smul434
    (c : ℂ) (q rho : ℝ) (N i : ℕ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (fun out st => c*F out st) =
    c*sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen F := by
  classical
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedFiniteGLinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 9000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The actual finite Fock×seen ghost operator is additive. -/
theorem source_original_ACTUAL_finite_G_add434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f g : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :
    sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap q rho N i V mu
        (fun z => f z+g z) a =
      sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap q rho N i V mu f a +
      sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap q rho N i V mu g a := by
  unfold sourceOriginalActualSignedFiniteG434
  rw [source_original_ACTUAL_signed_lift_add434]
  exact source_original_ACTUAL_SIGNED_G_add434
    SP sm BP bm J ell q rho N i V mu a.val.1 a.val.2 _ _

theorem source_original_ACTUAL_finite_G_smul434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (c : ℂ) (f : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap → ℂ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :
    sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap q rho N i V mu
        (fun z => c*f z) a =
      c*sourceOriginalActualSignedFiniteG434 SP sm BP bm J ell cap q rho N i V mu f a := by
  unfold sourceOriginalActualSignedFiniteG434
  rw [source_original_ACTUAL_signed_lift_smul434]
  exact source_original_ACTUAL_SIGNED_G_smul434
    SP sm BP bm J ell c q rho N i V mu a.val.1 a.val.2 _
end Green64Analytic.CorrelationSquare

end

end

