module

public import Green64.Library.Weights.Part070
public import Green64.Library.Correlation.Part050
public import Green64.Library.Correlation.Part052
public import Green64.Library.Weights.Part064
public import Green64.Library.Correlation.Part053
public import Green64.Library.Weights.Part068
public import Mathlib.Analysis.Fourier.AddCircle
public import Green64.Library.Weights.Part024
public import Green64.Library.Weights.Part066
public import Green64.Library.Weights.ActualSignedGhostMatrix

@[expose] public section

/-!
# Weights / Part071

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSourceFixedSchedule -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exactly the prior compatible projected-DIRTY J, fixed before L. -/
def sourceOriginalActualSourceJ434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ)
    (rho c0 Bdirty : ℝ) : ℕ :=
  let E := sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi cfg.q0
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let C := sourceOriginalMemoryEColumnLoss434 cfg ell Cq Cxi cfg.q0 rho
  sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfg.C0 K
    (2*(Bdirty+1)+C+E)

/-- The fixed slot count simultaneously satisfies the earlier DIRTY
inequality and has M<=L with positive OLD margin on every actual moving
source family. Neither M<=L nor an abstract group bound is assumed here. -/
theorem source_original_ACTUAL_SOURCE_J_and_OLD_margin434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (rho c0 Bdirty : ℝ) (hc0 : 0 < c0) :
    let J := sourceOriginalActualSourceJ434 cfg ell Jmin Cq Cxi rho c0 Bdirty
    let E := sourceOriginalMemoryERowLoss434 cfg ell Cq Cxi cfg.q0
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    max Jmin cfg.tmax ≤ J ∧
    2*Bdirty+2*E+2*cfg.C0*Real.log K+5 ≤
      c0*Real.log (((J+ell).choose ell:ℕ):ℝ) ∧
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp),
      ((J+ell:ℕ):ℝ) ≤ L ∧ 0 < Nat.ceil (L^2/4) ∧
      Nat.ceil (L^2/4)+Fintype.card β*((2*Nat.ceil (L^(0.52:ℝ))+1)*(J+ell))
        < Nat.ceil (L^2) := by
  dsimp only
  let J := sourceOriginalActualSourceJ434 cfg ell Jmin Cq Cxi rho c0 Bdirty
  have hj := source_original_memory_PROJECTED_DIRTY_parameter_budget434
    cfg ell Jmin Cq Cxi hell cfg.q0 rho c0 Bdirty hc0
  refine ⟨hj.1,hj.2,?_⟩
  filter_upwards [eventually_source_original_B26_fixed_slots_budget434 J ell,
    eventually_source_original_MEMORY_OLD_positive_margin434 cfg.C0 cfg.hC0]
    with L hM hMargin
  intro ι β _ _ _ _ x Y Hp u
  have hM' : ((J+ell:ℕ):ℝ) ≤ L := by simpa using hM
  exact ⟨hM',hMargin (Fintype.card β) (J+ell) u.hBigGroups hM'⟩

/-- The actual candidate q0=1/2 admits a compatible rho, without
altering q0 to obtain the numerical witness. No free rho decay is used. -/
theorem source_original_ACTUAL_SOURCE_q_half_rho_witness434 :
    0 < (1/2:ℝ) ∧ (1/2:ℝ) < 1 ∧
    0 < Real.sqrt (3/4:ℝ) ∧ Real.sqrt (3/4:ℝ) < 1 ∧
    Real.sqrt (1/2:ℝ) < (Real.sqrt (3/4:ℝ))^2 := by
  have hr : 0 < Real.sqrt (3/4:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hrr := Real.sq_sqrt (by norm_num : 0 ≤ (3/4:ℝ))
  have hq := Real.sq_sqrt (by norm_num : 0 ≤ (1/2:ℝ))
  have hq0 := Real.sqrt_nonneg (1/2:ℝ)
  refine ⟨by norm_num,by norm_num,hr,?_,?_⟩
  · nlinarith
  · nlinarith

/-- The source polynomial caps have simultaneous concrete witnesses;
the exponent choice is fixed before the scale. -/
theorem source_original_ACTUAL_SOURCE_polynomial_cap_witness434
    (Cq Cxi : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    (Nat.floor (L^Cq):ℝ) ≤ L^Cq ∧
    0 < L^(-(Cxi:ℝ)) ∧ (L^(-(Cxi:ℝ)))⁻¹ ≤ L^Cxi := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  refine ⟨Nat.floor_le (pow_nonneg hLp.le _),Real.rpow_pos_of_pos hLp _,?_⟩
  rw [Real.rpow_neg hLp.le,inv_inv,Real.rpow_natCast]

/-- The same source tail saving instantiated with the actual fixed J
chosen for DIRTY. J is not allowed to grow after the asymptotic threshold. -/
theorem eventually_source_original_ACTUAL_SOURCE_projected_J_birth_tail_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (rho c0 Bdirty Btail : ℝ) (hc0 : 0 < c0) (hBtail : 0 ≤ Btail) :
    let J := sourceOriginalActualSourceJ434 cfg ell Jmin Cq Cxi rho c0 Bdirty
    ∃ hmJ : cfg.tmax ≤ J,
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hi : Function.Injective
        (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
        Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (blockA blockB : Finset β) (Q : ℕ) (hQ : (Q:ℝ) ≤ L^Cq)
      (hA hB : SourceOriginalProbePattern434 β cfg.tmax → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB cfg.tmax,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB cfg.tmax,0 < hB nu)
      (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi) (zeta theta : ℝ) (k : ℤ),
      ‖sourceOriginalActualSourceBirthTail434 u blockA blockB J ell cfg.tmax hmJ Q hA hB
        xi zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2/4))‖ ≤ L^(-Btail) := by
  dsimp only
  let J := sourceOriginalActualSourceJ434 cfg ell Jmin Cq Cxi rho c0 Bdirty
  have hj := source_original_memory_PROJECTED_DIRTY_parameter_budget434
    cfg ell Jmin Cq Cxi hell cfg.q0 rho c0 Bdirty hc0
  have hmJ : cfg.tmax ≤ J := (le_max_right Jmin cfg.tmax).trans hj.1
  exact ⟨hmJ,eventually_source_original_ACTUAL_SOURCE_birth_tail_saving434
    cfg J ell cfg.tmax Cq Cxi hmJ Btail hBtail⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourcePositiveEnvelope -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal source S/Ts/Tb specialization of the already established root.
All SMALL and BIG prime nonzero instances follow from the original primes. -/
def sourceOriginalActualSourcePositiveTailEnvelope434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi zeta theta : ℝ)
    (k : ℤ) (R H : ℕ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  letI (g : Option ι) (p : {p : ℕ // p ∈ P g}) : NeZero p.val :=
    ⟨(source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property |>.ne_zero⟩
  letI (g : β) (p : {p : ℕ // p ∈ u.Tb g}) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  exact ((2:ℝ)^H)⁻¹ * sourceOriginalAbsoluteCommonMemoryRoot434
    (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
    (fun g => {p : ℕ // p ∈ u.Tb g}) (fun _ p => p.val) J ell m
    (fun g => Fintype.card {p : ℕ // p ∈ u.Tb g})
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    cfg.q0 2 (sourceOriginalActualSmallMass434 u) u.Vbig
    (sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
      J ell m hmJ Q hA hB xi) zeta theta k R

/-- The actual POSITIVE envelope has arbitrary fixed logarithmic saving.
It includes the factor 2^(-H), all absolute G/E weights, actual outer
Fock/vacuum masses and initial SMALL boundary. This stronger form is
needed to bound temporally masked signed discrepancies.
J and every polynomial exponent are fixed BEFORE the threshold. The
original physical hypotheses (BIG distinctness, harmonic normalization,
lower prime scale) remain explicit; no M, alphabet or operator cap is added. -/
theorem eventually_source_original_ACTUAL_SOURCE_positive_tail_envelope_saving434
    (cfg : SourceComparisonFixed434) (J ell m Cq Cxi : ℕ) (hmJ : m ≤ J)
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hi : Function.Injective
        (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
        Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (blockA blockB : Finset β) (Q : ℕ) (hQ : (Q:ℝ) ≤ L^Cq)
      (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi) (zeta theta : ℝ) (k : ℤ),
      sourceOriginalActualSourcePositiveTailEnvelope434 u blockA blockB J ell m hmJ Q hA hB
        xi zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2/4)) ≤ L^(-B) := by
  let Cb : ℝ := 16*max 1 cfg.vmin⁻¹
  let Enu : ℝ := (m:ℝ)*(2*cfg.C0)*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1
  let Es : ℝ := sourceOriginalB26SmallNormExponent434
    ell (Real.sqrt cfg.q0) cfg.vmin (cfg.C0+1)
  let CE : ℝ := Enu+Es
  have hCG : 0 ≤ cfg.C0 := cfg.hC0
  have hCS : 0 ≤ cfg.C0+1 := by linarith [cfg.hC0]
  have hCb : 1 ≤ Cb := by
    have hh := le_max_left (1:ℝ) cfg.vmin⁻¹
    dsimp only [Cb]
    linarith
  have hEnu : 0 ≤ Enu := by
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [Enu]
    positivity
  have hEs : 0 ≤ Es :=
    source_original_B26_small_norm_exponent_nonneg434
      ell (Real.sqrt cfg.q0) cfg.vmin (cfg.C0+1) hCS
  have hCE : 0 ≤ CE := add_nonneg hEnu hEs
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
    eventually_source_original_ACTUAL_SMALL_source_boundary434 cfg J ell,
    eventually_source_original_ACTUAL_common_positive_root_explicit_cost434
      cfg.cexp cfg.vmin hc cfg.hv,
    eventually_source_original_ACTUAL_full_birth_cost_budget434
      Cb cfg.C0 CE (cfg.C0+1) cfg.vmin B hCb cfg.hC0 hCE hCS cfg.hv hB (ell+m)]
      with L hL he hSmall hRoot hBudget
  intro ι β _ _ _ _ x Y Hp u hi hHarmonic hmin blockA blockB Q hQ hA hB hhxi
    hhA hhB hxi hXi zeta theta k
  let xi := hhxi
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) he
    simpa using hh
  let P := sourceOriginalActualSmallPrimeSets434 u
  let Vs := sourceOriginalActualSmallMass434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  have hsb := source_original_ACTUAL_SMALL_source_bounds434 u
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨(hsb.1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  have hVs (g : Option ι) : 0 < Vs g := cfg.hv.trans_le (hsb.2.2 g)
  have hmax (g : β) (p : BP g) : (p.val:ℝ) ≤ Real.exp (Real.sqrt L) := by
    apply u.hGroup
    rw [u.hG]
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,p.property⟩))
  have hBlock : (((blockA.card+blockB.card):ℕ):ℝ) ≤ (2*cfg.C0)*Real.log L := by
    have ha : (blockA.card:ℝ) ≤ (Fintype.card β:ℝ) := by
      exact_mod_cast Finset.card_le_univ blockA
    have hb : (blockB.card:ℝ) ≤ (Fintype.card β:ℝ) := by
      exact_mod_cast Finset.card_le_univ blockB
    push_cast
    nlinarith only [ha,hb,u.hBigGroups]
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let H := Nat.ceil (L^2/4)
  let S0 : ℝ := ∏ g : Option ι,((Fintype.card (SP g):ℝ)/Vs g)^(J+ell)
  let Cnu : ℝ := ∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
    sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu
  let Cs : ℝ := ∏ g : Option ι,memorySmallRowConstant cfg.q0 (Vs g) ell
  let E0 : ℝ := Real.exp ((cfg.C0+1)*L*Real.log L*
    (Real.sqrt L+Real.log (max 1 cfg.vmin⁻¹)))
  let G0 : ℝ := Real.exp (4*((N+1:ℕ):ℝ)*(1+Real.sqrt L))
  let F : ℝ := Cb*Real.exp (Real.sqrt L)
  have hF : 0 ≤ F := mul_nonneg (zero_le_one.trans hCb) (Real.exp_pos _).le
  have hnu : Cnu ≤ L^Enu :=
    source_original_memory_RAW_COMPARISON_cap_budget434 blockA blockB m Q
      L (2*cfg.C0) xi Cq Cxi hL (by positivity) hxi hBlock hQ hXi
  have hcs : Cs ≤ L^Es :=
    source_original_memory_SMALL_absolute_row_polynomial434 ell cfg.q0 cfg.vmin
      (cfg.C0+1) L cfg.hq0 cfg.hq1 cfg.hv hCS hL1 Vs hsb.2.2
      (source_original_ACTUAL_SMALL_group_count434 u hlog)
  have hnu0 : 0 ≤ Cnu := Finset.sum_nonneg
    (fun nu _ => source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu)
  have hcs0 : 0 ≤ Cs := by
    have hs : 0 < 1-Real.sqrt cfg.q0 := by
      nlinarith only [Real.sq_sqrt cfg.hq0.le,Real.sqrt_nonneg cfg.q0,cfg.hq1]
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hpoly : Cnu*Cs ≤ L^CE := by
    calc
      _ ≤ L^Enu*L^Es := mul_le_mul hnu hcs hcs0 (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [←Real.rpow_add hLp]
  have hS0 : S0 ≤ E0 := by
    simpa only [S0,SP,Vs,P,Fintype.card_coe,E0] using hSmall u
  have hS00 : 0 ≤ S0 := Finset.prod_nonneg
    (fun g _ => pow_nonneg (div_nonneg (Nat.cast_nonneg _) (hVs g).le) _)
  have hPow : (Cnu*Cs*F^((ell+m)*Fintype.card β))^N ≤
      (L^CE*F^((ell+m)*Fintype.card β))^N :=
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg hnu0 hcs0) (pow_nonneg hF _))
      (mul_le_mul_of_nonneg_right hpoly (pow_nonneg hF _)) N
  have hSource := hRoot SP (fun _ p => p.val) u.Tb hi cfg.q0 cfg.hq0 cfg.hq1 Vs hVs
    u.Vbig u.hVbig hHarmonic hmin hmax blockA blockB J ell m hmJ Q hA hB xi
    hhA hhB hxi zeta theta k 2 (by norm_num) H
  have hSource' :
      sourceOriginalActualSourcePositiveTailEnvelope434 u blockA blockB J ell m hmJ Q hA hB
        xi zeta theta k (Nat.ceil (L^(0.52:ℝ))) H ≤
      ((2:ℝ)^H)⁻¹*S0*(G0*(Cnu*Cs*F^((ell+m)*Fintype.card β))^N) := by
    convert hSource using 1 <;>
      simp only [sourceOriginalActualSourcePositiveTailEnvelope434,P,SP,Vs,N,H,S0,G0,Cnu,Cs,F,Cb] <;>
      congr 2 <;> push_cast <;> ring
  have hFinal := hBudget (Fintype.card β) u.hBigGroups
  apply hSource'.trans
  calc
    _ ≤ ((2:ℝ)^H)⁻¹*E0*(G0*(L^CE*F^((ell+m)*Fintype.card β))^N) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hS0 (by positivity)
      · exact mul_le_mul_of_nonneg_left hPow (Real.exp_pos _).le
      · exact mul_nonneg (Real.exp_pos _).le
          (pow_nonneg (mul_nonneg (mul_nonneg hnu0 hcs0) (pow_nonneg hF _)) _)
      · positivity
    _ = ((2:ℝ)^H)⁻¹*E0*G0*
        F^((ell+m)*Fintype.card β*N)*L^(CE*(N:ℝ)) := by
      rw [mul_pow,←pow_mul]
      have hp : (L^CE)^N=L^(CE*(N:ℝ)) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
      rw [hp]
      ring
    _ ≤ L^(-B) := by
      simpa only [H,E0,G0,F,N,Cb] using hFinal
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceOLDRemoval -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- ORIGINAL signed source root minus the root with both total-OLD
projectors at every E visit, specialized to the full S/Ts/Tb family and
canonical RAW/comparison K. No terminal birth or parity observable is
substituted for the original vacuum/seen construction. -/
def sourceOriginalActualSourceOLDDiscrepancy434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi rho zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  letI (g : Option ι) (p : {p : ℕ // p ∈ P g}) : NeZero p.val :=
    ⟨(source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property |>.ne_zero⟩
  letI (g : β) (p : {p : ℕ // p ∈ u.Tb g}) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let SP := fun g => {p : ℕ // p ∈ P g}
  let BP := fun g => {p : ℕ // p ∈ u.Tb g}
  let cap := fun g => Fintype.card (BP g)
  let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
    J ell m hmJ Q hA hB xi
  exact memorySourceRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m patterns cap cfg.q0 rho (sourceOriginalActualSmallMass434 u) u.Vbig
      K zeta theta k R -
    sourceOriginalOLDProjectedMemoryRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns cfg.q0 rho (sourceOriginalActualSmallMass434 u) u.Vbig
      K zeta theta k R T

/-- Arbitrary fixed logarithmic saving for the TRUE signed OLD-projector
discrepancy. The threshold precedes all moving source groups, alphabets,
meshes, phase tests and rho. The true source hypotheses are retained.
No M<=L, small-alphabet cap, active-continuation norm or discrepancy bound
is assumed. Both E-endpoint projectors use the original ceil(L^2). -/
theorem eventually_source_original_ACTUAL_SOURCE_OLD_projector_removal434
    (cfg : SourceComparisonFixed434) (J ell m Cq Cxi : ℕ) (hmJ : m ≤ J)
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hi : Function.Injective
        (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
        Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (blockA blockB : Finset β) (Q : ℕ) (hQ : (Q:ℝ) ≤ L^Cq)
      (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (rho : ℝ) (hrho : rho ≠ 0) (zeta theta : ℝ) (k : ℤ),
      ‖sourceOriginalActualSourceOLDDiscrepancy434 u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))‖ ≤ L^(-B) := by
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [
    eventually_source_original_ACTUAL_SOURCE_positive_tail_envelope_saving434 cfg J ell m Cq Cxi hmJ B hB,
    eventually_source_original_B26_fixed_slots_budget434 J ell,
    eventually_source_original_MEMORY_OLD_positive_margin434 cfg.C0 cfg.hC0,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hEnvelope hSlots hMargin hVisits
  intro ι β _ _ _ _ x Y Hp u hi hHarmonic hmin blockA blockB Q hQ hA hB xi
    hhA hhB hxi hXi rho hrho zeta theta k
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  let bm := fun (g : β) (p : BP g) => p.val
  have hsb := source_original_ACTUAL_SMALL_source_bounds434 u
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨(hsb.1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let R := Nat.ceil (L^(0.52:ℝ))
  let N := 2*R
  let H := Nat.ceil (L^2/4)
  let T := Nat.ceil (L^2)
  let Vs := sourceOriginalActualSmallMass434 u
  have hVs (g : Option ι) : 0 < Vs g := cfg.hv.trans_le (hsb.2.2 g)
  have hV (g : β) : 0 < u.Vbig g := cfg.hv.trans_le (u.hVbig g)
  have hmu (g : β) (p : BP g) : 0 < physicalSourceMuTilde BP bm cfg.q0 N u.Vbig g p := by
    have hb := (source_original_B26_physical_baseline_half434 BP bm cfg.q0 cfg.hq0.le cfg.hq1.le
      N g p (hVisits p.val (hmin g p))).1
    have hb0 : 0 < physicalSourceBaseline BP bm cfg.q0 N g p := by linarith
    have hp : (0:ℝ) < bm g p := by exact_mod_cast NeZero.pos (bm g p)
    have hv := hV g
    dsimp only [physicalSourceMuTilde]
    positivity
  have hSlots' : ((J+ell:ℕ):ℝ) ≤ L := by simpa using hSlots
  have hm0 := (hMargin (Fintype.card β) (J+ell) u.hBigGroups hSlots').2
  have hm : H+(2*R+1)*(Fintype.card β*(J+ell)) ≤ T := by
    dsimp only [H,R,T]
    nlinarith only [hm0]
  have hBound := source_original_ACTUAL_OLD_projector_discrepancy_common434
    SP (fun _ p => p.val) BP bm J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    hi (fun _ => le_rfl) cfg.q0 rho 2 hrho (by norm_num) Vs u.Vbig
    (sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
      J ell m hmJ Q hA hB xi) zeta theta k R T H hVs hmu hm
  have hBound' :
      ‖sourceOriginalActualSourceOLDDiscrepancy434 u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T‖ ≤
      sourceOriginalActualSourcePositiveTailEnvelope434 u blockA blockB J ell m hmJ Q hA hB
        xi zeta theta k R H := by
    simpa only [sourceOriginalActualSourceOLDDiscrepancy434,
      sourceOriginalActualSourcePositiveTailEnvelope434,SP,BP,P,bm,Vs,N] using hBound
  exact hBound'.trans
    (hEnvelope u hi hHarmonic hmin blockA blockB Q hQ hA hB xi
      hhA hhB hxi hXi zeta theta k)

/-- The OLD-removal saving uses the same fixed compatible J as projected
DIRTY. The explicit J and every exponent precede the L threshold. -/
theorem eventually_source_original_ACTUAL_SOURCE_projected_J_OLD_removal434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (rho c0 Bdirty Btail : ℝ) (hrho : rho ≠ 0) (hc0 : 0 < c0) (hBtail : 0 ≤ Btail) :
    let J := sourceOriginalActualSourceJ434 cfg ell Jmin Cq Cxi rho c0 Bdirty
    ∃ hmJ : cfg.tmax ≤ J,
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hi : Function.Injective
        (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
        Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (blockA blockB : Finset β) (Q : ℕ) (hQ : (Q:ℝ) ≤ L^Cq)
      (hA hB : SourceOriginalProbePattern434 β cfg.tmax → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB cfg.tmax,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB cfg.tmax,0 < hB nu)
      (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi) (zeta theta : ℝ) (k : ℤ),
      ‖sourceOriginalActualSourceOLDDiscrepancy434 u blockA blockB J ell cfg.tmax hmJ Q hA hB
        xi rho zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))‖ ≤ L^(-Btail) := by
  dsimp only
  let J := sourceOriginalActualSourceJ434 cfg ell Jmin Cq Cxi rho c0 Bdirty
  have hj := source_original_memory_PROJECTED_DIRTY_parameter_budget434
    cfg ell Jmin Cq Cxi hell cfg.q0 rho c0 Bdirty hc0
  have hmJ : cfg.tmax ≤ J := (le_max_right Jmin cfg.tmax).trans hj.1
  refine ⟨hmJ,?_⟩
  filter_upwards [eventually_source_original_ACTUAL_SOURCE_OLD_projector_removal434
    cfg J ell cfg.tmax Cq Cxi hmJ Btail hBtail] with L hL
  intro ι β _ _ _ _ x Y Hp u hi hHarmonic hmin blockA blockB Q hQ hA hB xi
    hhA hhB hxi hXi zeta theta k
  exact hL u hi hHarmonic hmin blockA blockB Q hQ hA hB xi
    hhA hhB hxi hXi rho hrho zeta theta k
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourcePhysicalDIRTYReduction -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Original signed source root minus full OLD-projected CLEAN root. -/
def sourceOriginalActualSourceCleanGap434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi rho zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  letI (g : Option ι) (p : {p : ℕ // p ∈ P g}) : NeZero p.val :=
    ⟨(source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property |>.ne_zero⟩
  letI (g : β) (p : {p : ℕ // p ∈ u.Tb g}) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let SP := fun g => {p : ℕ // p ∈ P g}
  let BP := fun g => {p : ℕ // p ∈ u.Tb g}
  let cap := fun g => Fintype.card (BP g)
  let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
    J ell m hmJ Q hA hB xi
  exact memorySourceRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m patterns cap cfg.q0 rho (sourceOriginalActualSmallMass434 u) u.Vbig
      K zeta theta k R -
    sourceOriginalOLDProjectedCleanMemoryRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns cfg.q0 rho (sourceOriginalActualSmallMass434 u) u.Vbig
      K zeta theta k R T
/-- EXACT original chronological marked DIRTY insertion root, using the
physical projected E operator, not only a comparison or frame surrogate. -/
def sourceOriginalActualSourcePhysicalDIRTYRoot434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi rho zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  letI (g : Option ι) (p : {p : ℕ // p ∈ P g}) : NeZero p.val :=
    ⟨(source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property |>.ne_zero⟩
  letI (g : β) (p : {p : ℕ // p ∈ u.Tb g}) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let SP := fun g => {p : ℕ // p ∈ P g}
  let BP := fun g => {p : ℕ // p ∈ u.Tb g}
  let cap := fun g => Fintype.card (BP g)
  let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
    J ell m hmJ Q hA hB xi
  exact sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap patterns
    cfg.q0 rho (sourceOriginalActualSmallMass434 u) u.Vbig K zeta theta k R T
/-- The full ORIGINAL signed source error after CLEAN substitution is
controlled by the already-paid OLD tail and ONE physical projected
marked DIRTY insertion. No unstated per-visit energy or saving input. -/
theorem eventually_source_original_ACTUAL_SOURCE_physical_DIRTY_reduction434
    (cfg : SourceComparisonFixed434) (J ell m Cq Cxi : ℕ) (hmJ : m ≤ J)
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hi : Function.Injective
        (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
        Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (blockA blockB : Finset β) (Q : ℕ) (hQ : (Q:ℝ) ≤ L^Cq)
      (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (rho : ℝ) (hrho : rho ≠ 0) (zeta theta : ℝ) (k : ℤ),
      ‖sourceOriginalActualSourceCleanGap434 u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))‖ ≤
      L^(-B) + ‖sourceOriginalActualSourcePhysicalDIRTYRoot434 u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))‖ := by
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [eventually_source_original_ACTUAL_SOURCE_OLD_projector_removal434
    cfg J ell m Cq Cxi hmJ B hB,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc] with L hOld hVisits
  intro ι β _ _ _ _ x Y Hp u hi hHarmonic hmin blockA blockB Q hQ hA hB xi
    hhA hhB hxi hXi rho hrho zeta theta k
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  let bm := fun (g : β) (p : BP g) => p.val
  have hsb := source_original_ACTUAL_SMALL_source_bounds434 u
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨(hsb.1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let R := Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let Vs := sourceOriginalActualSmallMass434 u
  have hVs (g : Option ι) : 0 < Vs g := cfg.hv.trans_le (hsb.2.2 g)
  have hV (g : β) : 0 < u.Vbig g := cfg.hv.trans_le (u.hVbig g)
  have hmu (g : β) (p : BP g) :
      0 < physicalSourceMuTilde BP bm cfg.q0 (2*R) u.Vbig g p := by
    have hb := (source_original_B26_physical_baseline_half434 BP bm cfg.q0
      cfg.hq0.le cfg.hq1.le (2*R) g p (hVisits p.val (hmin g p))).1
    have hb0 : 0 < physicalSourceBaseline BP bm cfg.q0 (2*R) g p := by linarith
    have hp : (0:ℝ) < bm g p := by exact_mod_cast NeZero.pos (bm g p)
    have hv := hV g
    dsimp only [physicalSourceMuTilde]
    positivity
  have hSplit := source_original_MEMORY_full_to_CLEAN_error_split434
    SP (fun _ p => p.val) BP bm J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    hi (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig
    (sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
      J ell m hmJ Q hA hB xi) zeta theta k R T hVs hmu
  have hs :
      ‖sourceOriginalActualSourceCleanGap434 u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T‖ ≤
      ‖sourceOriginalActualSourceOLDDiscrepancy434 u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T‖ +
      ‖sourceOriginalActualSourcePhysicalDIRTYRoot434 u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T‖ := by
    simpa only [sourceOriginalActualSourceCleanGap434,
      sourceOriginalActualSourcePhysicalDIRTYRoot434,
      sourceOriginalActualSourceOLDDiscrepancy434,SP,BP,P,bm,Vs] using hSplit
  apply hs.trans
  exact add_le_add (hOld u hi hHarmonic hmin blockA blockB Q hQ hA hB xi
    hhA hhB hxi hXi rho hrho zeta theta k) le_rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceCoherentVisitGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Actual S+Ts/Tb contribution of visit j, with the original
joint RAW/comparison K and the complete unreset birth history. -/
def sourceOriginalActualSourceSignedCoherentDIRTYVisit434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T j : ℕ) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  exact sourceOriginalActualSignedPostGhostVisit434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K zeta theta k R T j

/-- No positive TV envelope: the ORIGINAL source first-DIRTY root
has an exact Hermitian double-visitation signed Gram. There are
no new analytic hypotheses. Positivity of the actual BIG baseline
is an explicit finite-L admissibility condition, not a saving. -/
theorem source_original_ACTUAL_SOURCE_SIGNED_coherent_DIRTY_gram434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    star (sourceOriginalActualSourcePhysicalDIRTYRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T) *
    sourceOriginalActualSourcePhysicalDIRTYRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T =
    (star (physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
      (physicalSourceBaselineProduct
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) : ℂ)) *
    (∑ i ∈ Finset.range (2*R), ∑ j ∈ Finset.range (2*R),
      star (sourceOriginalActualSourceSignedCoherentDIRTYVisit434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T i) *
      sourceOriginalActualSourceSignedCoherentDIRTYVisit434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T j) := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hmu (g : β) (p : BP g) :
      0 < physicalSourceMuTilde BP (fun _ p => p.val)
        cfg.q0 (2*R) u.Vbig g p := by
    have hp : (0:ℝ) < (p.val:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos p.val)
    have hv : 0 < u.Vbig g := cfg.hv.trans_le (u.hVbig g)
    have hbp := hb g p
    unfold physicalSourceMuTilde
    positivity
  have h := source_original_ACTUAL_signed_postghost_DIRTY_coherent_gram434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    hi (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig hVs K
    zeta theta k R T hmu
  simpa only [sourceOriginalActualSourcePhysicalDIRTYRoot434,
    sourceOriginalActualSourceSignedCoherentDIRTYVisit434,
    SP, BP, P, Vs, K] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceSignedRootPairing -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exactly signed ORIGINAL S+Ts/Tb first-DIRTY prefix/suffix Fock root,
with the canonical RAW/comparison joint K and ONE cumulative numerical
seen history, transported by the original complex CLEAN transpose.
A finite arithmetic object, not a hypothesized saving. -/
def sourceOriginalActualSourceSignedDIRTYPairingRHS434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0 (2*R) u.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
    J ell m hmJ Q hA hB xi
  let cap := fun g : β => Fintype.card (BP g)
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
    (sourceOriginalCleanChoice434 SP (fun _ p => p.val)
      BP (fun _ p => p.val) J ell m cap pats)
    cfg.q0 rho Vs u.Vbig mu K zeta theta k (2*R) T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m cap pats
    (fun x z => ¬ sourceOriginalCleanChoice434 SP (fun _ p => p.val)
      BP (fun _ p => p.val) J ell m cap pats x z)
    cfg.q0 rho Vs u.Vbig mu K zeta theta k (2*R) T
  let H := sourceOriginalActualSignedHistoryState434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap
  let w := sourceOriginalActualSignedInitialWeight434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap (fun _ => le_rfl) Vs mu
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap cfg.q0 rho u.Vbig mu (2*R) (2*R)
    (fun out _ => physicalVacuum SP (fun _ p => p.val)
      BP (fun _ p => p.val) J ell out)
  exact (physicalSourceBaselineProduct BP (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    ∑ j ∈ Finset.range (2*R), ∑ b : H,
      sourceOriginalSignedForwardPrefix434 Clean j 0 w b *
      sourceOriginalSignedMatrixAction434 (Dirty j)
        (sourceOriginalSignedMatrixChain434
          (sourceOriginalSignedKernelAdd434 Clean Dirty)
          ((2*R)-(j+1)) (j+1) f) b

/-- The exact ORIGINAL moving source physical DIRTY root equals its
signed complex CLEAN-prefix/DIRTY/FULL-suffix bilinear expression.
No missing source S, no history maximum, no independent endpoint
signs and no extra global energy or cancellation hypothesis. -/
theorem source_original_ACTUAL_SOURCE_signed_DIRTY_root_prefix_suffix434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceMuTilde (fun g => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) u.Vbig g p) :
    sourceOriginalActualSourcePhysicalDIRTYRoot434 u blockA blockB
      J ell m hmJ Q hA hB xi rho zeta theta k R T =
    sourceOriginalActualSourceSignedDIRTYPairingRHS434 u blockA blockB
      J ell m hmJ Q hA hB xi rho zeta theta k R T := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
    J ell m hmJ Q hA hB xi
  have h := source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_prefix_suffix434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g)) pats
    hi (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K zeta theta k R T hVs hmu
  simpa only [sourceOriginalActualSourcePhysicalDIRTYRoot434,
    sourceOriginalActualSourceSignedDIRTYPairingRHS434,SP,BP,P,Vs] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceCoherentCleanGap -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact original source first-DIRTY amplitude, keeping all complex
chronological interference, rather than a positive TV or squared envelope. -/
theorem source_original_ACTUAL_SOURCE_signed_DIRTY_visit_identity434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    sourceOriginalActualSourcePhysicalDIRTYRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T =
    (physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    (∑ j ∈ Finset.range (2*R),
      sourceOriginalActualSourceSignedCoherentDIRTYVisit434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T j) := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hmu (g : β) (p : BP g) :
      0 < physicalSourceMuTilde BP (fun _ p => p.val)
        cfg.q0 (2*R) u.Vbig g p := by
    have hp : (0:ℝ) < (p.val:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos p.val)
    have hv : 0 < u.Vbig g := cfg.hv.trans_le (u.hVbig g)
    have hbp := hb g p
    unfold physicalSourceMuTilde
    positivity
  have h := source_original_ACTUAL_signed_physical_root_post_G_pair434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    hi (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K
    zeta theta k R T hVs hmu
  simpa only [sourceOriginalActualSourcePhysicalDIRTYRoot434,
    sourceOriginalActualSourceSignedCoherentDIRTYVisit434,
    sourceOriginalActualSignedPostGhostVisit434,
    SP, BP, P, Vs, K] using h


/-- Pointwise COMPLEX decomposition of the original-minus-CLEAN
source error. The only remainder is the independently controlled OLD tail.
No SMALL-group separation, harmonic smallness, or TV gain is assumed.
The chronological signed visits share one actual physical seen history. -/
theorem source_original_ACTUAL_SOURCE_signed_CLEAN_gap_identity434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    sourceOriginalActualSourceCleanGap434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T =
    sourceOriginalActualSourceOLDDiscrepancy434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T +
    (physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    (∑ j ∈ Finset.range (2*R),
      sourceOriginalActualSourceSignedCoherentDIRTYVisit434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T j) := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hmu (g : β) (p : BP g) :
      0 < physicalSourceMuTilde BP (fun _ p => p.val)
        cfg.q0 (2*R) u.Vbig g p := by
    have hp : (0:ℝ) < (p.val:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos p.val)
    have hv : 0 < u.Vbig g := cfg.hv.trans_le (u.hVbig g)
    have hbp := hb g p
    unfold physicalSourceMuTilde
    positivity
  have hP := source_original_MEMORY_PEP_PCLEAN_physical_DIRTY_general434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    hi (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K
    zeta theta k R T hVs hmu
  have hGap :
      sourceOriginalActualSourceCleanGap434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T =
      sourceOriginalActualSourceOLDDiscrepancy434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T +
      sourceOriginalActualSourcePhysicalDIRTYRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T := by
    change (memorySourceRoot SP (fun _ p => p.val)
        BP (fun _ p => p.val) J ell m
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        (fun g => Fintype.card (BP g)) cfg.q0 rho Vs u.Vbig
        K zeta theta k R -
      sourceOriginalOLDProjectedCleanMemoryRoot434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell m (fun g => Fintype.card (BP g))
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        cfg.q0 rho Vs u.Vbig K zeta theta k R T) =
      (memorySourceRoot SP (fun _ p => p.val)
        BP (fun _ p => p.val) J ell m
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        (fun g => Fintype.card (BP g)) cfg.q0 rho Vs u.Vbig
        K zeta theta k R -
      sourceOriginalOLDProjectedMemoryRoot434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell m (fun g => Fintype.card (BP g))
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        cfg.q0 rho Vs u.Vbig K zeta theta k R T) +
      sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell m (fun g => Fintype.card (BP g))
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        cfg.q0 rho Vs u.Vbig K zeta theta k R T
    rw [←hP]
    ring
  rw [hGap,source_original_ACTUAL_SOURCE_signed_DIRTY_visit_identity434
    u hi blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T hb]



/-- For fixed source slots J, the original-minus-CLEAN error differs
from its COMPLETE signed chronological visit sum only by the OLD tail
with arbitrary fixed logarithmic power. No source03 SMALL separation,
group-count lower bound, or SMALL harmonic identity is assumed here.
This is NOT a saving for the signed sum itself. -/
theorem eventually_source_original_ACTUAL_SOURCE_signed_CLEAN_coherent_remainder434
    (cfg : SourceComparisonFixed434) (J ell m Cq Cxi : ℕ) (hmJ : m ≤ J)
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hi : Function.Injective
        (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
        Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (blockA blockB : Finset β) (Q : ℕ) (hQ : (Q:ℝ) ≤ L^Cq)
      (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (rho : ℝ) (hrho : rho ≠ 0) (zeta theta : ℝ) (k : ℤ),
      ‖sourceOriginalActualSourceCleanGap434
          u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k
          (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2)) -
        (physicalSourceBaselineProduct
          (fun g : β => {p : ℕ // p ∈ u.Tb g})
          (fun _ p => p.val) cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) : ℂ) *
        (∑ j ∈ Finset.range (2*Nat.ceil (L^(0.52:ℝ))),
          sourceOriginalActualSourceSignedCoherentDIRTYVisit434
            u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k
            (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2)) j)‖ ≤
        L^(-B) := by
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [
    eventually_source_original_ACTUAL_SOURCE_OLD_projector_removal434
      cfg J ell m Cq Cxi hmJ B hB,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc
  ] with L hOld hVisits
  intro ι β _ _ _ _ x Y Hp u hi hHarmonic hmin blockA blockB Q hQ
    hA hB xi hhA hhB hxi hXi rho hrho zeta theta k
  let R := Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  have hb (g : β) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p := by
    have hhalf := (source_original_B26_physical_baseline_half434
      BP (fun _ p => p.val) cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*R) g p (hVisits p.val (hmin g p))).1
    linarith
  have hEq := source_original_ACTUAL_SOURCE_signed_CLEAN_gap_identity434
    u hi blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T hb
  have hOldHere := hOld u hi hHarmonic hmin
    blockA blockB Q hQ hA hB xi hhA hhB hxi hXi rho hrho zeta theta k
  have hNew :
      ‖sourceOriginalActualSourceCleanGap434
          u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T -
        (physicalSourceBaselineProduct BP (fun _ p => p.val)
          cfg.q0 (2*R) : ℂ) *
        (∑ j ∈ Finset.range (2*R),
          sourceOriginalActualSourceSignedCoherentDIRTYVisit434
            u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T j)‖ ≤
        L^(-B) := by
    rw [hEq, add_sub_cancel_right]
    exact hOldHere
  simpa only [R,T,BP] using hNew
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDirtyLaurentRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- One theta-independent Laurent polynomial for the literal source03
S plus ALL moving Ts/Tb and original RAW/comparison joint K.
No source03 separation, harmonic identity, or new energy assumption. -/
def sourceOriginalActualSourceDIRTYLaurentRoot434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) :
    AddMonoidAlgebra ℂ ℤ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  exact sourceOriginalActualPhysicalDIRTYLaurentRoot434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun _ => le_rfl)
    cfg.q0 rho Vs u.Vbig K zeta k R T

/-- Pointwise Laurent identity for the exact original moving physical
DIRTY root, including all jointly signed RAW/comparison cases and
chronological seen; positivity of BIG baseline is explicit. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_Laurent_exact434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T) =
    sourceOriginalActualSourcePhysicalDIRTYRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hmu (g : β) (p : BP g) :
      0 < physicalSourceMuTilde BP (fun _ p => p.val)
        cfg.q0 (2*R) u.Vbig g p := by
    have hp : (0:ℝ) < (p.val:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos p.val)
    have hv : 0 < u.Vbig g := cfg.hv.trans_le (u.hVbig g)
    have hbp := hb g p
    unfold physicalSourceMuTilde
    positivity
  have h := source_original_ACTUAL_physical_DIRTY_root_Laurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    hi (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K
    zeta theta k R T hVs hmu
  simpa only [sourceOriginalActualSourceDIRTYLaurentRoot434,
    sourceOriginalActualSourcePhysicalDIRTYRoot434, SP,BP,P,Vs,K] using h

/-- The original-minus-CLEAN physical root is EXACTLY original
OLD projector discrepancy plus the evaluation of the true signed
DIRTY Laurent polynomial, not a TV positive envelope. -/
theorem source_original_ACTUAL_SOURCE_CLEAN_gap_Laurent_identity434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    sourceOriginalActualSourceCleanGap434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T =
    sourceOriginalActualSourceOLDDiscrepancy434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T +
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T) := by
  have h1 := source_original_ACTUAL_SOURCE_signed_CLEAN_gap_identity434
    u hi blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T hb
  have h2 := source_original_ACTUAL_SOURCE_signed_DIRTY_visit_identity434
    u hi blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T hb
  have h3 := source_original_ACTUAL_SOURCE_DIRTY_Laurent_exact434
    u hi blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T hb
  calc
    _ = sourceOriginalActualSourceOLDDiscrepancy434
          u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T +
        (physicalSourceBaselineProduct
          (fun g : β => {p : ℕ // p ∈ u.Tb g})
          (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
        (∑ j ∈ Finset.range (2*R),
          sourceOriginalActualSourceSignedCoherentDIRTYVisit434
            u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T j) := h1
    _ = sourceOriginalActualSourceOLDDiscrepancy434
          u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T +
        sourceOriginalActualSourcePhysicalDIRTYRoot434
          u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T := by rw [h2]
    _ = _ := by rw [h3]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentCircleFourier -/

section

open MeasureTheory AddCircle
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

/-- The genuinely signed integer-displacement Laurent polynomial as
a continuous function on ONE physical frequency circle. Every
chronological history with a common total frequency is coalesced
inside its coefficient BEFORE taking Fourier norms. -/
def sourceOriginalActualLaurentCircle434
    (P : AddMonoidAlgebra ℂ ℤ) (t : AddCircle (1:ℝ)) : ℂ :=
  ∑ d ∈ P.coeff.support, P.coeff d * fourier (T := (1:ℝ)) d t

/-- Exact recovery of one signed TOTAL frequency coefficient.
This identity alone supplies no saving and does not justify replacing
a pointwise theta estimate with an averaged Fourier estimate. -/
theorem source_original_ACTUAL_Laurent_circle_fourier_coeff434
    (P : AddMonoidAlgebra ℂ ℤ) (d : ℤ) :
    fourierCoeff (T := (1:ℝ))
      (sourceOriginalActualLaurentCircle434 P) d = P.coeff d := by
  classical
  have hInt (n : ℤ) :
      Integrable (fun t : AddCircle (1:ℝ) =>
        P.coeff n * fourier (T := (1:ℝ)) n t)
          (AddCircle.haarAddCircle (T := (1:ℝ))) := by
    have hc : Continuous (fun t : AddCircle (1:ℝ) =>
        P.coeff n * fourier (T := (1:ℝ)) n t) :=
      continuous_const.mul (fourier (T := (1:ℝ)) n).continuous
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have hFourier (n : ℤ) :
      fourierCoeff (T := (1:ℝ))
        (fourier (T := (1:ℝ)) n) d =
        if d=n then 1 else 0 := by
    have h := congrFun (fourierCoeff_fourier
      (T := (1:ℝ)) n) d
    simpa [Pi.single_apply] using h
  calc
    _ = ∑ n ∈ P.coeff.support,
        fourierCoeff (T := (1:ℝ))
          (fun t : AddCircle (1:ℝ) =>
            P.coeff n * fourier (T := (1:ℝ)) n t) d := by
      have hs := fourierCoeff.sum
        (T := (1:ℝ)) P.coeff.support
        (fun n t => P.coeff n * fourier (T := (1:ℝ)) n t)
        (by intro n hn; exact hInt n)
      have ht := congrFun hs d
      change fourierCoeff (T := (1:ℝ))
        (fun t : AddCircle (1:ℝ) => ∑ n ∈ P.coeff.support,
          P.coeff n * fourier (T := (1:ℝ)) n t) d = _
      have hFun :
          (fun t : AddCircle (1:ℝ) => ∑ n ∈ P.coeff.support,
            P.coeff n * fourier (T := (1:ℝ)) n t) =
          (∑ n ∈ P.coeff.support,
            fun t : AddCircle (1:ℝ) =>
              P.coeff n * fourier (T := (1:ℝ)) n t) := by
        funext t
        simp only [Finset.sum_apply]
      rw [hFun]
      simpa only [Finset.sum_apply] using ht
    _ = ∑ n ∈ P.coeff.support, if n=d then P.coeff n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [fourierCoeff.const_mul,hFourier]
      by_cases h : n = d
      · subst n
        simp
      · have hd : d ≠ n := Ne.symm h
        simp [h, hd]
    _ = P.coeff d := by
      by_cases h : d ∈ P.coeff.support
      · simp [Finset.sum_ite_eq, h]
      · have hz : P.coeff d = 0 := by
          by_contra hn
          exact h (Finsupp.mem_support_iff.mpr hn)
        simp [Finset.sum_ite_eq, h, hz]

/-- Physical real theta evaluates the SAME finite Laurent polynomial
as the natural normalized circle Fourier series. -/
theorem source_original_ACTUAL_Laurent_circle_coe434
    (P : AddMonoidAlgebra ℂ ℤ) (theta : ℝ) :
    sourceOriginalActualLaurentCircle434 P
      (theta : AddCircle (1:ℝ)) =
    sourceOriginalActualThetaEval434 theta P := by
  classical
  have hterm (d : ℤ) :
      fourier (T := (1:ℝ)) d
        (theta : AddCircle (1:ℝ)) =
      sourceOriginalActualThetaFrequency434 theta 1 d := by
    rw [fourier_coe_apply]
    unfold sourceOriginalActualThetaFrequency434
    congr 1
    push_cast
    ring
  change (∑ d ∈ P.coeff.support,
    P.coeff d * fourier (T := (1:ℝ)) d (theta : AddCircle (1:ℝ))) = _
  simp_rw [hterm]
  unfold sourceOriginalActualThetaEval434
  rw [AddMonoidAlgebra.lift_apply]
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDirtyLaurentSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Exact original signed source CLEAN subtraction is, up to the
already-proved OLD projector L^-B tail, the evaluation at the SAME
theta of a single finite TRUE full-DIRTY Laurent polynomial.
Fixed source slots and B precede L→∞ and all moving prime families.
No smallness of the Laurent polynomial is inferred or assumed. -/
theorem eventually_source_original_ACTUAL_SOURCE_DIRTY_Laurent_remainder434
    (cfg : SourceComparisonFixed434) (J ell m Cq Cxi : ℕ) (hmJ : m ≤ J)
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hi : Function.Injective
        (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
        Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (blockA blockB : Finset β) (Q : ℕ) (hQ : (Q:ℝ) ≤ L^Cq)
      (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (rho : ℝ) (hrho : rho ≠ 0) (zeta theta : ℝ) (k : ℤ),
      ‖sourceOriginalActualSourceCleanGap434
          u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k
          (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2)) -
        sourceOriginalActualThetaEval434 theta
          (sourceOriginalActualSourceDIRTYLaurentRoot434
            u blockA blockB J ell m hmJ Q hA hB xi rho zeta k
            (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2)))‖ ≤ L^(-B) := by
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [
    eventually_source_original_ACTUAL_SOURCE_signed_CLEAN_coherent_remainder434
      cfg J ell m Cq Cxi hmJ B hB,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc
  ] with L hOld hVisits
  intro ι β _ _ _ _ x Y Hp u hi hHarmonic hmin
    blockA blockB Q hQ hA hB xi hhA hhB hxi hXi
    rho hrho zeta theta k
  let R := Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  have hb (g : β) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p := by
    have hhalf := (source_original_B26_physical_baseline_half434
      BP (fun _ p => p.val) cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*R) g p (hVisits p.val (hmin g p))).1
    linarith
  have hL := source_original_ACTUAL_SOURCE_DIRTY_Laurent_exact434
    u hi blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T hb
  have hV := source_original_ACTUAL_SOURCE_signed_DIRTY_visit_identity434
    u hi blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T hb
  have hRev :
      sourceOriginalActualThetaEval434 theta
        (sourceOriginalActualSourceDIRTYLaurentRoot434
          u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T) =
      (physicalSourceBaselineProduct BP (fun _ p => p.val)
        cfg.q0 (2*R) : ℂ) *
        ∑ j ∈ Finset.range (2*R),
          sourceOriginalActualSourceSignedCoherentDIRTYVisit434
            u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T j :=
    hL.trans hV
  have hSmall := hOld u hi hHarmonic hmin blockA blockB Q hQ
    hA hB xi hhA hhB hxi hXi rho hrho zeta theta k
  change ‖sourceOriginalActualSourceCleanGap434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T -
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T)‖ ≤ L^(-B)
  rw [hRev]
  simpa only [R,T,BP] using hSmall
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentCircleParseval -/

section

open MeasureTheory AddCircle
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

/-- Exact Haar-averaged signed energy of the original common-theta
Laurent amplitude. Same TOTAL signed frequency collisions stay
inside each coefficient, so this is not a positive TV estimate.
It does NOT bound a prescribed theta pointwise. -/
theorem source_original_ACTUAL_Laurent_circle_Parseval434
    (P : AddMonoidAlgebra ℂ ℤ) :
    (∑ d ∈ P.coeff.support, ‖P.coeff d‖^2) =
    ∫ t : AddCircle (1:ℝ),
      ‖sourceOriginalActualLaurentCircle434 P t‖^2
        ∂(AddCircle.haarAddCircle (T := (1:ℝ))) := by
  classical
  let f : C(AddCircle (1:ℝ),ℂ) :=
    ∑ d ∈ P.coeff.support, (P.coeff d) • fourier (T := (1:ℝ)) d
  have hf (t : AddCircle (1:ℝ)) :
      f t = sourceOriginalActualLaurentCircle434 P t := by
    change (∑ d ∈ P.coeff.support,
      P.coeff d • fourier (T := (1:ℝ)) d : C(AddCircle (1:ℝ),ℂ)) t =
        ∑ d ∈ P.coeff.support,
          P.coeff d * fourier (T := (1:ℝ)) d t
    rw [ContinuousMap.sum_apply]
    apply Finset.sum_congr rfl
    intro d hd
    rw [ContinuousMap.smul_apply]
    rfl
  have hcoeff (d : ℤ) :
      fourierCoeff (T := (1:ℝ)) f d = P.coeff d := by
    have he : (f : AddCircle (1:ℝ) → ℂ) =
        sourceOriginalActualLaurentCircle434 P := by
      funext t
      exact hf t
    rw [he]
    exact source_original_ACTUAL_Laurent_circle_fourier_coeff434 P d
  have hSquare := tsum_sq_fourierCoeff (T := (1:ℝ))
    (f.toLp 2 (AddCircle.haarAddCircle (T := (1:ℝ))) ℂ)
  simp_rw [fourierCoeff_toLp,hcoeff] at hSquare
  have hFinite :
      (∑' d : ℤ, ‖P.coeff d‖^2) =
      ∑ d ∈ P.coeff.support, ‖P.coeff d‖^2 := by
    apply tsum_eq_sum (s := P.coeff.support)
    intro d hd
    have hzero : P.coeff d = 0 := by
      by_contra hn
      exact hd (Finsupp.mem_support_iff.mpr hn)
    simp [hzero]
  rw [hFinite] at hSquare
  have hIntegral :
      (∫ t : AddCircle (1:ℝ), ‖f t‖^2
          ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) =
      ∫ t : AddCircle (1:ℝ),
        ‖(ContinuousMap.toAEEqFun (AddCircle.haarAddCircle (T := (1:ℝ))) f) t‖^2
          ∂(AddCircle.haarAddCircle (T := (1:ℝ))) := by
    apply integral_congr_ae
    filter_upwards
      [ContinuousMap.coeFn_toAEEqFun (AddCircle.haarAddCircle (T := (1:ℝ))) f]
      with t ht
    rw [←ht]
  simp only [ContinuousMap.coe_toLp] at hSquare
  rw [←hIntegral] at hSquare
  simpa only [hf] using hSquare
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDirtyCircle -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Source03 true first-DIRTY Fock root is the restriction to real
theta of ONE continuous circle Fourier polynomial with the SAME
signed Fock/seen histories and original joint RAW/comparison K. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_physical_circle434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    sourceOriginalActualLaurentCircle434
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T)
      (theta : AddCircle (1:ℝ)) =
    sourceOriginalActualSourcePhysicalDIRTYRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T := by
  rw [source_original_ACTUAL_Laurent_circle_coe434]
  exact source_original_ACTUAL_SOURCE_DIRTY_Laurent_exact434
    u hi blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T hb

/-- Unconditional finite harmonic-analysis identity on the ORIGINAL
source03 physical signed ROOT's common-theta Fourier polynomial.
A pointwise log saving is not inferred from this exact average. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_circle_energy434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    (∑ d ∈ P.coeff.support, ‖P.coeff d‖^2) =
      ∫ t : AddCircle (1:ℝ), ‖sourceOriginalActualLaurentCircle434 P t‖^2
        ∂(AddCircle.haarAddCircle (T := (1:ℝ))) := by
  dsimp only
  exact source_original_ACTUAL_Laurent_circle_Parseval434 _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYFrequencyLattice -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- For the real source03 S + EVERY moving Ts/Tb and original joint K,
the exact physical signed first-DIRTY Laurent root uses only
total signed displacements in kℤ. No source03 harmonic or
separation hypotheses and no fictitious probabilistic cancellation. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_k_lattice434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalLaurentKSupported434 k
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T) := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have h := source_original_ACTUAL_PHYSICAL_DIRTY_k_lattice434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K zeta k R T
  simpa only [sourceOriginalActualSourceDIRTYLaurentRoot434,
    SP, BP, P, Vs, K] using h

/-- Concrete arithmetic selection rule for each SOURCE physical
signed Fourier coefficient: it vanishes unless k divides the
integer total chronological return frequency. It is an exact
structural restriction, not a bound on surviving coefficients. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_off_k_lattice_zero434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k d : ℤ) (R T : ℕ)
    (hd : ¬k ∣ d) :
    (sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T).coeff d = 0 :=
  (source_original_ACTUAL_SOURCE_DIRTY_k_lattice434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T) d hd
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentFullCircleHilbert -/

section

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- ANY finite signed matrix-Laurent family on genuine shared
state carrier has a weighted finite-window Fourier energy
bounded by the same operators' FULL continuous circle-Haar L²
energy, without an artificial #frequency/#state multiplier.
The coefficient outside each Laurent polynomial's own support
is ACTUALLY zero. The density need not be normalized, and
the sqrt form safely includes nonnegative physical π. -/
theorem source_original_ACTUAL_Laurent_finite_window_Hilbert_circle434
    {H : Type} [Fintype H]
    (π : H → ℝ) (P : H → AddMonoidAlgebra ℂ ℤ)
    (F : Finset ℤ) :
    (∑ freq ∈ F, ∑ a : H,
      (Real.sqrt (π a)*‖(P a).coeff freq‖)^2) ≤
    ∑ a : H, (Real.sqrt (π a))^2 *
      (∫ theta : AddCircle (1:ℝ),
        ‖sourceOriginalActualLaurentCircle434 (P a) theta‖^2
          ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  let S : Finset ℤ := (P a).coeff.support
  let f : ℤ → ℝ := fun d =>
    (Real.sqrt (π a)*‖(P a).coeff d‖)^2
  have hs : (∑ d ∈ F, f d) ≤ ∑ d ∈ S, f d := by
    calc
      _ = ∑ d ∈ F ∩ S, f d := by
        apply (Finset.sum_subset Finset.inter_subset_left _).symm
        intro d hd hnot
        have hnS : d ∉ S := by
          intro hm
          exact hnot (Finset.mem_inter.mpr ⟨hd,hm⟩)
        have hz : (P a).coeff d = 0 := by
          by_contra hne
          exact hnS (Finsupp.mem_support_iff.mpr hne)
        simp [f,hz]
      _ ≤ ∑ d ∈ S, f d :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun d hd hnot => sq_nonneg _)
  have hP :
      (∑ d ∈ S, f d) =
      (Real.sqrt (π a))^2 *
        (∫ theta : AddCircle (1:ℝ),
          ‖sourceOriginalActualLaurentCircle434 (P a) theta‖^2
            ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) := by
    calc
      _ = (Real.sqrt (π a))^2 *
          (∑ d ∈ S, ‖(P a).coeff d‖^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        dsimp [f]
        ring
      _ = _ := by
        rw [source_original_ACTUAL_Laurent_circle_Parseval434]
  exact hs.trans_eq hP
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYArithmeticCoefficient -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Coherent SIGNED arithmetic TOTAL-frequency amplitude of the
literal original moving source03 S+Ts/Tb Fock×seen history, BEFORE
multiplication by its nonoscillatory actual BIG baseline.
The full raw/comparison joint K and both OLD gates are retained. -/
def sourceOriginalActualSourceDIRTYCoherentFreq434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (d : ℤ) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0 N u.Vbig
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m (fun g => Fintype.card (BP g))
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ))
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m (fun g => Fintype.card (BP g))
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ) x z)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let H := sourceOriginalActualSignedHistoryState434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g))
  let F : H → AddMonoidAlgebra ℂ ℤ := fun a =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell (fun g => Fintype.card (BP g))
        cfg.q0 rho u.Vbig mu N N
        (fun out _ => physicalVacuum SP (fun _ p => p.val)
          BP (fun _ p => p.val) J ell out) a)
  exact ∑ a : H,
    sourceOriginalActualSignedInitialWeight434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell (fun g => Fintype.card (BP g))
      (fun _ => le_rfl) Vs mu a *
    (sourceOriginalSignedLaurentDirtyChain434 C D N 0 F a).coeff d

/-- The original source03 Fourier coefficient is exactly the TRUE
BIG physical baseline times its coherent signed arithmetic
frequency amplitude, with no positive history or phase supremum.
Arbitrary moving groups, Q/xi, pattern signs and k are retained. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_coherent_coeff434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (d : ℤ) :
    (sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T).coeff d =
    (physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    sourceOriginalActualSourceDIRTYCoherentFreq434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T d := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have h := source_original_ACTUAL_PHYSICAL_DIRTY_Laurent_coeff434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K zeta k R T d
  simpa only [sourceOriginalActualSourceDIRTYLaurentRoot434,
    sourceOriginalActualSourceDIRTYCoherentFreq434,
    SP,BP,P,Vs,K] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYCoherentFrequencyEnergy -/

section

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Exact coherent frequency-energy factorization for the ORIGINAL
signed physical S+Ts/Tb first-DIRTY source root.
The TRUE BIG baseline is factored out of the energy without a
hypothetical gain or continuation bound. All original Fock×seen,
mixed RAW/comparison amplitudes and chronological cross terms remain
inside sourceOriginalActualSourceDIRTYCoherentFreq434.
No asymptotic logarithmic saving is asserted. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_coherent_frequency_energy434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    let Base : ℂ := physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R)
    (∑ d ∈ P.coeff.support, ‖P.coeff d‖^2) =
      ‖Base‖^2 *
        (∑ d ∈ P.coeff.support,
          ‖sourceOriginalActualSourceDIRTYCoherentFreq434
            u blockA blockB J ell m hmJ Q hA hB
            xi rho zeta k R T d‖^2) := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [source_original_ACTUAL_SOURCE_DIRTY_coherent_coeff434]
  rw [norm_mul]
  ring

/-- The original source complete circle-Haar DIRTY energy is EXACTLY
baseline² times the energy of coherent signed frequency amplitudes.
This is a finite Fourier identity, not a pointwise theta estimate. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_coherent_circle_energy434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    let Base : ℂ := physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R)
    (∫ t : AddCircle (1:ℝ),
      ‖sourceOriginalActualLaurentCircle434 P t‖^2
        ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) =
      ‖Base‖^2 *
        (∑ d ∈ P.coeff.support,
          ‖sourceOriginalActualSourceDIRTYCoherentFreq434
            u blockA blockB J ell m hmJ Q hA hB
            xi rho zeta k R T d‖^2) := by
  dsimp only
  rw [←source_original_ACTUAL_Laurent_circle_Parseval434]
  exact source_original_ACTUAL_SOURCE_DIRTY_coherent_frequency_energy434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPathState -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The TRUE source03 finite signed path state. This is exactly
the reachable original Fock output × cumulative numerical seen,
NOT an arbitrary abstract Markov state. SMALL=S+all Ts, BIG=all Tb. -/
def sourceOriginalActualSourceDIRTYPathState434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell : ℕ) : Type := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  exact sourceOriginalActualSignedHistoryState434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g))

/-- The source03 actual Fock×seen path carrier is finite for each
finite moving S/Ts/Tb family, with no Fintype on the unbounded full
physical Fock output or an invented prime universe. -/
noncomputable instance sourceOriginalActualSourceDIRTYPathStateFintype434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell : ℕ) :
    Fintype (sourceOriginalActualSourceDIRTYPathState434 u J ell) := by
  unfold sourceOriginalActualSourceDIRTYPathState434
  infer_instance
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPathAmplitude -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- True original source03 chronological path amplitude at TOTAL
integer frequency d, including RAW/comparison joint K,
SMALL distinguished S + Ts, every BIG Tb, the initial Fock/vacuum
weight and every first-DIRTY insertion position on the SAME path.
No arbitrary endpoint functions or independence of seen histories. -/
def sourceOriginalActualSourceDIRTYPathAmplitude434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d : ℤ) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns x z)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let H := sourceOriginalActualSignedHistoryState434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap
  let F : H → AddMonoidAlgebra ℂ ℤ := fun a =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell cap cfg.q0 rho u.Vbig mu N N
        (fun out _ => physicalVacuum SP (fun _ p => p.val)
          BP (fun _ p => p.val) J ell out) a)
  let w := sourceOriginalActualSignedInitialWeight434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap (fun _ => le_rfl) Vs mu
  exact sourceOriginalSignedLaurentDIRTYPathAmplitude434 C D F w N 0 p d
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYChronologicalRadius -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Actual source03 finite maximum physical E divisor over BOTH
orientations and every true source03 Fock×seen intermediate state.
The required positive-prime instances are justified by genuine
source03 S/Ts/Tb primality, not assumed in the public statement. -/
noncomputable def sourceOriginalActualSourceGEDualDivisorCap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (k : ℤ) : ℕ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  exact sourceOriginalActualGEDualDivisorCap434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell m
    (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434
      blockA blockB J m hmJ) k

/-- The ORIGINAL first-DIRTY source03 chronological Fock×seen path
is supported in a finite, exact ARITHMETIC window:
|total signed frequency| <= 2R * |k| * Dmax,
where Dmax is the supremum of ACTUAL oriented physical E divisors
over reachable intermediate Fock×seen source states. Nothing about
independent histories or magnitude of signed amplitudes is assumed.
All original K, OLD masks, alternating orientations and terminal
vacuum are preserved. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (freq : ℤ)
    (hn : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p freq ≠ 0) :
    freq.natAbs ≤ (2*R) * (k.natAbs *
      sourceOriginalActualSourceGEDualDivisorCap434
        u blockA blockB J ell m hmJ k) := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let H := sourceOriginalActualSourceDIRTYPathState434 u J ell
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns x z)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell cap cfg.q0 rho u.Vbig mu N N
        (fun out _ => physicalVacuum SP (fun _ p => p.val)
          BP (fun _ p => p.val) J ell out) b)
  let w := sourceOriginalActualSignedInitialWeight434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap (fun _ => le_rfl) Vs mu
  let B := k.natAbs *
    sourceOriginalActualGEDualDivisorCap434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns k
  have hC : ∀ i (a b : H) (e : ℤ),
      (C i a b).coeff e ≠ 0 → e.natAbs ≤ B := by
    intro i a b e he
    exact source_original_ACTUAL_GE_schedule_frequency_radius434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns
      (sourceOriginalCleanChoice434 SP (fun _ p => p.val)
        BP (fun _ p => p.val) J ell m cap patterns)
      cfg.q0 rho Vs u.Vbig mu K zeta k N T i a b e he
  have hD : ∀ i (a b : H) (e : ℤ),
      (D i a b).coeff e ≠ 0 → e.natAbs ≤ B := by
    intro i a b e he
    exact source_original_ACTUAL_GE_schedule_frequency_radius434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell m cap patterns x z)
      cfg.q0 rho Vs u.Vbig mu K zeta k N T i a b e he
  have hF : ∀ a : H, ∀ e : ℤ,
      (F a).coeff e ≠ 0 → e.natAbs ≤ 0 := by
    intro a e he
    by_cases he0 : e=0
    · simp [he0]
    · have hz : (F a).coeff e = 0 := by
        simp [F,AddMonoidAlgebra.coeff_single,he0]
      exact False.elim (he hz)
  have hpath :
      (sourceOriginalSignedLaurentDirtyPathWeight434
        C D F N 0 p.1 p.2).coeff freq ≠ 0 := by
    have heq :
      sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T p freq =
        w p.1 * (sourceOriginalSignedLaurentDirtyPathWeight434
          C D F N 0 p.1 p.2).coeff freq := by
      rfl
    rw [heq] at hn
    exact right_ne_zero_of_mul hn
  have hBound := source_original_Laurent_actual_DIRTY_path_radius434
    C D F B 0 hC hD hF N 0 p.1 p.2 freq hpath
  change freq.natAbs ≤ N*B
  simpa only [Nat.add_zero] using hBound
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPathCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- Original source03 first-DIRTY Fourier frequency d is exactly
the TRUE BIG baseline times the coherent sum of signed FIRST-DIRTY
amplitudes on ordered paths in its authentic Fock×seen carrier.
The transition and final state of consecutive visits are IDENTICAL,
and all RAW/comparison signs, OLD projectors, actual SMALL/BIG
marks and insertion positions are preserved. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_true_path_coefficient434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (d : ℤ) :
    (sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T).coeff d =
    (physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    ∑ path :
      (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell),
      sourceOriginalActualSourceDIRTYPathAmplitude434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T path d := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have h := source_original_ACTUAL_PHYSICAL_DIRTY_path_frequency434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K zeta k R T d
  convert h using 1
  all_goals try rfl

/-- Exact original physical source03 COMPLEX path-pair collision Gram
at a specified signed TOTAL integer frequency. Every off-diagonal
cross-history term survives, not a positive TV majorant. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_true_path_collision_gram434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) (d : ℤ) :
    (((‖(sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T).coeff d‖^2
        : ℝ)) : ℂ) =
    (((‖(physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ)‖^2 : ℝ)) : ℂ) *
    ∑ path :
      (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell),
      ∑ other :
        (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
        (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell),
        star (sourceOriginalActualSourceDIRTYPathAmplitude434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T path d) *
        sourceOriginalActualSourceDIRTYPathAmplitude434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T other d := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have h := source_original_ACTUAL_PHYSICAL_DIRTY_path_frequency_gram434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K zeta k R T d
  convert h using 1
  all_goals try rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPathKSupport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- EACH true chronological Fock×seen path's NONZERO complex
first-DIRTY amplitude, not just the final source-root sum, has
TOTAL integer Fourier frequency in kℤ. The actual G ghost,
original PEP projectors, four-sign RAW/comparison K, alternating
orientation, and same-path DIRTY insertion are all preserved. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d : ℤ)
    (hne : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p d ≠ 0) : k ∣ d := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {q : ℕ // q ∈ P g}
  let BP := fun g : β => {q : ℕ // q ∈ u.Tb g}
  letI (g : Option ι) (q : SP g) : NeZero q.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1
      g q.val q.property).ne_zero⟩
  letI (g : β) (q : BP g) : NeZero q.val :=
    ⟨(u.hTbPrime g q.val q.property).ne_zero⟩
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ q => q.val)
    cfg.q0 N u.Vbig
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ q => q.val) BP (fun _ q => q.val)
    J ell m cap patterns
    (sourceOriginalCleanChoice434
      SP (fun _ q => q.val) BP (fun _ q => q.val)
      J ell m cap patterns)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ q => q.val) BP (fun _ q => q.val)
    J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP (fun _ q => q.val) BP (fun _ q => q.val)
      J ell m cap patterns x z)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let H := sourceOriginalActualSignedHistoryState434
    SP (fun _ q => q.val) BP (fun _ q => q.val) J ell cap
  let F : H → AddMonoidAlgebra ℂ ℤ := fun a =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP (fun _ q => q.val) BP (fun _ q => q.val)
        J ell cap cfg.q0 rho u.Vbig mu N N
        (fun out _ => physicalVacuum
          SP (fun _ q => q.val) BP (fun _ q => q.val) J ell out) a)
  let w := sourceOriginalActualSignedInitialWeight434
    SP (fun _ q => q.val) BP (fun _ q => q.val)
    J ell cap (fun _ => le_rfl) Vs mu
  have hC : ∀ i a b, sourceOriginalLaurentKSupported434 k (C i a b) := by
    intro i a b
    exact source_original_ACTUAL_PHYSICAL_GE_schedule_k_lattice434
      SP (fun _ q => q.val) BP (fun _ q => q.val)
      J ell m cap patterns
      (sourceOriginalCleanChoice434
        SP (fun _ q => q.val) BP (fun _ q => q.val)
        J ell m cap patterns)
      cfg.q0 rho Vs u.Vbig mu K zeta k N T i a b
  have hD : ∀ i a b, sourceOriginalLaurentKSupported434 k (D i a b) := by
    intro i a b
    exact source_original_ACTUAL_PHYSICAL_GE_schedule_k_lattice434
      SP (fun _ q => q.val) BP (fun _ q => q.val)
      J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP (fun _ q => q.val) BP (fun _ q => q.val)
        J ell m cap patterns x z)
      cfg.q0 rho Vs u.Vbig mu K zeta k N T i a b
  have hF : ∀ a : H, sourceOriginalLaurentKSupported434 k (F a) := by
    intro a
    exact source_original_Laurent_K_single434 k 0 _ (dvd_zero k)
  have hPath := source_original_TRUE_Laurent_DIRTY_path_K434
    k C D F hC hD hF N 0 p.1 p.2
  by_contra hd
  have hz := hPath d hd
  apply hne
  change w p.1 *
    (sourceOriginalSignedLaurentDirtyPathWeight434
      C D F N 0 p.1 p.2).coeff d = 0
  rw [hz,mul_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPathPairEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Exact source03 global signed COLLISION energy as a complex
path-pair Gram sum, not a sum of independent positive histories.
All matching TOTAL signed frequencies d must be controlled together.
The physical BIG baseline is factored exactly, no log saving assumed.
This is the actual outstanding signed transference energy target. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_full_path_pair_energy434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    let Base : ℂ := physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R)
    ((∑ d ∈ P.coeff.support, ‖P.coeff d‖^2 : ℝ) : ℂ) =
      ((‖Base‖^2 : ℝ) : ℂ) *
        ∑ d ∈ P.coeff.support,
          ∑ path :
            (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
            (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell),
            ∑ other :
              (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
              (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell),
              star (sourceOriginalActualSourceDIRTYPathAmplitude434
                u blockA blockB J ell m hmJ Q hA hB
                xi rho zeta k R T path d) *
                sourceOriginalActualSourceDIRTYPathAmplitude434
                  u blockA blockB J ell m hmJ Q hA hB
                  xi rho zeta k R T other d := by
  dsimp only
  let P := sourceOriginalActualSourceDIRTYLaurentRoot434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
  let Base : ℂ := physicalSourceBaselineProduct
    (fun g : β => {p : ℕ // p ∈ u.Tb g})
    (fun _ p => p.val) cfg.q0 (2*R)
  calc
    ((∑ d ∈ P.coeff.support, ‖P.coeff d‖^2 : ℝ) : ℂ) =
      ∑ d ∈ P.coeff.support, ((‖P.coeff d‖^2 : ℝ) : ℂ) := by
        push_cast
        rfl
    _ = ∑ d ∈ P.coeff.support, ((‖Base‖^2 : ℝ) : ℂ) *
          (∑ path :
            (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
            (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell),
            ∑ other :
              (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
              (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell),
              star (sourceOriginalActualSourceDIRTYPathAmplitude434
                u blockA blockB J ell m hmJ Q hA hB
                xi rho zeta k R T path d) *
                sourceOriginalActualSourceDIRTYPathAmplitude434
                  u blockA blockB J ell m hmJ Q hA hB
                  xi rho zeta k R T other d) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact source_original_ACTUAL_SOURCE_DIRTY_true_path_collision_gram434
          u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T d
    _ = _ := by rw [Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLegalSmallTorusTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- On EVERY LITERALLY LEGAL original physical E branch, the
whole genuine SMALL Haar residue torus is translated by the
same signed source arithmetic displacement o*k*D.
This is an arithmetic constraint on legal labels, not an
averaged or postulated transition kernel. -/
theorem source_original_ACTUAL_legal_E_small_torus_transport434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hlegal : sourceOrientedPhysicalLegal
      SP sm BP bm J ell m cap patterns x o k z)
    (g : SG) :
    Green64SmallHaar.residues (sm g) (J+ell)
      ((sourceOrientedPhysicalOutput
        SP sm BP bm J ell m cap patterns x o k z).1 g) =
    Green64SmallHaar.translate (sm g)
      (sourceOrientedStep SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 o k)
      (Green64SmallHaar.residues (sm g) (J+ell) (x.1 g)) := by
  rcases hlegal with ⟨_,_,_,_,hs⟩
  exact (hs g).1

/-- Every original SMALL prime modulus individually sees the
exact arithmetic step, not a statistically independent phase.
In particular this makes precise that source Fourier displacement
and SMALL Haar residue transport are the SAME signed integer. -/
theorem source_original_ACTUAL_legal_E_prime_residue_transport434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hlegal : sourceOrientedPhysicalLegal
      SP sm BP bm J ell m cap patterns x o k z)
    (g : SG) (p : SP g) :
    Green64SmallHaar.residues (sm g) (J+ell)
      ((sourceOrientedPhysicalOutput
        SP sm BP bm J ell m cap patterns x o k z).1 g) p =
    Green64SmallHaar.residues (sm g) (J+ell) (x.1 g) p +
      ((o*k*(sourceOrientedPhysicalD
        SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 : ℤ))
        : ZMod (sm g p)) := by
  have h := congrArg (fun v => v p)
    (source_original_ACTUAL_legal_E_small_torus_transport434
      SP sm BP bm J ell m cap patterns x o k z hlegal g)
  simpa only [Green64SmallHaar.translate, sourceOrientedStep,
    Int.cast_mul, Int.cast_natCast] using h

/-- Actual SMALL residue translations compose ADDITIVELY.
Chronological transport is by the total signed displacement,
not by the product of the displacements or independent copies. -/
theorem source_original_ACTUAL_small_torus_translate_add434
    (g : SG) (a b : ℤ)
    (y : Green64SmallHaar.SmallTorus (sm g)) :
    Green64SmallHaar.translate (sm g) b
      (Green64SmallHaar.translate (sm g) a y) =
    Green64SmallHaar.translate (sm g) (a+b) y := by
  funext p
  simp only [Green64SmallHaar.translate, Int.cast_add]
  abel
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallTorusDeltaSupport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 14000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- A nonzero genuine finite-history basis delta forces equality of
BOTH the true physical Fock output and the cumulative numerical seen.
In particular a ghost or E cannot teleport to an unrelated SMALL
residue sector through the finite carrier restriction. -/
theorem source_original_ACTUAL_history_delta_nonzero_equal434
    (b : H)
    (out : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ)
    (hnonzero :
      sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
        (sourceOriginalSignedFiniteDelta434 b) out seen ≠ 0) :
    (out,seen) = b.val := by
  classical
  by_cases hc : (out,seen) ∈ sourceOriginalActualSignedHistoryCarrierFinset434
      SP sm BP bm J ell cap
  · let t : H := ⟨(out,seen),hc⟩
    have ht : t=b := by
      by_contra hn
      have hz :
          sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
            (sourceOriginalSignedFiniteDelta434 b) out seen = 0 := by
        simp [sourceOriginalActualSignedHistoryLift434,
          sourceOriginalSignedFiniteDelta434, hc, t, hn]
      exact hnonzero hz
    exact congrArg Subtype.val ht
  · have hz :
        sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
          (sourceOriginalSignedFiniteDelta434 b) out seen = 0 := by
      simp [sourceOriginalActualSignedHistoryLift434, hc]
    exact False.elim (hnonzero hz)

/-- The true physical Fock output can be read off from the same
nonzero finite-state delta; no SMALL label information is discarded. -/
theorem source_original_ACTUAL_history_delta_nonzero_output434
    (b : H)
    (out : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ)
    (hnonzero :
      sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
        (sourceOriginalSignedFiniteDelta434 b) out seen ≠ 0) :
    out = b.val.1 :=
  congrArg Prod.fst
    (source_original_ACTUAL_history_delta_nonzero_equal434
      SP sm BP bm J ell cap b out seen hnonzero)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGhostSmallSector -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 19000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The LITERAL signed finite Fock×seen G_i ghost matrix cannot
change ANY SMALL Haar state. A nonzero G entry may update BIG Fock
and cumulative numerical seen, but the entire SMALL state is
transported unchanged. No positivity or spectral hypothesis. -/
theorem source_original_ACTUAL_G_small_state_offdiag_zero434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (a b : H) (hsmall : a.val.1.1 ≠ b.val.1.1) :
    sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap
      q rho N i V mu a b = 0 := by
  classical
  unfold sourceOriginalActualSignedGhostMatrix434
    sourceOriginalSignedFiniteMatrix434
    sourceOriginalActualSignedFiniteG434
    sourceOriginalPhysicalGhostUnseenPrimeRow434
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hgate : ∀ g, ∀ p ∈ (d g).2, bm g p ∉ a.val.2
  · have hdelta :
        sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
          (sourceOriginalSignedFiniteDelta434 b)
          (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm
            (J+ell) a.val.1
            (sourceOriginalPhysicalGhostPrimeBirthLift434
              SP sm BP bm (J+ell) a.val.1 d))
          (a.val.2 ∪ sourceOriginalPhysicalGhostPrimeBirthSet434
            SP sm BP bm (J+ell) a.val.1 d) = 0 := by
      by_contra hne
      have heq := source_original_ACTUAL_history_delta_nonzero_output434
        SP sm BP bm J ell cap b
        (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm
          (J+ell) a.val.1
          (sourceOriginalPhysicalGhostPrimeBirthLift434
            SP sm BP bm (J+ell) a.val.1 d))
        (a.val.2 ∪ sourceOriginalPhysicalGhostPrimeBirthSet434
          SP sm BP bm (J+ell) a.val.1 d) hne
      apply hsmall
      simpa only [sourceOriginalPhysicalGhostAtomOutput434] using
        (congrArg Prod.fst heq)
    simp only [if_pos hgate, hdelta, mul_zero]
  · simp only [if_neg hgate]
end Green64Analytic.CorrelationSquare

end

end

