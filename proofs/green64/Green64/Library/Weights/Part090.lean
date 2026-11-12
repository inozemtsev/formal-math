module

public import Green64.Library.Weights.Part071
public import Green64.Library.Correlation.MemoryPromotionTargetMass
public import Green64.Library.Correlation.Part031
public import Green64.Library.Correlation.Part044
public import Green64.Library.Correlation.Part046
public import Green64.Library.Weights.Part087
public import Green64.Library.Correlation.PhysicalGhostWitnessCollapse
public import Green64.Library.Correlation.Part045
public import Green64.Library.Correlation.Part008
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Weights.Part054
public import Green64.Library.Weights.Part045
public import Green64.Library.Weights.Part056
public import Green64.Library.Weights.Part057
public import Green64.Library.Weights.Part018

@[expose] public section

/-!
# Weights / Part090

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredForestOLDEnvelope -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal positive source tail at the MOVING exponent E*N(L).
Apply the existing budget at fixed CE+E and B=0, then cancel L^(E*N).
All original groups, canonical K, boundary masses and finite root are retained. -/
theorem eventually_source_original_forest_SOURCE_TAIL_MOVING434
    (cfg : SourceComparisonFixed434) (J ell m Cq Cxi : ℕ) (hmJ : m ≤ J)
    (E : ℝ) (hE : 0 ≤ E) :
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
        xi zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2/4)) ≤ L^(-E*((2*Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ)) := by
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
      Cb cfg.C0 (CE+E) (cfg.C0+1) cfg.vmin 0 hCb cfg.hC0 (add_nonneg hCE hE) hCS cfg.hv (le_refl 0) (ell+m)]
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
  have hBudgetN : ((2:ℝ)^H)⁻¹*E0*G0*
      F^((ell+m)*Fintype.card β*N)*L^((CE+E)*(N:ℝ)) ≤ 1 := by
    simpa only [H,E0,G0,F,N,Cb,neg_zero,Real.rpow_zero] using
      hBudget (Fintype.card β) u.hBigGroups
  have hCancel : L^(CE*(N:ℝ)) = L^((CE+E)*(N:ℝ))*L^(-E*(N:ℝ)) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hFinal : ((2:ℝ)^H)⁻¹*E0*G0*
      F^((ell+m)*Fintype.card β*N)*L^(CE*(N:ℝ)) ≤ L^(-E*(N:ℝ)) := by
    calc
      _ = (((2:ℝ)^H)⁻¹*E0*G0*F^((ell+m)*Fintype.card β*N)*
            L^((CE+E)*(N:ℝ)))*L^(-E*(N:ℝ)) := by rw [hCancel];ring
      _ ≤ 1*L^(-E*(N:ℝ)) := mul_le_mul_of_nonneg_right hBudgetN
          (Real.rpow_nonneg hLp.le _)
      _ = _ := one_mul _
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
    _ ≤ L^(-E*((2*Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ)) := by
      simpa only [H,E0,G0,F,N,Cb] using hFinal
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestOLDRemoval -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The TRUE memorySourceRoot minus the original symmetric PEP root
has L^(-E*N(L)) saving, for every fixed canonical J/ell/m/precision.
The projected root itself is not assumed small and is not bounded here. -/
theorem eventually_source_original_forest_SOURCE_OLD_MOVING434
    (cfg : SourceComparisonFixed434) (J ell m Cq Cxi : ℕ) (hmJ : m ≤ J)
    (E : ℝ) (hE : 0 ≤ E) :
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
        xi rho zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))‖ ≤ L^(-E*((2*Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ)) := by
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [
    eventually_source_original_forest_SOURCE_TAIL_MOVING434 cfg J ell m Cq Cxi hmJ E hE,
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
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedProduct -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The finite product law before fresh target integration. Copied coordinates
have their UNIQUE value, selected fresh coordinates have a numerical pin. -/
def sourceOriginalForestPinnedTargetLaw434
    {I P : Type} [Fintype I] [DecidableEq I] [DecidableEq P]
    (S Q : Finset I) (a : I → P) (num : P → ℕ) (pin : I → ℕ)
    (mu : P → ℝ) (t : I → P) : ℝ :=
  ∏ i : I, if i ∈ S then (if t i = a i then 1 else 0)
    else if i ∈ Q then (if num (t i) = pin i then mu (t i) else 0)
    else mu (t i)

/-- Exact product integration yields one full atom factor per distinct
selected fresh coordinate, including repeated prescribed numerical values. -/
theorem source_original_forest_PINNED_PRODUCT434
    {I P : Type} [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P]
    (S Q : Finset I) (hQS : Disjoint Q S)
    (a : I → P) (num : P → ℕ) (pin : I → ℕ)
    (mu : P → ℝ) (hmu : ∀ p, 0 ≤ mu p) (R delta : ℝ)
    (hR : 1 ≤ R) (hd : 0 ≤ delta) (hMass : ∑ p : P, mu p ≤ R)
    (hAtom : ∀ b : ℕ, (∑ p : P, if num p = b then mu p else 0) ≤ delta*R) :
    (∑ t : I → P, sourceOriginalForestPinnedTargetLaw434 S Q a num pin mu t) ≤
      delta^Q.card * R^((Finset.univ \ S).card) := by
  let f := fun (i : I) (p : P) => if i ∈ S then (if p = a i then (1:ℝ) else 0)
    else if i ∈ Q then (if num p = pin i then mu p else 0) else mu p
  have hnon (i : I) : 0 ≤ ∑ p : P, f i p := by
    apply Finset.sum_nonneg
    intro p hp
    dsimp only [f]
    split_ifs <;> first | positivity | exact hmu p
  have heach (i : I) : (∑ p : P, f i p) ≤
      (if i ∈ Q then delta else 1)*(if i ∈ S then 1 else R) := by
    by_cases hs : i ∈ S
    · have hq : i ∉ Q := fun h => (Finset.disjoint_left.mp hQS h hs)
      simp [f,hs,hq]
    · by_cases hq : i ∈ Q
      · simpa only [f,if_neg hs,if_pos hq] using hAtom (pin i)
      · simpa only [f,if_neg hs,if_neg hq,one_mul] using hMass
  have he : (∑ t : I → P, sourceOriginalForestPinnedTargetLaw434 S Q a num pin mu t) =
      ∏ i : I, ∑ p : P, f i p := by
    simpa only [sourceOriginalForestPinnedTargetLaw434,f] using
      (Fintype.prod_sum f).symm
  rw [he]
  calc
    _ ≤ ∏ i : I, (if i ∈ Q then delta else 1)*(if i ∈ S then 1 else R) :=
      Finset.prod_le_prod₀ (fun i _ => hnon i) (fun i _ => heach i)
    _ = (∏ i : I, if i ∈ Q then delta else 1)*
        (∏ i : I, if i ∈ S then 1 else R) := Finset.prod_mul_distrib
    _ = _ := by
      simp [Finset.prod_ite,Finset.prod_const,Finset.filter_notMem_eq_sdiff]

/-- The pointwise pinned law keeps the exact target product on legal
shared/promoted copies and on the prescribed numerical pins. -/
theorem source_original_forest_PINNED_PRODUCT_VALUE434
    {I P : Type} [Fintype I] [DecidableEq I] [DecidableEq P]
    (S Q : Finset I) (a t : I → P) (num : P → ℕ) (pin : I → ℕ) (mu : P → ℝ)
    (hCopy : ∀ i ∈ S, t i = a i) (hPin : ∀ i ∈ Q, num (t i) = pin i) :
    sourceOriginalForestPinnedTargetLaw434 S Q a num pin mu t =
      ∏ i ∈ Finset.univ \ S, mu (t i) := by
  have he : sourceOriginalForestPinnedTargetLaw434 S Q a num pin mu t =
      ∏ i : I, if i ∈ S then (1:ℝ) else mu (t i) := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hs : i ∈ S
    · simp [hs,hCopy i hs]
    · by_cases hq : i ∈ Q <;> simp [hs,hq,hPin i]
  rw [he,Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul,Finset.filter_notMem_eq_sdiff]

/-- Injective numerical labels turn the actual pointwise atom estimate
into a bound for every numerical singleton, including out-of-group parents. -/
theorem source_original_forest_NUMERIC_ATOM434
    {P : Type} [Fintype P] [DecidableEq P]
    (num : P → ℕ) (hi : Function.Injective num) (mu : P → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (hm : ∀ p, mu p ≤ A) (b : ℕ) :
    (∑ p : P, if num p=b then mu p else 0) ≤ A := by
  by_cases hx : ∃ p : P, num p=b
  · obtain ⟨p,hp⟩ := hx
    have he : (∑ v : P, if num v=b then mu v else 0)=mu p := by
      rw [Finset.sum_eq_single p]
      · simp [hp]
      · intro v hv hne
        exact if_neg (fun hvb => hne (hi (hvb.trans hp.symm)))
      · simp
    rw [he]
    exact hm p
  · have he : (∑ p : P, if num p=b then mu p else 0)=0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact if_neg (fun h => hx ⟨p,h⟩)
    rw [he]
    exact hA
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedPure -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Pure product pinning, with no arbitrary inhabitant of the alphabet.
The zero-mass and empty-alphabet cases obey the same finite formula. -/
theorem source_original_forest_PURE_PINNED_PRODUCT434
    {I U : Type} [Fintype I] [DecidableEq I] [Fintype U]
    (Q : Finset I) (num : U → ℕ) (pin : I → ℕ) (mu : U → ℝ)
    (hmu : ∀ u,0 ≤ mu u) (delta : ℝ) (hd : 0 ≤ delta)
    (hAtom : ∀ b : ℕ,(∑ u : U,if num u=b then mu u else 0) ≤ delta*(∑ u : U,mu u)) :
    (∑ t : I → U,if ∀ i ∈ Q,num (t i)=pin i then ∏ i : I,mu (t i) else 0) ≤
      delta^Q.card * (∑ u : U,mu u)^Fintype.card I := by
  classical
  let f := fun (i : I) (u : U) => if i ∈ Q then (if num u=pin i then mu u else 0) else mu u
  have hf (i : I) (u : U) : 0 ≤ f i u := by
    dsimp only [f]
    split_ifs <;> first | exact hmu u | exact le_refl 0
  have heach (t : I → U) :
      (if ∀ i ∈ Q,num (t i)=pin i then ∏ i : I,mu (t i) else 0) ≤ ∏ i : I,f i (t i) := by
    split_ifs with ht
    · apply le_of_eq
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hq : i ∈ Q <;> simp [f,hq,ht i]
    · exact Finset.prod_nonneg (fun i _ => hf i (t i))
  have hsum (i : I) : (∑ u : U,f i u) ≤
      (if i ∈ Q then delta else 1)*(∑ u : U,mu u) := by
    by_cases hq : i ∈ Q
    · simpa only [f,if_pos hq] using hAtom (pin i)
    · simp [f,hq]
  calc
    _ ≤ ∑ t : I → U,∏ i : I,f i (t i) := Finset.sum_le_sum (fun t _ => heach t)
    _ = ∏ i : I,∑ u : U,f i u := (Fintype.prod_sum f).symm
    _ ≤ ∏ i : I,(if i ∈ Q then delta else 1)*(∑ u : U,mu u) :=
      Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun u _ => hf i u)) (fun i _ => hsum i)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [Finset.prod_ite,Finset.prod_const]

/-- Numerical potential addresses below a chosen birth length reindex to
actual fresh coordinates without changing the selected-child count. -/
theorem source_original_forest_RANGE_PINNED_PRODUCT434
    {U : Type} [Fintype U]
    (b : ℕ) (Q : Finset ℕ) (hQ : Q ⊆ Finset.range b)
    (num : U → ℕ) (pin : ℕ → ℕ) (mu : U → ℝ) (hmu : ∀ u,0 ≤ mu u)
    (delta : ℝ) (hd : 0 ≤ delta)
    (hAtom : ∀ v : ℕ,(∑ u : U,if num u=v then mu u else 0) ≤ delta*(∑ u : U,mu u)) :
    (∑ t : Fin b → U,if ∀ i : Fin b,i.val ∈ Q → num (t i)=pin i.val
      then ∏ i : Fin b,mu (t i) else 0) ≤ delta^Q.card*(∑ u : U,mu u)^b := by
  classical
  let Qb := (Finset.univ : Finset (Fin b)).filter (fun i => i.val ∈ Q)
  have hcard : Qb.card=Q.card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj he
      exact Fin.ext he
    · intro i hi
      refine ⟨⟨i,Finset.mem_range.mp (hQ hi)⟩,?_,rfl⟩
      simp [Qb,hi]
  have h := source_original_forest_PURE_PINNED_PRODUCT434 Qb num (fun i => pin i.val)
    mu hmu delta hd hAtom
  rw [hcard] at h
  simpa only [Qb,Finset.mem_filter,Finset.mem_univ,true_and,Fintype.card_fin] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedGhost -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 7000000

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Pinning fresh numerical coordinates before integration in the ACTUAL
sourceGhostTerm. No deletion indices, repetitions, or birth factorials are lost.
Unperformed selected potential addresses give zero, without conditioning. -/
theorem source_original_forest_GHOST_PINNED_WEIGHTED434
    (old : List U) (zero : U → Prop) [DecidablePred zero]
    (B : ℕ) (alpha chi gamma : ℂ) (nu : U → ℂ)
    (num : U → ℕ) (Q : Finset ℕ) (pin : ℕ → ℕ)
    (w delta : ℝ) (hw : 0<w) (hd : 0 ≤ delta)
    (hcontrol : ‖alpha‖/w+‖chi‖ ≤ 1)
    (hAtom : ∀ v : ℕ,(∑ u : U,if num u=v then ‖nu u‖ else 0) ≤
      delta*(∑ u : U,‖nu u‖)) :
    (∑ c : GhostWitnessChoice old zero B,
      if Q ⊆ Finset.range c.2.1.val ∧
        (∀ i : Fin c.2.1.val,i.val ∈ Q → num (c.2.2 i)=pin i.val) then
        ‖sourceGhostTerm old zero c.1.1 c.2.2 alpha chi gamma nu‖ *
          w^(afterGhost old c.1.1 c.2.2).length else 0) ≤
      delta^Q.card * Real.exp (‖gamma‖*w*(∑ u : U,‖nu u‖))*w^old.length := by
  classical
  let Z := zeroOld old zero
  let gate := fun (b : ℕ) (fresh : Fin b → U) => Q ⊆ Finset.range b ∧
    (∀ i : Fin b,i.val ∈ Q → num (fresh i)=pin i.val)
  have hFresh (A : {A : Finset (Fin old.length) // A ∈ Z.powerset}) (b : Fin (B+1)) :
      (∑ fresh : Fin b.val → U,if gate b.val fresh then
        ‖sourceGhostTerm old zero A.val fresh alpha chi gamma nu‖ *
          w^(afterGhost old A.val fresh).length else 0) ≤
      delta^Q.card * (∑ fresh : Fin b.val → U,
        ‖sourceGhostTerm old zero A.val fresh alpha chi gamma nu‖ *
          w^(afterGhost old A.val fresh).length) := by
    let C := ‖alpha‖^A.val.card * ‖chi‖^(Z.card-A.val.card) *
      (‖gamma‖^b.val/(b.val.factorial:ℝ)) * w^(old.length-A.val.card+b.val)
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have ht (fresh : Fin b.val → U) :
        ‖sourceGhostTerm old zero A.val fresh alpha chi gamma nu‖ *
          w^(afterGhost old A.val fresh).length = C*∏ j : Fin b.val,‖nu (fresh j)‖ := by
      rw [source_original_evolution_ghost_length434]
      simp only [sourceGhostTerm,norm_mul,norm_pow,norm_div,norm_one,norm_prod,
        Complex.norm_natCast,C,Z]
      ring
    by_cases hQ : Q ⊆ Finset.range b.val
    · have hp := source_original_forest_RANGE_PINNED_PRODUCT434 b.val Q hQ num pin
        (fun u => ‖nu u‖) (fun u => norm_nonneg _) delta hd hAtom
      calc
        _ = C * (∑ fresh : Fin b.val → U,
            if ∀ i : Fin b.val,i.val ∈ Q → num (fresh i)=pin i.val
            then ∏ j : Fin b.val,‖nu (fresh j)‖ else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro fresh hf
          by_cases hpin : ∀ i : Fin b.val,i.val ∈ Q → num (fresh i)=pin i.val
          · rw [if_pos (show gate b.val fresh from ⟨hQ,hpin⟩),if_pos hpin]
            exact ht fresh
          · rw [if_neg (show ¬gate b.val fresh from fun h => hpin h.2),if_neg hpin,mul_zero]
        _ ≤ C*(delta^Q.card*(∑ u : U,‖nu u‖)^b.val) := mul_le_mul_of_nonneg_left hp hC
        _ = _ := by
          simp_rw [ht]
          rw [←Finset.mul_sum,←Fintype.prod_sum (fun _ : Fin b.val => fun u : U => ‖nu u‖)]
          simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
          ring
    · have hz (fresh : Fin b.val → U) : ¬gate b.val fresh := fun h => hQ h.1
      simp only [if_neg (hz _),Finset.sum_const_zero]
      exact mul_nonneg (pow_nonneg hd _) (Finset.sum_nonneg (fun fresh _ =>
        mul_nonneg (norm_nonneg _) (pow_nonneg hw.le _)))
  have hrow := source_original_evolution_GHOST_weighted_row434 old zero B alpha chi gamma nu w hw hcontrol
  calc
    _ ≤ ∑ A : {A : Finset (Fin old.length) // A ∈ Z.powerset},
        ∑ b : Fin (B+1),delta^Q.card * (∑ fresh : Fin b.val → U,
          ‖sourceGhostTerm old zero A.val fresh alpha chi gamma nu‖ *
            w^(afterGhost old A.val fresh).length) := by
      simp only [GhostWitnessChoice,Fintype.sum_sigma]
      exact Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun b _ => hFresh A b))
    _ = delta^Q.card * (∑ c : GhostWitnessChoice old zero B,
        ‖sourceGhostTerm old zero c.1.1 c.2.2 alpha chi gamma nu‖ *
          w^(afterGhost old c.1.1 c.2.2).length) := by
      simp only [GhostWitnessChoice,Fintype.sum_sigma,Finset.mul_sum,Z]
    _ ≤ delta^Q.card * (Real.exp (‖gamma‖*w*(∑ u : U,‖nu u‖))*w^old.length) :=
      mul_le_mul_of_nonneg_left hrow (pow_nonneg hd _)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedTarget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- Literal fixed-choice BIG row with selected POTENTIAL target slots pinned
to previous numerical values. Selected slots must actually be fresh births.
The original shared/promoted equalities, target tau and all legality remain. -/
theorem source_original_forest_BIG_PINNED_TARGET434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R delta : ℝ)
    (hV : 0<V) (hr : 0 ≤ rho) (hR : 1 ≤ R) (hdelta : 0 ≤ delta)
    (hMass : ∑ p : P,mu p ≤ R)
    (hAtom : ∀ b : ℕ,(∑ p : P,if modulus p=b then mu p else 0) ≤ delta*R)
    (x : BigState modulus M B) (shared Q : Finset (Fin M)) (pin : Fin M → ℕ)
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ t : Fin M → P,if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
        Q ⊆ orientedFresh M shared c.2.1 ∧
        (∀ j ∈ Q,modulus (t (tau j))=pin j) then
      ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
      else 0) ≤
      delta^Q.card *
        ((rho^(Green64PhysicalEdge.oldZeroCount x.2+
          outputZeroCount modulus M B x sigma step c) / V^c.2.1.card) * R^d) := by
  classical
  let S := shared ∪ c.2.1
  let S' := S.map tau.toEmbedding
  let Q' := Q.map tau.toEmbedding
  let a := fun j : Fin M => if hj : j ∈ c.2.1 then
    (x.2.2 (c.2.2 ⟨j,hj⟩)).1 else x.1 (sigma j)
  let C := rho^(Green64PhysicalEdge.oldZeroCount x.2+
    outputZeroCount modulus M B x sigma step c) / V^c.2.1.card
  let law := sourceOriginalForestPinnedTargetLaw434 S' Q'
    (fun i => a (tau.symm i)) modulus (fun i => pin (tau.symm i)) mu
  have hC : 0 ≤ C := div_nonneg (pow_nonneg hr _) (pow_nonneg hV.le _)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hFresh : orientedFresh M shared c.2.1=Finset.univ \ S := by
    ext i
    simp [orientedFresh,orientedUnshared,S]
  by_cases hQ : Q ⊆ orientedFresh M shared c.2.1
  · have hMemS (i : Fin M) : i ∈ S' ↔ tau.symm i ∈ S := Finset.mem_map_equiv
    have hMemQ (i : Fin M) : i ∈ Q' ↔ tau.symm i ∈ Q := Finset.mem_map_equiv
    have hDisj : Disjoint Q' S' := by
      apply Finset.disjoint_left.mpr
      intro i hi hs
      have h := hQ ((hMemQ i).mp hi)
      rw [hFresh] at h
      exact (Finset.mem_sdiff.mp h).2 ((hMemS i).mp hs)
    have hLaw (t : Fin M → P) : 0 ≤ law t := by
      apply Finset.prod_nonneg
      intro i hi
      dsimp only [sourceOriginalForestPinnedTargetLaw434]
      split_ifs <;> first | positivity | exact hmu _
    have hAbs (p : P) : |mu p|=mu p := abs_of_nonneg (hmu p)
    have hNorm (t : Fin M → P) :
        ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖ =
        C*∏ j ∈ orientedFresh M shared c.2.1,mu (t (tau j)) := by
      simp only [orientedBigBranchCoefficient,norm_mul,norm_pow,norm_div,norm_one,norm_prod,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_pos hV,hAbs,C]
      ring
    have hMap : (orientedFresh M shared c.2.1).map tau.toEmbedding=Finset.univ \ S' := by
      ext i
      simp only [Finset.mem_map_equiv,Finset.mem_sdiff,Finset.mem_univ,true_and,hMemS]
      rw [hFresh]
      simp
    have hEach (t : Fin M → P) :
        (if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
          Q ⊆ orientedFresh M shared c.2.1 ∧
          (∀ j ∈ Q,modulus (t (tau j))=pin j) then
          ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
          else 0) ≤ C*law t := by
      split_ifs with ht
      · have hCopy (i : Fin M) (hi : i ∈ S') : t i=a (tau.symm i) := by
          have hj := (hMemS i).mp hi
          dsimp only [a]
          split_ifs with hja
          · simpa using ht.1.promoted_matches ⟨tau.symm i,hja⟩
          · have hjs : tau.symm i ∈ shared := (Finset.mem_union.mp hj).resolve_right hja
            simpa using (ht.1.shared_copy (tau.symm i) hjs).symm
        have hPin (i : Fin M) (hi : i ∈ Q') : modulus (t i)=pin (tau.symm i) := by
          simpa using ht.2.2 (tau.symm i) ((hMemQ i).mp hi)
        have hl : law t=∏ j ∈ orientedFresh M shared c.2.1,mu (t (tau j)) := by
          dsimp only [law]
          rw [source_original_forest_PINNED_PRODUCT_VALUE434 S' Q'
            (fun i => a (tau.symm i)) t modulus (fun i => pin (tau.symm i)) mu hCopy hPin]
          rw [←hMap,Finset.prod_map]
          rfl
        rw [hNorm,hl]
      · exact mul_nonneg hC (hLaw t)
    have hSize : (Finset.univ \ S').card ≤ d := by
      have hh : (Finset.univ \ S).card ≤ (orientedUnshared M shared).card :=
        Finset.card_le_card (by
          intro i hi
          simp only [S,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union,not_or] at hi
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi.1⟩)
      have he : (Finset.univ \ S').card=(Finset.univ \ S).card := by
        simp [Finset.card_sdiff,S']
      rw [he]
      exact hh.trans hd
    have hTotal : (∑ t : Fin M → P,law t) ≤ delta^Q.card*R^d := by
      have hp := source_original_forest_PINNED_PRODUCT434 S' Q' hDisj
        (fun i => a (tau.symm i)) modulus (fun i => pin (tau.symm i)) mu hmu R delta
        hR hdelta hMass hAtom
      have hpow : R^((Finset.univ \ S').card) ≤ R^d := pow_right_mono₀ hR hSize
      have hcard : Q'.card=Q.card := Finset.card_map _
      rw [hcard] at hp
      exact hp.trans (mul_le_mul_of_nonneg_left hpow (pow_nonneg hdelta _))
    calc
      _ ≤ ∑ t : Fin M → P,C*law t := Finset.sum_le_sum (fun t _ => hEach t)
      _ = C*∑ t : Fin M → P,law t := (Finset.mul_sum _ _ _).symm
      _ ≤ C*(delta^Q.card*R^d) := mul_le_mul_of_nonneg_left hTotal hC
      _ = _ := by ring
  · have hzero (t : Fin M → P) :
        ¬ (OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
          Q ⊆ orientedFresh M shared c.2.1 ∧
          (∀ j ∈ Q,modulus (t (tau j))=pin j)) := fun h => hQ h.2.1
    simp only [if_neg (hzero _),Finset.sum_const_zero]
    exact mul_nonneg (pow_nonneg hdelta _) (mul_nonneg hC (pow_nonneg hR0 _))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedBig -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- The actual target/injection row with a fixed set of potential birth pins.
Repeated OLD atoms remain indexed; they are never deduplicated. -/
theorem source_original_forest_BIG_PINNED_RETRIEVAL434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R delta : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1) (hR : 1 ≤ R) (hdelta : 0 ≤ delta)
    (hMass : ∑ p : P,mu p ≤ R)
    (hAtom : ∀ b : ℕ,(∑ p : P,if modulus p=b then mu p else 0) ≤ delta*R)
    (x : BigState modulus M B) (shared Q : Finset (Fin M)) (pin : Fin M → ℕ)
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (S A : Finset (Fin M)) (hA : A ⊆ orientedUnshared M shared)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ f : ↥A ↪ Fin x.2.1.val,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩) ∧
        Q ⊆ orientedFresh M shared A ∧ (∀ j ∈ Q,modulus (t (tau j))=pin j)
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step (S,⟨A,f⟩)‖
      else 0) ≤
      delta^Q.card * (memoryPromotionDampingConstant rho d * ((V^A.card)⁻¹*R^d)) := by
  classical
  let good := (Finset.univ : Finset (↥A ↪ Fin x.2.1.val)).filter
    (fun f => ∀ a,f a ∈ memoryTranslatedOldZero modulus M B x step)
  let row := fun f : ↥A ↪ Fin x.2.1.val => ∑ t : Fin M → P,
    if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩) ∧
      Q ⊆ orientedFresh M shared A ∧ (∀ j ∈ Q,modulus (t (tau j))=pin j)
    then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step (S,⟨A,f⟩)‖
    else 0
  let damp := fun f : ↥A ↪ Fin x.2.1.val =>
    rho^(Green64PhysicalEdge.oldZeroCount x.2+
      outputZeroCount modulus M B x sigma step (S,⟨A,f⟩))
  let C := delta^Q.card * ((V^A.card)⁻¹*R^d)
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg hdelta _)
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg hV.le _)) (pow_nonneg (zero_le_one.trans hR) _))
  have hcut : (∑ f,row f)=∑ f ∈ good,row f := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro f hf hbad
    have hn : ¬ ∀ a,f a ∈ memoryTranslatedOldZero modulus M B x step := by
      simpa only [good,Finset.mem_filter,Finset.mem_univ,true_and] using hbad
    apply Finset.sum_eq_zero
    intro t ht
    exact if_neg (fun hlegal => hn (memory_legal_promotion_into_zero
      modulus M B x t shared sigma tau D step (S,⟨A,f⟩) hlegal.1))
  have hEach (f : ↥A ↪ Fin x.2.1.val) : row f ≤ damp f*C := by
    have h := source_original_forest_BIG_PINNED_TARGET434 modulus M B mu hmu V rho R delta
      hV hr.le hR hdelta hMass hAtom x shared Q pin sigma tau D step (S,⟨A,f⟩) d hd
    simpa only [row,damp,C,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h
  have hsum : (∑ f ∈ good,damp f) ≤ memoryPromotionDampingConstant rho d :=
    source_original_memory_actual_retrieval_damping_sum434 modulus M B x sigma step
      S A rho hr hr1 d ((Finset.card_le_card hA).trans hd)
  change (∑ f,row f) ≤ _
  rw [hcut]
  calc
    _ ≤ ∑ f ∈ good,damp f*C := Finset.sum_le_sum (fun f _ => hEach f)
    _ = (∑ f ∈ good,damp f)*C := (Finset.sum_mul _ _ _).symm
    _ ≤ memoryPromotionDampingConstant rho d*C := mul_le_mul_of_nonneg_right hsum hC
    _ = _ := by ring

/-- The pinned retrieval row retains a constant independent of M and OLD length. -/
theorem source_original_forest_BIG_PINNED_RETRIEVAL_UNIFORM434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R delta : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1) (hR : 1 ≤ R) (hdelta : 0 ≤ delta)
    (hMass : ∑ p : P,mu p ≤ R)
    (hAtom : ∀ b : ℕ,(∑ p : P,if modulus p=b then mu p else 0) ≤ delta*R)
    (x : BigState modulus M B) (shared Q : Finset (Fin M)) (pin : Fin M → ℕ)
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (S A : Finset (Fin M)) (hA : A ⊆ orientedUnshared M shared)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ f : ↥A ↪ Fin x.2.1.val,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩) ∧
        Q ⊆ orientedFresh M shared A ∧ (∀ j ∈ Q,modulus (t (tau j))=pin j)
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step (S,⟨A,f⟩)‖
      else 0) ≤
      delta^Q.card * (memoryPromotionDampingConstant rho d * ((max 1 V⁻¹)^d*R^d)) := by
  have ha : A.card ≤ d := (Finset.card_le_card hA).trans hd
  have hv : (V^A.card)⁻¹ ≤ (max 1 V⁻¹)^d := by
    rw [←inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hV.le) (le_max_right _ _) _).trans
      (pow_right_mono₀ (le_max_left _ _) ha)
  have hc : 0 ≤ memoryPromotionDampingConstant rho d := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  exact (source_original_forest_BIG_PINNED_RETRIEVAL434 modulus M B mu hmu V rho R delta
    hV hr hr1 hR hdelta hMass hAtom x shared Q pin sigma tau D step S A hA d hd).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hv (pow_nonneg (zero_le_one.trans hR) _)) hc)
          (pow_nonneg hdelta _))

/-- COMPLETE actual BIG row with all stores, promotions, indexed injections
and target labels. A selected potential slot must be performed as a fresh birth.
This is an unconditional finite derivation from atom and mass bounds. -/
theorem source_original_forest_BIG_PINNED_COMPLETE434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R delta : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1) (hR : 1 ≤ R) (hdelta : 0 ≤ delta)
    (hMass : ∑ p : P,mu p ≤ R)
    (hAtom : ∀ b : ℕ,(∑ p : P,if modulus p=b then mu p else 0) ≤ delta*R)
    (x : BigState modulus M B) (shared Q : Finset (Fin M)) (pin : Fin M → ℕ)
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
        Q ⊆ orientedFresh M shared c.2.1 ∧ (∀ j ∈ Q,modulus (t (tau j))=pin j)
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
      else 0) ≤
      delta^Q.card * ((4:ℝ)^d * (memoryPromotionDampingConstant rho d *
        ((max 1 V⁻¹)^d*R^d))) := by
  classical
  let U := orientedUnshared M shared
  let row := fun S A : Finset (Fin M) => ∑ f : ↥A ↪ Fin x.2.1.val,∑ t : Fin M → P,
    if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩) ∧
      Q ⊆ orientedFresh M shared A ∧ (∀ j ∈ Q,modulus (t (tau j))=pin j)
    then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step (S,⟨A,f⟩)‖
    else 0
  let C := delta^Q.card * (memoryPromotionDampingConstant rho d * ((max 1 V⁻¹)^d*R^d))
  have hC : 0 ≤ C := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    have hmem : 0 ≤ memoryPromotionDampingConstant rho d := by
      unfold memoryPromotionDampingConstant
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    exact mul_nonneg (pow_nonneg hdelta _) (mul_nonneg hmem
      (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
        (pow_nonneg (zero_le_one.trans hR) _)))
  have hrow (S A : Finset (Fin M)) (hA : A ⊆ U) : row S A ≤ C :=
    source_original_forest_BIG_PINNED_RETRIEVAL_UNIFORM434 modulus M B mu hmu V rho R delta
      hV hr hr1 hR hdelta hMass hAtom x shared Q pin sigma tau D step S A hA d hd
  have hzero (S A : Finset (Fin M)) (hbad : ¬ S ⊆ U ∨ ¬ A ⊆ U) : row S A=0 := by
    apply Finset.sum_eq_zero
    intro f hf
    apply Finset.sum_eq_zero
    intro t ht
    apply if_neg
    intro hlegal
    rcases hbad with hS | hA
    · exact hS hlegal.1.stores_unshared
    · exact hA hlegal.1.promotes_unshared
  have hdecomp :
      (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
        if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
          Q ⊆ orientedFresh M shared c.2.1 ∧ (∀ j ∈ Q,modulus (t (tau j))=pin j)
        then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
        else 0) = ∑ S : Finset (Fin M),∑ A : Finset (Fin M),row S A := by
    simp only [BigEdgeChoice,Fintype.sum_prod_type,Fintype.sum_sigma,row]
  rw [hdecomp]
  calc
    _ = ∑ S ∈ U.powerset,∑ A : Finset (Fin M),row S A := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S hS hnot
      apply Finset.sum_eq_zero
      intro A hA
      exact hzero S A (Or.inl (by simpa only [Finset.mem_powerset] using hnot))
    _ = ∑ S ∈ U.powerset,∑ A ∈ U.powerset,row S A := by
      apply Finset.sum_congr rfl
      intro S hS
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro A hA hnot
      exact hzero S A (Or.inr (by simpa only [Finset.mem_powerset] using hnot))
    _ ≤ ∑ S ∈ U.powerset,∑ A ∈ U.powerset,C := by
      apply Finset.sum_le_sum
      intro S hS
      exact Finset.sum_le_sum (fun A hA => hrow S A (Finset.mem_powerset.mp hA))
    _ = (4:ℝ)^U.card*C := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
      ring
    _ ≤ (4:ℝ)^d*C := mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) hd) hC
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedWeight -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- The actual E OLD weight ratio is bounded before target integration.
Stores and promotions remain indexed, and the full output list is used. -/
theorem source_original_forest_BIG_OLD_WEIGHT434
    (x : BigState modulus M B) (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) (w : ℝ) (hw : 1 ≤ w)
    (d : ℕ) (hd : c.1.card ≤ d) :
    w^(physicalPendingOutput modulus M B x sigma step c).length ≤
      w^d*w^x.2.1.val := by
  rw [pending_output_length]
  have he : x.2.1.val-c.2.1.card+c.1.card ≤ d+x.2.1.val := by omega
  simpa only [pow_add] using pow_right_mono₀ hw he

/-- COMPLETE weighted positive original BIG row, with one full collision
factor per selected fresh coordinate and no additional OLD-size dependence. -/
theorem source_original_forest_BIG_PINNED_WEIGHTED434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R delta w : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1) (hR : 1 ≤ R)
    (hdelta : 0 ≤ delta) (hw : 1 ≤ w) (hMass : ∑ p : P,mu p ≤ R)
    (hAtom : ∀ b : ℕ,(∑ p : P,if modulus p=b then mu p else 0) ≤ delta*R)
    (x : BigState modulus M B) (shared Q : Finset (Fin M)) (pin : Fin M → ℕ)
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
        Q ⊆ orientedFresh M shared c.2.1 ∧ (∀ j ∈ Q,modulus (t (tau j))=pin j)
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖ *
        w^(physicalPendingOutput modulus M B x sigma step c).length
      else 0) ≤
      delta^Q.card * (w^d*(4:ℝ)^d * (memoryPromotionDampingConstant rho d *
        ((max 1 V⁻¹)^d*R^d))) * w^x.2.1.val := by
  classical
  let mask := fun (c : BigEdgeChoice modulus M B x) (t : Fin M → P) =>
    OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c ∧
      Q ⊆ orientedFresh M shared c.2.1 ∧ (∀ j ∈ Q,modulus (t (tau j))=pin j)
  let term := fun (c : BigEdgeChoice modulus M B x) (t : Fin M → P) =>
    if mask c t then
      ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖ else 0
  have hEach (c : BigEdgeChoice modulus M B x) (t : Fin M → P) :
      (if mask c t then
        ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖ *
          w^(physicalPendingOutput modulus M B x sigma step c).length else 0) ≤
      term c t*(w^d*w^x.2.1.val) := by
    dsimp only [term]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left
        (source_original_forest_BIG_OLD_WEIGHT434 modulus M B x sigma step c w hw d
          ((Finset.card_le_card h.1.stores_unshared).trans hd)) (norm_nonneg _)
    · simp
  have hrow : (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,term c t) ≤
      delta^Q.card * ((4:ℝ)^d * (memoryPromotionDampingConstant rho d *
        ((max 1 V⁻¹)^d*R^d))) :=
    source_original_forest_BIG_PINNED_COMPLETE434 modulus M B mu hmu V rho R delta
      hV hr hr1 hR hdelta hMass hAtom x shared Q pin sigma tau D step d hd
  calc
    _ ≤ ∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,term c t*(w^d*w^x.2.1.val) :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun t _ => hEach c t))
    _ = (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,term c t)*(w^d*w^x.2.1.val) := by
      simp only [Finset.sum_mul]
    _ ≤ (delta^Q.card * ((4:ℝ)^d * (memoryPromotionDampingConstant rho d *
        ((max 1 V⁻¹)^d*R^d))))*(w^d*w^x.2.1.val) :=
      mul_le_mul_of_nonneg_right hrow (mul_nonneg
        (pow_nonneg (zero_le_one.trans hw) _) (pow_nonneg (zero_le_one.trans hw) _))
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedFrame -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
variable (M : ℕ) (cap : G → ℕ) (x : BigGroupState BP modulus M cap)

/-- Literal simultaneous numerical pins on potential E slots of ALL BIG groups. -/
def sourceOriginalForestBigFramePins434
    (shared Q : G → Finset (Fin M)) (tau : BigGroupPerm (BG:=G) M)
    (pin : G → Fin M → ℕ) (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) : Prop :=
  ∀ g,Q g ⊆ orientedFresh M (shared g) (b g).2.2.1 ∧
    ∀ j ∈ Q g,modulus g ((b g).1 (tau g j))=pin g j

/-- Actual all-BIG weighted pinned row. No group-tagged equality replaces
numerical equality, and the common D/step remains fixed before integration. -/
theorem source_original_forest_BIG_FRAME_PINNED434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (V : G → ℝ) (rho R delta w : ℝ) (hV : ∀ g,0<V g)
    (hr : 0< rho) (hr1 : rho<1) (hR : 1 ≤ R) (hd : 0 ≤ delta) (hw : 1 ≤ w)
    (hMass : ∀ g,(∑ p : BP g,mu g p) ≤ R)
    (hAtom : ∀ g v,(∑ p : BP g,if modulus g p=v then mu g p else 0) ≤ delta*R)
    (shared Q : G → Finset (Fin M)) (pin : G → Fin M → ℕ)
    (sigma tau : BigGroupPerm (BG:=G) M) (D : ℕ) (step : ℤ) (d : ℕ)
    (hsize : ∀ g,(orientedUnshared M (shared g)).card ≤ d) :
    (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b ∧
        sourceOriginalForestBigFramePins434 BP modulus M cap x shared Q tau pin b then
        sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho shared sigma tau step b *
          w^(∑ g,(physicalPendingOutput (modulus g) M (cap g) (x g) (sigma g) step (b g).2).length)
        else 0) ≤
      delta^(∑ g,(Q g).card) *
        (∏ g : G,w^d*(4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 (V g)⁻¹)^d*R^d))) *
        w^(∑ g,(x g).2.1.val) := by
  classical
  let f := fun (g : G) (z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g)) =>
    if OrientedBigEdgeLegal (modulus g) M (cap g) (x g) z.1
      (shared g) (sigma g) (tau g) D step z.2 ∧
      Q g ⊆ orientedFresh M (shared g) z.2.2.1 ∧
      (∀ j ∈ Q g,modulus g (z.1 (tau g j))=pin g j) then
      ‖orientedBigBranchCoefficient (modulus g) M (cap g) (mu g) (V g) rho
        (x g) z.1 (shared g) (sigma g) (tau g) step z.2‖ *
        w^(physicalPendingOutput (modulus g) M (cap g) (x g) (sigma g) step z.2).length else 0
  have hprod (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) :
      (∏ g : G,f g (b g)) =
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b ∧
        sourceOriginalForestBigFramePins434 BP modulus M cap x shared Q tau pin b then
        sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho shared sigma tau step b *
          w^(∑ g,(physicalPendingOutput (modulus g) M (cap g) (x g) (sigma g) step (b g).2).length)
        else 0 := by
    simp only [f,Finset.prod_ite_zero,Finset.mem_univ,forall_const,
      sourceOriginalMemoryBigFrameLegal434,sourceOriginalForestBigFramePins434,
      sourceOriginalMemoryBigFrameNorm434,forall_and,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have he :
      (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,∏ g : G,f g (b g)) =
      ∏ g : G,∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g),f g z := by
    convert (Fintype.prod_sum f).symm using 1 <;> congr <;> exact Subsingleton.elim _ _
  simp_rw [←hprod]
  rw [he]
  calc
    _ ≤ ∏ g : G,delta^(Q g).card *
        (w^d*(4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 (V g)⁻¹)^d*R^d))) *
        w^(x g).2.1.val := by
      apply Finset.prod_le_prod₀
      · intro g hg
        apply Finset.sum_nonneg
        intro z hz
        dsimp only [f]
        split_ifs <;> positivity
      · intro g hg
        rw [Fintype.sum_prod_type,Finset.sum_comm]
        exact source_original_forest_BIG_PINNED_WEIGHTED434 (modulus g) M (cap g)
          (mu g) (hmu g) (V g) rho R delta w (hV g) hr hr1 hR hd hw (hMass g) (hAtom g)
          (x g) (shared g) (Q g) (pin g) (sigma g) (tau g) D step d (hsize g)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedPacket -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Weighted all-BIG pinned row at the literal common source divisor and step. -/
def sourceOriginalForestPinnedPhysicalBigRow434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss : GroupPermFamily (G:=SG) (J+ell))
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ) (rho : ℝ) (o k : ℤ)
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ) (w : ℝ) : ℝ :=
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap pat aux st bs ss
  let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap pat aux st bs ss o k
  ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
    if sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap st.2
        (sourceBigShared J ell m pat) bs bt D step b ∧
      sourceOriginalForestBigFramePins434 BP bigMod (J+ell) cap st.2
        (sourceBigShared J ell m pat) Q bt pin b then
      sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu V rho
        (sourceBigShared J ell m pat) bs bt step b *
      w^(∑ g,(physicalPendingOutput (bigMod g) (J+ell) (cap g) (st.2 g) (bs g) step (b g).2).length)
    else 0

def sourceOriginalForestEPinnedPacket434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ) (w : ℝ)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) : ℝ :=
  ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
  ∑ zs : GroupState SP smallMod (J+ell),
    let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bigSigma bigTau ss tt b zs
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      sourceOriginalForestBigFramePins434 BP bigMod (J+ell) cap st.2
        (sourceBigShared J ell m (patterns nu)) Q bigTau pin b
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z‖ * w^(∑ g,(physicalPendingOutput (bigMod g) (J+ell) (cap g) (st.2 g) (bigSigma g)
        (sourceOrientedStep SP smallMod BP bigMod J ell m cap (patterns nu) aux st bigSigma ss o k)
        (b g).2).length) else 0

/-- Exact transfer from the proved BIG promotion row to the literal
SMALL x BIG source packet. The global joint K is bounded once, after
fixing the full BIG endpoints; it is never separated into functions of
individual groups or endpoints. -/
theorem source_original_forest_E_PINNED_PACKET434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ) (w : ℝ)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0<q) (hq1 : q<1) (hVs : ∀ g,0<Vs g) (hw : 1 ≤ w)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (Kcap : ℝ)
    (hK : ∀ target : (g : BG) → Fin (J+ell) → BP g,
      ‖Knu nu aux (fun g i => (st.2 g).1 (bigSigma g i)) target‖ ≤ Kcap) :
    sourceOriginalForestEPinnedPacket434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bigSigma bigTau ss tt Q pin w q rho Vs Vb mu Knu
      zeta theta o k ≤
    ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ *
    Kcap * (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    sourceOriginalForestPinnedPhysicalBigRow434 SP smallMod BP bigMod
      J ell m cap (patterns nu) aux st bigSigma bigTau ss mu Vb rho o k Q pin w := by
  classical
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
    (patterns nu) aux st bigSigma ss
  let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
    (patterns nu) aux st bigSigma ss o k
  let W := ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
    (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
    (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  let scalar := fun b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 =>
    originalEdgeScalar (Knu nu aux
      (fun g i => (st.2 g).1 (bigSigma g i))
      (fun g i => (b g).1 (bigTau g i))) zeta theta D o k
  let wt := fun b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 =>
    w^(∑ g,(physicalPendingOutput (bigMod g) (J+ell) (cap g) (st.2 g) (bigSigma g) step (b g).2).length)
  let bn := fun b => sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu Vb rho
    (sourceBigShared J ell m (patterns nu)) bigSigma bigTau step b * wt b
  let good := fun b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 =>
    sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap st.2
      (sourceBigShared J ell m (patterns nu)) bigSigma bigTau D step b ∧
      sourceOriginalForestBigFramePins434 BP bigMod (J+ell) cap st.2
        (sourceBigShared J ell m (patterns nu)) Q bigTau pin b
  let smallK := fun b zs => groupPermutedKernel SP smallMod (J+ell) q Vs
    (sourceSmallShared J ell) step (fun _ _ => scalar b) ss tt st.1 zs
  have hW : 0 ≤ W := norm_nonneg _
  have hbn (b) : 0 ≤ bn b := mul_nonneg
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (pow_nonneg (zero_le_one.trans hw) _)
  have hCs : 0 ≤ Cs := by
    have hsqrt : Real.sqrt q < 1 := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    have hs : 0<1-Real.sqrt q := sub_pos.mpr hsqrt
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hscalar (b) : ‖scalar b‖ ≤ Kcap := by
    dsimp only [scalar]
    rw [source_original_edge_scalar_norm434 _ _ _ _ _ _ ho]
    exact hK _
  have hsmall (b) : (∑ zs : GroupState SP smallMod (J+ell),‖smallK b zs‖) ≤
      ‖scalar b‖*Cs :=
    source_original_memory_SOURCE_SMALL_group_kernel_row434 SP smallMod J ell
      q Vs hq hq1 hVs step (fun _ _ => scalar b) ss tt st.1
  let choice := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
    J ell m cap patterns nu aux st bigSigma bigTau ss tt
  have hnorm (b) (zs) :
      ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st (choice b zs)‖ * wt b =
      (W*bn b)*‖smallK b zs‖ := by
    dsimp only [choice,sourceOriginalMemoryFixedPhysicalChoice434,
      sourceOrientedPhysicalCoefficient,W,bn,sourceOriginalMemoryBigFrameNorm434,
      smallK,scalar,D,step]
    simp only [norm_mul,norm_prod]
    ring
  have hrow (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2) :
      (∑ zs : GroupState SP smallMod (J+ell),
        if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns
          st o k (choice b zs) ∧ sourceOriginalForestBigFramePins434 BP bigMod (J+ell) cap st.2
        (sourceBigShared J ell m (patterns nu)) Q bigTau pin b
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (choice b zs)‖ * wt b else 0) ≤
      (W*Kcap*Cs)*(if good b then bn b else 0) := by
    by_cases hb : good b
    · rw [if_pos hb]
      calc
        _ ≤ ∑ zs : GroupState SP smallMod (J+ell),(W*bn b)*‖smallK b zs‖ := by
          apply Finset.sum_le_sum
          intro zs hzs
          split_ifs
          · rw [hnorm]
          · exact mul_nonneg (mul_nonneg hW (hbn b)) (norm_nonneg _)
        _ = (W*bn b)*(∑ zs : GroupState SP smallMod (J+ell),‖smallK b zs‖) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ (W*bn b)*(‖scalar b‖*Cs) :=
          mul_le_mul_of_nonneg_left (hsmall b) (mul_nonneg hW (hbn b))
        _ ≤ (W*bn b)*(Kcap*Cs) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hscalar b) hCs)
            (mul_nonneg hW (hbn b))
        _ = _ := by ring
    · rw [if_neg hb,mul_zero]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro zs hzs
      apply if_neg
      intro hz
      exact hb ⟨hz.1.2.2.2.1,hz.2⟩
  unfold sourceOriginalForestEPinnedPacket434
  calc
    _ ≤ ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
        (W*Kcap*Cs)*(if good b then bn b else 0) :=
      Finset.sum_le_sum (fun b _ => hrow b)
    _ = (W*Kcap*Cs)*∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
        if good b then bn b else 0 := (Finset.mul_sum _ _ _).symm
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedEdge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalForestEPinnedRow434
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ) (w : ℝ)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) : ℝ :=
  ∑ z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st,
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      sourceOriginalForestBigFramePins434 BP bigMod (J+ell) cap st.2
      (sourceBigShared J ell m (patterns z.1)) Q z.2.2.1.tauBig pin z.2.2.1.bigChoice
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z‖ *
      w^(∑ g,((sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k z).2 g).2.card) else 0

/-- Exact outer-sum disintegration of the original E row, without a
new kernel or a loss of equal-output or repeated-atom multiplicities. -/
theorem source_original_forest_E_PINNED_PACKETS434
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ) (w : ℝ)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    sourceOriginalForestEPinnedRow434 SP smallMod BP bigMod J ell m cap
      patterns Q pin w q rho Vs Vb mu Knu zeta theta o k st =
    ∑ nu : Nu, ∑ aux : SourceBigAux BP J m (patterns nu),
    ∑ bs : BigGroupPerm (BG:=BG) (J+ell),
    ∑ bt : BigGroupPerm (BG:=BG) (J+ell),
    ∑ ss : GroupPermFamily (G:=SG) (J+ell),
    ∑ tt : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalForestEPinnedPacket434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bs bt ss tt Q pin w q rho Vs Vb mu Knu zeta theta o k := by
  classical
  letI : Fintype (sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2) := inferInstance
  letI : Fintype (GroupState SP smallMod (J+ell)) := inferInstance
  letI : Fintype (BigGroupPerm (BG:=BG) (J+ell)) := inferInstance
  letI : Fintype (GroupPermFamily (G:=SG) (J+ell)) := inferInstance
  letI (nu : Nu) : Fintype (SourceBigAux BP J m (patterns nu)) := inferInstance
  let e : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st ≃
      (Σ nu : Nu, SourceBigAux BP J m (patterns nu) ×
        BigGroupPerm (BG:=BG) (J+ell) × BigGroupPerm (BG:=BG) (J+ell) ×
        GroupPermFamily (G:=SG) (J+ell) × GroupPermFamily (G:=SG) (J+ell) ×
        sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 ×
        GroupState SP smallMod (J+ell)) :=
    { toFun := fun z => ⟨z.1,z.2.1,z.2.2.1.sigmaBig,z.2.2.1.tauBig,
        z.2.2.2.1,z.2.2.2.2,z.2.2.1.bigChoice,z.2.2.1.smallTarget⟩
      invFun := fun z => ⟨z.1,z.2.1,
        ⟨z.2.2.1,z.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2⟩,
        z.2.2.2.2.1,z.2.2.2.2.2.1⟩
      left_inv := by rintro ⟨nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩;rfl
      right_inv := by rintro ⟨nu,aux,bs,bt,ss,tt,b,zs⟩;rfl }
  unfold sourceOriginalForestEPinnedRow434
  rw [Fintype.sum_equiv e _ (fun z =>
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k
      (e.symm z) ∧ sourceOriginalForestBigFramePins434 BP bigMod (J+ell) cap st.2
      (sourceBigShared J ell m (patterns (e.symm z).1)) Q (e.symm z).2.2.1.tauBig pin (e.symm z).2.2.1.bigChoice
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st (e.symm z)‖ *
      w^(∑ g,((sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns st o k (e.symm z)).2 g).2.card) else 0)
    (by rintro ⟨nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩; rfl)]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type]
  rfl

/-- Complete literal joint E pinned row. Full K is capped pointwise;
D retains all shared SMALL labels, and every auxiliary and endpoint
permutation mass is normalized exactly. The bound is derived, not assumed. -/
theorem source_original_forest_E_PINNED_FULL_ROW434
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ)
    (w delta R q rho : ℝ) (hw : 1 ≤ w) (hd : 0 ≤ delta) (hR : 1 ≤ R)
    (hq : 0<q) (hq1 : q<1) (hr : 0< rho) (hr1 : rho<1)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (hVs : ∀ g,0<Vs g) (hVb : ∀ g,0<Vb g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hMass : ∀ g,(∑ p : BP g,mu g p) ≤ R)
    (hAtom : ∀ g v,(∑ p : BP g,if bigMod g p=v then mu g p else 0) ≤ delta*R)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bigMod g p:ℝ)=Vb g)
    (Knu : SourcePatternK BP J ell m patterns) (Kcap : Nu → ℝ)
    (hK0 : ∀ nu,0 ≤ Kcap nu) (hK : ∀ nu aux s t,‖Knu nu aux s t‖ ≤ Kcap nu)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    sourceOriginalForestEPinnedRow434 SP smallMod BP bigMod J ell m cap patterns
      Q pin w q rho Vs Vb mu Knu zeta theta o k st ≤
    delta^(∑ g,(Q g).card) *
      ((∑ nu : Nu,Kcap nu)*(∏ g : SG,memorySmallRowConstant q (Vs g) ell)*
        (∏ g : BG,w^(ell+m)*(4:ℝ)^(ell+m)*
          (memoryPromotionDampingConstant rho (ell+m)*((max 1 (Vb g)⁻¹)^(ell+m)*R^(ell+m))))) *
      w^(∑ g,(st.2 g).2.1.val) := by
  classical
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  let Cb := ∏ g : BG,w^(ell+m)*(4:ℝ)^(ell+m)*
    (memoryPromotionDampingConstant rho (ell+m)*((max 1 (Vb g)⁻¹)^(ell+m)*R^(ell+m)))
  let B := delta^(∑ g,(Q g).card)*Cb*w^(∑ g,(st.2 g).2.1.val)
  have hCs : 0 ≤ Cs := by
    have hsqrt : Real.sqrt q < 1 := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    have hs : 0<1-Real.sqrt q := sub_pos.mpr hsqrt
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hBig (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
      (bs bt : BigGroupPerm (BG:=BG) (J+ell)) (ss : GroupPermFamily (G:=SG) (J+ell)) :
      sourceOriginalForestPinnedPhysicalBigRow434 SP smallMod BP bigMod J ell m cap
        (patterns nu) aux st bs bt ss mu Vb rho o k Q pin w ≤ B := by
    exact source_original_forest_BIG_FRAME_PINNED434 BP bigMod (J+ell) cap st.2 mu hmu
      Vb rho R delta w hVb hr hr1 hR hd hw hMass hAtom
      (sourceBigShared J ell m (patterns nu)) Q pin bs bt _ _ (ell+m)
      (memory_source_unshared_count J ell m (patterns nu))
  have hNu (nu : Nu) :
      (∑ aux : SourceBigAux BP J m (patterns nu),
        ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
        ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
          sourceOriginalForestEPinnedPacket434 SP smallMod BP bigMod J ell m cap patterns
            nu aux st bs bt ss tt Q pin w q rho Vs Vb mu Knu zeta theta o k) ≤ Kcap nu*Cs*B := by
    let W := fun aux : SourceBigAux BP J m (patterns nu) =>
      ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ)*
        (bigEndpointPairMass (BG:=BG) (J+ell):ℂ)*
        (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖
    calc
      _ ≤ ∑ aux : SourceBigAux BP J m (patterns nu),
          ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
          ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
          W aux*(Kcap nu*Cs*B) := by
        apply Finset.sum_le_sum
        intro aux ha
        apply Finset.sum_le_sum
        intro bs hb
        apply Finset.sum_le_sum
        intro bt hc
        apply Finset.sum_le_sum
        intro ss hs
        apply Finset.sum_le_sum
        intro tt ht
        have hp := source_original_forest_E_PINNED_PACKET434 SP smallMod BP bigMod
          J ell m cap patterns nu aux st bs bt ss tt Q pin w q rho Vs Vb hq hq1 hVs hw
          mu Knu zeta theta o k ho (Kcap nu) (fun target => hK nu aux _ target)
        have hh := mul_le_mul_of_nonneg_left (hBig nu aux bs bt ss)
          (mul_nonneg (mul_nonneg (show 0 ≤ W aux from norm_nonneg _) (hK0 nu)) hCs)
        exact hp.trans (by convert hh using 1 <;> dsimp only [W,Cs] <;> ring)
      _ = (∑ aux : SourceBigAux BP J m (patterns nu),
          ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
          ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
          W aux)*(Kcap nu*Cs*B) := by simp only [Finset.sum_mul]
      _ = Kcap nu*Cs*B := by
        rw [source_original_memory_ALL_OUTER_total_mass434 (SG:=SG) BP bigMod
          J ell m Vb hVb hHarmonic (patterns nu),one_mul]
  rw [source_original_forest_E_PINNED_PACKETS434]
  calc
    _ ≤ ∑ nu : Nu,Kcap nu*Cs*B := Finset.sum_le_sum (fun nu _ => hNu nu)
    _ = (∑ nu : Nu,Kcap nu)*Cs*B := by simp only [Finset.sum_mul]
    _ = _ := by dsimp only [Cs,Cb,B];ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestPinnedSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Every original tilted physical atom is small, directly from its actual
baseline and prime floor. No normalized replacement law is postulated. -/
theorem source_original_forest_PHYSICAL_ATOM434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ) (g : G)
    (vmin floor : ℝ) (hv : 0<vmin) (hfloor : 0<floor) (hV : vmin ≤ V g)
    (hBig : ∀ p : BP g,floor ≤ (modulus g p:ℝ))
    (hb : ∀ p : BP g,(1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q N g p)
    (p : BP g) : physicalSourceMuTilde BP modulus q N V g p ≤ 2/(vmin*floor) := by
  have hV0 : 0<V g := hv.trans_le hV
  have hmul : vmin*floor ≤ V g*(modulus g p:ℝ) :=
    mul_le_mul hV (hBig p) hfloor.le hV0.le
  have hinv : 1/(V g*(modulus g p:ℝ)) ≤ 1/(vmin*floor) :=
    one_div_le_one_div_of_le (mul_pos hv hfloor) hmul
  have hcap : physicalSourceMuTilde BP modulus q N V g p ≤
      2*(1/(V g*(modulus g p:ℝ))) := by
    unfold physicalSourceMuTilde
    rw [←div_div]
    calc
      _ ≤ (1/(V g*(modulus g p:ℝ)))/((1:ℝ)/2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (hb p)
      _ = _ := by ring
  calc
    _ ≤ 2*(1/(V g*(modulus g p:ℝ))) := hcap
    _ ≤ 2*(1/(vmin*floor)) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = _ := by ring

/-- Actual source-depth weighted BIG row with numerical forest pins.
The exponential atom factor and mass two are DERIVED for the original
physicalSourceMuTilde. Uniform in J, cap, input state, pins and permutations. -/
theorem eventually_source_original_forest_SOURCE_BIG_PINNED_WEIGHTED434
    (c vmin : ℝ) (hc : 0<c) (hv : 0<vmin)
    (q rho : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0< rho) (hr1 : rho<1)
    (ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
      (V : G → ℝ) (J : ℕ) (pat : SourcePattern G J m) (g : G)
      (hi : Function.Injective (modulus g)) (hV : vmin ≤ V g)
      (hHarmonic : ∑ p : BP g,1/(modulus g p:ℝ)=V g)
      (hBig : ∀ p : BP g,Real.exp (L^c) ≤ (modulus g p:ℝ))
      (B : ℕ) (x : BigState (modulus g) (J+ell) B)
      (Q : Finset (Fin (J+ell))) (pin : Fin (J+ell) → ℕ)
      (sigma tau : Equiv.Perm (Fin (J+ell))) (D : ℕ) (step : ℤ) (w : ℝ) (hw : 1 ≤ w),
    let mu := physicalSourceMuTilde BP modulus q (2*Nat.ceil (L^(0.52:ℝ))) V g
    let delta := 2/(vmin*Real.exp (L^c))
    (∑ z : BigEdgeChoice (modulus g) (J+ell) B x,∑ t : Fin (J+ell) → BP g,
      if OrientedBigEdgeLegal (modulus g) (J+ell) B x t (sourceBigShared J ell m pat g)
          sigma tau D step z ∧ Q ⊆ orientedFresh (J+ell) (sourceBigShared J ell m pat g) z.2.1 ∧
          (∀ j ∈ Q,modulus g (t (tau j))=pin j)
      then ‖orientedBigBranchCoefficient (modulus g) (J+ell) B mu (V g) rho x t
        (sourceBigShared J ell m pat g) sigma tau step z‖ *
        w^(physicalPendingOutput (modulus g) (J+ell) B x sigma step z).length else 0) ≤
      delta^Q.card * (w^(ell+m)*(4:ℝ)^(ell+m) *
        (memoryPromotionDampingConstant rho (ell+m) *
          ((max 1 (V g)⁻¹)^(ell+m)*2^(ell+m)))) * w^x.2.1.val := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro G instG instDG BP instP instDP modulus instNZ V J pat g hi hV hHarmonic hBig
    B x Q pin sigma tau D step w hw
  have hV0 : 0<V g := hv.trans_le hV
  have hb (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q (2*Nat.ceil (L^(0.52:ℝ))) g p :=
    (source_original_B26_physical_baseline_half434 BP modulus q hq hq1 _ g p
      (hL _ (hBig p))).1
  obtain ⟨hmu,hMass⟩ := source_original_memory_physical_tilt_mass_two434 BP modulus
    q (2*Nat.ceil (L^(0.52:ℝ))) V g hV0 hHarmonic hb
  let mu := physicalSourceMuTilde BP modulus q (2*Nat.ceil (L^(0.52:ℝ))) V g
  let delta := 2/(vmin*Real.exp (L^c))
  have hdelta : 0 ≤ delta := by dsimp only [delta]; positivity
  have hpoint (p : BP g) : mu p ≤ delta :=
    source_original_forest_PHYSICAL_ATOM434 BP modulus q _ V g vmin (Real.exp (L^c))
      hv (Real.exp_pos _) hV hBig hb p
  have hAtom (b : ℕ) : (∑ p : BP g,if modulus g p=b then mu p else 0) ≤ delta*2 :=
    source_original_forest_NUMERIC_ATOM434 (modulus g) hi mu (delta*2) (by positivity)
      (fun p => (hpoint p).trans (by linarith)) b
  exact source_original_forest_BIG_PINNED_WEIGHTED434 (modulus g) (J+ell) B mu hmu
    (V g) rho 2 delta w hV0 hr hr1 (by norm_num) hdelta hw hMass hAtom x
    (sourceBigShared J ell m pat g) Q pin sigma tau D step (ell+m)
    (memory_source_unshared_count J ell m pat g)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestGhostAtoms -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Numerical singleton mass of the genuine zero-residue birth atom law.
There is exactly one residue-zero atom per prime; no 1/p is inserted here. -/
theorem source_original_forest_BIRTH_NUMERIC_MASS434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (v : ℕ) :
    (∑ z : Atom P modulus,if modulus z.1=v then
      ‖sourceBirthNu (fun p => (mu p:ℂ)) z‖ else 0) =
    ∑ p : P,if modulus p=v then mu p else 0 := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hm : modulus p=v
  · simp only [hm,if_true,sourceBirthNu,birthMass,apply_ite,norm_zero,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hmu p)]
    change (∑ r : ZMod (modulus p),if r=0 then mu p else 0)=mu p
    rw [Finset.sum_ite_eq']
    simp
  · simp [hm]

/-- The original harmonic tilted mass is at least one when its actual
baseline is at most one. This proves the lower normalization needed by G. -/
theorem source_original_forest_PHYSICAL_MASS_ONE434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ) (g : G) (hV : 0<V g)
    (hHarmonic : ∑ p : BP g,1/(modulus g p:ℝ)=V g)
    (hb : ∀ p : BP g,0 < physicalSourceBaseline BP modulus q N g p)
    (hb1 : ∀ p : BP g,physicalSourceBaseline BP modulus q N g p ≤ 1) :
    1 ≤ ∑ p : BP g,physicalSourceMuTilde BP modulus q N V g p := by
  have hp (p : BP g) : 0<(modulus g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hn : (∑ p : BP g,1/(V g*(modulus g p:ℝ)))=1 := by
    calc
      _ = (V g)⁻¹*(∑ p : BP g,1/(modulus g p:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        simp [div_eq_mul_inv,mul_inv_rev,mul_comm]
      _ = 1 := by rw [hHarmonic,inv_mul_cancel₀ (ne_of_gt hV)]
  rw [←hn]
  apply Finset.sum_le_sum
  intro p hp'
  unfold physicalSourceMuTilde
  have hden : V g*(modulus g p:ℝ)*physicalSourceBaseline BP modulus q N g p ≤
      V g*(modulus g p:ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb1 p) (mul_pos hV (hp p)).le
  exact one_div_le_one_div_of_le (mul_pos (mul_pos hV (hp p)) (hb p)) hden

/-- The actual tilted numerical birth law obeys the NORMALIZED atom cap
needed for sourceGhostTerm pinning; its total mass is not discarded. -/
theorem source_original_forest_PHYSICAL_NORMALIZED_ATOM434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ) (g : G)
    (hi : Function.Injective (modulus g)) (vmin floor : ℝ)
    (hv : 0<vmin) (hfloor : 0<floor) (hV : vmin ≤ V g)
    (hHarmonic : ∑ p : BP g,1/(modulus g p:ℝ)=V g)
    (hBig : ∀ p : BP g,floor ≤ (modulus g p:ℝ))
    (hb : ∀ p : BP g,(1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q N g p)
    (hb1 : ∀ p : BP g,physicalSourceBaseline BP modulus q N g p ≤ 1) :
    let mu := physicalSourceMuTilde BP modulus q N V g
    ∀ v : ℕ,(∑ p : BP g,if modulus g p=v then mu p else 0) ≤
      (2/(vmin*floor))*(∑ p : BP g,mu p) := by
  dsimp only
  have hdelta : 0 ≤ 2/(vmin*floor) := by positivity
  have hmass := source_original_forest_PHYSICAL_MASS_ONE434 BP modulus q N V g
    (hv.trans_le hV) hHarmonic (fun p => lt_of_lt_of_le (by norm_num) (hb p)) hb1
  intro v
  have hsmall := source_original_forest_NUMERIC_ATOM434 (modulus g) hi
    (physicalSourceMuTilde BP modulus q N V g) (2/(vmin*floor)) hdelta
    (source_original_forest_PHYSICAL_ATOM434 BP modulus q N V g vmin floor hv hfloor hV hBig hb) v
  exact hsmall.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass hdelta)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestGhostSource -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The genuine source visit parameters and zero-residue birth law, with
indexed numerical pins, doubled birth costs, actual repeats and b!.
The normalized atom hypothesis is discharged for physicalSourceMuTilde
by source_original_forest_PHYSICAL_NORMALIZED_ATOM434. -/
theorem source_original_forest_SOURCE_GHOST_PINNED434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (old : List (Atom P modulus)) (B : ℕ)
    (q rho V W w : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho)
    (hV : 0 ≤ V) (hVW : V ≤ W) (hW : 1 ≤ W)
    (hw : 0 < w) (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (hmass : ∑ p,mu p ≤ 2)
    (Q : Finset ℕ) (pin : ℕ → ℕ) (delta : ℝ) (hd : 0 ≤ delta)
    (hAtom : ∀ v : ℕ,(∑ p : P,if modulus p=v then mu p else 0) ≤ delta*(∑ p : P,mu p)) :
    (∑ c : GhostWitnessChoice old (fun z => z.2=0) B,
      if Q ⊆ Finset.range c.2.1.val ∧
        (∀ j : Fin c.2.1.val,j.val ∈ Q → modulus (c.2.2 j).1=pin j.val) then
      (2:ℝ)^c.2.1.val *
        ‖sourceGhostTerm old (fun z => z.2=0) c.1.1 c.2.2
          (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
          (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
          (-((sourceVisitEta q N i:ℝ):ℂ)*(V:ℂ)/(rho:ℂ))
          (sourceBirthNu (fun p => (mu p:ℂ)))‖ *
        w^(afterGhost old c.1.1 c.2.2).length else 0) ≤
      delta^Q.card*Real.exp (4*W*w/rho)*w^old.length := by
  let eta := sourceVisitEta q N i
  let qi := sourceVisitQ q N i
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  have hqi := source_original_evolution_visit_q_bounds434 q hq hq1 N i
  have hnA : ‖-((eta:ℝ):ℂ)/(rho:ℂ)‖ = eta/rho := by
    simp [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg he.1,abs_of_pos hr,eta]
  have hnX : ‖((qi:ℝ):ℂ)/(rho:ℂ)^2‖ = qi/rho^2 := by
    simp [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hqi.1,abs_of_pos hr,qi]
  have hnC : ‖2*(-((eta:ℝ):ℂ)*(V:ℂ)/(rho:ℂ))‖ = 2*eta*V/rho := by
    simp [norm_div,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg he.1,abs_of_nonneg hV,abs_of_pos hr,eta]
    ring
  have hc : ‖-((eta:ℝ):ℂ)/(rho:ℂ)‖/w +
      ‖((qi:ℝ):ℂ)/(rho:ℂ)^2‖ ≤ 1 := by
    rw [hnA,hnX,div_div]
    have h1 := div_le_div_of_nonneg_right he.2 (mul_pos hr hw).le
    have h2 := div_le_div_of_nonneg_right hqi.2 (sq_nonneg rho)
    exact (add_le_add h1 h2).trans hcontrol
  have hAtom' (v : ℕ) :
      (∑ z : Atom P modulus,if modulus z.1=v then
        ‖sourceBirthNu (fun p => (mu p:ℂ)) z‖ else 0) ≤
      delta*(∑ z : Atom P modulus,‖sourceBirthNu (fun p => (mu p:ℂ)) z‖) := by
    rw [source_original_forest_BIRTH_NUMERIC_MASS434 modulus mu hmu,
      source_original_evolution_birth_norm_mass434 modulus mu hmu]
    exact hAtom v
  have hs := source_original_forest_GHOST_PINNED_WEIGHTED434 old
    (fun z => z.2=0) B (-((eta:ℝ):ℂ)/(rho:ℂ))
    (((qi:ℝ):ℂ)/(rho:ℂ)^2)
    (2*(-((eta:ℝ):ℂ)*(V:ℂ)/(rho:ℂ)))
    (sourceBirthNu (fun p => (mu p:ℂ))) (fun z => modulus z.1) Q pin w delta hw hd hc hAtom'
  simp_rw [source_original_evolution_double_birth_norm434] at hs
  rw [hnC,source_original_evolution_birth_norm_mass434 modulus mu hmu] at hs
  have hC : 2*eta*V/rho ≤ 2*W/rho := by
    apply div_le_div_of_nonneg_right _ hr.le
    have hh := mul_le_mul_of_nonneg_right he.2 hV
    nlinarith only [hh,hVW]
  have hM : 0 ≤ ∑ p,mu p := Finset.sum_nonneg (fun p _ => hmu p)
  have hecap : (2*eta*V/rho)*w*(∑ p,mu p) ≤ 4*W*w/rho := by
    have hh := mul_le_mul hC hmass hM (by positivity : 0 ≤ 2*W/rho)
    convert mul_le_mul_of_nonneg_left hh hw.le using 1 <;> ring
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hecap) (pow_nonneg hd _)) (pow_nonneg hw.le _))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestGhostPhysical -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Full original physical G witness row, with every birth weighted by two.
No reachability or distinctness condition is placed on OLD inventory.
The two original finite-state indices and every local witness remain literal. -/
theorem source_original_forest_PHYSICAL_G_PINNED_ROW434
    (q rho W w : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hw : 0 < w) (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (Q : BG → Finset ℕ) (pin : BG → ℕ → ℕ) (delta : ℝ) (hd : 0 ≤ delta)
    (hAtom : ∀ g v,(∑ p : BP g,if bm g p=v then mu g p else 0) ≤ delta*(∑ p : BP g,mu g p))
    (x : FullPhysicalState SP sm BP bm M cap) :
    (∑ y : FullPhysicalState SP sm BP bm M cap,
      ∑ c : FullGhostWitness SP sm BP bm M cap x,
        if ∀ g,Q g ⊆ Finset.range (c g).2.1.val ∧
          (∀ j : Fin (c g).2.1.val,j.val ∈ Q g → bm g ((c g).2.2 j).1=pin g j.val) then
        (2:ℝ)^(∑ g,(c g).2.1.val) *
          ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖ *
          w^(∑ g,((y.2 g).2).1.val) else 0) ≤
      delta^(∑ g,(Q g).card)*Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho) *
        w^(∑ g,((x.2 g).2).1.val) := by
  classical
  let good (g : BG)
      (c : GhostWitnessChoice (fockToList ((x.2 g).2))
        (fun z : Atom (BP g) (bm g) => z.2=0) (cap g)) : Prop :=
    Q g ⊆ Finset.range c.2.1.val ∧
      (∀ j : Fin c.2.1.val,j.val ∈ Q g → bm g (c.2.2 j).1=pin g j.val)
  let factor (g : BG)
      (c : GhostWitnessChoice (fockToList ((x.2 g).2))
        (fun z : Atom (BP g) (bm g) => z.2=0) (cap g)) : ℝ :=
    if good g c then (2:ℝ)^c.2.1.val *
      ‖sourceGhostTerm (fockToList ((x.2 g).2)) (fun z => z.2=0) c.1.1 c.2.2
        (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
        (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
        (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))
        (sourceBirthNu (fun p => (mu g p:ℂ)))‖ *
      w^(afterGhost (fockToList ((x.2 g).2)) c.1.1 c.2.2).length else 0
  have hf0 (g : BG) (c) : 0 ≤ factor g c := by
    dsimp only [factor]
    split_ifs <;> positivity
  have hsingle (c : FullGhostWitness SP sm BP bm M cap x) :
      (∑ y : FullPhysicalState SP sm BP bm M cap,
        if ∀ g,good g (c g) then
          (2:ℝ)^(∑ g,(c g).2.1.val) *
            ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖ *
            w^(∑ g,((y.2 g).2).1.val) else 0) ≤ ∏ g,factor g (c g) := by
    by_cases hgood : ∀ g,good g (c g)
    · simp only [if_pos hgood]
      by_cases hc : sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c
      · simp_rw [source_original_PHYSICAL_G_witness_target434 SP sm BP bm M cap
          q rho N i V mu x _ c hc]
        simp only [apply_ite,norm_zero,mul_ite,mul_zero,ite_mul,zero_mul,
          Finset.sum_ite_eq',Finset.mem_univ,if_true]
        dsimp only [sourceOriginalPhysicalGhostWitnessTarget434,sourceOriginalFockFromList434]
        rw [sourceOriginalPhysicalGhostWitnessCoefficient434,norm_prod]
        dsimp only [factor]
        simp only [if_pos (hgood _),Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
        exact le_rfl
      · simp_rw [source_original_PHYSICAL_G_witness_nofit_zero434 SP sm BP bm M cap
          q rho N i V mu x _ c hc,norm_zero,mul_zero,zero_mul,Finset.sum_const_zero]
        exact Finset.prod_nonneg (fun g _ => hf0 g (c g))
    · simp only [if_neg hgood,Finset.sum_const_zero]
      exact Finset.prod_nonneg (fun g _ => hf0 g (c g))
  have hg (g : BG) :
      (∑ c,factor g c) ≤ delta^(Q g).card*Real.exp (4*W*w/rho)*w^((x.2 g).2).1.val := by
    simpa only [factor,good,fockToList_length] using
      source_original_forest_SOURCE_GHOST_PINNED434 (bm g)
        (fockToList ((x.2 g).2)) (cap g) q rho (V g) W w N i hq hq1 hr
        (hV g) (hVW g) hW hw hcontrol (mu g) (hmu g) (hmass g)
        (Q g) (pin g) delta hd (hAtom g)
  have hexp (n : ℕ) :
      Real.exp (4*W*w/rho)^n=Real.exp ((4*W*w/rho)*(n:ℝ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,ih,←Real.exp_add]
      congr 1
      push_cast
      ring
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ c : FullGhostWitness SP sm BP bm M cap x,∏ g,factor g (c g) :=
      Finset.sum_le_sum (fun c _ => hsingle c)
    _ = ∏ g,∑ c,factor g c := (Fintype.prod_sum factor).symm
    _ ≤ ∏ g,delta^(Q g).card*Real.exp (4*W*w/rho)*w^((x.2 g).2).1.val :=
      Finset.prod_le_prod₀
        (fun g _ => Finset.sum_nonneg (fun c _ => hf0 g c)) (fun g _ => hg g)
    _ = _ := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Finset.prod_pow_eq_pow_sum,hexp]
      congr 2 <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestSourceLaws -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Original moving-depth tilted laws: positivity, total mass at most two,
and the full normalized numerical-atom cap. All estimates are derived from
the original harmonic mass and exponential prime floor, uniformly in groups. -/
theorem eventually_source_original_forest_TILT_LAWS434
    (c vmin q : ℝ) (hc : 0<c) (hv : 0<vmin) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (V : G → ℝ) (hi : ∀ g,Function.Injective (bm g)) (hV : ∀ g,vmin ≤ V g)
      (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
      (hBig : ∀ g (p : BP g),Real.exp (L^c) ≤ (bm g p:ℝ)),
    let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
    (∀ g p,0 < mu g p) ∧ (∀ g,∑ p : BP g,mu g p ≤ 2) ∧
      (∀ g v,(∑ p : BP g,if bm g p=v then mu g p else 0) ≤
        (2/(vmin*Real.exp (L^c)))*(∑ p : BP g,mu g p)) := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hVisits
  intro G instG instDG BP instP instDP bm instNZ V hi hV hHarmonic hBig
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  have hb (g : G) (p : BP g) : (1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p ∧
      physicalSourceBaseline BP bm q N g p ≤ 1 :=
    source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p (hVisits _ (hBig g p))
  refine ⟨?_,?_,?_⟩
  · intro g p
    have hbp : 0<physicalSourceBaseline BP bm q N g p :=
      lt_of_lt_of_le (by norm_num) (hb g p).1
    have hp : 0<(bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    exact one_div_pos.mpr (mul_pos (mul_pos (hv.trans_le (hV g)) hp) hbp)
  · intro g
    exact (source_original_memory_physical_tilt_mass_two434 BP bm q N V g
      (hv.trans_le (hV g)) (hHarmonic g) (fun p => (hb g p).1)).2
  · intro g
    exact source_original_forest_PHYSICAL_NORMALIZED_ATOM434 BP bm q N V g (hi g)
      vmin (Real.exp (L^c)) hv (Real.exp_pos _) (hV g) (hHarmonic g) (hBig g)
      (fun p => (hb g p).1) (fun p => (hb g p).2)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestEdgeEventual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Literal complete original E row with RAW-none and ALL comparisons,
full orientation K and actual source tilt. The small/group geometry is
arbitrary subject to the original positive masses and prime floor;
no collision row, normalized atom law or analytic K bound is assumed. -/
theorem eventually_source_original_forest_SOURCE_E_PINNED434
    (c vmin q rho : ℝ) (hc : 0 < c) (hv : 0 < vmin)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
      (V : G → ℝ) (hV : ∀ g,vmin ≤ V g)
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ P g},1/(p.val:ℝ)=V g)
      (hBig : ∀ g (p : {p : ℕ // p ∈ P g}),Real.exp (L^c) ≤ (p.val:ℝ))
      (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
      (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
      (conductor : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (cap : G → ℕ)
      (Q : G → Finset (Fin (J+ell))) (pin : G → Fin (J+ell) → ℕ)
      (w : ℝ) (hw : 1 ≤ w) (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (x : FullPhysicalState SP sm (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) (J+ell) cap),
    let pat := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ
      conductor hA hB xi
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      q (2*Nat.ceil (L^(0.52:ℝ))) V
    let delta := 2/(vmin*Real.exp (L^c))
    sourceOriginalForestEPinnedRow434 SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) J ell m cap pat Q pin w q rho Vs V mu
      (memoryOrientationK _ J ell m pat K o) zeta theta o k x ≤
    delta^(∑ g,(Q g).card) *
      ((∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
          sourceOriginalMemoryRawComparisonCap434 blockA blockB m conductor xi nu)*
        (∏ g : SG,memorySmallRowConstant q (Vs g) ell)*
        (∏ g : G,w^(ell+m)*(4:ℝ)^(ell+m)*
          (memoryPromotionDampingConstant rho (ell+m)*
            ((max 1 (V g)⁻¹)^(ell+m)*(2:ℝ)^(ell+m))))) *
      w^(∑ g,(x.2 g).2.1.val) := by
  filter_upwards [eventually_source_original_forest_TILT_LAWS434 c vmin q hc hv hq.le hq1.le] with L hL
  intro SG instSG instDSG SP instSP instDSP sm instSM G instG instDG P instP
    V hV hHarmonic hBig Vs hVs blockA blockB J ell m hmJ conductor hA hB xi
    hhA hhB hxi cap Q pin w hw zeta theta o k ho x
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm := fun (g : G) (p : BP g) => p.val
  let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
  let delta := 2/(vmin*Real.exp (L^c))
  obtain ⟨hmu,hmass,hAtom⟩ := hL BP bm V (fun g => Subtype.val_injective) hV hHarmonic hBig
  have hd : 0 ≤ delta := by dsimp [delta];positivity
  have ha (g : G) (v : ℕ) :
      (∑ p : BP g,if bm g p=v then mu g p else 0) ≤ delta*2 :=
    (hAtom g v).trans (mul_le_mul_of_nonneg_left (hmass g) hd)
  let pat := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ
    conductor hA hB xi
  have hK : ∀ nu aux s t,‖memoryOrientationK BP J ell m pat K o nu aux s t‖ ≤
      sourceOriginalMemoryRawComparisonCap434 blockA blockB m conductor xi nu := by
    intro nu aux s t
    unfold memoryOrientationK
    split_ifs
    · exact source_original_memory_RAW_COMPARISON_K_cap434 P V blockA blockB J ell m hmJ
        conductor hA hB xi hhA hhB hxi nu aux s t
    · exact source_original_memory_RAW_COMPARISON_K_cap434 P V blockA blockB J ell m hmJ
        conductor hA hB xi hhA hhB hxi nu aux t s
  exact source_original_forest_E_PINNED_FULL_ROW434 SP sm BP bm J ell m cap pat Q pin
    w delta 2 q rho hw hd (by norm_num) hq hq1 hr hr1 Vs V hVs
    (fun g => hv.trans_le (hV g)) mu (fun g p => (hmu g p).le) hmass ha hHarmonic
    (memoryOrientationK BP J ell m pat K o)
    (sourceOriginalMemoryRawComparisonCap434 blockA blockB m conductor xi)
    (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m conductor xi)
    hK zeta theta o k ho x
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealAbsoluteCap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- An absolute bilinear cap for the ACTUAL full frozen family. Auxiliary
and two-endpoint permutation measures have total one for each pattern.
The only size input is the pointwise cap on K; repeated prime labels,
joint phases and the actual auxiliary ban are retained. -/
theorem source_original_unfiltered_ideal_FROZEN_ABSOLUTE_CAP434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (J ell m : ℕ) (hmJ : m ≤ J)
    {Nu : Type} [Fintype Nu] [DecidableEq Nu]
    (patterns : Nu → SourcePattern G J m)
    (hshape : ∀ nu, ∃ p : SourceOriginalProbePattern434 G m,
      patterns nu = sourceOriginalProbeMemoryPattern434 J m hmJ p)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hnorm : ∀ g,∑ p : BP g,mu g p=1)
    (V : G → ℝ) (hV : ∀ g,0 < V g)
    (hVeq : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (K : SourcePatternK BP J ell m patterns)
    (C : Nu → ℝ) (hC : ∀ nu,0 ≤ C nu)
    (hK : ∀ nu aux s t, ‖K nu aux s t‖ ≤ C nu)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F H : SourceOriginalB26Active434 BP J ell → ℂ) :
    ‖(∑ s,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*star (F s)*
      sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V K
        dsmall zeta theta o k H s)‖^2 ≤
    (∑ nu,C nu)^2*sourceOriginalB26ActiveEnergy434 BP J ell mu F*
      sourceOriginalB26ActiveEnergy434 BP J ell mu H := by
  let Active := SourceOriginalB26Active434 BP J ell
  let Frame := SourceOriginalB26FrozenFrame434 BP J ell m patterns
  let w := fun h : Frame =>
    ‖(sourceAuxMass BP bm J m V (patterns h.1) h.2.1:ℂ)*
      (bigEndpointPairMass (BG := G) (J+ell):ℂ)‖
  let kap := fun (h : Frame) (s t : Active) =>
    if (o=1 ∨ o= -1) ∧ k≠0 ∧
        sourceOriginalB26FrozenAuxBan434 BP J ell m (patterns h.1) h.2.1 s t then
      originalEdgeScalar
        (K h.1 h.2.1 (fun g i => s g (h.2.2.1 g i)) (fun g i => t g (h.2.2.2 g i)))
        zeta theta (sourceOriginalB26FrozenD434 BP bm J ell m dsmall
          (patterns h.1) h.2.1 s h.2.2.1) o k
    else 0
  let z := fun h : Frame => ∑ s : Active,∑ t : Active,
    ((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu (patterns h.1)
        s t h.2.2.1 h.2.2.2*(star (F s)*H t*kap h s t)
  let EF := sourceOriginalB26ActiveEnergy434 BP J ell mu F
  let EH := sourceOriginalB26ActiveEnergy434 BP J ell mu H
  have hEF : 0 ≤ EF := Finset.sum_nonneg (fun s _ =>
    mul_nonneg (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g _)))
      (sq_nonneg _))
  have hEH : 0 ≤ EH := Finset.sum_nonneg (fun s _ =>
    mul_nonneg (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g _)))
      (sq_nonneg _))
  have hw (h : Frame) : 0 ≤ w h := norm_nonneg _
  have hwC (h : Frame) :
      (w h:ℂ)=(sourceAuxMass BP bm J m V (patterns h.1) h.2.1:ℂ)*
        (bigEndpointPairMass (BG := G) (J+ell):ℂ) := by
    have hPm : 0 ≤ bigEndpointPairMass (BG := G) (J+ell) :=
      (groupPermutationPairMass_positive (G := G) (J+ell)).le
    dsimp only [w]
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (source_original_memory_aux_mass_nonneg434
        BP bm J m V hV (patterns h.1) h.2.1),
      abs_of_nonneg hPm]
    push_cast
    rfl
  have hsum (T : Nu → ℝ) : (∑ h : Frame,w h*T h.1)=∑ nu,T nu := by
    simp only [Frame,SourceOriginalB26FrozenFrame434,Fintype.sum_sigma,
      Fintype.sum_prod_type,w]
    apply Finset.sum_congr rfl
    intro nu _
    simp_rw [← Finset.sum_mul]
    rw [source_original_memory_BIG_AUX_total_mass434 BP bm J ell m V hV hVeq]
    exact one_mul _
  have hkap (h : Frame) (s t : Active) : ‖kap h s t‖ ≤ C h.1 := by
    dsimp only [kap]
    split_ifs with hg
    · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k hg.1]
      exact hK _ _ _ _
    · simpa only [norm_zero] using hC h.1
  have hz (h : Frame) : ‖z h‖^2 ≤ (1:ℝ)*(C h.1*EF)*(C h.1*EH) := by
    obtain ⟨p,hp⟩ := hshape h.1
    have hb := source_original_B26_permuted_uniform_bilinear434
      BP J ell m hmJ p mu hmu hnorm h.2.2.1 h.2.2.2
      (C h.1) (hC h.1) F H (kap h) (hkap h)
    rw [← hp] at hb
    change ‖z h‖^2 ≤ _ at hb
    calc
      _ ≤ (C h.1)^2*EF*EH := hb
      _ = _ := by ring
  have hh := source_original_B26_homogeneous_shared_integration434
    w (fun h => C h.1*EF) (fun h => C h.1*EH) z 1 hw
    (fun h => mul_nonneg (hC h.1) hEF)
    (fun h => mul_nonneg (hC h.1) hEH) zero_le_one hz
  have hleft :
      (∑ s,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*star (F s)*
        sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V K
          dsmall zeta theta o k H s) =
      ∑ h : Frame,(w h:ℂ)*z h := by
    unfold sourceOriginalB26FrozenBigBlock434
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    dsimp only [z]
    rw [hwC]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    unfold sourceOriginalB26FrozenBigWeight434
    dsimp only [kap]
    split_ifs <;> ring
  rw [hleft]
  have hEFsum : (∑ h : Frame,w h*(C h.1*EF))=(∑ nu,C nu)*EF := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul,hsum]
  have hEHsum : (∑ h : Frame,w h*(C h.1*EH))=(∑ nu,C nu)*EH := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul,hsum]
  rw [hEFsum,hEHsum] at hh
  change _ ≤ (∑ nu,C nu)^2*EF*EH
  nlinarith only [hh]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealCap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Enlarge only the combinatorial cap, after choosing the probe order. -/
def sourceOriginalUnfilteredIdealCap434 (cfg : SourceComparisonFixed434) (m : ℕ) :
    SourceComparisonFixed434 := { cfg with tmax := max cfg.tmax m }

/-- Transport original source data without changing any alphabet, harmonic
mass, endpoint, or numerical datum. Only three cap proofs are weakened. -/
def sourceOriginalUnfilteredIdealData434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime) (m : ℕ) :
    SourceComparisonData434 ι G (sourceOriginalUnfilteredIdealCap434 cfg m) x L Y Hprime where
  Z := data.Z
  hY := data.hY
  hYmax := data.hYmax
  hH := data.hH
  hYstrong := data.hYstrong
  hZ := data.hZ
  hYIdent := data.hYIdent
  hSmallGroups := data.hSmallGroups
  hBigGroups := data.hBigGroups
  lo := data.lo
  hi := data.hi
  Ncap := data.Ncap
  alpha := data.alpha
  hNcap := data.hNcap
  hCap := data.hCap
  hAlpha := data.hAlpha
  G := data.G
  Ptw := data.Ptw
  S := data.S
  primeSlot := data.primeSlot
  Ts := data.Ts
  Tb := data.Tb
  Vs := data.Vs
  Vsmall := data.Vsmall
  Vbig := data.Vbig
  ts := data.ts
  tb := data.tb
  coef := data.coef
  k := data.k
  qBase := data.qBase
  c := data.c
  chi0 := data.chi0
  hBase := data.hBase
  hBaseCap := data.hBaseCap
  hk := data.hk.trans (le_max_left _ _)
  hVs := data.hVs
  hts := fun g => (data.hts g).trans (le_max_left _ _)
  htb := fun g => (data.htb g).trans (le_max_left _ _)
  hVsmall := data.hVsmall
  hVbig := data.hVbig
  hcoef := data.hcoef
  C := data.C
  hC := data.hC
  hCBudget := data.hCBudget
  hcBound := data.hcBound
  sigma0 := data.sigma0
  sigma1 := data.sigma1
  hSigma0 := data.hSigma0
  hSigma1 := data.hSigma1
  hModScale := data.hModScale
  hSG := data.hSG
  hSPrime := data.hSPrime
  hSN := data.hSN
  hPN := data.hPN
  hRough := data.hRough
  hGroup := data.hGroup
  hLong := data.hLong
  I := data.I
  hI := data.hI
  hSmall := data.hSmall
  hSlot := data.hSlot
  hIBand := data.hIBand
  F1 := data.F1
  F2 := data.F2
  p1 := data.p1
  p2 := data.p2
  U1 := data.U1
  U2 := data.U2
  hF1 := data.hF1
  hF2 := data.hF2
  hp1 := data.hp1
  hp2 := data.hp2
  hmin1 := data.hmin1
  hmin2 := data.hmin2
  hU1 := data.hU1
  hU2 := data.hU2
  hcell1 := data.hcell1
  hcell2 := data.hcell2
  hHIdent := data.hHIdent
  psi1 := data.psi1
  hSmooth := data.hSmooth
  hSupport := data.hSupport
  v1 := data.v1
  hv1 := data.hv1
  hBudget := data.hBudget
  hG := data.hG
  hParity := data.hParity
  hTsPrime := data.hTsPrime
  hTbPrime := data.hTbPrime
  hOrigW := data.hOrigW
  hOrigSmall := data.hOrigSmall
  hOrigLong := data.hOrigLong
  hSlotMin := data.hSlotMin
  hHband := data.hHband
  hArcCap := data.hArcCap
  hDisjS := data.hDisjS
  hDisjB := data.hDisjB

/-- The chosen probe order is now within the cap. -/
theorem source_original_unfiltered_ideal_cap_contains434
    (cfg : SourceComparisonFixed434) (m : ℕ) :
    m ≤ (sourceOriginalUnfilteredIdealCap434 cfg m).tmax := le_max_right _ _

/-- Transport preserves the literal full endpoint, not merely its bound. -/
theorem source_original_unfiltered_ideal_endpoint_unchanged434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime) (m : ℕ) :
    (sourceOriginalUnfilteredIdealData434 data m).endpoint = data.endpoint := rfl

/-- All original prime alphabets and harmonic masses are literally unchanged. -/
theorem source_original_unfiltered_ideal_alphabets_masses_unchanged434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime) (m : ℕ) :
    (sourceOriginalUnfilteredIdealData434 data m).Tb = data.Tb ∧
    (sourceOriginalUnfilteredIdealData434 data m).Ts = data.Ts ∧
    (sourceOriginalUnfilteredIdealData434 data m).S = data.S ∧
    (sourceOriginalUnfilteredIdealData434 data m).Vbig = data.Vbig ∧
    (sourceOriginalUnfilteredIdealData434 data m).Vsmall = data.Vsmall ∧
    (sourceOriginalUnfilteredIdealData434 data m).Vs = data.Vs := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealCommonDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- ONE endpoint multiplier for every pattern and every endpoint permutation. -/
def sourceOriginalUnfilteredIdealCommonDensity434
    {G : Type} [Fintype G] (BP : G → Type) (M : ℕ)
    (r : (g : G) → BP g → ℝ) (s : (g : G) → Fin M → BP g) : ℝ :=
  ∏ g, ∏ i, r g (s g i)

/-- The remaining frame multiplier after the common change of density.
Only the genuinely free coordinates enter this expression. -/
def sourceOriginalUnfilteredIdealFreeRatio434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) (J ell m : ℕ) (pat : SourcePattern G J m)
    (r : (g : G) → BP g → ℝ)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) : ℝ :=
  ∏ g, ∏ i : Fin (J+ell),
    if i ∈ sourceBigShared J ell m pat g then 1
    else r g (s g (sigma g i))*r g (t g (tau g i))

/-- Exact common-unitary joint density, valid on and off shared-copy support.
The endpoint multiplier is independent of the pattern. No phase or K
is commuted through a conditional expectation. -/
theorem source_original_unfiltered_ideal_COMMON_DENSITY434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (J ell m : ℕ) (pat : SourcePattern G J m)
    (mu r : (g : G) → BP g → ℝ)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    ((∏ g,∏ i,mu g (s g i)*(r g (s g i))^2 : ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m
        (fun g p => mu g p*(r g p)^2) pat s t sigma tau =
    ((∏ g,∏ i,mu g (s g i) : ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau *
      (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ) *
      (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r t:ℂ) *
      (sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m pat r s t sigma tau:ℂ) := by
  rw [source_original_B26_fresh_law_permuted434 BP J ell m pat
    (fun g p => mu g p*(r g p)^2) s t sigma tau,
    source_original_B26_fresh_law_permuted434 BP J ell m pat mu s t sigma tau]
  unfold sourceOriginalUnfilteredIdealCommonDensity434
  rw [← source_original_B26_endpoint_permutation_mass434 BP (J+ell)
    (fun g p => mu g p*(r g p)^2) s sigma,
    ← source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu s sigma,
    ← source_original_B26_endpoint_permutation_mass434 BP (J+ell) r s sigma,
    ← source_original_B26_endpoint_permutation_mass434 BP (J+ell) r t tau]
  unfold sourceOriginalB26FrozenFreshLaw434 sourceOriginalUnfilteredIdealFreeRatio434
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  push_cast
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ sourceBigShared J ell m pat g
  · by_cases he : t g (tau g i)=s g (sigma g i)
    · simp only [hi,if_pos,he,Complex.ofReal_one]; ring
    · simp [hi,he]
  · simp only [hi,if_false,Complex.ofReal_pow,Complex.ofReal_mul]; ring

/-- The common multiplier is an exact energy isometry, with no pattern
or permutation dependence and no loss proportional to the Fock size. -/
theorem source_original_unfiltered_ideal_COMMON_ENERGY434
    {G : Type} [Fintype G]
    (BP : G → Type) [∀ g,Fintype (BP g)] (J ell : ℕ)
    (mu r : (g : G) → BP g → ℝ)
    (F : ((g : G) → Fin (J+ell) → BP g) → ℂ) :
    sourceOriginalB26ActiveEnergy434 BP J ell mu
      (fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s) =
    sourceOriginalB26ActiveEnergy434 BP J ell (fun g p => mu g p*(r g p)^2) F := by
  unfold sourceOriginalB26ActiveEnergy434 sourceOriginalUnfilteredIdealCommonDensity434
  apply Finset.sum_congr rfl
  intro s _
  rw [norm_mul,mul_pow,Complex.sq_norm]
  simp only [Complex.normSq_ofReal,Finset.prod_mul_distrib,Finset.prod_pow]
  ring

/-- Instantiation with the actual physical baseline and tilted prime law. -/
theorem source_original_unfiltered_ideal_PHYSICAL_COMMON_DENSITY434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ)
    (hb : ∀ g p,0 < physicalSourceBaseline BP modulus q N g p)
    (J ell m : ℕ) (pat : SourcePattern G J m)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    let mu := sourceOriginalJointHarmonicMu434 BP modulus V
    let nu := physicalSourceMuTilde BP modulus q N V
    let r := sourceOriginalB26PhysicalTiltRoot434 BP modulus q N
    ((∏ g,∏ i,nu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m nu pat s t sigma tau =
    ((∏ g,∏ i,mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau *
      (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ) *
      (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r t:ℂ) *
      (sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m pat r s t sigma tau:ℂ) := by
  dsimp only
  have he : physicalSourceMuTilde BP modulus q N V =
      (fun g p => sourceOriginalJointHarmonicMu434 BP modulus V g p *
        (sourceOriginalB26PhysicalTiltRoot434 BP modulus q N g p)^2) := by
    funext g p
    exact source_original_B26_PHYSICAL_TILT_ATOM434 BP modulus q N V g p (hb g p)
  rw [he]
  exact source_original_unfiltered_ideal_COMMON_DENSITY434 BP J ell m pat _ _ s t sigma tau

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealEndpointMean -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The simultaneous mean over the ACTUAL full family of independent endpoint
slot permutations. It allows arbitrary inter-group correlations in the test. -/
def sourceOriginalUnfilteredIdealEndpointMean434
    {G : Type} [Fintype G] [DecidableEq G] (BP : G → Type) (M : ℕ)
    (f : ((g : G) → Fin M → BP g) → ℂ)
    (x : (g : G) → Fin M → BP g) : ℂ :=
  (Fintype.card (BigGroupPerm (BG := G) M) : ℂ)⁻¹ *
    ∑ sigma : BigGroupPerm (BG := G) M, f (fun g i => x g (sigma g i))

/-- Relabeling one group permutes the original full permutation ensemble. -/
def sourceOriginalUnfilteredIdealPermShift434
    {G : Type} [DecidableEq G] (M : ℕ) (g : G) (tau : Equiv.Perm (Fin M)) :
    BigGroupPerm (BG := G) M ≃ BigGroupPerm (BG := G) M where
  toFun sigma := Function.update sigma g ((sigma g).trans tau)
  invFun sigma := Function.update sigma g ((sigma g).trans tau.symm)
  left_inv sigma := by
    funext h
    by_cases hh : h = g
    · subst h
      ext i
      simp [Equiv.trans_apply]
    · simp [Function.update_of_ne hh]
  right_inv sigma := by
    funext h
    by_cases hh : h = g
    · subst h
      ext i
      simp [Equiv.trans_apply]
    · simp [Function.update_of_ne hh]

theorem source_original_unfiltered_ideal_endpoint_mean_invariant434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) (M : ℕ)
    (f : ((g : G) → Fin M → BP g) → ℂ)
    (g : G) (tau : Equiv.Perm (Fin M))
    (x : (g : G) → Fin M → BP g) :
    sourceOriginalUnfilteredIdealEndpointMean434 BP M f
      (sourceOriginalJointGroupRelabel434 BP g tau x) =
      sourceOriginalUnfilteredIdealEndpointMean434 BP M f x := by
  unfold sourceOriginalUnfilteredIdealEndpointMean434
  congr 1
  apply Fintype.sum_equiv (sourceOriginalUnfilteredIdealPermShift434 M g tau)
  intro sigma
  congr 1
  funext h i
  by_cases hh : h = g
  · subst h
    simp [sourceOriginalJointGroupRelabel434,
      sourceOriginalUnfilteredIdealPermShift434, Equiv.trans_apply]
  · simp [sourceOriginalJointGroupRelabel434,
      sourceOriginalUnfilteredIdealPermShift434, Function.update_of_ne hh]

theorem source_original_unfiltered_ideal_endpoint_permutation_energy434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (sigma : BigGroupPerm (BG := G) M) :
    sourceOriginalJointBigEnergy434 BP mu (fun x => f (fun g i => x g (sigma g i))) =
      sourceOriginalJointBigEnergy434 BP mu f := by
  unfold sourceOriginalJointBigEnergy434
  apply Fintype.sum_equiv (sourceOriginalB26EndpointPermutationEquiv434 BP M sigma)
  intro x
  congr 1
  exact (source_original_B26_endpoint_permutation_mass434 BP M mu x sigma).symm

/-- The actual simultaneous endpoint mean is contractive in the original
joint harmonic/product density, with no factorial loss. -/
theorem source_original_unfiltered_ideal_endpoint_mean_contract434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p, 0 ≤ mu g p)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP mu (sourceOriginalUnfilteredIdealEndpointMean434 BP M f) ≤
      sourceOriginalJointBigEnergy434 BP mu f := by
  let n : ℝ := Fintype.card (BigGroupPerm (BG := G) M)
  have hn : n ≠ 0 := by
    dsimp only [n]
    exact_mod_cast Fintype.card_ne_zero (α := BigGroupPerm (BG := G) M)
  have hp (x : SourceOriginalJointBigState434 BP M) :
      Complex.normSq (sourceOriginalUnfilteredIdealEndpointMean434 BP M f x) ≤
        n⁻¹ * ∑ sigma : BigGroupPerm (BG := G) M,
          Complex.normSq (f (fun g i => x g (sigma g i))) :=
    source_original_finite_complex_average_normSq434
      (fun sigma : BigGroupPerm (BG := G) M => f (fun g i => x g (sigma g i)))
  calc
    _ ≤ ∑ x : SourceOriginalJointBigState434 BP M,
        sourceOriginalJointBigMass434 BP mu x *
          (n⁻¹ * ∑ sigma : BigGroupPerm (BG := G) M,
            Complex.normSq (f (fun g i => x g (sigma g i)))) := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left (hp x)
      exact Finset.prod_nonneg (fun g _ =>
        source_original_big_product_mass_nonneg434 (mu g) (hmu g) (x g))
    _ = n⁻¹ * ∑ sigma : BigGroupPerm (BG := G) M,
        sourceOriginalJointBigEnergy434 BP mu (fun x => f (fun g i => x g (sigma g i))) := by
      simp only [sourceOriginalJointBigEnergy434, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sigma hsigma
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = n⁻¹ * (n * sourceOriginalJointBigEnergy434 BP mu f) := by
      simp only [source_original_unfiltered_ideal_endpoint_permutation_energy434,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n]
    _ = _ := by field_simp

/-- Quantitative harmonic coordinate gain for the TRUE simultaneous original
endpoint mean, not a postulated symmetric input or a factored test.
Only the original block cardinality and normalized harmonic data enter. -/
theorem source_original_unfiltered_ideal_ACTUAL_MEAN_COORDINATE_LOG434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g) (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    {M : ℕ} (probes trailing : G → Finset (Fin M))
    (hd : ∀ g, Disjoint (probes g) (trailing g))
    (gs : List G) (hgs : gs.Nodup) (m ell : ℕ)
    (hcard : ∀ g ∈ gs, (probes g).card = m ∧ (trailing g).card = ell)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcount : c*Real.log LL ≤ (gs.length:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP (sourceOriginalJointHarmonicMu434 BP prime V)
      (sourceOriginalUnfilteredIdealGroups434 BP (sourceOriginalJointHarmonicMu434 BP prime V)
        probes trailing gs (sourceOriginalUnfilteredIdealEndpointMean434 BP M f)) ≤
      LL^(-A) * sourceOriginalJointBigEnergy434 BP (sourceOriginalJointHarmonicMu434 BP prime V) f := by
  obtain ⟨hpos, hnorm⟩ := source_original_joint_harmonic_normalized434 BP prime V hV hEq
  rw [source_original_unfiltered_ideal_groups_survivor434 BP _ hnorm _ _ hd]
  have h := source_original_joint_harmonic_big_log_power434 BP prime V hV hEq
    probes trailing hd gs hgs m ell hcard LL A c hLL hc hm hell hcount hbudget
    (sourceOriginalUnfilteredIdealEndpointMean434 BP M f)
    (fun g _ tau x => source_original_unfiltered_ideal_endpoint_mean_invariant434 BP M f g tau x)
  have hc' := source_original_unfiltered_ideal_endpoint_mean_contract434 BP M
    (sourceOriginalJointHarmonicMu434 BP prime V) hpos f
  have hpow : 0 < LL^A := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (le_trans (by norm_num) hLL)]
  calc
    _ ≤ sourceOriginalJointBigEnergy434 BP (sourceOriginalJointHarmonicMu434 BP prime V) f /
        LL^A := (le_div_iff₀ hpow).mpr (h.trans hc')
    _ = _ := by ring

end Green64Analytic.CorrelationSquare

end

end

