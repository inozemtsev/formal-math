module

public import Green64.Library.Sieve.Foundations.Part053
public import Green64.Library.Sieve.Foundations.Part006
public import Green64.Library.Weights.Part037
public import Green64.Library.Sieve.Foundations.PresieveBlocks
public import Green64.Library.Weights.Part108
public import Green64.Library.Sieve.Foundations.Part001

@[expose] public section

/-!
# Sieve / Foundations / Part054

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalPresieveAsymptotic -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
open Green64Analytic.SmallB
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- An absolute constant from the actual shifted C=8 block sieve. -/
def parityOriginalPresieveExponentialConstant434 : ℝ := 3*parityOriginalPresieveRho434 0

theorem parity_original_presieve_exponential_constant_pos434 :
    0<parityOriginalPresieveExponentialConstant434 := by
  have hDen : 0<1-Real.exp (-1) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  unfold parityOriginalPresieveExponentialConstant434
  rw [parity_original_presieve_rho_exact434]
  positivity

/-- The source loss retains its exponential dependence on beta, with an
absolute actual shifted-sieve constant fixed before beta and kappa. -/
theorem parity_original_presieve_source_depth_exponential_loss434
    (beta : ℝ) (hBeta : 0<beta) (hSmall : beta≤1/1000) :
    parityOriginalPresieveRho434 (sourceDepth beta)*
      Real.exp (parityOriginalPresieveRho434 (sourceDepth beta)) ≤
      parityOriginalPresieveExponentialConstant434*Real.exp (-(1/(40*beta))) := by
  have hDepth := sourceDepth_budget beta hBeta (by linarith)
  have hRho := parity_original_presieve_rho_small434 (sourceDepth beta)
    (parity_original_presieve_source_depth_ge_fifty434 beta hBeta hSmall)
  have hExp : Real.exp (parityOriginalPresieveRho434 (sourceDepth beta))≤3 :=
    (Real.exp_le_exp.mpr (hRho.2.1.trans (by norm_num))).trans Real.exp_one_lt_three.le
  have hDecay : Real.exp (-(sourceDepth beta:ℝ))≤Real.exp (-(1/(40*beta))) :=
    Real.exp_le_exp.mpr (neg_le_neg hDepth.2.2.1)
  have hRhoEq : parityOriginalPresieveRho434 (sourceDepth beta)=
      parityOriginalPresieveRho434 0*Real.exp (-(sourceDepth beta:ℝ)) := by
    simp only [parityOriginalPresieveRho434,Nat.cast_zero,neg_zero,Real.exp_zero,mul_one]
  calc
    _ ≤ 3*parityOriginalPresieveRho434 (sourceDepth beta) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hExp hRho.1.le
    _ = parityOriginalPresieveExponentialConstant434*Real.exp (-(sourceDepth beta:ℝ)) := by
      rw [hRhoEq]
      unfold parityOriginalPresieveExponentialConstant434
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hDecay
      parity_original_presieve_exponential_constant_pos434.le

/-- The precise negative-parity initial-presieve main coefficient: the
actual singular series and the full explicit truncation loss are retained.
The auxiliary distribution level 1/2-kappa is admissible; it need not equal
the manuscript's larger fixed theta=1/2-kappa/2. -/
theorem parity_original_negative_presieve_singular_lower434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (beta kappa eps : ℝ) (hBeta : 0<beta) (hSmall : beta≤1/1000)
    (hKappa : 0<kappa) (hKappaUpper : kappa<1/50) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,
      (singularSeries*Real.exp (-Real.eulerMascheroniConstant)/beta*
        (1-parityOriginalPresieveRho434 (sourceDepth beta)*
          Real.exp (parityOriginalPresieveRho434 (sourceDepth beta)))-eps)*
          localizedMass Psi (-1) L/L ≤
        parityOriginalRoughMass434 Psi (-1) beta L := by
  let c := singularSeries*Real.exp (-Real.eulerMascheroniConstant)/beta
  let rho := parityOriginalPresieveRho434 (sourceDepth beta)
  let q := 1-rho*Real.exp rho
  have hRho := parity_original_presieve_rho_small434 (sourceDepth beta)
    (parity_original_presieve_source_depth_ge_fifty434 beta hBeta hSmall)
  have hqNonneg : 0≤q := (by norm_num : (0:ℝ)≤3/4).trans hRho.2.2
  have hqUpper : q≤1 := by
    have hPos := mul_nonneg hRho.1.le (Real.exp_pos rho).le
    dsimp [q]
    linarith
  have hVLower := (tendsto_order.mp
    (parity_original_shifted_euler_power_mertens434 beta hBeta)).1
      (c-eps/2) (by dsimp [c];linarith)
  have hSieve := parity_original_negative_full_rough_source_depth434
    Psi hSmooth hSupport hNonneg hInterior beta kappa (eps/2)
    hBeta (by linarith) hKappa hKappaUpper (by positivity)
  filter_upwards [hVLower,hSieve,eventually_gt_atTop (0:ℝ)] with L hV hS hL
  let X := localizedMass Psi (-1) L
  let V := parityOriginalShiftedEuler434 ((Real.exp L)^beta)
  have hX : 0≤X := by
    dsimp only [X]
    rw [parity_original_minus_Xrho_eq_original_XA434]
    exact source_original_XA_nonneg _ _ _ _ _ hNonneg
  have hCoef : c*q-eps/2≤(L*V)*q := by
    have hMult := mul_le_mul_of_nonneg_right hV.le hqNonneg
    have hLeft : c*q-eps/2≤(c-eps/2)*q := by nlinarith
    exact hLeft.trans hMult
  have hMain := mul_le_mul_of_nonneg_right hCoef (div_nonneg hX hL.le)
  change (c*q-eps)*X/L≤_
  calc
    _ = (c*q-eps/2)*(X/L)-(eps/2)*X/L := by ring
    _ ≤ (L*V*q)*(X/L)-(eps/2)*X/L := _root_.sub_le_sub hMain (le_refl _)
    _ = X*V*q-(eps/2)*X/L := by field_simp [ne_of_gt hL]
    _ ≤ _ := hS.1

/-- Parity (8.1) for the genuine h=-2,rho=-1 source, with the actual singular
multiplier and an explicit universal exponential defect. The epsilon form
states the full relative o(1); it assumes no sieve, mass or Mertens conclusion. -/
theorem parity_original_negative_initial_presieve_8_1_434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (beta kappa eps : ℝ) (hBeta : 0<beta) (hSmall : beta≤1/1000)
    (hKappa : 0<kappa) (hKappaUpper : kappa<1/50) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,
      (singularSeries*Real.exp (-Real.eulerMascheroniConstant)/beta*
        (1-parityOriginalPresieveExponentialConstant434*Real.exp (-(1/(40*beta))))-eps)*
          localizedMass Psi (-1) L/L ≤
        parityOriginalRoughMass434 Psi (-1) beta L := by
  have hLoss := parity_original_presieve_source_depth_exponential_loss434 beta hBeta hSmall
  have hSPos : 0<singularSeries :=
    zero_lt_one.trans_le singularSeries_converges_and_ge_one.2
  have hc : 0≤ singularSeries*Real.exp (-Real.eulerMascheroniConstant)/beta := by
    positivity
  filter_upwards [parity_original_negative_presieve_singular_lower434
    Psi hSmooth hSupport hNonneg hInterior beta kappa eps hBeta hSmall
    hKappa hKappaUpper hEps,eventually_gt_atTop (0:ℝ)] with L hBound hL
  have hX : 0≤localizedMass Psi (-1) L := by
    rw [parity_original_minus_Xrho_eq_original_XA434]
    exact source_original_XA_nonneg _ _ _ _ _ hNonneg
  have hCoef := _root_.sub_le_sub
    (mul_le_mul_of_nonneg_left (_root_.sub_le_sub_left hLoss 1) hc) (le_refl eps)
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCoef hX) hL.le).trans hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalConditionalGrowingDepth -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- Literal Parity8.2 sieve depth. This moving sieve depth is distinct from
the fixed TypeII/proxy parameters chosen before L. -/
def parityOriginalConditionalDepth434 (L : ℝ) : ℕ := 2*⌈(Real.log L)^2⌉₊

theorem parity_original_conditional_depth_bounds434 (L : ℝ) :
    Even (parityOriginalConditionalDepth434 L) ∧
      2*(Real.log L)^2≤(parityOriginalConditionalDepth434 L:ℝ) ∧
      (parityOriginalConditionalDepth434 L:ℝ)≤2*(Real.log L)^2+2 := by
  have hlo := Nat.le_ceil ((Real.log L)^2)
  have hhi := Nat.ceil_lt_add_one (sq_nonneg (Real.log L))
  constructor
  · exact ⟨⌈(Real.log L)^2⌉₊,by dsimp [parityOriginalConditionalDepth434];omega⟩
  · simp only [parityOriginalConditionalDepth434,Nat.cast_mul,Nat.cast_ofNat]
    constructor <;> linarith

theorem parity_original_conditional_depth_tendsto434 :
    Tendsto (fun L : ℝ => (parityOriginalConditionalDepth434 L:ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 B)] with L hL
  have hOne : (1:ℝ)≤Real.log L := (le_max_left _ _).trans hL
  have hB : B≤Real.log L := (le_max_right _ _).trans hL
  have hlo := (parity_original_conditional_depth_bounds434 L).2.1
  nlinarith

/-- The actual growing-depth modulus level, uniform over every allowed
large prime and all block counts. It is not inferred from a fixed-depth lemma. -/
theorem parity_original_conditional_growing_level434
    (gamma eta theta : ℝ) (hGamma : 0<gamma) (hGap : eta<theta) :
    ∀ᶠ L : ℝ in atTop,
      2≤parityOriginalConditionalDepth434 L ∧
      2≤Real.exp (Real.sqrt L) ∧
      Real.exp (Real.sqrt L)<(Real.exp L)^gamma ∧
      (Real.exp L)^eta*(Real.exp (Real.sqrt L))^
        (4*(parityOriginalConditionalDepth434 L:ℝ)+2)≤(Real.exp L)^theta := by
  have hLog : Tendsto (fun L : ℝ => (Real.log L)^2/Real.sqrt L) atTop (𝓝 0) := by
    simpa only [Real.rpow_two,←Real.sqrt_eq_rpow] using
      (_root_.isLittleO_log_rpow_rpow_atTop (2:ℝ)
        (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hConst : Tendsto (fun L : ℝ => (10:ℝ)/Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hRatio : Tendsto (fun L : ℝ => (8*(Real.log L)^2+10)/Real.sqrt L) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using (hLog.const_mul 8).add hConst
  have hSmall := (tendsto_order.mp hRatio).2 (theta-eta) (sub_pos.mpr hGap)
  have hDepthTwo := parity_original_conditional_depth_tendsto434.eventually_ge_atTop 2
  filter_upwards [hSmall,hDepthTwo,parity_original_conditioned_subpower_level434
    gamma eta theta 0 hGamma hGap,eventually_gt_atTop (0:ℝ)] with L hSmall hTwo hW hL
  have hUpper := (parity_original_conditional_depth_bounds434 L).2.2
  have hSqrt := Real.sqrt_pos.mpr hL
  have hQuot : 8*(Real.log L)^2+10≤(theta-eta)*Real.sqrt L :=
    (div_le_iff₀ hSqrt).mp hSmall.le
  have hH : 4*(parityOriginalConditionalDepth434 L:ℝ)+2≤(theta-eta)*Real.sqrt L := by
    linarith
  have hLevel : Real.sqrt L*(4*(parityOriginalConditionalDepth434 L:ℝ)+2)≤L*(theta-eta) := by
    have hm := mul_le_mul_of_nonneg_right hH hSqrt.le
    have hs := Real.sq_sqrt hL.le
    nlinarith
  refine ⟨by exact_mod_cast hTwo,hW.1,hW.2.1,?_⟩
  rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,←Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Literal growing-depth exponential loss beats every fixed inverse power. -/
theorem parity_original_conditional_depth_anylog434 (A : ℝ) (hA : 0≤A) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-(parityOriginalConditionalDepth434 L:ℝ))≤L^(-A) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 0 (A/2)),
    eventually_gt_atTop (0:ℝ)] with L hLog hL
  have hLogZero : 0≤Real.log L := (le_max_left _ _).trans hLog
  have hLogA : A/2≤Real.log L := (le_max_right _ _).trans hLog
  have hLower := (parity_original_conditional_depth_bounds434 L).2.1
  have hExponent : -(parityOriginalConditionalDepth434 L:ℝ)≤Real.log L*(-A) := by
    have hm := mul_le_mul_of_nonneg_right hLogA hLogZero
    nlinarith
  rw [Real.rpow_def_of_pos hL]
  exact Real.exp_le_exp.mpr hExponent

theorem parity_original_conditional_rho_tendsto_zero434 :
    Tendsto (fun L : ℝ => parityOriginalPresieveRho434 (parityOriginalConditionalDepth434 L))
      atTop (𝓝 0) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp parity_original_conditional_depth_tendsto434
  simpa only [parityOriginalPresieveRho434,Function.comp_def,mul_zero] using
    he.const_mul ((Real.exp (Real.exp 1*8)/(1-Real.exp (-1)))/Real.exp (-8/(1/2)))

/-- Genuine source conditional sieve evaluated at the manuscript's moving
H(L)=2 ceil((log L)^2), with the single actual total remainder. -/
theorem parity_original_negative_growing_conditional_sieve434
    (Psi : ℝ → ℝ) (hNonneg : ∀ t,0≤Psi t)
    (gamma eta theta : ℝ) (hGamma : 0<gamma) (hGap : eta<theta) :
    ∀ᶠ L : ℝ in atTop,∀ S : Finset ℕ,
      (∀ p∈S,p.Prime ∧ (Real.exp L)^gamma<(p:ℝ) ∧ (p:ℝ)≤(Real.exp L)^eta) →
      let W := Real.exp (Real.sqrt L)
      let X := sourceOriginalXA 20
        (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
        (sourceOriginalPAllActualBands 20 L) (Real.exp L) Psi
      let main := X*(∏ q∈sourceAllOddPrimeSet W,(1-sourceShiftTwoLocalDensity q))*
        (∑ p∈S,sourceShiftTwoLocalDensity p)
      let rho := parityOriginalPresieveRho434 (parityOriginalConditionalDepth434 L)
      main*(1-rho*Real.exp rho)-parityOriginalShiftedRemainderRange434 20 Psi L theta ≤
        (∑ p∈S,parityOriginalConditionedMass434 20 Psi L p (sourceAllOddPrimeSet W)) ∧
      (∑ p∈S,parityOriginalConditionedMass434 20 Psi L p (sourceAllOddPrimeSet W)) ≤
        main*Real.exp rho+parityOriginalShiftedRemainderRange434 20 Psi L theta := by
  filter_upwards [parity_original_conditional_growing_level434 gamma eta theta hGamma hGap]
    with L hLevel S hS
  let W := Real.exp (Real.sqrt L)
  have hW : 1<W := (by norm_num : (1:ℝ)<2).trans_le hLevel.2.1
  obtain ⟨J,hJ⟩ := source_exists_natural_halfpower_depth W hW
  let blocks := fun j : Fin J => sourceNaturalOddPrimeBlock 1 W j.val
  have hBlocks : ∀ j q,q∈blocks j → q.Prime ∧ 3≤q ∧
      W^((1/2:ℝ)^(j.val+1))<(q:ℝ) ∧ (q:ℝ)≤W^((1/2:ℝ)^j.val) := by
    intro j q hq
    have hp := source_natural_block_prime 1 W j.val q hq
    exact ⟨hp.1,source_natural_block_odd 1 W j.val q hq,hp.2⟩
  have hP : Finset.univ.biUnion blocks=sourceAllOddPrimeSet W :=
    source_natural_unit_blocks_cover_all_odd_primes J W hW hJ
  have hPrime : ∀ p∈S,p.Prime ∧ 3≤p ∧ W<(p:ℝ) ∧ (p:ℝ)≤(Real.exp L)^eta := by
    intro p hp
    have h := hS p hp
    have hWp : W<(p:ℝ) := hLevel.2.2.1.trans h.2.1
    have hTwo : (2:ℝ)<p := hLevel.2.1.trans_lt hWp
    have hThree : 3≤p := by
      have hNat : 2<p := by exact_mod_cast hTwo
      omega
    exact ⟨h.1,hThree,hWp,h.2.2⟩
  have hBound := parity_original_conditioned_sum434 20 Psi L theta W ((Real.exp L)^eta)
    J (parityOriginalConditionalDepth434 L) blocks S hW hLevel.1
    (parity_original_conditional_depth_bounds434 L).1 hNonneg hBlocks hPrime hLevel.2.2.2
  dsimp only at hBound
  rw [hP] at hBound
  exact hBound
end Green64Analytic.SourceBlockSieve

end

end

/-! ## OriginalConditionalAsymptotic -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- Every factor of the actual odd-prime Euler product is strictly positive. -/
theorem parity_original_shifted_euler_pos434 (z : ℝ) :
    0 < parityOriginalShiftedEuler434 z := by
  apply Finset.prod_pos
  intro p hp
  have hPrime := (Finset.mem_filter.mp hp).2
  have hThree := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hTot : (1:ℝ) < p.totient := by
    rw [Nat.totient_prime hPrime]
    exact_mod_cast (show 1 < p-1 by omega)
  apply sub_pos.mpr
  unfold sourceShiftTwoLocalDensity
  exact (inv_lt_one₀ (by linarith : (0:ℝ) < p.totient)).mpr hTot

/-- The actual subpower Euler product is large enough for the proved
o(X/L) congruence remainder to be negligible on X V1(W). -/
theorem parity_original_subpower_euler_inverse_scale434 :
    Tendsto (fun L : ℝ => 1/(L*parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L))))
      atTop (𝓝 0) := by
  have hS : 0 < singularSeries :=
    (by norm_num : (0:ℝ)<1).trans_le singularSeries_converges_and_ge_one.2
  have hC : singularSeries*Real.exp (-Real.eulerMascheroniConstant) ≠ 0 :=
    ne_of_gt (mul_pos hS (Real.exp_pos _))
  have hRoot : Tendsto (fun L : ℝ => (1:ℝ)/Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h := hRoot.div parity_original_shifted_euler_subpower_mertens434 hC
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have hs := Real.sqrt_pos.mpr hL
  have hV := parity_original_shifted_euler_pos434 (Real.exp (Real.sqrt L))
  have hsq := Real.sq_sqrt hL.le
  change (1/Real.sqrt L)/(Real.sqrt L*parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L))) =
    1/(L*parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L)))
  field_simp [ne_of_gt hs,ne_of_gt hL,ne_of_gt hV]
  nlinarith

end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- Literal Parity8.2 source mass, retaining the prime divisor, the full
least-prime-factor cutoff, and the original parity source weight. -/
def parityOriginalConditionalBinMass434
    (Psi : ℝ → ℝ) (rho gamma eta L : ℝ) : ℝ :=
  ∑ p∈parityOriginalPrimeBin434 gamma eta L,
    parityOriginalConditionedRoughMass434 Psi rho L (Real.exp (Real.sqrt L)) p

theorem negative_localizedMass_eventually_pos
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t) :
    ∀ᶠ L : ℝ in atTop,0<localizedMass Psi (-1) L := by
  obtain ⟨c,hc,hMass⟩ := localizedMass_lower_bound
    Psi hCont hSupport hNonneg hInterior
  filter_upwards [hMass,eventually_gt_atTop (0:ℝ)] with L hM hL
  exact (by positivity : 0<c*Real.exp L*L^(-221:ℝ)).trans_le (hM (-1) (Or.inr rfl))

/-- Actual congruence remainder divided by actual source mass times V1(W).
Neither the positive source mass nor its asymptotic scale is a hypothesis. -/
theorem parity_original_negative_congruence_over_subpower_mass434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (theta : ℝ) (hTheta : 0<theta) (hThetaUpper : theta<1/2) :
    Tendsto (fun L : ℝ => parityOriginalCongruenceTotalError434 Psi (-1) theta L /
      (localizedMass Psi (-1) L*
        parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L)))) atTop (𝓝 0) := by
  have hE := (parity_original_negative_congruence_littleO_Xrho434
    Psi hSmooth hSupport hNonneg hInterior theta hTheta hThetaUpper).tendsto_div_nhds_zero
  have h := hE.mul parity_original_subpower_euler_inverse_scale434
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [negative_localizedMass_eventually_pos
    Psi hSmooth.continuous hSupport hNonneg hInterior,
    eventually_gt_atTop (0:ℝ)] with L hX hL
  have hV := parity_original_shifted_euler_pos434 (Real.exp (Real.sqrt L))
  field_simp [ne_of_gt hX,ne_of_gt hL,ne_of_gt hV]

/-- The literal growing-depth conditional sieve on the full original
roughness mask, with exactly the source total congruence error. -/
theorem parity_original_negative_growing_full_rough434
    (Psi : ℝ → ℝ) (hNonneg : ∀ t,0≤Psi t)
    (gamma eta theta : ℝ) (hGamma : 0<gamma) (hGap : eta<theta) :
    ∀ᶠ L : ℝ in atTop,∀ S : Finset ℕ,
      (∀ p∈S,p.Prime ∧ (Real.exp L)^gamma<(p:ℝ) ∧ (p:ℝ)≤(Real.exp L)^eta) →
      let W := Real.exp (Real.sqrt L)
      let X := localizedMass Psi (-1) L
      let main := X*parityOriginalShiftedEuler434 W*(∑ p∈S,sourceShiftTwoLocalDensity p)
      let rho := parityOriginalPresieveRho434 (parityOriginalConditionalDepth434 L)
      main*(1-rho*Real.exp rho)-parityOriginalCongruenceTotalError434 Psi (-1) theta L ≤
        (∑ p∈S,parityOriginalConditionedRoughMass434 Psi (-1) L W p) ∧
      (∑ p∈S,parityOriginalConditionedRoughMass434 Psi (-1) L W p) ≤
        main*Real.exp rho+parityOriginalCongruenceTotalError434 Psi (-1) theta L := by
  filter_upwards [parity_original_negative_growing_conditional_sieve434
    Psi hNonneg gamma eta theta hGamma hGap,
    parity_original_negative_conditioned_rough_eq434 Psi] with L hSieve hEq S hS
  have h := hSieve S hS
  simpa only [parity_original_minus_Xrho_eq_original_XA434,
    hEq (Real.exp (Real.sqrt L)) (Real.exp_pos _).le,
    parityOriginalShiftedEuler434,parityOriginalCongruenceTotalError434,
    parity_original_negative_congruence_remainder_eq434,
    parityOriginalShiftedRemainderRange434] using h

/-- Parity8.2 for the original h=-2 negative-parity source: the actual
prime-conditioned W-rough mass is asymptotic to Xminus V1(W) log(eta/gamma).
The proof uses the manuscript's H(L), actual modulus injection, native
Mertens, and the proved original mass lower bound. No distribution,
positive-mass, proxy identity, or desired asymptotic is assumed. -/
theorem parity_original_negative_conditional_sieve_8_2_434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (gamma eta theta : ℝ) (hGamma : 0<gamma) (hOrder : gamma<eta)
    (hGap : eta<theta) (hThetaUpper : theta<1/2) :
    Tendsto (fun L : ℝ => parityOriginalConditionalBinMass434 Psi (-1) gamma eta L /
      (localizedMass Psi (-1) L*
        parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L))))
      atTop (𝓝 (Real.log (eta/gamma))) := by
  let B := fun L : ℝ => ∑ p∈parityOriginalPrimeBin434 gamma eta L,sourceShiftTwoLocalDensity p
  let r := fun L : ℝ => parityOriginalPresieveRho434 (parityOriginalConditionalDepth434 L)
  let Z := fun L : ℝ => localizedMass Psi (-1) L*
    parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L))
  let E := fun L : ℝ => parityOriginalCongruenceTotalError434 Psi (-1) theta L
  let F := fun L : ℝ => parityOriginalConditionalBinMass434 Psi (-1) gamma eta L
  have hB : Tendsto B atTop (𝓝 (Real.log (eta/gamma))) :=
    parity_original_prime_bin_local_density_tendsto434 gamma eta hGamma hOrder
  have hr : Tendsto r atTop (𝓝 0) := parity_original_conditional_rho_tendsto_zero434
  have hexp : Tendsto (fun L => Real.exp (r L)) atTop (𝓝 1) := by
    simpa only [Real.exp_zero,Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hr
  have hLoss : Tendsto (fun L => 1-r L*Real.exp (r L)) atTop (𝓝 1) := by
    simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (hr.mul hexp)
  have hE : Tendsto (fun L => E L/Z L) atTop (𝓝 0) :=
    parity_original_negative_congruence_over_subpower_mass434
      Psi hSmooth hSupport hNonneg hInterior theta (hGamma.trans (hOrder.trans hGap)) hThetaUpper
  have hLow : Tendsto (fun L => B L*(1-r L*Real.exp (r L))-E L/Z L)
      atTop (𝓝 (Real.log (eta/gamma))) := by
    simpa only [mul_one,sub_zero] using (hB.mul hLoss).sub hE
  have hHigh : Tendsto (fun L => B L*Real.exp (r L)+E L/Z L)
      atTop (𝓝 (Real.log (eta/gamma))) := by
    simpa only [mul_one,add_zero] using (hB.mul hexp).add hE
  have hBounds : ∀ᶠ L : ℝ in atTop,
      B L*(1-r L*Real.exp (r L))-E L/Z L≤F L/Z L ∧
      F L/Z L≤B L*Real.exp (r L)+E L/Z L := by
    filter_upwards [parity_original_negative_growing_full_rough434
      Psi hNonneg gamma eta theta hGamma hGap,
      negative_localizedMass_eventually_pos
        Psi hSmooth.continuous hSupport hNonneg hInterior] with L hSieve hX
    have hz : 0<Z L := mul_pos hX (parity_original_shifted_euler_pos434 _)
    have h := hSieve (parityOriginalPrimeBin434 gamma eta L)
      (fun p hp => (parity_original_prime_bin_mem434 gamma eta L p).mp hp)
    change Z L*B L*(1-r L*Real.exp (r L))-E L≤F L ∧
      F L≤Z L*B L*Real.exp (r L)+E L at h
    constructor
    · have hl := div_le_div_of_nonneg_right h.1 hz.le
      have heq : (Z L*B L*(1-r L*Real.exp (r L))-E L)/Z L =
          B L*(1-r L*Real.exp (r L))-E L/Z L := by
        field_simp [ne_of_gt hz]
      exact heq ▸ hl
    · have hu := div_le_div_of_nonneg_right h.2 hz.le
      have heq : (Z L*B L*Real.exp (r L)+E L)/Z L =
          B L*Real.exp (r L)+E L/Z L := by
        field_simp [ne_of_gt hz]
      exact heq ▸ hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLow hHigh
    (hBounds.mono (fun L h => h.1)) (hBounds.mono (fun L h => h.2))

/-- The source upper endpoint 1/2-kappa is supported by the original
congruence level theta=1/2-kappa/2, with its positive gap retained. -/
theorem parity_original_negative_conditional_source_endpoint_8_2_434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (gamma kappa : ℝ) (hGamma : 0<gamma) (hKappa : 0<kappa)
    (hUpper : gamma<1/2-kappa) :
    Tendsto (fun L : ℝ =>
      parityOriginalConditionalBinMass434 Psi (-1) gamma (1/2-kappa) L /
      (localizedMass Psi (-1) L*
        parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L))))
      atTop (𝓝 (Real.log ((1/2-kappa)/gamma))) := by
  exact parity_original_negative_conditional_sieve_8_2_434
    Psi hSmooth hSupport hNonneg hInterior gamma (1/2-kappa) (1/2-kappa/2)
    hGamma hUpper (by linarith) (by linarith)

/-- Exact summation over actual adjacent external bins, before taking any
limit. The source mass is unchanged and no number-of-bins loss is inserted. -/
theorem parity_original_conditional_source_bins_exact434
    (Psi : ℝ → ℝ) (rho : ℝ) (t : ℕ → ℝ) (ht : Monotone t)
    (L : ℝ) (hL : 0≤L) (N : ℕ) :
    (∑ i∈Finset.range N,parityOriginalConditionalBinMass434 Psi rho (t i) (t (i+1)) L)=
      parityOriginalConditionalBinMass434 Psi rho (t 0) (t N) L := by
  unfold parityOriginalConditionalBinMass434
  rw [parity_original_prime_bins_sum_union434 t ht L hL,
    parity_original_prime_bins_union434 t ht L hL N]

end Green64Analytic.Parity

end

end

/-! ## OriginalFiniteBuchstab -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- Actual localized prime mass of the original parity source. There is no
roughness or squarefreeness premise in its definition. -/
def primeMass (Psi : ℝ → ℝ) (rho L : ℝ) : ℝ :=
  ∑ u∈Finset.range (⌊2*Real.exp L⌋₊+1),
    if (u+2).Prime then
      parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
        Psi ((u:ℝ)/Real.exp L) else 0

/-- Actual least-prime composite masses partition exactly across all
consecutive source bins, including empty bins and integral endpoints. -/
theorem parity_original_least_prime_mass_bins_exact434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (Y : ℕ)
    (hL : 0≤L) (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ) :
    (∑ i∈Finset.range N,
      parityOriginalUnbalancedLeastPrimeMass434 d L rho Psi (t i) (t (i+1)) Y)=
      parityOriginalUnbalancedLeastPrimeMass434 d L rho Psi (t 0) (t N) Y := by
  unfold parityOriginalUnbalancedLeastPrimeMass434
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hp : (u+2).Prime
  · simp [hp]
  · have h := parity_original_monotone_bins_weight_partition434 L hL t ht N
      (u+2).minFac
      ((parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)
    have hr := congrArg Complex.re h
    simpa only [Complex.re_sum,apply_ite,Complex.ofReal_re,Complex.zero_re,
      hp,not_false_eq_true,true_and] using hr

/-- Every active original prime u+2 already survives the initial cutoff.
The assertion is derived from the actual compact support and u+2>u. -/
theorem parity_original_active_prime_survives_initial_cutoff434
    (d : ℕ) (L rho beta : ℝ) (Psi : ℝ → ℝ)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hL : 0≤L) (hBeta : beta≤1) (u : ℕ) (hPrime : (u+2).Prime)
    (hWeight : parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L)≠0) :
    (Real.exp L)^beta<((u+2).minFac:ℝ) := by
  have hPsi : Psi ((u:ℝ)/Real.exp L)≠0 :=
    fun h => hWeight (by rw [h,mul_zero])
  have hu := (hSupport hPsi).1
  have huLower : Real.exp L≤(u:ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ (Real.exp_pos L)).mp hu
  have hCut : (Real.exp L)^beta≤Real.exp L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hL) hBeta
  rw [hPrime.minFac_eq,Nat.cast_add,Nat.cast_ofNat]
  linarith

/-- Exact finite original Buchstab classification: the full rough source
equals its true prime mass plus all least-prime bins plus the actual
balanced residual. The original weight, cutoff floor and multiplicities
are retained. No source-equality assumption is introduced. -/
theorem parity_original_rough_prime_composite_decomposition434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (rho beta kappa L : ℝ) (hL : 0≤L) (hBeta : beta≤1)
    (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ)
    (htZero : t 0=beta) (htEnd : t N=1/2-kappa) :
    parityOriginalRoughMass434 Psi rho beta L =
      primeMass Psi rho L+
      (∑ i∈Finset.range N,
        parityOriginalUnbalancedLeastPrimeMass434 (sourceOriginalLiteralDepth 20 L)
          L rho Psi (t i) (t (i+1)) ⌊2*Real.exp L⌋₊)+
      balancedCompositeMass (sourceOriginalLiteralDepth 20 L)
        L rho Psi kappa ⌊2*Real.exp L⌋₊ := by
  rw [parity_original_least_prime_mass_bins_exact434 _ _ _ _ _ hL t ht N,htZero,htEnd]
  have hBetaUpper : beta≤1/2-kappa := by
    simpa only [htZero,htEnd] using ht (Nat.zero_le N)
  have hExp : (Real.exp L)^beta=Real.exp (beta*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
  have hCutOrder : Real.exp (beta*L)≤Real.exp ((1/2-kappa)*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBetaUpper hL)
  unfold parityOriginalRoughMass434 primeMass
    parityOriginalUnbalancedLeastPrimeMass434 balancedCompositeMass
  simp_rw [Finset.sum_filter]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  let w := parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
    Psi ((u:ℝ)/Real.exp L)
  change (if (Real.exp L)^beta<((u+2).minFac:ℝ) then w else 0)=
    (if (u+2).Prime then w else 0)+
    (if ¬(u+2).Prime ∧ parityOriginalExponentBin434 L beta (1/2-kappa) (u+2).minFac
      then w else 0)+
    (if ¬(u+2).Prime ∧ Real.exp ((1/2-kappa)*L)<((u+2).minFac:ℝ)
      then w else 0)
  by_cases hw : w=0
  · simp only [hw,ite_self,add_zero]
  · by_cases hp : (u+2).Prime
    · have hCut := parity_original_active_prime_survives_initial_cutoff434
        (sourceOriginalLiteralDepth 20 L) L rho beta Psi hSupport hL hBeta u hp hw
      simp only [hp,not_true_eq_false,false_and,ite_false,ite_true,hCut,add_zero]
    · rw [hExp]
      by_cases hLow : Real.exp (beta*L)<((u+2).minFac:ℝ)
      · by_cases hUpper : ((u+2).minFac:ℝ)≤Real.exp ((1/2-kappa)*L)
        · simp only [hp,not_false_eq_true,true_and,parityOriginalExponentBin434,hLow,hUpper,
            not_lt_of_ge hUpper,ite_false,ite_true,add_zero,zero_add]
        · have hUpper' := lt_of_not_ge hUpper
          simp only [hp,not_false_eq_true,true_and,parityOriginalExponentBin434,hLow,hUpper,
            hUpper',ite_false,ite_true,add_zero,zero_add]
      · have hHigh : ¬Real.exp ((1/2-kappa)*L)<((u+2).minFac:ℝ) :=
          fun h => hLow (hCutOrder.trans_lt h)
        simp only [hp,not_false_eq_true,true_and,parityOriginalExponentBin434,hLow,hHigh,
          false_and,ite_false,add_zero]

/-- The actual prime-mass subtraction inequality, joined to the already
proved ORIGINAL unbalanced rough/prime and ordered balanced prime-pair
sources. Both parity signs are allowed algebraically; no positive prime
mass or source-budget estimate is assumed or concluded here. -/
theorem parity_eventually_original_prime_mass_source_subtraction434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀x,0≤Psi x)
    (beta kappa : ℝ) (hBeta : beta≤1) (hKappa : 0<kappa)
    (hKappaUpper : kappa<1/50)
    (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ)
    (htZero : t 0=beta) (htEnd : t N=1/2-kappa) :
    ∀ᶠ L : ℝ in atTop,∀ rho S : ℝ,|rho|≤1 →
      parityOriginalRoughMass434 Psi rho beta L-
      (∑ i∈Finset.range N,
        (parityOriginalSieveUnbalancedBinSource434 false false (sourceOriginalLiteralDepth 20 L)
          L rho Psi S (t i) (t (i+1)) ⌊2*Real.exp L⌋₊).re)-
      (balancedFactorSum false false (sourceOriginalLiteralDepth 20 L)
        L rho Psi S beta kappa ⌊2*Real.exp L⌋₊).re ≤
      primeMass Psi rho L := by
  filter_upwards [parity_eventually_original_balanced_composite_mass_le_source434
    kappa hKappa hKappaUpper Psi hSupport hNonneg,
    eventually_ge_atTop (0:ℝ)] with L hBalanced hL rho S hRho
  have hId := parity_original_rough_prime_composite_decomposition434
    Psi hSupport rho beta kappa L hL hBeta t ht N htZero htEnd
  have hUnbalanced := Finset.sum_le_sum (s:=Finset.range N) (fun i hi =>
    parity_original_unbalanced_composite_mass_le_source434
      (sourceOriginalLiteralDepth 20 L) L rho hRho Psi hNonneg S (t i) (t (i+1))
      ⌊2*Real.exp L⌋₊)
  have hBal := hBalanced (sourceOriginalLiteralDepth 20 L) ⌊2*Real.exp L⌋₊
    rho S beta hRho
  linarith
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedDensityWindow -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- Precise cofactor exponents on the actual original source in a fixed
prime bin. Arbitrarily small fixed delta is retained; the original Psi is
not shrunk and mn=u+2 is used directly, without truncated Nat subtraction. -/
theorem parity_original_actual_cofactor_precise_window434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (gamma eta delta : ℝ) (hDelta : 0< delta) :
    ∀ᶠ L : ℝ in atTop,∀ (rho : ℝ) (u p m : ℕ),
      parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
        Psi ((u:ℝ)/Real.exp L)≠0 →
      m*p=u+2 → (Real.exp L)^gamma<(p:ℝ) → (p:ℝ)≤(Real.exp L)^eta →
      Real.exp ((1-eta)*L)≤(m:ℝ) ∧ (m:ℝ)≤ Real.exp ((1-gamma+delta)*L) := by
  filter_upwards [eventually_ge_atTop (max 1 (6/delta))] with L hLarge
  have hL1 : 1≤ L := (le_max_left _ _).trans hLarge
  have hL : 0< L := by linarith
  have hLD : 6/delta≤ L := (le_max_right _ _).trans hLarge
  have hDL : 6≤ delta*L := by
    have hh := (div_le_iff₀ hDelta).mp hLD
    linarith
  have heL : 1≤ Real.exp L := Real.one_le_exp hL.le
  have hFour : 4≤ Real.exp (delta*L) := by
    linarith [Real.add_one_le_exp (delta*L)]
  intro rho u p m hWeight hProd hpLow hpHigh
  have hPsi : Psi ((u:ℝ)/Real.exp L)≠0 := fun hz => hWeight (by rw [hz,mul_zero])
  have hSupp := hSupport hPsi
  have huLow : Real.exp L≤(u:ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ (Real.exp_pos L)).mp hSupp.1
  have huHigh : (u:ℝ)≤2*Real.exp L := (div_le_iff₀ (Real.exp_pos L)).mp hSupp.2
  have hProdReal : (p:ℝ)*(m:ℝ)=(u:ℝ)+2 := by
    exact_mod_cast (show p*m=u+2 by simpa only [Nat.mul_comm] using hProd)
  have hExp (a : ℝ) : (Real.exp L)^a=Real.exp (a*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
  rw [hExp eta] at hpHigh
  rw [hExp gamma] at hpLow
  have hmNonneg : (0:ℝ)≤ m := Nat.cast_nonneg _
  have hProdLow : Real.exp L≤(p:ℝ)*(m:ℝ) := by linarith
  have hProdHigh : (p:ℝ)*(m:ℝ)≤4*Real.exp L := by linarith
  have hLow := hProdLow.trans (mul_le_mul_of_nonneg_right hpHigh hmNonneg)
  have hExpLow : Real.exp (eta*L)*Real.exp ((1-eta)*L)=Real.exp L := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hmLow : Real.exp ((1-eta)*L)≤(m:ℝ) :=
    le_of_mul_le_mul_left (by simpa only [hExpLow] using hLow) (Real.exp_pos (eta*L))
  have hMid : Real.exp (gamma*L)*(m:ℝ)≤4*Real.exp L :=
    (mul_le_mul_of_nonneg_right hpLow.le hmNonneg).trans hProdHigh
  have hExpHigh : Real.exp L*Real.exp (delta*L)=
      Real.exp (gamma*L)*Real.exp ((1-gamma+delta)*L) := by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hUpper : 4*Real.exp L≤
      Real.exp (gamma*L)*Real.exp ((1-gamma+delta)*L) := by
    rw [←hExpHigh]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hFour (Real.exp_pos L).le
  exact ⟨hmLow,le_of_mul_le_mul_left (hMid.trans hUpper) (Real.exp_pos (gamma*L))⟩

/-- Genuine D29 density bound on the ORIGINAL full-cell rough-proxy
coefficient of an active Parity source pair. The actual cofactor window and
integer carrier membership are proved from the source, not assumed.
There is no abstract density-cap or desired bin-budget hypothesis. -/
theorem parity_original_actual_fullcell_cofactor_density434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (S gamma eta delta eps : ℝ) (hS : 0< S) (hGamma : 0< gamma)
    (hOrder : gamma< eta) (hEta : eta<1/2)
    (hDelta : 0< delta) (hDeltaGamma : delta< gamma) (hEps : 0< eps) :
    ∀ᶠ L : ℝ in atTop,∀ (rho : ℝ) (u p m : ℕ),
      parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
        Psi ((u:ℝ)/Real.exp L)≠0 →
      m*p=u+2 → (Real.exp L)^gamma<(p:ℝ) → (p:ℝ)≤(Real.exp L)^eta →
      (parityOriginalFullCellCoefficient434 true false L S gamma 1 (⌊2*Real.exp L⌋₊+2) m).re ≤
        (Green64Analytic.SmallB.sourceDensity gamma (Real.log (m:ℝ)/L)+eps)/
          (L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  have hGA : gamma<1-eta := by linarith
  have hAB : 1-eta≤1-gamma+delta := by linarith
  have hB : 1-gamma+delta<1 := by linarith
  filter_upwards [parity_original_actual_cofactor_precise_window434
      Psi hSupport gamma eta delta hDelta,
    sourceD29_original_full_proxy_pointwise_compact S gamma (1-eta) (1-gamma+delta)
      eps hS hGamma hGA hAB hB hEps,
    eventually_gt_atTop (0:ℝ)] with L hWindow hPoint hL rho u p m hWeight hProd hpLow hpHigh
  have hmWindow := hWindow rho u p m hWeight hProd hpLow hpHigh
  have hPsi : Psi ((u:ℝ)/Real.exp L)≠0 := fun hz => hWeight (by rw [hz,mul_zero])
  have huHigh : (u:ℝ)≤2*Real.exp L :=
    (div_le_iff₀ (Real.exp_pos L)).mp (hSupport hPsi).2
  have huY : u≤⌊2*Real.exp L⌋₊ := (Nat.le_floor_iff (by positivity)).mpr huHigh
  have hmPos : 0< m := by
    have hReal : (0:ℝ)< m := (Real.exp_pos _).trans_le hmWindow.1
    exact_mod_cast hReal
  have hpPos : 0< p := by
    have hReal : (0:ℝ)< p := (Real.rpow_pos_of_pos (Real.exp_pos L) gamma).trans hpLow
    exact_mod_cast hReal
  have hmBound : m≤ u+2 := by
    have h := Nat.mul_le_mul_left m hpPos
    simpa [hProd] using h
  have hmCarrier : m∈Finset.Icc 1 (⌊2*Real.exp L⌋₊+2) :=
    Finset.mem_Icc.mpr ⟨hmPos,by omega⟩
  have hExact : parityOriginalFullCellCoefficient434 true false L S gamma
      1 (⌊2*Real.exp L⌋₊+2) m =
      ((sourceD20FullProxy (L^(-S)) (Real.exp (Real.sqrt L)) ((Real.exp L)^gamma) m:ℝ):ℂ) := by
    simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellProxyBeta434,hmCarrier]
  rw [hExact,Complex.ofReal_re]
  exact hPoint m hmWindow.1 hmWindow.2
end Green64Analytic.Parity

end

end

/-! ## OriginalPresieveIntegratedAudit -/

section

set_option pp.universes false

end

