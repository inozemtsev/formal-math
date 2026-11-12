module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part008

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.GaussFactorization -/

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicBesselNormalizer (h : ActualEisensteinCubic.O) : ℂ :=
  (2*Real.pi:ℂ)/Complex.Gamma (4/3)*(2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ)

def cubicResidualFourierCoefficient (h : ActualEisensteinCubic.O) : ℂ :=
  cubicBesselNormalizer h*nonzeroScatteringResidue h

lemma sourceFourierKernel_cubic_height (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) :
    (v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*
        (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [sourceFourierKernel_four_thirds _ (mul_ne_zero (cuspFrequency_ne_zero h hh) hv0)]
  have hnorm : ‖cuspFrequency h*(v:ℂ)‖=‖cuspFrequency h‖*v := by
    rw [norm_mul,Complex.norm_of_nonneg hv.le]
  rw [hnorm]
  simp only [Complex.ofReal_mul]
  have hbase : (2*Real.pi*(‖cuspFrequency h‖*v):ℂ)=
      (2*Real.pi*‖cuspFrequency h‖:ℂ)*(v:ℂ) := by ring
  have hpow : (2*Real.pi*(‖cuspFrequency h‖*v):ℂ)^(1/3:ℂ)=
      (2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ)*(v:ℂ)^(1/3:ℂ) := by
    rw [hbase]
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      (Complex.mul_cpow_ofReal_nonneg (a := 2*Real.pi*‖cuspFrequency h‖) (b := v)
        (by positivity) hv.le (1/3:ℂ))
  have hvpow : (v:ℂ)^(-(4/3:ℂ)-1)*(v:ℂ)^(1/3:ℂ)=1/(v:ℂ)^2 := by
    rw [←Complex.cpow_add _ _ hv0,show -(4/3:ℂ)-1+1/3=-(2:ℂ) by ring,
      Complex.cpow_neg,Complex.cpow_ofNat]
    simp only [one_div]
  have harg : 4*Real.pi*(‖cuspFrequency h‖*v)=4*Real.pi*‖cuspFrequency h‖*v := by ring
  rw [hpow,harg]
  unfold cubicBesselNormalizer
  calc
    _ = ((2*Real.pi:ℂ)/Complex.Gamma (4/3)*(2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ))*
        ((v:ℂ)^(-(4/3:ℂ)-1)*(v:ℂ)^(1/3:ℂ))*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by ring
    _ = _ := by rw [hvpow]; ring

end

section
open Filter MeasureTheory
open scoped Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspWhittakerHeightFactor_punctured_ne_zero (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    ∀ᶠw : ℂ in 𝓝[≠] s,cuspWhittakerHeightFactor w h≠0 := by
  rcases (cuspWhittakerHeightFactor_analyticAt h s hs).eventually_eq_zero_or_eventually_ne_zero with hz|hne
  · have han : AnalyticOnNhd ℂ (fun w => cuspWhittakerHeightFactor w h) {w : ℂ | 1<w.re} :=
      fun w hw => cuspWhittakerHeightFactor_analyticAt h w hw
    have hcon : Convex ℝ {w : ℂ | 1<w.re} :=
      (convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap
    have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hcon.isPreconnected hs hz
    have hval : cuspWhittakerHeightFactor (5:ℂ) h=0 := heq (by norm_num)
    have hpos := cuspWhittakerHeightFactor_real_re_pos 5 (by norm_num) h
    norm_num only [Complex.ofReal_ofNat] at hpos
    rw [hval,Complex.zero_re] at hpos
    exact (lt_irrefl 0 hpos).elim
  · exact hne

lemma continuedNonzeroScattering_eq_arithmetic_germ (h : ActualEisensteinCubic.O) (hh : h≠0)
    (s : ℂ) (hs : 2<s.re) (hi : 0<s.im) :
    continuedNonzeroScattering h =ᶠ[𝓝[≠] s] (fun w => scatteringCoefficient w h) := by
  have hopen : IsOpen {w : ℂ | 2<w.re ∧ 0<w.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hfull : ∀ᶠw : ℂ in 𝓝 s,2<w.re ∧ 0<w.im := hopen.mem_nhds ⟨hs,hi⟩
  have hdomain : ∀ᶠw : ℂ in 𝓝[≠] s,2<w.re ∧ 0<w.im :=
    hfull.filter_mono nhdsWithin_le_nhds
  filter_upwards [hdomain,cuspWhittakerHeightFactor_punctured_ne_zero h s (by linarith)] with w hw hH
  exact continuedNonzeroScattering_eq_upper h hh w hw.1 hw.2 hH

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspWeightedWhittakerHeightFactor_differentiableAt
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ (fun w => cuspWeightedWhittakerHeightFactor ρ w h) s := by
  have heq : (fun w => cuspWeightedWhittakerHeightFactor ρ w h)=
      (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (cuspFrequency h*v)) := by
    funext w
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => (mul_assoc _ _ _).symm)
  rw [heq]
  exact cuspWeightedWhittakerAverage_differentiableAt ρ (cuspFrequency h) s hs

lemma cuspWeightedWhittakerHeightFactor_analyticAt
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspWeightedWhittakerHeightFactor ρ w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact cuspWeightedWhittakerHeightFactor_differentiableAt ρ h w hw

lemma kernelCuspWeightedFourierFamily_cross_identity
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (fun s => kernelCuspWeightedFourierFamily ρ h s*cuspWhittakerHeightFactor s h)
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspWeightedWhittakerHeightFactor ρ s h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s => kernelCuspWeightedFourierFamily ρ h s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (kernelCuspWeightedFourierFamily_analyticAt_nonreal ρ h s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspWeightedWhittakerHeightFactor ρ s h) domain := by
    intro s hs
    exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s hs.1.ne' hs.2.ne').mul (cuspWeightedWhittakerHeightFactor_analyticAt ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelCuspWeightedFourierFamily ρ h s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
          cuspWeightedWhittakerHeightFactor ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [kernelCuspWeightedFourierFamily_initial_factor ρ h hh s hs.1 hs.2,
      kernelCuspFourierFamily_eq_upper h hh ⟨by linarith [hs.1],hs.2⟩]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

lemma upperVertical_tendsto_cubic_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => (4/3:ℂ)+(t:ℂ)*Complex.I) 0 := by fun_prop
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    change (4/3:ℂ)+(t:ℂ)*Complex.I≠(4/3:ℂ)
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_one,zero_mul,add_zero] at hh
    exact ht.ne' (by linarith [hh])

lemma kernelCuspWeightedFourier_residue_factor
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspWeightedFourier ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*nonzeroScatteringResidue h*
        cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h := by
  have hbase : Tendsto (fun s : ℂ => cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) h)) :=
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hweight : Tendsto (fun s : ℂ => cuspWeightedWhittakerHeightFactor ρ s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h)) :=
    (cuspWeightedWhittakerHeightFactor_analyticAt ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft := ((kernelCuspWeightedFourierFamily_residue_limit ρ h).mul hbase).comp
    upperVertical_tendsto_cubic_punctured
  have hright := ((kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).mul hweight).comp
    upperVertical_tendsto_cubic_punctured
  have hevent : (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspWeightedFourierFamily ρ h ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)
        ((4/3:ℂ)+(t:ℂ)*Complex.I))*cuspWeightedWhittakerHeightFactor ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)*Complex.I∈{s : ℂ | 1<s.re ∧ 0<s.im} := by
      constructor
      · norm_num
      · simpa using ht
    have he := kernelCuspWeightedFourierFamily_cross_identity ρ h hh hs
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : kernelCuspWeightedFourier ρ h cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      kernelCuspFourier h cubicEisensteinResidue*cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hevent
  have hH := cuspWhittakerHeightFactor_center_ne_zero h
  calc
    _ = (kernelCuspFourier h cubicEisensteinResidue*cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h)/
        cuspWhittakerHeightFactor (4/3:ℂ) h := (eq_div_iff hH).mpr heq
    _ = _ := by
      unfold nonzeroScatteringResidue
      field_simp [cusp_volume_ne_zero,hH]

lemma cuspWeightedWhittakerHeightFactor_center_bessel
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h=
      cubicBesselNormalizer h*(∫v in Set.Icc (5:ℝ) 6,
        ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [cuspWeightedWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  dsimp only
  rw [sourceFourierKernel_cubic_height h hh v hpos]
  ring

lemma kernelCuspWeightedFourier_residue_bessel
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspWeightedFourier ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFourierCoefficient h*
        (∫v in Set.Icc (5:ℝ) 6,ρ v*
          (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [kernelCuspWeightedFourier_residue_factor ρ h hh,
    cuspWeightedWhittakerHeightFactor_center_bessel ρ h hh,cubicResidualFourierCoefficient]
  ring

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma denominatorRep_mk_congr (c d : Eis) :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) d)-d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact denominatorRep_spec c _

lemma isCoprime_right_congr_of_dvd (c d e : Eis) (h : c ∣ d-e) :
    IsCoprime c d ↔ IsCoprime c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+c*n := by linear_combination hn
  rw [hd,IsCoprime.add_mul_left_right_iff]

abbrev CubicUnitResidue (b : Eis) :=
  {r : Eis ⧸ Ideal.span {b} // IsUnit r}

def denominatorCRTMap (a b : Eis) (r : AdmissibleResidue (a*b)) :
    AdmissibleResidue a × CubicUnitResidue b :=
  let d:=denominatorRep (a*b) r.1
  (⟨Ideal.Quotient.mk (Ideal.span {3*a}) d,
      (denominatorCondition_congr a _ d (denominatorRep_mk_congr a d)).mpr
        ⟨r.2.1.of_mul_left_left,r.2.2⟩⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr r.2.1.of_mul_left_right⟩)

lemma denominatorCRTMap_injective (a b : Eis) (hab : IsCoprime (3*a) b) :
    Function.Injective (denominatorCRTMap a b) := by
  intro r t he
  have h1:=congrArg (fun z : AdmissibleResidue a × CubicUnitResidue b => z.1.1) he
  have h2:=congrArg (fun z : AdmissibleResidue a × CubicUnitResidue b => z.2.1) he
  change Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) t.1) at h1
  change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) t.1) at h2
  have hdiv : 3*(a*b) ∣ denominatorRep (a*b) r.1-denominatorRep (a*b) t.1 := by
    simpa only [mul_assoc] using hab.mul_dvd
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1))
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2))
  apply Subtype.ext
  rw [←denominatorRep_spec (a*b) r.1,←denominatorRep_spec (a*b) t.1]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hdiv)

lemma denominatorCRTMap_surjective (a b : Eis) (hab : IsCoprime (3*a) b) :
    Function.Surjective (denominatorCRTMap a b) := by
  rintro ⟨r,t⟩
  obtain ⟨u,v,huv⟩ := hab
  let delta:=denominatorRep a r.1
  let xi:=GaussianShiftedPartition.representative b t.1
  let d:=v*b*delta+u*(3*a)*xi
  have hda : 3*a ∣ d-delta := by
    refine ⟨u*(xi-delta),?_⟩
    dsimp [d]
    linear_combination delta*huv
  have hdb : b ∣ d-xi := by
    refine ⟨v*(delta-xi),?_⟩
    dsimp [d]
    linear_combination xi*huv
  have hxi : IsCoprime b xi := by
    apply (isUnit_quotient_span_iff b xi).mp
    simpa only [xi,GaussianShiftedPartition.representative_spec] using t.2
  have had : denominatorCondition a d := (denominatorCondition_congr a d delta hda).mpr r.2
  have hbd : IsCoprime b d := (isCoprime_right_congr_of_dvd b d xi hdb).mpr hxi
  have hd : denominatorCondition (a*b) d := ⟨had.1.mul_left hbd,had.2⟩
  let q : AdmissibleResidue (a*b):=⟨Ideal.Quotient.mk (Ideal.span {3*(a*b)}) d,
    (denominatorCondition_congr (a*b) _ d (denominatorRep_mk_congr (a*b) d)).mpr hd⟩
  refine ⟨q,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) q.1)=r.1
    rw [←denominatorRep_spec a r.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh : 3*a ∣ denominatorRep (a*b) q.1-d := by
      exact (show 3*a ∣ 3*(a*b) from ⟨b,by ring⟩).trans (denominatorRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hda
  · change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) q.1)=t.1
    rw [←GaussianShiftedPartition.representative_spec b t.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh : b ∣ denominatorRep (a*b) q.1-d := by
      exact (show b ∣ 3*(a*b) from ⟨3*a,by ring⟩).trans (denominatorRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hdb

def denominatorCRTEquiv (a b : Eis) (hab : IsCoprime (3*a) b) :
    AdmissibleResidue (a*b) ≃ AdmissibleResidue a × CubicUnitResidue b :=
  Equiv.ofBijective (denominatorCRTMap a b)
    ⟨denominatorCRTMap_injective a b hab,denominatorCRTMap_surjective a b hab⟩

def residueAdditive (h c d : Eis) : ℂ :=
  ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding d/eisEmbedding c)

lemma residueAdditive_congr (h c d e : Eis) (hc : c≠0) (hde : 3*c ∣ d-e) :
    residueAdditive h c d=residueAdditive h c e := by
  obtain ⟨n,hn⟩:=hde
  have hd:d=e+3*c*n:=by linear_combination hn
  have he:eisEmbedding c≠0:=eisEmbedding_ne_zero hc
  unfold residueAdditive
  rw [hd]
  have hh : cuspFrequency h*eisEmbedding (e+3*c*n)/eisEmbedding c=
      cuspFrequency h*eisEmbedding e/eisEmbedding c+cuspFrequency h*(3*eisEmbedding n) := by
    simp only [map_add,map_mul,map_ofNat]
    field_simp
  rw [hh,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

def cubicUnitGaussSum (h b : Eis) : ℂ :=
  ∑' r : CubicUnitResidue b,
    eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b r.1)

lemma residueAdditive_three_congr (h b d e : Eis) (hb : b≠0) (hde : b ∣ d-e) :
    residueAdditive (3*h) b d=residueAdditive (3*h) b e := by
  obtain ⟨n,hn⟩:=hde
  have hd:d=e+b*n:=by linear_combination hn
  have he:eisEmbedding b≠0:=eisEmbedding_ne_zero hb
  unfold residueAdditive
  rw [hd]
  have hh : cuspFrequency (3*h)*eisEmbedding (e+b*n)/eisEmbedding b=
      cuspFrequency (3*h)*eisEmbedding e/eisEmbedding b+cuspFrequency h*(3*eisEmbedding n) := by
    simp only [cuspFrequency,map_add,map_mul,map_ofNat]
    field_simp
  rw [hh,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

lemma residueAdditive_crt (h a b alpha beta d : Eis) (ha : a≠0) (hb : b≠0)
    (hbez : alpha*b+beta*(3*a)=1) :
    residueAdditive h (a*b) d=
      residueAdditive (h*alpha) a d*residueAdditive (3*(h*beta)) b d := by
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  have hbeq:=congrArg eisEmbedding hbez
  simp only [map_add,map_mul,map_one,map_ofNat] at hbeq
  simp only [cuspFrequency,map_mul,map_ofNat]
  field_simp [hae,hbe,eisLam_ne_zero]
  linear_combination -(eisEmbedding h*eisEmbedding d)*hbeq

lemma arithmetic_crt_summand (h a b alpha beta : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hbez : alpha*b+beta*(3*a)=1)
    (r : AdmissibleResidue (a*b)) :
    eisEmbedding (symbol (a*b) (denominatorRep (a*b) r.1))*
      residueAdditive h (a*b) (denominatorRep (a*b) r.1)=
    (eisEmbedding (symbol a (denominatorRep a (denominatorCRTMap a b r).1.1))*
      residueAdditive (h*alpha) a (denominatorRep a (denominatorCRTMap a b r).1.1))*
    (eisEmbedding (symbol (GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1)) := by
  let d:=denominatorRep (a*b) r.1
  let delta:=denominatorRep a (denominatorCRTMap a b r).1.1
  let xi:=GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1
  have hdprimary : lambda^2∣d-1:=lambda_sq_dvd_three.trans r.2.2
  have hdelta : 3*a∣delta-d:=denominatorRep_mk_congr a d
  have hxi : b∣xi-d:=by
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact GaussianShiftedPartition.representative_spec b _
  have hchar : symbol (a*b) d=symbol a delta*symbol xi b := by
    rw [symbol_mul_numerator a b d hdprimary,
      symbol_reciprocity b d hb (primary_ne_zero d hdprimary) hbprimary hdprimary,
      ←symbol_congr hxi]
    rw [←row_symbol_congr_modulus a delta d halevel r.2.2 hdelta]
  change eisEmbedding (symbol (a*b) d)*residueAdditive h (a*b) d=
    (eisEmbedding (symbol a delta)*residueAdditive (h*alpha) a delta)*
      (eisEmbedding (symbol xi b)*residueAdditive (3*(h*beta)) b xi)
  rw [hchar,map_mul,residueAdditive_crt h a b alpha beta d ha hb hbez,
    residueAdditive_congr (h*alpha) a delta d ha hdelta,
    residueAdditive_three_congr (h*beta) b xi d hb hxi]
  ring

theorem arithmeticResidueSum_crt (h a b alpha beta : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hbez : alpha*b+beta*(3*a)=1) :
    arithmeticResidueSum h (a*b)=
      arithmeticResidueSum (h*alpha) a*cubicUnitGaussSum (h*beta) b := by
  have hab : IsCoprime (3*a) b:=⟨beta,alpha,by linear_combination hbez⟩
  let f : AdmissibleResidue a→ℂ:=fun r=>
    eisEmbedding (symbol a (denominatorRep a r.1))*residueAdditive (h*alpha) a (denominatorRep a r.1)
  let g : CubicUnitResidue b→ℂ:=fun r=>
    eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b r.1)
  have heq: arithmeticResidueSum h (a*b)=∑' r : AdmissibleResidue (a*b),
      f (denominatorCRTEquiv a b hab r).1*g (denominatorCRTEquiv a b hab r).2 := by
    unfold arithmeticResidueSum
    apply tsum_congr
    intro r
    exact arithmetic_crt_summand h a b alpha beta ha hb halevel hbprimary hbez r
  rw [heq,(denominatorCRTEquiv a b hab).tsum_eq (fun r=>f r.1*g r.2)]
  let : Finite (AdmissibleResidue a):=finite_admissibleResidue a ha
  let : Finite (Eis ⧸ Ideal.span {b}):=finite_quotient_span hb
  let : Fintype (AdmissibleResidue a):=Fintype.ofFinite _
  let : Fintype (CubicUnitResidue b):=Fintype.ofFinite _
  change (∑' r : AdmissibleResidue a × CubicUnitResidue b,f r.1*g r.2)=
    (∑' r : AdmissibleResidue a,f r)*(∑' t : CubicUnitResidue b,g t)
  simp only [tsum_fintype,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

end

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma residueAdditive_mul (h c t d : Eis) :
    residueAdditive h c (t*d)=residueAdditive (h*t) c d := by
  unfold residueAdditive cuspFrequency
  simp only [map_mul]
  congr 1
  ring

lemma residueAdditive_swap (h c d : Eis) :
    residueAdditive h c d=residueAdditive d c h := by
  unfold residueAdditive cuspFrequency
  congr 1
  ring

lemma arithmeticResidueSum_frequency_congr (h k c : Eis) (hc : c≠0)
    (hh : 3*c∣h-k) : arithmeticResidueSum h c=arithmeticResidueSum k c := by
  unfold arithmeticResidueSum
  apply tsum_congr
  intro r
  congr 1
  change residueAdditive h c (denominatorRep c r.1)=residueAdditive k c (denominatorRep c r.1)
  rw [residueAdditive_swap h,residueAdditive_swap k]
  exact residueAdditive_congr _ c h k hc hh

theorem arithmeticResidueSum_frequency_twist (h c t : Eis) (hc : c≠0)
    (hlevel : (3:Eis)∣c) (ht : denominatorCondition c t) :
    eisEmbedding (symbol c t)*arithmeticResidueSum (h*t) c=arithmeticResidueSum h c := by
  have heq:=(residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c=>eisEmbedding (symbol c (denominatorRep c r.1))*
      residueAdditive h c (denominatorRep c r.1))
  calc
    _ = ∑' r : AdmissibleResidue c,eisEmbedding (symbol c t)*
      (eisEmbedding (symbol c (denominatorRep c r.1))*residueAdditive (h*t) c (denominatorRep c r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c (residueMultiplicationEquiv c hc t ht r).1))*
        residueAdditive h c (denominatorRep c (residueMultiplicationEquiv c hc t ht r).1) := by
      apply tsum_congr
      intro r
      change _=eisEmbedding (symbol c (denominatorRep c (residueMultiplication c t ht r).1))*
        residueAdditive h c (denominatorRep c (residueMultiplication c t ht r).1)
      rw [residueMultiplication_phase c hlevel t ht r,map_mul]
      dsimp only [residueMultiplication]
      rw [residueAdditive_congr h c _ (t*denominatorRep c r.1) hc
        (denominatorRep_product_congr c t r.1),residueAdditive_mul]
      ring
    _ = _ := heq

lemma cubicUnitGaussSum_frequency_congr (h k b : Eis) (hb : b≠0)
    (hh : b∣h-k) : cubicUnitGaussSum h b=cubicUnitGaussSum k b := by
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro r
  congr 1
  have he (u : Eis) : residueAdditive (3*u) b (GaussianShiftedPartition.representative b r.1)=
      residueAdditive (3*GaussianShiftedPartition.representative b r.1) b u := by
    unfold residueAdditive cuspFrequency
    simp only [map_mul,map_ofNat]
    congr 1
    ring
  rw [he h,he k]
  exact residueAdditive_three_congr _ b h k hb hh

def cubicUnitResidueMul (b t : Eis) (ht : IsCoprime b t) (r : CubicUnitResidue b) :
    CubicUnitResidue b :=
  ⟨Ideal.Quotient.mk (Ideal.span {b}) t*r.1,
    ((isUnit_quotient_span_iff b t).mpr ht).mul r.2⟩

lemma cubicUnitResidueMul_injective (b t : Eis) (ht : IsCoprime b t) :
    Function.Injective (cubicUnitResidueMul b t ht) := by
  intro r q heq
  apply Subtype.ext
  exact ((isUnit_quotient_span_iff b t).mpr ht).mul_left_cancel (congrArg Subtype.val heq)

def cubicUnitResidueMulEquiv (b t : Eis) (hb : b≠0) (ht : IsCoprime b t) :
    CubicUnitResidue b ≃ CubicUnitResidue b := by
  letI : Finite (Eis ⧸ Ideal.span {b}):=finite_quotient_span hb
  exact Equiv.ofBijective (cubicUnitResidueMul b t ht)
    ⟨cubicUnitResidueMul_injective b t ht,
      Finite.surjective_of_injective (cubicUnitResidueMul_injective b t ht)⟩

lemma cubicUnitResidueMul_rep_congr (b t : Eis) (ht : IsCoprime b t)
    (r : CubicUnitResidue b) :
    b∣GaussianShiftedPartition.representative b (cubicUnitResidueMul b t ht r).1-
      t*GaussianShiftedPartition.representative b r.1 := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [GaussianShiftedPartition.representative_spec,map_mul,
    GaussianShiftedPartition.representative_spec]
  rfl

theorem cubicUnitGaussSum_frequency_twist (h b t : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (ht : IsCoprime b t) :
    eisEmbedding (symbol t b)*cubicUnitGaussSum (h*t) b=cubicUnitGaussSum h b := by
  have heq:=(cubicUnitResidueMulEquiv b t hb ht).tsum_eq
    (fun r : CubicUnitResidue b=>eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b r.1))
  calc
    _ = ∑' r : CubicUnitResidue b,eisEmbedding (symbol t b)*
      (eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
        residueAdditive (3*(h*t)) b (GaussianShiftedPartition.representative b r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : CubicUnitResidue b,
      eisEmbedding (symbol (GaussianShiftedPartition.representative b
        (cubicUnitResidueMulEquiv b t hb ht r).1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b
        (cubicUnitResidueMulEquiv b t hb ht r).1) := by
      apply tsum_congr
      intro r
      change _=eisEmbedding (symbol (GaussianShiftedPartition.representative b
        (cubicUnitResidueMul b t ht r).1) b)*
        residueAdditive (3*h) b (GaussianShiftedPartition.representative b (cubicUnitResidueMul b t ht r).1)
      rw [symbol_congr (cubicUnitResidueMul_rep_congr b t ht r),
        symbol_mul_numerator t _ b hbprimary,map_mul]
      rw [residueAdditive_three_congr h b _ (t*GaussianShiftedPartition.representative b r.1)
        hb (cubicUnitResidueMul_rep_congr b t ht r),residueAdditive_mul]
      rw [show (3*h)*t=3*(h*t) by ring]
      ring
    _ = _ := heq

theorem arithmeticResidueSum_coprime_product (h a b : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hab : IsCoprime (3*a) b) :
    arithmeticResidueSum h (a*b)=
      eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
        arithmeticResidueSum h a*cubicUnitGaussSum h b := by
  obtain ⟨beta,alpha,hbez⟩:=hab
  have hbez' : alpha*b+beta*(3*a)=1:=by linear_combination hbez
  have hab' : IsCoprime (3*a) b:=⟨beta,alpha,hbez⟩
  have hb3 : (3:Eis)∣b-1:=three_dvd_lambda_sq.trans hbprimary
  have hbt : denominatorCondition a b:=⟨hab'.of_mul_left_right,hb3⟩
  have hA := arithmeticResidueSum_frequency_twist (h*alpha) a b ha halevel hbt
  have hAf : 3*a∣(h*alpha)*b-h:=⟨-h*beta,by linear_combination h*hbez'⟩
  rw [arithmeticResidueSum_frequency_congr _ h a ha hAf] at hA
  have hB := cubicUnitGaussSum_frequency_twist (h*beta) b (3*a) hb hbprimary hab'.symm
  have hBf : b∣(h*beta)*(3*a)-h:=⟨-h*alpha,by linear_combination h*hbez'⟩
  rw [cubicUnitGaussSum_frequency_congr _ h b hb hBf] at hB
  rw [arithmeticResidueSum_crt h a b alpha beta ha hb halevel hbprimary hbez',←hA,←hB]
  ring

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.RamifiedGaussSeries -/

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedElement_ne_zero (u : Eisˣ) (n : ℕ) : u.val*lambda^n≠0 := by
  have hl : lambda≠0:=by
    intro hh
    apply CompletedGauss.embedding_lambda_ne_zero
    rw [hh,map_zero]
  exact mul_ne_zero u.ne_zero (pow_ne_zero _ hl)

lemma ramifiedElement_level (u : Eisˣ) (n : ℕ) (hn : 2≤n) :
    (3:Eis)∣u.val*lambda^n :=
  dvd_mul_of_dvd_right (three_dvd_lambda_sq.trans (pow_dvd_pow lambda hn)) _

lemma ramified_denominator_condition (u : Eisˣ) (n : ℕ) (d : Eis)
    (hd : (3:Eis)∣d-1) : denominatorCondition (u.val*lambda^n) d := by
  have hu : IsCoprime u.val d:=⟨u.inv,0,by simp⟩
  have hl3 : lambda∣(3:Eis):=(dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
  have hld : IsCoprime lambda d:=coprime_of_dvd_sub_one lambda d (hl3.trans hd)
  exact ⟨hu.mul_left hld.pow_left,hd⟩

lemma ramified_symbol_congr_mod_nine (u : Eisˣ) (n : ℕ) (d e : Eis)
    (hd : (3:Eis)∣d-1) (he : (3:Eis)∣e-1) (hde : (9:Eis)∣d-e) :
    symbol (u.val*lambda^n) d=symbol (u.val*lambda^n) e := by
  have hdp:=lambda_sq_dvd_three.trans hd
  have hep:=lambda_sq_dvd_three.trans he
  rw [symbol_mul_numerator _ _ d hdp,symbol_mul_numerator _ _ e hep,
    symbol_pow_numerator _ d hdp,symbol_pow_numerator _ e hep,
    symbol_unit_congr_mod_nine u.val d e u.isUnit hdp hep hde,
    CubicRamified.symbol_lambda_congr_mod_nine d e hdp hep hde]

lemma primary_add_nine (d w : Eis) (hd : (3:Eis)∣d-1) :
    (3:Eis)∣d+9*w-1 := by
  convert dvd_add hd (show (3:Eis)∣9*w from ⟨3*w,by ring⟩) using 1 ; ring

def ramifiedResidueAdd (u : Eisˣ) (n : ℕ) (w : Eis)
    (r : AdmissibleResidue (u.val*lambda^n)) : AdmissibleResidue (u.val*lambda^n) :=
  let c:=u.val*lambda^n
  let d:=denominatorRep c r.1+9*w
  ⟨Ideal.Quotient.mk (Ideal.span {3*c}) d,
    (denominatorCondition_congr c _ d (denominatorRep_mk_congr c d)).mpr
      (ramified_denominator_condition u n d (primary_add_nine _ _ r.2.2))⟩

lemma ramifiedResidueAdd_injective (u : Eisˣ) (n : ℕ) (w : Eis) :
    Function.Injective (ramifiedResidueAdd u n w) := by
  intro r q heq
  have hh:=congrArg Subtype.val heq
  change Ideal.Quotient.mk (Ideal.span {3*(u.val*lambda^n)}) (denominatorRep _ r.1+9*w)=
    Ideal.Quotient.mk (Ideal.span {3*(u.val*lambda^n)}) (denominatorRep _ q.1+9*w) at hh
  simp only [map_add,denominatorRep_spec] at hh
  exact Subtype.ext (add_right_cancel hh)

def ramifiedResidueAddEquiv (u : Eisˣ) (n : ℕ) (w : Eis) :
    AdmissibleResidue (u.val*lambda^n) ≃ AdmissibleResidue (u.val*lambda^n) := by
  letI : Finite (AdmissibleResidue (u.val*lambda^n)):=
    finite_admissibleResidue _ (ramifiedElement_ne_zero u n)
  exact Equiv.ofBijective (ramifiedResidueAdd u n w)
    ⟨ramifiedResidueAdd_injective u n w,
      Finite.surjective_of_injective (ramifiedResidueAdd_injective u n w)⟩

lemma residueAdditive_add (h c d e : Eis) :
    residueAdditive h c (d+e)=residueAdditive h c d*residueAdditive h c e := by
  unfold residueAdditive
  rw [map_add,mul_add,add_div,AddChar.map_add_eq_mul]

theorem ramified_arithmetic_additive_eigen (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (w : Eis) :
    residueAdditive h (u.val*lambda^n) (9*w)*arithmeticResidueSum h (u.val*lambda^n)=
      arithmeticResidueSum h (u.val*lambda^n) := by
  let c:=u.val*lambda^n
  have hc:c≠0:=ramifiedElement_ne_zero u n
  have hlevel:(3:Eis)∣c:=ramifiedElement_level u n hn
  have heq:=(ramifiedResidueAddEquiv u n w).tsum_eq
    (fun r : AdmissibleResidue c=>eisEmbedding (symbol c (denominatorRep c r.1))*
      residueAdditive h c (denominatorRep c r.1))
  calc
    _ = ∑' r : AdmissibleResidue c,residueAdditive h c (9*w)*
      (eisEmbedding (symbol c (denominatorRep c r.1))*residueAdditive h c (denominatorRep c r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c (ramifiedResidueAddEquiv u n w r).1))*
        residueAdditive h c (denominatorRep c (ramifiedResidueAddEquiv u n w r).1) := by
      apply tsum_congr
      intro r
      let d:=denominatorRep c r.1
      have hrep : 3*c∣denominatorRep c (ramifiedResidueAdd u n w r).1-(d+9*w):=
        denominatorRep_mk_congr c (d+9*w)
      have hdp:(3:Eis)∣d+9*w-1:=primary_add_nine d w r.2.2
      have hchar : symbol c (denominatorRep c (ramifiedResidueAdd u n w r).1)=symbol c d := by
        rw [row_symbol_congr_modulus c _ (d+9*w) hlevel hdp hrep]
        exact ramified_symbol_congr_mod_nine u n (d+9*w) d hdp r.2.2 ⟨w,by ring⟩
      change _=eisEmbedding (symbol c (denominatorRep c (ramifiedResidueAdd u n w r).1))*
        residueAdditive h c (denominatorRep c (ramifiedResidueAdd u n w r).1)
      rw [hchar,residueAdditive_congr h c _ (d+9*w) hc hrep,residueAdditive_add]
      dsimp only [d]
      ring
    _ = _ := heq

theorem ramified_arithmetic_support (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (hA : arithmeticResidueSum h (u.val*lambda^n)≠0) :
    u.val*lambda^n∣3*h := by
  let c:=u.val*lambda^n
  have hc:c≠0:=ramifiedElement_ne_zero u n
  have hp : ∀w:Eis,residueAdditive h c (9*w)=1:=by
    intro w
    apply mul_right_cancel₀ hA
    rw [ramified_arithmetic_additive_eigen h u n hn w,one_mul]
  let psi:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc
  have hprimitive:psi.IsPrimitive:=GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  by_contra hdiv
  have hne:Ideal.Quotient.mk (Ideal.span {c}) (3*h)≠0:=by
    intro hh
    exact hdiv (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  apply hprimitive hne
  ext x
  obtain ⟨w,rfl⟩:=Ideal.Quotient.mk_surjective x
  simp only [AddChar.mulShift_apply,←map_mul,psi,eisTraceModChar,
    IdealGaussCRT.traceModChar_mk,AddChar.one_apply]
  convert hp w using 1
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_ofNat]
  congr 1
  field_simp
  ; ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_primary_coprime (u : Eisˣ) (n : ℕ) (b : Eis)
    (hb : lambda^2∣b-1) : IsCoprime (3*(u.val*lambda^n)) b := by
  have h3:IsCoprime (3:Eis) b:=(primary_coprime_three b hb).symm
  have hl:IsCoprime lambda b:=coprime_of_dvd_sub_one lambda b
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hb)
  have hu:IsCoprime u.val b:=⟨u.inv,0,by simp⟩
  exact h3.mul_left (hu.mul_left hl.pow_left)

theorem arithmeticResidueSum_ramified_split (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1) :
    arithmeticResidueSum h ((u.val*lambda^n)*b)=
      eisEmbedding (symbol (u.val*lambda^n) b)*
      eisEmbedding (symbol (3*(u.val*lambda^n)) b)*
      arithmeticResidueSum h (u.val*lambda^n)*cubicUnitGaussSum h b :=
  arithmeticResidueSum_coprime_product h _ b (ramifiedElement_ne_zero u n)
    (primary_ne_zero b hb) (ramifiedElement_level u n hn) hb (ramified_primary_coprime u n b hb)

lemma ramifiedElement_absNorm (u : Eisˣ) (n : ℕ) :
    Ideal.absNorm (Ideal.span {u.val*lambda^n})=3^n := by
  have hu:Ideal.span {u.val}=(1:Ideal Eis):=by
    rw [Ideal.one_eq_top]
    exact Ideal.span_singleton_eq_top.mpr u.isUnit
  rw [←Ideal.span_singleton_mul_span_singleton,map_mul,hu,map_one,one_mul,
    ←Ideal.span_singleton_pow,map_pow,absNorm_span_lambda]

lemma three_absNorm : Ideal.absNorm (Ideal.span {(3:Eis)})=9 := by
  rw [←qNat_eq_absNorm_span]
  have he:(3:Eis)=ActualEisensteinCoordinates.eval 3 0:=by
    simp [ActualEisensteinCoordinates.eval]
  rw [he,ShortDraftLatticeCount.qNat,ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem ramified_arithmetic_norm_bound (h : Eis) (hh : h≠0) (u : Eisˣ)
    (n : ℕ) (hn : 2≤n) (hA : arithmeticResidueSum h (u.val*lambda^n)≠0) :
    3^n≤9*Ideal.absNorm (Ideal.span {h}) := by
  have hI:(Ideal.span {h}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hh
  have hN:0<Ideal.absNorm (Ideal.span {h}):=
    Nat.pos_of_ne_zero (fun hz=>hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply Nat.le_of_dvd (by positivity)
  obtain ⟨v,hv⟩:=ramified_arithmetic_support h u n hn hA
  refine ⟨Ideal.absNorm (Ideal.span {v}),?_⟩
  calc
    9*Ideal.absNorm (Ideal.span {h})=Ideal.absNorm (Ideal.span {(3:Eis)*h}):=by
      rw [←Ideal.span_singleton_mul_span_singleton,map_mul,three_absNorm]
    _=Ideal.absNorm (Ideal.span {(u.val*lambda^n)*v}):=by rw [hv]
    _=3^n*Ideal.absNorm (Ideal.span {v}):=by
      rw [←Ideal.span_singleton_mul_span_singleton,map_mul,ramifiedElement_absNorm]

def ramifiedFrequencyBound (h : Eis) : ℕ:=Nat.log 3 (9*Ideal.absNorm (Ideal.span {h}))

theorem arithmeticResidueSum_ramified_index_bound (h : Eis) (hh : h≠0)
    (u : Eisˣ) (n : ℕ) (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1)
    (hA : arithmeticResidueSum h ((u.val*lambda^n)*b)≠0) :
    n≤ ramifiedFrequencyBound h := by
  have ha:arithmeticResidueSum h (u.val*lambda^n)≠0:=by
    intro hz
    apply hA
    rw [arithmeticResidueSum_ramified_split h u n hn b hb,hz,mul_zero,zero_mul]
  exact Nat.le_log_of_pow_le (by decide) (ramified_arithmetic_norm_bound h hh u n hn ha)

theorem arithmeticDirichletTerm_ramified_vanish (s : ℂ) (h : Eis) (hh : h≠0)
    (u : Eisˣ) (n : ℕ) (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1)
    (hout : ramifiedFrequencyBound h<n) :
    arithmeticDirichletTerm s h
      ⟨(u.val*lambda^n)*b,dvd_mul_of_dvd_left (ramifiedElement_level u n hn) b⟩=0 := by
  have hA:arithmeticResidueSum h ((u.val*lambda^n)*b)=0:=by
    by_contra hA
    exact (not_le_of_gt hout) (arithmeticResidueSum_ramified_index_bound h hh u n hn b hb hA)
  simp only [arithmeticDirichletTerm,hA,mul_zero,ite_self]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev NonzeroLevelLower := {c : LevelLower // c.1≠0}

def ramifiedLower (u : Eisˣ) (n : ℕ) (I : GoodIdeal) : Eis :=
  (u.val*lambda^(n+2))*primaryGenerator I.1

lemma ramifiedLower_ne_zero (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    ramifiedLower u n I≠0:=mul_ne_zero (ramifiedElement_ne_zero u (n+2)) I.2

lemma ramifiedLower_level (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    (3:Eis)∣ramifiedLower u n I:=
  dvd_mul_of_dvd_left (ramifiedElement_level u (n+2) (by omega)) _

lemma ramifiedLower_span (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {ramifiedLower u n I}=ramifiedIdeal^(n+2)*I.1 := by
  unfold ramifiedLower
  rw [mul_assoc,Ideal.span_singleton_mul_left_unit u.isUnit,lambdaFactor_generator_span]

def ramifiedLowerMap (p : Eisˣ × ℕ × GoodIdeal) : NonzeroLevelLower:=
  ⟨⟨ramifiedLower p.1 p.2.1 p.2.2,ramifiedLower_level _ _ _⟩,ramifiedLower_ne_zero _ _ _⟩

lemma ramifiedLowerMap_injective : Function.Injective ramifiedLowerMap := by
  rintro ⟨u,n,I⟩ ⟨v,m,J⟩ h
  have hc : ramifiedLower u n I=ramifiedLower v m J:=congrArg (fun c:NonzeroLevelLower=>c.1.1) h
  have hs:=congrArg (fun x:Eis=>Ideal.span {x}) hc
  rw [ramifiedLower_span,ramifiedLower_span] at hs
  have hh:lambdaFactorMap (n+2,I)=lambdaFactorMap (m+2,J):=Subtype.ext hs
  have he:=lambdaFactorMap_bijective.1 hh
  have hnm:n=m:=by have ht:=congrArg Prod.fst he; omega
  have hIJ:I=J:=congrArg Prod.snd he
  subst m
  subst J
  have huv:u=v:=by
    apply Units.ext
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero) I.2)
    simpa only [ramifiedLower,mul_assoc] using hc
  subst v
  rfl

lemma ramifiedLowerMap_surjective : Function.Surjective ramifiedLowerMap := by
  intro c
  let C:NonzeroIdeal:=⟨Ideal.span {c.1.1},Ideal.span_singleton_eq_bot.not.mpr c.2⟩
  obtain ⟨⟨k,I⟩,hCI⟩:=lambdaFactorMap_bijective.2 C
  have hfact:ramifiedIdeal^k*I.1=Ideal.span {c.1.1}:=congrArg Subtype.val hCI
  have hp2:ramifiedIdeal^2∣ramifiedIdeal^k*I.1:=by
    rw [hfact]
    change (Ideal.span {lambda} : Ideal Eis) ^ 2 ∣ _
    rw [Ideal.span_singleton_pow,Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton]
    exact lambda_sq_dvd_three.trans c.1.2
  have hk:2≤k:=by
    by_contra hh
    have hcases:k=0∨k=1:=by omega
    have hnot:=((goodIdeal_iff_not_ramified I.1).mp I.2)
    rcases hcases with rfl|rfl
    · simp only [pow_zero,one_mul] at hp2
      exact hnot ((dvd_pow_self ramifiedIdeal (by decide : (2:ℕ)≠0)).trans hp2)
    · rw [pow_one,pow_two] at hp2
      exact hnot ((mul_dvd_mul_iff_left ramifiedIdeal_prime.ne_zero).mp hp2)
  obtain ⟨n,hn⟩:=Nat.exists_eq_add_of_le hk
  have hk':k=n+2:=by omega
  subst k
  have hspan : Ideal.span {lambda^(n+2)*primaryGenerator I.1}=Ideal.span {c.1.1}:=
    (lambdaFactor_generator_span (n+2) I).trans (by simpa only [Nat.add_comm] using hfact)
  obtain ⟨u,hu⟩:=Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨(u,n,I),Subtype.ext (Subtype.ext ?_)⟩
  change ramifiedLower u n I=c.1.1
  simpa only [ramifiedLower,mul_assoc,mul_comm,mul_left_comm] using hu

def ramifiedLowerEquiv : Eisˣ × ℕ × GoodIdeal ≃ NonzeroLevelLower:=
  Equiv.ofBijective ramifiedLowerMap ⟨ramifiedLowerMap_injective,ramifiedLowerMap_surjective⟩

lemma arithmeticDirichlet_support_nonzero (s : ℂ) (h : Eis) :
    Function.support (arithmeticDirichletTerm s h)⊆{c : LevelLower | c.1≠0} := by
  intro c hc
  change arithmeticDirichletTerm s h c≠0 at hc
  intro hz
  exact hc (by simp only [arithmeticDirichletTerm,hz,ite_true])

theorem arithmeticDirichletSeries_ramified_reindex (s : ℂ) (hs : 2<s.re) (h : Eis) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑'n:ℕ,∑'I:GoodIdeal,
        arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1 := by
  have hsum:Summable (arithmeticDirichletTerm s h):=(arithmeticDirichletTerm_summable_norm s hs h).of_norm
  have hsub:Summable (fun c:NonzeroLevelLower=>arithmeticDirichletTerm s h c.1):=hsum.subtype _
  have hp:=ramifiedLowerEquiv.summable_iff.mpr hsub
  change Summable (fun p:Eisˣ×ℕ×GoodIdeal=>arithmeticDirichletTerm s h (ramifiedLowerMap p).1) at hp
  calc
    _=∑'c:NonzeroLevelLower,arithmeticDirichletTerm s h c.1:=
      (tsum_subtype_eq_of_support_subset (arithmeticDirichlet_support_nonzero s h)).symm
    _=∑'p:Eisˣ×ℕ×GoodIdeal,arithmeticDirichletTerm s h (ramifiedLowerMap p).1:=
      (ramifiedLowerEquiv.tsum_eq _).symm
    _=_:=by
      rw [hp.tsum_prod]
      apply tsum_congr
      intro u
      exact (hp.prod_factor u).tsum_prod

theorem arithmeticDirichletSeries_finite_ramified (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),∑'I:GoodIdeal,
        arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs h]
  apply tsum_congr
  intro u
  apply tsum_eq_sum
  intro n hn
  have hout:ramifiedFrequencyBound h<n+2:=by
    have hh':¬n< ramifiedFrequencyBound h+1:=by simpa only [Finset.mem_range] using hn
    omega
  have hzero (I:GoodIdeal) : arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1=0 :=
    arithmeticDirichletTerm_ramified_vanish s h hh u (n+2) (by omega)
      (primaryGenerator I.1) (primaryGenerator_spec I.1 I.2).2 hout
  simp only [hzero,tsum_zero]

theorem arithmeticDirichletSeries_gauss_expansion (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),∑'I:GoodIdeal,
        ((‖eisEmbedding (ramifiedLower u n I)‖^2:ℝ):ℂ)^(-s)*
          (eisEmbedding (symbol (u.val*lambda^(n+2)) (primaryGenerator I.1))*
           eisEmbedding (symbol (3*(u.val*lambda^(n+2))) (primaryGenerator I.1))*
           arithmeticResidueSum h (u.val*lambda^(n+2))*cubicUnitGaussSum h (primaryGenerator I.1)) := by
  rw [arithmeticDirichletSeries_finite_ramified s hs h hh]
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  apply tsum_congr
  intro I
  rw [arithmeticDirichletTerm, ite_eq_right (ramifiedLowerMap (u,n,I)).2]
  dsimp only [ramifiedLowerMap]
  congr 1
  exact arithmeticResidueSum_ramified_split h u (n+2) (by omega)
    (primaryGenerator I.1) (primaryGenerator_spec I.1 I.2).2

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

theorem cubicUnitGaussSum_phase_shift (h a b : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (hab : IsCoprime (3*a) b) :
    eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*cubicUnitGaussSum h b=
      cubicUnitGaussSum (h*(9*a)) b := by
  have hbt : IsCoprime b (9*a):=by
    rw [show (9:Eis)*a=3*(3*a) by ring]
    exact (primary_coprime_three b hbprimary).mul_right hab.symm
  have heig:=cubicUnitGaussSum_frequency_twist h b (9*a) hb hbprimary hbt
  have hs : symbol a b*symbol (3*a) b*symbol (9*a) b=1 := by
    calc
      _=symbol (a*(3*a)*(9*a)) b:=by
        symm
        calc
          _=symbol (a*(3*a)) b*symbol (9*a) b:=
            symbol_mul_numerator _ _ b hbprimary
          _=_:=by rw [symbol_mul_numerator a (3*a) b hbprimary]
      _=symbol ((3*a)^3) b:=by congr 1; ring
      _=(symbol (3*a) b)^3:=symbol_pow_numerator _ _ hbprimary 3
      _=1:=symbol_cube_of_isCoprime _ _ hbprimary hab
  have he : eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
      eisEmbedding (symbol (9*a) b)=1:=by
    simpa only [map_mul,map_one] using congrArg eisEmbedding hs
  calc
    _=(eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b))*
        (eisEmbedding (symbol (9*a) b)*cubicUnitGaussSum (h*(9*a)) b):=by rw [heig]
    _=(eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
        eisEmbedding (symbol (9*a) b))*cubicUnitGaussSum (h*(9*a)) b:=by ring
    _=_:=by rw [he,one_mul]

def unramifiedCubicGaussSeries (s : ℂ) (h : Eis) : ℂ:=
  ∑'I:GoodIdeal,(Ideal.absNorm I.1:ℂ)^(-s)*cubicUnitGaussSum h (primaryGenerator I.1)

theorem arithmeticDirichletSeries_unramified_gauss (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*arithmeticResidueSum h (u.val*lambda^(n+2))*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))) := by
  rw [arithmeticDirichletSeries_gauss_expansion s hs h hh]
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  rw [unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  rw [eisEmbedding_norm_sq_eq_absNorm_span,Complex.ofReal_natCast,ramifiedLower_span,
    map_mul,map_pow,ramifiedIdeal_absNorm,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  rw [←cubicUnitGaussSum_phase_shift h (u.val*lambda^(n+2)) (primaryGenerator I.1)
    I.2 hp (ramified_primary_coprime u (n+2) _ hp)]
  ring

theorem scatteringCoefficient_unramified_gauss (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    scatteringCoefficient s h=
      (∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*arithmeticResidueSum h (u.val*lambda^(n+2))*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient,arithmeticDirichletSeries_unramified_gauss s hs h hh]

end

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

theorem cubicUnitGaussSum_cube_shift (h b t : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (hbt : IsCoprime b t) :
    cubicUnitGaussSum (h*t^3) b=cubicUnitGaussSum h b := by
  have heig:=cubicUnitGaussSum_frequency_twist h b (t^3) hb hbprimary hbt.pow_right
  have hs : symbol (t^3) b=1:=by
    rw [symbol_pow_numerator t b hbprimary 3]
    exact symbol_cube_of_isCoprime t b hbprimary hbt.symm
  simpa only [hs,map_one,one_mul] using heig

theorem unramifiedCubicGaussSeries_neg (s : ℂ) (h : Eis) :
    unramifiedCubicGaussSeries s (-h)=unramifiedCubicGaussSeries s h := by
  apply tsum_congr
  intro I
  congr 1
  have hc : IsCoprime (primaryGenerator I.1) (-1:Eis):=⟨0,-1,by ring⟩
  simpa only [show (-1:Eis)^3=-1 by ring,mul_neg_one] using cubicUnitGaussSum_cube_shift h (primaryGenerator I.1) (-1) I.2
    (primaryGenerator_spec I.1 I.2).2 hc

theorem unramifiedCubicGaussSeries_lambda_pow (s : ℂ) (h : Eis) (n : ℕ) :
    unramifiedCubicGaussSeries s (h*lambda^n)=
      unramifiedCubicGaussSeries s (h*lambda^(n%3)) := by
  apply tsum_congr
  intro I
  congr 1
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  have hl:IsCoprime lambda (primaryGenerator I.1):=
    coprime_of_dvd_sub_one lambda _ ((show lambda∣lambda^2 from ⟨lambda,by ring⟩).trans hp)
  have he:lambda^n=lambda^(n%3)*(lambda^(n/3))^3:=by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [he,←mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.2 hp hl.symm.pow_right

theorem unramifiedCubicGaussSeries_lambda_cube (s : ℂ) (h : Eis) :
    unramifiedCubicGaussSeries s (h*lambda^3)=unramifiedCubicGaussSeries s h := by
  simpa using unramifiedCubicGaussSeries_lambda_pow s h 3

theorem unit_eq_sign_omega (u : Eisˣ) :
    ∃j:Fin 3,(u:Eis)=omega^j.val ∨ (u:Eis)=-(omega^j.val) := by
  let ζ:=IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η:Eisˣ:=(ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη:(η:Eis)=omega:=rfl
  have hlist:u∈([1,-1,η,-η,η^2,-η^2]:List Eisˣ):=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h|h|h|h|h|h
  · exact ⟨0,Or.inl (by simp [h])⟩
  · exact ⟨0,Or.inr (by simp [h])⟩
  · exact ⟨1,Or.inl (by simp [h,hη])⟩
  · exact ⟨1,Or.inr (by simp [h,hη])⟩
  · exact ⟨2,Or.inl (by simp only [h,Units.val_pow_eq_pow_val,hη];rfl)⟩
  · exact ⟨2,Or.inr (by simp only [h,Units.val_neg,Units.val_pow_eq_pow_val,hη];rfl)⟩

theorem unramifiedCubicGaussSeries_nine_family (h : Eis) (u : Eisˣ) (n : ℕ) :
    ∃j k:Fin 3,∀s:ℂ,
      unramifiedCubicGaussSeries s (h*(9*((u:Eis)*lambda^n)))=
        unramifiedCubicGaussSeries s (h*omega^j.val*lambda^k.val) := by
  have hl:lambda^2=-3*omega:=by
    have hw:omega^2=-omega-1:=by
      have h3:omega^3=1:=omega_primitive.pow_eq_one
      have h1:omega≠1:=omega_primitive.ne_one (by decide)
      have hp:(omega-1)*(omega^2+omega+1)=0:=by linear_combination h3
      have hz:omega^2+omega+1=0:=(mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr h1)
      linear_combination hz
    change (omega-1)^2=-3*omega
    linear_combination hw
  have h9:(9:Eis)=omega*lambda^4:=by
    calc
      _=9*omega^3:=by rw [omega_primitive.pow_eq_one];ring
      _=omega*((-3*omega)^2):=by ring
      _=omega*((lambda^2)^2):=by rw [hl]
      _=omega*lambda^4:=by ring
  let ζ:=IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η:Eisˣ:=(ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη:(η:Eis)=omega:=rfl
  obtain ⟨j,hj⟩:=unit_eq_sign_omega (η*u)
  refine ⟨j,⟨(n+4)%3,Nat.mod_lt _ (by decide)⟩,?_⟩
  intro s
  have he:h*(9*((u:Eis)*lambda^n))=(h*((η*u:Eisˣ):Eis))*lambda^(n+4):=by
    rw [h9,Units.val_mul,hη,pow_add]
    ring
  rw [he,unramifiedCubicGaussSeries_lambda_pow]
  rcases hj with hj|hj
  · rw [hj]
  · rw [hj]
    simpa only [mul_neg,neg_mul] using
      unramifiedCubicGaussSeries_neg s (h*omega^j.val*lambda^((n+4)%3))

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reciprocity.KubotaCharacter -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

def rationalEmbedding : SL(2,ℤ)→*SL(2,ActualEisensteinCubic.O) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ActualEisensteinCubic.O)

def levelThreeConjugate (g : SL(2,ActualEisensteinCubic.O)) (M : levelThree) : levelThree :=
  ⟨g*(M:SL(2,ActualEisensteinCubic.O))*g⁻¹,by
    change Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)})) _=1
    rw [map_mul,map_mul,map_inv,M.property,mul_one,mul_inv_cancel]⟩

lemma levelThree_bottom_primary (M : levelThree) : lambda^2∣(M:SL(2,ActualEisensteinCubic.O)) 1 1-1 :=
  lambda_sq_dvd_three.trans (by simpa using levelThree_entry M 1 1)

lemma value_inverse_formula (M : levelThree) :
    value M⁻¹=symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
  have hd := levelThree_bottom_primary M
  change symbol (((M:SL(2,ActualEisensteinCubic.O))⁻¹) 1 0) (((M:SL(2,ActualEisensteinCubic.O))⁻¹) 0 0)=_
  simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  exact symbol_neg_numerator _ _ hd

lemma value_upper_formula (M : levelThree) :
    value M=symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
  have hd := levelThree_bottom_primary M
  have hdet : (M:SL(2,ActualEisensteinCubic.O)) 0 0*(M:SL(2,ActualEisensteinCubic.O)) 1 1-
      (M:SL(2,ActualEisensteinCubic.O)) 0 1*(M:SL(2,ActualEisensteinCubic.O)) 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (M:SL(2,ActualEisensteinCubic.O)).property
  have hprod : symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)=1 := by
    rw [←symbol_mul_numerator _ _ _ hd]
    calc
      _ = symbol (-1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
        apply symbol_congr
        refine ⟨(M:SL(2,ActualEisensteinCubic.O)) 0 0,?_⟩
        linear_combination -hdet
      _ = 1 := symbol_neg_one _ hd
  have hinv : value M*symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)=1 := by
    rw [←value_inverse_formula,←value_mul,mul_inv_cancel,value_one]
  calc
    value M = value M*1 := by rw [mul_one]
    _ = value M*(symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)) := by rw [hprod]
    _ = symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      (value M*symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)) := by ring
    _ = _ := by rw [hinv,mul_one]

theorem value_conjugate_S (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding ModularGroup.S) M)=value M := by
  rw [value_upper_formula M]
  change symbol (((rationalEmbedding ModularGroup.S)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.S)⁻¹) 1 0)
    (((rationalEmbedding ModularGroup.S)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.S)⁻¹) 0 0)=_
  simp only [rationalEmbedding,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_inv,ModularGroup.coe_S,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  simpa using symbol_neg_numerator ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) (levelThree_bottom_primary M)

theorem complexCharacter_conjugate_S (M : levelThree) :
    complexCharacter (levelThreeConjugate (rationalEmbedding ModularGroup.S) M)=complexCharacter M :=
  congrArg ConcreteTraceCRT.eisEmbedding (value_conjugate_S M)

end CubicKubota

namespace CubicJacobiGlobal
open ActualEisensteinCubic

theorem symbol_shift_by_self (c a : ActualEisensteinCubic.O) (ha : lambda^2∣a-1) (hc : (3:ActualEisensteinCubic.O)∣c) :
    symbol c (a+c)=symbol c a := by
  have hA : lambda^2∣a+c-1 := by
    convert dvd_add ha (lambda_sq_dvd_three.trans hc) using 1 ; ring
  calc
    symbol c (a+c)=symbol (-a) (a+c) := by
      apply symbol_congr
      refine ⟨1,?_⟩
      ring
    _ = symbol a (a+c) := symbol_neg_numerator a (a+c) hA
    _ = symbol (a+c) a := symbol_reciprocity a (a+c) (primary_ne_zero a ha)
      (primary_ne_zero (a+c) hA) ha hA
    _ = symbol c a := by
      apply symbol_congr
      refine ⟨1,?_⟩
      ring
end CubicJacobiGlobal

namespace CubicKubota
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

theorem value_conjugate_T (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding ModularGroup.T) M)=value M := by
  change symbol (((rationalEmbedding ModularGroup.T)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.T)⁻¹) 1 0)
    (((rationalEmbedding ModularGroup.T)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.T)⁻¹) 0 0)=_
  simp only [rationalEmbedding,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_inv,ModularGroup.coe_T,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  simpa [value] using symbol_shift_by_self ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 0 0)
    (levelThree_primary M) (levelThree_lower M)

lemma levelThreeConjugate_one (M : levelThree) : levelThreeConjugate 1 M=M := by
  apply Subtype.ext
  simp [levelThreeConjugate]

lemma levelThreeConjugate_mul (g h : SL(2,ActualEisensteinCubic.O)) (M : levelThree) :
    levelThreeConjugate (g*h) M=levelThreeConjugate g (levelThreeConjugate h M) := by
  apply Subtype.ext
  simp [levelThreeConjugate,mul_assoc]

def characterConjugationStabilizer : Subgroup (SL(2,ActualEisensteinCubic.O)) where
  carrier g := ∀M : levelThree,value (levelThreeConjugate g M)=value M
  one_mem' M := by rw [levelThreeConjugate_one]
  mul_mem' hg hh M := by rw [levelThreeConjugate_mul,hg,hh]
  inv_mem' {g} hg M := by
    have h := hg (levelThreeConjugate g⁻¹ M)
    rw [←levelThreeConjugate_mul,mul_inv_cancel,levelThreeConjugate_one] at h
    exact h.symm

theorem value_conjugate_rational (g : SL(2,ℤ)) (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding g) M)=value M := by
  have htop : characterConjugationStabilizer.comap rationalEmbedding=⊤ := by
    apply top_unique
    rw [←SpecialLinearGroup.SL2Z_generators]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (rfl|rfl)
    · exact value_conjugate_S
    · exact value_conjugate_T
  have hg : g∈characterConjugationStabilizer.comap rationalEmbedding := by rw [htop];trivial
  exact hg M

theorem complexCharacter_conjugate_rational (g : SL(2,ℤ)) (M : levelThree) :
    complexCharacter (levelThreeConjugate (rationalEmbedding g) M)=complexCharacter M :=
  congrArg ConcreteTraceCRT.eisEmbedding (value_conjugate_rational g M)

end CubicKubota
end

open scoped BigOperators Classical
namespace CubicJacobiGlobal
open ActualEisensteinCubic
open CubicRamified
open CompletedGauss hiding O

def rationalPrimary (n : ℕ) : ActualEisensteinCubic.O := if n%3=1 then (n:ActualEisensteinCubic.O) else -(n:ActualEisensteinCubic.O)

lemma rationalPrimary_coord (n : ℕ) (hn : ¬3∣n) : ∃A : ℤ,rationalPrimary n=primaryCoord A 0 := by
  have hm : n%3=1 ∨ n%3=2 := by
    have hl := Nat.mod_lt n (by decide : 0<3)
    have h0 : n%3≠0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
    omega
  rcases hm with hm|hm
  · refine ⟨(n/3:ℕ),?_⟩
    have he : n=1+3*(n/3) := by omega
    rw [rationalPrimary,ite_eq_left hm,primaryCoord_eq]
    conv_lhs => rw [he]
    simp only [Int.cast_natCast,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,]
    ring
  · refine ⟨-((n/3:ℕ):ℤ)-1,?_⟩
    have he : n=2+3*(n/3) := by omega
    rw [rationalPrimary,ite_eq_right (by omega),primaryCoord_eq]
    conv_lhs => rw [he]
    simp only [Int.cast_sub,Int.cast_neg,Int.cast_natCast,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,]
    ring

lemma rationalPrimary_primary (n : ℕ) (hn : ¬3∣n) : lambda^2∣rationalPrimary n-1 := by
  obtain ⟨A,hA⟩ := rationalPrimary_coord n hn
  rw [hA]
  exact primaryCoord_primary A 0

lemma rationalPrimary_denominator (x : ActualEisensteinCubic.O) (n : ℕ) : symbol x (rationalPrimary n)=symbol x (n:ActualEisensteinCubic.O) := by
  unfold rationalPrimary
  split_ifs
  · rfl
  · simp only [symbol,Ideal.span_singleton_neg]

lemma rationalPrimary_numerator (m n : ℕ) (hn : ¬3∣n) :
    symbol (rationalPrimary m) (rationalPrimary n)=symbol (m:ActualEisensteinCubic.O) (rationalPrimary n) := by
  change symbol (if m%3=1 then (m:ActualEisensteinCubic.O) else -(m:ActualEisensteinCubic.O)) (rationalPrimary n)=_
  split_ifs
  · rfl
  · exact symbol_neg_numerator _ _ (rationalPrimary_primary n hn)

lemma rational_symbol_mul (a b n : ℕ) (hn : ¬3∣n) :
    symbol ((a*b:ℕ):ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol (a:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)*symbol (b:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O) := by
  rw [←rationalPrimary_denominator _ n,←rationalPrimary_denominator (a:ActualEisensteinCubic.O) n,
    ←rationalPrimary_denominator (b:ActualEisensteinCubic.O) n,Nat.cast_mul]
  exact symbol_mul_numerator _ _ _ (rationalPrimary_primary n hn)

lemma rational_symbol_three (n : ℕ) (hn : ¬3∣n) : symbol (3:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
  rw [←rationalPrimary_denominator _ n]
  obtain ⟨A,hA⟩ := rationalPrimary_coord n hn
  rw [hA]
  have hprimary := primaryCoord_primary A 0
  have hthree : (3:ActualEisensteinCubic.O)=-((1+2*omega)^2) := by
    have hw : omega^2=-omega-1 := by
      change (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger^2=
        -(IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger-1
      exact IsCyclotomicExtension.Rat.Three.eta_sq (IsCyclotomicExtension.zeta_spec 3 ℚ K)
    linear_combination 4*hw
  have htrace := symbol_traceLambda_eq_linearRay (primaryCoord A 0) hprimary
  change symbol (1+2*omega) (primaryCoord A 0)=_ at htrace
  rw [hthree,symbol_neg_numerator _ _ hprimary,symbol_pow_numerator _ _ hprimary,
    htrace,linearRay_primaryCoord]
  simp

lemma rational_symbol_reciprocity (m n : ℕ) (hm : ¬3∣m) (hn : ¬3∣n) :
    symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol (n:ActualEisensteinCubic.O) (m:ActualEisensteinCubic.O) := by
  calc
    _ = symbol (rationalPrimary m) (rationalPrimary n) := by
      rw [rationalPrimary_numerator m n hn,rationalPrimary_denominator]
    _ = symbol (rationalPrimary n) (rationalPrimary m) :=
      symbol_reciprocity _ _ (primary_ne_zero _ (rationalPrimary_primary m hm))
        (primary_ne_zero _ (rationalPrimary_primary n hn))
        (rationalPrimary_primary m hm) (rationalPrimary_primary n hn)
    _ = _ := by rw [rationalPrimary_numerator n m hm,rationalPrimary_denominator]

lemma rational_symbol_mod (m n : ℕ) : symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol ((m%n:ℕ):ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O) := by
  apply symbol_congr
  refine ⟨(m/n:ℕ),?_⟩
  have he : m=m%n+n*(m/n) := (Nat.mod_add_div m n).symm
  have hh : (m:ActualEisensteinCubic.O)=(m%n:ℕ)+ (n:ActualEisensteinCubic.O)*(m/n:ℕ) := by exact_mod_cast he
  linear_combination hh

theorem rational_symbol_eq_one (n : ℕ) (hn : ¬3∣n) (m : ℕ) (hmn : Nat.Coprime m n) :
    symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hn1 : n=1
    · subst n
      simpa only [Nat.cast_one] using symbol_one (m:ActualEisensteinCubic.O)
    have hn0 : 0<n := Nat.pos_of_ne_zero (fun h => hn (by rw [h];exact dvd_zero 3))
    have hsmall : ∀r : ℕ,r<n → Nat.Coprime r n → symbol (r:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
      intro r
      induction r using Nat.strong_induction_on with
      | h r ihr =>
        intro hrn hcop
        by_cases hr0 : r=0
        · subst r
          have : n=1 := by simpa using hcop
          exact False.elim (hn1 this)
        by_cases hr3 : 3∣r
        · have hquot : r/3< r := Nat.div_lt_self (Nat.pos_of_ne_zero hr0) (by decide)
          have hfactor : r=3*(r/3) := (Nat.mul_div_cancel' hr3).symm
          have hqc : Nat.Coprime (r/3) n := hcop.of_dvd_left (Nat.div_dvd_of_dvd hr3)
          rw [hfactor,rational_symbol_mul _ _ n hn]
          norm_num only [Nat.cast_ofNat]
          rw [rational_symbol_three n hn,one_mul]
          exact ihr (r/3) hquot (lt_trans hquot hrn) hqc
        · rw [rational_symbol_reciprocity r n hr3 hn]
          exact ih r hrn hr3 n hcop.symm
    rw [rational_symbol_mod]
    apply hsmall (m%n) (Nat.mod_lt m hn0)
    change Nat.gcd (m%n) n=1
    rw [←Nat.gcd_rec n m]
    exact hmn.symm

end CubicJacobiGlobal

section

open scoped BigOperators Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic

lemma primary_int_natAbs_not_three (a : ℤ) (ha : lambda^2∣(a:ActualEisensteinCubic.O)-1) : ¬3∣a.natAbs := by
  intro h
  have hInt : (3:ℤ)∣a := Int.natCast_dvd.mpr h
  have hO : (3:ActualEisensteinCubic.O)∣(a:ActualEisensteinCubic.O) := by
    rcases hInt with ⟨b,hb⟩
    refine ⟨(b:ActualEisensteinCubic.O),?_⟩
    simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) hb
  have hL2 : lambda∣lambda^2 := dvd_pow_self _ (by decide : (2:ℕ)≠0)
  have hLa := (hL2.trans lambda_sq_dvd_three).trans hO
  have hLa1 := hL2.trans ha
  have h1 : lambda∣(1:ActualEisensteinCubic.O) := by
    convert dvd_sub hLa hLa1 using 1 ; ring
  exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one h1)

theorem integer_symbol_eq_one (c a : ℤ) (ha : lambda^2∣(a:ActualEisensteinCubic.O)-1)
    (hcop : Nat.Coprime c.natAbs a.natAbs) : symbol (c:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=1 := by
  have hnum : symbol (c:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=symbol (c.natAbs:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O) := by
    rcases Int.natAbs_eq c with h|h
    · have he : (c:ActualEisensteinCubic.O)=(c.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact congrArg (fun z : ActualEisensteinCubic.O => symbol z (a:ActualEisensteinCubic.O)) he
    · have he : (c:ActualEisensteinCubic.O)=-(c.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact (congrArg (fun z : ActualEisensteinCubic.O => symbol z (a:ActualEisensteinCubic.O)) he).trans
        (symbol_neg_numerator _ _ ha)
  rw [hnum]
  have hden : symbol (c.natAbs:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=symbol (c.natAbs:ActualEisensteinCubic.O) (a.natAbs:ActualEisensteinCubic.O) := by
    rcases Int.natAbs_eq a with h|h
    · have he : (a:ActualEisensteinCubic.O)=(a.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact congrArg (symbol (c.natAbs:ActualEisensteinCubic.O)) he
    · have he : (a:ActualEisensteinCubic.O)=-(a.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      rw [he]
      simp only [symbol,Ideal.span_singleton_neg]
  rw [hden]
  exact rational_symbol_eq_one a.natAbs (primary_int_natAbs_not_three a ha) c.natAbs hcop
end CubicJacobiGlobal

namespace CubicKubota

section
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

theorem value_rational_intersection (g : SL(2,ℤ)) (hg : rationalEmbedding g∈levelThree) :
    value ⟨rationalEmbedding g,hg⟩=1 := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hcop : IsCoprime (g 1 0) (g 0 0) := by
    refine ⟨-(g 0 1),g 1 1,?_⟩
    linear_combination hdet
  have hp := levelThree_primary ⟨rationalEmbedding g,hg⟩
  change lambda^2∣((g 0 0:ℤ):ActualEisensteinCubic.O)-1 at hp
  change symbol ((g 1 0:ℤ):ActualEisensteinCubic.O) ((g 0 0:ℤ):ActualEisensteinCubic.O)=1
  exact integer_symbol_eq_one (g 1 0) (g 0 0) hp (Int.isCoprime_iff_nat_coprime.mp hcop)

theorem complexCharacter_rational_intersection (g : SL(2,ℤ)) (hg : rationalEmbedding g∈levelThree) :
    complexCharacter ⟨rationalEmbedding g,hg⟩=1 := by
  change ConcreteTraceCRT.eisEmbedding (value ⟨rationalEmbedding g,hg⟩)=1
  rw [value_rational_intersection g hg,map_one]

end

open ActualEisensteinCubic

def levelTwo : Subgroup (SL(2,ActualEisensteinCubic.O)) where
  carrier g := ∃n : levelThree,∃r : SL(2,ℤ),(n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=g
  one_mem' := ⟨1,1,by simp⟩
  mul_mem' := by
    rintro g h ⟨n,r,rfl⟩ ⟨m,s,rfl⟩
    refine ⟨n*levelThreeConjugate (rationalEmbedding r) m,r*s,?_⟩
    simp [levelThreeConjugate,map_mul,mul_assoc]
  inv_mem' := by
    rintro g ⟨n,r,rfl⟩
    refine ⟨levelThreeConjugate (rationalEmbedding r⁻¹) n⁻¹,r⁻¹,?_⟩
    simp [levelThreeConjugate,map_inv,mul_assoc]

lemma levelThree_le_levelTwo : levelThree≤levelTwo := by
  intro g hg
  exact ⟨⟨g,hg⟩,1,by simp⟩

lemma rational_mem_levelTwo (r : SL(2,ℤ)) : rationalEmbedding r∈levelTwo :=
  ⟨1,r,by simp⟩

lemma levelTwo_eq_sup : levelTwo=levelThree⊔rationalEmbedding.range := by
  apply le_antisymm
  · rintro g ⟨n,r,rfl⟩
    exact Subgroup.mul_mem _
      ((show levelThree≤levelThree⊔rationalEmbedding.range from le_sup_left) n.property)
      ((show rationalEmbedding.range≤levelThree⊔rationalEmbedding.range from le_sup_right) ⟨r,rfl⟩)
  · apply sup_le levelThree_le_levelTwo
    rintro g ⟨r,rfl⟩
    exact rational_mem_levelTwo r

lemma complexCharacter_product_well_defined (n m : levelThree) (r s : SL(2,ℤ))
    (h : (n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=(m:SL(2,ActualEisensteinCubic.O))*rationalEmbedding s) :
    complexCharacter n=complexCharacter m := by
  have he : ((m⁻¹*n:levelThree):SL(2,ActualEisensteinCubic.O))=rationalEmbedding (s*r⁻¹) := by
    have hh := congrArg (fun g : SL(2,ActualEisensteinCubic.O)=>(m:SL(2,ActualEisensteinCubic.O))⁻¹*g*(rationalEmbedding r)⁻¹) h
    simpa [map_mul,map_inv,mul_assoc] using hh
  have hm : rationalEmbedding (s*r⁻¹)∈levelThree := he ▸ (m⁻¹*n).property
  have hv : complexCharacter (m⁻¹*n)=1 := by
    have he' : (m⁻¹*n:levelThree)=⟨rationalEmbedding (s*r⁻¹),hm⟩ := Subtype.ext he
    rw [he']
    exact complexCharacter_rational_intersection (s*r⁻¹) hm
  calc
    complexCharacter n=complexCharacter (m*(m⁻¹*n)) := by rw [mul_inv_cancel_left]
    _ = complexCharacter m*complexCharacter (m⁻¹*n) := map_mul _ _ _
    _ = complexCharacter m := by rw [hv,mul_one]

def levelTwoLeft (g : levelTwo) : levelThree := g.property.choose

def levelTwoRight (g : levelTwo) : SL(2,ℤ) := g.property.choose_spec.choose

lemma levelTwo_product (g : levelTwo) :
    (levelTwoLeft g:SL(2,ActualEisensteinCubic.O))*rationalEmbedding (levelTwoRight g)=(g:SL(2,ActualEisensteinCubic.O)) :=
  g.property.choose_spec.choose_spec

def levelTwoValue (g : levelTwo) : ℂ := complexCharacter (levelTwoLeft g)

lemma levelTwoValue_of_product (g : levelTwo) (n : levelThree) (r : SL(2,ℤ))
    (h : (n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=(g:SL(2,ActualEisensteinCubic.O))) : levelTwoValue g=complexCharacter n :=
  complexCharacter_product_well_defined (levelTwoLeft g) n (levelTwoRight g) r
    ((levelTwo_product g).trans h.symm)

def levelTwoComplexCharacter : levelTwo→*ℂ where
  toFun := levelTwoValue
  map_one' := by
    rw [levelTwoValue_of_product 1 1 1 (by simp),map_one]
  map_mul' g h := by
    have hp :
        ((levelTwoLeft g*levelThreeConjugate (rationalEmbedding (levelTwoRight g)) (levelTwoLeft h):levelThree):SL(2,ActualEisensteinCubic.O))*
          rationalEmbedding (levelTwoRight g*levelTwoRight h)=((g*h:levelTwo):SL(2,ActualEisensteinCubic.O)) := by
      simp only [Subgroup.coe_mul,levelThreeConjugate,map_mul]
      simp only [mul_assoc,inv_mul_cancel_left]
      rw [←levelTwo_product g,←levelTwo_product h]
      group
    rw [levelTwoValue_of_product (g*h) _ _ hp,map_mul,complexCharacter_conjugate_rational]
    rfl

lemma levelTwoComplexCharacter_restrict (n : levelThree) :
    levelTwoComplexCharacter ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩=complexCharacter n := by
  exact levelTwoValue_of_product _ n 1 (by simp)

lemma levelTwoComplexCharacter_rational (r : SL(2,ℤ)) :
    levelTwoComplexCharacter ⟨rationalEmbedding r,rational_mem_levelTwo r⟩=1 := by
  exact (levelTwoValue_of_product _ 1 r (by simp)).trans (map_one _)

lemma levelTwoComplexCharacter_cube (g : levelTwo) : levelTwoComplexCharacter g^3=1 :=
  complexCharacter_cube (levelTwoLeft g)

lemma norm_levelTwoComplexCharacter (g : levelTwo) : ‖levelTwoComplexCharacter g‖=1 :=
  norm_complexCharacter (levelTwoLeft g)

end CubicKubota
end

namespace CubicKubota

open scoped Classical MatrixGroups
open ActualEisensteinCubic
open CubicEisenstein

theorem globalKubotaKernel_conjugate (g : levelTwo) (k : SL(2,ActualEisensteinCubic.O))
    (hk : k∈globalKubotaKernel) :
    (g:SL(2,ActualEisensteinCubic.O))*k*(g:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel := by
  obtain ⟨hk3,hkv⟩ := (globalKubotaKernel_mem k).mp hk
  let n : levelThree := ⟨k,hk3⟩
  let n2 : levelTwo := ⟨k,levelThree_le_levelTwo hk3⟩
  let cn := levelThreeConjugate (g:SL(2,ActualEisensteinCubic.O)) n
  refine (globalKubotaKernel_mem _).mpr ⟨cn.property,?_⟩
  change complexCharacter cn=1
  rw [←levelTwoComplexCharacter_restrict cn]
  have he : (⟨(cn:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo cn.property⟩:levelTwo)=g*n2*g⁻¹ :=
    Subtype.ext rfl
  rw [he,map_mul,map_mul]
  have hn : levelTwoComplexCharacter n2=1 :=
    (levelTwoComplexCharacter_restrict n).trans hkv
  rw [hn,mul_one,←map_mul,mul_inv_cancel,map_one]

def kernelInLevelTwo : Subgroup levelTwo := globalKubotaKernel.comap levelTwo.subtype

instance kernelInLevelTwo_normal : kernelInLevelTwo.Normal where
  conj_mem k hk g := globalKubotaKernel_conjugate g k hk

theorem globalKubotaKernel_rational_conjugate_iff (r : SL(2,ℤ)) (k : SL(2,ActualEisensteinCubic.O)) :
    rationalEmbedding r*k*(rationalEmbedding r)⁻¹∈globalKubotaKernel ↔
      k∈globalKubotaKernel := by
  constructor
  · intro h
    have hh := globalKubotaKernel_conjugate
      (⟨rationalEmbedding r⁻¹,rational_mem_levelTwo r⁻¹⟩:levelTwo) _ h
    simpa [map_inv,mul_assoc] using hh
  · exact globalKubotaKernel_conjugate
      (⟨rationalEmbedding r,rational_mem_levelTwo r⟩:levelTwo) k

end CubicKubota

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein

def cuspHeightCompact (a b : ℝ) : Set HyperbolicSpace :=
  cuspCoordinateLift '' (Set.Icc a b ×ˢ Metric.closedBall (0:ℂ) (∑i,‖periodBasis i‖))

lemma cuspHeightCompact_isCompact (a b : ℝ) (ha : 0<a) : IsCompact (cuspHeightCompact a b) := by
  apply (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
  intro q hq
  exact (cuspCoordinateLift_continuousAt q (ha.trans_le hq.1.1)).continuousWithinAt

lemma cuspPeriodStrip_subset_heightCompact (a b : ℝ) (_ha : 0<a) :
    cuspPeriodStrip a b⊆cuspHeightCompact a b := by
  intro w hw
  refine ⟨(hyperbolicHeight w,hyperbolicHorizontal w),⟨hw.2,?_⟩,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain _ hw.1
  · rw [←spatialComplexSplit_coordinates,cuspCoordinateLift,
      spatialComplexSplit.symm_apply_apply,euclideanToHyperbolic_coordinates]

lemma cuspPeriodStrip_measure_ne_top_of_pos (a b : ℝ) (ha : 0<a) :
    hyperbolicVolume (cuspPeriodStrip a b)≠(⊤:ℝ≥0∞) := by
  apply ne_of_lt
  exact (measure_mono (cuspPeriodStrip_subset_heightCompact a b ha)).trans_lt
    (cuspHeightCompact_isCompact a b ha).measure_lt_top

theorem cuspPeriodStripFiniteVolume (a b : ℝ) (ha : 0<a) :
    IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
  isFiniteMeasure_restrict.mpr (cuspPeriodStrip_measure_ne_top_of_pos a b ha)

lemma cuspStrip_restrict_le_compact (a b : ℝ) (ha : 0<a) :
    hyperbolicVolume.restrict (cuspPeriodStrip a b)≤
      (1:ℝ≥0∞) • hyperbolicVolume.restrict (cuspHeightCompact a b) := by
  simpa only [one_smul] using
    (Measure.restrict_mono_set hyperbolicVolume (cuspPeriodStrip_subset_heightCompact a b ha))

abbrev CuspHeightStripL2 (a b : ℝ) := Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip a b))

def kernelCuspHeightPullback (a b : ℝ) (ha : 0<a) : KernelQuotientL2→L[ℂ]CuspHeightStripL2 a b :=
  (dominatedComplexL2 (by simp : (1:ℝ≥0∞)≠⊤) (cuspStrip_restrict_le_compact a b ha)).comp
    (kernelCompactPullbackCLM (cuspHeightCompact a b) (cuspHeightCompact_isCompact a b ha))

lemma kernelCuspHeightPullback_ae (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    kernelCuspHeightPullback a b ha F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip a b)]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hfirst := dominatedComplexL2_ae (by simp : (1:ℝ≥0∞)≠⊤) (cuspStrip_restrict_le_compact a b ha)
    (kernelCompactPullbackCLM (cuspHeightCompact a b) (cuspHeightCompact_isCompact a b ha) F)
  have hsecond := (Measure.absolutelyContinuous_of_le_smul (cuspStrip_restrict_le_compact a b ha)).ae_eq
    (kernelCompactPullbackCLM_ae (cuspHeightCompact a b) (cuspHeightCompact_isCompact a b ha) F)
  exact hfirst.trans hsecond

lemma kernelCuspHeight_quasiMeasurePreserving (a b : ℝ) (ha : 0<a) :
    Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) (integralQuotientVolume globalKubotaKernel) := by
  have hcompact : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspHeightCompact a b)) (integralQuotientVolume globalKubotaKernel) :=
    ⟨measurable_integralOrbitProjection _,
      Measure.absolutelyContinuous_of_le_smul (kernelCompactMultiplicity_spec _ (cuspHeightCompact_isCompact a b ha))⟩
  exact ⟨hcompact.measurable,
    ((Measure.absolutelyContinuous_of_le_smul (cuspStrip_restrict_le_compact a b ha)).map
      (measurable_integralOrbitProjection _)).trans hcompact.absolutelyContinuous⟩

def cuspHeightQuotientCompact (a b : ℝ) : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' cuspHeightCompact a b

lemma cuspHeightQuotientCompact_isCompact (a b : ℝ) (ha : 0<a) :
    IsCompact (cuspHeightQuotientCompact a b) :=
  (cuspHeightCompact_isCompact a b ha).image (continuous_integralOrbitProjection _)

lemma cuspPeriodStrip_image_subset (a b : ℝ) (ha : 0<a) :
    integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip a b⊆cuspHeightQuotientCompact a b :=
  Set.image_mono (cuspPeriodStrip_subset_heightCompact a b ha)

def positiveEuclideanStrip (a b : ℝ) : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Icc a b ×ˢ periodDomain)

lemma positiveEuclideanStrip_measurable (a b : ℝ) : MeasurableSet (positiveEuclideanStrip a b) :=
  spatialComplexSplit.measurable (measurableSet_Icc.prod periodDomain_measurable)

lemma positiveEuclideanStrip_positive (a b : ℝ) (ha : 0<a) :
    positiveEuclideanStrip a b⊆euclideanUpperHalf := by
  intro p hp
  exact ha.trans_le hp.1.1

lemma positiveEuclideanStrip_preimage (a b : ℝ) :
    hyperbolicEuclideanCoordinates ⁻¹' positiveEuclideanStrip a b=cuspPeriodStrip a b := by
  ext w
  change spatialComplexSplit (hyperbolicEuclideanCoordinates w)∈(Set.Icc a b ×ˢ periodDomain) ↔ _
  rw [spatialComplexSplit_coordinates]
  exact and_comm

lemma cuspPeriodStrip_integral_coordinates_of_pos (a b : ℝ) (ha : 0<a)
    (g : HyperbolicSpace→ℂ) (hg : AEStronglyMeasurable g hyperbolicVolume)
    (hint : IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ periodDomain) volume) :
    (∫w in cuspPeriodStrip a b,g w∂hyperbolicVolume)=
      ∫v in Set.Icc a b,(∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3 := by
  have hm := euclideanToHyperbolic_measurePreserving_on (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)
  rw [positiveEuclideanStrip_preimage] at hm
  have hh := hg.mono_measure (Measure.restrict_le_self (s := cuspPeriodStrip a b))
  have he : (∫w in cuspPeriodStrip a b,g w∂hyperbolicVolume)=
      ∫p in positiveEuclideanStrip a b,g (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
    rw [←hm.map_eq] at hh ⊢
    exact integral_map hm.measurable.aemeasurable hh
  rw [he,hyperbolicEuclidean_setIntegral_complex (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map
    (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
    (Set.Icc a b ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : (∫p in positiveEuclideanStrip a b,g (euclideanToHyperbolic p)/(p 2:ℂ)^3)=
      ∫q in Set.Icc a b ×ˢ periodDomain,g (cuspCoordinateLift q)/(q.1:ℂ)^3 := by
    rw [hsplit]
    simp only [positiveEuclideanStrip,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply,
      spatialComplexSplit_fst]
  rw [heq]
  change (∫q in Set.Icc a b ×ˢ periodDomain,
    g (cuspCoordinateLift q)/(q.1:ℂ)^3 ∂((volume : Measure ℝ).prod volume))=_
  rw [setIntegral_prod _ hint]
  congr 1
  ext v
  exact integral_div ((v:ℂ)^3) (fun z => g (cuspCoordinateLift (v,z)))

lemma cuspCoordinateLift_weighted_integrable_of_pos (a b : ℝ) (ha : 0<a)
    (g : HyperbolicSpace→ℂ) (hg : Continuous g) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ periodDomain) volume := by
  let radiusBound : ℝ := ∑i,‖periodBasis i‖
  have hc : ContinuousOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ Metric.closedBall (0:ℂ) radiusBound) := by
    intro q hq
    have hpos : 0<q.1 := ha.trans_le hq.1.1
    exact ((hg.continuousAt.comp (cuspCoordinateLift_continuousAt q hpos)).div
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.pow 3)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousWithinAt
  apply (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
  intro q hq
  refine ⟨hq.1,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain q.2 hq.2

end CubicEisenstein

end

end OAI

end

