module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part012
public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part013

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.TranslatedFourierResidues -/

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
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma period_integral_fourier_translation (f:ℂ→ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)=f z) (h:Eis) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ShortDraftTrace.breveE (cuspFrequency h*b)*
        ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  let g : ℂ→ℂ := fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hg : ∀(n:Eis)(z:ℂ),g (z+3*eisEmbedding n)=g z := by
    intro n z
    dsimp only [g]
    rw [hp,cuspFrequency_negative_period]
  have he (z:ℂ) : f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z)=
      ShortDraftTrace.breveE (cuspFrequency h*b)*g (b+z) := by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · rw [add_comm]
    · congr 1
      ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hg b]

theorem rational_cusp_fourier_right_T (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspFourierPhase h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspFourierPhase h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspFourierPhase h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg),
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
    cuspFourierPhase,hyperbolicHorizontal_upperPoint]
  rw [period_integral_fourier_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) h (n:ℂ)]
  ring

lemma translatedCuspFourier_residue_scaled_of_initial (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspFourierPhase h w∂hyperbolicVolume) :
    translatedCuspFourier h M cubicEisensteinResidue=
      c*translatedCuspFourier h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily h M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := fun s=>c*translatedCuspFamily h N 2 3 (by norm_num) (by norm_num) s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal h M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedCuspFamily_analyticAt_nonreal h N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial h M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial h N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit h M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit h N 2 3 (by norm_num) (by norm_num)).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  dsimp only [f,g] at hv
  dsimp only [Function.comp_def]
  linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hv

lemma translatedCuspFourier_one (h:Eis) (F:KernelQuotientL2) :
    translatedCuspFourier h 1 F=kernelCuspFourier h F := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

lemma translatedCuspFourier_bruhat (h:Eis) (e:Fin 2) (a:Fin 3⊕(Fin 3×Fin 3)) :
    translatedCuspFourier h (rationalLift (rationalBruhatRep (e,a))) cubicEisensteinResidue=
      match a with
      | Sum.inl _=>kernelCuspFourier h cubicEisensteinResidue
      | Sum.inr ab=>ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
        translatedCuspFourier h oppositeSource cubicEisensteinResidue := by
  cases a with
  | inl a =>
    rw [←one_mul (kernelCuspFourier h cubicEisensteinResidue),←translatedCuspFourier_one h]
    apply translatedCuspFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    simp only [map_one,one_smul,one_mul]
  | inr ab =>
    apply translatedCuspFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    change (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex ModularGroup.S •
        (rationalComplex (ModularGroup.T^ab.2.val) • w))*cuspFourierPhase h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)*
        cuspFourierPhase h w∂hyperbolicVolume
    simpa only [map_mul,mul_smul] using
      rational_cusp_fourier_right_T ModularGroup.S ab.2.val h s (by linarith)

def sourceRayPhaseSum (h:Eis) : ℂ :=
  ∑ b:Fin 3,ShortDraftTrace.breveE (cuspFrequency h*(b.val:ℂ))

theorem kernelSourceProjection_residue_fourier (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      (4:ℂ)⁻¹*(kernelCuspFourier h cubicEisensteinResidue+
        sourceRayPhaseSum h*translatedCuspFourier h oppositeSource cubicEisensteinResidue) := by
  rw [kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  change (24:ℂ)⁻¹*(∑i:RationalBruhatIndex,
    translatedCuspFourier h (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=_
  rw [Fintype.sum_prod_type]
  simp_rw [translatedCuspFourier_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_mul]
  change (24:ℂ)⁻¹*((2:ℂ)*(3*kernelCuspFourier h cubicEisensteinResidue+
    3*(sourceRayPhaseSum h*translatedCuspFourier h oppositeSource cubicEisensteinResidue)))=_
  ring

end

section
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_cube (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)^3=1 := by
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  have hp:=cuspFrequency_period h (1:Eis)
  simpa only [map_one,mul_one,one_mul,Nat.cast_ofNat,mul_comm] using hp

lemma sourceRayPhaseSum_formula (h:Eis) :
    sourceRayPhaseSum h=1+ShortDraftTrace.breveE (cuspFrequency h)+
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
  unfold sourceRayPhaseSum
  simp only [Fin.sum_univ_succ,Fin.val_zero,Nat.cast_zero,mul_zero,AddChar.map_zero_eq_one,
    Fin.val_succ,Nat.cast_add,Nat.cast_one,zero_add,mul_one,Fin.sum_univ_zero,add_zero]
  have he : ShortDraftTrace.breveE (cuspFrequency h*(1+1))=
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
    rw [mul_add,mul_one,AddChar.map_add_eq_mul,pow_two]
  rw [he]
  ring

lemma sourceRayPhaseSum_eq (h:Eis) :
    sourceRayPhaseSum h=if ShortDraftTrace.breveE (cuspFrequency h)=1 then 3 else 0 := by
  rw [sourceRayPhaseSum_formula]
  split_ifs with he
  · rw [he]
    norm_num
  · have hc:=sourceRayPhase_cube h
    have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
        (1+ShortDraftTrace.breveE (cuspFrequency h)+ShortDraftTrace.breveE (cuspFrequency h)^2)=0 := by
      linear_combination hc
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)

lemma kernelCuspFourier_residue_horizontal (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ShortDraftTrace.breveE (cuspFrequency h)*kernelCuspFourier h cubicEisensteinResidue := by
  have hh:=translatedCuspFourier_residue_scaled_of_initial h 1 1
    (ShortDraftTrace.breveE (cuspFrequency h)) (by
      intro s hs hi
      have he:=rational_cusp_fourier_right_T (1:SL(2,ℤ)) 1 h s (by linarith)
      have hT (w:HyperbolicSpace) : hyperbolicEisenstein s (rationalComplex ModularGroup.T • w)=hyperbolicEisenstein s w := by
        simpa only [pow_one] using hyperbolicEisenstein_T_pow s 1 w
      simpa only [one_mul,pow_one,map_one,one_smul,Nat.cast_one,mul_one,hT] using he)
  simpa only [translatedCuspFourier_one] using hh

lemma kernelCuspFourier_residue_eq_zero_of_not_horizontal (h:Eis)
    (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    kernelCuspFourier h cubicEisensteinResidue=0 := by
  have he:=kernelCuspFourier_residue_horizontal h
  have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
      kernelCuspFourier h cubicEisensteinResidue=0 := by linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hh)

theorem kernelSourceProjection_residue_fourier_mask (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      if ShortDraftTrace.breveE (cuspFrequency h)=1 then
        (4:ℂ)⁻¹*(kernelCuspFourier h cubicEisensteinResidue+
          3*translatedCuspFourier h oppositeSource cubicEisensteinResidue)
      else 0 := by
  rw [kernelSourceProjection_residue_fourier,sourceRayPhaseSum_eq]
  split_ifs with hh
  · rfl
  · rw [kernelCuspFourier_residue_eq_zero_of_not_horizontal h hh]
    ring

end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma oppositeFrequency_cross_identity (h:Eis) :
    Set.EqOn (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s (3*(9*h)))
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s (3*(9*h))) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt (3*(9*h)) s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspWhittakerHeightFactor s (3*(9*h)))=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num)
      (by norm_num) s hs.1 hs.2,opposite_cusp_fourier_average s (by linarith [hs.1]),
      translatedCuspFamily_opposite_initial (9*h) s hs.1 hs.2]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedCuspFourier_unramified_residue (h:Eis) :
    translatedCuspFourier h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspWhittakerHeightFactor (4/3:ℂ) h := by
  have hh (k:Eis) : Tendsto (fun s:ℂ=>cuspWhittakerHeightFactor s k)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) k)) :=
    (cuspWhittakerHeightFactor_analyticAt k (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl := ((translatedCuspFamily_residue_limit h oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh (3*(9*h)))).comp upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit (3*(9*h)) oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh h)).comp upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) (3*(9*h)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeFrequency_cross_identity h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedCuspFourier h oppositeSource cubicEisensteinResidue*
      cuspWhittakerHeightFactor (4/3:ℂ) (3*(9*h))=
      translatedCuspFourier (3*(9*h)) oppositeSource cubicEisensteinResidue*
        cuspWhittakerHeightFactor (4/3:ℂ) h := tendsto_nhds_unique_of_eventuallyEq hl hr hev
  unfold unramifiedGaussResidue
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff (cuspWhittakerHeightFactor_center_ne_zero (3*(9*h)))).mpr heq

def principalArithmeticResidue (h:Eis) : ℂ :=
  if h=0 then constantArithmeticResidue else nonzeroScatteringResidue h

lemma kernelCuspFourier_principal_residue (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average,principalArithmeticResidue,ite_eq_left rfl,
      cuspWhittakerHeightFactor_zero (4/3) (by norm_num),cuspConstantAverageResidue]
    ring
  · rw [principalArithmeticResidue,ite_eq_right hh,nonzeroScatteringResidue]
    field_simp [cusp_volume_ne_zero,cuspWhittakerHeightFactor_center_ne_zero h]

def sourceArithmeticResidue (h:Eis) : ℂ :=
  if ShortDraftTrace.breveE (cuspFrequency h)=1 then
    (4:ℂ)⁻¹*(principalArithmeticResidue h+
      3*unramifiedGaussResidue (9*h)/((9*Real.sqrt 3/2:ℝ):ℂ))
  else 0

theorem kernelSourceProjection_gauss_residue (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  rw [kernelSourceProjection_residue_fourier_mask,sourceArithmeticResidue]
  split_ifs with hh
  · rw [kernelCuspFourier_principal_residue,translatedCuspFourier_unramified_residue]
    field_simp [cusp_volume_ne_zero]

  · ring

theorem cubicSourceResidualFunction_fourier_average (h:Eis) :
    (∫w in cuspPeriodStrip 5 6,cubicSourceResidualFunction w*cuspFourierPhase h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  rw [←kernelSourceProjection_gauss_residue,kernelCuspFourier_integral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae cubicSourceResidualFunction_represents_projection] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w) hw.symm

lemma unramifiedGaussResidue_zero :
    unramifiedGaussResidue 0=((9*Real.sqrt 3/2:ℝ):ℂ)*constantArithmeticResidue := by
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero (0:Eis))
  have ht:=translatedCuspFourier_unramified_residue (0:Eis)
  simp only [mul_zero] at ht
  rw [←ht,translatedCuspFourier_opposite_zero_residue]
  have hp:=kernelCuspFourier_principal_residue (0:Eis)
  rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average] at hp
  simpa [principalArithmeticResidue] using hp

lemma sourceArithmeticResidue_zero : sourceArithmeticResidue 0=constantArithmeticResidue := by
  rw [sourceArithmeticResidue]
  simp only [cuspFrequency,map_zero,zero_div,AddChar.map_zero_eq_one,
    principalArithmeticResidue,mul_zero,unramifiedGaussResidue_zero,ite_true]
  field_simp [cusp_volume_ne_zero]
  ; ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def horizontalPhaseMultiplier (freq direction : ℂ) : ℂ :=
  (2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))

lemma brevePhase_hasDerivAt (freq z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ShortDraftTrace.breveE (freq*(z+(x:ℂ)*direction)))
      (horizontalPhaseMultiplier freq direction*
        ShortDraftTrace.breveE (freq*(z+(t:ℂ)*direction))) t := by
  have hz : HasDerivAt (fun x : ℝ => freq*(z+(x:ℂ)*direction)) (freq*direction) t := by
    convert (((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const direction).const_add z).const_mul freq using 1 <;>
      simp
  have he := ((hz.add hz.star).const_mul (2*Real.pi*Complex.I)).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp ((2*Real.pi*Complex.I)*
    (freq*(z+(x:ℂ)*direction)+star (freq*(z+(x:ℂ)*direction)))))
    ((2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))*
      Complex.exp ((2*Real.pi*Complex.I)*
        (freq*(z+(t:ℂ)*direction)+star (freq*(z+(t:ℂ)*direction))))) t
  simpa only [Pi.add_apply,mul_comm] using he

lemma horizontalPhaseMultiplier_norm (freq direction : ℂ) :
    ‖horizontalPhaseMultiplier freq direction‖≤4*Real.pi*‖freq‖*‖direction‖ := by
  have hc : ‖(2*Real.pi*Complex.I:ℂ)‖=2*Real.pi := by
    norm_num [norm_mul,abs_of_pos Real.pi_pos]
  unfold horizontalPhaseMultiplier
  rw [norm_mul,hc]
  calc
    _ ≤ (2*Real.pi)*(‖freq*direction‖+‖star (freq*direction)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [norm_star,norm_mul];ring

lemma horizontalPhaseMultiplier_wirtinger (freq : ℂ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq 1+
      Complex.I*horizontalPhaseMultiplier freq Complex.I)=2*Real.pi*Complex.I*star freq := by
  simp only [horizontalPhaseMultiplier,mul_one,star_mul,Complex.star_def,
    Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ring

lemma norm_mul_exp_neg_bound (a r : ℝ) (ha : 0<a) :
    r*Real.exp (-a*r)≤(2/a)*Real.exp (-(a/2)*r) := by
  have hbase := Real.add_one_le_exp ((a/2)*r)
  have hr : r≤(2/a)*Real.exp ((a/2)*r) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith
  calc
    _ ≤ ((2/a)*Real.exp ((a/2)*r))*Real.exp (-a*r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

lemma summable_norm_mul_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => ‖cuspFrequency h‖*Real.exp (-a*‖cuspFrequency h‖)) := by
  apply Summable.of_nonneg_of_le (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun h => norm_mul_exp_neg_bound a _ ha)
  exact (summable_exp_neg_cuspFrequency_norm (a/2) (half_pos ha)).mul_left (2/a)

local notation "O" => ActualEisensteinCubic.O

def cubicResidualDirectionalTerm (h : ActualEisensteinCubic.O) (v : ℝ) (z direction : ℂ) : ℂ :=
  horizontalPhaseMultiplier (cuspFrequency h) direction*cubicResidualNonzeroTerm h (v,z)

lemma cubicResidualNonzeroTerm_horizontal_hasDerivAt (h : ActualEisensteinCubic.O) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualNonzeroTerm h (v,z+(x:ℂ)*direction))
      (cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (brevePhase_hasDerivAt (cuspFrequency h) z direction t).const_mul
    (cubicResidualModeAmplitude v h)
  have hf : (fun x : ℝ => cubicResidualNonzeroTerm h (v,z+(x:ℂ)*direction))=
      (fun x : ℝ => cubicResidualModeAmplitude v h*
        ShortDraftTrace.breveE (cuspFrequency h*(z+(x:ℂ)*direction))) := by
    funext x
    exact cubicResidualNonzeroTerm_eq_amplitude v hv h _
  rw [hf]
  convert hh using 1
  rw [cubicResidualDirectionalTerm,cubicResidualNonzeroTerm_eq_amplitude v hv h]
  ring

lemma cubicResidualDirectionalTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),v∈Set.Icc a b →
      ‖cubicResidualDirectionalTerm h v z direction‖≤
        C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound a b ha hab
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hv
  rw [cubicResidualDirectionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h (v,z) hv)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma cubicResidualDirectionalTerm_summable (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => cubicResidualDirectionalTerm h v z direction) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualDirectionalTerm_slab_bound v v hv le_rfl direction
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h v z ⟨le_rfl,le_rfl⟩)
  exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C

lemma cubicResidualNonzeroSeries_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualNonzeroSeries (v,z+(x:ℂ)*direction))
      (∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualDirectionalTerm_slab_bound v v hv le_rfl direction
  have hs := (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : ActualEisensteinCubic.O => cubicResidualNonzeroTerm h (v,z+(0:ℂ)*direction)) := by
    simpa only [zero_mul,add_zero] using cubicResidualNonzeroTerm_summable (v,z) hv
  exact hasDerivAt_tsum hs (fun h x => cubicResidualNonzeroTerm_horizontal_hasDerivAt h v hv z direction x)
    (fun h x => hbound h v (z+(x:ℂ)*direction) ⟨le_rfl,le_rfl⟩) hz t

lemma cubicResidualFunction_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualFunction (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (cubicResidualNonzeroSeries_horizontal_hasDerivAt v hv z direction t).const_add
    ((3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ))
  simpa only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint] using hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalWirtingerBar (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ => f (z+(t:ℂ))) 0+
    Complex.I*deriv (fun t : ℝ => f (z+(t:ℂ)*Complex.I)) 0)

lemma horizontalWirtingerBar_brevePhase (freq z : ℂ) :
    horizontalWirtingerBar (fun w => ShortDraftTrace.breveE (freq*w)) z=
      (2*Real.pi*Complex.I*star freq)*ShortDraftTrace.breveE (freq*z) := by
  have h1 := (brevePhase_hasDerivAt freq z 1 0).deriv
  have hI := (brevePhase_hasDerivAt freq z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  linear_combination ShortDraftTrace.breveE (freq*z)*horizontalPhaseMultiplier_wirtinger freq

theorem cubicResidualFunction_wirtingerBar (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w => cubicResidualFunction (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*star (cuspFrequency h))*cubicResidualNonzeroTerm h (v,z) := by
  have h1 := (cubicResidualFunction_horizontal_hasDerivAt v hv z 1 0).deriv
  have hI := (cubicResidualFunction_horizontal_hasDerivAt v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  have hs1 := cubicResidualDirectionalTerm_summable v hv z 1
  have hsI := (cubicResidualDirectionalTerm_summable v hv z Complex.I).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_add hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold cubicResidualDirectionalTerm
  linear_combination cubicResidualNonzeroTerm h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

lemma cubicResidualFunction_wirtingerBar_summable (v : ℝ) (hv : 0<v) (z : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => (2*Real.pi*Complex.I*star (cuspFrequency h))*cubicResidualNonzeroTerm h (v,z)) := by
  have hs := ((cubicResidualDirectionalTerm_summable v hv z 1).add
    ((cubicResidualDirectionalTerm_summable v hv z Complex.I).mul_left Complex.I)).mul_left (1/2:ℂ)
  apply hs.congr
  intro h
  unfold cubicResidualDirectionalTerm
  linear_combination cubicResidualNonzeroTerm h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay -/

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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def residualCuspDecayRate : ℝ := Real.pi*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹/4

lemma residualCuspDecayRate_pos : 0< residualCuspDecayRate := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  unfold residualCuspDecayRate
  positivity

lemma cubicResidualNonzeroTerm_cusp_bound (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖cubicResidualNonzeroTerm h (v,z)‖≤C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := cubicResidualFourierCoefficient_subexponential (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,mul_nonneg hC (cubicBesselUpperAway_pos delta hdelta).le,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,ite_eq_left hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hav ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [cubicResidualNonzeroTerm_bessel h hh v hv z,norm_mul,norm_mul,norm_mul,
    breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*v*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hcoeff h hh) hv.le)
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*cubicBesselUpperAway delta)*v*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*v)/2=
        -(4*Real.pi*‖cuspFrequency h‖*v/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hav (mul_pos Real.pi_pos hr).le]

lemma cubicResidualDirectionalTerm_cusp_majorant (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃D : ℝ,0≤D ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖cubicResidualDirectionalTerm h v z direction‖≤
        (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*
          (‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_cusp_bound a ha
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · subst h
    simp only [cubicResidualDirectionalTerm,cubicResidualNonzeroTerm,ite_true,mul_zero,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
      Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
      (show 0≤Real.pi*v/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
    unfold residualCuspDecayRate
    nlinarith
  rw [cubicResidualDirectionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h v z hav)
        (norm_nonneg _) (by positivity)
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*(Real.exp (-(2*residualCuspDecayRate)*v)*
          Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖))) := by
      gcongr
    _ = _ := by ring

lemma cubicResidualDirectionalSeries_cusp_decay (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(z : ℂ),a≤v →
      ‖∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z direction‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hbound⟩ := cubicResidualDirectionalTerm_cusp_majorant a ha direction
  have hc := residualCuspDecayRate_pos
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hs := summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by positivity,?_⟩
  intro v z hav
  have hsum := tsum_of_norm_bounded
    (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v)))
    (fun h => hbound h v z hav)
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*
        Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem cubicResidualFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := cubicResidualDirectionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := cubicResidualDirectionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (cubicResidualFunction_horizontal_hasDerivAt v hv z 1 0).deriv
  have hI := (cubicResidualFunction_horizontal_hasDerivAt v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end CubicEisenstein

namespace ShortDraftCRT
open scoped BigOperators Classical Matrix

section
variable {R : Type*} [CommRing R]

theorem exists_frequency_lift (N p h : R) (hcop : IsCoprime N p) :
    ∃k : R, N∣k ∧ p∣k-h := by
  obtain ⟨u,v,huv⟩ := hcop
  refine ⟨h*u*N,⟨h*u,by ring⟩,⟨-h*v,?_⟩⟩
  linear_combination h*huv

theorem crossNum_congr_of_lift_dvd (N a c : R) (rows : List (R×R))
    (hlift : ∀ph∈rows,N∣ph.2) :
    N∣crossNum a c rows-a*(rows.map Prod.fst).prod := by
  induction rows with
  | nil => simp [crossNum]
  | cons ph rows ih =>
    rcases ph with ⟨p,h⟩
    have ht := ih (fun ph hm=>hlift ph (List.mem_cons_of_mem _ hm))
    have hh := hlift (p,h) (List.mem_cons_self ..)
    have h1 := dvd_mul_of_dvd_left ht p
    have h2 := dvd_mul_of_dvd_left hh (crossDen c rows)
    convert dvd_add h1 h2 using 1 ;
      simp only [crossNum,List.map_cons,List.prod_cons] ; ring

theorem crossNum_fixed_sector_congr (M a c : R) (rows rows0 : List (R×R))
    (hc : c∣M)
    (hlift : ∀ph∈rows,M^2∣ph.2) (hlift0 : ∀ph∈rows0,M^2∣ph.2)
    (hsector : M^2∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod) :
    M*c∣crossNum a c rows-crossNum a c rows0 := by
  have hmc : M*c∣M^2 := by simpa only [pow_two] using mul_dvd_mul_left M hc
  have h1 := crossNum_congr_of_lift_dvd (M^2) a c rows hlift
  have h0 := crossNum_congr_of_lift_dvd (M^2) a c rows0 hlift0
  have h2 := dvd_mul_of_dvd_right hsector a
  apply hmc.trans
  convert dvd_sub (dvd_add h1 h2) h0 using 1 ; ring

variable [IsDomain R]

theorem fixed_ray_completion_in_sector (M a c : R) (rows rows0 : List (R×R))
    (b0 d0 : R) (hc0 : c≠0) (hc : c∣M)
    (hbase : IsCoprime a c) (hrows : GoodRows c rows)
    (hr : IsCoprime (rows.map Prod.fst).prod (M*c))
    (hlift : ∀ph∈rows,M^2∣ph.2) (hlift0 : ∀ph∈rows0,M^2∣ph.2)
    (hsector : M^2∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod)
    (hdet0 : crossNum a c rows0*d0-b0*crossDen c rows0=1) :
    ∃b d : R, crossNum a c rows*d-b*crossDen c rows=1 ∧ M*c∣d-d0 ∧
      (!![crossNum a c rows,b;crossDen c rows,d] : Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) =
        (!![crossNum a c rows0,b0;crossDen c rows0,d0] : Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by
  have hn := crossNum_fixed_sector_congr M a c rows rows0 hc hlift hlift0 hsector
  have hrmod : M∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod :=
    (show M∣M^2 by simpa only [pow_two] using (dvd_mul_right M M)).trans hsector
  have hcop := coprime_cross_num_list a c rows hbase hrows
  rw [crossDen_eq_product] at hcop hdet0 ⊢
  obtain ⟨b,d,hd,hdd,hmat⟩ := exists_fixed_matrix_completion M c
    (crossNum a c rows0) (rows0.map Prod.fst).prod d0 b0 hc0 hdet0
    (crossNum a c rows) (rows.map Prod.fst).prod hn hrmod hr hcop.of_mul_right_right
  refine ⟨b,d,hd,hdd,?_⟩
  simpa only [crossDen_eq_product] using hmat

end

variable {R : Type*} [CommRing R] [IsDomain R]

theorem exists_sectorwise_completions {ι Q : Type*} (M c : R) (hc : c≠0)
    (sector : ι→Q) (a r : ι→R)
    (hcop : ∀i,IsCoprime (a i) (c*r i))
    (hr : ∀i,IsCoprime (r i) (M*c))
    (ha : ∀i j,sector i=sector j → M*c∣a i-a j)
    (hrr : ∀i j,sector i=sector j → M∣r i-r j) :
    ∃(b d : ι→R) (C : Q→Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧
      ∀i,(!![a i,b i;c*r i,d i] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have hlocal (q : Q) :
      ∃C : Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M}),
        ∀i,sector i=q → ∃b d : R,a i*d-b*(c*r i)=1 ∧
          (!![a i,b;c*r i,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq : ∃i,sector i=q
    · obtain ⟨j,hj⟩ := hq
      obtain ⟨x,y,hxy⟩ := hcop j
      have hdet : a j*x-(-y)*(c*r j)=1 := by linear_combination hxy
      refine ⟨(!![a j,-y;c*r j,x] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs : sector i=sector j := hi.trans hj.symm
      obtain ⟨b,d,hd,_,he⟩ := exists_fixed_matrix_completion M c (a j) (r j) x (-y)
        hc hdet (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hd,he⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i : ι) := hC (sector i) i rfl
  choose b d hd he using hi
  exact ⟨b,d,C,hd,he⟩

def LiftedRows (M c : R) :=
  {rows : List (R×R) // GoodRows c rows ∧ (∀ph∈rows,M^2∣ph.2) ∧
    IsCoprime (rows.map Prod.fst).prod (M*c)}

theorem exists_uniform_cusp_completions (M a c : R) (hc0 : c≠0)
    (hc : c∣M) (hbase : IsCoprime a c) :
    ∃(b d : LiftedRows M c→R)
      (C : (R⧸Ideal.span {M^2})→Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M})),
      (∀i,crossNum a c i.val*d i-b i*crossDen c i.val=1) ∧
      ∀i,(!![crossNum a c i.val,b i;crossDen c i.val,d i] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M}))=
        C (Ideal.Quotient.mk (Ideal.span {M^2}) (i.val.map Prod.fst).prod) := by
  let sector : LiftedRows M c→R⧸Ideal.span {M^2} :=
    fun i=>Ideal.Quotient.mk (Ideal.span {M^2}) (i.val.map Prod.fst).prod
  have hsector (i j : LiftedRows M c) (hs : sector i=sector j) :
      M^2∣(i.val.map Prod.fst).prod-(j.val.map Prod.fst).prod :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hs)
  obtain ⟨b,d,C,hd,he⟩ := exists_sectorwise_completions M c hc0 sector
    (fun i=>crossNum a c i.val) (fun i=>(i.val.map Prod.fst).prod)
    (fun i=>by
      simpa only [←crossDen_eq_product] using coprime_cross_num_list a c i.val hbase i.property.1)
    (fun i=>i.property.2.2)
    (fun i j hs=>crossNum_fixed_sector_congr M a c i.val j.val hc
      i.property.2.1 j.property.2.1 (hsector i j hs))
    (fun i j hs=>(show M∣M^2 by simpa only [pow_two] using dvd_mul_right M M).trans
      (hsector i j hs))
  refine ⟨b,d,C,?_,?_⟩
  · intro i
    simpa only [crossDen_eq_product] using hd i
  · intro i
    simpa only [crossDen_eq_product,sector] using he i

theorem eisenstein_uniform_cusp_completions
    (M a c : ActualEisensteinCubic.O) (hM : M≠0) (hc0 : c≠0)
    (hc : c∣M) (hbase : IsCoprime a c) :
    ∃(b d : LiftedRows M c→ActualEisensteinCubic.O)
      (S : Set (Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O⧸Ideal.span {M}))),
      S.Finite ∧ S.ncard≤Ideal.absNorm (Ideal.span {M^2}) ∧
      (∀i,crossNum a c i.val*d i-b i*crossDen c i.val=1) ∧
      ∀i,(!![crossNum a c i.val,b i;crossDen c i.val,d i] :
        Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O).map
          (Ideal.Quotient.mk (Ideal.span {M}))∈S := by
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {M^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero _ hM)
  obtain ⟨b,d,C,hd,he⟩ := exists_uniform_cusp_completions M a c hc0 hc hbase
  refine ⟨b,d,Set.range C,Set.finite_range C,?_,hd,?_⟩
  · have hh := Set.ncard_image_le (s := Set.univ) (f := C)
    simpa only [Set.image_univ,Set.ncard_univ,Ideal.absNorm_apply,
      Submodule.cardQuot_apply] using hh
  · intro i
    exact ⟨_,(he i).symm⟩

end ShortDraftCRT

open scoped BigOperators Classical

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_principal_global (a c0 r : Eis)
    (ha : lambda^2∣a-1) (hr : lambda^2∣r-1) :
    symbol (c0*r) a=symbol c0 a*symbol a r := by
  rw [symbol_mul_numerator _ _ a ha,
    symbol_reciprocity r a (primary_ne_zero r hr) (primary_ne_zero a ha) hr ha]

theorem A3_ramified_global (a b cprime d u : Eis)
    (hdet : a*d-b*(u*cprime)=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) :
    symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b)*symbol cprime a := by
  have h1 : symbol a (a-u*b)*symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b) := by
    rw [←symbol_mul_numerator _ _ _ hA]
    apply symbol_congr
    refine ⟨u*cprime,?_⟩
    linear_combination -u*hdet
  have h2 : symbol (a-u*b) a*symbol cprime a=1 := by
    rw [←symbol_mul_numerator _ _ _ ha,←symbol_one_numerator a ha]
    apply symbol_congr
    refine ⟨cprime-d,?_⟩
    linear_combination hdet
  rw [symbol_reciprocity a (a-u*b) (primary_ne_zero a ha)
    (primary_ne_zero _ hA) ha hA] at h1
  calc
    _ = (symbol (a-u*b) a*symbol cprime a)*symbol (u*cprime-u*d) (a-u*b) := by rw [h2,one_mul]
    _ = (symbol (a-u*b) a*symbol (u*cprime-u*d) (a-u*b))*symbol cprime a := by ring
    _ = _ := by rw [h1]

theorem A3_ramified_global_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) (hr : lambda^2∣r-1) :
    symbol (u*(c0*r)-u*d) (a-u*b)=
      (symbol (-u) (a-u*b)*symbol c0 a)*symbol a r := by
  rw [A3_ramified_global a b (c0*r) d u hdet ha hA,
    A3_principal_global a c0 r ha hr]
  ring

theorem A3_unramified_global (a b c d : Eis)
    (hdet : a*d-b*c=1) (hb : lambda^2∣(-b)-1) (hc : lambda^2∣c-1)
    (h9 : (9:Eis)∣a*d) :
    symbol (-d) (-b)=symbol a c := by
  have hp : lambda^2∣((-b)*c)-1 := primary_mul (-b) c hb hc
  have hprod : symbol d (-b)*symbol d c=1 := by
    rw [←symbol_mul_denominator]
    have hnine : (9:Eis)∣(-b)*c-1 := by
      convert dvd_neg.mpr h9 using 1
      linear_combination hdet
    have hd : d∣(-b)*c-1 := by
      refine ⟨-a,?_⟩
      linear_combination hdet
    rw [symbol_denominator_congr d ((-b)*c) 1 hp (by simp) hnine hd,symbol_one]
  have hother : symbol a c*symbol d c=1 := by
    rw [←symbol_mul_numerator _ _ _ hc,←symbol_one_numerator c hc]
    apply symbol_congr
    refine ⟨b,?_⟩
    linear_combination hdet
  rw [symbol_neg_numerator _ _ hb]
  calc
    symbol d (-b) = symbol d (-b)*(symbol a c*symbol d c) := by rw [hother,mul_one]
    _ = (symbol d (-b)*symbol d c)*symbol a c := by ring
    _ = symbol a c := by rw [hprod,one_mul]

theorem A3_unramified_global_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hb : lambda^2∣(-b)-1)
    (hc : lambda^2∣c0*r-1) (h9 : (9:Eis)∣a*d) :
    symbol (-d) (-b)=symbol a c0*symbol a r := by
  rw [A3_unramified_global a b (c0*r) d hdet hb hc h9,symbol_mul_denominator]

theorem A3_fixed_factor_congr (M c0 a a0 : Eis)
    (h9M : (9:Eis)∣M) (ha : lambda^2∣a-1) (ha0 : lambda^2∣a0-1)
    (hsector : M*c0∣a-a0) : symbol c0 a=symbol c0 a0 := by
  apply symbol_denominator_congr c0 a a0 ha ha0
  · exact (h9M.trans (dvd_mul_right M c0)).trans hsector
  · exact (dvd_mul_left c0 M).trans hsector

end

open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_ramified_fixed_factor_congr (M c0 u a a0 b b0 : Eis)
    (h9M : (9:Eis)∣M) (hcM : c0∣M) (huM : u∣M)
    (ha : lambda^2∣a-1) (ha0 : lambda^2∣a0-1)
    (hA : lambda^2∣a-u*b-1) (hA0 : lambda^2∣a0-u*b0-1)
    (hma : M∣a-a0) (hmb : M∣b-b0) :
    symbol (-u) (a-u*b)*symbol c0 a=
      symbol (-u) (a0-u*b0)*symbol c0 a0 := by
  have hdiff : M∣(a-u*b)-(a0-u*b0) := by
    convert dvd_sub hma (dvd_mul_of_dvd_right hmb u) using 1 ; ring
  have hfirst : symbol (-u) (a-u*b)=symbol (-u) (a0-u*b0) := by
    apply symbol_denominator_congr _ _ _ hA hA0 (h9M.trans hdiff)
    exact neg_dvd.mpr (huM.trans hdiff)
  have hsecond := symbol_denominator_congr c0 a a0 ha ha0 (h9M.trans hma) (hcM.trans hma)
  rw [hfirst,hsecond]

theorem A3_unramified_fixed_factor_congr (M c0 a a0 : Eis)
    (hcM : c0∣M) (hma : M∣a-a0) : symbol a c0=symbol a0 c0 :=
  symbol_congr (hcM.trans hma)

theorem norm_embedded_cubic_symbol (x a : Eis)
    (ha : lambda^2∣a-1) (hcop : IsCoprime x a) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol x a)‖=1 := by
  have hcube : ConcreteTraceCRT.eisEmbedding (symbol x a)^3=1 := by
    rw [←map_pow,symbol_cube_of_isCoprime x a ha hcop,map_one]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm hcube

theorem norm_A3_principal_fixed_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (ha : lambda^2∣a-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol c0 a)‖=1 := by
  apply norm_embedded_cubic_symbol _ _ ha
  refine ⟨-b*r,d,?_⟩
  linear_combination hdet

theorem norm_A3_ramified_fixed_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣a-u*b-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b)*symbol c0 a)‖=1 := by
  have hfirst : ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b))‖=1 := by
    apply norm_embedded_cubic_symbol _ _ hA
    refine ⟨b*(c0*r-d),d,?_⟩
    linear_combination hdet
  have hsecond : ‖ConcreteTraceCRT.eisEmbedding (symbol c0 a)‖=1 := by
    apply norm_embedded_cubic_symbol _ _ ha
    refine ⟨-b*u*r,d,?_⟩
    linear_combination hdet
  rw [map_mul,norm_mul,hfirst,hsecond,one_mul]

theorem norm_A3_unramified_fixed_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hc : lambda^2∣c0-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol a c0)‖=1 := by
  apply norm_embedded_cubic_symbol _ _ hc
  refine ⟨d,-b*r,?_⟩
  linear_combination hdet

end ShortDraftCusp

open scoped BigOperators Classical
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicUnitGaussSum_norm_le (h c:Eis) (hc:c≠0) (hp:lambda^2∣c-1):
    ‖cubicUnitGaussSum h c‖≤Ideal.absNorm (Ideal.span {c}):=by
  let:Finite (Eis⧸Ideal.span {c}):=finite_quotient_span hc
  let:Fintype (Eis⧸Ideal.span {c}):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue c):=Fintype.ofFinite _
  have hs (r:CubicUnitResidue c):
      ‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)‖=1:=by
    apply Complex.norm_eq_one_of_pow_eq_one (n:=3) _ (by decide)
    rw [←map_pow,symbol_cube_of_isCoprime _ c hp _ ,map_one]
    apply IsCoprime.symm
    apply (isUnit_quotient_span_iff c _).mp
    simpa only [GaussianShiftedPartition.representative_spec] using r.2
  rw [cubicUnitGaussSum,tsum_fintype]
  calc
    _≤∑r:CubicUnitResidue c,‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive (3*h) c (GaussianShiftedPartition.representative c r.val)‖:=norm_sum_le _ _
    _=(Fintype.card (CubicUnitResidue c):ℝ):=by
      simp only [norm_mul,hs,residueAdditive,breveE_norm,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _≤(Fintype.card (Eis⧸Ideal.span {c}):ℝ):=by
      exact_mod_cast Fintype.card_subtype_le (fun r=>IsUnit r)
    _=Ideal.absNorm (Ideal.span {c}):=by
      simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem unramifiedCubicGaussSeries_summable_norm (s:ℂ) (hs:2<s.re) (h:Eis):
    Summable (fun I:GoodIdeal=>‖(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)‖):=by
  have hs':1<(s-1).re:=by simp only [Complex.sub_re,Complex.one_re];linarith
  apply ((unramifiedNormWeight_summable_norm (s-1) hs').subtype
    (fun I:Ideal Eis=>primaryGenerator I≠0)).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro I
  dsimp only [Function.comp_def]
  simp only [unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast,
    unramifiedNormWeight_of_good s I.val I.2]
  have hg:=cubicUnitGaussSum_norm_le h (primaryGenerator I.val) I.2
    (primaryGenerator_spec I.val I.2).2
  rw [(primaryGenerator_spec I.val I.2).1] at hg
  nlinarith [norm_nonneg ((Ideal.absNorm I.val:ℂ)^(-s))]

abbrev PrimeDeletedIdeal (p:Eis):={I:GoodIdeal//¬(Ideal.span {p}:Ideal Eis)∣I.val}

def unramifiedPrimeDeletedSeries (p:Eis) (s:ℂ) (h:Eis):ℂ:=
  ∑'I:PrimeDeletedIdeal p,(Ideal.absNorm I.val.val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator I.val.val)

lemma primaryGenerator_pow (I:Ideal Eis) (n:ℕ):
    primaryGenerator (I ^n)=primaryGenerator I ^n:=
  map_pow primaryGeneratorHom I n

lemma gaussPrimeIdeal_prime (p:Eis) (hp:Prime p):Prime (Ideal.span {p}:Ideal Eis):=
  Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)

def gaussPrimeFactorMap (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (q:ℕ×PrimeDeletedIdeal p):GoodIdeal:=
  ⟨(Ideal.span {p})^q.1*q.2.val.val,by
    rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) q.2.val.2⟩

lemma gaussPrimeFactorMap_bijective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    Function.Bijective (gaussPrimeFactorMap p hp hprimary):=by
  let P:Ideal Eis:=Ideal.span {p}
  have hP:Prime P:=gaussPrimeIdeal_prime p hp
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh:P^n*I.val.val=P^m*J.val.val:=congrArg Subtype.val heq
    have hn:n=m:=by
      have hm:=congrArg (multiplicity P) hh
      rw [prime_power_remainder_multiplicity hP I.2,
        prime_power_remainder_multiplicity hP J.2] at hm
      exact hm
    subst m
    have hIJ:I=J:=Subtype.ext (Subtype.ext
      (mul_left_cancel₀ (pow_ne_zero n hP.ne_zero) hh))
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hP
      (primaryGenerator_ne_zero_ideal I.val I.2)).exists_eq_pow_mul_and_not_dvd
    have hgood:primaryGenerator J≠0:=by
      intro hzero
      apply I.2
      rw [hJ,primaryGenerator_mul,hzero,mul_zero]
    refine ⟨(multiplicity P I.val,⟨⟨J,hgood⟩,hnot⟩),?_⟩
    exact Subtype.ext hJ.symm

def gaussPrimeFactorEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    ℕ×PrimeDeletedIdeal p≃GoodIdeal:=
  Equiv.ofBijective (gaussPrimeFactorMap p hp hprimary)
    (gaussPrimeFactorMap_bijective p hp hprimary)

lemma primeDeleted_generator_coprime (p:Eis) (hp:Prime p) (I:PrimeDeletedIdeal p):
    IsCoprime p (primaryGenerator I.val.val):=by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  apply I.2
  rw [Ideal.dvd_iff_le,←(primaryGenerator_spec I.val.val I.val.2).1,
    Ideal.span_singleton_le_span_singleton]
  exact hd

lemma primary_pow_congruence (p:Eis) (hprimary:lambda^2∣p-1) (n:ℕ):
    lambda^2∣p^n-1:=by
  simpa only [one_pow] using hprimary.trans (sub_dvd_pow_sub_pow p 1 n)

lemma gaussPrimeFactor_term (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (s:ℂ) (h:Eis) (n:ℕ) (I:PrimeDeletedIdeal p):
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val)=
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
      ((Ideal.absNorm I.val.val:ℂ)^(-s)*cubicUnitGaussSum (h*p^n) (primaryGenerator I.val.val)):=by
  change (Ideal.absNorm ((Ideal.span {p})^n*I.val.val):ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator ((Ideal.span {p})^n*I.val.val))=_
  rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary,
    cubicUnitGaussSum_coprime_product h (p^n) (primaryGenerator I.val.val)
      (pow_ne_zero _ hp.ne_zero) I.val.2 (primary_pow_congruence p hprimary n)
      (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).pow_left,
    map_mul,map_pow,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have he:((Ideal.absNorm (Ideal.span {p})^n:ℕ):ℂ)^(-s)=
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n:=by
    rw [Nat.cast_pow,←Complex.natCast_cpow_natCast_mul,Complex.cpow_nat_mul]
  rw [he]
  ring

theorem unramifiedCubicGaussSeries_prime_reindex (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis):
    unramifiedCubicGaussSeries s h=
      ∑'n:ℕ,((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
        unramifiedPrimeDeletedSeries p s (h*p^n):=by
  have hsum:Summable (fun I:GoodIdeal=>(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)):=
    (unramifiedCubicGaussSeries_summable_norm s hs h).of_norm
  have hpull:=(gaussPrimeFactorEquiv p hp hprimary).summable_iff.mpr hsum
  change Summable (fun q:ℕ×PrimeDeletedIdeal p=>
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val)) at hpull
  rw [unramifiedCubicGaussSeries,←(gaussPrimeFactorEquiv p hp hprimary).tsum_eq]
  change (∑'q:ℕ×PrimeDeletedIdeal p,
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val))=_
  rw [hpull.tsum_prod]
  apply tsum_congr
  intro n
  change (∑'I:PrimeDeletedIdeal p,(Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val))=_
  simp_rw [gaussPrimeFactor_term p hp hprimary s h n]
  exact tsum_mul_left

lemma unramifiedPrimeDeletedSeries_cube_shift (p:Eis) (hp:Prime p) (s:ℂ) (h:Eis):
    unramifiedPrimeDeletedSeries p s (h*p^3)=unramifiedPrimeDeletedSeries p s h:=by
  apply tsum_congr
  intro I
  congr 1
  exact cubicUnitGaussSum_cube_shift h _ p I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).symm

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.PrimePowerGaussSums -/

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

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

@[simp] lemma cubicUnitGaussSum_one (h:Eis):cubicUnitGaussSum h 1=1:=by
  let:Subsingleton (Eis⧸Ideal.span {(1:Eis)}):=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let r:CubicUnitResidue (1:Eis):=⟨1,isUnit_one⟩
  rw [cubicUnitGaussSum,tsum_eq_single r (fun b hb=>False.elim (hb (Subsingleton.elim b r)))]
  rw [symbol_one,map_one,one_mul,
    residueAdditive_three_congr h 1 _ 0 one_ne_zero (one_dvd _)]
  simp only [residueAdditive,map_zero,mul_zero,zero_div,AddChar.map_zero_eq_one]

lemma cubicUnitGaussSum_frequency_dvd (h c:Eis) (hc:c≠0) (hch:c∣h):
    cubicUnitGaussSum h c=cubicUnitGaussSum 0 c:=
  cubicUnitGaussSum_frequency_congr h 0 c hc (by simpa only [sub_zero] using hch)

lemma cubicUnitGaussSum_prime_power_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (n:ℕ):
    cubicUnitGaussSum 0 (p^(n+1))=
      if 3∣n+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^n*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)-1) else 0:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary n 0
  simp only [mul_zero] at he
  rw [he,primeCubicGauss_of_dvd p hp hprimary (n+1) 0 (dvd_zero _)]
  split_ifs <;>ring

lemma cubicUnitGaussSum_prime_power_too_large (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (a k:ℕ) (hk:a+1<k):
    cubicUnitGaussSum (h*p^a) (p^k)=0:=by
  by_contra hG
  cases k with
  | zero=>omega
  | succ n=>
    have hd:=cubicUnitGaussSum_prime_power_support p hp hprimary n (h*p^a) hG
    have hd':p^(a+1)∣p^a*h:=by
      rw [mul_comm]
      exact (pow_dvd_pow p (by omega:a+1≤n)).trans hd
    rw [pow_succ] at hd'
    exact hph ((mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp hd')

lemma unramifiedPrimeDeletedSeries_pow_mod (p:Eis) (hp:Prime p) (s:ℂ) (h:Eis) (n:ℕ):
    unramifiedPrimeDeletedSeries p s (h*p^n)=
      unramifiedPrimeDeletedSeries p s (h*p^(n%3)):=by
  apply tsum_congr
  intro I
  congr 1
  have he:p^n=p^(n%3)*(p^(n/3))^3:=by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [he,←mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2
    (primeDeleted_generator_coprime p hp I).symm.pow_right

theorem unramifiedCubicGaussSeries_prime_finite (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^a)=
      ∑k∈Finset.range (a+2),((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*
        cubicUnitGaussSum (h*p^a) (p^k)*unramifiedPrimeDeletedSeries p s (h*p^a*p^k):=by
  rw [unramifiedCubicGaussSeries_prime_reindex p hp hprimary s hs]
  apply tsum_eq_sum
  intro k hk
  have hk':a+1<k:=by
    have hh: a+2≤k:=by simpa only [Finset.mem_range,not_lt] using hk
    omega
  rw [cubicUnitGaussSum_prime_power_too_large p hp hprimary h hph a k hk',mul_zero,zero_mul]

lemma unramifiedCubicGaussSeries_prime_zero_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s h=unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 0
  simpa only [pow_zero,pow_one,mul_one,cubicUnitGaussSum_one,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,one_mul,
    primeCubicGauss_one_eq] using he

lemma unramifiedCubicGaussSeries_prime_one_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p)=unramifiedPrimeDeletedSeries p s (h*p)+
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^2*(Ideal.absNorm (Ideal.span {p}):ℂ)*
        primeCubicGauss p hp hprimary 2 h*unramifiedPrimeDeletedSeries p s h:=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 1
  have hg1:cubicUnitGaussSum (h*p) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero (dvd_mul_left p h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p) (p^2)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)*primeCubicGauss p hp hprimary 2 h:=by
    simpa only [pow_one,mul_comm p h] using cubicUnitGaussSum_prime_power_lift p hp hprimary 1 h
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,mul_zero,zero_mul,add_zero,hg2] at he
  have hr:h*p*p^2=h*p^3:=by ring
  rw [hr,unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_prime_three_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+((Ideal.absNorm (Ideal.span {p}):ℂ)^3-(Ideal.absNorm (Ideal.span {p}):ℂ)^2)*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^4*
        primeCubicGauss p hp hprimary 1 h*unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 3
  have hg0 (k:ℕ) (hk:k≤3):cubicUnitGaussSum (h*p^3) (p^k)=cubicUnitGaussSum 0 (p^k):=
    cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      ((pow_dvd_pow p hk).trans (dvd_mul_left (p^3) h))
  have hg1:cubicUnitGaussSum (h*p^3) p=0:=by
    have hh:=hg0 1 (by omega)
    simp only [pow_one] at hh
    rw [hh]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^3) (p^2)=0:=by
    rw [hg0 2 (by omega)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^3) (p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1):=by
    rw [hg0 3 le_rfl]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 2
  have hg4:cubicUnitGaussSum (h*p^3) (p^4)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*primeCubicGauss p hp hprimary 1 h:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 3 h
    rw [primeCubicGauss_mod_three p hp hprimary 4] at hh
    simpa only [mul_comm (p^3) h,Nat.reduceMod] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,hg4,mul_zero,zero_mul,add_zero] at he
  have hr6:h*p^3*p^3=h*p^6:=by ring
  have hr7:h*p^3*p^4=h*p^7:=by ring
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp,hr6,hr7,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 6,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 7] at he
  norm_num only [Nat.reduceMod,pow_zero,pow_one,mul_one] at he
  exact he.trans (by ring)

theorem unramifiedCubicGaussSeries_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedCubicGaussSeries s (h*p):=by
  rw [unramifiedCubicGaussSeries_prime_three_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_zero_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_one_power p hp hprimary s hs h hph]
  have hg:=primeCubicGauss_one_mul_two p hp hprimary h hph
  linear_combination ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
    (Ideal.absNorm (Ideal.span {p}):ℂ)*unramifiedPrimeDeletedSeries p s h*hg

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

structure SubexponentialBesselCoefficients where
  value : ActualEisensteinCubic.O→ℂ
  growth : ∀epsilon : ℝ,0<epsilon → ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
    ‖value h‖≤C*Real.exp (epsilon*‖cuspFrequency h‖)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def term (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else (coeff.value h/cubicBesselNormalizer h)*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)

def amplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma term_bessel (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.term h (v,z)=coeff.value h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [term,ite_eq_right hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hn := cubicBesselNormalizer_ne_zero h hh
  have hp : (v:ℂ)^3*(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ) := by
    rw [←Complex.cpow_ofNat (v:ℂ) 3,←Complex.cpow_add _ _ hv0]
    congr 1
    ring
  calc
    _ = (coeff.value h/cubicBesselNormalizer h)*(v:ℂ)^3*
        ((v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z) := by rw [←hp];ring
    _ = _ := by
      rw [sourceFourierKernel_cubic_height h hh v hv]
      field_simp

lemma term_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    coeff.term h (v,z)=coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  by_cases hh : h=0
  · simp only [term,amplitude,ite_eq_left hh,zero_mul]
  · rw [coeff.term_bessel h hh v hv z,amplitude,ite_eq_right hh]

lemma term_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (coeff.term h) {p : ℝ × ℂ | 0<p.1} := by
  unfold term
  by_cases hh : h=0
  · simp only [ite_eq_left hh]
    exact continuousOn_const
  simp only [ite_eq_right hh]
  intro p hp
  change 0<p.1 at hp
  have hpow : ContinuousAt (fun q : ℝ × ℂ => (q.1:ℂ)^(2/3:ℂ)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (2/3:ℂ) (Or.inr hp.ne')).comp continuousAt_fst
  have hsource : ContinuousAt (fun q : ℝ × ℂ => sourceFourierKernel (4/3) (cuspFrequency h*q.1)) p :=
    (sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp (by fun_prop)
  have hphase : Continuous (fun q : ℝ × ℂ => ShortDraftTrace.breveE (cuspFrequency h*q.2)) := by
    change Continuous (fun q : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2))))
    fun_prop
  exact (((continuousAt_const.mul hpow).mul hsource).mul hphase.continuousAt).continuousWithinAt

lemma slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.term h p‖≤C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*b*cubicBesselUpperAway delta,by positivity,?_⟩
  intro h p hp
  have hv : 0<p.1 := ha.trans_le hp.1
  by_cases hh : h=0
  · simp only [term,ite_eq_left hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*p.1 := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1 ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [show p=(p.1,p.2) from rfl,coeff.term_bessel h hh _ hv,
    norm_mul,norm_mul,norm_mul,breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*b*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*p.1)/2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (by positivity))
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*b*cubicBesselUpperAway delta)*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*p.1)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*p.1)/2=
        -(4*Real.pi*‖cuspFrequency h‖*p.1/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hp.1 (mul_pos Real.pi_pos hr).le]

lemma summable (p : ℝ × ℂ) (hp : 0<p.1) : Summable (fun h : ActualEisensteinCubic.O => coeff.term h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

def series (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,coeff.term h p

lemma series_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn coeff.series {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  apply continuousOn_tsum (u := fun h : ActualEisensteinCubic.O => C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))
  · intro h
    exact (coeff.term_continuousOn h).mono (fun p hp => ha.trans_le hp.1)
  · exact (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma series_continuousOn : ContinuousOn coeff.series {p : ℝ × ℂ | 0<p.1} := by
  intro p hp
  change 0<p.1 at hp
  have hclosed := coeff.series_continuousOn_slab (p.1/2) (2*p.1) (by linarith) (by linarith)
  have hnb : {q : ℝ × ℂ | q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

lemma series_uniform (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    TendstoUniformlyOn (fun t : Finset ActualEisensteinCubic.O => fun p : ℝ × ℂ => ∑h∈t,coeff.term h p)
      coeff.series atTop {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  exact tendstoUniformlyOn_tsum
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C) hbound

lemma series_bessel (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.series (v,z)=∑'h : ActualEisensteinCubic.O,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  exact tsum_congr (fun h => coeff.term_eq_amplitude v hv h z)

lemma series_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.series (v,z+3*ConcreteTraceCRT.eisEmbedding n)=coeff.series (v,z) := by
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · simp only [term,ite_eq_left hh]
  simp only [term,ite_eq_right hh]
  rw [mul_add,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

def function (w : HyperbolicSpace) : ℂ := coeff.series (hyperbolicHeight w,hyperbolicHorizontal w)

lemma function_continuous : Continuous coeff.function := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  have hp : (hyperbolicHeight w,hyperbolicHorizontal w)∈{p : ℝ × ℂ | 0<p.1} := hyperbolicHeight_pos w
  exact (coeff.series_continuousOn.continuousAt (hopen.mem_nhds hp)).comp
    (f := fun u : HyperbolicSpace => (hyperbolicHeight u,hyperbolicHorizontal u))
    (hyperbolicHeight_continuous.prodMk hyperbolicHorizontal_continuous).continuousAt

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma series_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v k := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
    ShortDraftTrace.breveE (-cuspFrequency k*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*z)+starRingEnd ℂ (cuspFrequency h*z)))*
      Complex.exp (2*Real.pi*Complex.I*((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
    change ‖(coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)‖≤_
    rw [←coeff.term_eq_amplitude v hv h z,norm_mul,breveE_norm,mul_one]
    exact hbound h (v,z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=
      if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v h else 0 := by
    change (∫z in periodDomain,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=_
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_cusp_character_product]
    split_ifs <;> ring
  calc
    _ = ∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (∑'h : ActualEisensteinCubic.O,coeff.term h (v,z))*ShortDraftTrace.breveE (-cuspFrequency k*z)=_
        rw [←tsum_mul_right]
        apply tsum_congr
        intro h
        rw [coeff.term_eq_amplitude v hv h z])
    _ = ∑'h : ActualEisensteinCubic.O,∫z in periodDomain,f h z := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = ∑'h : ActualEisensteinCubic.O,if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v h else 0 := tsum_congr hterm
    _ = _ := by simp

lemma series_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.series (v,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  exact (coeff.series_continuousOn.continuousAt (hopen.mem_nhds hv)).comp
    (f := fun z : ℂ => (v,z)) (by fun_prop)

def fullFunction (constant : ℂ) (w : HyperbolicSpace) : ℂ :=
  constant*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+coeff.function w

lemma fullFunction_continuous (constant : ℂ) : Continuous (coeff.fullFunction constant) := by
  have hp : Continuous (fun w : HyperbolicSpace => (hyperbolicHeight w:ℂ)^(2/3:ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (Complex.continuousAt_ofReal_cpow_const (hyperbolicHeight w) (2/3:ℂ)
      (Or.inr (hyperbolicHeight_pos w).ne')).comp (f := hyperbolicHeight) hyperbolicHeight_continuous.continuousAt
  exact (continuous_const.mul hp).add coeff.function_continuous

lemma fullFunction_fourier (constant : ℂ) (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.fullFunction constant (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if k=0 then constant*(v:ℂ)^(2/3:ℂ) else coeff.amplitude v k) := by
  have hphase : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency k*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  have hc0 := periodDomain_integrable_of_continuous
    (fun z => (constant*(v:ℂ)^(2/3:ℂ))*ShortDraftTrace.breveE (-cuspFrequency k*z))
    (continuous_const.mul hphase)
  have hcn := periodDomain_integrable_of_continuous
    (fun z => coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))
    ((coeff.series_height_continuous v hv).mul hphase)
  simp_rw [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,add_mul]
  rw [integral_add hc0 hcn,integral_const_mul,integral_cusp_character,coeff.series_fourier v hv k]
  by_cases hk : k=0
  · simp only [ite_eq_left hk,amplitude,mul_zero]
    ring
  · simp only [ite_eq_right hk,mul_zero,zero_add]

lemma fullFunction_period (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.fullFunction constant (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      coeff.fullFunction constant (upperPoint z v hv) := by
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    coeff.series_period]

lemma fullFunction_height_continuous (constant : ℂ) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.fullFunction constant (upperPoint z v hv)) := by
  have hc := coeff.series_height_continuous v hv
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  fun_prop

lemma fullFunction_height_memLp (constant : ℂ) (v : ℝ) (hv : 0<v) :
    MemLp (fun z : ℂ => coeff.fullFunction constant (cuspCoordinateLift (v,z))) 2
      (volume.restrict periodDomain) := by
  simp_rw [cuspCoordinateLift_positive v _ hv]
  have hc := coeff.fullFunction_height_continuous constant v hv
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hn : Continuous (fun z : ℂ => ‖coeff.fullFunction constant (upperPoint z v hv)‖^2) := by
    fun_prop
  apply (hn.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

end SubexponentialBesselCoefficients
end CubicEisenstein

open scoped BigOperators Classical

namespace ShortDraftCRT
variable {R : Type*} [CommRing R]

theorem inverse_residue_congr (D r r0 u u0 : R) (hcop : IsCoprime D r)
    (hr : D∣r-r0) (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) : D∣u-u0 := by
  apply hcop.dvd_of_dvd_mul_right
  have hh := dvd_sub (dvd_sub hu hu0) (dvd_mul_of_dvd_right hr u0)
  convert hh using 1 ; ring

theorem inverse_weight_residue_congr (D r r0 u u0 d d0 : R)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    D∣(-d*u)-(-d0*u0) := by
  have hi := inverse_residue_congr D r r0 u u0 hcop hr hu hu0
  have hh := dvd_add (dvd_mul_of_dvd_left hd u) (dvd_mul_of_dvd_right hi d0)
  convert dvd_neg.mpr hh using 1 ; ring

theorem fixed_additive_sector {K : Type*} [Field K]
    (ι : R→+*K) (ψ : AddChar K ℂ) (lam D r r0 u u0 d d0 x : R)
    (hlam : ι lam≠0) (hD : ι D≠0)
    (hperiod : ∀y : R,ψ (ι y/ι lam)=1)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    ψ (ι (-d*u)*ι x/(ι lam*ι D))=
      ψ (ι (-d0*u0)*ι x/(ι lam*ι D)) :=
  addChar_congr_of_dvd ι ψ lam D (-d*u) (-d0*u0) x hlam hD hperiod
    (inverse_weight_residue_congr D r r0 u u0 d d0 hcop hr hu hu0 hd)

theorem strong_sector_additive_congruences (M lam c r r0 d d0 : R)
    (hlam : lam^3∣M) (hc : c∣M) (hr : M^2∣r-r0) (hd : M*c∣d-d0) :
    lam^3*c∣r-r0 ∧ lam^3*c∣d-d0 := by
  constructor
  · apply (show lam^3*c∣M^2 by simpa only [pow_two] using mul_dvd_mul hlam hc).trans hr
  · exact (mul_dvd_mul hlam (dvd_refl c)).trans hd

end ShortDraftCRT

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedHeightCompact (M:levelTwo) (a b:ℝ) : Set KernelQuotient :=
  kernelSourceAction M '' cuspHeightQuotientCompact a b

lemma translatedHeightCompact_isCompact (M:levelTwo) (a b:ℝ) (ha:0<a) :
    IsCompact (translatedHeightCompact M a b) :=
  (cuspHeightQuotientCompact_isCompact a b ha).image (kernelSourceAction_continuous M)

def translatedHeightFourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) : KernelQuotientL2→L[ℂ]ℂ :=
  (kernelCuspHeightFourier a b ha ρ h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedHeightFourier_integral (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M F=
      ∫w in cuspPeriodStrip a b,F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,kernelCuspHeightFourier_integral]
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp (kernelSourcePullback_ae_eq M F)
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w) hw

lemma translatedHeightFourier_restrict (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M
      (kernelMassRestrictionCLM (translatedHeightCompact M a b)
        (translatedHeightCompact_isCompact M a b ha).measurableSet F)=translatedHeightFourier a b ha ρ h M F := by
  rw [translatedHeightFourier_integral,translatedHeightFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha).measurableSet F)
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  have hm:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedHeightCompact M a b :=
    ⟨_,cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem hm _))

def translatedHeightFamily (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) : ℂ :=
  translatedHeightFourier a b ha ρ h M
    (kernelLocalCorrectedSeed (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

lemma translatedHeightFamily_analyticAt (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) (hs:s.re≠1) (hi:s.im≠0) :
    AnalyticAt ℂ (translatedHeightFamily a b ha ρ h M) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedHeightFourier a b ha ρ h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedHeightCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma translatedHeightFamily_residue_limit (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) :
    Tendsto (fun s:ℂ=>(s-4/3)*translatedHeightFamily a b ha ρ h M s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (translatedHeightFourier a b ha ρ h M cubicEisensteinResidue)) := by
  have hh:=(translatedHeightFourier a b ha ρ h M).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (translatedHeightCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedHeightFourier_restrict,
    translatedHeightFamily] using hh

lemma translatedHeightFamily_initial (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) (hs:4<s.re) (hi:0<s.im) :
    translatedHeightFamily a b ha ρ h M s=
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  have hcorrected:kernelCorrectedSeed 2 3 (by norm_num) (by norm_num) s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith) := by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi] with q hq
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hq]
    ring
  have hlocal:=kernelLocalCorrectedSeed_ae_eq _ (translatedHeightCompact_isCompact M a b ha)
    2 3 (by norm_num) (by norm_num) s
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hlocal
  have hE:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hp:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  have hpE:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hE
  rw [translatedHeightFamily,translatedHeightFourier_integral]
  apply integral_congr_ae
  filter_upwards [hp,hpE,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwe hwm
  have hm:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedHeightCompact M a b :=
    ⟨_,cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩,rfl⟩
  dsimp only [Function.comp_def] at hw hwe
  rw [hw,Set.indicator_of_mem hm,hwe,kernelSourceAction_mk,kernelQuotientEisenstein_mk]

end CubicEisenstein

end

end OAI

end

