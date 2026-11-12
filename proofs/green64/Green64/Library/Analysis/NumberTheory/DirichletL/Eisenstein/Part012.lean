module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part011

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.RationalTranslations -/

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
open scoped BigOperators Classical MatrixGroups

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def rationalComplex : SL(2,ℤ) →* SL(2,ℂ) := integralComplexMatrix.comp rationalEmbedding

lemma rationalUnipotent_nat (n : ℕ) : rationalUnipotent (n:ℤ)=ModularGroup.T^n := by
  induction n with
  | zero => simpa using rationalUnipotent_zero
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,rationalUnipotent_add,ih,rationalUnipotent_one,pow_succ]

lemma rationalComplex_S_sq_row (v : Fin 2→ℂ) :
    rowOperator (rationalComplex (ModularGroup.S^2)) v = -v := by
  have hS : ((ModularGroup.S ^ 2 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-1,0;0,-1] := by decide
  have hC : (rationalComplex (ModularGroup.S ^ 2) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![-1,0;0,-1] := by
    apply Matrix.ext
    intro i j
    change eisEmbedding ((Int.castRingHom O) ((ModularGroup.S ^ 2 : SL(2,ℤ)) i j)) = _
    rw [congrFun (congrFun hS i) j]
    fin_cases i <;> fin_cases j <;> simp
  rw [rowOperator_apply,hC]
  funext j
  fin_cases j <;> simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma hyperbolicEisenstein_S_sq (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S^2) • w)=hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    change eisenstein (rationalComplex (ModularGroup.S^2)*g) s=eisenstein g s
    apply tsum_congr
    intro x
    unfold summand
    rw [←rowOperator_mul,rationalComplex_S_sq_row,map_neg]
    simp [rowEnergy]

lemma hyperbolicEisenstein_T_pow (s : ℂ) (n : ℕ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.T^n) • w)=hyperbolicEisenstein s w := by
  simpa only [rationalUnipotent_nat,rationalComplex,MonoidHom.comp_apply] using hyperbolicEisenstein_unipotent (n:ℤ) s w

lemma hyperbolicEisenstein_S_even (s : ℂ) (e : Fin 2) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S^(2*e.val)) • w)=hyperbolicEisenstein s w := by
  fin_cases e
  · simp
  · exact hyperbolicEisenstein_S_sq s w

lemma hyperbolicEisenstein_bruhat (s : ℂ) (e : Fin 2) (a : Fin 3⊕(Fin 3×Fin 3)) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (rationalBruhatRep (e,a)) • w)=
      match a with
      | Sum.inl _ => hyperbolicEisenstein s w
      | Sum.inr ab => hyperbolicEisenstein s
          (rationalComplex ModularGroup.S • (rationalComplex (ModularGroup.T^ab.2.val) • w)) := by
  simp only [rationalBruhatRep,map_mul,mul_smul,hyperbolicEisenstein_S_even]
  cases a with
  | inl a => exact hyperbolicEisenstein_T_pow s a.val w
  | inr ab => simp only [map_mul,mul_smul,hyperbolicEisenstein_T_pow]

theorem sourceEisenstein_four_cusps (s : ℂ) (w : HyperbolicSpace) :
    sourceEisenstein s w = (4:ℂ)⁻¹ * (hyperbolicEisenstein s w +
      ∑ b : Fin 3, hyperbolicEisenstein s
        (rationalComplex ModularGroup.S • (rationalComplex (ModularGroup.T^b.val) • w))) := by
  rw [sourceEisenstein,sourceProjection_eq_twentyFour]
  change (24:ℂ)⁻¹ * (∑ i : RationalBruhatIndex,
    hyperbolicEisenstein s (rationalComplex (rationalBruhatRep i) • w)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hyperbolicEisenstein_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  ring

end

section

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedCuspCompact (M:levelTwo):Set KernelQuotient:=
  kernelSourceAction M '' kernelCuspAverageCompact

lemma translatedCuspCompact_isCompact (M:levelTwo):IsCompact (translatedCuspCompact M):=
  kernelCuspAverageCompact_isCompact.image (kernelSourceAction_continuous M)

def translatedCuspFourier (h:Eis) (M:levelTwo):KernelQuotientL2→L[ℂ]ℂ:=
  (kernelCuspFourier h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedCuspFourier_integral (h:Eis) (M:levelTwo) (F:KernelQuotientL2):
    translatedCuspFourier h M F=∫w in cuspPeriodStrip 5 6,
      F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspFourierPhase h w∂hyperbolicVolume:=by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,kernelCuspFourier_integral]
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelSourcePullback_ae_eq M F) (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w) hw

lemma translatedCuspFourier_restrict (h:Eis) (M:levelTwo) (F:KernelQuotientL2):
    translatedCuspFourier h M
      (kernelMassRestrictionCLM (translatedCuspCompact M)
        (translatedCuspCompact_isCompact M).measurableSet F)=translatedCuspFourier h M F:=by
  rw [translatedCuspFourier_integral,translatedCuspFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedCuspCompact M)
      (translatedCuspCompact_isCompact M).measurableSet F)
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedCuspCompact M:=
    ⟨_,kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem hmem _))

def translatedCuspFamily (h:Eis) (M:levelTwo) (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ):ℂ:=
  translatedCuspFourier h M
    (kernelLocalCorrectedSeed (translatedCuspCompact M) (translatedCuspCompact_isCompact M) a b ha hab s)

lemma translatedCuspFamily_meromorphicAt (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b):
    MeromorphicAt (translatedCuspFamily h M a b ha hab) (4/3:ℂ):=
  meromorphicAt_clm (translatedCuspFourier h M)
    (kernelLocalCorrectedSeed_meromorphicAt _ (translatedCuspCompact_isCompact M) a b ha hab)

lemma translatedCuspFamily_analyticAt_nonreal (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ) (hs:s.re≠1) (hi:s.im≠0):
    AnalyticAt ℂ (translatedCuspFamily h M a b ha hab) s:=by
  exact (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedCuspFourier h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedCuspCompact_isCompact M)
        a b ha hab s hs hi) rfl

lemma translatedCuspFamily_residue_limit (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b):
    Tendsto (fun s:ℂ=>(s-4/3)*translatedCuspFamily h M a b ha hab s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (translatedCuspFourier h M (kernelEisensteinResidueVector a b ha hab))):=by
  have hh:=(translatedCuspFourier h M).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit _ (translatedCuspCompact_isCompact M) a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedCuspFourier_restrict,
    translatedCuspFamily] using hh

lemma translatedCuspFamily_actual_integral (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ):
    translatedCuspFamily h M a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s
        (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
          cuspFourierPhase h w∂hyperbolicVolume:=by
  rw [translatedCuspFamily,translatedCuspFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelLocalCorrectedSeed_ae_eq _ (translatedCuspCompact_isCompact M) a b ha hab s)
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedCuspCompact M:=
    ⟨_,kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem hmem _))

theorem translatedCuspFamily_initial (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (ha1:1<a) (s:ℂ) (hs:4<s.re) (hi:0<s.im):
    translatedCuspFamily h M a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume:=by
  have hcorrected:kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith):=by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap a b ha1 hab s hs hi] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  rw [translatedCuspFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (by dsimp only [Function.comp_def];rw [kernelSourceAction_mk,kernelQuotientEisenstein_mk]))

end

section

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def oppositeSource:levelTwo:=rationalLift ModularGroup.S

lemma oppositeSource_matrix:sourceComplexMatrix oppositeSource=oppositeMatrix:=by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oppositeSource,sourceComplexMatrix,rationalLift,rationalEmbedding,
      integralComplexMatrix,Matrix.SpecialLinearGroup.map_apply_coe,ModularGroup.coe_S,oppositeMatrix]

lemma hyperbolicEisenstein_opposite_upper (s:ℂ) (z:ℂ) (v:ℝ) (hv:0<v):
    hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • upperPoint z v hv)=
      oppositeEisenstein z v hv s:=by
  rw [oppositeSource_matrix]
  rfl

theorem opposite_cusp_fourier_average (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspWhittakerHeightFactor s h:=by
  let g:HyperbolicSpace→ℂ:=fun w=>
    hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*cuspFourierPhase h w
  have hg:Continuous g:=((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable g hg)]
  have heq:(∫v in Set.Icc (5:ℝ) 6,
      (∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,unramifiedCubicGaussSeries s (9*h)*
        ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)):=by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0:0<v:=by linarith [hv.1]
    have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
    have hslice:(∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
          unramifiedCubicGaussSeries s (9*h):=by
      simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
        cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      exact oppositeEisenstein_fourier v hv0 s hs h
    have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3:=by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hslice,hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma translatedCuspFamily_opposite_initial (h:Eis) (s:ℂ)
    (hs:4<s.re) (hi:0<s.im):
    translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num) s=
      unramifiedCubicGaussSeries s h*cuspWhittakerHeightFactor s (3*h):=by
  rw [translatedCuspFamily_initial (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num) (by norm_num) s hs hi,
    opposite_cusp_fourier_average s (by linarith),
    show (9:Eis)*(3*h)=27*h by ring,unramifiedCubicGaussSeries_twentySeven]

def continuedUnramifiedGauss (h:Eis) (s:ℂ):ℂ:=
  translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num) s/
    cuspWhittakerHeightFactor s (3*h)

def unramifiedGaussResidue (h:Eis):ℂ:=
  translatedCuspFourier (3*h) oppositeSource cubicEisensteinResidue/
    cuspWhittakerHeightFactor (4/3:ℂ) (3*h)

theorem continuedUnramifiedGauss_meromorphicAt_center (h:Eis):
    MeromorphicAt (continuedUnramifiedGauss h) (4/3:ℂ):=by
  exact (translatedCuspFamily_meromorphicAt (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num)).div
      (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).meromorphicAt

theorem continuedUnramifiedGauss_meromorphicOn_upper (h:Eis):
    MeromorphicOn (continuedUnramifiedGauss h) {s:ℂ|1<s.re ∧ 0<s.im}:=by
  intro s hs
  exact (translatedCuspFamily_analyticAt_nonreal (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num) s (ne_of_gt hs.1) (ne_of_gt hs.2)).meromorphicAt.div
      (cuspWhittakerHeightFactor_analyticAt (3*h) s hs.1).meromorphicAt

theorem continuedUnramifiedGauss_residue_limit (h:Eis):
    Tendsto (fun s:ℂ=>(s-4/3)*continuedUnramifiedGauss h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (unramifiedGaussResidue h)):=by
  have hd:Tendsto (fun s:ℂ=>cuspWhittakerHeightFactor s (3*h))
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) (3*h))):=
    (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hh:=(translatedCuspFamily_residue_limit (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num)).div hd (cuspWhittakerHeightFactor_center_ne_zero (3*h))
  convert hh using 1
  · funext s
    simp only [continuedUnramifiedGauss,Pi.div_apply]
    ring
  · rfl

theorem continuedUnramifiedGauss_initial (h:Eis) (s:ℂ)
    (hs:4<s.re) (hi:0<s.im) (hH:cuspWhittakerHeightFactor s (3*h)≠0):
    continuedUnramifiedGauss h s=unramifiedCubicGaussSeries s h:=by
  rw [continuedUnramifiedGauss,translatedCuspFamily_opposite_initial h s hs hi,
    mul_div_cancel_right₀ _ hH]

theorem continuedUnramifiedGauss_initial_open (h:Eis):
    ∃U:Set ℂ,IsOpen U ∧ U.Nonempty ∧ U⊆{s:ℂ|4<s.re ∧ 0<s.im} ∧
      Set.EqOn (continuedUnramifiedGauss h) (fun s=>unramifiedCubicGaussSeries s h) U:=by
  obtain ⟨ε,hε,hball⟩:=Metric.eventually_nhds_iff.mp (cuspWhittakerHeightFactor_ne_zero_near_five (3*h))
  let z:ℂ:=5+(ε/2:ℝ)*Complex.I
  have hz:dist z (5:ℂ)<ε:=by
    have he:dist z (5:ℂ)=ε/2:=by simp [z,dist_eq_norm,hε.le]
    rw [he]
    linarith
  have hzim:0<z.im:=by simpa [z] using half_pos hε
  refine ⟨Metric.ball (5:ℂ) ε ∩ {s:ℂ|0<s.im},
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im),
    ⟨z,hz,hzim⟩,?_,?_⟩
  · intro s hs
    exact ⟨(hball hs.1).1,hs.2⟩
  · intro s hs
    exact continuedUnramifiedGauss_initial h s (hball hs.1).1 hs.2 (hball hs.1).2

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma gaussRep_mk_congr (c d : Eis) :
    c ∣ GaussianShiftedPartition.representative c (Ideal.Quotient.mk (Ideal.span {c}) d)-d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact GaussianShiftedPartition.representative_spec c _

def cubicUnitCRTMap (a b : Eis) (r : CubicUnitResidue (a*b)) :
    CubicUnitResidue a × CubicUnitResidue b :=
  let d:=GaussianShiftedPartition.representative (a*b) r.1
  let hd:IsCoprime (a*b) d:=by
    apply (isUnit_quotient_span_iff (a*b) d).mp
    simpa only [d,GaussianShiftedPartition.representative_spec] using r.2
  (⟨Ideal.Quotient.mk (Ideal.span {a}) d,
      (isUnit_quotient_span_iff a d).mpr hd.of_mul_left_left⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr hd.of_mul_left_right⟩)

lemma cubicUnitCRTMap_injective (a b : Eis) (hab : IsCoprime a b) :
    Function.Injective (cubicUnitCRTMap a b) := by
  intro r t he
  have h1:=congrArg (fun z : CubicUnitResidue a × CubicUnitResidue b=>z.1.1) he
  have h2:=congrArg (fun z : CubicUnitResidue a × CubicUnitResidue b=>z.2.1) he
  change Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) t.1) at h1
  change Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) t.1) at h2
  have hdiv : a*b ∣ GaussianShiftedPartition.representative (a*b) r.1-
      GaussianShiftedPartition.representative (a*b) t.1 :=
    hab.mul_dvd
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1))
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2))
  apply Subtype.ext
  rw [←GaussianShiftedPartition.representative_spec (a*b) r.1,
    ←GaussianShiftedPartition.representative_spec (a*b) t.1]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hdiv)

lemma cubicUnitCRTMap_surjective (a b : Eis) (hab : IsCoprime a b) :
    Function.Surjective (cubicUnitCRTMap a b) := by
  rintro ⟨r,t⟩
  obtain ⟨u,v,huv⟩:=hab
  let delta:=GaussianShiftedPartition.representative a r.1
  let xi:=GaussianShiftedPartition.representative b t.1
  let d:=v*b*delta+u*a*xi
  have hda:a∣d-delta:=⟨u*(xi-delta),by dsimp [d];linear_combination delta*huv⟩
  have hdb:b∣d-xi:=⟨v*(delta-xi),by dsimp [d];linear_combination xi*huv⟩
  have had:IsCoprime a delta:=by
    apply (isUnit_quotient_span_iff a delta).mp
    simpa only [delta,GaussianShiftedPartition.representative_spec] using r.2
  have hbd:IsCoprime b xi:=by
    apply (isUnit_quotient_span_iff b xi).mp
    simpa only [xi,GaussianShiftedPartition.representative_spec] using t.2
  have hd:IsCoprime (a*b) d:=
    ((isCoprime_right_congr_of_dvd a d delta hda).mpr had).mul_left
      ((isCoprime_right_congr_of_dvd b d xi hdb).mpr hbd)
  let q:CubicUnitResidue (a*b):=⟨Ideal.Quotient.mk (Ideal.span {a*b}) d,
    (isUnit_quotient_span_iff (a*b) d).mpr hd⟩
  refine ⟨q,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) q.1)=r.1
    rw [←GaussianShiftedPartition.representative_spec a r.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh:a∣GaussianShiftedPartition.representative (a*b) q.1-d:=
      (dvd_mul_right a b).trans (gaussRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hda
  · change Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) q.1)=t.1
    rw [←GaussianShiftedPartition.representative_spec b t.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh:b∣GaussianShiftedPartition.representative (a*b) q.1-d:=
      (dvd_mul_left b a).trans (gaussRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hdb

def cubicUnitCRTEquiv (a b:Eis) (hab:IsCoprime a b):
    CubicUnitResidue (a*b)≃CubicUnitResidue a×CubicUnitResidue b:=
  Equiv.ofBijective (cubicUnitCRTMap a b)
    ⟨cubicUnitCRTMap_injective a b hab,cubicUnitCRTMap_surjective a b hab⟩

lemma residueAdditive_unit_crt (h a b alpha beta d:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1):
    residueAdditive (3*h) (a*b) d=
      residueAdditive (3*(h*alpha)) a d*residueAdditive (3*(h*beta)) b d:=by
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  have hbeq:=congrArg eisEmbedding hbez
  simp only [map_add,map_mul,map_one] at hbeq
  simp only [cuspFrequency,map_mul,map_ofNat]
  field_simp [hae,hbe,eisLam_ne_zero]
  linear_combination -(eisEmbedding h*eisEmbedding d)*hbeq

lemma cubicUnitCRT_summand (h a b alpha beta:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1) (r:CubicUnitResidue (a*b)):
    eisEmbedding (symbol (GaussianShiftedPartition.representative (a*b) r.1) (a*b))*
      residueAdditive (3*h) (a*b) (GaussianShiftedPartition.representative (a*b) r.1)=
    (eisEmbedding (symbol (GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1) a)*
      residueAdditive (3*(h*alpha)) a (GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1))*
    (eisEmbedding (symbol (GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1)):=by
  let d:=GaussianShiftedPartition.representative (a*b) r.1
  let delta:=GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1
  let xi:=GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1
  have hdelta:a∣delta-d:=gaussRep_mk_congr a d
  have hxi:b∣xi-d:=gaussRep_mk_congr b d
  change eisEmbedding (symbol d (a*b))*residueAdditive (3*h) (a*b) d=
    (eisEmbedding (symbol delta a)*residueAdditive (3*(h*alpha)) a delta)*
    (eisEmbedding (symbol xi b)*residueAdditive (3*(h*beta)) b xi)
  rw [symbol_mul_denominator,map_mul,symbol_congr hdelta,symbol_congr hxi,
    residueAdditive_unit_crt h a b alpha beta d ha hb hbez,
    residueAdditive_three_congr (h*alpha) a delta d ha hdelta,
    residueAdditive_three_congr (h*beta) b xi d hb hxi]
  ring

theorem cubicUnitGaussSum_crt (h a b alpha beta:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1):
    cubicUnitGaussSum h (a*b)=
      cubicUnitGaussSum (h*alpha) a*cubicUnitGaussSum (h*beta) b:=by
  have hab:IsCoprime a b:=⟨beta,alpha,by linear_combination hbez⟩
  let f:CubicUnitResidue a→ℂ:=fun r=>eisEmbedding
    (symbol (GaussianShiftedPartition.representative a r.1) a)*
    residueAdditive (3*(h*alpha)) a (GaussianShiftedPartition.representative a r.1)
  let g:CubicUnitResidue b→ℂ:=fun r=>eisEmbedding
    (symbol (GaussianShiftedPartition.representative b r.1) b)*
    residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b r.1)
  have he:cubicUnitGaussSum h (a*b)=∑'r:CubicUnitResidue (a*b),
      f (cubicUnitCRTEquiv a b hab r).1*g (cubicUnitCRTEquiv a b hab r).2:=by
    unfold cubicUnitGaussSum
    apply tsum_congr
    intro r
    exact cubicUnitCRT_summand h a b alpha beta ha hb hbez r
  rw [he,(cubicUnitCRTEquiv a b hab).tsum_eq (fun r=>f r.1*g r.2)]
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span ha
  let:Finite (Eis⧸Ideal.span {b}):=finite_quotient_span hb
  let:Fintype (CubicUnitResidue a):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue b):=Fintype.ofFinite _
  change (∑'r:CubicUnitResidue a×CubicUnitResidue b,f r.1*g r.2)=
    (∑'r:CubicUnitResidue a,f r)*(∑'r:CubicUnitResidue b,g r)
  simp only [tsum_fintype,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

theorem cubicUnitGaussSum_coprime_product (h a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b):
    cubicUnitGaussSum h (a*b)=cubicUnitGaussSum h a*cubicUnitGaussSum (h*a) b:=by
  obtain ⟨beta,alpha,hbez⟩:=hab
  have hbez':alpha*b+beta*a=1:=by linear_combination hbez
  have hab':IsCoprime a b:=⟨beta,alpha,hbez⟩
  have hA:=cubicUnitGaussSum_frequency_twist (h*alpha) a b ha hap hab'
  rw [cubicUnitGaussSum_frequency_congr _ h a ha
    (show a∣(h*alpha)*b-h from ⟨-h*beta,by linear_combination h*hbez'⟩)] at hA
  have hB:=cubicUnitGaussSum_frequency_twist (h*beta) b a hb hbp hab'.symm
  rw [cubicUnitGaussSum_frequency_congr _ h b hb
    (show b∣(h*beta)*a-h from ⟨-h*alpha,by linear_combination h*hbez'⟩)] at hB
  rw [cubicUnitGaussSum_crt h a b alpha beta ha hb hbez',←hA,←hB,
    symbol_reciprocity b a hb ha hbp hap]
  have hshift:=cubicUnitGaussSum_frequency_twist h b a hb hbp hab'.symm
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hbp hab',map_one]
  rw [←hshift]
  calc
    _=(eisEmbedding (symbol a b))^3*cubicUnitGaussSum h a*cubicUnitGaussSum (h*a) b:=by ring
    _=_:=by rw [hc,one_mul]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedCongruence_zero (j : Fin 3) (n : ℕ) :
    ramifiedCongruence (0:Eis) j.val n ↔ j=0 ∧ 3∣n := by
  have hz : ActualEisensteinCoordinates.coords (0:Eis)=(0,0) := by
    have hh:=ShortDraftLatticeCount.coords_eval 0 0
    simpa [ActualEisensteinCoordinates.eval] using hh
  simp only [ramifiedCongruence,hz,add_zero,sub_zero]
  rw [←Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨h1,h2⟩
    have hj : j.val=0 := by omega
    exact ⟨Fin.ext hj,by simpa only [hj,Nat.cast_zero,Nat.cast_ofNat,mul_zero,zero_add] using h1⟩
  · rintro ⟨rfl,hn⟩
    simpa using And.intro hn (dvd_zero (3:ℤ))

lemma arithmeticResidueSum_zero_ramified (u : Eisˣ) (n : ℕ) :
    arithmeticResidueSum 0 (u.val*lambda^(n+2))=
      if u=1 ∨ u= -1 then if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0 else 0 := by
  have hp : residueAdditive (0:Eis) 3 1=1 := by
    simp [residueAdditive,cuspFrequency]
  by_cases hu : u=1 ∨ u= -1
  · have hs : (u:Eis)=omega^0 ∨ (u:Eis)=-(omega^0) := by
      rcases hu with rfl|rfl <;> simp
    rw [ramified_arithmetic_explicit_table 0 0 u (n+2) 0 (by omega) hs (by simp),
      show ramifiedCongruence (0:Eis) 0 (n+2) ↔ 3∣n+2 by
        simpa using ramifiedCongruence_zero (0:Fin 3) (n+2),hp,mul_one,ite_eq_left hu]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
  · obtain ⟨j,hj⟩:=unit_eq_sign_omega u
    have hj0 : j≠0 := by
      intro he
      subst j
      apply hu
      rcases hj with hj|hj
      · left; apply Units.ext; simpa using hj
      · right; apply Units.ext; simpa using hj
    rw [ramified_arithmetic_explicit_table 0 0 u (n+2) j.val (by omega) hj (by simp),
      ramifiedCongruence_zero,ite_eq_right (by simp [hj0]),ite_eq_right hu]

lemma arithmeticDirichletSeries_zero_separate (s : ℂ) (hs : 2<s.re) :
    arithmeticDirichletSeries s 0=
      (∑'u:Eisˣ,∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
        arithmeticResidueSum 0 (u.val*lambda^(n+2)))*unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs 0,←tsum_mul_right]
  apply tsum_congr
  intro u
  rw [←tsum_mul_right]
  apply tsum_congr
  intro n
  rw [unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  change (if ramifiedLower u n I=0 then 0 else
    ((‖eisEmbedding (ramifiedLower u n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (ramifiedLower u n I))=_
  rw [ite_eq_right (ramifiedLower_ne_zero u n I),eisEmbedding_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,ramifiedLower_span,map_mul,map_pow,ramifiedIdeal_absNorm,
    Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  rw [show arithmeticResidueSum 0 (ramifiedLower u n I)=
      eisEmbedding (symbol (u.val*lambda^(n+2)) (primaryGenerator I.1))*
      eisEmbedding (symbol (3*(u.val*lambda^(n+2))) (primaryGenerator I.1))*
      arithmeticResidueSum 0 (u.val*lambda^(n+2))*cubicUnitGaussSum 0 (primaryGenerator I.1) from
    arithmeticResidueSum_ramified_split 0 u (n+2) (by omega) _ hp]
  have hg:=cubicUnitGaussSum_phase_shift 0 (u.val*lambda^(n+2)) (primaryGenerator I.1)
    I.2 hp (ramified_primary_coprime u (n+2) _ hp)
  simp only [zero_mul] at hg
  linear_combination ((3^(n+2):ℕ):ℂ)^(-s)*(Ideal.absNorm I.1:ℂ)^(-s)*
    arithmeticResidueSum 0 (u.val*lambda^(n+2))*hg

def ramifiedCubeExponent : ℕ ≃ {n:ℕ // 3∣n+2} :=
  Equiv.ofBijective (fun k=>⟨3*k+1,by use k+1;omega⟩) ⟨by
    intro a b h
    have hh:=congrArg Subtype.val h
    dsimp at hh
    omega,by
    rintro ⟨n,k,hk⟩
    refine ⟨k-1,Subtype.ext ?_⟩
    dsimp
    omega⟩

lemma zero_ramified_geometric (s : ℂ) (hs : 1<s.re) :
    (∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
      (if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0))=((3:ℂ)^(3*s-3)-1)⁻¹ := by
  let F : ℕ→ℂ := fun n=>((3^(n+2):ℕ):ℂ)^(-s)*
    (if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0)
  have hsup:Function.support F⊆{n:ℕ|3∣n+2} := by
    intro n hn
    by_contra h
    change ¬3∣n+2 at h
    exact hn (by simp [F,h])
  change (∑'n,F n)=_
  rw [←tsum_subtype_eq_of_support_subset hsup]
  change (∑'n : {n:ℕ // 3∣n+2},F n.val)=_
  rw [←ramifiedCubeExponent.tsum_eq]
  have he (k:ℕ) : F (ramifiedCubeExponent k).val=ramifiedRatio s^(k+1) := by
    change ((3^(3*k+1+2):ℕ):ℂ)^(-s)*(if 3∣3*k+1+2 then ((3^(3*k+1+2):ℕ):ℂ) else 0)=_
    rw [ite_eq_left (by use k+1;omega),show 3*k+1+2=3*(k+1) by omega]
    simpa using cube_norm_weight_algebra s k 1 (by decide)
  simp_rw [he]
  exact ramified_geometric_sum s hs

lemma zero_ramified_factor (s : ℂ) (hs : 1<s.re) :
    (∑'u:Eisˣ,∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
      arithmeticResidueSum 0 (u.val*lambda^(n+2)))=
      2*((3:ℂ)^(3*s-3)-1)⁻¹ := by
  have hne : (1:Eisˣ)≠ -1 := by
    intro h
    have hh:=congrArg Units.val h
    norm_num at hh
  rw [tsum_eq_sum (s:={1,-1}) (fun u hu=>by
    have hn : ¬(u=1 ∨ u= -1):=by simpa using hu
    simp [arithmeticResidueSum_zero_ramified,hn])]
  simp only [Finset.sum_insert,Finset.mem_singleton,hne,not_false_eq_true,Finset.sum_singleton]
  simp only [arithmeticResidueSum_zero_ramified,true_or,or_true,ite_true]
  rw [zero_ramified_geometric s hs]
  ring

theorem arithmeticDirichletSeries_zero_unramified (s : ℂ) (hs : 2<s.re) :
    arithmeticDirichletSeries s 0=
      (2*((3:ℂ)^(3*s-3)-1)⁻¹)*unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_zero_separate s hs,zero_ramified_factor s (by linarith)]

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage -/

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma ramified_denominator_ne_zero (s : ℂ) (hs : 1<s.re) :
    (3:ℂ)^(3*s-3)-1≠0 := by
  intro he
  have hpow : (3:ℂ)^(3*s-3)=1 := sub_eq_zero.mp he
  have hnorm : 1<‖(3:ℂ)^(3*s-3)‖ := by
    rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.one_lt_rpow (by norm_num)
    norm_num
    linarith
  rw [hpow,norm_one] at hnorm
  exact lt_irrefl _ hnorm

theorem unramifiedCubicGaussSeries_zero (s : ℂ) (hs : 2<s.re) :
    unramifiedCubicGaussSeries s 0=unramifiedTotientSeries (3*s-2) := by
  have he:=arithmeticDirichletSeries_zero_unramified s hs
  rw [arithmeticDirichletSeries_zero_totient s (by linarith)] at he
  exact (mul_left_cancel₀ (mul_ne_zero (by norm_num) (inv_ne_zero (ramified_denominator_ne_zero s (by linarith)))) he).symm

lemma cuspWhittakerHeightFactor_zero (s : ℂ) (hs : 1<s.re) :
    cuspWhittakerHeightFactor s 0=((Real.pi:ℂ)/(s-1))*cuspScatterHeightFactor s := by
  have hs0 : s≠0 := by intro he;subst s;norm_num at hs
  unfold cuspWhittakerHeightFactor
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero s hs]
  rw [integral_mul_const,cuspScatterHeightFactor_integral s hs0]
  ring

lemma opposite_zero_initial_cross (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s=
      ((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s := by
  have hb : kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s=cuspConstantAverage s := by
    apply (kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num)
      s (by linarith) (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi)).trans
    exact hyperbolicEisenstein_cusp_average_eq s (by linarith)
  have ht:=translatedCuspFamily_opposite_initial 0 s hs hi
  simp only [mul_zero] at ht
  rw [ht,cuspWhittakerHeightFactor_zero s (by linarith),baseOutgoingConstant,hb,
    cuspConstantAverage,scatteringCoefficient,arithmeticDirichletSeries_zero_unramified s (by linarith)]
  have hs1 : s-1≠0 := by intro he;have hsx : s=1:=sub_eq_zero.mp he;subst s;norm_num at hs
  have halg (D V A P H U : ℂ) (hD:D≠0) (hV:V≠0) :
      2*(U*(P*H))=D*(V*(A+P*((2*D⁻¹)*U/V)*H)-V*A) := by
    field_simp
    ; ring
  exact halg _ _ _ _ _ _ (ramified_denominator_ne_zero s (by linarith)) cusp_volume_ne_zero

lemma opposite_zero_cross_identity :
    Set.EqOn (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s)
      {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s) domain := by
    intro s hs
    exact analyticAt_const.mul (translatedCuspFamily_analyticAt_nonreal 0 oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hright : AnalyticOnNhd ℂ
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) domain := by
    intro s hs
    have hp : AnalyticAt ℂ (fun z:ℂ=>(3:ℂ)^(3*z-3)-1) s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      exact Eventually.of_forall fun z=>
        ((((differentiableAt_const (3:ℂ)).mul differentiableAt_id).sub_const 3).const_cpow
          (Or.inl (by norm_num))).sub_const 1
    exact hp.mul (baseOutgoingConstant_analyticAt s hs.1 hs.2)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact opposite_zero_initial_cross s hs.1 hs.2
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

theorem translatedCuspFourier_opposite_zero_residue :
    translatedCuspFourier 0 oppositeSource cubicEisensteinResidue=cuspConstantAverageResidue := by
  have hd : Tendsto (fun s:ℂ=>(3:ℂ)^(3*s-3)-1) (𝓝[≠] (4/3:ℂ)) (𝓝 (2:ℂ)) := by
    have hc : Continuous (fun s:ℂ=>(3:ℂ)^(3*s-3)-1) :=
      (((continuous_const.mul continuous_id).sub continuous_const).const_cpow
        (Or.inl (by norm_num))).sub continuous_const
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hl := ((translatedCuspFamily_residue_limit 0 oppositeSource 2 3
    (by norm_num) (by norm_num)).const_mul 2).comp upperVertical_tendsto_cubic_punctured
  have hr := (hd.mul baseOutgoingConstant_residue_limit).comp upperVertical_tendsto_cubic_punctured
  have hevent : (fun t:ℝ=>2*((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((3:ℂ)^(3*((4/3:ℂ)+(t:ℂ)*Complex.I)-3)-1)*
        ((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*baseOutgoingConstant ((4/3:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=opposite_zero_cross_identity (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : 2*translatedCuspFourier 0 oppositeSource cubicEisensteinResidue=2*cuspConstantAverageResidue :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hevent
  exact mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) heq

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rationalComplex_conjugate (r:SL(2,ℤ)) (M:levelThree) :
    complexMatrix (levelThreeConjugate (rationalEmbedding r) M)*rationalComplex r=
      rationalComplex r*complexMatrix M := by
  rw [←integralComplexMatrix_levelThree,←integralComplexMatrix_levelThree]
  change integralComplexMatrix ((rationalEmbedding r)*(M:SL(2,Eis))*(rationalEmbedding r)⁻¹)*
    integralComplexMatrix (rationalEmbedding r)=
      integralComplexMatrix (rationalEmbedding r)*integralComplexMatrix (M:SL(2,Eis))
  rw [←map_mul,inv_mul_cancel_right,map_mul]

lemma hyperbolicEisenstein_rational_automorphy (r:SL(2,ℤ)) (M:levelThree)
    (s:ℂ) (hs:2<s.re) (w:HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex r • (complexMatrix M • w))=
      complexCharacter M*hyperbolicEisenstein s (rationalComplex r • w) := by
  rw [←mul_smul,←rationalComplex_conjugate,mul_smul,hyperbolicEisenstein_automorphy _ _ hs,
    complexCharacter_conjugate_rational]

lemma hyperbolicEisenstein_rational_periodic (r:SL(2,ℤ)) (a:Eis)
    (s:ℂ) (hs:2<s.re) (z:ℂ) (v:ℝ) (hv:0<v) :
    hyperbolicEisenstein s (rationalComplex r • upperPoint (z+3*eisEmbedding a) v hv)=
      hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv) := by
  have he : upperPoint (z+3*eisEmbedding a) v hv=complexMatrix (upperTranslation a) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace)) (upperTranslation_section a z v hv).symm
  rw [he,hyperbolicEisenstein_rational_automorphy r _ s hs,complexCharacter_upperTranslation,one_mul]

lemma rationalComplex_unipotent_coe (t : ℤ) :
    (rationalComplex (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1,(t : ℂ);0,1] := by
  apply Matrix.ext
  intro i j
  change eisEmbedding ((Int.castRingHom Eis) ((!![1,t;0,1] : Matrix (Fin 2) (Fin 2) ℤ) i j)) = _
  fin_cases i <;> fin_cases j <;> simp

lemma rationalUnipotent_section (t:ℤ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex (rationalUnipotent t)*upperSection z v hv=upperSection (z+t) v hv := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, rationalComplex_unipotent_coe]
  change (!![1,(t : ℂ);0,1] *
    !![(Real.sqrt v : ℂ),z/(Real.sqrt v : ℂ);0,(Real.sqrt v : ℂ)⁻¹] :
      Matrix (Fin 2) (Fin 2) ℂ) =
    !![(Real.sqrt v : ℂ),(z+t)/(Real.sqrt v : ℂ);0,(Real.sqrt v : ℂ)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

lemma rationalComplex_T_pow_upper (n:ℕ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex (ModularGroup.T^n) • upperPoint z v hv=upperPoint (z+n) v hv := by
  change ((rationalComplex (ModularGroup.T^n)*upperSection z v hv):HyperbolicSpace)=
    (upperSection (z+(n:ℂ)) v hv:HyperbolicSpace)
  have he:=congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace)) (rationalUnipotent_section (n:ℤ) z v hv)
  simpa only [rationalUnipotent_nat,Int.cast_natCast] using he

theorem rational_cusp_average_right_T (r:SL(2,ℤ)) (n:ℕ) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)∂hyperbolicVolume)=
    ∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex r • w)∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (rationalComplex r • w)
  have hf : Continuous f := (hyperbolicEisenstein_continuous s hs).comp (continuous_hyperbolic_action _)
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).comp (continuous_hyperbolic_action _)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  apply congrArg (fun q:ℂ=>q/(v:ℂ)^3)
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper]
  have hh:=period_integral_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) (n:ℂ)
  simpa only [add_comm] using hh

lemma cuspFourierPhase_zero (w:HyperbolicSpace) : cuspFourierPhase (0:Eis) w=1 := by
  simp [cuspFourierPhase,cuspFrequency]

lemma kernelCuspFourier_zero (F:KernelQuotientL2) :
    kernelCuspFourier (0:Eis) F=kernelCuspStripAverage F := by
  rw [kernelCuspFourier_integral,kernelCuspStripAverage_hyperbolic]
  simp only [cuspFourierPhase_zero,mul_one]

theorem translatedCuspFourier_residue_eq_of_initial (M N:levelTwo)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)∂hyperbolicVolume)=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)∂hyperbolicVolume) :
    translatedCuspFourier 0 M cubicEisensteinResidue=
      translatedCuspFourier 0 N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily 0 M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := translatedCuspFamily 0 N 2 3 (by norm_num) (by norm_num)
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal 0 M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal 0 N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial 0 M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial 0 N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    simp only [cuspFourierPhase_zero,mul_one]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit 0 M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := (translatedCuspFamily_residue_limit 0 N 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  exact congrArg (fun z:ℂ=>((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*z) hv

end

open CubicKubota

lemma sourceComplexMatrix_rationalLift (r:SL(2,ℤ)) :
    sourceComplexMatrix (rationalLift r)=rationalComplex r := rfl

lemma translatedCuspFourier_one_residue :
    translatedCuspFourier 0 1 cubicEisensteinResidue=cuspConstantAverageResidue := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one,
    kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average]

lemma translatedCuspFourier_bruhat_residue (i:RationalBruhatIndex) :
    translatedCuspFourier 0 (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue=
      cuspConstantAverageResidue := by
  rcases i with ⟨e,a|⟨a,b⟩⟩
  · calc
      _=translatedCuspFourier 0 1 cubicEisensteinResidue := by
        apply translatedCuspFourier_residue_eq_of_initial
        intro s hs hi
        simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
        simp only [map_one,one_smul]
      _=cuspConstantAverageResidue := translatedCuspFourier_one_residue
  · calc
      _=translatedCuspFourier 0 oppositeSource cubicEisensteinResidue := by
        apply translatedCuspFourier_residue_eq_of_initial
        intro s hs hi
        simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
        change (∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex ModularGroup.S •
            (rationalComplex (ModularGroup.T^b.val) • w))∂hyperbolicVolume)=
          ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)∂hyperbolicVolume
        simpa only [map_mul,mul_smul] using
          rational_cusp_average_right_T ModularGroup.S b.val s (by linarith)
      _=cuspConstantAverageResidue := translatedCuspFourier_opposite_zero_residue

theorem kernelSourceProjection_residue_cusp_average :
    kernelCuspStripAverage (kernelSourceProjection cubicEisensteinResidue)=
      cuspConstantAverageResidue := by
  rw [←kernelCuspFourier_zero,kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  have he (i:RationalBruhatIndex) :
      kernelCuspFourier 0 (kernelSourcePullback (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=
        cuspConstantAverageResidue := translatedCuspFourier_bruhat_residue i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_fin,smul_eq_mul,nsmul_eq_mul]
  norm_num
  ring

theorem kernelSourceProjection_cubicEisensteinResidue_ne_zero :
    kernelSourceProjection cubicEisensteinResidue≠0 := by
  intro hz
  have hh:=kernelSourceProjection_residue_cusp_average
  rw [hz,map_zero] at hh
  exact cuspConstantAverageResidue_ne_zero hh.symm

theorem cubicSourceResidualFunction_cusp_average :
    (∫w in cuspPeriodStrip 5 6,cubicSourceResidualFunction w∂hyperbolicVolume)=
      cuspConstantAverageResidue := by
  rw [←kernelSourceProjection_residue_cusp_average,kernelCuspStripAverage_hyperbolic]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae cubicSourceResidualFunction_represents_projection] with w hw
  exact hw.symm

theorem cubicSourceResidualFunction_ne_zero : cubicSourceResidualFunction≠0 := by
  intro hz
  have he:=cubicSourceResidualFunction_cusp_average
  rw [hz] at he
  simp only [Pi.zero_apply,integral_zero] at he
  exact cuspConstantAverageResidue_ne_zero he.symm

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

lemma complex_gaussian_power_integrable (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0< r) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2))
      (Set.Ioi 0) volume := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t:ℂ))) (s/2) := by
    simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm]
      using Complex.GammaIntegral_convergent hs2
  have hlinear := (MellinConvergent.comp_mul_left
    (f := fun t : ℝ => Complex.exp (-(t:ℂ))) (s := s/2) hr).mpr hbase
  have hgaussian := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) (s := s) (a := 2)
      (by norm_num)).mpr hlinear
  simpa only [MellinConvergent,smul_eq_mul,Real.rpow_two,
    Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using hgaussian

lemma complex_gaussian_power_integral (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0< r) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2)) =
      (1/2:ℂ)*((1/(r:ℂ))^(s/2)*Complex.Gamma (s/2)) := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have he := mellin_comp_rpow (fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) s 2
  simp only [mellin,smul_eq_mul,Real.rpow_two,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.real_smul] at he
  norm_num only [Complex.ofReal_ofNat] at he
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs2 hr] at he
  simpa [neg_mul] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def cubicMellinMixture (s : ℂ) (t x : ℝ) : ℂ :=
  (t:ℂ)^(-(2:ℂ)/3)*Complex.exp (-(t:ℂ))*
    ((x:ℂ)^((s-1/3)-1)*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2))

lemma cubicMellinMixture_slice_integrable (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    IntegrableOn (cubicMellinMixture s t) (Set.Ioi 0) volume := by
  apply (complex_gaussian_power_integrable (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)).const_mul

lemma cubicMellinMixture_integral_x (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
  simp only [cubicMellinMixture,integral_const_mul]
  rw [complex_gaussian_power_integral (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)]
  have hb : (1/(((1/(4*t):ℝ):ℂ)))=(4:ℂ)*(t:ℂ) := by
    push_cast
    field_simp
  have hm : ((4:ℂ)*(t:ℂ))^((s-1/3)/2)=
      (4:ℂ)^((s-1/3)/2)*(t:ℂ)^((s-1/3)/2) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : 0≤(4:ℝ)) ht.le ((s-1/3)/2)
  rw [hb,hm]
  have hp : (t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2)=
      (t:ℂ)^((s+1/3)/2-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        (((t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2))*Complex.exp (-(t:ℂ))) := by ring
    _ = _ := by rw [hp]

lemma cubicMellinMixture_norm (s : ℂ) (t x : ℝ) (ht : 0<t) (hx : 0<x) :
    ‖cubicMellinMixture s t x‖ =
      (t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
  have he : -((1/(4*t):ℝ):ℂ)*(x:ℂ)^2=(-(1/(4*t))*x^2:ℝ) := by
    push_cast
    rfl
  simp only [cubicMellinMixture,norm_mul,he,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp,Complex.ofReal_re,Complex.neg_re]
  norm_num

lemma real_gaussian_power_integral (sigma r : ℝ) (hs : 0<sigma) (hr : 0< r) :
    (∫x : ℝ in Set.Ioi 0,x^(sigma-1)*Real.exp (-r*x^2)) =
      r^(-sigma/2)*(1/2)*Real.Gamma (sigma/2) := by
  simpa only [Real.rpow_two,sub_add_cancel] using
    (_root_.integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=sigma-1) (b:=r)
      (by norm_num) (by linarith) hr)

lemma cubicMellinMixture_integral_norm (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,‖cubicMellinMixture s t x‖) =
      ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
        (t^((s.re+1/3)/2-1)*Real.exp (-t)) := by
  calc
    _ = ∫x : ℝ in Set.Ioi 0,(t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact cubicMellinMixture_norm s t x ht hx
    _ = _ := by
      rw [integral_const_mul,real_gaussian_power_integral (s.re-1/3) (1/(4*t))
        (by linarith) (by positivity)]
      have hpow : (1/(4*t):ℝ)^(-(s.re-1/3)/2)=(4:ℝ)^((s.re-1/3)/2)*t^((s.re-1/3)/2) := by
        rw [show -(s.re-1/3)/2=-((s.re-1/3)/2) by ring,
          Real.rpow_neg_eq_inv_rpow,one_div,inv_inv,
          Real.mul_rpow (by norm_num : 0≤(4:ℝ)) ht.le]
      rw [hpow]
      have hp : t^(-(2:ℝ)/3)*t^((s.re-1/3)/2)=t^((s.re+1/3)/2-1) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
            ((t^(-(2:ℝ)/3)*t^((s.re-1/3)/2))*Real.exp (-t)) := by ring
        _ = _ := by rw [hp]

lemma cubicMellinMixture_integrable (s : ℂ) (hs : 1/3<s.re) :
    Integrable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    unfold cubicMellinMixture
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicMellinMixture_slice_integrable s hs t ht
  · have hg := (Real.GammaIntegral_convergent
        (show 0<(s.re+1/3)/2 by linarith)).const_mul
        ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))
    apply hg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [cubicMellinMixture_integral_norm s hs t ht]
    ring

lemma cubicMellinMixture_integral_t (s : ℂ) (x : ℝ) :
    (∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      (x:ℂ)^((s-1/3)-1)*schlafliIntegral (1/3) x := by
  rw [schlafliIntegral,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have he : Complex.exp (-(t:ℂ))*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2)=
      Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t)) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [show (1/3:ℂ)-1=-(2:ℂ)/3 by ring]
  unfold cubicMellinMixture
  linear_combination (t:ℂ)^(-(2:ℂ)/3)*(x:ℂ)^((s-1/3)-1)*he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma schlafliBesselK_cubic_mellin_mixture (s : ℂ) (x : ℝ) (hx : 0<x) :
    (x:ℂ)^(s-1)*schlafliBesselK (1/3) x =
      ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*(∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
  rw [schlafliBesselK,cubicMellinMixture_integral_t]
  have hdiv : (x/2:ℂ)^(-(1/3:ℂ))=(x:ℂ)^(-(1/3:ℂ))/(2:ℂ)^(-(1/3:ℂ)) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.div_cpow_ofReal_nonneg hx.le (by norm_num : 0≤(2:ℝ)) (-(1/3:ℂ))
  rw [hdiv,Complex.cpow_neg (2:ℂ) (1/3),div_inv_eq_mul]
  have hp : (x:ℂ)^(s-1)*(x:ℂ)^(-(1/3:ℂ))=(x:ℂ)^((s-1/3)-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring
  linear_combination (1/2:ℂ)*(2:ℂ)^(1/3:ℂ)*schlafliIntegral (1/3) x*hp

lemma schlafliBesselK_cubic_mellin_integrable (s : ℂ) (hs : 1/3<s.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*schlafliBesselK (1/3) x)
      (Set.Ioi 0) volume := by
  apply ((cubicMellinMixture_integrable s hs).integral_prod_right.const_mul
    ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (schlafliBesselK_cubic_mellin_mixture s x hx).symm

lemma cubicMellinMixture_double_integral (s : ℂ) (hs : 1/3<s.re) :
    (∫t : ℝ in Set.Ioi 0,∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        Complex.Gamma ((s+1/3)/2) := by
  have hB : 0<((s+1/3)/2).re := by norm_num; linarith
  calc
    _ = ∫t : ℝ in Set.Ioi 0,
        ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cubicMellinMixture_integral_x s hs t ht
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [Complex.GammaIntegral,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm] using
        (Complex.Gamma_eq_integral hB).symm

theorem schlafliBesselK_cubic_mellin (s : ℂ) (hs : 1/3<s.re) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*schlafliBesselK (1/3) x) =
      (2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by
  have hmix : Integrable (Function.uncurry (cubicMellinMixture s))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    convert cubicMellinMixture_integrable s hs using 1
    funext p
    rcases p with ⟨t,x⟩
    rfl
  have hswap := (integral_integral_swap hmix).symm
  have h4 : (4:ℂ)^((s-1/3)/2)=(2:ℂ)^(2*((s-1/3)/2)) := by
    have hh := (Complex.natCast_cpow_natCast_mul 2 2 ((s-1/3)/2)).symm
    norm_num at hh
    exact hh
  have hprod : (2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)=(2:ℂ)^s := by
    rw [h4,←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  have hscale : (1/4:ℂ)*(2:ℂ)^s=(2:ℂ)^(s-2) := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
    ring
  calc
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (∫x : ℝ in Set.Ioi 0,∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact schlafliBesselK_cubic_mellin_mixture s x hx
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          Complex.Gamma ((s+1/3)/2)) := by
      rw [hswap,cubicMellinMixture_double_integral s hs]
    _ = ((1/4:ℂ)*((2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)))*
        Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by ring
    _ = _ := by rw [hprod,hscale]

end CubicEisenstein

end

end OAI

end

