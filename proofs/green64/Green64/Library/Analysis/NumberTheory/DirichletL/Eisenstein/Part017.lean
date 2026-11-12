module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part016

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part017

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.RamifiedSixBranches -/

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
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def arbitraryIntervalWhittaker (a b:ℝ) (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) :ℂ:=
  ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v)

lemma arbitraryIntervalWhittaker_analyticAt (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:1<s.re) :
    AnalyticAt ℂ (arbitraryIntervalWhittaker a b ρ freq) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact cuspWeightedWhittakerInterval_differentiableAt ρ a b ha freq w hw

lemma ramifiedSource_height_fourier_average (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))•w)*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
      ramifiedCuspGaussSeries side h hf s*arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) s := by
  let M:=integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))
  let g:HyperbolicSpace→ℂ:=fun w=>sourceEisenstein s (M•w)*
    arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w
  have hg:Continuous g:=((sourceProjection_continuous _ (hyperbolicEisenstein_continuous s hs)).comp
    (continuous_hyperbolic_action M)).mul (arbitraryCuspWeightedPhase_continuous ρ _)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  rw [arbitraryIntervalWhittaker,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
  have hinner:(∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ramifiedCuspGaussSeries side h hf s:=by
    simp only [g,cuspCoordinateLift_positive v _ hv0,arbitraryCuspWeightedPhase,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    have he (z:ℂ):sourceEisenstein s (M•upperPoint z v hv0)*
        (ρ v*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ρ v*(sourceEisenstein s (M•upperPoint z v hv0)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z)):=by ring
    simp_rw [he]
    rw [integral_const_mul,ramifiedSourceEisenstein_fourier side h hf v hv0 s hs]
    ring
  have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3:=by
    rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only
  rw [hinner,hp]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

abbrev RamifiedSixBranch := Unit ⊕ (Unit ⊕ (Unit ⊕ Fin 3))

def unitCuspUnramifiedIndex (u t:Eisˣ) (h:Eis) :Eis:=
  3*((↑u⁻¹:Eis)^2*(t:Eis))^2*((↑t⁻¹:Eis)*h)

def ramifiedSixIndex (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) :RamifiedSixBranch→Eis
  | .inl _=>unitCuspUnramifiedIndex 1 (ramifiedCuspRoot side) h
  | .inr (.inl _)=>unitCuspUnramifiedIndex (-(ramifiedCuspRoot side)) (-(ramifiedCuspRoot side)) h
  | .inr (.inr (.inl _))=>unitCuspUnramifiedIndex (-(ramifiedCuspRoot side)) 1 h
  | .inr (.inr (.inr l))=>3*((↑(-(ramifiedCuspRoot side))⁻¹:Eis)^2*
      (onceCuspScale (ramifiedCuspScaleUnit side)*omega^l.val))^2*
        onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf l

def ramifiedSixWeight (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) (s:ℂ) :ℂ:=
  let t:=ramifiedCuspRoot side
  let phase:=ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (↑t⁻¹:Eis))
  match i with
  | .inl _=>(4:ℂ)⁻¹*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))
  | .inr (.inl _)=>(4:ℂ)⁻¹*phase*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding ((-t:Eisˣ):Eis))
  | .inr (.inr (.inl _))=>(4:ℂ)⁻¹*phase*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding ((1:Eisˣ):Eis))
  | .inr (.inr (.inr l))=>(4:ℂ)⁻¹*phase*
      (if (3:Eis)∣onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf l+
          ramifiedAffineParameter (onceCuspRayIndex (-t) (ramifiedCuspScaleUnit side) l).val 1 then
        (3:ℂ)*(3:ℂ)^(-s)*ShortDraftTrace.breveE
          (ninthCuspFrequency h/eisEmbedding (onceCuspScale (ramifiedCuspScaleUnit side)*omega^l.val)) else 0)

lemma ramifiedSixWeight_analytic (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) (s:ℂ) :
    AnalyticAt ℂ (ramifiedSixWeight side h hf i) s := by
  rcases i with i|i
  · exact analyticAt_const
  rcases i with i|i
  · exact analyticAt_const
  rcases i with i|i
  · exact analyticAt_const
  unfold ramifiedSixWeight
  dsimp only
  split_ifs
  · apply analyticAt_const.mul
    apply AnalyticAt.mul _ analyticAt_const
    apply analyticAt_const.mul
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact Eventually.of_forall (fun z=>(differentiableAt_id.neg).const_cpow (Or.inl (by norm_num)))
  · exact analyticAt_const

lemma ramifiedCuspGaussSeries_eq_six (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (s:ℂ) :
    ramifiedCuspGaussSeries side h hf s=
      ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i s*
        unramifiedCubicGaussSeries s (ramifiedSixIndex side h hf i) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_unique,ramifiedSixWeight,ramifiedSixIndex,
    ramifiedCuspGaussSeries,unitCuspGaussSeries,unitCuspUnramifiedIndex,onceCuspGaussSeries]
  simp only [Fin.sum_univ_three]
  split_ifs <;> ring

def ramifiedArithmeticResidue (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) :ℂ:=
  ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i (4/3)*
    unramifiedGaussResidue (ramifiedSixIndex side h hf i)

end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem ramifiedSource_height_residue (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    sourceArbitraryHeightFourier
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)))
      a b ha ρ (ninthCuspFrequency h) cubicEisensteinResidue=
      ramifiedArithmeticResidue side h hf*
        arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) (4/3) := by
  let M:=integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))
  let coeff:RamifiedSixBranch→ℂ→ℂ:=fun i s=>
    ramifiedSixWeight side h hf i s*arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) s
  have hc:∀i s,1<s.re→AnalyticAt ℂ (coeff i) s:=fun i s hs=>
    (ramifiedSixWeight_analytic side h hf i s).mul
      (arbitraryIntervalWhittaker_analyticAt a b ha ρ (ninthCuspFrequency h) s hs)
  have he:=finite_unramified_residue (ramifiedSixIndex side h hf) coeff hc
    (sourceArbitraryHeightFamily M a b ha ρ (ninthCuspFrequency h))
    (sourceArbitraryHeightFourier M a b ha ρ (ninthCuspFrequency h) cubicEisensteinResidue)
    (sourceArbitraryHeightFamily_analyticAt M a b ha ρ (ninthCuspFrequency h))
    (sourceArbitraryHeightFamily_residue_limit M a b ha ρ (ninthCuspFrequency h)) (by
      intro s hs hi
      rw [sourceArbitraryHeightFamily_initial M a b ha ρ (ninthCuspFrequency h) s hs hi,
        ramifiedSource_height_fourier_average side h hf a b ha ρ s (by linarith),
        ramifiedCuspGaussSeries_eq_six,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      dsimp only [coeff]
      ring)
  refine he.trans ?_
  rw [ramifiedArithmeticResidue,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [coeff]
  ring

theorem ramifiedSource_height_residue_integral (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    (∫w in cuspPeriodStrip a b,
      ramifiedSourceFunction (ramifiedCuspRoot side:Eis) w*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
      ramifiedArithmeticResidue side h hf*
        arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) (4/3) := by
  unfold ramifiedSourceFunction
  rw [←sourceArbitraryHeightFourier_residue_integral
    (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))) a b ha ρ (ninthCuspFrequency h)]
  exact ramifiedSource_height_residue side h hf a b ha ρ

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceMatrix (q : IntegralCoverCosets H globalKubotaKernel) : SL(2,ℂ) :=
  g*integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹:globalKubotaKernel):SL(2,ActualEisensteinCubic.O))

lemma kernelCorrespondenceTest_field (f : kernelSmoothTests) (p : EuclideanSpatial) :
    kernelTestField (kernelCorrespondenceTest hHK hJK e g he f) p=
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑q : IntegralCoverCosets H globalKubotaKernel,
        kernelTestField f (euclideanAction (kernelCorrespondenceMatrix g q) p) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change kernelCorrespondenceFunction hJK e g he f.1
    (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))=_
  rw [kernelCorrespondenceFunction_lift]
  apply Finset.sum_congr rfl
  intro q _
  change f.1 (integralOrbitProjection globalKubotaKernel
      (kernelCorrespondenceMatrix g q•euclideanToHyperbolic p))=
    f.1 (integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (euclideanAction (kernelCorrespondenceMatrix g q) p)))
  rw [euclideanAction,euclideanToHyperbolic_coordinates]

lemma kernelCorrespondenceTest_energyDensity_le (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (kernelCorrespondenceTest hHK hJK e g he f) w≤
      (H.relIndex globalKubotaKernel:ℝ)*
        (kernelCorrespondenceFunction hJK e g he (fun q=>(kernelQuotientEnergyDensity f q:ℂ))
          (integralOrbitProjection globalKubotaKernel w)).re := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  let p := hyperbolicEuclideanCoordinates w
  let A := kernelCorrespondenceMatrix (H:=H) g
  have hFd (q : IntegralCoverCosets H globalKubotaKernel) :
      DifferentiableAt ℝ (kernelTestField f) (euclideanAction (A q) p) :=
    (kernelTestField_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
  have hcomp (q : IntegralCoverCosets H globalKubotaKernel) :
      DifferentiableAt ℝ (kernelTestField f ∘ euclideanAction (A q)) p := by
    obtain ⟨der,hder,_⟩ := hyperbolicDifferentialIsometry (A q) p (hyperbolicHeight_pos w)
    exact (hFd q).comp p hder.differentiableAt
  have hh := coverEnergyDensity_sum_le Finset.univ
    (fun q : IntegralCoverCosets H globalKubotaKernel=>kernelTestField f ∘ euclideanAction (A q))
    p (fun q _=>hcomp q)
  have hfield : kernelTestField (kernelCorrespondenceTest hHK hJK e g he f)=
      fun p=>∑q : IntegralCoverCosets H globalKubotaKernel,kernelTestField f (euclideanAction (A q) p) :=
    funext (kernelCorrespondenceTest_field hHK hJK e g he f)
  rw [kernelTestEnergyDensity_eq_cover,hfield]
  change coverEnergyDensity (fun p=>∑q : IntegralCoverCosets H globalKubotaKernel,
    kernelTestField f (euclideanAction (A q) p)) p≤_
  calc
    _ ≤ (Fintype.card (IntegralCoverCosets H globalKubotaKernel):ℝ)*
        ∑q : IntegralCoverCosets H globalKubotaKernel,
          coverEnergyDensity (kernelTestField f ∘ euclideanAction (A q)) p := by
      simpa only [Finset.card_univ,Function.comp_def] using hh
    _ = _ := by
      have hcard : Fintype.card (IntegralCoverCosets H globalKubotaKernel)=
          H.relIndex globalKubotaKernel := by
        rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
      rw [hcard,kernelCorrespondenceFunction_lift]
      simp only [Complex.re_sum,Complex.ofReal_re]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      rw [coverEnergyDensity_comp (A q) _ p (hyperbolicHeight_pos w) (hFd q)]
      change coverEnergyDensity (kernelTestField f) (euclideanAction (A q) p)=
        kernelTestEnergyDensity f (A q•w)
      rw [kernelTestEnergyDensity_eq_cover]
      congr 1
      dsimp [p,euclideanAction]
      rw [euclideanToHyperbolic_coordinates]

lemma kernelCorrespondenceTest_energy_le (f : kernelSmoothTests) :
    kernelDirichletEnergy (kernelCorrespondenceTest hHK hJK e g he f)≤
      (H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ)*kernelDirichletEnergy f := by
  let density : KernelQuotient→ℂ := fun q=>(kernelQuotientEnergyDensity f q:ℂ)
  have hdm : Measurable density := Complex.continuous_ofReal.measurable.comp
    (kernelQuotientEnergyDensity_continuous f).measurable
  have hdi : Integrable density (integralQuotientVolume globalKubotaKernel) :=
    (kernelQuotientEnergyDensity_integrable f).ofReal
  have hTi := kernelCorrespondenceFunction_integrable hHK hJK e g he density hdm hdi
  have hint := kernelCorrespondenceFunction_integral hHK hJK e g he density hdm hdi
  have hre : (∫q,(kernelCorrespondenceFunction hJK e g he density q).re
      ∂integralQuotientVolume globalKubotaKernel)=
        (J.relIndex globalKubotaKernel:ℝ)*kernelDirichletEnergy f := by
    have htr := integral_re hTi
    have hdf := integral_re hdi
    simp only [RCLike.re_to_complex] at htr hdf
    rw [htr,hint]
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    rw [←hdf]
    rfl
  unfold kernelDirichletEnergy
  calc
    _ ≤ ∫q,(H.relIndex globalKubotaKernel:ℝ)*
        (kernelCorrespondenceFunction hJK e g he density q).re
        ∂integralQuotientVolume globalKubotaKernel := by
      apply integral_mono (kernelQuotientEnergyDensity_integrable _) (hTi.re.const_mul _)
      intro q
      induction q using Quotient.inductionOn with
      | _ w => exact kernelCorrespondenceTest_energyDensity_le hHK hJK e g he f w
    _ = _ := by
      rw [integral_const_mul,hre]
      exact (mul_assoc _ _ _).symm

end

local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceTestLinear : kernelSmoothTests→ₗ[ℂ]kernelSmoothTests where
  toFun := kernelCorrespondenceTest hHK hJK e g he
  map_add' f h := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (f+h).1
        (integralOrbitProjection globalKubotaKernel w)=
          kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)+
          kernelCorrespondenceFunction hJK e g he h.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift,Submodule.coe_add,Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (c•f).1
        (integralOrbitProjection globalKubotaKernel w)=
          c • kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift,Submodule.coe_smul,Pi.smul_apply,Finset.smul_sum]

lemma kernelCorrespondenceL2_norm_le (F : KernelQuotientL2) :
    ‖kernelCorrespondenceL2 hHK hJK e g he F‖≤
      Real.sqrt ((H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ))*‖F‖ := by
  let C := integralConjugatePullback e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  let P := integralCoverPullback hJK globalKubotaKernel_le_levelThree
  let Tr := integralCoverTrace hHK globalKubotaKernel_le_levelThree
  have hTr := integralCoverTrace_opNorm_le hHK globalKubotaKernel_le_levelThree
  have hP := integralCoverPullback_norm_le hJK globalKubotaKernel_le_levelThree F
  rw [←Real.sqrt_eq_rpow] at hTr hP
  change ‖Tr (C (P F))‖≤_
  calc
    _ ≤ ‖Tr‖*‖C (P F)‖ := Tr.le_opNorm _
    _ ≤ Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*‖C (P F)‖ :=
      mul_le_mul_of_nonneg_right hTr (norm_nonneg _)
    _ = Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*‖P F‖ := by rw [C.norm_map]
    _ ≤ Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*
        (Real.sqrt (J.relIndex globalKubotaKernel:ℝ)*‖F‖) :=
      mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _)]; ring

lemma kernelCorrespondenceTest_graph_norm (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f)‖≤
      Real.sqrt ((H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ))*
        ‖kernelEnergyGraphCore f‖ := by
  have hm := kernelCorrespondenceL2_norm_le hHK hJK e g he (kernelSmoothTestsToL2 f)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hm
  rw [←kernelCorrespondenceTest_mass hHK hJK e g he,mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [kernelEnergyGraphCore_norm_sq,mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),kernelEnergyGraphCore_norm_sq]
  have he := kernelCorrespondenceTest_energy_le hHK hJK e g he f
  nlinarith

def kernelCorrespondenceEnergy : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  (kernelEnergyGraphCore.comp (kernelCorrespondenceTestLinear hHK hJK e g he)).extendOfNorm
    kernelEnergyGraphCore

lemma kernelCorrespondenceEnergy_core (f : kernelSmoothTests) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore f)=
      kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f) :=
  LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense
    ⟨_,kernelCorrespondenceTest_graph_norm hHK hJK e g he⟩ f

lemma kernelCorrespondenceEnergy_mass (u : KernelEnergyGraph) :
    kernelEnergyMass (kernelCorrespondenceEnergy hHK hJK e g he u)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelEnergyMass u) := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (kernelEnergyMass.continuous.comp (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    ((kernelCorrespondenceL2 hHK hJK e g he).continuous.comp kernelEnergyMass.continuous) ?_) u
  funext f
  change kernelEnergyMass (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore f))=
    kernelCorrespondenceL2 hHK hJK e g he (kernelEnergyMass (kernelEnergyGraphCore f))
  rw [kernelCorrespondenceEnergy_core,kernelEnergyMass_core,kernelEnergyMass_core,
    kernelCorrespondenceTest_mass]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspShiftNumerator (b : Bool) : Eis :=
  if b then -2-omega else omega-1

lemma ramifiedCuspShift_congr (b : Bool) :
    (3:Eis)∣ramifiedCuspShiftNumerator b-onceCuspScale (ramifiedCuspScaleUnit b) := by
  refine ⟨-1,?_⟩
  cases b
  · simp [ramifiedCuspShiftNumerator,ramifiedCuspScaleUnit,onceCuspScale,
      Units.val_neg,ramifiedOmegaUnit_val,ramifiedTraceLambda]
    linear_combination 2*ramified_omega_relation
  · simp only [ramifiedCuspShiftNumerator,ramifiedCuspScaleUnit,ite_true,onceCuspScale,
      Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,ramifiedTraceLambda]
    linear_combination -(2*omega-1)*ramified_omega_relation

lemma ramifiedCuspShift_support (b : Bool) (h : Eis) :
    (3:Eis)∣ramifiedCuspShiftNumerator b-h ↔
      (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b) := by
  constructor
  · intro hh
    convert dvd_sub (ramifiedCuspShift_congr b) hh using 1 ; ring
  · intro hh
    convert dvd_sub (ramifiedCuspShift_congr b) hh using 1 ; ring

lemma ramifiedSource_affine_shift (b : Bool) (x : Eis) (z : ℂ)
    (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)=
      affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv) := by
  rw [affinePeriodChar_mk]
  cases b
  · simp only [ramifiedCuspRoot,ramifiedCuspShiftNumerator]
    simp only [Bool.false_eq_true,↓reduceIte,ramifiedOmegaUnit_val]
    rw [ramifiedSourceFunction_upper_shift10]
    congr 2
    simp only [ramifiedShift10,map_mul,map_ofNat]
    ring
  · simp only [ramifiedCuspRoot,ite_true,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
      ramifiedCuspShiftNumerator]
    rw [ramifiedSourceFunction_upper_shift19]
    congr 2
    simp only [ramifiedShift19,map_mul,map_ofNat]
    ring

lemma ramifiedSource_weighted_shift (b : Bool) (h x : Eis) (z : ℂ)
    (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
    affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
      (ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by
  rw [ramifiedSource_affine_shift]
  have hphase : affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
    affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
    rw [affinePeriodChar_mk,affinePeriodChar_mk,←AddChar.map_add_eq_mul,←AddChar.map_add_eq_mul]
    congr 1
    simp only [ninthCuspFrequency,cuspFrequency,map_mul,map_sub,map_ofNat]
    ring
  calc
    _ = ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        (affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
          (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))) := by ring
    _ = _ := by rw [hphase];ring

theorem ramifiedSource_active_weighted_periodic (b : Bool) (h : Eis)
    (hh : (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    ∀x : Eis,∀z : ℂ,
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  intro x z
  rw [ramifiedSource_weighted_shift]
  have hc := (affinePeriodChar_eq_one (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)).mpr
    ((ramifiedCuspShift_support b h).mpr hh)
  rw [hc]
  simp

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedScaledMode (b : Bool) (h : Eis) (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (3*z) v hv)*
    ShortDraftTrace.breveE (-cuspFrequency h*z)

lemma ramifiedScaledMode_shift (b : Bool) (h x : Eis) (v : ℝ) (hv : 0<v) (z : ℂ) :
    ramifiedScaledMode b h v hv (z+eisEmbedding x)=
      affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*ramifiedScaledMode b h v hv z := by
  unfold ramifiedScaledMode
  rw [show 3*(z+eisEmbedding x)=3*z+3*eisEmbedding x by ring]
  have h1 : -cuspFrequency h*(z+eisEmbedding x)=
      -ninthCuspFrequency h*(3*z+3*eisEmbedding x) := by rw [ninthCuspFrequency];ring
  have h2 : -cuspFrequency h*z= -ninthCuspFrequency h*(3*z) := by rw [ninthCuspFrequency];ring
  rw [h1,h2]
  exact ramifiedSource_weighted_shift b h x (3*z) v hv

lemma ramifiedScaledMode_periodic (b : Bool) (h : Eis) (v : ℝ) (hv : 0<v) :
    ∀x : Eis,∀z : ℂ,ramifiedScaledMode b h v hv (z+3*eisEmbedding x)=
      ramifiedScaledMode b h v hv z := by
  intro x z
  have hx : Ideal.Quotient.mk (Ideal.span {(3:Eis)}) (3*x)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right 3 x))
  simpa only [map_mul,map_ofNat,hx,AddChar.map_zero_eq_one,one_mul] using
    ramifiedScaledMode_shift b h (3*x) v hv z

theorem ramifiedSource_scaled_fourier_off_support (b : Bool) (h : Eis)
    (hh : ¬(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint (3*z) v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=0 := by
  let χ := affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
  have hχ : χ≠1 := by
    intro he
    exact hh ((ramifiedCuspShift_support b h).mp
      ((affinePeriodChar_eq_one (3:Eis) (by norm_num) _).mp he))
  have hex : ∃x : Eis⧸Ideal.span {(3:Eis)},χ x≠1 := by
    by_contra he
    push Not at he
    apply hχ
    ext x
    simpa only [AddChar.one_apply] using he x
  obtain ⟨x,hx⟩ := hex
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  change (∫z in periodDomain,ramifiedScaledMode b h v hv z)=0
  apply periodic_integral_zero_of_eigen_translation _ (ramifiedScaledMode_periodic b h v hv)
    (eisEmbedding y) (χ (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) y)) hx
  intro z
  simpa only [add_comm] using ramifiedScaledMode_shift b h y v hv z

lemma ramifiedSource_height_continuous (b : Bool) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ=>ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)) := by
  let c : ℂ→UpperCoordinates := fun z=>⟨(z,v),hv⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const
  have ht := continuous_upperCoordinates.comp hc
  have ht' : Continuous (fun z : ℂ=>upperPoint z v hv) := by
    simpa only [Function.comp_def,c] using ht
  exact (ramifiedSourceFunction_continuous _).comp ht'

theorem ramifiedSource_scaled_fourier_active (b : Bool) (h : Eis)
    (hh : (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint (3*z) v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint z v hv)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have he (z : ℂ) : -ninthCuspFrequency h*(3*z)= -cuspFrequency h*z := by
    rw [ninthCuspFrequency]
    ring
  have hphase : Continuous (fun z : ℂ=>ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by
    change Continuous (fun z : ℂ=>Complex.exp (2*Real.pi*Complex.I*
      ((-ninthCuspFrequency h*z)+starRingEnd ℂ (-ninthCuspFrequency h*z))))
    fun_prop
  have hi := period_integral_eisenstein_mul
    (fun z=>ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))
    ((ramifiedSource_height_continuous b v hv).mul hphase).measurable
    (ramifiedSource_active_weighted_periodic b h hh v hv) (3:Eis) (by norm_num)
  simpa only [map_ofNat,he] using hi

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceAdjoint -/

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
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace

local notation "O" => ActualEisensteinCubic.O

lemma integralConjugatePullback_inverse_left {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : IntegralQuotientL2 H) :
    integralConjugatePullback e g he hH hJ
      (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F)=F := by
  apply Lp.ext
  have hi := integralConjugatePullback_ae e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F
  have hc := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp hi
  filter_upwards [integralConjugatePullback_ae e g he hH hJ
    (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F),hc]
    with q hq hqi
  dsimp only [Function.comp_def] at hqi
  rw [hq,hqi,integralConjugateMap_inverse]

lemma integralConjugatePullback_pairing {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : IntegralQuotientL2 H) (G : IntegralQuotientL2 J) :
    ⟪F,integralConjugatePullback e g he hH hJ G⟫_ℂ=
      ⟪integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F,G⟫_ℂ := by
  calc
    _ = ⟪integralConjugatePullback e g he hH hJ
      (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F),
      integralConjugatePullback e g he hH hJ G⟫_ℂ := by
        rw [integralConjugatePullback_inverse_left]
    _ = _ := LinearIsometry.inner_map_map _ _ _

theorem kernelCorrespondenceL2_pairing {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F G : KernelQuotientL2) :
    ⟪F,kernelCorrespondenceL2 hHK hJK e g he G⟫_ℂ=
      ⟪kernelCorrespondenceL2 hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) F,G⟫_ℂ := by
  change ⟪F,integralCoverTrace hHK globalKubotaKernel_le_levelThree
    (integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree G))⟫_ℂ=_
  rw [integralCoverTrace_pairing,integralConjugatePullback_pairing]
  exact (ContinuousLinearMap.adjoint_inner_left
    (integralCoverPullback hJK globalKubotaKernel_le_levelThree) G _).symm

theorem kernelCorrespondenceL2_adjoint {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    ContinuousLinearMap.adjoint (kernelCorrespondenceL2 hHK hJK e g he)=
      kernelCorrespondenceL2 hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) := by
  apply ContinuousLinearMap.ext
  intro F
  apply ext_inner_right ℂ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact kernelCorrespondenceL2_pairing hHK hJK e g he F G

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section

lemma continuous_period_integral {X:Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (f:X→ℂ→ℂ) (hf:Continuous f.uncurry) :
    Continuous (fun x=>∫z in periodDomain,f x z) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨U,hUc,hUn⟩:=exists_compact_mem_nhds x0
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(hUc.prod (isCompact_closedBall (0:ℂ) radius)).bddAbove_image hf.norm.continuousOn
  apply continuousAt_of_dominated
  · filter_upwards with x using (show Continuous (f x) from hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hUn] with x hx
    filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
    apply hC
    exact ⟨(x,z),⟨hx,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz⟩,rfl⟩
  · let:=periodDomain_finiteMeasure
    exact integrable_const C
  · filter_upwards with z using (show Continuous (fun x=>f x z) from hf.comp (continuous_id.prodMk continuous_const)).continuousAt

def continuousCuspSlice (f:HyperbolicSpace→ℂ) (freq:ℂ) (v:ℝ) :ℂ:=
  (∫z in periodDomain,f (cuspCoordinateLift (v,z))*ShortDraftTrace.breveE (-freq*z))/(v:ℂ)^3

lemma continuousCuspSlice_integrable (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (a b:ℝ) (ha:0<a) :
    IntegrableOn (continuousCuspSlice f freq) (Set.Icc a b) volume := by
  let g:HyperbolicSpace→ℂ:=fun w=>f w*arbitraryCuspWeightedPhase 1 freq w
  have hg:Continuous g:=hf.mul (arbitraryCuspWeightedPhase_continuous 1 freq)
  have hi:=cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hp:0<v:=ha.trans_le hv.1
  rw [integral_div,continuousCuspSlice]
  apply congrArg (fun c:ℂ=>c/(v:ℂ)^3)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only [g]
    rw [arbitraryCuspWeightedPhase,cuspCoordinateLift_positive v z hp,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    simp)

lemma continuousCuspSlice_continuousOn (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (a b:ℝ) (ha:0<a) :
    ContinuousOn (continuousCuspSlice f freq) (Set.Icc a b) := by
  let coord:(ℝ × ℂ)→UpperCoordinates:=fun q=>⟨(q.2,max a q.1),ha.trans_le (le_max_left _ _)⟩
  have hc:Continuous coord:=by
    apply Continuous.subtype_mk
    exact continuous_snd.prodMk (continuous_const.max continuous_fst)
  have hup:Continuous (fun q:(ℝ × ℂ)=>f (upperPoint q.2 (max a q.1) (ha.trans_le (le_max_left _ _)))):=
    hf.comp (continuous_upperCoordinates.comp hc)
  have he:Continuous (fun q:(ℝ × ℂ)=>ShortDraftTrace.breveE (-freq*q.2)):=by
    change Continuous (fun q:(ℝ × ℂ)=>Complex.exp (2*Real.pi*Complex.I*((-freq*q.2)+starRingEnd ℂ (-freq*q.2))))
    fun_prop
  have hi:=continuous_period_integral (fun v z=>f (upperPoint z (max a v) (ha.trans_le (le_max_left _ _)))*
      ShortDraftTrace.breveE (-freq*z)) (hup.mul he)
  have hnum:ContinuousOn (fun v:ℝ=>∫z in periodDomain,f (cuspCoordinateLift (v,z))*
      ShortDraftTrace.breveE (-freq*z)) (Set.Icc a b):=by
    apply hi.continuousOn.congr
    intro v hv
    have hp:0<v:=ha.trans_le hv.1
    simp only [max_eq_right hv.1,cuspCoordinateLift_positive v _ hp]
  exact hnum.div (Complex.continuous_ofReal.pow 3).continuousOn
    (fun v hv=>pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne'))

lemma continuousCuspSlice_test (f:HyperbolicSpace→ℂ) (hf:Continuous f) (freq:ℂ)
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    (∫w in cuspPeriodStrip a b,f w*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
      ∫v in Set.Icc a b,ρ v*continuousCuspSlice f freq v := by
  have hg:Continuous (fun w=>f w*arbitraryCuspWeightedPhase ρ freq w):=
    hf.mul (arbitraryCuspWeightedPhase_continuous ρ freq)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha _ hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha _ hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hp:0<v:=ha.trans_le hv.1
  dsimp only
  rw [continuousCuspSlice,←mul_div_assoc]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only
    rw [arbitraryCuspWeightedPhase,cuspCoordinateLift_positive v z hp,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    ring)

theorem continuousCuspSlice_eq_of_tests (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (g:ℝ→ℂ)
    (hg:∀a b:ℝ,0<a→ ContinuousOn g (Set.Icc a b))
    (ht:∀a b:ℝ,∀_ha:0<a,∀ρ:BoundedContinuousFunction ℝ ℂ,
      (∫w in cuspPeriodStrip a b,f w*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
        ∫v in Set.Icc a b,ρ v*g v) (v:ℝ) (hv:0<v) :
    continuousCuspSlice f freq v=g v := by
  have ha:0<v/2:=half_pos hv
  have hab:v/2≠2*v:=by linarith
  have he:continuousCuspSlice f freq=ᵐ[volume.restrict (Set.Icc (v/2) (2*v))]g:=by
    apply interval_ae_eq_of_boundedContinuous_height_tests (v/2) (2*v) _ _
      (continuousCuspSlice_integrable f hf freq _ _ ha) ((hg _ _ ha).integrableOn_Icc)
    intro ρ
    rw [←continuousCuspSlice_test f hf freq _ _ ha ρ]
    exact ht _ _ ha ρ
  exact Measure.eqOn_Icc_of_ae_eq volume hab he
    (continuousCuspSlice_continuousOn f hf freq _ _ ha) (hg _ _ ha)
      (by constructor <;>linarith)

local notation "Eis" => ActualEisensteinCubic.O

theorem ramifiedSource_fourier_all_heights (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ramifiedArithmeticResidue side h hf*(v:ℂ)^(2/3:ℂ)*
        sourceFourierKernel (4/3) (ninthCuspFrequency h*v) := by
  let R:=ramifiedArithmeticResidue side h hf
  let g:ℝ→ℂ:=fun v=>R*(v:ℂ)^(-(4/3:ℂ)-1)*
    sourceFourierKernel (4/3) (ninthCuspFrequency h*v)
  have hg:∀a b:ℝ,0<a→ ContinuousOn g (Set.Icc a b):=by
    intro a b ha x hx
    have hp:0<x:=ha.trans_le hx.1
    exact ((continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const x (-(4/3:ℂ)-1) (Or.inr hp.ne'))).mul
        ((sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp
          ((Complex.continuous_ofReal.const_mul (ninthCuspFrequency h)).continuousAt))).continuousWithinAt
  have ht:∀a b:ℝ,∀ha:0<a,∀ρ:BoundedContinuousFunction ℝ ℂ,
      (∫w in cuspPeriodStrip a b,ramifiedSourceFunction (ramifiedCuspRoot side:Eis) w*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
          ∫x in Set.Icc a b,ρ x*g x:=by
    intro a b ha ρ
    rw [ramifiedSource_height_residue_integral side h hf a b ha ρ,
      arbitraryIntervalWhittaker,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x=>by dsimp only [g,R];ring)
  have he:=continuousCuspSlice_eq_of_tests
    (ramifiedSourceFunction (ramifiedCuspRoot side:Eis)) (ramifiedSourceFunction_continuous _)
    (ninthCuspFrequency h) g hg ht v hv
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only [continuousCuspSlice,g,R] at he
  simp only [cuspCoordinateLift_positive v _ hv,hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  convert he using 1 ;ring

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma continuous_period_fourier_bound (f:ℂ→ℂ) (hf:Continuous f) :
    ∃C:ℝ,0≤C∧∀freq:ℂ,‖∫z in periodDomain,f z*ShortDraftTrace.breveE (-freq*z)‖≤C := by
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨B,hB⟩:=(isCompact_closedBall (0:ℂ) radius).bddAbove_image hf.norm.continuousOn
  refine ⟨max 0 B*(volume.restrict periodDomain).real Set.univ,mul_nonneg (le_max_left _ _) (measureReal_nonneg),?_⟩
  intro freq
  let:=periodDomain_finiteMeasure
  apply norm_integral_le_of_norm_le_const
  filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
  rw [norm_mul,breveE_norm,mul_one]
  apply le_trans _ (le_max_right _ _)
  apply hB
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz,rfl⟩

theorem continuous_fourier_bessel_subexponential (f:ℝ→ℂ→ℂ) (c:Eis→ℂ)
    (hf:∀v:ℝ,0<v→ Continuous (f v))
    (hfour:∀v:ℝ,∀_hv:0<v,∀h:Eis,h≠0→
      (∫z in periodDomain,f v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ((9*Real.sqrt 3/2:ℝ):ℂ)*c h*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))
    (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖c h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let v:ℝ:=ε/(9*Real.pi)
  have hv:0<v:=div_pos hε (by positivity)
  let area:ℂ:=((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea:0<‖area‖:=norm_pos_iff.mpr cusp_volume_ne_zero
  obtain ⟨B,hB,hbound⟩:=continuous_period_fourier_bound (f v) (hf v hv)
  let D:ℝ:=‖area‖*v*cubicBesselLowerConstant
  have hD:0<D:=mul_pos (mul_pos harea hv) cubicBesselLowerConstant_pos
  refine ⟨B/D,div_nonneg hB hD.le,?_⟩
  intro h hh
  have hx:0<4*Real.pi*‖cuspFrequency h‖*v:=by
    have hr:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    positivity
  have hl: cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))≤
      ‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖:=by
    have hb:=(schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx).trans (Complex.re_le_norm _)
    convert hb using 1
    congr 2
    dsimp [v]
    field_simp

  have hb:=hbound (cuspFrequency h)
  rw [hfour v hv h hh,norm_mul,norm_mul,norm_mul,Complex.norm_of_nonneg hv.le] at hb
  have hm:‖c h‖*(D*Real.exp (-(ε*‖cuspFrequency h‖)))≤B:=by
    calc
      _ = (‖area‖*‖c h‖*v)*(cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))) := by dsimp [D];ring
      _ ≤ (‖area‖*‖c h‖*v)*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖ :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ B := hb
  have hexp:0<Real.exp (-(ε*‖cuspFrequency h‖)):=Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD hexp)).mpr at hm
  calc
    _ ≤ B/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hm
    _ = (B/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg];field_simp

theorem continuous_periodic_eq_bessel (c:SubexponentialBesselCoefficients)
    (f:ℂ→ℂ) (hf:Continuous f) (v:ℝ) (hv:0<v)
    (hp:∀n:Eis,∀z:ℂ,f (z+3*ConcreteTraceCRT.eisEmbedding n)=f z)
    (hfour:∀h:Eis,(∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*c.amplitude v h) :
    ∀z:ℂ,f z=c.fullFunction 0 (upperPoint z v hv) := by
  have hc:=c.fullFunction_height_continuous 0 v hv
  have he:f=ᵐ[volume.restrict periodDomain](fun z=>c.fullFunction 0 (upperPoint z v hv)):=by
    apply periodDomain_L2_ext _ _ (periodDomain_memLp_of_continuous f hf)
      (periodDomain_memLp_of_continuous _ hc)
    intro h
    rw [hfour,c.fullFunction_fourier]
    by_cases hh:h=0
    · simp [hh,SubexponentialBesselCoefficients.amplitude]
    · simp [hh]
  have hall:=ae_eq_of_periodDomain_eq f _ hp (fun n z=>c.fullFunction_period 0 v hv z n) he
  exact congrFun (Measure.eq_of_ae_eq hall hf hc)

end

section
open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma ninthCuspFrequency_three (h:Eis) :
    3*ninthCuspFrequency h=cuspFrequency h := by
  unfold ninthCuspFrequency cuspFrequency
  ring

lemma sourceFourierKernel_cubic_amplitude (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    (v:ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  have he:=sourceFourierKernel_cubic_height h hh v hv
  rw [hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  calc
    _ = ((v:ℂ)^(2/3:ℂ)/(v:ℂ)^3)*sourceFourierKernel (4/3) (cuspFrequency h*v) := by ring
    _ = _ := he
    _ = _ := by field_simp

lemma ramified_kernel_scaled_bessel (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    ((3*v:ℝ):ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (ninthCuspFrequency h*(3*v:ℝ))=
      (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hfreq:ninthCuspFrequency h*((3*v:ℝ):ℂ)=cuspFrequency h*v:=by
    push_cast
    rw [←ninthCuspFrequency_three]
    ring
  have hp:((3*v:ℝ):ℂ)^(2/3:ℂ)=(3:ℂ)^(2/3:ℂ)*(v:ℂ)^(2/3:ℂ):=by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (a:=3) (b:=v) (by norm_num) hv.le (2/3:ℂ)
  rw [hfreq,hp,mul_assoc,sourceFourierKernel_cubic_amplitude h hh v hv]
  ring

end

section
open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedScaledRow (side:Bool) (v:ℝ) (z:ℂ) :ℂ:=
  ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (cuspCoordinateLift (3*v,3*z))

def ramifiedBesselValue (side:Bool) (h:Eis) :ℂ:=
  if hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side) then
    (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf/
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  else 0

lemma ramifiedScaledRow_continuous (side:Bool) (v:ℝ) (hv:0<v) :
    Continuous (ramifiedScaledRow side v) := by
  have hp:0<3*v:=by positivity
  have he:ramifiedScaledRow side v=(fun z=>ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (3*z) (3*v) hp)):=by
    funext z
    exact congrArg (ramifiedSourceFunction (ramifiedCuspRoot side:Eis)) (cuspCoordinateLift_positive (3*v) (3*z) hp)
  rw [he]
  exact (ramifiedSource_height_continuous side (3*v) hp).comp (continuous_const.mul continuous_id)

lemma ramifiedScaledRow_periodic (side:Bool) (v:ℝ) (hv:0<v) (n:Eis) (z:ℂ) :
    ramifiedScaledRow side v (z+3*eisEmbedding n)=ramifiedScaledRow side v z := by
  have hp:0<3*v:=by positivity
  have he:=ramifiedScaledMode_periodic side 0 (3*v) hp n z
  simpa only [ramifiedScaledMode,cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
    AddChar.map_zero_eq_one,mul_one,ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp] using he

lemma ramifiedScaledRow_zero (side:Bool) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,ramifiedScaledRow side v z)=0 := by
  have hp:0<3*v:=by positivity
  simp only [ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp]
  cases side
  · simpa [ramifiedCuspRoot,ramifiedOmegaUnit_val] using ramifiedSource_zero_mode10 (3*v) hp
  · simpa [ramifiedCuspRoot,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val] using ramifiedSource_zero_mode19 (3*v) hp

lemma ramifiedScaledRow_fourier (side:Bool) (v:ℝ) (hv:0<v) (h:Eis) :
    (∫z in periodDomain,ramifiedScaledRow side v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if h=0 then 0 else ramifiedBesselValue side h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)) := by
  by_cases hh:h=0
  · subst h
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,AddChar.map_zero_eq_one,
      mul_one]
    simpa only [ite_true,mul_zero] using ramifiedScaledRow_zero side v hv
  have hp:0<3*v:=by positivity
  rw [ite_eq_right hh]
  simp only [ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp]
  by_cases hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)
  · rw [ramifiedSource_scaled_fourier_active side h hf (3*v) hp,
      ramifiedSource_fourier_all_heights side h hf (3*v) hp,
      ramifiedBesselValue,dite_eq_left hf,mul_assoc,ramified_kernel_scaled_bessel h hh v hv]
    field_simp [cusp_volume_ne_zero]

  · rw [ramifiedSource_scaled_fourier_off_support side h hf (3*v) hp,
      ramifiedBesselValue,dite_eq_right hf]
    ring

lemma ramifiedBesselValue_subexponential (side:Bool) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖ramifiedBesselValue side h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  apply continuous_fourier_bessel_subexponential (ramifiedScaledRow side) (ramifiedBesselValue side)
    (ramifiedScaledRow_continuous side) _ ε hε
  intro v hv h hh
  simpa only [ite_eq_right hh,mul_assoc] using ramifiedScaledRow_fourier side v hv h

def ramifiedBesselCoefficients (side:Bool) :SubexponentialBesselCoefficients where
  value:=ramifiedBesselValue side
  growth:=ramifiedBesselValue_subexponential side

theorem ramifiedScaledRow_eq_bessel (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedScaledRow side v z=(ramifiedBesselCoefficients side).fullFunction 0 (upperPoint z v hv) := by
  apply continuous_periodic_eq_bessel (ramifiedBesselCoefficients side) (ramifiedScaledRow side v)
    (ramifiedScaledRow_continuous side v hv) v hv (ramifiedScaledRow_periodic side v hv) _ z
  intro h
  simpa only [SubexponentialBesselCoefficients.amplitude,ramifiedBesselCoefficients] using
    ramifiedScaledRow_fourier side v hv h

theorem ramifiedSource_cubic_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C∧∀v:ℝ,∀hv:0<v,∀z:ℂ,a≤v→
      ‖ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩:=(ramifiedBesselCoefficients side).fullFunction_zero_cubic_decay
    (a/3) (by positivity)
  refine ⟨27*C,by positivity,?_⟩
  intro v hv z hav
  have hp:0<v/3:=by positivity
  have he:=ramifiedScaledRow_eq_bessel side (v/3) hp (z/3)
  have hb:=hbound (v/3) hp (z/3) (by linarith)
  rw [←he] at hb
  have hv3:3*(v/3)=v:=by ring
  have hz3:(3:ℂ)*(z/3)=z:=by ring
  simp only [ramifiedScaledRow,hv3,hz3,cuspCoordinateLift_positive v z hv] at hb
  calc
    _ ≤ C/(v/3)^3 := hb
    _ = 27*C/v^3 := by field_simp;ring

end

local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspBesselTerm (side:Bool) (h:Eis) (v:ℝ) (z:ℂ) :ℂ:=
  (if h=0 then 0 else ramifiedBesselValue side h*((v/3:ℝ):ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/3)))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*z)

lemma ramifiedCuspBesselTerm_eq (side:Bool) (h:Eis) (v:ℝ) (hv:0<v) (z:ℂ) :
    (ramifiedBesselCoefficients side).term h (v/3,z/3)=ramifiedCuspBesselTerm side h v z := by
  rw [SubexponentialBesselCoefficients.term_eq_amplitude _ _ (by positivity)]
  have he:cuspFrequency h*(z/3)=ninthCuspFrequency h*z:=by
    rw [←ninthCuspFrequency_three]
    ring
  simp only [SubexponentialBesselCoefficients.amplitude,ramifiedBesselCoefficients,
    ramifiedCuspBesselTerm,he]

lemma ramifiedSource_eq_series (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      (ramifiedBesselCoefficients side).series (v/3,z/3) := by
  have he:=ramifiedScaledRow_eq_bessel side (v/3) (by positivity) (z/3)
  have hv3:3*(v/3)=v:=by ring
  have hz3:(3:ℂ)*(z/3)=z:=by ring
  simpa only [ramifiedScaledRow,hv3,hz3,cuspCoordinateLift_positive v z hv,
    SubexponentialBesselCoefficients.fullFunction,zero_mul,zero_add,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,
    hyperbolicHorizontal_upperPoint] using he

theorem ramifiedSource_bessel (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      ∑'h:Eis,ramifiedCuspBesselTerm side h v z := by
  rw [ramifiedSource_eq_series,SubexponentialBesselCoefficients.series]
  exact tsum_congr (fun h=>ramifiedCuspBesselTerm_eq side h v hv z)

theorem ramifiedSource_bessel_normal (side:Bool) (a b:ℝ) (ha:0<a) (hab:a≤b) :
    ∃g:Eis→ℝ,Summable g∧∀h:Eis,∀v:ℝ,v∈Set.Icc a b→∀z:ℂ,
      ‖ramifiedCuspBesselTerm side h v z‖≤g h := by
  obtain ⟨C,hC,hbound⟩:=(ramifiedBesselCoefficients side).slab_bound (a/3) (b/3)
    (by positivity) (by linarith)
  refine ⟨fun h=>C*Real.exp (-(Real.pi*(a/3))*‖cuspFrequency h‖),
    (summable_exp_neg_cuspFrequency_norm (Real.pi*(a/3)) (by positivity)).mul_left C,?_⟩
  intro h v hv z
  have hp:0<v:=ha.trans_le hv.1
  rw [←ramifiedCuspBesselTerm_eq side h v hp z]
  exact hbound h (v/3,z/3) ⟨by dsimp only;linarith [hv.1],by dsimp only;linarith [hv.2]⟩

theorem ramifiedSource_exponential_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C∧∀v:ℝ,∀hv:0<v,∀z:ℂ,a≤v→
      ‖ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)‖≤
        C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C,hC,hbound⟩:=(ramifiedBesselCoefficients side).series_cusp_decay (a/3) (by positivity)
  refine ⟨C,hC,?_⟩
  intro v hv z hav
  rw [ramifiedSource_eq_series]
  convert hbound (v/3) (z/3) (by linarith) using 1 ;ring_nf

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

lemma coverGradientAt_add (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverGradientAt (F+G) p=coverGradientAt F p+coverGradientAt G p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_add hF hG,WithLp.equiv_apply,WithLp.ofLp_add,
    Pi.add_apply,_root_.add_apply,mul_add]

lemma coverGradientAt_sub (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverGradientAt (F-G) p=coverGradientAt F p-coverGradientAt G p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_sub hF hG,WithLp.equiv_apply,WithLp.ofLp_sub,
    Pi.sub_apply,_root_.sub_apply,mul_sub]

lemma coverGradientAt_smul (c : ℂ) (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) :
    coverGradientAt (c•F) p=c•coverGradientAt F p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_const_smul hF,WithLp.equiv_apply,WithLp.ofLp_smul,
    Pi.smul_apply,_root_.smul_apply,smul_eq_mul,mul_left_comm]

def coverDirichletPair (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  inner ℂ (coverGradientAt F p) (coverGradientAt G p)

lemma coverDirichletPair_polarization (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverDirichletPair F G p=
      ((coverEnergyDensity (F+G) p:ℂ)-(coverEnergyDensity (F-G) p:ℂ)+
        ((coverEnergyDensity (F-Complex.I•G) p:ℂ)-
          (coverEnergyDensity (F+Complex.I•G) p:ℂ))*Complex.I)/4 := by
  unfold coverDirichletPair
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [RCLike.I_to_complex]
  rw [←coverGradientAt_add F G p hF hG,←coverGradientAt_sub F G p hF hG,
    ←coverGradientAt_smul Complex.I G p hG,
    ←coverGradientAt_sub F (Complex.I•G) p hF (hG.const_smul _),
    ←coverGradientAt_add F (Complex.I•G) p hF (hG.const_smul _)]
  simp only [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,
    coverGradientAt_norm_sq _ _ (hF.add hG),coverGradientAt_norm_sq _ _ (hF.sub hG),
    coverGradientAt_norm_sq _ _ (hF.sub (hG.const_smul _)),
    coverGradientAt_norm_sq _ _ (hF.add (hG.const_smul _))]

lemma coverDirichletPair_comp (g : SL(2,ℂ)) (F G : EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2)
    (hF : DifferentiableAt ℝ F (euclideanAction g p))
    (hG : DifferentiableAt ℝ G (euclideanAction g p)) :
    coverDirichletPair (F ∘ euclideanAction g) (G ∘ euclideanAction g) p=
      coverDirichletPair F G (euclideanAction g p) := by
  obtain ⟨der,hder,_⟩ := hyperbolicDifferentialIsometry g p hp
  rw [coverDirichletPair_polarization _ _ p (hF.comp p hder.differentiableAt)
    (hG.comp p hder.differentiableAt),coverDirichletPair_polarization F G _ hF hG]
  have ha : (F ∘ euclideanAction g)+(G ∘ euclideanAction g)=(F+G) ∘ euclideanAction g := rfl
  have hs : (F ∘ euclideanAction g)-(G ∘ euclideanAction g)=(F-G) ∘ euclideanAction g := rfl
  have hai : (F ∘ euclideanAction g)+Complex.I•(G ∘ euclideanAction g)=
      (F+Complex.I•G) ∘ euclideanAction g := rfl
  have hsi : (F ∘ euclideanAction g)-Complex.I•(G ∘ euclideanAction g)=
      (F-Complex.I•G) ∘ euclideanAction g := rfl
  rw [ha,hs,hai,hsi,coverEnergyDensity_comp g _ p hp (hF.add hG),
    coverEnergyDensity_comp g _ p hp (hF.sub hG),
    coverEnergyDensity_comp g _ p hp (hF.add (hG.const_smul _)),
    coverEnergyDensity_comp g _ p hp (hF.sub (hG.const_smul _))]

lemma coverDirichletPair_sum_right {ι : Type*} (s : Finset ι)
    (F : EuclideanSpatial→ℂ) (G : ι→EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hG : ∀i∈s,DifferentiableAt ℝ (G i) p) :
    coverDirichletPair F (fun x=>∑i∈s,G i x) p=∑i∈s,coverDirichletPair F (G i) p := by
  simp only [coverDirichletPair,coverGradientAt_sum s G p hG,inner_sum]

lemma coverDirichletPair_norm_le (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    ‖coverDirichletPair F G p‖≤(coverEnergyDensity F p+coverEnergyDensity G p)/2 := by
  have hh := norm_inner_le_norm (𝕜:=ℂ) (coverGradientAt F p) (coverGradientAt G p)
  have hs := sq_nonneg (‖coverGradientAt F p‖-‖coverGradientAt G p‖)
  rw [←coverGradientAt_norm_sq F p hF,←coverGradientAt_norm_sq G p hG]
  exact le_trans hh (by nlinarith)

lemma kernelDirichletPairDensity_eq_cover (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelDirichletPairDensity f h (integralOrbitProjection globalKubotaKernel w)=
      coverDirichletPair (kernelTestField f) (kernelTestField h) (hyperbolicEuclideanCoordinates w) := by
  rw [kernelDirichletPairDensity_coordinate]
  rfl

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceEnergy -/

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
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma kernelTestField_comp_contDiffAt (f : kernelSmoothTests) (g : SL(2,ℂ))
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f ∘ euclideanAction g) p := by
  have hd := ((((f.2.1.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff g))
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt
  simpa only [Function.comp_def,kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates] using hd

lemma coverGradientAt_lift_continuous (F : EuclideanSpatial→ℂ)
    (hF : ∀p,0<p 2→ ContDiffAt ℝ ∞ F p) :
    Continuous (fun w : HyperbolicSpace=>coverGradientAt F (hyperbolicEuclideanCoordinates w)) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3=>ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  apply (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
  rw [continuous_iff_continuousAt]
  intro w
  exact (((hF _ (hyperbolicHeight_pos w)).continuousAt_fderiv (by simp)).clm_apply
    continuousAt_const).comp hyperbolicEuclideanCoordinates_continuous.continuousAt

def kernelCorrespondencePairLift (g : SL(2,ℂ)) (f h : kernelSmoothTests)
    (w : HyperbolicSpace) : ℂ :=
  coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)

lemma kernelCorrespondencePairLift_continuous (g : SL(2,ℂ)) (f h : kernelSmoothTests) :
    Continuous (kernelCorrespondencePairLift g f h) :=
  (coverGradientAt_lift_continuous _ (kernelTestField_contDiffAt f)).inner
    (coverGradientAt_lift_continuous _ (kernelTestField_comp_contDiffAt h g))

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

include hHK hJK he in
omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePairLift_invariant (f h : kernelSmoothTests)
    (k : H) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (k•w)=kernelCorrespondencePairLift g f h w := by
  let A := integralComplexMatrix (k:SL(2,ActualEisensteinCubic.O))
  let B := integralComplexMatrix (e k:SL(2,ActualEisensteinCubic.O))
  have hfi : kernelTestField f ∘ euclideanAction A=kernelTestField f :=
    funext (kernelTestField_invariant f ⟨(k:SL(2,ActualEisensteinCubic.O)),hHK k.property⟩)
  have hhi : (kernelTestField h ∘ euclideanAction g) ∘ euclideanAction A=
      kernelTestField h ∘ euclideanAction g := by
    rw [Function.comp_assoc,←euclideanAction_mul,he k,euclideanAction_mul,←Function.comp_assoc]
    have hh : kernelTestField h ∘ euclideanAction B=kernelTestField h :=
      funext (kernelTestField_invariant h ⟨(e k:SL(2,ActualEisensteinCubic.O)),hJK (e k).property⟩)
    rw [hh]
  have hp := hyperbolicHeight_pos w
  have hh := coverDirichletPair_comp A (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_contDiffAt f _ (euclideanAction_positive A _)).differentiableAt (by simp))
    ((kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive A _)).differentiableAt (by simp))
  rw [hfi,hhi] at hh
  change _=coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)
  rw [integralSubgroup_smul]
  simpa only [kernelCorrespondencePairLift,A,euclideanAction,euclideanToHyperbolic_coordinates] using hh.symm

def kernelCorrespondencePair (f h : kernelSmoothTests) : IntegralOrbitQuotient H→ℂ :=
  Quotient.lift (kernelCorrespondencePairLift g f h) (by
    rintro w v ⟨k,rfl⟩
    exact (kernelCorrespondencePairLift_invariant hHK hJK e g he f h k w).symm)

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_projection (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelCorrespondencePair hHK hJK e g he f h (integralOrbitProjection H w)=
      kernelCorrespondencePairLift g f h w := rfl

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_measurable (f h : kernelSmoothTests) :
    Measurable (kernelCorrespondencePair hHK hJK e g he f h) :=
  measurable_from_quotient.mpr (kernelCorrespondencePairLift_continuous g f h).measurable

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_norm_le (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    ‖kernelCorrespondencePair hHK hJK e g he f h q‖≤
      (kernelQuotientEnergyDensity f (integralCoverMap hHK q)+
        kernelQuotientEnergyDensity h (integralCoverMap hJK (integralConjugateMap e g he q)))/2 := by
  induction q using Quotient.inductionOn with
  | _ w =>
    have hf := (kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt h g (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hb := coverDirichletPair_norm_le (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
      (hyperbolicEuclideanCoordinates w) hf hh
    rw [coverEnergyDensity_comp g _ _ (hyperbolicHeight_pos w)
      ((kernelTestField_contDiffAt h _ (euclideanAction_positive g _)).differentiableAt (by simp))] at hb
    change ‖kernelCorrespondencePairLift g f h w‖≤
      (kernelTestEnergyDensity f w+kernelTestEnergyDensity h (g•w))/2
    simpa only [kernelCorrespondencePairLift,kernelTestEnergyDensity_eq_cover,euclideanAction,
      euclideanToHyperbolic_coordinates] using hb

lemma kernelCorrespondencePair_integrable (f h : kernelSmoothTests) :
    Integrable (kernelCorrespondencePair hHK hJK e g he f h) (integralQuotientVolume H) := by
  have hf := (integralCoverMap_measurePreserving hHK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable f).smul_measure
      (c:=(H.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hh := (integralCoverMap_measurePreserving hJK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable h).smul_measure
      (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hhh := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hh
  apply ((hf.add hhh).div_const 2).mono' (kernelCorrespondencePair_measurable hHK hJK e g he f h).aestronglyMeasurable
  exact Filter.Eventually.of_forall (kernelCorrespondencePair_norm_le hHK hJK e g he f h)

end

local notation "O" => ActualEisensteinCubic.O

lemma kernelCorrespondencePairLift_kernel (g : SL(2,ℂ)) (f h : kernelSmoothTests)
    (r : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (r•w)=
      coverDirichletPair (kernelTestField f)
        (kernelTestField h ∘ euclideanAction (g*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))))
        (hyperbolicEuclideanCoordinates w) := by
  have hf := (kernelTestField_contDiffAt f _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hh := (kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hp := coverDirichletPair_comp (integralComplexMatrix r) (kernelTestField f)
    (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)
    (hyperbolicHeight_pos w) hf hh
  have hfi : kernelTestField f ∘ euclideanAction (integralComplexMatrix r)=kernelTestField f :=
    funext (kernelTestField_invariant f r)
  rw [hfi,Function.comp_assoc,←euclideanAction_mul] at hp
  simpa only [kernelCorrespondencePairLift,integralSubgroup_smul,euclideanAction,
    euclideanToHyperbolic_coordinates] using hp.symm

lemma kernelTestField_comp_inverse (f : kernelSmoothTests) (g : SL(2,ℂ)) :
    (kernelTestField f ∘ euclideanAction g⁻¹) ∘ euclideanAction g=kernelTestField f := by
  funext p
  simp only [Function.comp_def,kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates,
    inv_smul_smul]

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

lemma kernelCorrespondencePair_trace (f h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h) q=
      integralCoverTraceFunction H globalKubotaKernel
        (kernelCorrespondencePair hHK hJK e g he f h) q := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h)
      (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_eq_cover]
    have hfield := funext (kernelCorrespondenceTest_field hHK hJK e g he h)
    rw [hfield]
    have hd (r : IntegralCoverCosets H globalKubotaKernel) :
        DifferentiableAt ℝ (kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
          (hyperbolicEuclideanCoordinates w) :=
      (kernelTestField_comp_contDiffAt h _ _ (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hsum := coverDirichletPair_sum_right Finset.univ (kernelTestField f)
      (fun r=>kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
      (hyperbolicEuclideanCoordinates w) (fun r _=>hd r)
    simp only [Function.comp_apply] at hsum
    rw [hsum]
    change (∑r : IntegralCoverCosets H globalKubotaKernel,_)=
      ∑r : IntegralCoverCosets H globalKubotaKernel,
        kernelCorrespondencePair hHK hJK e g he f h (integralCoverFiberPoint H globalKubotaKernel r w)
    apply Finset.sum_congr rfl
    intro r _
    rw [integralCoverFiberPoint_rep,kernelCorrespondencePair_projection,
      kernelCorrespondencePairLift_kernel]
    rfl

lemma kernelCorrespondenceForm_integral (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h)=
      ∫q,kernelCorrespondencePair hHK hJK e g he f h q∂integralQuotientVolume H := by
  unfold kernelDirichletForm
  simp_rw [kernelCorrespondencePair_trace]
  exact integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
    (kernelCorrespondencePair_measurable hHK hJK e g he f h)
    (kernelCorrespondencePair_integrable hHK hJK e g he f h)

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_conjugate (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    kernelCorrespondencePair hHK hJK e g he f h q=
      star (kernelCorrespondencePair hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) h f (integralConjugateMap e g he q)) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelCorrespondencePairLift g f h w=
      star (kernelCorrespondencePairLift g⁻¹ h f (g•w))
    have hf := (kernelTestField_contDiffAt h _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt f g⁻¹ _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hc := coverDirichletPair_comp g (kernelTestField h) (kernelTestField f ∘ euclideanAction g⁻¹)
      (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) hf hh
    rw [kernelTestField_comp_inverse] at hc
    have hs := congrArg star hc
    have hswap : star (inner ℂ
        (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w))
        (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w)))=
        inner ℂ (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w))
          (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)) :=
      inner_conj_symm _ _
    rw [coverDirichletPair,hswap] at hs
    simpa only [kernelCorrespondencePairLift,coverDirichletPair,euclideanAction,
      euclideanToHyperbolic_coordinates] using hs

theorem kernelCorrespondenceForm_adjoint (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h)=
      kernelDirichletForm (kernelCorrespondenceTest hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) f) h := by
  let opposite := kernelCorrespondencePair hJK hHK e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he) h f
  have hom := kernelCorrespondencePair_measurable hJK hHK e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he) h f
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  rw [kernelCorrespondenceForm_integral]
  calc
    _ = ∫q,star (opposite (integralConjugateMap e g he q))∂integralQuotientVolume H := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (kernelCorrespondencePair_conjugate hHK hJK e g he f h)
    _ = ∫q,star (opposite q)∂integralQuotientVolume J := by
      have hh := integral_map («μ»:=integralQuotientVolume H) hm.measurable.aemeasurable
        (continuous_star.measurable.comp hom).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = star (∫q,opposite q∂integralQuotientVolume J) := by
      simp only [Complex.star_def]
      exact integral_conj
    _ = _ := by
      rw [←kernelCorrespondenceForm_integral hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he),kernelDirichletForm_conj]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

lemma kernelCorrespondenceEnergy_pairing_core (f h : kernelSmoothTests) :
    inner ℂ (kernelEnergyGraphCore f)
      (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore h))=
    inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he) (kernelEnergyGraphCore f)) (kernelEnergyGraphCore h) := by
  rw [kernelCorrespondenceEnergy_core,kernelCorrespondenceEnergy_core,
    kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  simp only [kernelEnergyMass_core,kernelEnergyGradient_core,kernelGradientToL2_inner]
  rw [kernelCorrespondenceTest_mass,kernelCorrespondenceTest_mass,
    kernelCorrespondenceL2_pairing,kernelCorrespondenceForm_adjoint]

theorem kernelCorrespondenceEnergy_pairing (u v : KernelEnergyGraph) :
    inner ℂ u (kernelCorrespondenceEnergy hHK hJK e g he v)=
      inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) u) v := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_id.inner continuous_const)
    ((kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he)).continuous.inner continuous_const) ?_) u
  funext f
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_const.inner (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    (continuous_const.inner continuous_id) ?_) v
  funext h
  exact kernelCorrespondenceEnergy_pairing_core hHK hJK e g he f h

lemma kernelCorrespondenceEnergy_pairing_left (u v : KernelEnergyGraph) :
    inner ℂ (kernelCorrespondenceEnergy hHK hJK e g he u) v=
      inner ℂ u (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) v) := by
  have hh := congrArg (starRingEnd ℂ)
    (kernelCorrespondenceEnergy_pairing hHK hJK e g he v u)
  simpa only [inner_conj_symm (𝕜 := ℂ) (E := KernelEnergyGraph)] using hh

lemma kernelCorrespondenceL2_pairing_left (F G : KernelQuotientL2) :
    inner ℂ (kernelCorrespondenceL2 hHK hJK e g he F) G=
      inner ℂ F (kernelCorrespondenceL2 hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) G) := by
  have hh := congrArg star (kernelCorrespondenceL2_pairing hHK hJK e g he G F)
  simpa only [←starRingEnd_apply,inner_conj_symm] using hh

theorem kernelCorrespondence_variationalSolution (F : KernelQuotientL2) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelVariationalSolution F)=
      kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F) := by
  apply kernelVariationalSolution_unique
  intro v
  rw [←kernelEnergyGraph_inner,kernelCorrespondenceEnergy_pairing_left,
    kernelEnergyGraph_inner,kernelVariationalSolution_equation,
    kernelCorrespondenceEnergy_mass]
  exact (kernelCorrespondenceL2_pairing_left hHK hJK e g he F (kernelEnergyMass v)).symm

theorem kernelCorrespondence_variationalResolvent (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelCorrespondenceL2 hHK hJK e g he F)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelVariationalResolvent F) := by
  change kernelEnergyMass (kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F))=_
  rw [←kernelCorrespondence_variationalSolution,kernelCorrespondenceEnergy_mass]
  rfl

theorem kernelCorrespondence_operatorGraph (F G : KernelQuotientL2)
    (hFG : (F,G)∈kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      kernelCorrespondenceL2 hHK hJK e g he G)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hFG ⊢
  rw [←map_add,kernelCorrespondence_variationalResolvent,hFG]

theorem kernelCorrespondence_eigenvector (F : KernelQuotientL2) (eigenvalue : ℂ)
    (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      eigenvalue • kernelCorrespondenceL2 hHK hJK e g he F)∈kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelCorrespondence_operatorGraph hHK hJK e g he F (eigenvalue • F) hF

end

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspFrequency_mul_right (h c:Eis) : cuspFrequency (h*c)=cuspFrequency h*eisEmbedding c := by
  unfold cuspFrequency
  rw [map_mul]
  ring

lemma cusp_character_continuous (h:Eis) :
    Continuous (fun z:ℂ=>ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
  change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*
    ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
  fun_prop

lemma cusp_character_fractional_period (c:Eis) (hc:c≠0) (h q:Eis) (z:ℂ) :
    ShortDraftTrace.breveE (-cuspFrequency (h*c)*(z+3*eisEmbedding q/eisEmbedding c))=
      ShortDraftTrace.breveE (-cuspFrequency (h*c)*z) := by
  rw [mul_add,AddChar.map_add_eq_mul]
  have he:-cuspFrequency (h*c)*(3*eisEmbedding q/eisEmbedding c)=
      -cuspFrequency h*(3*eisEmbedding q):=by
    rw [cuspFrequency_mul_right]
    field_simp [eisEmbedding_ne_zero hc]
  rw [he]
  have hz:ShortDraftTrace.breveE (-cuspFrequency h*(3*eisEmbedding q))=1:=by
    simpa only [zero_add,mul_zero,AddChar.map_zero_eq_one] using cuspFrequency_negative_period h q 0
  rw [hz,mul_one]

lemma period_fourier_fractional_translation (f:ℂ→ℂ)
    (hf:∀n:Eis,∀z:ℂ,f (z+3*eisEmbedding n)=f z)
    (c:Eis) (hc:c≠0) (h q:Eis) :
    (∫z in periodDomain,f (z+3*eisEmbedding q/eisEmbedding c)*
      ShortDraftTrace.breveE (-cuspFrequency (h*c)*z))=
    ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z) := by
  let g:ℂ→ℂ:=fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z)
  have hg (n:Eis) (z:ℂ):g (z+3*eisEmbedding n)=g z:=by
    dsimp [g]
    rw [hf,cuspFrequency_negative_period]
  have hi:=period_integral_translation g hg (3*eisEmbedding q/eisEmbedding c)
  have hp (z:ℂ):g (3*eisEmbedding q/eisEmbedding c+z)=
      f (z+3*eisEmbedding q/eisEmbedding c)*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z):=by
    dsimp [g]
    rw [add_comm (3*eisEmbedding q/eisEmbedding c) z,cusp_character_fractional_period c hc]
  simpa only [hp,g] using hi

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cube_upperPoint_continuous (v:ℝ) (hv:0<v) : Continuous (fun z:ℂ=>upperPoint z v hv) := by
  let c:ℂ→UpperCoordinates:=fun z=>⟨(z,v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const
  simpa only [Function.comp_def,c] using continuous_upperCoordinates.comp hc

theorem cubeAverage_fourier (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F)
    (hperiod:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (h:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp F (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ∫z in periodDomain,F (upperPoint z (v/‖eisEmbedding p‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)))*
        ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z) := by
  let V:=v/‖eisEmbedding p‖^3
  have hV:0<V:=div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)
  let f:ℂ→ℂ:=fun z=>F (upperPoint z V hV)
  let H:ℂ→ℂ:=fun z=>cubeAverage p hp F (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hf:Continuous f:=hF.comp (cube_upperPoint_continuous V hV)
  have hfperiod (n:Eis) (z:ℂ):f (z+3*eisEmbedding n)=f z:=by
    dsimp [f]
    rw [←complexTranslation_action]
    exact hperiod n _
  have hH:Continuous H:=
    ((cubeAverage_continuous p hp F hF).comp (cube_upperPoint_continuous v hv)).mul (cusp_character_continuous h)
  have hHperiod (n:Eis) (z:ℂ):H (z+3*eisEmbedding n)=H z:=by
    dsimp [H]
    rw [←complexTranslation_action,cubeAverage_period_three p hp F hperiod,cuspFrequency_negative_period]
  let term (r:Eis⧸Ideal.span {p^3}) (z:ℂ):=
    f (z+3*eisEmbedding (GaussianShiftedPartition.representative (p^3) r)/eisEmbedding (p^3))*
      ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)
  have hpoint (z:ℂ):H (eisEmbedding (p^3)*z)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*(∑' r:Eis⧸Ideal.span {p^3},term r z):=by
    have hphase:ShortDraftTrace.breveE (-cuspFrequency h*(eisEmbedding (p^3)*z))=
        ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z):=by
      rw [cuspFrequency_mul_right]
      congr 1
      ring
    dsimp only [H,cubeAverage]
    rw [hphase]
    rw [mul_assoc,←tsum_mul_right]
    congr 1
    apply tsum_congr
    intro r
    dsimp only [term,f]
    rw [cubeAverageMatrix_action]
    congr 2
    apply upperPoint_congr
    · rw [map_pow]
      field_simp [eisEmbedding_ne_zero hp]
    · rfl
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  have hi (r:Eis⧸Ideal.span {p^3}):IntegrableOn (term r) periodDomain:=by
    apply periodDomain_integrable_of_continuous
    exact (hf.comp (continuous_id.add continuous_const)).mul (cusp_character_continuous (h*p^3))
  have hint:(∫z in periodDomain,∑' r:Eis⧸Ideal.span {p^3},term r z)=
      ∑' r:Eis⧸Ideal.span {p^3},∫z in periodDomain,term r z:=by
    simp only [tsum_fintype]
    exact integral_finsetSum _ (fun r _=>hi r)
  have hterm (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,term r z)=∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z):=
    period_fourier_fractional_translation f hfperiod (p^3) (pow_ne_zero 3 hp) h _
  have hcard:(Nat.card (Eis⧸Ideal.span {p^3}):ℂ)=(Ideal.absNorm (Ideal.span {p}):ℂ)^3:=by
    change (Ideal.absNorm (Ideal.span {p^3}):ℂ)=_
    rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  change (∫z in periodDomain,H z)=∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)
  calc
    _=∫z in periodDomain,H (eisEmbedding (p^3)*z):=
      (period_integral_eisenstein_mul H hH.measurable hHperiod (p^3) (pow_ne_zero 3 hp)).symm
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
        (∑' r:Eis⧸Ideal.span {p^3},∫z in periodDomain,term r z):=by
      simp_rw [hpoint]
      rw [integral_const_mul,hint]
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
        (∑' (_:Eis⧸Ideal.span {p^3}),∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)):=by
      congr 1
      exact tsum_congr hterm
    _=_:=by rw [tsum_const,nsmul_eq_mul,hcard];field_simp

end

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem cubeSource_fourier (p:Eis) (hp:p≠0) (h:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude (v/‖eisEmbedding p‖^3) (h*p^3) := by
  rw [cubeAverage_fourier p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous
    cubicSource_period_three h v hv]
  simp_rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_fourier _ (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)) _

lemma cubeSource_amplitude_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (v:ℝ) (hv:0<v) :
    sourceResidualFullModeAmplitude (v/‖eisEmbedding p‖^3) (h*p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceResidualFullModeAmplitude v h := by
  have hc:((9*Real.sqrt 3/2:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (by positivity)
  apply mul_left_cancel₀ hc
  calc
    _=∫z in periodDomain,cubeAverage p hp cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z):=(cubeSource_fourier p hp h v hv).symm
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*
      (∫z in periodDomain,cubicSourceResidualFunction (upperPoint z v hv)*
        ShortDraftTrace.breveE (-cuspFrequency h*z)):=by
      simp_rw [hU,mul_assoc]
      exact integral_const_mul _ _
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*
      (((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h):=by
      simp_rw [cubicSourceResidualFunction_eq_bessel]
      rw [sourceBesselFunction_fourier]
    _=_:=by ring

lemma schlafliBesselK_cubic_ne_zero (x:ℝ) (hx:0<x) : schlafliBesselK (1/3:ℂ) x≠0 := by
  have hp:0<(schlafliBesselK (1/3:ℂ) x).re:=
    lt_of_lt_of_le (mul_pos cubicBesselLowerConstant_pos (Real.exp_pos _)) (schlafliBesselK_cubic_lower x hx)
  intro he
  rw [he,Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem sourceResidualFourierCoefficient_cube_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*p^3)=(‖eisEmbedding p‖:ℂ)*sourceResidualFourierCoefficient h := by
  have hhp:h*p^3≠0:=mul_ne_zero hh (pow_ne_zero 3 hp)
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hrC:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hf:‖cuspFrequency (h*p^3)‖=‖cuspFrequency h‖*‖eisEmbedding p‖^3:=by
    rw [cuspFrequency_mul_right,norm_mul,map_pow,norm_pow]
  have hx:0<4*Real.pi*‖cuspFrequency h‖:=by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))
  have hK:=schlafliBesselK_cubic_ne_zero _ hx
  have he:=cubeSource_amplitude_of_eigenrelation p hp hU h 1 (by norm_num)
  simp only [sourceResidualFullModeAmplitude,ite_eq_right hhp,ite_eq_right hh,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_pow,mul_one,hf] at he
  have harg:4*Real.pi*(‖cuspFrequency h‖*‖eisEmbedding p‖^3)*(1/‖eisEmbedding p‖^3)=
      4*Real.pi*‖cuspFrequency h‖:=by field_simp
  rw [harg] at he
  have he':sourceResidualFourierCoefficient (h*p^3)/(‖eisEmbedding p‖:ℂ)^3=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceResidualFourierCoefficient h:=by
    apply mul_right_cancel₀ hK
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using he
  have hn:(Ideal.absNorm (Ideal.span {p}):ℂ)=(‖eisEmbedding p‖:ℂ)^2:=by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span p).symm
  rw [hn] at he'
  have he'' :=(div_eq_iff (pow_ne_zero 3 hrC)).mp he'
  rw [he'']
  field_simp

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CubeEigenrelation -/

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

section

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma positive_cube_cpow_third (r:ℝ) (hr:0< r) :
    ((r^3:ℝ):ℂ)^(1/3:ℂ)=(r:ℂ) := by
  calc
    _=(((r^3)^(1/3:ℝ):ℝ):ℂ):=by
      simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
        (Complex.ofReal_cpow (pow_nonneg hr.le 3) (1/3)).symm
    _=_:=by
      congr 1
      rw [←Real.rpow_natCast_mul hr.le 3]
      norm_num

lemma cubicBesselNormalizer_mul_cube (h p:Eis) (hp:p≠0) :
    cubicBesselNormalizer (h*p^3)=(‖eisEmbedding p‖:ℂ)*cubicBesselNormalizer h := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hf:‖cuspFrequency (h*p^3)‖=‖cuspFrequency h‖*‖eisEmbedding p‖^3:=by
    rw [cuspFrequency_mul_right,norm_mul,map_pow,norm_pow]
  have ha:0≤2*Real.pi*‖cuspFrequency h‖:=by positivity
  have he:(2*Real.pi*‖cuspFrequency (h*p^3)‖:ℂ)=
      ((‖eisEmbedding p‖^3:ℝ):ℂ)*((2*Real.pi*‖cuspFrequency h‖:ℝ):ℂ):=by
    rw [hf]
    push_cast
    ring
  unfold cubicBesselNormalizer
  rw [he,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hr.le 3) ha,
    positive_cube_cpow_third _ hr]
  push_cast
  ring

lemma eisenstein_norm_eq_sqrt_norm (p:Eis) :
    ‖eisEmbedding p‖=Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]

theorem sourceResidualFourierCoefficient_cube_sqrt (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*p^3)=
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ):ℂ)*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient_cube_of_eigenrelation p hp hU h hh,
    eisenstein_norm_eq_sqrt_norm]

theorem sourceArithmeticResidue_cube_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) : sourceArithmeticResidue (h*p^3)=sourceArithmeticResidue h := by
  have ht:=sourceResidualFourierCoefficient_cube_of_eigenrelation p hp hU h hh
  unfold sourceResidualFourierCoefficient at ht
  rw [cubicBesselNormalizer_mul_cube h p hp] at ht
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  apply mul_left_cancel₀ (mul_ne_zero hr (cubicBesselNormalizer_ne_zero h hh))
  simpa only [mul_assoc] using ht

end

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

def cubeSourceDifference (p:Eis) (hp:p≠0) (w:HyperbolicSpace) : ℂ :=
  cubeAverage p hp cubicSourceResidualFunction w-
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w

lemma cubeSourceDifference_continuous (p:Eis) (hp:p≠0) :
    Continuous (cubeSourceDifference p hp) :=
  (cubeAverage_continuous p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous).sub
    (continuous_const.mul cubicSourceResidualFunction_continuous)

lemma cubeSourceDifference_period_three (p:Eis) (hp:p≠0) (n:Eis) (w:HyperbolicSpace) :
    cubeSourceDifference p hp (complexTranslation (3*eisEmbedding n) • w)=cubeSourceDifference p hp w := by
  unfold cubeSourceDifference
  rw [cubeAverage_period_three p hp cubicSourceResidualFunction cubicSource_period_three,
    cubicSource_period_three]

lemma cubeSourceDifference_period_one (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1) (w:HyperbolicSpace) :
    cubeSourceDifference p hp (complexTranslation 1 • w)=cubeSourceDifference p hp w := by
  unfold cubeSourceDifference
  rw [cubeAverage_period_one p hp hprimary cubicSourceResidualFunction cubicSource_period_three cubicSource_period_one,
    cubicSource_period_one]

lemma sourceCusp_period_nine (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (z+9*eisEmbedding n) v hv)=
      cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv) := by
  have h:=sourceCusp_scaled_periodic M v hv n (z/3)
  have h1:3*(z/3+3*eisEmbedding n)=z+9*eisEmbedding n:=by ring
  have h0:3*(z/3)=z:=by ring
  simpa only [h1,h0] using h

lemma cubeSource_summand_cusp_period {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv))=
    cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint z v hv)) := by
  let T:=cubeCuspTriangular d hp
  let V:=v/‖T 1 1‖^2
  have hV:0<V:=div_pos hv (cubeCuspTriangular_norm_sq_pos d hp)
  have he (x:ℂ):cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint x v hv))=
    cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*x+T 0 1)/T 1 1) V hV):=by
    rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul,
      complex_upper_triangular_action (cubeCuspTriangular d hp) (cubeCuspTriangular_entries d hp).2.1]
  have hx:(T 0 0*(z+9*eisEmbedding (p^3*n))+T 0 1)/T 1 1=
      (T 0 0*z+T 0 1)/T 1 1+9*eisEmbedding (p^(2*d.exponent.val)*n):=by
    calc
      _=(T 0 0*z+T 0 1)/T 1 1+9*((T 0 0/T 1 1)*eisEmbedding (p^3))*eisEmbedding n:=by
        rw [map_mul]
        ring
      _=_:=by rw [cubeCuspTriangular_integral_scale d hp,map_mul];ring
  calc
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*(z+9*eisEmbedding (p^3*n))+T 0 1)/T 1 1) V hV):=he _
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*z+T 0 1)/T 1 1+9*eisEmbedding (p^(2*d.exponent.val)*n)) V hV):=by rw [hx]
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*z+T 0 1)/T 1 1) V hV):=sourceCusp_period_nine d.matrix _ V hV _
    _=_:=(he z).symm

lemma cubeSourceDifference_cusp_period (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv)=
    cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv) := by
  have hU:cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv)=
    cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv):=by
    exact congrArg (fun t:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*t)
      (tsum_congr (fun r:Eis⧸Ideal.span {p^3}=>cubeSource_summand_cusp_period
        (actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary) hp.ne_zero z v hv n))
  exact congrArg₂ (fun a b:ℂ=>a-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*b)
    hU (sourceCusp_period_nine M z v hv (p^3*n))

lemma cubeSourceDifference_cusp_average_zero (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=0 :=
  cubeSource_difference_average_zero M p hp hprimary v hv

lemma cubeSourceDifference_decay (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤
      (K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹))/v^3 :=
  cubeSource_difference_decay_from_representatives p hp hprimary K hK hrep M z v hv hv1

end CubicEisenstein

open scoped Classical

namespace FiniteAutomorphismCover

variable {G : Type*} [Group G] {ι : Type*}

def common (K R : Subgroup G) (a : ι → G ≃* G) : Subgroup G :=
  K ⊓ ⨅i, R.comap (a i).toMonoidHom

lemma common_le (K R : Subgroup G) (a : ι → G ≃* G) : common K R a ≤ K :=
  inf_le_left

lemma common_le_preimage (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    common K R a ≤ R.comap (a i).toMonoidHom :=
  inf_le_right.trans (iInf_le _ i)

instance common_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] : (common K R a).FiniteIndex := by
  let : (⨅i, R.comap (a i).toMonoidHom).FiniteIndex :=
    Subgroup.finiteIndex_iInf (fun i => inferInstance)
  unfold common
  infer_instance

def toSource (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) : common K R a →* R where
  toFun h := ⟨a i (h : G), common_le_preimage K R a i h.property⟩
  map_one' := Subtype.ext (map_one (a i))
  map_mul' x y := Subtype.ext (map_mul (a i) (x : G) (y : G))

@[simp] lemma toSource_coe (K R : Subgroup G) (a : ι → G ≃* G) (i : ι)
    (h : common K R a) : (toSource K R a i h : G) = a i (h : G) := rfl

lemma toSource_injective (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    Function.Injective (toSource K R a i) := by
  intro x y hxy
  apply Subtype.ext
  exact (a i).injective (congrArg (fun r : R => (r : G)) hxy)

lemma toSource_range (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    (toSource K R a i).range =
      (common K R a).comap ((a i).symm.toMonoidHom.comp R.subtype) := by
  ext r
  constructor
  · rintro ⟨h,rfl⟩
    change (a i).symm (a i (h : G)) ∈ common K R a
    simpa only [MulEquiv.symm_apply_apply] using h.property
  · intro hr
    refine ⟨⟨(a i).symm (r : G),hr⟩,?_⟩
    apply Subtype.ext
    exact (a i).apply_symm_apply (r : G)

instance toSource_range_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] (i : ι) : (toSource K R a i).range.FiniteIndex := by
  rw [toSource_range]
  infer_instance

def hom (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a →* G :=
  lengthScale.subtype.comp (e.toMonoidHom.comp (toSource K R a i))

@[simp] lemma hom_apply (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    hom K R lengthScale a e i h = (e (toSource K R a i h) : G) := rfl

lemma hom_injective (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    Function.Injective (hom K R lengthScale a e i) :=
  lengthScale.subtype_injective.comp (e.injective.comp (toSource_injective K R a i))

def target (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) : Subgroup G :=
  (hom K R lengthScale a e i).range

lemma target_le (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i ≤ lengthScale := by
  rintro x ⟨h,rfl⟩
  exact (e (toSource K R a i h)).property

lemma target_le_common_ambient (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) (hLK : lengthScale ≤ K) (i : ι) : target K R lengthScale a e i ≤ K :=
  (target_le K R lengthScale a e i).trans hLK

lemma target_eq_map (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i = ((toSource K R a i).range.map e.toMonoidHom).map lengthScale.subtype := by
  rw [target,hom,MonoidHom.range_comp,MonoidHom.range_comp]

instance target_finiteIndex [Finite ι] (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) [K.FiniteIndex] [R.FiniteIndex] [lengthScale.FiniteIndex] (i : ι) :
    (target K R lengthScale a e i).FiniteIndex := by
  let : ((toSource K R a i).range.map e.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective _ e.surjective
  constructor
  rw [target_eq_map,Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

def equiv (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a ≃* target K R lengthScale a e i :=
  MonoidHom.ofInjective (hom_injective K R lengthScale a e i)

@[simp] lemma equiv_coe (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    (equiv K R lengthScale a e i h : G) = (e (toSource K R a i h) : G) := rfl

end FiniteAutomorphismCover

namespace CubicKubota
open scoped BigOperators Classical MatrixGroups

open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma literalCube_zero_pair (p : ActualEisensteinCubic.O) (hp : p≠0) (x : cubeKernelCorrespondence p) :
    cubeAverageMatrix p hp 0*integralComplexMatrix (cubeKernelRightGlobal p hp x)=
      integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0 := by
  let M := cubeKernelLeftGlobal p x
  let N := cubeKernelRightGlobal p hp x
  let z := cubeDilationRoot p
  have hz : z^2=eisEmbedding p^3 := cubeDilationRoot_sq p
  have hz0 : z≠0 := cubeDilationRoot_ne_zero p hp
  have he := cubeCorrespondence_entries p x.1
  change p^3*M 0 0=N 0 0*p^3 ∧ p^3*M 0 1=N 0 1 ∧
    M 1 0=N 1 0*p^3 ∧ M 1 1=N 1 1 at he
  have h00 : eisEmbedding (M 0 0)=eisEmbedding (N 0 0) :=
    congrArg eisEmbedding (mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _)))
  have h01 := congrArg eisEmbedding he.2.1
  have h10 := congrArg eisEmbedding he.2.2.1
  have h11 := congrArg eisEmbedding he.2.2.2
  simp only [map_mul,map_pow] at h01 h10
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      cubeAverageMatrix_entries,integralComplexMatrix_apply]
  · change z⁻¹*eisEmbedding (N 0 0)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 0)=
      eisEmbedding (M 0 0)*z⁻¹+eisEmbedding (M 0 1)*0
    rw [h00,map_zero]
    ring
  · change z⁻¹*eisEmbedding (N 0 1)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 1)=
      eisEmbedding (M 0 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 0 1)*z
    rw [←h01,←hz,map_zero]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 0)+z*eisEmbedding (N 1 0)=
      eisEmbedding (M 1 0)*z⁻¹+eisEmbedding (M 1 1)*0
    rw [h10,←hz]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 1)+z*eisEmbedding (N 1 1)=
      eisEmbedding (M 1 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 1 1)*z
    rw [h11,map_zero]
    ring

theorem literalCube_zero_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralCoverIntertwines (cubeKernelRangeEquiv p hp).symm (cubeAverageMatrix p hp 0) := by
  intro r
  let x := (MonoidHom.ofInjective (cubeKernelRightGlobal_injective p hp)).symm r
  have hr : cubeKernelRightGlobal p hp x=(r:SL(2,ActualEisensteinCubic.O)) :=
    MonoidHom.apply_ofInjective_symm (cubeKernelRightGlobal_injective p hp) r
  change cubeAverageMatrix p hp 0*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0
  rw [←hr]
  exact literalCube_zero_pair p hp x

lemma cubeTranslation_complex (q : ActualEisensteinCubic.O) :
    integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O))=complexTranslation (3*eisEmbedding q) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [integralComplexMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [upperTranslation, complexTranslation, map_ofNat]

lemma cubeAverageMatrix_factor_zero (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O) :
    cubeAverageMatrix p hp q=cubeAverageMatrix p hp 0*
      integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
  rw [cubeTranslation_complex]
  have h0 : complexTranslation 0=1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [complexTranslation]
  simp only [cubeAverageMatrix,map_zero,mul_zero,h0,mul_one]

theorem literalCube_summand_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O)
    (A : SL(2,ActualEisensteinCubic.O)) (r : (cubeKernelRightGlobal p hp).range)
    (hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*A=(r:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))) :
    cubeAverageMatrix p hp q*integralComplexMatrix A=
      integralComplexMatrix ((cubeKernelRangeEquiv p hp).symm r:SL(2,ActualEisensteinCubic.O))*cubeAverageMatrix p hp q := by
  have hAc := congrArg integralComplexMatrix hA
  simp only [map_mul] at hAc
  rw [cubeAverageMatrix_factor_zero,mul_assoc,hAc,←mul_assoc,
    literalCube_zero_intertwines p hp r,mul_assoc]

end CubicKubota

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverIntertwines_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h) :
    IntegralCoverIntertwines (e.trans f) (h*g) := by
  intro x
  change (h*g)*integralComplexMatrix (x:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (f (e x):SL(2,ActualEisensteinCubic.O))*(h*g)
  rw [mul_assoc,he x,←mul_assoc,hf (e x),mul_assoc]

lemma integralConjugateMap_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (q : IntegralOrbitQuotient H) :
    integralConjugateMap f h hf (integralConjugateMap e g he q)=
      integralConjugateMap (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection K (h•(g•w))=integralOrbitProjection K ((h*g)•w)
    rw [mul_smul]

lemma integralConjugatePullback_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (hK : K≤CubicKubota.levelThree) (F : IntegralQuotientL2 K) :
    integralConjugatePullback e g he hH hJ (integralConjugatePullback f h hf hJ hK F)=
      integralConjugatePullback (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) hH hK F := by
  apply Lp.ext
  have hinner := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp
    (integralConjugatePullback_ae f h hf hJ hK F)
  filter_upwards [integralConjugatePullback_ae e g he hH hJ (integralConjugatePullback f h hf hJ hK F),
    hinner,integralConjugatePullback_ae (e.trans f) (h*g)
      (integralCoverIntertwines_trans e f g h he hf) hH hK F] with q ho hi ht
  dsimp only [Function.comp_def] at hi
  rw [ho,hi,ht,integralConjugateMap_trans]

def kernelCoverLeg {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 H :=
  (integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree)

lemma kernelCoverLeg_representative {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F : KernelQuotientL2) (f : KernelQuotient→ℂ)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f) :
    kernelCoverLeg hHK hJK e g he F=ᵐ[integralQuotientVolume H]
      fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q)) := by
  have hc := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  exact (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hc)

lemma kernelCoverLeg_adjoint_apply {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F : IntegralQuotientL2 H) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) F=
      integralCoverTrace hJK globalKubotaKernel_le_levelThree
        (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
          (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) F) := by
  apply ext_inner_right ℂ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ F (integralConjugatePullback e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
    (integralCoverPullback hJK globalKubotaKernel_le_levelThree G))=_
  rw [integralConjugatePullback_pairing]
  exact (ContinuousLinearMap.adjoint_inner_left (integralCoverPullback hJK globalKubotaKernel_le_levelThree) G _).symm

theorem kernelCoverLeg_adjoint_comp {H Ji Jj : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hiK : Ji≤globalKubotaKernel) (hjK : Jj≤globalKubotaKernel)
    [Ji.IsFiniteRelIndex globalKubotaKernel] [Jj.IsFiniteRelIndex globalKubotaKernel]
    (ei : H≃*Ji) (ej : H≃*Jj) (gi gj : SL(2,ℂ))
    (hei : IntegralCoverIntertwines ei gi) (hej : IntegralCoverIntertwines ej gj) :
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)).comp
      (kernelCoverLeg hHK hiK ei gi hei)=
        kernelCorrespondenceL2 hjK hiK (ej.symm.trans ei) (gi*gj⁻¹)
          (integralCoverIntertwines_trans ej.symm ei gj⁻¹ gi
            (integralCoverIntertwines_inverse ej gj hej) hei) := by
  apply ContinuousLinearMap.ext
  intro F
  change ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)
    (kernelCoverLeg hHK hiK ei gi hei F)=_
  rw [kernelCoverLeg_adjoint_apply]
  change integralCoverTrace hjK globalKubotaKernel_le_levelThree
    (integralConjugatePullback ej.symm gj⁻¹ (integralCoverIntertwines_inverse ej gj hej)
      (hjK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)
      (integralConjugatePullback ei gi hei
        (hHK.trans globalKubotaKernel_le_levelThree) (hiK.trans globalKubotaKernel_le_levelThree)
        (integralCoverPullback hiK globalKubotaKernel_le_levelThree F)))=_
  rw [integralConjugatePullback_trans]
  rfl

end CubicEisenstein

open scoped Classical MatrixGroups BigOperators

namespace CubicKubota
open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

abbrev CubeResidues (p : ActualEisensteinCubic.O) := ActualEisensteinCubic.O ⧸ Ideal.span {p^3}

def cubeCommonAutomorphism (p : ActualEisensteinCubic.O) (r : CubeResidues p) : SL(2,ActualEisensteinCubic.O) ≃* SL(2,ActualEisensteinCubic.O) :=
  MulAut.conj (upperTranslation (GaussianShiftedPartition.representative (p^3) r):SL(2,ActualEisensteinCubic.O))

def cubeCommonCover (p : ActualEisensteinCubic.O) (hp : p≠0) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.common globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p)

lemma cubeCommonCover_le (p : ActualEisensteinCubic.O) (hp : p≠0) : cubeCommonCover p hp≤globalKubotaKernel :=
  FiniteAutomorphismCover.common_le _ _ _

lemma cubeCommonCover_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) : (cubeCommonCover p hp).FiniteIndex := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let := (cubeKernelGlobal_finite_covers p hp).2
  exact FiniteAutomorphismCover.common_finiteIndex _ _ _

def cubeCommonTarget (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.target globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r

lemma cubeCommonTarget_le (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonTarget p hp r≤globalKubotaKernel :=
  FiniteAutomorphismCover.target_le_common_ambient _ _ _ _ _ (cubeKernelLeftGlobal_le p) r

lemma cubeCommonTarget_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    (cubeCommonTarget p hp r).FiniteIndex := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let := (cubeKernelGlobal_finite_covers p hp).1
  let := (cubeKernelGlobal_finite_covers p hp).2
  exact FiniteAutomorphismCover.target_finiteIndex _ _ _ _ _ r

def cubeCommonEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonCover p hp≃*cubeCommonTarget p hp r :=
  FiniteAutomorphismCover.equiv globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r

lemma cubeCommon_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    IntegralCoverIntertwines (cubeCommonEquiv p hp r)
      (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)) := by
  intro h
  let q := GaussianShiftedPartition.representative (p^3) r
  let rh := FiniteAutomorphismCover.toSource globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p) r h
  have hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      (rh:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
    change (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      ((upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))⁻¹)*
        (upperTranslation q:SL(2,ActualEisensteinCubic.O))
    simp only [mul_assoc,inv_mul_cancel,mul_one]
  exact literalCube_summand_intertwines p hp q (h:SL(2,ActualEisensteinCubic.O)) rh hA

def cubeCommonLeg (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 (cubeCommonCover p hp) := by
  letI := cubeCommonTarget_finiteIndex p hp r
  letI : (cubeCommonTarget p hp r).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg (cubeCommonCover_le p hp) (cubeCommonTarget_le p hp r)
    (cubeCommonEquiv p hp r)
    (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r))
    (cubeCommon_intertwines p hp r)

end CubicKubota

end

end OAI

end

