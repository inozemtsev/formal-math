module

public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.ArbitraryCuspPullback
public import Green64.Library.OAI.NumberTheory.DirichletL.Reciprocity.CubeCorrespondence
public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.CuspDilation

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part015

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ConjugateCuspProfiles -/

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
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

theorem cuspBarProfile_conjugate_reflection (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) :
    cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0) v=
      reflectedCuspProfile (-star (CubicKubota.complexCharacter G)/(g 1 0)^2)
        (‖g 1 0‖^2)
        (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) (-g 1 1/g 1 0)) v := by
  have hdual : 0<(‖g 1 0‖^2*v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv,reflectedCuspProfile,cuspZProfile_positive _ _ _ hdual]
  have he := cubicSourceConjugateFunction_cuspDerivative G g H hfactor hc v hv
  have hpow : (v:ℂ)^(-2:ℂ)=((v:ℂ)^2)⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hpow]
  simp only [one_div] at he
  rw [he]
  ring

theorem conjugateSource_principal_cusp_mellin_entire (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0≠0) :
    (∀s : ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (complexMatrix G 0 0/complexMatrix G 1 0)) s) ∧
    Differentiable ℂ
      (mellin (cuspBarProfile cubicSourceConjugateFunction (complexMatrix G 0 0/complexMatrix G 1 0))) := by
  let g := complexMatrix G
  apply cusp_mellin_entire
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile cubicSourceConjugateFunction (-g 1 1/g 1 0))
    (-star (CubicKubota.complexCharacter G)/(g 1 0)^2) (‖g 1 0‖^2)
    residualCuspDecayRate residualCuspDecayRate
  · change 0<‖complexMatrix G 1 0‖^2
    positivity
  · exact residualCuspDecayRate_pos
  · exact residualCuspDecayRate_pos
  · exact cuspBarProfile_conjugate_continuousOn _
  · exact cuspZProfile_conjugate_continuousOn _
  · exact cuspBarProfile_conjugate_isBigO _
  · exact cuspZProfile_conjugate_isBigO _
  · intro v hv
    simpa only [one_smul] using cuspBarProfile_conjugate_reflection G g 1 (by simp [g]) hc v hv

theorem conjugateSource_cusp_mellin_reflection (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0) (s : ℂ) :
    mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) (2*s)=
      (-star (CubicKubota.complexCharacter G)/(g 1 0)^2)*(‖g 1 0‖^2:ℝ)^(2-2*s:ℂ)*
        mellin (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) (-g 1 1/g 1 0)) (2-2*s) := by
  apply cusp_mellin_reflection_of_identity _ _ _ _ _ (by positivity)
  intro v hv
  exact cuspBarProfile_conjugate_reflection G g H hfactor hc v hv

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselIntegralDeriv_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt (fun y : ℝ=>∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv y t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  apply continuousAt_of_dominated («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (bound:=fun t : ℝ=>(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)))
  · exact Eventually.of_forall (fun y=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
  · filter_upwards [Ioi_mem_nhds (show delta<x by dsimp [delta];linarith)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hyp : 0<y := hdelta.trans hy
    have htp : 0<t := ht
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  · exact cubicBesselDerivativeMajorant_integrable.const_mul (4/delta)
  · exact Eventually.of_forall (fun t=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)

lemma schlafliBesselK_cubic_derivative_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt schlafliBesselK_cubic_derivative x := by
  have hp4 : ContinuousAt (fun y : ℝ=>(y/2)^(-(4:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hp1 : ContinuousAt (fun y : ℝ=>(y/2)^(-(1:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hI := (cubicBesselIntegral_hasDerivAt x hx).continuousAt
  have hD := cubicBesselIntegralDeriv_continuousAt x hx
  apply Complex.continuous_ofReal.continuousAt.comp
  exact ((continuousAt_const.mul hp4).mul hI).add ((continuousAt_const.mul hp1).mul hD)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma amplitudeDeriv_continuousAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    ContinuousAt (fun y : ℝ=>coeff.amplitudeDeriv y h) v := by
  by_cases hh : h=0
  · simpa only [amplitudeDeriv,ite_eq_left hh] using (continuousAt_const (y:=(0:ℂ)) (x:=v))
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hK : ContinuousAt (fun y : ℝ=>schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_hasDerivAt _ (by positivity)).continuousAt.comp (by fun_prop)
  have hD : ContinuousAt (fun y : ℝ=>schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_derivative_continuousAt _ (by positivity)).comp (by fun_prop)
  simp only [amplitudeDeriv,ite_eq_right hh]
  exact continuousAt_const.mul (hK.add ((Complex.continuous_ofReal.continuousAt.mul continuousAt_const).mul hD))

lemma termFDeriv_continuousAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContinuousAt (coeff.termFDeriv h) p := by
  by_cases hh : h=0
  · have he : coeff.termFDeriv h=fun _=>(0:(ℝ × ℂ)→L[ℝ]ℂ) := by
      funext q
      simp only [termFDeriv,ite_eq_left hh]
    rw [he]
    exact continuousAt_const
  have hA := (coeff.amplitudeDeriv_continuousAt p.1 hp h).comp continuousAt_fst
  have hphase : ContinuousAt (fun q : ℝ × ℂ=>ShortDraftTrace.breveE (cuspFrequency h*q.2)) p := by
    change ContinuousAt (fun q : ℝ × ℂ=>Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2)))) p
    fun_prop
  have hfirst := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
    (ContinuousLinearMap.fst ℝ ℝ ℂ)).continuous.continuousAt.comp (hA.mul hphase)
  have hterm := (coeff.term_continuousOn h).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
  have hsecond := hterm.smul (continuousAt_const
    (y:=(horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)))
  have he : coeff.termFDeriv h=(fun q : ℝ × ℂ=>
      (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
        (coeff.amplitudeDeriv q.1 h*ShortDraftTrace.breveE (cuspFrequency h*q.2))+
      coeff.term h q • (horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)) := by
    funext q
    simp only [termFDeriv,ite_eq_right hh]
  rw [he]
  exact hfirst.add hsecond

lemma seriesFDeriv_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun p : ℝ × ℂ=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p)
      {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*((1+‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h p hp
    exact (coeff.termFDeriv_continuousAt h p (ha.trans_le hp.1)).continuousWithinAt
  · exact (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma series_contDiffAt_one (p : ℝ × ℂ) (hp : 0<p.1) : ContDiffAt ℝ 1 coeff.series p := by
  apply contDiffAt_one_iff.mpr
  refine ⟨(fun q=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h q),
    {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)},?_,?_,?_⟩
  · exact continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  · exact coeff.seriesFDeriv_continuousOn_slab _ _ (by linarith) (by linarith)
  · intro q hq
    exact coeff.series_hasFDerivAt q (by change p.1/2≤q.1 ∧ q.1≤2*p.1 at hq;linarith [hq.1])

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

def cuspSpatialInput (q : ℝ × ℂ) : SpatialCoordinates := ![q.2.re,q.2.im,q.1]
def cuspSpatialOutput (p : SpatialCoordinates) : ℝ × ℂ := (p 2,spatialHorizontal p)

lemma cuspSpatialInput_contDiff : ContDiff ℝ 1 cuspSpatialInput := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.re)
    exact Complex.reCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.im)
    exact Complex.imCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.1)
    fun_prop

lemma cuspSpatialOutput_contDiff : ContDiff ℝ 1 cuspSpatialOutput :=
  (contDiff_apply ℝ ℝ 2).prodMk (spatialHorizontal_contDiff.of_le (by simp))

lemma cuspSpatialInput_horizontal (q : ℝ × ℂ) : spatialHorizontal (cuspSpatialInput q)=q.2 :=
  Complex.re_add_im q.2

lemma cuspSpatialAction_lift (g : SL(2,ℂ)) (q : ℝ × ℂ) (hq : 0<q.1) :
    cuspCoordinateLift (cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput q)))=
      g•cuspCoordinateLift q := by
  have hin : hyperbolicSpatialCoordinates (cuspCoordinateLift q)=cuspSpatialInput q := by
    rw [show q=(q.1,q.2) from rfl,cuspCoordinateLift_positive q.1 q.2 hq]
    simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,cuspSpatialInput]
  have he := mobiusSpatial_coordinates_global g (cuspCoordinateLift q)
  rw [hin] at he
  have hr := hyperbolicSpatialCoordinates_reconstruct (g•cuspCoordinateLift q)
  have hp : 0< mobiusSpatial g (cuspSpatialInput q) 2 := mobiusSpatial_positive g _ hq
  rw [cuspSpatialOutput,cuspCoordinateLift_positive _ _ hp]
  refine Eq.trans ?_ hr
  apply upperPoint_congr
  · rw [he]
    rfl
  · rw [he]

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_cusp_contDiffAt_one (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hreal : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>q.1^(2/3:ℝ)) p :=
    contDiff_fst.contDiffAt.rpow_const_of_ne hp.ne'
  have hcast := Complex.ofRealCLM.contDiff.contDiffAt.comp p hreal
  have hpow : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>(q.1:ℂ)^(2/3:ℂ)) p := by
    apply hcast.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    have he := Complex.ofReal_cpow (le_of_lt hq) (2/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
    exact he.symm
  have hfull : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p :=
    (contDiffAt_const.mul hpow).add (coeff.series_contDiffAt_one p hp)
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

lemma fullFunction_translate_cusp_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (g•cuspCoordinateLift q)) p := by
  have hmid : ContDiffAt ℝ 1 (fun q=>mobiusSpatial g (cuspSpatialInput q)) p :=
    ((mobiusSpatial_contDiffAt g (cuspSpatialInput p) hp).of_le (by simp)).comp p
      cuspSpatialInput_contDiff.contDiffAt
  have hact := cuspSpatialOutput_contDiff.contDiffAt.comp p hmid
  have hpos : 0<(cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput p))).1 :=
    mobiusSpatial_positive g _ hp
  have hfull := (coeff.fullFunction_cusp_contDiffAt_one constant _ hpos).comp p hact
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact congrArg (coeff.fullFunction constant) (cuspSpatialAction_lift g q hq).symm

lemma fullFunction_translate_split_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>coeff.fullFunction constant (g•cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>(q.2,q.1)) p := by fun_prop
  exact (coeff.fullFunction_translate_cusp_contDiffAt_one constant g (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceResidualFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_contDiffAt_one _ g p hp

lemma cubicSourceConjugateFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceConjugateFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  exact Complex.conjCLE.contDiff.contDiffAt.comp p
    (cubicSourceResidualFunction_translate_split_contDiffAt_one g p hp)

lemma horizontalWirtingerBar_eq_fderiv (F : ℂ × ℝ→ℂ) (A : (ℂ × ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerBar (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)+Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar,h1,hI]

lemma cuspBarProfile_continuousOn_of_contDiff (f : HyperbolicSpace→ℂ)
    (hreg : ∀p : ℂ × ℝ,0<p.2 → ContDiffAt ℝ 1
      (fun q : ℂ × ℝ=>f (cuspCoordinateLift (q.2,q.1))) p) (z : ℂ) :
    ContinuousOn (cuspBarProfile f z) (Set.Ioi 0) := by
  let F : ℂ × ℝ→ℂ := fun q=>f (cuspCoordinateLift (q.2,q.1))
  intro v hv
  have hd : ContinuousAt (fderiv ℝ F) (z,v) :=
    (hreg (z,v) hv).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (fun y : ℝ=>(z,y)) v := continuousAt_const.prodMk continuousAt_id
  have h1 := (hd.comp hc).clm_apply (continuousAt_const (y:=((1,0):ℂ × ℝ)))
  have hI := (hd.comp hc).clm_apply (continuousAt_const (y:=((Complex.I,0):ℂ × ℝ)))
  have hformula : ContinuousAt (fun y : ℝ=>(1/2:ℂ)*
      ((fderiv ℝ F (z,y)) (1,0)+Complex.I*(fderiv ℝ F (z,y)) (Complex.I,0))) v :=
    continuousAt_const.mul (h1.add (continuousAt_const.mul hI))
  apply ContinuousAt.continuousWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show 0<v from hv)] with y hy
  exact horizontalWirtingerBar_eq_fderiv F (fderiv ℝ F (z,y)) z y
    ((hreg (z,y) hy).differentiableAt (by norm_num)).hasFDerivAt

lemma cuspZProfile_continuousOn_of_contDiff (f : HyperbolicSpace→ℂ)
    (hreg : ∀p : ℂ × ℝ,0<p.2 → ContDiffAt ℝ 1
      (fun q : ℂ × ℝ=>f (cuspCoordinateLift (q.2,q.1))) p) (z : ℂ) :
    ContinuousOn (cuspZProfile f z) (Set.Ioi 0) := by
  let F : ℂ × ℝ→ℂ := fun q=>f (cuspCoordinateLift (q.2,q.1))
  intro v hv
  have hd : ContinuousAt (fderiv ℝ F) (z,v) :=
    (hreg (z,v) hv).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (fun y : ℝ=>(z,y)) v := continuousAt_const.prodMk continuousAt_id
  have h1 := (hd.comp hc).clm_apply (continuousAt_const (y:=((1,0):ℂ × ℝ)))
  have hI := (hd.comp hc).clm_apply (continuousAt_const (y:=((Complex.I,0):ℂ × ℝ)))
  have hformula : ContinuousAt (fun y : ℝ=>(1/2:ℂ)*
      ((fderiv ℝ F (z,y)) (1,0)-Complex.I*(fderiv ℝ F (z,y)) (Complex.I,0))) v :=
    continuousAt_const.mul (h1.sub (continuousAt_const.mul hI))
  apply ContinuousAt.continuousWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show 0<v from hv)] with y hy
  exact horizontalWirtingerZ_eq_fderiv F (fderiv ℝ F (z,y)) z y
    ((hreg (z,y) hy).differentiableAt (by norm_num)).hasFDerivAt

lemma cuspBarProfile_source_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspBarProfile (fun w=>cubicSourceResidualFunction (H•w)) z) (Set.Ioi 0) :=
  cuspBarProfile_continuousOn_of_contDiff _
    (cubicSourceResidualFunction_translate_split_contDiffAt_one H) z

lemma cuspZProfile_source_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w=>cubicSourceResidualFunction (H•w)) z) (Set.Ioi 0) :=
  cuspZProfile_continuousOn_of_contDiff _
    (cubicSourceResidualFunction_translate_split_contDiffAt_one H) z

lemma cuspBarProfile_conjugate_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspBarProfile (fun w=>cubicSourceConjugateFunction (H•w)) z) (Set.Ioi 0) :=
  cuspBarProfile_continuousOn_of_contDiff _
    (cubicSourceConjugateFunction_translate_split_contDiffAt_one H) z

lemma cuspZProfile_conjugate_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) z) (Set.Ioi 0) :=
  cuspZProfile_continuousOn_of_contDiff _
    (cubicSourceConjugateFunction_translate_split_contDiffAt_one H) z

end

section
open Filter MeasureTheory
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ninth_trace_character_period (c x : Eis) :
    ShortDraftTrace.breveE ((eisEmbedding c/(9*eisLam))*(9*eisEmbedding x))=1 := by
  have he : (eisEmbedding c/(9*eisLam))*(9*eisEmbedding x)=eisEmbedding (c*x)/eisLam := by
    rw [map_mul]
    ring
  rw [he,breveE_embedding_div_traceLambda]

lemma ramifiedSource_scaled_periodic10 (v : ℝ) (hv : 0<v) (x : Eis) (z : ℂ) :
    ramifiedSourceFunction omega (upperPoint (3*(z+3*eisEmbedding x)) v hv)=
      ramifiedSourceFunction omega (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding x)=3*z+3*eisEmbedding (3*x) := by
    rw [map_mul,map_ofNat]
    ring
  rw [he,ramifiedSourceFunction_upper_shift10,show eisEmbedding (3*x)=3*eisEmbedding x by rw [map_mul,map_ofNat]]
  have hp : ShortDraftTrace.breveE (ramifiedShift10*(3*(3*eisEmbedding x)))=1 := by
    simpa only [ramifiedShift10,show (3:ℂ)*(3*eisEmbedding x)=9*eisEmbedding x by ring] using
      ninth_trace_character_period (omega-1) x
  rw [hp,one_mul]

lemma ramifiedSource_scaled_periodic19 (v : ℝ) (hv : 0<v) (x : Eis) (z : ℂ) :
    ramifiedSourceFunction (omega^2) (upperPoint (3*(z+3*eisEmbedding x)) v hv)=
      ramifiedSourceFunction (omega^2) (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding x)=3*z+3*eisEmbedding (3*x) := by
    rw [map_mul,map_ofNat]
    ring
  rw [he,ramifiedSourceFunction_upper_shift19,show eisEmbedding (3*x)=3*eisEmbedding x by rw [map_mul,map_ofNat]]
  have hp : ShortDraftTrace.breveE (ramifiedShift19*(3*(3*eisEmbedding x)))=1 := by
    simpa only [ramifiedShift19,show (3:ℂ)*(3*eisEmbedding x)=9*eisEmbedding x by ring] using
      ninth_trace_character_period (-2-omega) x
  rw [hp,one_mul]

lemma periodic_integral_zero_of_eigen_translation (f : ℂ→ℂ)
    (hf : ∀x:Eis,∀z,f (z+3*eisEmbedding x)=f z) (b c : ℂ)
    (hc : c≠1) (he : ∀z,f (b+z)=c*f z) :
    (∫z in periodDomain,f z)=0 := by
  have hi := period_integral_translation f hf b
  simp_rw [he] at hi
  rw [integral_const_mul] at hi
  have hzero : (c-1)*(∫z in periodDomain,f z)=0 := by linear_combination hi
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)

theorem ramifiedSource_zero_mode10 (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction omega (upperPoint (3*z) v hv))=0 := by
  apply periodic_integral_zero_of_eigen_translation _
    (ramifiedSource_scaled_periodic10 v hv) 1 (eisEmbedding omega)
  · exact fun h => omega_primitive.ne_one (by decide) (eisEmbedding_injective (by simpa using h))
  · intro z
    have he : 3*(1+z)=3*z+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 0) := by
      norm_num [ActualEisensteinCoordinates.eval]
      ring
    rw [he,ramifiedSourceFunction_upper_shift10,ramifiedShift10_period]
    norm_num [cubicExp]

theorem ramifiedSource_zero_mode19 (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (omega^2) (upperPoint (3*z) v hv))=0 := by
  apply periodic_integral_zero_of_eigen_translation _
    (ramifiedSource_scaled_periodic19 v hv) 1 (eisEmbedding (omega^2))
  · intro h
    have he : omega^2=(1:Eis) := eisEmbedding_injective (by simpa using h)
    have hpoly := ramified_omega_relation
    rw [he] at hpoly
    have hw : omega=(-2:Eis) := by linear_combination hpoly
    rw [hw] at he
    norm_num at he
  · intro z
    have he : 3*(1+z)=3*z+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 0) := by
      norm_num [ActualEisensteinCoordinates.eval]
      ring
    rw [he,ramifiedSourceFunction_upper_shift19,ramifiedShift19_period]
    norm_num [cubicExp]

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

abbrev UnitLowerData := Σa:PrimaryLower,{d:PrimaryLower//IsCoprime a.val d.val}

def unitLowerToPrimitive (u : Eisˣ) (p : UnitLowerData) : PrimitiveRow := by
  refine ⟨![(u:Eis)*(p.1.val-p.2.val.val),p.2.val.val],?_,?_,p.2.val.2⟩
  · change IsCoprime ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd p.2.val.val (p.1.val-p.2.val.val) p.1.val
      ⟨-1,by ring⟩).mpr
    exact p.2.2.symm
  · have hd : (3:Eis)∣p.1.val-p.2.val.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub p.1.2 p.2.val.2
    exact hd.mul_left (u:Eis)

lemma unitLowerToPrimitive_bijective (u : Eisˣ) :
    Function.Bijective (unitLowerToPrimitive u) := by
  constructor
  · rintro ⟨a,d,hd⟩ ⟨b,e,he⟩ h
    have hrow := congrArg Subtype.val h
    have hde : d=e := Subtype.ext (congrFun hrow 1)
    subst e
    have hab : a=b := by
      apply Subtype.ext
      have hh := congrFun hrow 0
      change (u:Eis)*(a.val-d.val)=(u:Eis)*(b.val-d.val) at hh
      have hcancel := u.isUnit.mul_left_cancel hh
      linear_combination hcancel
    subst b
    rfl
  · intro r
    let d : PrimaryLower := ⟨r.val 1,r.2.2.2⟩
    let a : PrimaryLower := ⟨(↑u⁻¹:Eis)*r.val 0+r.val 1,by
      have hc := r.2.2.1.mul_left (↑u⁻¹:Eis)
      have hh := dvd_add hc r.2.2.2
      convert hh using 1 ;ring⟩
    have hcop : IsCoprime a.val d.val := by
      apply IsCoprime.symm
      apply (isCoprime_right_congr_of_dvd d.val a.val ((↑u⁻¹:Eis)*r.val 0)
        ⟨1,by dsimp [a,d];ring⟩).mpr
      exact (isCoprime_mul_unit_left_right u⁻¹.isUnit _ _).mpr r.2.1.symm
    refine ⟨⟨a,d,hcop⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change (u:Eis)*((↑u⁻¹:Eis)*r.val 0+r.val 1-r.val 1)=r.val 0
      rw [add_sub_cancel_right,←mul_assoc]
      simp
    · rfl

def unitLowerEquiv (u : Eisˣ) : UnitLowerData≃PrimitiveRow :=
  Equiv.ofBijective _ (unitLowerToPrimitive_bijective u)

lemma rowOperator_lowerCusp (t : Eis) (v : Fin 2→ℂ) :
    rowOperator (integralComplexMatrix (lowerCuspMatrix t)) v=
      ![v 0+eisEmbedding t*v 1,v 1] := by
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,integralComplexMatrix_apply]
  fin_cases i <;>
    simp [lowerCuspMatrix,mul_comm]

lemma unitLower_row_phase (u : Eisˣ) (p : UnitLowerData) :
    (cosetCharacter (primitiveRowEquiv.symm (unitLowerEquiv u p)))⁻¹=
      eisEmbedding (symbol (u:Eis) p.2.val.val)*
        eisEmbedding (symbol p.2.val.val p.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val)=_
  have hh : symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val=
      symbol ((u:Eis)*p.1.val) p.2.val.val := by
    exact symbol_congr ⟨-(u:Eis),by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.val),
    symbol_reciprocity p.1.val p.2.val.val (primaryLower_ne_zero p.1)
      (primaryLower_ne_zero p.2.val) (primaryLower_primary p.1)
        (primaryLower_primary p.2.val),map_mul]

def unitLowerTerm (u : Eisˣ) (z : ℂ) (v : ℝ) (s : ℂ) (a d : Eis) : ℂ :=
  (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s

lemma unitLower_summand (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (p : UnitLowerData) :
    summand (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s
      (primitiveRowEquiv.symm (unitLowerEquiv u p))=
      unitLowerTerm u z v s p.1.val p.2.val.val := by
  let r : Fin 2→ℂ := ![eisEmbedding ((u:Eis)*p.1.val),eisEmbedding p.2.val.val]
  have hr : rowOperator (integralComplexMatrix (lowerCuspMatrix (u:Eis)))
      (embeddedRow (primitiveRowEquiv.symm (unitLowerEquiv u p)))=r := by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [unitLowerEquiv, Equiv.ofBijective_apply, unitLowerToPrimitive, r, map_mul, map_sub, mul_sub]
  have hr0 : r≠0 := by
    intro hh
    have he := congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.val) he
  have hp := heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,unitLower_row_phase]
  change _=(eisEmbedding (symbol (u:Eis) p.2.val.val)*eisEmbedding (symbol p.2.val.val p.1.val))*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi : ((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹ := by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

theorem unitLowerEisenstein_eq_rows (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v) (s : ℂ) :
    eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s=
      ∑'p:UnitLowerData,unitLowerTerm u z v s p.1.val p.2.val.val := by
  rw [eisenstein,←primitiveRowEquiv.symm.tsum_eq,←(unitLowerEquiv u).tsum_eq]
  exact tsum_congr (unitLower_summand u z v hv s)

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Cusp.ResiduesModThree -/

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

open scoped Classical MatrixGroups

namespace EisensteinCuspModThree

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCoordinates (eval coords eval_coords unique_coordinates eval_mul)

abbrev Pair := ZMod 3 × ZMod 3
def add (x y : Pair) : Pair := (x.1+y.1,x.2+y.2)
def neg (x : Pair) : Pair := (-x.1,-x.2)
def sub (x y : Pair) : Pair := add x (neg y)
def mul (x y : Pair) : Pair := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def scalar (a : ZMod 3) (x : Pair) : Pair := (a*x.1,a*x.2)
def residue (x : ActualEisensteinCubic.O) : Pair := ((coords x).1,(coords x).2)

lemma residue_eval (a b : ℤ) : residue (eval a b)=((a:ZMod 3),(b:ZMod 3)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n:ZMod 3)) h.1)
    (congrArg (fun n : ℤ => (n:ZMod 3)) h.2)

lemma residue_intCast (a : ℤ) : residue (a:ActualEisensteinCubic.O)=((a:ZMod 3),0) := by
  simpa [eval] using residue_eval a 0

lemma residue_zero : residue (0:ActualEisensteinCubic.O)=(0,0) := by simpa using residue_intCast 0
lemma residue_one : residue (1:ActualEisensteinCubic.O)=(1,0) := by simpa using residue_intCast 1

lemma residue_add (x y : ActualEisensteinCubic.O) : residue (x+y)=add (residue x) (residue y) := by
  have he : x+y=eval ((coords x).1+(coords y).1) ((coords x).2+(coords y).2) := by
    nth_rw 1 [←eval_coords x,←eval_coords y]
    simp only [eval,Int.cast_add]
    ring
  rw [he,residue_eval]
  simp [residue,add]

lemma residue_neg (x : ActualEisensteinCubic.O) : residue (-x)=neg (residue x) := by
  have he : -x=eval (-(coords x).1) (-(coords x).2) := by
    nth_rw 1 [←eval_coords x]
    simp only [eval,Int.cast_neg]
    ring
  rw [he,residue_eval]
  simp only [residue, neg, Int.cast_neg]
  rfl

lemma residue_sub (x y : ActualEisensteinCubic.O) : residue (x-y)=sub (residue x) (residue y) := by
  rw [sub_eq_add_neg,residue_add,residue_neg]
  rfl

lemma residue_mul (x y : ActualEisensteinCubic.O) : residue (x*y)=mul (residue x) (residue y) := by
  calc
    residue (x*y)=residue (eval (coords x).1 (coords x).2*eval (coords y).1 (coords y).2) := by
      rw [eval_coords,eval_coords]
    _ = _ := by rw [eval_mul,residue_eval]; simp [residue,mul]

lemma residue_eq_implies_three_dvd {x y : ActualEisensteinCubic.O} (h : residue x=residue y) : (3:ActualEisensteinCubic.O)∣x-y := by
  have h1 : (3:ℤ)∣(coords x).1-(coords y).1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).1 (coords x).1 3).mp
      (congrArg Prod.fst h).symm
  have h2 : (3:ℤ)∣(coords x).2-(coords y).2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).2 (coords x).2 3).mp
      (congrArg Prod.snd h).symm
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  refine ⟨eval a b,?_⟩
  nth_rw 1 [←eval_coords x,←eval_coords y]
  have he1 : (coords x).1=(coords y).1+3*a := by omega
  have he2 : (coords x).2=(coords y).2+3*b := by omega
  simp only [eval,he1,he2]
  push_cast
  ring

lemma residue_mul_intCast (a : ℤ) (x : ActualEisensteinCubic.O) : residue ((a:ActualEisensteinCubic.O)*x)=scalar (a:ZMod 3) (residue x) := by
  rw [residue_mul,residue_intCast]
  simp [mul,scalar]

def primitive (a c : Pair) : Prop := ¬(a.1+a.2=0 ∧ c.1+c.2=0)
instance primitive_decidable (a c : Pair) : Decidable (primitive a c) := inferInstanceAs
  (Decidable (¬(a.1+a.2=0 ∧ c.1+c.2=0)))

lemma primitive_of_determinant : ∀a b c d : Pair,sub (mul a d) (mul b c)=(1,0) → primitive a c := by
  decide +kernel

lemma first_column_primitive (M : SL(2,ActualEisensteinCubic.O)) : primitive (residue (M 0 0)) (residue (M 1 0)) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by simpa only [Matrix.det_fin_two] using M.property
  have hh := congrArg residue hd
  rw [residue_sub,residue_mul,residue_mul,residue_one] at hh
  exact primitive_of_determinant _ _ _ _ hh

def omegaPower (k : Fin 3) : Pair := if k=0 then (1,0) else if k=1 then (0,1) else (-1,-1)
def unitPair (u : Fin 2 × Fin 3) : Pair := scalar ((-1:ZMod 3)^u.1.val) (omegaPower u.2)
def cuspPair (j : Fin 3) : Pair := if j=0 then (0,0) else if j=1 then (0,1) else (-1,-1)

def columnTop (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 0 0,0) (scalar (g 0 1) (cuspPair j))) (unitPair u)
def columnBottom (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 1 0,0) (scalar (g 1 1) (cuspPair j))) (unitPair u)

theorem primitive_column_three_cusps : ∀a c : Pair, primitive a c →
    ∃g : SL(2,ZMod 3), ∃j : Fin 3, ∃u : Fin 2 × Fin 3,
      columnTop g j u=a ∧ columnBottom g j u=c := by
  decide +kernel

end

open scoped Classical MatrixGroups Matrix

local notation "O" => ActualEisensteinCubic.O
local notation "ζ" => ActualEisensteinCubic.omega
open CubicKubota CubicEisenstein

def unitRepresentative (u : Fin 2 × Fin 3) : ActualEisensteinCubic.Oˣ :=
  (-1:ActualEisensteinCubic.Oˣ)^u.1.val*CubicRamified.omega_isUnit.unit^u.2.val

lemma unitRepresentative_value (u : Fin 2 × Fin 3) :
    (unitRepresentative u:ActualEisensteinCubic.O)=(-1:ActualEisensteinCubic.O)^u.1.val*ζ^u.2.val := by
  simp [unitRepresentative]

lemma residue_omega : residue ζ=(0,1) := by
  have he : ActualEisensteinCoordinates.eval 0 1=ζ := by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [←he]
  exact residue_eval 0 1

lemma residue_omega_sq : residue (ζ^2)=(-1,-1) := by
  rw [pow_two,residue_mul,residue_omega]
  norm_num [mul]
  rfl

lemma unitRepresentative_residue (u : Fin 2 × Fin 3) :
    residue (unitRepresentative u:ActualEisensteinCubic.O)=unitPair u := by
  rw [unitRepresentative_value]
  rcases u with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [unitPair,omegaPower,scalar,residue_one,residue_neg,residue_omega,residue_omega_sq,neg] <;>
    decide +kernel

def cuspParameter (j : Fin 3) : ActualEisensteinCubic.O := if j=0 then 0 else if j=1 then ζ else ζ^2
def cuspRepresentative (j : Fin 3) : SL(2,ActualEisensteinCubic.O) := lowerCuspMatrix (cuspParameter j)

lemma cuspParameter_residue (j : Fin 3) : residue (cuspParameter j)=cuspPair j := by
  fin_cases j <;> simp [cuspParameter,cuspPair,residue_zero,residue_omega,residue_omega_sq]

def unitDiagonal (u : ActualEisensteinCubic.Oˣ) : SL(2,ActualEisensteinCubic.O) :=
  ⟨!![(u:ActualEisensteinCubic.O),0;0,(↑u⁻¹:ActualEisensteinCubic.O)],by simp [Matrix.det_fin_two]⟩

def columnRepresentative (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) : SL(2,ActualEisensteinCubic.O) :=
  rationalEmbedding r*cuspRepresentative j*unitDiagonal (unitRepresentative u)

lemma columnRepresentative_entry (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) (i : Fin 2) :
    columnRepresentative r j u i 0=
      ((r i 0:ActualEisensteinCubic.O)+(r i 1:ActualEisensteinCubic.O)*cuspParameter j)*(unitRepresentative u:ActualEisensteinCubic.O) := by
  change (((r : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom O) *
    !![1, 0; cuspParameter j, 1]) *
    !![(unitRepresentative u : O), 0; 0, (↑(unitRepresentative u)⁻¹ : O)]) i 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma columnRepresentative_top_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 0 0)=columnTop (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma columnRepresentative_bottom_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 1 0)=columnBottom (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma same_column_quotient_lower_zero (M N : SL(2,ActualEisensteinCubic.O))
    (h0 : N 0 0=M 0 0) (h1 : N 1 0=M 1 0) : (N⁻¹*M) 1 0=0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,]
  rw [h0,h1]
  ring

theorem three_cusp_decomposition (M : SL(2,ActualEisensteinCubic.O)) :
    ∃G : levelTwo, ∃j : Fin 3, ∃T : SL(2,ActualEisensteinCubic.O),
      T 1 0=0 ∧ IsUnit (T 0 0) ∧ IsUnit (T 1 1) ∧
        M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T := by
  obtain ⟨g,j,u,ht,hb⟩ := primitive_column_three_cusps _ _ (first_column_primitive M)
  obtain ⟨r,hr⟩ := rationalReductionThree_surjective g
  let B := columnRepresentative r j u
  have hB0 : residue (B 0 0)=residue (M 0 0) := by
    dsimp only [B]
    rw [columnRepresentative_top_residue,hr]
    exact ht
  have hB1 : residue (B 1 0)=residue (M 1 0) := by
    dsimp only [B]
    rw [columnRepresentative_bottom_residue,hr]
    exact hb
  have hxy : IsCoprime (M 0 0) (M 1 0) := by
    refine ⟨M 1 1,-M 0 1,?_⟩
    have hd := M.property
    rw [Matrix.det_fin_two] at hd
    linear_combination hd
  obtain ⟨N,hN0,hN1,hNB⟩ := exists_congruent_cusp_completion B (M 0 0) (M 1 0) hxy
    (residue_eq_implies_three_dvd hB0.symm) (residue_eq_implies_three_dvd hB1.symm)
  let G : levelTwo := ⟨(N*B⁻¹)*rationalEmbedding r,⟨⟨N*B⁻¹,hNB⟩,r,rfl⟩⟩
  let T : SL(2,ActualEisensteinCubic.O) := unitDiagonal (unitRepresentative u)*(N⁻¹*M)
  have hT : T 1 0=0 := by
    have hz := same_column_quotient_lower_zero M N hN0 hN1
    change (∑k : Fin 2,(unitDiagonal (unitRepresentative u)) 1 k*(N⁻¹*M) k 0)=0
    rw [Fin.sum_univ_two]
    change 0*(N⁻¹*M) 0 0+(↑(unitRepresentative u)⁻¹:ActualEisensteinCubic.O)*(N⁻¹*M) 1 0=0
    rw [hz]
    ring
  have hdet : T 0 0*T 1 1=1 := by
    have hd := T.property
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd
  refine ⟨G,j,T,hT,?_,?_,?_⟩
  · exact IsUnit.of_mul_eq_one _ hdet
  · exact IsUnit.of_mul_eq_one _ (show T 1 1*T 0 0=1 by simpa only [mul_comm] using hdet)
  · dsimp [G,T,B,columnRepresentative]
    group

end EisensteinCuspModThree

namespace CubicEisenstein
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
abbrev PrimaryCoprimeDenominator (a : PrimaryLower) := {d:PrimaryLower//IsCoprime a.val d.val}

def primaryDenominatorFromCoprime (a : PrimaryLower) (x : CoprimeElement a.val) :
    PrimaryCoprimeDenominator a := by
  refine ⟨⟨a.val+3*x.val,?_⟩,?_⟩
  · convert dvd_add a.2 (dvd_mul_right (3:Eis) x.val) using 1 ;ring
  · apply (isCoprime_right_congr_of_dvd a.val (a.val+3*x.val) (3*x.val) ⟨1,by ring⟩).mpr
    exact (primary_coprime_three a.val (primaryLower_primary a)).mul_right x.2

lemma primaryDenominatorFromCoprime_bijective (a : PrimaryLower) :
    Function.Bijective (primaryDenominatorFromCoprime a) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg (fun d : PrimaryCoprimeDenominator a => d.val.val) h
    change a.val+3*x.val=a.val+3*y.val at he
    exact mul_left_cancel₀ (by norm_num : (3:Eis)≠0) (add_left_cancel he)
  · intro d
    have hdiv : (3:Eis)∣d.val.val-a.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub d.val.2 a.2
    obtain ⟨x,hx⟩ := hdiv
    have hd : d.val.val=a.val+3*x := by linear_combination hx
    have hcop : IsCoprime a.val x := by
      have hc : IsCoprime a.val (3*x) :=
        (isCoprime_right_congr_of_dvd a.val d.val.val (3*x) ⟨1,by rw [hd];ring⟩).mp d.2
      exact hc.of_isCoprime_of_dvd_right (dvd_mul_left x 3)
    refine ⟨⟨x,hcop⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact hd.symm

def primaryDenominatorEquiv (a : PrimaryLower) : CoprimeElement a.val≃PrimaryCoprimeDenominator a :=
  Equiv.ofBijective _ (primaryDenominatorFromCoprime_bijective a)

def unitLowerIntegral (u : Eisˣ) (v : ℝ) (s freq : ℂ) (a d : Eis) : ℂ :=
  ∫z in periodDomain,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z)

lemma hasSum_unitLowerIntegrals (u : Eisˣ) (v : ℝ) (hv : 0<v) (s freq : ℂ) (hs : 2<s.re) :
    HasSum (fun p : UnitLowerData => unitLowerIntegral u v s freq p.1.val p.2.val.val)
      (∫z in periodDomain,eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*
        upperSection z v hv) s*ShortDraftTrace.breveE (-freq*z)) := by
  have hh := ((unitLowerEquiv u).trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))) v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [Equiv.trans_apply,unitLowerIntegral]
    rw [unitLower_summand])

lemma unitLowerTerm_eq_shifted (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (a d : Eis) (ha : a≠0) :
    unitLowerTerm u z v s a d=
      (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a)*
        ((‖eisEmbedding a‖^2:ℝ):ℂ)^(-s))*
          shiftedHeightKernel v s (eisEmbedding d/eisEmbedding ((u:Eis)*a)) z := by
  rw [unitLowerTerm,rowHeight_eq_shiftedHeightKernel z v hv s ((u:Eis)*a) d (mul_ne_zero u.ne_zero ha),
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]
  ring

lemma unitLowerTerm_integrable (u : Eisˣ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (hs : 1<s.re) (a d : Eis) (ha : a≠0) :
    Integrable (fun z=>unitLowerTerm u z v s a d) := by
  simp_rw [unitLowerTerm_eq_shifted u _ v hv s a d ha]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma unitLowerTerm_fourier_integral (u : Eisˣ) (v : ℝ) (hv : 0<v)
    (s freq : ℂ) (a d : Eis) (ha : a≠0) :
    (∫z:ℂ,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding a‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
            ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding ((u:Eis)*a))) := by
  simp_rw [unitLowerTerm_eq_shifted u _ v hv s a d ha,mul_assoc]
  rw [integral_const_mul,integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding ((u:Eis)*a)) freq]
  ring_nf

lemma unitLowerGaussTerm_factor (h a k r : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    (eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))=
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)))*
        (eisEmbedding (symbol r a)*residueAdditive (3*k) a r) := by
  have hchar : eisEmbedding (symbol (u:Eis) (a+3*r))=
      eisEmbedding (symbol (u:Eis) a)*ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3) := by
    rw [hu]
    exact symbol_omega_pow_primary_shift j a r hprimary
  have hs : symbol (a+3*r) a=symbol (3*r) a := symbol_congr ⟨1,by ring⟩
  rw [hchar,hs,symbol_mul_numerator _ _ _ hprimary,map_mul]
  have hp := unitLower_phase_identity h a r k u j ha hk
  calc
    _ = (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol r a))*
      (ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))) := by ring
    _ = _ := by rw [hp];ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma unitLowerTwistedCoefficient_add (h a k r n : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    (eisEmbedding (symbol (u:Eis) (a+3*(r+a*n)))*eisEmbedding (symbol (a+3*(r+a*n)) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(r+a*n))/eisEmbedding ((u:Eis)*a))=
    (eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a)) := by
  rw [unitLowerGaussTerm_factor h a k (r+a*n) u j ha hprimary hu hk,
    unitLowerGaussTerm_factor h a k r u j ha hprimary hu hk]
  rw [symbol_congr (show a∣r+a*n-r from ⟨n,by ring⟩),
    residueAdditive_three_congr k a (r+a*n) r ha ⟨n,by ring⟩]

lemma unitLowerTerm_weighted_translate (h a k r n : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda)
    (z : ℂ) (v : ℝ) (s : ℂ) :
    unitLowerTerm u z v s a (a+3*(r+a*((u:Eis)*n)))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
    unitLowerTerm u (z+3*eisEmbedding n) v s a (a+3*r)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding n)) := by
  let c1 := eisEmbedding (symbol (u:Eis) (a+3*(r+a*((u:Eis)*n))))*
    eisEmbedding (symbol (a+3*(r+a*((u:Eis)*n))) a)
  let c0 := eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a)
  let B := ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a)
  let Q := ninthCuspFrequency h*(3*eisEmbedding n)
  have hc0 := eisEmbedding_ne_zero (mul_ne_zero u.ne_zero ha)
  have harg : ninthCuspFrequency h*eisEmbedding (a+3*(r+a*((u:Eis)*n)))/eisEmbedding ((u:Eis)*a)=B+Q := by
    dsimp [B,Q]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero u.ne_zero,eisEmbedding_ne_zero ha]
    ;ring
  have hcoef := unitLowerTwistedCoefficient_add h a k r ((u:Eis)*n) u j ha hprimary hu hk
  change c1*ShortDraftTrace.breveE (ninthCuspFrequency h*
    eisEmbedding (a+3*(r+a*((u:Eis)*n)))/eisEmbedding ((u:Eis)*a))=c0*ShortDraftTrace.breveE B at hcoef
  rw [harg,AddChar.map_add_eq_mul] at hcoef
  have heB : ShortDraftTrace.breveE B≠0 := Complex.exp_ne_zero _
  have heQ : ShortDraftTrace.breveE Q≠0 := Complex.exp_ne_zero _
  have hmult : c1*ShortDraftTrace.breveE Q=c0 := by
    apply mul_right_cancel₀ heB
    calc
      _ = c1*(ShortDraftTrace.breveE B*ShortDraftTrace.breveE Q) := by ring
      _ = _ := hcoef
  have hsolve : c1=c0*ShortDraftTrace.breveE (-Q) := by
    rw [AddChar.map_neg_eq_inv]
    calc
      c1=c1*(ShortDraftTrace.breveE Q*(ShortDraftTrace.breveE Q)⁻¹) := by rw [mul_inv_cancel₀ heQ,mul_one]
      _ = (c1*ShortDraftTrace.breveE Q)*(ShortDraftTrace.breveE Q)⁻¹ := by ring
      _ = _ := by rw [hmult]
  have hrow : eisEmbedding ((u:Eis)*a)*z+eisEmbedding (a+3*(r+a*((u:Eis)*n)))=
      eisEmbedding ((u:Eis)*a)*(z+3*eisEmbedding n)+eisEmbedding (a+3*r) := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  change c1*((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding (a+3*(r+a*((u:Eis)*n)))‖^2+
    ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=_
  rw [hsolve,hrow]
  unfold unitLowerTerm
  have hphase : -ninthCuspFrequency h*(z+3*eisEmbedding n)=(-Q)+(-ninthCuspFrequency h*z) := by
    dsimp [Q]
    ring
  rw [hphase,AddChar.map_add_eq_mul]
  dsimp only [c0]
  ring

lemma unitLowerIntegral_sum_translate (h a k r : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 1<s.re) :
    (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a (a+3*(r+a*((u:Eis)*n))))=
      ∫z:ℂ,unitLowerTerm u z v s a (a+3*r)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have hint := trace_mul_integrable (fun z=>unitLowerTerm u z v s a (a+3*r))
    (unitLowerTerm_integrable u v hv s hs a (a+3*r) ha) (ninthCuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => unitLowerTerm_weighted_translate h a k r n u j ha hprimary hu hk z v s)

def unitCuspIndexEquiv (u : Eisˣ) : Eis≃Eis where
  toFun n := (u:Eis)*n
  invFun n := (↑u⁻¹:Eis)*n
  left_inv n := by simp [←mul_assoc]
  right_inv n := by simp [←mul_assoc]

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma unitDenominator_integral_formula (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j) (a : PrimaryLower)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∑'d:PrimaryCoprimeDenominator a,unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val := by
  obtain ⟨k,hk⟩ := unitCuspFrequency_lift h a.val u j (primaryLower_primary a) hh
  let e := (cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hf : Summable (fun d:PrimaryCoprimeDenominator a =>
      unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val) :=
    (hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs).summable.sigma_factor a
  have hsum := e.summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue a.val×Eis =>
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2))) at hsum
  rw [←e.tsum_eq]
  change (∑'q:CubicUnitResidue a.val×Eis,
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2)))=_
  rw [hsum.tsum_prod]
  have hinner (r:CubicUnitResidue a.val) :
      (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a.val
        (a.val+3*(GaussianShiftedPartition.representative a.val r.val+a.val*n)))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) (a.val+3*GaussianShiftedPartition.representative a.val r.val))*
            eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val r.val) a.val))*
              ShortDraftTrace.breveE (ninthCuspFrequency h*
                eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val r.val)/eisEmbedding ((u:Eis)*a.val))) := by
    rw [←(unitCuspIndexEquiv u).tsum_eq]
    exact (unitLowerIntegral_sum_translate h a.val k
      (GaussianShiftedPartition.representative a.val r.val) u j (primaryLower_ne_zero a)
      (primaryLower_primary a) hu hk v hv s (by linarith)).trans
        (unitLowerTerm_fourier_integral u v hv s (ninthCuspFrequency h) a.val _ (primaryLower_ne_zero a))
  simp_rw [hinner]
  exact tsum_mul_left

theorem unitLowerEisenstein_fourier (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
          unramifiedCubicGaussSeries s (3*h*(u:Eis)) := by
  have hhSum := hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs
  rw [←hhSum.tsum_eq,hhSum.summable.tsum_sigma]
  simp_rw [unitDenominator_integral_formula u j hu h hh _ v hv s hs]
  have he : (∑'a:PrimaryLower,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*unitCuspArithmeticSeries s h u := by
    rw [unitCuspArithmeticSeries,←tsum_mul_left]
    apply tsum_congr
    intro a
    ring
  rw [he,unitCuspArithmeticSeries_eq s h u j hu hh]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_entry_integer (g : levelTwo) (i j : Fin 2) :
    (3:Eis)∣((g:SL(2,Eis)) i j-((levelTwoRight g) i j:ℤ)) := by
  have he : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (g:SL(2,Eis)) =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (rationalEmbedding (levelTwoRight g)) := by
    rw [←levelTwo_product g,map_mul]
    have hn : Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (levelTwoLeft g:SL(2,Eis))=1 := (levelTwoLeft g).property
    rw [hn,one_mul]
  have h := congrArg (fun A : SL(2,Eis⧸Ideal.span {(3:Eis)})=>A i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)

def integerUpper (b : ℤ) : SL(2,ℤ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two_of]⟩
def integerLower (c : ℤ) : SL(2,ℤ) := ⟨!![1,0;c,1],by simp [Matrix.det_fin_two_of]⟩

lemma levelTwoComplexCharacter_primary (g : levelTwo)
    (ha : lambda^2∣((g:SL(2,Eis)) 0 0)-1) :
    levelTwoComplexCharacter g =
      eisEmbedding (symbol ((g:SL(2,Eis)) 1 0) ((g:SL(2,Eis)) 0 0)) := by
  let A : SL(2,Eis) := g
  let b : ℤ := levelTwoRight g 0 1
  let c : ℤ := levelTwoRight g 1 0
  have hA : (3:Eis)∣A 0 0-1 := three_dvd_primary_sub_one _ ha
  have hB : (3:Eis)∣A 0 1-(b:Eis) := levelTwo_entry_integer g 0 1
  have hC : (3:Eis)∣A 1 0-(c:Eis) := levelTwo_entry_integer g 1 0
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hD : (3:Eis)∣A 1 1-(1+(b:Eis)*(c:Eis)) := by
    have hh := dvd_add (dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_left hA (A 1 1)))
      (dvd_mul_of_dvd_left hB (A 1 0))) (dvd_mul_of_dvd_right hC (b:Eis))
    convert hh using 1 ; linear_combination hdet
  let N : SL(2,Eis) := ⟨!![A 0 0,A 0 1-(b:Eis)*A 0 0;
    A 1 0-(c:Eis)*A 0 0,A 1 1-(c:Eis)*A 0 1-(b:Eis)*(A 1 0-(c:Eis)*A 0 0)],by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact hA
    · have hh:=dvd_sub hB (dvd_mul_of_dvd_right hA (b:Eis))
      convert hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_sub hC (dvd_mul_of_dvd_right hA (c:Eis))
      convert hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_add (dvd_sub (dvd_sub hD (dvd_mul_of_dvd_right hB (c:Eis)))
        (dvd_mul_of_dvd_right hC (b:Eis))) (dvd_mul_of_dvd_right hA ((b:Eis)*(c:Eis)))
      convert hh using 1 ; dsimp [N] ; ring
  let lengthScale : levelTwo := ⟨rationalEmbedding (integerLower c),rational_mem_levelTwo _⟩
  let U : levelTwo := ⟨rationalEmbedding (integerUpper b),rational_mem_levelTwo _⟩
  let n : levelThree := ⟨N,hN⟩
  let n2 : levelTwo := ⟨N,levelThree_le_levelTwo hN⟩
  have he : g=lengthScale*n2*U := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change A i j = (((!![(1 : ℤ), 0; c, 1]).map (Int.castRingHom Eis) *
      (N : Matrix (Fin 2) (Fin 2) Eis)) *
      (!![(1 : ℤ), b; 0, 1]).map (Int.castRingHom Eis)) i j
    fin_cases i <;> fin_cases j <;>
      norm_num [N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  conv_lhs => rw [he,map_mul,map_mul]
  have hL : levelTwoComplexCharacter lengthScale=1 := levelTwoComplexCharacter_rational _
  have hU : levelTwoComplexCharacter U=1 := levelTwoComplexCharacter_rational _
  rw [hL,hU,one_mul,mul_one]
  change levelTwoComplexCharacter ⟨(n:SL(2,Eis)),levelThree_le_levelTwo n.property⟩=_
  rw [levelTwoComplexCharacter_restrict]
  change eisEmbedding (symbol (A 1 0-(c:Eis)*A 0 0) (A 0 0))=_
  congr 1
  exact symbol_congr (x:=A 1 0-(c:Eis)*A 0 0) (y:=A 1 0) (d:=A 0 0) ⟨-(c:Eis),by ring⟩

end CubicKubota

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reciprocity.PrimaryCongruences -/

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

open scoped Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma integer_congruence_primary_cases (c : Eis) (r : ℤ) (h : (3:Eis)∣c-(r:Eis)) :
    (3:Eis)∣c ∨ lambda^2∣c-1 ∨ lambda^2∣(-c)-1 := by
  have hr : (3:ℤ)∣r ∨ (3:ℤ)∣r-1 ∨ (3:ℤ)∣r+1 := by omega
  rcases hr with hr|hr|hr
  · left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis):=⟨(t:Eis),by exact_mod_cast ht⟩
    simpa using dvd_add h hn
  · right;left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)-1:=⟨(t:Eis),by exact_mod_cast ht⟩
    exact lambda_sq_dvd_three.trans (by simpa using dvd_add h hn)
  · right;right
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)+1:=⟨(t:Eis),by exact_mod_cast ht⟩
    apply lambda_sq_dvd_three.trans
    convert dvd_neg.mpr (dvd_add h hn) using 1 ; ring

lemma symbol_three_shift_primary (c a t:Eis) (hc:lambda^2∣c-1) (ha:lambda^2∣a-1) :
    symbol c (a+3*t*c)=symbol c a := by
  have hs:=primary_add_multiple_three a c t ha
  calc
    _=symbol (a+3*t*c) c:=symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ hs) hc hs
    _=symbol a c:=symbol_congr ⟨3*t,by ring⟩
    _=symbol c a:=(symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ ha) hc ha).symm

lemma symbol_three_shift_integer (c a t:Eis) (r:ℤ)
    (ha:lambda^2∣a-1) (hc:(3:Eis)∣c-(r:Eis)) :
    symbol c (a+3*t*c)=symbol c a := by
  rcases integer_congruence_primary_cases c r hc with h|h|h
  · exact symbol_three_shift c a t ha h
  · exact symbol_three_shift_primary c a t h ha
  · have hh:=symbol_three_shift_primary (-c) a (-t) h ha
    have he:a+3*(-t)*(-c)=a+3*t*c:=by ring
    rw [he,symbol_neg_numerator _ _ (primary_add_multiple_three a c t ha),
      symbol_neg_numerator _ _ ha] at hh
    exact hh

end CubicJacobiGlobal
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_cube_phase_balance (A N:levelTwo) (p q:Eis) (j:ℕ)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0) :
    levelTwoComplexCharacter N *
        eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)^j =
      levelTwoComplexCharacter A *
        eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^(3-j) := by
  have hs : symbol ((A:SL(2,Eis)) 1 0) ((A:SL(2,Eis)) 0 0) =
      symbol ((A:SL(2,Eis)) 1 0) p ^ j *
        symbol ((A:SL(2,Eis)) 1 0) ((N:SL(2,Eis)) 0 0) := by
    rw [←symbol_three_shift_integer _ _ q (levelTwoRight A 1 0) hA (levelTwo_entry_integer A 1 0),
      hx,symbol_mul_denominator,cubicSymbol_pow_denominator]
  rw [levelTwoComplexCharacter_primary N hN,levelTwoComplexCharacter_primary A hA,hc,
    symbol_mul_numerator _ _ _ hN,symbol_pow_numerator _ _ hN,
    symbol_reciprocity p ((N:SL(2,Eis)) 0 0) (primary_ne_zero _ hp) (primary_ne_zero _ hN) hp hN,
    hs,map_mul,map_pow,map_mul,map_pow]
  ring

lemma levelTwo_comparison_character (A N:levelTwo)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ *
        levelTwoComplexCharacter A = levelTwoComplexCharacter N := by
  rw [←levelTwoComplexCharacter_restrict ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩]
  change levelTwoComplexCharacter (N*A⁻¹)*levelTwoComplexCharacter A=levelTwoComplexCharacter N
  rw [map_mul,map_inv,mul_assoc]
  have hA:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [inv_mul_cancel₀ hA,mul_one]

lemma levelTwo_cube_comparison_phase (A N:levelTwo) (p q:Eis) (j:ℕ) (hj:j≤3)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ =
      eisEmbedding (symbol (((N:SL(2,Eis)) 0 0)*((A:SL(2,Eis)) 1 0)) p)^(3-j) := by
  let a:=eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)
  let b:=eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)
  have ha3:a^3=1:=by
    dsimp [a]
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hC,map_one]
  have hpow:a^j*a^(3-j)=1:=by rw [←pow_add,Nat.add_sub_of_le hj,ha3]
  have hbal:=levelTwo_cube_phase_balance A N p q j hp hA hN hx hc
  change levelTwoComplexCharacter N*a^j=levelTwoComplexCharacter A*b^(3-j) at hbal
  have he:levelTwoComplexCharacter N=levelTwoComplexCharacter A*(b*a)^(3-j):=by
    calc
      _=levelTwoComplexCharacter N*(a^j*a^(3-j)):=by rw [hpow,mul_one]
      _=(levelTwoComplexCharacter N*a^j)*a^(3-j):=(mul_assoc _ _ _).symm
      _=(levelTwoComplexCharacter A*b^(3-j))*a^(3-j):=by rw [hbal]
      _=_:=by rw [mul_pow];ring
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [symbol_mul_numerator _ _ _ hp,map_mul]
  change complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=(b*a)^(3-j)
  apply mul_right_cancel₀ hbase
  rw [hcomp,he]
  ring

end CubicKubota
end

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_cubicExp_nat_mul (n : ℕ) (t : ℤ) :
    cubicExp ((n:ℤ)*t)=cubicExp t^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,cubicExp_add,ih,pow_succ]

lemma ramified_trace_symbol (a : Eis) (ha : lambda^2∣a-1) :
    symbol ramifiedTraceLambda a=linearRay 0 (-1) a := by
  have h := symbol_traceLambda_eq_linearRay a ha
  change symbol ramifiedTraceLambda a=linearRay 0 (-1) a at h
  exact h

lemma ramifiedSymbol_primaryCoord (j n : ℕ) (A B : ℤ) :
    symbol (omega^j*ramifiedTraceLambda^n) (primaryCoord A B)=
      cubicExp ((j:ℤ)*(2*A-B)-(n:ℤ)*B) := by
  rw [symbol_mul_numerator _ _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) n,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    ramified_trace_symbol _ (primaryCoord_primary _ _),linearRay_primaryCoord,linearRay_primaryCoord,
    ←ramified_cubicExp_nat_mul,←ramified_cubicExp_nat_mul,←cubicExp_add]
  congr 1
  ring

def ramifiedAffineParameter (j n : ℕ) : Eis := (j:Eis)*ramifiedTraceLambda-(n:Eis)

lemma ramifiedAffineParameter_coords (j n : ℕ) (C D : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ramifiedAffineParameter j n*ActualEisensteinCoordinates.eval C D)).2=
      (j:ℤ)*(2*C-D)-(n:ℤ)*D := by
  have hk : ramifiedAffineParameter j n=ActualEisensteinCoordinates.eval ((j:ℤ)-(n:ℤ)) (2*(j:ℤ)) := by
    change (j:Eis)*(1+2*omega)-(n:Eis)=(((j:ℤ)-(n:ℤ):ℤ):Eis)+((2*(j:ℤ):ℤ):Eis)*omega
    push_cast
    ring
  rw [hk,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

theorem ramified_symbol_primary_shift (j n : ℕ) (a x : Eis) (ha : lambda^2∣a-1) :
    eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) (a+3*x))=
      eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) a)*
        ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  let C := (ActualEisensteinCoordinates.coords x).1
  let D := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval C D := (ActualEisensteinCoordinates.eval_coords x).symm
  have hsum : primaryCoord A B+3*x=primaryCoord (A+C) (B+D) := by
    rw [hx,primaryCoord_eq,primaryCoord_eq]
    change 1+3*(A:Eis)+3*(B:Eis)*omega+3*((C:Eis)+(D:Eis)*omega)=_
    push_cast
    ring
  rw [hsum,ramifiedSymbol_primaryCoord,ramifiedSymbol_primaryCoord]
  have ht := breveE_real_trace_of_O (3:ℝ) (ramifiedAffineParameter j n*x)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [ht,hx,ramifiedAffineParameter_coords,←embedding_cubicExp,←map_mul,←cubicExp_add]
  apply congrArg eisEmbedding
  apply congrArg cubicExp
  ring

lemma ramified_symbol_primary_shift_signed (j n : ℕ) (r a x : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) :
    eisEmbedding (symbol r (a+3*x))=eisEmbedding (symbol r a)*
      ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  rcases hr with rfl|rfl
  · exact ramified_symbol_primary_shift j n a x ha
  · rw [symbol_neg_numerator _ _ (primary_add_three a x ha),symbol_neg_numerator _ _ ha]
    exact ramified_symbol_primary_shift j n a x ha

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_square : ramifiedTraceLambda^2=(-3:Eis) := by
  unfold ramifiedTraceLambda
  linear_combination 4*ramified_omega_relation

lemma ramified_character_coprime (j n : ℕ) (r a : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) : IsCoprime r a := by
  have hc3 := (primary_coprime_three a ha).symm
  have ht : ramifiedTraceLambda∣(3:Eis) := by
    refine ⟨-ramifiedTraceLambda,?_⟩
    linear_combination ramifiedTraceLambda_square
  have hcT := hc3.of_isCoprime_of_dvd_left ht
  have hcW : IsCoprime omega a := by
    refine ⟨omega^2,0,?_⟩
    rw [zero_mul,add_zero,←pow_succ,omega_primitive.pow_eq_one]
  have hc : IsCoprime (omega^j*ramifiedTraceLambda^n) a := hcW.pow_left.mul_left hcT.pow_left
  rcases hr with rfl|rfl
  · exact hc
  · exact hc.neg_left

lemma affineCusp_phase_identity (h h1 q a k c x : Eis)
    (ha : a≠0) (hq : q≠0) (hh : h=q*h1) (hk : 3*k=h1+c*a) :
    ShortDraftTrace.breveE (eisEmbedding (c*x)/eisLam/3)*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*residueAdditive (3*k) a x := by
  have hk' : eisEmbedding k=(eisEmbedding h1+eisEmbedding c*eisEmbedding a)/3 := by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    have he := congrArg eisEmbedding hk
    simp only [map_mul,map_add,map_ofNat] at he
    linear_combination he
  rw [←AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  apply congrArg ShortDraftTrace.breveE
  rw [hh]
  simp only [ninthCuspFrequency,cuspFrequency,map_add,map_mul,map_ofNat]
  rw [hk']
  field_simp [eisEmbedding_ne_zero ha,eisEmbedding_ne_zero hq,eisLam_ne_zero]
  ;ring

def ramifiedAffineGauss (h q r a : Eis) : ℂ :=
  ∑'x:CubicUnitResidue a,
    (eisEmbedding (symbol r (a+3*GaussianShiftedPartition.representative a x.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a x.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a x.val)/eisEmbedding (q*a))

lemma ramifiedAffineGauss_factor (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a))*cubicUnitGaussSum k a := by
  rw [ramifiedAffineGauss,cubicUnitGaussSum,←tsum_mul_left]
  apply tsum_congr
  intro x
  let t := GaussianShiftedPartition.representative a x.val
  have hs : symbol (a+3*t) a=symbol (3*t) a := symbol_congr ⟨1,by ring⟩
  change (eisEmbedding (symbol r (a+3*t))*eisEmbedding (symbol (a+3*t) a))*
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))=_
  rw [ramified_symbol_primary_shift_signed j n r a t hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary]
  rw [map_mul eisEmbedding (symbol 3 a) (symbol t a)]
  have hp := affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) t ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol t a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*t)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring

theorem ramifiedAffineGauss_eq_unramified (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        cubicUnitGaussSum (3*r^2*h1) a := by
  rw [ramifiedAffineGauss_factor h h1 q r a k j n ha hprimary hq hr hh hk]
  have hcop := ramified_character_coprime j n r a hr hprimary
  have hcop3 : IsCoprime (3*r^2) a := (primary_coprime_three a hprimary).symm.mul_left hcop.pow_left
  have hp := cubicUnitGaussSum_phase_shift k (r^2) a ha hprimary hcop3
  have hc := symbol_cube_of_isCoprime r a hprimary hcop
  have hchars : eisEmbedding (symbol (r^2) a)*eisEmbedding (symbol (3*r^2) a)=
      eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a) := by
    rw [←map_mul,←symbol_mul_numerator _ _ a hprimary,
      show r^2*(3*r^2)=3*r^4 by ring,symbol_mul_numerator _ _ a hprimary,
      symbol_pow_numerator _ _ hprimary 4,pow_succ,hc,one_mul,map_mul]
    ring
  rw [hchars] at hp
  have hcong : a∣k*(9*r^2)-3*r^2*h1 := by
    refine ⟨3*r^2*ramifiedAffineParameter j n,?_⟩
    linear_combination 3*r^2*hk
  have hg := cubicUnitGaussSum_frequency_congr (k*(9*r^2)) (3*r^2*h1) a ha hcong
  calc
    _ = ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*cubicUnitGaussSum k a) := by ring
    _ = _ := by rw [hp,hg]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology Pointwise

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def eisensteinUnitRotation (u : ActualEisensteinCubic.Oˣ) : ℂ≃ₗᵢ[ℝ]ℂ where
  toFun z := eisEmbedding (u:ActualEisensteinCubic.O)*z
  invFun z := eisEmbedding (↑u⁻¹:ActualEisensteinCubic.O)*z
  left_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  right_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  map_add' z w := mul_add _ _ _
  map_smul' t z := by
    simp only [RingHom.id_apply,Complex.real_smul]
    ring
  norm_map' z := by
    change ‖eisEmbedding (u:ActualEisensteinCubic.O)*z‖=‖z‖
    rw [norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

def eisensteinUnitEquiv (u : ActualEisensteinCubic.Oˣ) : ActualEisensteinCubic.O≃ActualEisensteinCubic.O where
  toFun x := (u:ActualEisensteinCubic.O)*x
  invFun x := (↑u⁻¹:ActualEisensteinCubic.O)*x
  left_inv x := by dsimp only; rw [←mul_assoc];simp
  right_inv x := by dsimp only; rw [←mul_assoc];simp

def periodUnitEquiv (u : ActualEisensteinCubic.Oˣ) : periodLattice≃periodLattice :=
  (periodEquiv.symm.trans (eisensteinUnitEquiv u)).trans periodEquiv

lemma periodUnitEquiv_val (u : ActualEisensteinCubic.Oˣ) (x : periodLattice) :
    (periodUnitEquiv u x:ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(x:ℂ) := by
  obtain ⟨n,rfl⟩ := periodEquiv.surjective x
  dsimp only [periodUnitEquiv,Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change (periodEquiv ((u:ActualEisensteinCubic.O)*n):ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(periodEquiv n:ℂ)
  change 3*eisEmbedding ((u:ActualEisensteinCubic.O)*n)=eisEmbedding (u:ActualEisensteinCubic.O)*(3*eisEmbedding n)
  rw [map_mul]
  ring

lemma periodDomain_unit_rotation (u : ActualEisensteinCubic.Oˣ) :
    IsAddFundamentalDomain periodLattice (eisensteinUnitRotation u '' periodDomain) volume := by
  apply periodDomain_fundamental.image_of_equiv (eisensteinUnitRotation u).toEquiv
    (eisensteinUnitRotation u).symm.measurePreserving.quasiMeasurePreserving (periodUnitEquiv u⁻¹)
  intro n z
  change eisEmbedding (u:ActualEisensteinCubic.O)*((periodUnitEquiv u⁻¹ n:ℂ)+z)=
    (n:ℂ)+eisEmbedding (u:ActualEisensteinCubic.O)*z
  rw [periodUnitEquiv_val,mul_add,←mul_assoc,←map_mul]
  simp

theorem period_integral_unit_rotation (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z))=∫z in periodDomain,f z := by
  have hperiod (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*eisEmbedding m+z)=f z
    simpa only [add_comm] using hp m z
  have heq := periodDomain_fundamental.setIntegral_eq (periodDomain_unit_rotation u) hperiod
  have hchange := (eisensteinUnitRotation u).measurePreserving.setIntegral_image_emb
    (eisensteinUnitRotation u).toHomeomorph.measurableEmbedding f periodDomain
  exact hchange.symm.trans heq.symm

theorem period_integral_unit_affine (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) (b : ℂ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z+b))=∫z in periodDomain,f z := by
  have hg : ∀n : ActualEisensteinCubic.O,∀z : ℂ,(fun w=>f (w+b)) (z+3*eisEmbedding n)=(fun w=>f (w+b)) z := by
    intro n z
    dsimp
    rw [show z+3*eisEmbedding n+b=(z+b)+3*eisEmbedding n by ring,hp]
  rw [period_integral_unit_rotation (fun w=>f (w+b)) hg u]
  simpa only [add_comm] using period_integral_translation f hp b

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_action (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix T • upperPoint z v hv=
      upperPoint (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 1 1,T 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (T 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hprod : eisEmbedding (T 1 1)*star (eisEmbedding (T 1 1))=1 := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
      Complex.mul_conj (eisEmbedding (T 1 1))
  have hstar : star (eisEmbedding (T 1 1))=eisEmbedding (T 0 0) := by
    have hnon : eisEmbedding (T 1 1)≠0 := by
      intro hz
      rw [hz,norm_zero] at hn
      exact zero_ne_one hn
    apply mul_left_cancel₀ hnon
    rw [hprod,←map_mul,mul_comm,hdet,map_one]
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,star_zero,
      mul_zero,add_zero,norm_zero,hn,one_pow,hstar,map_mul]
    norm_num
    ; ring
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
      hn,one_pow,]
    norm_num

theorem period_integral_upper_triangular
    (F : HyperbolicSpace→ℂ) (v : ℝ) (hv : 0<v)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,
      F (upperPoint (3*(z+3*eisEmbedding n)) v hv)=F (upperPoint (3*z) v hv))
    (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0) :
    (∫z in periodDomain,F (integralComplexMatrix T • upperPoint (3*z) v hv))=
      ∫z in periodDomain,F (upperPoint (3*z) v hv) := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 0 0,T 1 1,hdet,by rw [mul_comm,hdet]⟩
  let f : ℂ→ℂ := fun z=>F (upperPoint (3*z) v hv)
  have he (z : ℂ) : F (integralComplexMatrix T • upperPoint (3*z) v hv)=
      f (eisEmbedding (↑(u^2):ActualEisensteinCubic.O)*z+eisEmbedding (T 0 0*T 0 1)/3) := by
    rw [integral_upper_triangular_action T hc]
    dsimp only [f]
    congr 2
    simp only [Units.val_pow_eq_pow_val,map_pow]
    ring
  simp_rw [he]
  exact period_integral_unit_affine f hp (u^2) _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

lemma series_scaled_three_average_zero (coeff : SubexponentialBesselCoefficients)
    (v : ℝ) (hv : 0<v) : (∫z in periodDomain,coeff.series (v,3*z))=0 := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.term h (v,3*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.term h (v,3*z))
    simp_rw [coeff.term_eq_amplitude v hv h]
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*(3*z))+
        starRingEnd ℂ (cuspFrequency h*(3*z)))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) :=
    hbound h (v,3*z) ⟨le_rfl,le_rfl⟩
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
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=0 := by
    have he (z : ℂ) : cuspFrequency h*(3*z)= -cuspFrequency (-(3*h))*z := by
      simp only [cuspFrequency,map_neg,map_mul,map_ofNat]
      ring
    change (∫z in periodDomain,coeff.term h (v,3*z))=0
    simp_rw [coeff.term_eq_amplitude v hv h,he]
    rw [integral_const_mul,integral_cusp_character]
    by_cases hh : h=0
    · simp [hh,amplitude]
    · have hk : -(3*h)≠(0:ActualEisensteinCubic.O) := neg_ne_zero.mpr (mul_ne_zero (by norm_num) hh)
      simp [hk]
  change (∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z)=0
  rw [←integral_tsum_of_summable_integral_norm hi hs]
  simp_rw [hterm]
  exact tsum_zero

lemma fullFunction_scaled_three_average (coeff : SubexponentialBesselCoefficients)
    (c : ℂ) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,coeff.fullFunction c (upperPoint (3*z) v hv))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*c*(v:ℂ)^(2/3:ℂ) := by
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  have hc : Continuous (fun z : ℂ=>coeff.series (v,3*z)) :=
    (coeff.series_height_continuous v hv).comp (continuous_const.mul continuous_id)
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  rw [integral_add (integrable_const _) (periodDomain_integrable_of_continuous _ hc),
    series_scaled_three_average_zero coeff v hv,add_zero,setIntegral_const]
  rw [Measure.real,periodDomain_volume,ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul]
  ring

end SubexponentialBesselCoefficients

theorem cubicSource_scaled_three_average (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (upperPoint (3*z) v hv))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)*(v:ℂ)^(2/3:ℂ) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_scaled_three_average _ v hv

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

lemma lowerCuspMatrix_zero : lowerCuspMatrix (0:ActualEisensteinCubic.O)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerCuspMatrix]

lemma cubicSource_scaled_periodic (v : ℝ) (hv : 0<v) (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (upperPoint (3*(z+3*eisEmbedding n)) v hv)=
      cubicSourceResidualFunction (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding n)=3*z+3*eisEmbedding (3*n) := by
    rw [map_mul,map_ofNat]
    ring
  rw [cubicSourceResidualFunction_eq_bessel,he]
  exact sourceBesselFunction_period v hv (3*z) (3*n)

lemma sourceCuspRepresentative_periodic (j : Fin 3) (v : ℝ) (hv : 0<v) (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) •
      upperPoint (3*(z+3*eisEmbedding n)) v hv)=
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) •
      upperPoint (3*z) v hv) := by
  fin_cases j
  · simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using cubicSource_scaled_periodic v hv n z
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_scaled_periodic10 v hv n z
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_scaled_periodic19 v hv n z

def sourcePrincipalCuspConstant : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)

lemma sourceCuspRepresentative_average (j : Fin 3) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • upperPoint (3*z) v hv))=
      (if j=0 then sourcePrincipalCuspConstant else 0)*(v:ℂ)^(2/3:ℂ) := by
  fin_cases j
  · simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero,sourcePrincipalCuspConstant] using
      cubicSource_scaled_three_average v hv
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_zero_mode10 v hv
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_zero_mode19 v hv

lemma sourceCusp_average_of_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      (levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0))*(v:ℂ)^(2/3:ℂ) := by
  have he (z : ℂ) : cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • upperPoint (3*z) v hv)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  simp_rw [he]
  rw [integral_const_mul]
  have hi := period_integral_upper_triangular
    (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
    v hv (sourceCuspRepresentative_periodic j v hv) T hT
  rw [hi,sourceCuspRepresentative_average]
  ring

def sourceCuspConstant (M : SL(2,ActualEisensteinCubic.O)) : ℂ :=
  ∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) 1 (by norm_num))

theorem sourceCusp_average_all (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  have h1 := sourceCusp_average_of_decomposition M G j T hT hM 1 (by norm_num)
  have hc : sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by
    simpa only [sourceCuspConstant,Complex.ofReal_one,Complex.one_cpow,mul_one] using h1
  rw [hc]
  exact sourceCusp_average_of_decomposition M G j T hT hM v hv

theorem sourceCuspConstant_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by
  simpa only [sourceCuspConstant,Complex.ofReal_one,Complex.one_cpow,mul_one] using
    sourceCusp_average_of_decomposition M G j T hT hM 1 (by norm_num)

lemma sourcePrincipalCuspConstant_ne_zero : sourcePrincipalCuspConstant≠0 := by
  unfold sourcePrincipalCuspConstant
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      constantArithmeticResidue_ne_zero

lemma sourceCuspConstant_zero_iff (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=0 ↔ j≠0 := by
  have hG : levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn := norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  rw [sourceCuspConstant_decomposition M G j T hT hM]
  by_cases hj : j=0 <;> simp [hj,hG,sourcePrincipalCuspConstant_ne_zero]

lemma sourceCuspConstant_left (G : levelTwo) (M : SL(2,ActualEisensteinCubic.O)) :
    sourceCuspConstant ((G:SL(2,ActualEisensteinCubic.O))*M)=levelTwoComplexCharacter G*sourceCuspConstant M := by
  unfold sourceCuspConstant
  simp_rw [map_mul,mul_smul,cubicSourceResidualFunction_automorphy]
  exact integral_const_mul _ _

lemma sourceCuspConstant_upper_right (M T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) :
    sourceCuspConstant (M*T)=sourceCuspConstant M := by
  obtain ⟨G,j,S,hS,_,_,hM⟩ := three_cusp_decomposition M
  have hST : (S*T) 1 0=0 := by
    change (∑k : Fin 2,S 1 k*T k 0)=0
    rw [Fin.sum_univ_two,hS,hT]
    ring
  have he : M*T=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*(S*T) := by rw [hM]; group
  rw [sourceCuspConstant_decomposition (M*T) G j (S*T) hST he,
    sourceCuspConstant_decomposition M G j S hS hM]

end CubicEisenstein

end

end OAI

end

