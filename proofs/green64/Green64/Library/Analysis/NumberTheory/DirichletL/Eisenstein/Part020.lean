module

public import Green64.Library.Analysis.NumberTheory.DirichletL.GaussSum.Part007

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part020

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.SourceCuspKernels -/

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
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def sourceCuspCoefficients (j : Fin 3) : SubexponentialBesselCoefficients :=
  ![sourceBesselCoefficients,ramifiedBesselCoefficients false,ramifiedBesselCoefficients true] j

def sourceCuspScale (j : Fin 3) : ℝ := ![1,3,3] j
def sourceCuspBesselConstant (j : Fin 3) : ℂ := ![(3*Real.pi)*constantArithmeticResidue,0,0] j

lemma sourceCuspScale_pos (j : Fin 3) : 0<sourceCuspScale j := by
  fin_cases j <;> norm_num [sourceCuspScale]

lemma ramifiedSource_scaled_fullFunction (side : Bool) (v : ℝ) (hv : 0<v) (z : ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      (ramifiedBesselCoefficients side).fullFunction 0
        (upperPoint (z/3) (v/3) (by positivity)) := by
  rw [ramifiedSource_eq_series]
  simp only [SubexponentialBesselCoefficients.fullFunction,zero_mul,zero_add,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]

theorem sourceCusp_bessel_expansion (j : Fin 3) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)=
      (sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (z/(sourceCuspScale j:ℂ)) (v/sourceCuspScale j)
          (div_pos hv (sourceCuspScale_pos j))) := by
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      lowerCuspMatrix_zero,sourceBesselFunction] using congrFun cubicSourceResidualFunction_eq_bessel (upperPoint z v hv)
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val] using
      ramifiedSource_scaled_fullFunction false v hv z
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val] using
      ramifiedSource_scaled_fullFunction true v hv z

def sourceCuspZTerm (j : Fin 3) (z : ℂ) (v : ℝ) (h : Eis) : ℂ :=
  (sourceCuspCoefficients j).scaledConjugateZTerm (sourceCuspScale j) v z h

theorem sourceCuspZFamily_series (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspZFamily j z v=∑'h:Eis,sourceCuspZTerm j z v h := by
  rw [sourceCuspZFamily,cuspZProfile_positive _ _ _ hv]
  have he : (fun w=>cubicSourceConjugateFunction (integralComplexMatrix (cuspRepresentative j) • upperPoint w v hv))=
      fun w=>star ((sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (w/(sourceCuspScale j:ℂ)) (v/sourceCuspScale j) (div_pos hv (sourceCuspScale_pos j)))) := by
    funext w
    exact congrArg star (sourceCusp_bessel_expansion j v hv w)
  rw [he]
  exact (sourceCuspCoefficients j).scaledConjugate_wirtingerZ (sourceCuspBesselConstant j)
    (sourceCuspScale j) (sourceCuspScale_pos j) v hv z

theorem sourceCuspZTerm_summable (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    Summable (sourceCuspZTerm j z v) :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_summable (sourceCuspScale j) (sourceCuspScale_pos j) v hv z

lemma sourceCuspZTerm_zero (j : Fin 3) (z : ℂ) (v : ℝ) : sourceCuspZTerm j z v 0=0 :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_zero _ _ _

lemma sourceCuspZTerm_bessel (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v)
    (h : Eis) (hh : h≠0) :
    sourceCuspZTerm j z v h=
      (-2*Real.pi*Complex.I*cuspFrequency h/(sourceCuspScale j:ℂ))*
        star ((sourceCuspCoefficients j).value h)*((v/sourceCuspScale j:ℝ):ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/sourceCuspScale j))*
          ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ))) :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_bessel _ (sourceCuspScale_pos j) v hv z h hh

theorem thetaTwistedCuspProfile_reflected_series (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd : ∀h,(d h).point=thetaFourierTranslation c h) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((d h).multiplier/(v:ℂ)^2*
          ∑'n:Eis,sourceCuspZTerm (d h).index (d h).dualPoint (((d h).heightScale*v)⁻¹) n) := by
  rw [thetaTwistedCuspProfile_reflection_of_data Ψ c hc d hd v hv]
  apply Finset.sum_congr rfl
  intro h hh
  rw [sourceCuspZFamily_series _ _ _ (inv_pos.mpr (mul_pos (d h).heightScale_pos hv))]

def finiteReflectedSourceTerm (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (v : ℝ) (h : Eis⧸Ideal.span {c}) (n : Eis) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
    ((d h).multiplier/(v:ℂ)^2*
      sourceCuspZTerm (d h).index (d h).dualPoint (((d h).heightScale*v)⁻¹) n)

theorem finiteReflectedSourceTerm_summable (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (v : ℝ) (hv : 0<v) (h : Eis⧸Ideal.span {c}) :
    Summable (finiteReflectedSourceTerm Ψ c hc d v h) :=
  ((sourceCuspZTerm_summable _ _ _ (inv_pos.mpr (mul_pos (d h).heightScale_pos hv))).mul_left _).mul_left _

theorem thetaTwistedCuspProfile_reflected_single_series (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd : ∀h,(d h).point=thetaFourierTranslation c h) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑'n:Eis,∑h:Eis⧸Ideal.span {c},finiteReflectedSourceTerm Ψ c hc d v h n := by
  rw [thetaTwistedCuspProfile_reflected_series Ψ c hc d hd v hv,
    Summable.tsum_finsetSum (fun h hh=>finiteReflectedSourceTerm_summable Ψ c hc d v hv h)]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [finiteReflectedSourceTerm,tsum_mul_left]

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def sourceCuspRadialLength (h : Eis) : ℝ := if h=0 then 1 else ‖eisEmbedding h‖^2
def sourceCuspRadialScale (j : Fin 3) : ℝ := thetaBesselScale/sourceCuspScale j

def sourceCuspRadialBaseCoefficient (j : Fin 3) (h : Eis) : ℂ :=
  (-2*Real.pi*Complex.I*cuspFrequency h)*star ((sourceCuspCoefficients j).value h)/
    ((sourceCuspScale j:ℂ)^2*(sourceCuspRadialLength h:ℂ))

def sourceCuspRadialCoefficient (j : Fin 3) (z : ℂ) (h : Eis) : ℂ :=
  sourceCuspRadialBaseCoefficient j h*
    ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ)))

lemma sourceCuspRadialLength_pos (h : Eis) : 0<sourceCuspRadialLength h := by
  by_cases hh:h=0
  · simp only [sourceCuspRadialLength,ite_eq_left hh,zero_lt_one]
  · rw [sourceCuspRadialLength,ite_eq_right hh]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))

lemma sourceCuspRadialScale_pos (j : Fin 3) : 0<sourceCuspRadialScale j :=
  div_pos thetaBesselScale_pos (sourceCuspScale_pos j)

lemma sourceCuspRadialCoefficient_norm (j : Fin 3) (z : ℂ) (h : Eis) :
    ‖sourceCuspRadialCoefficient j z h‖=‖sourceCuspRadialBaseCoefficient j h‖ := by
  rw [sourceCuspRadialCoefficient,norm_mul,breveE_norm,mul_one]

lemma sourceCuspRadialCoefficient_zero (j : Fin 3) (z : ℂ) :
    sourceCuspRadialCoefficient j z 0=0 := by
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,cuspFrequency,
    map_zero,zero_div,mul_zero,zero_mul]

lemma sourceCuspRadialLength_frequency (h : Eis) (hh : h≠0) :
    ‖cuspFrequency h‖=thetaBesselScale*Real.sqrt (sourceCuspRadialLength h) := by
  rw [cuspFrequency_eq_thetaFrequencyScale,norm_mul,sourceCuspRadialLength,ite_eq_right hh,
    Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem sourceCuspZTerm_eq_radial (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) (h : Eis) :
    sourceCuspZTerm j z v h=
      (sourceCuspRadialCoefficient j z h*(sourceCuspRadialLength h:ℂ))*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*sourceCuspRadialScale j*Real.sqrt (sourceCuspRadialLength h)*v) := by
  by_cases hh:h=0
  · subst h
    rw [sourceCuspZTerm_zero,sourceCuspRadialCoefficient_zero]
    ring
  · rw [sourceCuspZTerm_bessel j z v hv h hh,sourceCuspRadialLength_frequency h hh]
    have ha : 4*Real.pi*(thetaBesselScale*Real.sqrt (sourceCuspRadialLength h))*(v/sourceCuspScale j)=
        4*Real.pi*sourceCuspRadialScale j*Real.sqrt (sourceCuspRadialLength h)*v := by
      unfold sourceCuspRadialScale
      ring
    rw [ha]
    have hs0 : (sourceCuspScale j:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
    have hl0 : (sourceCuspRadialLength h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceCuspRadialLength_pos h).ne'
    simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,Complex.ofReal_div]
    field_simp [hs0,hl0]

theorem sourceCuspZFamily_eq_radialBesselProfile (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspZFamily j z v=
      radialBesselProfile sourceCuspRadialLength (sourceCuspRadialCoefficient j z) (sourceCuspRadialScale j) v := by
  rw [sourceCuspZFamily_series j z v hv]
  exact tsum_congr (sourceCuspZTerm_eq_radial j z v hv)

theorem thetaTwistedCuspProfile_reflected_radial (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd : ∀h,(d h).point=thetaFourierTranslation c h) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((d h).multiplier/(v:ℂ)^2*
          radialBesselProfile sourceCuspRadialLength
            (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
            (sourceCuspRadialScale (d h).index) (((d h).heightScale*v)⁻¹)) := by
  rw [thetaTwistedCuspProfile_reflection_of_data Ψ c hc d hd v hv]
  apply Finset.sum_congr rfl
  intro h hh
  rw [sourceCuspZFamily_eq_radialBesselProfile _ _ _ (inv_pos.mpr (mul_pos (d h).heightScale_pos hv))]

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

lemma positive_nat_pow_cpow (x:ℝ) (hx:0≤x) (n:ℕ) (s:ℂ) :
    ((x^n:ℝ):ℂ)^s=((x:ℂ)^s)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hx n) hx,
        hn,pow_succ]

lemma positive_reflection_powers (Q u d X r:ℝ)
    (hQ:0<Q) (hu:0<u) (hd:0<d) (hX:0<X) (hr:0< r) (w:ℂ) :
    (Q:ℂ)^(1+2*w)*(u:ℂ)^(2-2*w)*(2:ℂ)^(4*w)/(d:ℂ)^(2+2*w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(u/d)^2:ℝ):ℂ)*((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^(-w) := by
  have hQ0:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hu0:(u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hu.ne'
  have hd0:(d:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hd.ne'
  have hX0:(X:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hX.ne'
  have hr0:(r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hQp:(Q:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hQ0)
  have hup:(u:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hu0)
  have hdp:(d:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hd0)
  have hXp:(X:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hX0)
  have hrp:(r:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hr0)
  have h2p:(2:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have h16:((16:ℝ):ℂ)^w=((2:ℂ)^w)^4 := by
    have hh:=positive_nat_pow_cpow 2 (by norm_num) 4 w
    norm_num only [show (2:ℝ)^4=16 by norm_num] at hh
    exact hh
  have hy:((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^w=
      (((u:ℂ)^w)^2*((d:ℂ)^w)^2*(X:ℂ)^w*(r:ℂ)^w)/
        (((2:ℂ)^w)^4*((Q:ℂ)^w)^2) := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (by positivity) (by positivity)]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hr.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hX.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    rw [positive_nat_pow_cpow u hu.le,positive_nat_pow_cpow d hd.le,
      positive_nat_pow_cpow Q hQ.le,h16]
  rw [Complex.cpow_add _ _ hQ0,Complex.cpow_one,
    Complex.cpow_sub _ _ hu0,Complex.cpow_add _ _ hd0]
  simp only [Complex.cpow_ofNat_mul,Complex.cpow_ofNat]
  rw [Complex.cpow_neg,Complex.cpow_neg,Complex.cpow_neg,hy]
  push_cast
  field_simp

theorem bessel_reflection_scale (q d Q X r:ℝ)
    (hq:0<q) (hd:0<d) (hQ:0<Q) (hX:0<X) (hr:0< r) (w:ℂ) :
    (Q:ℂ)^(2-2*(1/2-w))*besselReflectionFactor q d (1/2-w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(q/d)^2:ℝ):ℂ)*
        ((CubicReflectionKernel.paperScale*(27*q^2*d^2*X*r/Q^2):ℝ):ℂ)^(-w) := by
  have he:=positive_reflection_powers Q (4*Real.pi*q) (4*Real.pi*d) X r
    hQ (by positivity) (by positivity) hX hr w
  have hp:Q*((4*Real.pi*q)/(4*Real.pi*d))^2=Q*(q/d)^2 := by
    field_simp
  have hy:(4*Real.pi*q)^2*(4*Real.pi*d)^2*X*r/(16*Q^2)=
      CubicReflectionKernel.paperScale*(27*q^2*d^2*X*r/Q^2) := by
    unfold CubicReflectionKernel.paperScale
    ring
  rw [hp,hy] at he
  unfold besselReflectionFactor
  convert he using 1 ; congr 2 ; ring_nf

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

namespace CubicReflectionKernel

lemma paperKernel_three_halves (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (x:ℝ) (hx:0<x) :
    paperKernel V x=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      ((paperScale*x:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
        mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I) := by
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  change paperKernel V x=_
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*gammaMultiplier s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using he

lemma paperKernel_three_halves_bound (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V) :
    ∃C:ℝ,0<C ∧ ∀x:ℝ,0<x→‖paperKernel V x‖≤C*(paperScale*x)^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩:=mellinInv_euler_line_bound V v0 v1 hv0 hVs hV 2 0
  refine ⟨C,hC,?_⟩
  intro x hx
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*gammaMultiplier s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  rw [he]
  exact hb (3/2) (by norm_num) (paperScale*x) (mul_pos paperScale_pos hx)

end CubicReflectionKernel
namespace CompletedGauss

section
open CubicReflectionKernel

lemma paperKernel_weighted_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>a i*paperKernel V (c*r i)) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound V v0 v1 hv0 hVs hV
  apply Summable.of_norm
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _≤‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

theorem paperKernel_weighted_mellin {α:Type*} [Countable α]
    (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) :
    (∑'i,a i*paperKernel V (c*r i))=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      (∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
        (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
          mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)) := by
  let M:ℝ→ℂ:=fun t=>((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
    mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)
  have hM:Integrable M:=by
    simpa only [M,inverseMellinIntegrand,Complex.ofReal_div,Complex.ofReal_ofNat] using
      inverseMellinIntegrand_vertical_integrable V v0 v1 hv0 hVs hV 2 0 (3/2)
        (by norm_num) (paperScale*c) (mul_pos paperScale_pos hc)
  have hi (i:α) : a i*paperKernel V (c*r i)=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I))*M t := by
    rw [paperKernel_three_halves V v0 v1 hv0 hVs hV _ (mul_pos hc (hr i))]
    rw [←mul_assoc,mul_comm (a i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_pos paperScale_pos hc).le (hr i).le]
    dsimp only [M]
    ring
  simp_rw [hi]
  rw [tsum_mul_left]
  congr 1
  simpa only [M,Complex.ofReal_div,Complex.ofReal_ofNat] using
    weighted_vertical_sum_integral r hr a (3/2) has M hM

end

open CubicEisenstein CubicReflectionKernel

lemma besselSmoothingIntegrand_reflected_kernel_line {α:Type*} [Countable α]
    (F:ℝ→ℂ) (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hreflect:∀v:ℝ,0<v→F v=A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (X:ℝ) (hX:0<X) (t:ℝ) :
    besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I)=
      (A*((Q*(q/d)^2:ℝ):ℂ))*
        ((∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
          (((paperScale*(27*q^2*d^2*X/Q^2):ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
            mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I))) := by
  let s:ℂ:=(-1:ℂ)+(-t)*Complex.I
  let w:ℂ:=(3/2:ℂ)+t*Complex.I
  have hs:s.re-1/2=-(3/2:ℝ):=by dsimp [s];norm_num
  have hslt:s.re<4/3:=by dsimp [s];norm_num
  have hsum:Summable (fun i=>‖a i‖*(r i)^(s.re-1/2)):=by simpa only [hs] using has
  have hsw:1/2-w=s:=by dsimp [s,w];ring
  have hw:1/2-s=w:=by rw [←hsw];ring
  have hsw':s-1/2=-w:=by rw [←hsw];ring
  have hp:=bessel_reflection_scale q d Q X 1 hq hd hQ hX (by norm_num) w
  simp only [hsw,Complex.ofReal_one,Complex.one_cpow,mul_one] at hp
  have he:=continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect s hslt hsum
  change besselSmoothingIntegrand F q V X s=_
  rw [besselSmoothingIntegrand,he,hw,hsw']
  change _=(A*((Q*(q/d)^2:ℝ):ℂ))*
    ((∑'i,a i*(r i:ℂ)^(-w))*
      (((paperScale*(27*q^2*d^2*X/Q^2):ℝ):ℂ)^(-w)*mellinEulerData V 0 w))
  rw [mellinEulerData,pow_zero,one_mul,mellinData]
  calc
    _=(A*mellin V (-w)*gammaMultiplier w*(∑'i,a i*(r i:ℂ)^(-w)))*
      ((Q:ℂ)^(2-2*s)*besselReflectionFactor q d s*(X:ℂ)^(-w)):=by ring
    _=_:=by rw [hp];ring

theorem completedT_smoothed_reflection {α:Type*} [Countable α]
    (Ψ:ActualEisensteinCubic.O→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hF:∀s:ℂ,MellinConvergent (completedBesselProfile Ψ q) s)
    (hFe:Differentiable ℂ (mellin (completedBesselProfile Ψ q)))
    (hreflect:∀v:ℝ,0<v→ completedBesselProfile Ψ q v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=
      (A*(Q:ℂ)*((q/d:ℝ):ℂ)^2)*
        ∑'i,a i*paperKernel (Vstar W) (27*q^2*d^2*X*r i/Q^2) := by
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  have hl:=besselSmoothingIntegrand_reflected_integrable (completedBesselProfile Ψ q)
    r hr a q d Q hq hd hQ A hreflect has (Vstar W) v0 v1 hv0 hVs hV X hX
  have hlreal : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X
        (((-1:ℝ):ℂ)+t*Complex.I)) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hl
  have hshift:=completedT_mellin_shift Ψ hΨ q hq hF hFe W v0 v1 hv0 hWs hW X hX
    (-1) (by norm_num) hlreal
  let c:ℝ:=27*q^2*d^2*X/Q^2
  have hc:0<c:=by dsimp [c];positivity
  let M:ℝ→ℂ:=fun t=>(∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
    (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
      mellinEulerData (Vstar W) 0 ((3/2:ℂ)+t*Complex.I))
  have hk:=paperKernel_weighted_mellin r hr a has (Vstar W) v0 v1 hv0 hVs hV c hc
  have hpoint (t:ℝ) :
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((-1:ℂ)+(-t)*Complex.I)=
        (A*((Q*(q/d)^2:ℝ):ℂ))*M t :=
    besselSmoothingIntegrand_reflected_kernel_line (completedBesselProfile Ψ q)
      r hr a q d Q hq hd hQ A hreflect has (Vstar W) X hX t
  calc
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hshift
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((-1:ℂ)+(-t)*Complex.I):=by
      congr 1
      simpa only [Complex.ofReal_neg] using
        (integral_neg_eq_self (fun t:ℝ=>
          besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X
            ((-1:ℂ)+t*Complex.I)) volume).symm
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*((1/(2*Real.pi):ℂ)*∫t:ℝ,M t):=by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*(∑'i,a i*paperKernel (Vstar W) (c*r i)):=by rw [hk]
    _=_:=by
      push_cast
      congr 1
      · ring
      · apply tsum_congr
        intro i
        congr 2
        dsimp [c]
        ring

theorem reflected_paperKernel_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (q d Q X:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (hX:0<X)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W) :
    Summable (fun i=>a i*paperKernel (Vstar W) (27*q^2*d^2*X*r i/Q^2)) := by
  have h:=paperKernel_weighted_summable r hr a has (Vstar W) v0 v1 hv0
    (Vstar_support W v0 v1 hWs) (Vstar_contDiff W v0 v1 hv0 hWs hW)
    (27*q^2*d^2*X/Q^2) (by positivity)
  apply h.congr
  intro i
  congr 2
  ring

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

namespace CompletedGauss
open CubicEisenstein CubicReflectionKernel

theorem besselSmoothingIntegral_reflected_kernel {α:Type*} [Countable α]
    (F:ℝ→ℂ) (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hreflect:∀v:ℝ,0<v→F v=A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (X:ℝ) (hX:0<X) :
    (1/(2*Real.pi):ℂ)*∫t:ℝ,besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)=
      (A*(Q:ℂ)*((q/d:ℝ):ℂ)^2)*
        ∑'i,a i*paperKernel V (27*q^2*d^2*X*r i/Q^2) := by
  let c:ℝ:=27*q^2*d^2*X/Q^2
  have hc:0<c:=by dsimp [c];positivity
  let M:ℝ→ℂ:=fun t=>(∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
    (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
      mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I))
  have hk:=paperKernel_weighted_mellin r hr a has V v0 v1 hv0 hVs hV c hc
  have hpoint (t:ℝ) :
      besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I)=
        (A*((Q*(q/d)^2:ℝ):ℂ))*M t :=
    besselSmoothingIntegrand_reflected_kernel_line F
      r hr a q d Q hq hd hQ A hreflect has V X hX t
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I):=by
      congr 1
      simpa only [Complex.ofReal_neg] using
        (integral_neg_eq_self (fun t:ℝ=>
          besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) volume).symm
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*((1/(2*Real.pi):ℂ)*∫t:ℝ,M t):=by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*(∑'i,a i*paperKernel V (c*r i)):=by rw [hk]
    _=_:=by
      push_cast
      congr 1
      · ring
      · apply tsum_congr
        intro i
        congr 2
        dsimp [c]
        ring

theorem paperKernel_weighted_norm_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>‖a i*paperKernel V (c*r i)‖) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound V v0 v1 hv0 hVs hV
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _≤‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

end CompletedGauss

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.FullFrequencyExpansion -/

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
open scoped Classical BigOperators

open ActualEisensteinCubic CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem thetaFullFrequency_tsum (c w : Eis→ℂ)
    (hsupp : ∀h:Eis,h≠0→c h≠0→∃p:ThetaFullIndex,thetaFullFrequency p=h) :
    (∑'h:{h:Eis // h≠0},w h.val*c h.val)=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*c (thetaFullFrequency p) := by
  let phi : ThetaFullIndex→{h:Eis // h≠0} := fun p=>⟨thetaFullFrequency p,thetaFullFrequency_ne_zero p⟩
  let f : {h:Eis // h≠0}→ℂ := fun h=>w h.val*c h.val
  have hinj : Function.Injective phi := by
    intro p q hpq
    exact thetaFullFrequency_injective (congrArg Subtype.val hpq)
  change (∑'h:{h:Eis // h≠0},f h)=∑'p:ThetaFullIndex,f (phi p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p:Function.support (fun p:ThetaFullIndex=>f (phi p))=>phi p.val)
  · exact hinj.comp Subtype.val_injective
  · intro h hh
    have hc : c h.val≠0 := by
      intro hz
      exact hh (by simp only [f,hz,mul_zero])
    obtain ⟨p,hp⟩:=hsupp h.val h.property hc
    have hphi : phi p=h := Subtype.ext hp
    have hfp : f (phi p)≠0 := by rwa [hphi]
    exact ⟨⟨p,hfp⟩,hphi⟩
  · intro p
    rfl

theorem sourceFourier_tsum_full_index (w : Eis→ℂ) :
    (∑'h:{h:Eis // h≠0},w h.val*star (sourceResidualFourierCoefficient h.val))=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*
        star (sourceResidualFourierCoefficient (thetaFullFrequency p)) := by
  apply thetaFullFrequency_tsum (fun h => star (sourceResidualFourierCoefficient h)) w
  intro h hh hc
  have hn : sourceResidualFourierCoefficient h≠0 := by
    intro hz
    exact hc (by rw [hz,star_zero])
  obtain ⟨u,m,I,J,hsq,hI,hJ,hfactor⟩:=
    sourceResidualFourierCoefficient_full_squarefree_cube_support h hh hn
  refine ⟨(u,m,(⟨I,hsq,hI⟩,⟨J,hJ⟩)),?_⟩
  exact hfactor.symm

theorem ramifiedFourier_tsum_full_index (side : Bool) (w : Eis→ℂ) :
    (∑'h:{h:Eis // h≠0},w h.val*star (ramifiedBesselValue side h.val))=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*
        star (ramifiedBesselValue side (thetaFullFrequency p)) := by
  apply thetaFullFrequency_tsum (fun h => star (ramifiedBesselValue side h)) w
  intro h hh hc
  have hn : ramifiedBesselValue side h≠0 := by
    intro hz
    exact hc (by rw [hz,star_zero])
  obtain ⟨u,m,I,J,hsq,hI,hJ,hfactor⟩:=ramifiedBesselValue_squarefree_cube_support side h hh hn
  refine ⟨(u,m,(⟨I,hsq,hI⟩,⟨J,hJ⟩)),?_⟩
  exact hfactor.symm

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma squarefreeCube_scale_le_norm_third (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (u:Eisˣ) (m:ℕ) :
    (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖≤
      ‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ) := by
  have hn:1≤‖eisEmbedding (primaryGenerator I)‖:=cubePrime_norm_ge_one _ hI
  have hn':1≤‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ):=
    Real.one_le_rpow hn (by norm_num)
  have hb:(‖eisEmbedding (primaryGenerator J)‖^3)^(1/3:ℝ)=‖eisEmbedding (primaryGenerator J)‖:=by
    rw [←Real.rpow_natCast_mul (norm_nonneg _)]
    norm_num
  have he:‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ)=
      (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ)*
        ‖eisEmbedding (primaryGenerator J)‖:=by
    rw [map_mul,map_mul,map_pow,norm_mul,norm_mul,norm_pow,
      Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _),
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),ramified_norm_third,hb]
  rw [he]
  have hscale:0≤(3:ℝ)^((m:ℝ)/6):=Real.rpow_nonneg (by norm_num) _
  have hbn:0≤‖eisEmbedding (primaryGenerator J)‖:=norm_nonneg _
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hscale hn') hbn

lemma coefficient_polynomial_of_squarefree_cube_support (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hsupport:∀h:Eis,h≠0→F h≠0→∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)
    (hbound:∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→
      ∀(u:Eisˣ) (m:ℕ),
      ‖F ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖)
    (h:Eis) (hh:h≠0) : ‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  by_cases hz:F h=0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨u,m,I,J,hsq,hI,hJ,rfl⟩:=hsupport h hh hz
  refine (hbound I J hI hJ hsq u m).trans ?_
  have hb:=mul_le_mul_of_nonneg_left (squarefreeCube_scale_le_norm_third I J hI u m) hC
  exact (by simpa only [mul_assoc] using hb)

theorem three_cusp_coefficients_polynomial_bound :
    ∃C:ℝ,0<C ∧ ∀h:Eis,h≠0→
      ‖sourceResidualFourierCoefficient h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) ∧
      ∀side:Bool,‖ramifiedBesselValue side h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_squarefree_cube_bound
  refine ⟨C,hC,?_⟩
  intro h hh
  constructor
  · exact coefficient_polynomial_of_squarefree_cube_support sourceResidualFourierCoefficient C hC.le
      sourceResidualFourierCoefficient_full_squarefree_cube_support
      (fun I J hI hJ hsq u m=>(hbound I J hI hJ hsq u m).1) h hh
  · intro side
    exact coefficient_polynomial_of_squarefree_cube_support (ramifiedBesselValue side) C hC.le
      (ramifiedBesselValue_squarefree_cube_support side)
      (fun I J hI hJ hsq u m=>(hbound I J hI hJ hsq u m).2 side) h hh

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma coefficient_weighted_summable_of_polynomial (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hF:∀h:Eis,h≠0→‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ)) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:0<D^(-4:ℝ):=Real.rpow_pos_of_pos hD _
  have hs:Summable (fun h:Eis=>(C/D^(-4:ℝ))*‖eisEmbedding h‖^(-(11/3):ℝ)):=
    (summable_embedding_rpow (-(11/3):ℝ) (by norm_num)).mul_left _
  apply Summable.of_nonneg_of_le (fun h=>by split_ifs <;> positivity) _ hs
  intro h
  split_ifs with hh
  · exact mul_nonneg (div_nonneg hC hDp.le) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have he:‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)=
        ‖eisEmbedding h‖^(-(11/3):ℝ):=by
      rw [←Real.rpow_add hx]
      congr 1
      norm_num
    calc
      _≤(C*‖eisEmbedding h‖^(1/3:ℝ))*‖cuspFrequency h‖^(-4:ℝ):=
        mul_le_mul_of_nonneg_right (hF h hh) (Real.rpow_nonneg (norm_nonneg _) _)
      _=(C/D^(-4:ℝ))*(‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)):=by
        rw [cuspFrequency,norm_div,Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
        change (C*‖eisEmbedding h‖^(1/3:ℝ))*(‖eisEmbedding h‖^(-4:ℝ)/D^(-4:ℝ))=_
        ring
      _=_:=by rw [he]

theorem three_cusp_coefficients_weighted_summable :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖sourceResidualFourierCoefficient h‖*‖cuspFrequency h‖^(-4:ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖ramifiedBesselValue side h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_polynomial_bound
  constructor
  · exact coefficient_weighted_summable_of_polynomial _ C hC.le (fun h hh=>(hbound h hh).1)
  · intro side
    exact coefficient_weighted_summable_of_polynomial _ C hC.le (fun h hh=>(hbound h hh).2 side)

lemma derivative_coefficient_weighted_summable (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)‖*‖cuspFrequency h‖^(-5:ℝ)) := by
  apply (hF.mul_left ‖A‖).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖cuspFrequency h‖:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have hp:‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)=‖cuspFrequency h‖^(-4:ℝ):=by
      conv_lhs => lhs; rw [←Real.rpow_one ‖cuspFrequency h‖]
      rw [←Real.rpow_add hx]
      norm_num
    rw [norm_mul,norm_mul,norm_star]
    calc
      _=‖A‖*‖F h‖*(‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)):=by rw [hp];ring
      _=_:=by ring

theorem three_cusp_derivative_coefficients_weighted_summable (A:ℂ) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (sourceResidualFourierCoefficient h)‖*‖cuspFrequency h‖^(-5:ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (ramifiedBesselValue side h)‖*‖cuspFrequency h‖^(-5:ℝ)) :=
  ⟨derivative_coefficient_weighted_summable _ A three_cusp_coefficients_weighted_summable.1,
    fun side=>derivative_coefficient_weighted_summable _ A (three_cusp_coefficients_weighted_summable.2 side)⟩

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma radial_inverse_weight (x:ℝ) (hx:0<x) :
    (x^2)^(-(3/2):ℝ)/x^2=x^(-5:ℝ) := by
  calc
    _=(x^2)^(-(3/2):ℝ)*(x^2)^(-1:ℝ):=by rw [Real.rpow_neg_one];rfl
    _=(x^2)^(-(5/2):ℝ):=by
      rw [←Real.rpow_add (sq_pos_of_pos hx)]
      congr 1
      norm_num
    _=x^(-5:ℝ):=by
      rw [←Real.rpow_natCast_mul hx.le]
      congr 1
      norm_num

lemma radialCoefficient_weighted_summable_of_fourth (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:D^(-5:ℝ)≠0:=(Real.rpow_pos_of_pos hD _).ne'
  apply ((derivative_coefficient_weighted_summable F A hF).mul_left (D^(-5:ℝ))).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have hf:‖cuspFrequency h‖=‖eisEmbedding h‖/D:=by rw [cuspFrequency,norm_div]
    have hw:D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)=‖eisEmbedding h‖^(-5:ℝ):=by
      rw [Real.div_rpow hx.le hD.le]
      field_simp [hDp]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _=‖A*cuspFrequency h*star (F h)‖*(D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)):=by rw [hf];ring
      _=‖A*cuspFrequency h*star (F h)‖*‖eisEmbedding h‖^(-5:ℝ):=by rw [hw]
      _=_:=by rw [←radial_inverse_weight _ hx];ring

theorem three_cusp_radial_coefficients_weighted_summable (A:ℂ) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (sourceResidualFourierCoefficient h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (ramifiedBesselValue side h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) :=
  ⟨radialCoefficient_weighted_summable_of_fourth _ A three_cusp_coefficients_weighted_summable.1,
    fun side=>radialCoefficient_weighted_summable_of_fourth _ A (three_cusp_coefficients_weighted_summable.2 side)⟩

end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_weighted_summable (j:Fin 3) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖(sourceCuspCoefficients j).value h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  fin_cases j
  · exact three_cusp_coefficients_weighted_summable.1
  · exact three_cusp_coefficients_weighted_summable.2 false
  · exact three_cusp_coefficients_weighted_summable.2 true

theorem sourceCuspRadialCoefficient_weighted_summable (j:Fin 3) (z:ℂ) :
    Summable (fun h:Eis=>‖sourceCuspRadialCoefficient j z h‖*
      (sourceCuspRadialLength h)^(-(3/2):ℝ)) := by
  let A:ℂ:=(-2*Real.pi*Complex.I)/(sourceCuspScale j:ℂ)^2
  have hs:=radialCoefficient_weighted_summable_of_fourth (sourceCuspCoefficients j).value A
    (sourceCuspCoefficients_weighted_summable j)
  apply hs.congr
  intro h
  by_cases hh:h=0
  · subst h
    simp only [ite_true,sourceCuspRadialCoefficient_zero,norm_zero,zero_mul]
  · rw [ite_eq_right hh,sourceCuspRadialCoefficient_norm,sourceCuspRadialBaseCoefficient,
      sourceCuspRadialLength,ite_eq_right hh]
    congr 1
    apply congrArg norm
    dsimp only [A]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma SourceCuspDatum.cuspBarProfile_mellin_entire (d : SourceCuspDatum) :
    (∀s:ℂ,MellinConvergent (cuspBarProfile cubicSourceConjugateFunction d.point) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction d.point)) :=
  (conjugateSource_levelTwo_three_cusp_mellin_entire d.gamma d.index d.matrix rfl d.lower_ne_zero).1

lemma SourceCuspDatum.reflection_radial (d : SourceCuspDatum) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction d.point v=
      d.multiplier*((v:ℂ)^(-2:ℂ)*
        radialBesselProfile sourceCuspRadialLength
          (sourceCuspRadialCoefficient d.index d.dualPoint)
          (sourceCuspRadialScale d.index) ((d.heightScale*v)⁻¹)) := by
  rw [d.reflection v hv,sourceCuspZFamily_eq_radialBesselProfile _ _ _
    (inv_pos.mpr (mul_pos d.heightScale_pos hv)),Complex.cpow_neg,Complex.cpow_ofNat]
  ring

theorem completedBesselProfile_eq_finite_cuspProfiles
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h) (v:ℝ) (hv:0<v) :
    completedBesselProfile Ψ thetaBesselScale v=
      ∑h:Eis⧸Ideal.span {c},
        (thetaDerivativeScalar⁻¹*
          finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h)*
        cuspBarProfile cubicSourceConjugateFunction (d h).point v := by
  calc
    _=thetaDerivativeScalar⁻¹*thetaTwistedCuspProfile Ψ c hc v:=by
      rw [thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hperiod c hc hcQ v hv,
        ←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]
    _=_:=by
      simp only [thetaTwistedCuspProfile,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [hd h]
      ring

def SourceCuspDatum.smoothedKernel (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  (d.multiplier*(d.heightScale:ℂ)*
      ((thetaBesselScale/sourceCuspRadialScale d.index:ℝ):ℂ)^2)*
    ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
      CubicReflectionKernel.paperKernel (Vstar W)
        (27*thetaBesselScale^2*(sourceCuspRadialScale d.index)^2*X*
          sourceCuspRadialLength n/d.heightScale^2)

end

section
open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaBesselScale_square : thetaBesselScale^2=(1/27:ℝ) := by
  rw [thetaBesselScale_eq,div_pow,one_pow,Real.sq_sqrt (by norm_num)]

lemma sourceCuspRadialScale_ratio (j:Fin 3) :
    thetaBesselScale/sourceCuspRadialScale j=sourceCuspScale j := by
  rw [sourceCuspRadialScale]
  field_simp [thetaBesselScale_pos.ne']

lemma sourceCuspKernel_argument (j:Fin 3) (X r Q:ℝ) :
    27*thetaBesselScale^2*(sourceCuspRadialScale j)^2*X*r/Q^2=
      X*r/(27*(sourceCuspScale j)^2*Q^2) := by
  rw [sourceCuspRadialScale,div_pow,thetaBesselScale_square]
  ring

lemma SourceCuspDatum.smoothedKernel_eq (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength n/(27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  simp only [SourceCuspDatum.smoothedKernel,sourceCuspRadialScale_ratio,sourceCuspKernel_argument]

lemma SourceCuspDatum.smoothedKernel_prefactor_norm (d:SourceCuspDatum) :
    ‖d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2‖=
      (sourceCuspScale d.index)^2 := by
  rw [norm_mul,norm_mul,norm_pow,d.multiplier_norm,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos d.heightScale_pos,abs_of_pos (sourceCuspScale_pos _)]
  rw [inv_mul_cancel₀ d.heightScale_pos.ne',one_mul]

lemma SourceCuspDatum.smoothedKernel_prefactor_norm_le (d:SourceCuspDatum) :
    ‖d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2‖≤9 := by
  rw [d.smoothedKernel_prefactor_norm]
  rcases d with ⟨G,j,hj⟩
  fin_cases j <;> norm_num [sourceCuspScale]

end

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedT_finite_smoothed_reflection
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          (d h).smoothedKernel W X := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G:(Eis⧸Ideal.span {c})→ℝ→ℂ:=fun h=>
    cuspBarProfile cubicSourceConjugateFunction (d h).point
  let w:(Eis⧸Ideal.span {c})→ℂ:=fun h=>thetaDerivativeScalar⁻¹*
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h
  have hFG:∀v:ℝ,0<v→ completedBesselProfile Ψ thetaBesselScale v=∑h,w h*G h v:=
    completedBesselProfile_eq_finite_cuspProfiles Ψ Q hperiod c hc hcQ d hd
  have hG (h:Eis⧸Ideal.span {c}) : ∀s:ℂ,MellinConvergent (G h) s:=
    (d h).cuspBarProfile_mellin_entire.1
  have hF:=completedBesselProfile_mellin_entire_of_periodic Ψ Q hperiod c hc hcQ
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  let J:(Eis⧸Ideal.span {c})→ℝ→ℂ:=fun h t=>
    besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I)
  have hi (h:Eis⧸Ideal.span {c}) : Integrable (J h):=
    besselSmoothingIntegrand_reflected_integrable (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  have hireal (h:Eis⧸Ideal.span {c}) : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X (((-1:ℝ):ℂ)+t*Complex.I)):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,J] using hi h
  have hleft:=besselSmoothingIntegrand_finite_integrable
    (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X (-1)
    (fun h t=>hG h _) hireal
  have hshift:=completedT_mellin_shift Ψ hΨ thetaBesselScale thetaBesselScale_pos hF.1 hF.2
    W v0 v1 hv0 hWs hW X hX (-1) (by norm_num) hleft
  have hline (h:Eis⧸Ideal.span {c}) : (1/(2*Real.pi):ℂ)*(∫t:ℝ,J h t)=(d h).smoothedKernel W X:=by
    exact besselSmoothingIntegral_reflected_kernel (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ thetaBesselScale)
          thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hshift
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,∑h,w h*J h t:=by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact besselSmoothingIntegrand_finite_sum
        (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X _
        (fun h=>hG h _)
    _=∑h,w h*((1/(2*Real.pi):ℂ)*∫t:ℝ,J h t):=by
      rw [integral_finsetSum Finset.univ (fun h _=>(hi h).const_mul (w h)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_const_mul]
      ring
    _=∑h,w h*(d h).smoothedKernel W X:=by simp_rw [hline]
    _=_:=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only [w]
      ring

theorem completedT_canonical_smoothed_reflection
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          (finiteTwistCusp c hc h).smoothedKernel W X :=
  completedT_finite_smoothed_reflection Ψ hΨ Q hperiod c hc hcQ
    (finiteTwistCusp c hc) (finiteTwistCusp_point c hc) W v0 v1 hv0 hWs hW X hX

end

open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspReduction : SL(2,Eis) →* SL(2,Eis⧸Ideal.span {(3:Eis)}) :=
  Matrix.SpecialLinearGroup.map (n:=Fin 2) (Ideal.Quotient.mk (Ideal.span {(3:Eis)}))

abbrev FixedCuspSector := fixedCuspReduction.range

instance : Finite FixedCuspSector := by
  let : Finite (Eis⧸Ideal.span {(3:Eis)}) := finite_quotient_span (by norm_num : (3:Eis)≠0)
  infer_instance

def fixedCuspSector (M : SL(2,Eis)) : FixedCuspSector :=
  ⟨fixedCuspReduction M,⟨M,rfl⟩⟩

def fixedCuspRepresentative (s : FixedCuspSector) : SL(2,Eis) := s.property.choose

lemma fixedCuspRepresentative_reduction (s : FixedCuspSector) :
    fixedCuspReduction (fixedCuspRepresentative s)=s.val := s.property.choose_spec

lemma fixedCusp_difference_levelThree (M : SL(2,Eis)) :
    M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹∈levelThree := by
  change fixedCuspReduction (M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹)=1
  rw [map_mul,map_inv,fixedCuspRepresentative_reduction]
  change fixedCuspReduction M*(fixedCuspReduction M)⁻¹=1
  exact mul_inv_cancel _

theorem exists_fixed_cusp_decomposition :
    ∃(j:FixedCuspSector→Fin 3) (T:FixedCuspSector→SL(2,Eis))
      (G:SL(2,Eis)→levelTwo),
      (∀s,T s 1 0=0 ∧ IsUnit (T s 0 0) ∧ IsUnit (T s 1 1)) ∧
      ∀M:SL(2,Eis),M=(G M:SL(2,Eis))*cuspRepresentative (j (fixedCuspSector M))*
        T (fixedCuspSector M) := by
  have h (s:FixedCuspSector) := three_cusp_decomposition (fixedCuspRepresentative s)
  choose G0 j T hT hT0 hT1 he using h
  let D : SL(2,Eis)→levelTwo := fun M=>
    ⟨M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹,
      levelThree_le_levelTwo (fixedCusp_difference_levelThree M)⟩
  refine ⟨j,T,fun M=>D M*G0 (fixedCuspSector M),fun s=>⟨hT s,hT0 s,hT1 s⟩,?_⟩
  intro M
  change M=(M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹)*
    (G0 (fixedCuspSector M):SL(2,Eis))*cuspRepresentative (j (fixedCuspSector M))*T (fixedCuspSector M)
  rw [he (fixedCuspSector M)]
  group

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays -/

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_full_support (j:Fin 3) (h:Eis) (hh:h≠0)
    (hc:(sourceCuspCoefficients j).value h≠0) :
    ∃p:ThetaFullIndex,thetaFullFrequency p=h := by
  have hs : ∃u:Eisˣ,∃m:ℕ,∃I J:Ideal Eis,Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u:Eis)*ActualEisensteinCubic.lambda^m*primaryGenerator I*(primaryGenerator J)^3 := by
    fin_cases j
    · exact sourceResidualFourierCoefficient_full_squarefree_cube_support h hh hc
    · exact ramifiedBesselValue_squarefree_cube_support false h hh hc
    · exact ramifiedBesselValue_squarefree_cube_support true h hh hc
  obtain ⟨u,m,I,J,hI,hIg,hJg,he⟩:=hs
  exact ⟨(u,m,(⟨I,hI,hIg⟩,⟨J,hJg⟩)),he.symm⟩

lemma sourceCuspRadialCoefficient_full_support (j:Fin 3) (z:ℂ) (h:Eis)
    (hh:h≠0) (hc:sourceCuspRadialCoefficient j z h≠0) :
    ∃p:ThetaFullIndex,thetaFullFrequency p=h := by
  apply sourceCuspCoefficients_full_support j h hh
  intro hz
  apply hc
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,hz,
    star_zero,mul_zero,zero_div,zero_mul]

theorem sourceCuspRadialCoefficient_tsum_full_index (j:Fin 3) (z:ℂ) (w:Eis→ℂ) :
    (∑'h:Eis,w h*sourceCuspRadialCoefficient j z h)=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*
        sourceCuspRadialCoefficient j z (thetaFullFrequency p) := by
  have hs:Function.support (fun h:Eis=>w h*sourceCuspRadialCoefficient j z h)⊆
      {h:Eis|h≠0}:=by
    intro h hh hz
    subst h
    exact hh (by
      change w 0*sourceCuspRadialCoefficient j z 0=0
      rw [sourceCuspRadialCoefficient_zero,mul_zero])
  calc
    _=∑'h:{h:Eis//h≠0},w h.val*sourceCuspRadialCoefficient j z h.val:=
      (tsum_subtype_eq_of_support_subset hs).symm
    _=_:=thetaFullFrequency_tsum (sourceCuspRadialCoefficient j z) w
      (sourceCuspRadialCoefficient_full_support j z)

lemma SourceCuspDatum.smoothedKernel_full_index (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'p:ThetaFullIndex,sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength (thetaFullFrequency p)/
              (27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  rw [d.smoothedKernel_eq]
  congr 1
  have he:=sourceCuspRadialCoefficient_tsum_full_index d.index d.dualPoint
    (fun h=>CubicReflectionKernel.paperKernel (Vstar W)
      (X*sourceCuspRadialLength h/(27*(sourceCuspScale d.index)^2*d.heightScale^2)))
  simpa only [mul_comm] using he

lemma SourceCuspDatum.smoothedKernel_full_index_norm_summable
    (d:SourceCuspDatum) (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    Summable (fun p:ThetaFullIndex=>
      ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
        CubicReflectionKernel.paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/
            (27*(sourceCuspScale d.index)^2*d.heightScale^2))‖) := by
  have hs:=paperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient d.index d.dualPoint)
    (sourceCuspRadialCoefficient_weighted_summable _ _)
    (Vstar W) v0 v1 hv0 (Vstar_support W v0 v1 hWs) (Vstar_contDiff W v0 v1 hv0 hWs hW)
    (X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))
    (by have := sourceCuspScale_pos d.index; have := d.heightScale_pos; positivity)
  have hp:=hs.comp_injective thetaFullFrequency_injective
  apply hp.congr
  intro p
  exact congrArg (fun y:ℝ=>‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
    CubicReflectionKernel.paperKernel (Vstar W) y‖)
    (by ring :
      X/(27*(sourceCuspScale d.index)^2*d.heightScale^2)*sourceCuspRadialLength (thetaFullFrequency p)=
        X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale d.index)^2*d.heightScale^2))

theorem completedT_finite_smoothed_full_index
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          ((d h).multiplier*((d h).heightScale:ℂ)*(sourceCuspScale (d h).index:ℂ)^2)*
        ∑'p:ThetaFullIndex,sourceCuspRadialCoefficient (d h).index (d h).dualPoint (thetaFullFrequency p)*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength (thetaFullFrequency p)/
              (27*(sourceCuspScale (d h).index)^2*(d h).heightScale^2)) := by
  rw [completedT_finite_smoothed_reflection Ψ hΨ Q hperiod c hc hcQ d hd W v0 v1 hv0 hWs hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [(d h).smoothedKernel_full_index]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspCoefficientBound : ℝ :=
  Classical.choose three_cusp_coefficients_squarefree_cube_bound

lemma fixedCuspCoefficientBound_pos : 0<fixedCuspCoefficientBound :=
  (Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).1

def fixedCuspArrayIndex (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  (u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3

def fixedCuspArrayEligible (I J:Ideal Eis) : Prop :=
  Squarefree I ∧ primaryGenerator I≠0 ∧ primaryGenerator J≠0

def fixedCuspArrayWeight (m:ℕ) (J:Ideal Eis) : ℝ :=
  (3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ)

lemma fixedCuspArrayWeight_nonneg (m:ℕ) (J:Ideal Eis) :
    0≤fixedCuspArrayWeight m J := by
  unfold fixedCuspArrayWeight
  positivity

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))

lemma sourceCuspCoefficients_squarefree_cube_bound (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J) :
    ‖(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)‖≤
      fixedCuspCoefficientBound*fixedCuspArrayWeight m J := by
  rcases helig with ⟨hsq,hI,hJ⟩
  have hb:=(Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).2
    I J hI hJ hsq u m
  rw [primaryGenerator_norm J hJ] at hb
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.1
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 false
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 true

def fixedCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  if fixedCuspArrayEligible I J then
    (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J) /
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)
  else 0

lemma fixedCuspArray_zero_of_ineligible (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:¬fixedCuspArrayEligible I J) : fixedCuspArray j u m I J=0 := by
  simp only [fixedCuspArray,ite_eq_right h]

lemma fixedCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedCuspArray j u m I J‖≤1 := by
  by_cases h:fixedCuspArrayEligible I J
  · have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
    rw [fixedCuspArray,ite_eq_left h,norm_div,Complex.norm_real,Real.norm_of_nonneg hpos.le]
    exact (div_le_one hpos).mpr (sourceCuspCoefficients_squarefree_cube_bound j u m I J h)
  · simp only [fixedCuspArray,ite_eq_right h,norm_zero,zero_le_one]

lemma fixedCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedCuspArray j u m I J := by
  have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
  rw [fixedCuspArray,ite_eq_left h,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

def fixedConjugateCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  star (fixedCuspArray j u m I J)

lemma fixedConjugateCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedConjugateCuspArray j u m I J‖≤1 := by
  simpa only [fixedConjugateCuspArray,norm_star] using fixedCuspArray_norm_le_one j u m I J

lemma fixedConjugateCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star ((sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J))=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedConjugateCuspArray j u m I J := by
  rw [fixedCuspArray_reconstruct j u m I J h,star_mul]
  simp only [fixedConjugateCuspArray,Complex.star_def,Complex.conj_ofReal]
  ring

lemma fixedConjugateCuspArray_reconstruct_explicit (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (hsq:Squarefree I) (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    star ((sourceCuspCoefficients j).value
      ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3))=
      ((fixedCuspCoefficientBound*(3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ):ℝ):ℂ)*
        fixedConjugateCuspArray j u m I J := by
  simpa only [fixedCuspArrayIndex,fixedCuspArrayWeight,mul_assoc] using
    fixedConjugateCuspArray_reconstruct j u m I J ⟨hsq,hI,hJ⟩

end CubicEisenstein

section
open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace IdealGaussCRT
open CubicEisenstein

theorem finiteAdditiveFourierCoeff_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (φ : ∀i,R i→ℂ) (h : T) :
    finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h=
      ∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (e h i) := by
  have hsum : (∑x:T,(∏i,φ i (e x i))*ψ (-h*x))=
      ∏i,∑x:R i,φ i x*coordinateAddChar R e ψ i (-(e h i)*x) := by
    calc
      _ = ∑x:T,∏i,φ i (e x i)*coordinateAddChar R e ψ i (-(e h i)*e x i) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [addChar_finite_crt_factor R e ψ (-h*x)]
        simp only [map_mul,map_neg,Pi.mul_apply,Pi.neg_apply,Finset.prod_mul_distrib]
      _ = ∑x:(∀i,R i),∏i,φ i (x i)*coordinateAddChar R e ψ i (-(e h i)*x i) :=
        Equiv.sum_comp e.toEquiv (fun x:∀i,R i=>∏i,φ i (x i)*coordinateAddChar R e ψ i (-(e h i)*x i))
      _ = _ := (Fintype.prod_sum (fun i (x:R i)=>φ i x*coordinateAddChar R e ψ i (-(e h i)*x))).symm
  have hcard : (Fintype.card T:ℂ)=∏i,(Fintype.card (R i):ℂ) := by
    rw [Fintype.card_congr e.toEquiv,Fintype.card_pi,Nat.cast_prod]
  simp only [finiteAdditiveFourierCoeff,hsum,hcard,Finset.prod_div_distrib]

theorem finite_fourier_weighted_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (φ κ : ∀i,R i→ℂ) :
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h *
      ∏i,κ i (e h i))=
      ∏i,∑h:R i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) h*κ i h := by
  simp only [finiteAdditiveFourierCoeff_crt,←Finset.prod_mul_distrib]
  calc
    _ = ∑h:∀i,R i,∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (h i)*κ i (h i) :=
      Equiv.sum_comp e.toEquiv
        (fun h:∀i,R i=>∏i,finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) (h i)*κ i (h i))
    _ = _ := (Fintype.prod_sum (fun i (h:R i)=>
      finiteAdditiveFourierCoeff (coordinateAddChar R e ψ i) (φ i) h*κ i h)).symm

end IdealGaussCRT

namespace LocalReflectionBrackets

section
open CubicEisenstein
variable {F : Type*} [Field F] [Fintype F]

def frequencyMultiplier (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  if h=0 then 1 else (((χ⁻¹)^2) ((σ:F)*h))*ψ (((ε:F)*x)*h⁻¹)

def frequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ (fun t=>(χ^j) t) h*frequencyMultiplier χ ψ σ ε x h

lemma frequencyRow_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) :
    frequencyRow χ ψ j σ ε x 0=zeroFourierCoefficient χ j := by
  simp only [frequencyRow,frequencyMultiplier,finiteAdditiveFourierCoeff,
    zeroFourierCoefficient,ite_true,neg_zero,zero_mul,AddChar.map_zero_eq_one,
    mul_one,div_eq_mul_inv]
  ring

lemma frequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) :
    (∑h:Fˣ,frequencyRow χ ψ j σ ε x h)=activeRow χ ψ j σ ε x := by
  unfold frequencyRow finiteAdditiveFourierCoeff frequencyMultiplier activeRow
  simp only [Units.ne_zero,ite_false,Units.val_inv_eq_inv_val,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  ring_nf

open ActualEisensteinCubic CompletedGauss
noncomputable local instance quotientFieldFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _

theorem canonical_frequencyRow_zero (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hgood : lambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (ψ : AddChar (ActualEisensteinCubic.O⧸P) ℂ)
    (j : ℕ) (hj : j<6) (σ ε : (ActualEisensteinCubic.O⧸P)ˣ) (x : ActualEisensteinCubic.O⧸P) :
    frequencyRow (actualSextic P hgood) ψ j σ ε x 0=
      if j=0 then 1-(Fintype.card (ActualEisensteinCubic.O⧸P):ℂ)⁻¹ else 0 := by
  rw [frequencyRow_zero]
  simpa only [actualSextic] using canonical_zeroFourierCoefficient P hgood hchar j hj

theorem canonical_frequencyRow_units (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hgood : lambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (ψ : AddChar (ActualEisensteinCubic.O⧸P) ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : j<6) (σ ε : (ActualEisensteinCubic.O⧸P)ˣ) (x : ActualEisensteinCubic.O⧸P) :
    (∑h:(ActualEisensteinCubic.O⧸P)ˣ,frequencyRow (actualSextic P hgood) ψ j σ ε x h)=
      (((actualSextic P hgood)⁻¹)^2) σ *
        phase (actualSextic P hgood) ψ j ε*bracket (actualSextic P hgood) j x := by
  rw [frequencyRow_units]
  simpa only [actualSextic] using canonical_A5_normalized P hgood hchar ψ hψ j hj σ ε x

end

open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance quotientFintypeCrt (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_finite_reflection_crt {ι T : Type*} [Fintype ι]
    [CommRing T] [Fintype T]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e : T≃+*∀i,Eis⧸P i) (ψ : AddChar T ℂ) (hψ : ψ.IsPrimitive)
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i) :
    let χ := fun i=>actualSextic (P i) (hg i)
    let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let (i : ι) : Field (Eis⧸P i) := Ideal.Quotient.field (P i)
  let χ := fun i=>actualSextic (P i) (hg i)
  let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
  let f := fun i=>frequencyRow (χ i) (ψi i) (j i) (σ i) (ε i) (x i)
  have hsum : (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑h:∀i,Eis⧸P i,∏i,f i (h i) := by
    simp only [finiteAdditiveFourierCoeff_crt,←Finset.prod_mul_distrib]
    exact Equiv.sum_comp e.toEquiv (fun h:∀i,Eis⧸P i=>∏i,f i (h i))
  have hactive (i : ι) : (∑h:(Eis⧸P i)ˣ,f i h)=
      (((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i) := by
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψi i)
      (coordinateAddChar_isPrimitive (fun i=>Eis⧸P i) e ψ hψ i) (j i) (hj i) (σ i) (ε i) (x i)
  have hzero (i : ι) : f i 0=if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0 := by
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψi i) (j i) (hj i) (σ i) (ε i) (x i)
  change (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=_
  rw [hsum,FixedRayActiveSet.product_sum_by_active_set (fun i=>Eis⧸P i) f]
  simp only [hactive,hzero]
  rfl

theorem canonical_principal_reflection_crt {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i)
    (c : Eis) (hc : c≠0) (hcP : Ideal.span {c}=∏i,P i)
    [Fintype (Eis⧸Ideal.span {c})] :
    let e := (Ideal.quotEquivOfEq hcP).trans (quotientProdEquivPi P hcop)
    let ψ := quotientTrace c hc
    let χ := fun i=>actualSextic (P i) (hg i)
    let ψi := coordinateAddChar (fun i=>Eis⧸P i) e ψ
    (∑h:Eis⧸Ideal.span {c},finiteAdditiveFourierCoeff ψ (principalSexticRow P hcop hg j c hcP) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) (e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let e := (Ideal.quotEquivOfEq hcP).trans (quotientProdEquivPi P hcop)
  have hψ : (quotientTrace c hc).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  have hrow : principalSexticRow P hcop hg j c hcP=
      fun t=>∏i,(actualSextic (P i) (hg i)^j i) (e t i) := by
    funext t
    rfl
  dsimp only
  rw [hrow]
  exact canonical_finite_reflection_crt P e (quotientTrace c hc) hψ hg hchar j hj σ ε x

end LocalReflectionBrackets
end

namespace CubicEisenstein
open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_right_removed_bottom (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 1 0=M 1 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_top (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 0 0=M 0 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_last (M T:SL(2,Eis)) :
    (M*T⁻¹) 1 1= -M 1 0*T 0 1+M 1 1*T 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

lemma upper_diagonal_product (T:SL(2,Eis)) (hT:T 1 0=0) : T 0 0*T 1 1=1 := by
  have hd:=T.property
  simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd

structure FixedCuspShape (H:SL(2,Eis)) where
  gamma : levelTwo
  index : Fin 3
  upper : SL(2,Eis)
  lower_zero : upper 1 0=0
  upper_unit : IsUnit (upper 0 0)
  lower_unit : IsUnit (upper 1 1)
  factorization : H=(gamma:SL(2,Eis))*cuspRepresentative index*upper

lemma exists_fixedCuspShape (H:SL(2,Eis)) : Nonempty (FixedCuspShape H) := by
  obtain ⟨G,j,T,hT,hT0,hT1,he⟩:=three_cusp_decomposition H
  exact ⟨⟨G,j,T,hT,hT0,hT1,he⟩⟩

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H) (g:levelTwo)

lemma removed_eq : (g:SL(2,Eis))*H*s.upper⁻¹=
    ((g*s.gamma:levelTwo):SL(2,Eis))*cuspRepresentative s.index := by
  calc
    _ = (g:SL(2,Eis))*((s.gamma:SL(2,Eis))*cuspRepresentative s.index*s.upper)*s.upper⁻¹ :=
      congrArg (fun K:SL(2,Eis)=>(g:SL(2,Eis))*K*s.upper⁻¹) s.factorization
    _ = _ := by simp only [Subgroup.coe_mul]; group

def datum (h:((g:SL(2,Eis))*H) 1 0≠0) : SourceCuspDatum where
  gamma := g*s.gamma
  index := s.index
  lower_ne_zero := by
    rw [←map_mul,←s.removed_eq g,integralComplexMatrix_apply,
      upper_right_removed_bottom _ _ s.lower_zero,map_mul]
    exact mul_ne_zero (eisEmbedding_ne_zero h) (eisEmbedding_ne_zero s.lower_unit.ne_zero)

lemma datum_matrix (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).matrix=integralComplexMatrix ((g:SL(2,Eis))*H*s.upper⁻¹) := by
  rw [s.removed_eq g,map_mul]
  rfl

lemma datum_point (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).point=
      eisEmbedding (((g:SL(2,Eis))*H) 0 0)/eisEmbedding (((g:SL(2,Eis))*H) 1 0) := by
  rw [SourceCuspDatum.point,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,
    upper_right_removed_top _ _ s.lower_zero,upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_mul]
  exact mul_div_mul_right _ _ (eisEmbedding_ne_zero s.lower_unit.ne_zero)

lemma datum_heightScale (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).heightScale=‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2 := by
  rw [SourceCuspDatum.heightScale,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul,norm_mul]
  have hn:‖eisEmbedding (s.upper 1 1)‖=1 := by
    rcases s.lower_unit with ⟨u,hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hn,mul_one]

lemma datum_dualPoint (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).dualPoint=
      eisEmbedding (s.upper 0 0*s.upper 0 1)-
        eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0)) := by
  rw [SourceCuspDatum.dualPoint,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,upper_right_removed_last,
    upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_add,map_neg,map_mul]
  have hd:eisEmbedding (s.upper 0 0)*eisEmbedding (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hc:=eisEmbedding_ne_zero h
  have ht:=eisEmbedding_ne_zero s.lower_unit.ne_zero
  field_simp [hc,ht]
  linear_combination (eisEmbedding (s.upper 0 0)*eisEmbedding (((g:SL(2,Eis))*H) 1 1)-
    eisEmbedding (((g:SL(2,Eis))*H) 1 0)*eisEmbedding (s.upper 0 1))*hd

lemma datum_multiplier (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).multiplier=
      -star (levelTwoComplexCharacter g)*star (levelTwoComplexCharacter s.gamma)*
        eisEmbedding (s.upper 0 0)^2/eisEmbedding (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [SourceCuspDatum.multiplier,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul]
  change -star (levelTwoComplexCharacter (g*s.gamma))/
    (eisEmbedding (((g:SL(2,Eis))*H) 1 0)*eisEmbedding (s.upper 1 1))^2=_
  rw [map_mul,star_mul]
  have hc:=eisEmbedding_ne_zero h
  have ht:=eisEmbedding_ne_zero s.lower_unit.ne_zero
  have hd:eisEmbedding (s.upper 0 0)*eisEmbedding (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hp:eisEmbedding (s.upper 0 0)^2*eisEmbedding (s.upper 1 1)^2=1 := by
    rw [←mul_pow,hd,one_pow]
  field_simp [hc,ht]
  linear_combination (star (levelTwoComplexCharacter g)*star (levelTwoComplexCharacter s.gamma))*hp

lemma datum_additive_phase (h:((g:SL(2,Eis))*H) 1 0≠0) (freq:ℂ) (scale:ℂ) :
    ShortDraftTrace.breveE (-freq*(s.datum g h).dualPoint/scale)=
      ShortDraftTrace.breveE (-freq*eisEmbedding (s.upper 0 0*s.upper 0 1)/scale)*
      ShortDraftTrace.breveE (freq*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0))/scale) := by
  rw [s.datum_dualPoint]
  rw [show -freq*(eisEmbedding (s.upper 0 0*s.upper 0 1)-
      eisEmbedding (s.upper 0 0)^2*(eisEmbedding (((g:SL(2,Eis))*H) 1 1)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)))/scale=
    -freq*eisEmbedding (s.upper 0 0*s.upper 0 1)/scale+
      freq*eisEmbedding (s.upper 0 0)^2*eisEmbedding (((g:SL(2,Eis))*H) 1 1)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)/scale by ring]
  simp only [AddChar.map_add_eq_mul,mul_div_assoc]

end FixedCuspShape
end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

namespace ReflectedBranchData

def withFixedCuspArray {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (fixedConjugateCuspArray cusp u)
    (fun m n b=>fixedConjugateCuspArray_norm_le_one cusp u m n.val b.val) rowPhase hrow

lemma withFixedCuspArray_amplitude {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    (d.withFixedCuspArray cusp u rowPhase hrow).amplitude i n b=
      fixedConjugateCuspArray cusp u i.1 n b := rfl

theorem withFixedCuspArray_value {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withFixedCuspArray cusp u rowPhase hrow).value W X ρ q k=
      d.rawValue (fixedConjugateCuspArray cusp u) rowPhase W X ρ q k :=
  d.withCanonicalCuspArray_value (fixedConjugateCuspArray cusp u)
    (fun m n b=>fixedConjugateCuspArray_norm_le_one cusp u m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

def extractedFixedCuspArray {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedConjugateCuspArray cusp u m
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1*n)
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2*b)

lemma extractedFixedCuspArray_norm_le_one {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (m:ℕ) (n b:Ideal Eis) : ‖d.extractedFixedCuspArray cusp u m n b‖≤1 :=
  fixedConjugateCuspArray_norm_le_one cusp u m _ _

lemma extractedFixedCuspArray_zero {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 1*n)
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 2*b)) :
    d.extractedFixedCuspArray cusp u m n b=0 := by
  simp only [extractedFixedCuspArray,fixedConjugateCuspArray,
    fixedCuspArray_zero_of_ineligible _ _ _ _ _ h,star_zero]

def withExtractedFixedCuspArray {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (d.extractedFixedCuspArray cusp u)
    (fun m n b=>d.extractedFixedCuspArray_norm_le_one cusp u m n.val b.val) rowPhase hrow

lemma withExtractedFixedCuspArray_amplitude {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    (d.withExtractedFixedCuspArray cusp u rowPhase hrow).amplitude i n b=
      d.extractedFixedCuspArray cusp u i.1 n b := rfl

theorem withExtractedFixedCuspArray_value {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withExtractedFixedCuspArray cusp u rowPhase hrow).value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArray cusp u) rowPhase W X ρ q k :=
  d.withCanonicalCuspArray_value (d.extractedFixedCuspArray cusp u)
    (fun m n b=>d.extractedFixedCuspArray_norm_le_one cusp u m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end ReflectedBranchData
end CompletedGauss

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Cusp.WeylRepresentatives -/

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

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def A3WeylCusp (u : Eis) : SL(2,Eis) :=
  ⟨!![u,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma A3_ramified_relative_matrix (M : SL(2,Eis)) (u : Eis) :
    ((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) =
      !![M 0 0-u*M 0 1,M 0 1;M 1 0-u*M 1 1,M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerCuspMatrix,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma A3_unramified_relative_matrix (M : SL(2,Eis)) (u : Eis) :
    ((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) =
      !![-M 0 1,M 0 0+u*M 0 1;-M 1 1,M 1 0+u*M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A3WeylCusp,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma A3_principal_mem_levelThree (M : SL(2,Eis))
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0) (hd : (3:Eis)∣M 1 1-1) : M∈levelThree := by
  apply (mem_levelThree_iff_entries M).mpr
  intro i j
  fin_cases i <;> fin_cases j <;> simpa using (by assumption)

lemma A3_ramified_mem_levelThree (M : SL(2,Eis)) (u : Eis)
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0-u) (hd : (3:Eis)∣M 1 1-1) :
    M*(lowerCuspMatrix u)⁻¹∈levelThree := by
  apply (mem_levelThree_iff_entries _).mpr
  intro i j
  rw [A3_ramified_relative_matrix]
  fin_cases i <;> fin_cases j
  · convert dvd_sub ha (dvd_mul_of_dvd_right hb u) using 1 ; simp ; ring
  · simpa using hb
  · convert dvd_sub hc (dvd_mul_of_dvd_right hd u) using 1 ; simp ; ring
  · simpa using hd

lemma A3_unramified_mem_levelThree (M : SL(2,Eis)) (u : Eis)
    (ha : (3:Eis)∣M 0 0-u) (hb : (3:Eis)∣M 0 1+1)
    (hc : (3:Eis)∣M 1 0-1) (hd : (3:Eis)∣M 1 1) :
    M*(A3WeylCusp u)⁻¹∈levelThree := by
  apply (mem_levelThree_iff_entries _).mpr
  intro i j
  rw [A3_unramified_relative_matrix]
  fin_cases i <;> fin_cases j
  · convert dvd_neg.mpr hb using 1 ; simp ; ring
  · convert dvd_add ha (dvd_mul_of_dvd_right hb u) using 1 ; simp ; ring
  · simpa using dvd_neg.mpr hd
  · convert dvd_add hc (dvd_mul_of_dvd_right hd u) using 1 ; simp ; ring

end

open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_principal_character (M : SL(2,Eis)) (hM : M∈levelThree)
    (c0 r : Eis) (hC : M 1 0=c0*r) (hr : lambda^2∣r-1) :
    complexCharacter ⟨M,hM⟩ =
      eisEmbedding (symbol c0 (M 0 0))*eisEmbedding (symbol (M 0 0) r) := by
  change eisEmbedding (symbol (M 1 0) (M 0 0))=_
  rw [hC,A3_principal_global _ _ _ (levelThree_primary ⟨M,hM⟩) hr,map_mul]

lemma A3_ramified_literal_character (M : SL(2,Eis)) (u : Eis)
    (hM : M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hM⟩ =
      eisEmbedding (symbol (M 1 0-u*M 1 1) (M 0 0-u*M 0 1)) := by
  change eisEmbedding (symbol
    (((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 1 0)
    (((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 0 0))=_
  rw [A3_ramified_relative_matrix]
  rfl

lemma A3_unramified_literal_character (M : SL(2,Eis)) (u : Eis)
    (hM : M*(A3WeylCusp u)⁻¹∈levelThree) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hM⟩ =
      eisEmbedding (symbol (-M 1 1) (-M 0 1)) := by
  change eisEmbedding (symbol
    (((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 1 0)
    (((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 0 0))=_
  rw [A3_unramified_relative_matrix]
  rfl

theorem A3_ramified_character (M : SL(2,Eis)) (u c0 r : Eis)
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0-u) (hd : (3:Eis)∣M 1 1-1)
    (hC : M 1 0=u*(c0*r)) (hr : lambda^2∣r-1) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,
      A3_ramified_mem_levelThree M u ha hb hc hd⟩ =
      eisEmbedding (symbol (-u) (M 0 0-u*M 0 1)*symbol c0 (M 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  have hA : lambda^2∣(M 0 0-u*M 0 1)-1 := by
    apply lambda_sq_dvd_three.trans
    convert dvd_sub ha (dvd_mul_of_dvd_right hb u) using 1 ; ring
  have hdet : M 0 0*M 1 1-M 0 1*(u*(c0*r))=1 := by
    rw [←hC]
    simpa only [Matrix.det_fin_two] using M.property
  rw [A3_ramified_literal_character,hC,
    A3_ramified_global_factor _ _ _ _ _ _ hdet
      (lambda_sq_dvd_three.trans ha) hA hr,map_mul]

theorem A3_unramified_character (M : SL(2,Eis)) (u c0 r : Eis)
    (ha : (3:Eis)∣M 0 0-u) (hb : (3:Eis)∣M 0 1+1)
    (hc : (3:Eis)∣M 1 0-1) (hd : (3:Eis)∣M 1 1)
    (hC : M 1 0=c0*r) (h9 : (9:Eis)∣M 0 0*M 1 1) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,
      A3_unramified_mem_levelThree M u ha hb hc hd⟩ =
      eisEmbedding (symbol (M 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  have hb' : lambda^2∣(-M 0 1)-1 := by
    apply lambda_sq_dvd_three.trans
    convert dvd_neg.mpr hb using 1 ; ring
  have hc' : lambda^2∣c0*r-1 := by
    rw [←hC]
    exact lambda_sq_dvd_three.trans hc
  have hdet : M 0 0*M 1 1-M 0 1*(c0*r)=1 := by
    rw [←hC]
    simpa only [Matrix.det_fin_two] using M.property
  rw [A3_unramified_literal_character,
    A3_unramified_global_factor _ _ _ _ _ hdet hb' hc' h9,map_mul]

end ShortDraftCusp

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspArrayIndex_ne_zero (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayIndex u m I J≠0 :=
  mul_ne_zero (mul_ne_zero (ramifiedElement_ne_zero u m) hI) (pow_ne_zero _ hJ)

lemma fixedCuspArrayIndex_norm_sq (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    ‖eisEmbedding (fixedCuspArrayIndex u m I J)‖^2=
      (3:ℝ)^m*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hr:‖eisEmbedding (u.val*lambda^m)‖^2=(3:ℝ)^m := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ramifiedElement_absNorm,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _=‖eisEmbedding (u.val*lambda^m)‖^2*‖eisEmbedding (primaryGenerator I)‖^2*
      (‖eisEmbedding (primaryGenerator J)‖^2)^3 := by
        simp only [fixedCuspArrayIndex,map_mul,map_pow,norm_mul,norm_pow]
        ring
    _=_ := by rw [hr,primaryGenerator_norm_sq I hI,primaryGenerator_norm_sq J hJ]

lemma fixedCuspArrayIndex_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    ‖eisEmbedding (fixedCuspArrayIndex u m I J)‖=
      Real.sqrt ((3:ℝ)^m*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3) := by
  rw [←fixedCuspArrayIndex_norm_sq u m I J hI hJ,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

lemma fixedCuspArrayWeight_div_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayWeight m J/‖eisEmbedding (fixedCuspArrayIndex u m I J)‖=
      1/((3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hn:0<(Ideal.absNorm I:ℝ) := by
    rw [←primaryGenerator_norm_sq I hI]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hI))
  have hb:0<(Ideal.absNorm J:ℝ) := by
    rw [←primaryGenerator_norm_sq J hJ]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))
  rw [fixedCuspArrayWeight,fixedCuspArrayIndex_norm u m I J hI hJ]
  simpa only [Real.rpow_natCast] using cusp_coefficient_normalization (m:ℝ)
    (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) hn hb

theorem fixedConjugateCuspArray_div_norm (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star ((sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J))/
      (‖eisEmbedding (fixedCuspArrayIndex u m I J)‖:ℂ)=
    (fixedCuspCoefficientBound:ℂ)*fixedConjugateCuspArray j u m I J/
      (((3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [fixedConjugateCuspArray_reconstruct j u m I J h]
  calc
    _=(fixedCuspCoefficientBound:ℂ)*fixedConjugateCuspArray j u m I J*
      ((fixedCuspArrayWeight m J/‖eisEmbedding (fixedCuspArrayIndex u m I J)‖:ℝ):ℂ) := by
        push_cast
        ring
    _=_ := by
      rw [fixedCuspArrayWeight_div_norm u m I J h.2.1 h.2.2]
      push_cast
      ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFullFrequency_eq_fixedCuspArrayIndex (p:ThetaFullIndex) :
    thetaFullFrequency p=fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val := rfl

lemma sourceCuspRadialLength_full_index (p:ThetaFullIndex) :
    sourceCuspRadialLength (thetaFullFrequency p)=
      (3:ℝ)^p.2.1*(Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3 := by
  rw [sourceCuspRadialLength,ite_eq_right (thetaFullFrequency_ne_zero p),thetaFullFrequency_eq_fixedCuspArrayIndex]
  exact fixedCuspArrayIndex_norm_sq p.1 p.2.1 p.2.2.1.val p.2.2.2.val
    p.2.2.1.property.2 p.2.2.2.property

lemma thetaRamifiedScale_eq (m:ℕ) :
    ramifiedScale 1 completedRamifiedStep m=(3:ℝ)^((m:ℝ)/3) := by
  unfold ramifiedScale completedRamifiedStep
  rw [one_mul,←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma thetaRamifiedScale_cube (m:ℕ) :
    (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  rw [thetaRamifiedScale_eq,←Real.rpow_mul_natCast (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  rw [show ((m:ℝ)/3)*(3:ℝ)=m by ring,Real.rpow_natCast]

lemma sourceCusp_full_index_kernel_argument (p:ThetaFullIndex) (j:Fin 3) (Q X:ℝ) :
    X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2)=
      (X/(27*(sourceCuspScale j)^2*Q^2))*(ramifiedScale 1 completedRamifiedStep p.2.1)^3*
        (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3 := by
  rw [sourceCuspRadialLength_full_index,thetaRamifiedScale_cube]
  ring

def sourceFrequencyAngle (h:Eis) : ℂ := eisEmbedding h/(‖eisEmbedding h‖:ℂ)

lemma sourceFrequencyAngle_norm (h:Eis) (hh:h≠0) : ‖sourceFrequencyAngle h‖=1 := by
  rw [sourceFrequencyAngle,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))

lemma sourceCuspRadialCoefficient_angle (j:Fin 3) (z:ℂ) (h:Eis) (hh:h≠0) :
    sourceCuspRadialCoefficient j z h=
      ((-2*Real.pi*Complex.I*thetaFrequencyScale)/(sourceCuspScale j:ℂ)^2)*
        sourceFrequencyAngle h*
        (star ((sourceCuspCoefficients j).value h)/(‖eisEmbedding h‖:ℂ))*
        ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ))) := by
  have hn:(‖eisEmbedding h‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))
  have hs:(sourceCuspScale j:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
  rw [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,sourceCuspRadialLength,ite_eq_right hh]
  rw [cuspFrequency_eq_thetaFrequencyScale]
  unfold sourceFrequencyAngle
  push_cast
  field_simp [hn,hs]

def fixedRadialCoefficientScalar : ℂ :=
  (-2*Real.pi*Complex.I)*thetaFrequencyScale*(fixedCuspCoefficientBound:ℂ)

theorem sourceCuspRadialCoefficient_fixed_array
    (j:Fin 3) (z:ℂ) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) (h:fixedCuspArrayEligible I J) :
    sourceCuspRadialCoefficient j z (fixedCuspArrayIndex u m I J)=
      (fixedRadialCoefficientScalar/(sourceCuspScale j:ℂ)^2)*
        (fixedConjugateCuspArray j u m I J*
          sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
          ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
            (z/(sourceCuspScale j:ℂ))))/
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm I:ℝ)*
          (Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [sourceCuspRadialCoefficient_angle _ _ _
    (fixedCuspArrayIndex_ne_zero u m I J h.2.1 h.2.2),
    fixedConjugateCuspArray_div_norm j u m I J h,thetaRamifiedScale_eq]
  unfold fixedRadialCoefficientScalar
  push_cast
  ring

end

open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFullIndex_denominator_pos (p:ThetaFullIndex) :
    0< ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ) := by
  have hI:0<(Ideal.absNorm p.2.2.1.val:ℝ):=by
    rw [←primaryGenerator_norm_sq _ p.2.2.1.property.2]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero p.2.2.1.property.2))
  have hJ:0<(Ideal.absNorm p.2.2.2.val:ℝ):=by
    rw [←primaryGenerator_norm_sq _ p.2.2.2.property]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero p.2.2.2.property))
  rw [thetaRamifiedScale_eq]
  positivity

lemma SourceCuspDatum.smoothed_unit_phase_norm (d:SourceCuspDatum) :
    ‖d.multiplier*(d.heightScale:ℂ)‖=1 := by
  rw [norm_mul,d.multiplier_norm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos d.heightScale_pos,inv_mul_cancel₀ d.heightScale_pos.ne']

theorem SourceCuspDatum.smoothedFullCoefficient_normalization (d:SourceCuspDatum) (p:ThetaFullIndex) :
    (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)=
    (fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      (fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        sourceFrequencyAngle (thetaFullFrequency p)*
        ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
          (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
      ((ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ) := by
  have hs:(sourceCuspScale d.index:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos _).ne'
  have hn:((ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (thetaFullIndex_denominator_pos p).ne'
  simp only [thetaFullFrequency_eq_fixedCuspArrayIndex]
  rw [sourceCuspRadialCoefficient_fixed_array _ _ _ _ _ _
    ⟨p.2.2.1.property.1,p.2.2.1.property.2,p.2.2.2.property⟩]
  field_simp [hs,hn]

lemma SourceCuspDatum.smoothedFullCoefficient_norm_le (d:SourceCuspDatum) (p:ThetaFullIndex) :
    ‖(d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖≤
    ‖fixedRadialCoefficientScalar‖/
      (ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)) := by
  have ha:‖fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency p)*
      ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
        (d.dualPoint/(sourceCuspScale d.index:ℂ)))‖≤1:=by
    rw [norm_mul,norm_mul,sourceFrequencyAngle_norm _ (thetaFullFrequency_ne_zero p),breveE_norm,mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  rw [d.smoothedFullCoefficient_normalization,norm_div,norm_mul,norm_mul,
    d.smoothed_unit_phase_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg (thetaFullIndex_denominator_pos p).le]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg _) ha) (thetaFullIndex_denominator_pos p).le

theorem SourceCuspDatum.smoothedKernel_fixed_array (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=(fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          sourceFrequencyAngle (thetaFullFrequency p)*
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3) := by
  rw [d.smoothedKernel_full_index,←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [←mul_assoc,d.smoothedFullCoefficient_normalization,sourceCusp_full_index_kernel_argument]
  ring

end CubicEisenstein

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticAllOddCRT
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem idealRowHom_congr_mod (I:Ideal Eis) (x y:Eis) (hxy:x-y∈I) :
    idealRowHom x I=idealRowHom y I := by
  by_cases hI:I=0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _)=(if I=0 then 0 else _)
  rw [ite_eq_right hI,ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hle:I≤P:=((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  unfold localRowValue
  split_ifs with hp
  · let:P.IsMaximal:=hp.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl

lemma sexticReciprocityPhase_congr_right (a x y:Eis) (hxy:(4:Eis)∣x-y) :
    sexticReciprocityPhase a x=sexticReciprocityPhase a y := by
  unfold sexticReciprocityPhase
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y hxy]

lemma sexticReciprocityPhase_norm (a x:Eis) : ‖sexticReciprocityPhase a x‖≤1 := by
  unfold sexticReciprocityPhase quadraticRaySign
  split_ifs <;> norm_num

def reciprocalRow (a:Eis) (ha:Supported (Ideal.span {a})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})
  map_one' := by rw [sexticReciprocityPhase_one_right a ha,idealRowHom_one_supported _ ha,one_mul]
  map_mul' x y := by
    rw [sexticReciprocityPhase_mul_right,idealRowHom_argument_mul]
    ring

lemma reciprocalRow_norm (a:Eis) (ha:Supported (Ideal.span {a})) (n:Eis) :
    ‖reciprocalRow a ha n‖≤1 := by
  change ‖sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (sexticReciprocityPhase_norm a n)).trans (idealRowHom_norm _ _)

lemma reciprocalRow_periodic (a:Eis) (ha:Supported (Ideal.span {a})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(4:Eis)}*Ideal.span {a}) (reciprocalRow a ha) := by
  intro x y hxy
  change sexticReciprocityPhase a x*idealRowHom x (Ideal.span {a})=
    sexticReciprocityPhase a y*idealRowHom y (Ideal.span {a})
  rw [sexticReciprocityPhase_congr_right a x y
    (Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)),
    idealRowHom_congr_mod _ x y (Ideal.mul_le_right hxy)]

lemma reciprocalRow_eq_idealRowHom (a n:Eis)
    (ha:Supported (Ideal.span {a})) (hn:Supported (Ideal.span {n}))
    (hpa:lambda^2∣a-1) (hpn:lambda^2∣n-1) :
    reciprocalRow a ha n=idealRowHom a (Ideal.span {n}) := by
  have h:=idealRowHom_primary_reciprocity n a hpn hpa hn ha
  have hs:sexticReciprocityPhase n a=sexticReciprocityPhase a n := by
    exact congrArg (fun z:ℤ=>(z:ℂ)) (quadraticRaySign_symm _ _)
  change sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})=_
  rw [hs] at h
  exact h.symm

end CanonicalRowCompletion

namespace CubicEisenstein
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def amplitude (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedConjugateCuspArray s.index u m I J*
    sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
    ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      eisEmbedding (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))

lemma amplitude_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ‖s.amplitude u m I J‖≤1 := by
  by_cases he:fixedCuspArrayEligible I J
  · rw [amplitude,norm_mul,norm_mul,breveE_norm,
      sourceFrequencyAngle_norm _ (fixedCuspArrayIndex_ne_zero u m I J he.2.1 he.2.2),mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  · simp only [amplitude,fixedConjugateCuspArray,
      fixedCuspArray_zero_of_ineligible _ _ _ _ _ he,star_zero,zero_mul,norm_zero]
    norm_num

theorem smoothedKernel_fixed_shape (g:levelTwo) (hc:((g:SL(2,Eis))*H) 1 0≠0)
    (W:ℝ→ℂ) (X:ℝ) :
    (s.datum g hc).smoothedKernel W X=
      (fixedRadialCoefficientScalar*((s.datum g hc).multiplier*
        (‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ)))*
      ∑'p:ThetaFullIndex,
        ((s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*
            eisEmbedding (s.upper 0 0)^2*
            (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0))/
            (sourceCuspScale s.index:ℂ)))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^4))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3) := by
  rw [(s.datum g hc).smoothedKernel_fixed_array,s.datum_heightScale]
  have hi:(s.datum g hc).index=s.index:=rfl
  simp only [hi,←pow_mul,show (2:ℕ)*2=4 by norm_num]
  congr 1
  apply tsum_congr
  intro p
  have hp:=s.datum_additive_phase g hc (cuspFrequency (thetaFullFrequency p))
    (sourceCuspScale s.index:ℂ)
  rw [show -cuspFrequency (thetaFullFrequency p)*
      ((s.datum g hc).dualPoint/(sourceCuspScale s.index:ℂ))=
      -cuspFrequency (thetaFullFrequency p)*(s.datum g hc).dualPoint/(sourceCuspScale s.index:ℂ) by ring,hp]
  unfold amplitude
  rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
  ring

lemma smoothed_row_factor (g:levelTwo) (hc:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g hc).multiplier*((s.datum g hc).heightScale:ℂ)=
      -star (levelTwoComplexCharacter g)*
        (star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2)*
        ((‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ):ℂ)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [s.datum_multiplier,s.datum_heightScale]
  push_cast
  ring

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical Matrix MatrixGroups

namespace ShortDraftCRT
variable {R:Type*} [CommRing R]

lemma exists_controlled_inverse (B c a:R) (ha:IsCoprime a (B*c)) :
    ∃d0:R,B*c∣a*d0-1 := by
  obtain ⟨x,y,hxy⟩:=ha
  refine ⟨x,-y,?_⟩
  linear_combination hxy

lemma exists_controlled_zero_inverse (B c a:R)
    (hBc:IsCoprime B c) (hac:IsCoprime a c) :
    ∃d0:R,B∣d0 ∧ c∣a*d0-1 := by
  obtain ⟨x,y,hxy⟩:=hac.mul_left hBc
  refine ⟨B*x,⟨x,rfl⟩,-y,?_⟩
  linear_combination hxy

variable [IsDomain R]

lemma fixed_completion_upper_right_dvd (B M c r a d0 b d:R)
    (hc:c≠0) (hBM:B∣M) (hr:IsCoprime r (M*c))
    (hinv:B*c∣a*d0-1) (hdet:a*d-b*(c*r)=1) (hd:M*c∣d-d0) : B∣b := by
  have hBcM:B*c∣M*c:=mul_dvd_mul_right hBM c
  have hadd:B*c∣a*(d-d0):=dvd_mul_of_dvd_right (hBcM.trans hd) a
  have hfull:B*c∣a*d-1:=by
    convert dvd_add hadd hinv using 1 ; ring
  have hmul:B*c∣c*(b*r):=by
    convert hfull using 1
    linear_combination -hdet
  rw [mul_comm B c] at hmul
  have hbr:B∣b*r:=(mul_dvd_mul_iff_left hc).mp hmul
  have hBr:IsCoprime B r:=hr.of_mul_right_left.symm.of_isCoprime_of_dvd_left hBM
  exact hBr.dvd_of_dvd_mul_right hbr

theorem exists_fixed_completion_upper_right (B M c r a d0:R)
    (hc:c≠0) (hBM:B∣M) (hr:IsCoprime r (M*c)) (har:IsCoprime a r)
    (hinv:B*c∣a*d0-1) :
    ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b := by
  obtain ⟨b,d,hdet,hd⟩:=exists_fixed_completion M c r a d0
    ((dvd_mul_left c B).trans hinv) hr har
  exact ⟨b,d,hdet,hd,fixed_completion_upper_right_dvd B M c r a d0 b d hc hBM hr hinv hdet hd⟩

omit [IsDomain R] in
theorem exists_fixed_completion_lower_right (B M c r a d0:R)
    (hBM:B∣M) (hr:IsCoprime r (M*c)) (har:IsCoprime a r)
    (hzero:B∣d0) (hinv:c∣a*d0-1) :
    ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣d ∧ B∣a*d ∧ B∣b*(c*r)+1 := by
  obtain ⟨b,d,hdet,hd⟩:=exists_fixed_completion M c r a d0 hinv hr har
  have hdd:B∣d-d0:=(hBM.trans (dvd_mul_right M c)).trans hd
  have hBd:B∣d:=by
    convert dvd_add hdd hzero using 1 ; ring
  have hBad:B∣a*d:=dvd_mul_of_dvd_right hBd a
  refine ⟨b,d,hdet,hd,hBd,hBad,?_⟩
  convert hBad using 1
  linear_combination -hdet

theorem controlled_completion_matrix_congr (M c r r0 a a0 b b0 d d0 inverse:R)
    (hc:c≠0) (hr:IsCoprime M r)
    (hdet:a*d-b*(c*r)=1) (hdet0:a0*d0-b0*(c*r0)=1)
    (ha:M*c∣a-a0) (hd:M*c∣d-inverse) (hd0:M*c∣d0-inverse)
    (hrr:M∣r-r0) :
    (!![a,b;c*r,d]:Matrix (Fin 2) (Fin 2) R).map (Ideal.Quotient.mk (Ideal.span {M}))=
      (!![a0,b0;c*r0,d0]:Matrix (Fin 2) (Fin 2) R).map (Ideal.Quotient.mk (Ideal.span {M})) := by
  apply fixed_completion_matrix_congr M c r r0 a a0 b b0 d d0 hc hr hdet hdet0 ha _ hrr
  convert dvd_sub hd hd0 using 1 ; ring

end ShortDraftCRT

end

end OAI

end

