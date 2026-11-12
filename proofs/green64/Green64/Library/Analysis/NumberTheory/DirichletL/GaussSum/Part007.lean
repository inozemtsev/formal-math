module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part019

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / GaussSum / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.GaussSum.MellinSupport -/

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

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeWeight_zero_of_primaryGenerator_zero (Ψ:Eis→*ℂ) (I:Ideal Eis)
    (h:primaryGenerator I=0) : cubeWeight Ψ I=0 := by
  simp [cubeWeight,h,FiniteGaussPhase.angularFactor]

lemma completedMellinCoefficient_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:completedMellinCoefficient Ψ p≠0) :
    Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0 := by
  have hleft:Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 := by
    by_contra hh
    apply hp
    simp only [completedMellinCoefficient,columnWeight,squarefreeGaussCoefficient,
      dite_eq_right hh,zero_mul,zero_div]
  refine ⟨hleft.1,hleft.2,?_⟩
  intro hright
  apply hp
  rw [completedMellinCoefficient,cubeWeight_zero_of_primaryGenerator_zero Ψ _ hright,mul_zero]

lemma completedMellinCoefficient_zero_off_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:¬(Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0)) :
    completedMellinCoefficient Ψ p=0 := by
  by_contra hn
  exact hp (completedMellinCoefficient_support Ψ p hn)

def primaryCubePairToMellinIndex
    (p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0})) : CompletedMellinIndex :=
  (⟨p.1.val,p.1.property.1.ne_zero⟩,
    ⟨p.2.val,primaryGenerator_ne_zero_ideal p.2.val p.2.property⟩)

lemma primaryCubePairToMellinIndex_injective : Function.Injective primaryCubePairToMellinIndex := by
  intro p q hpq
  exact Prod.ext
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.1.val) hpq))
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.2.val) hpq))

theorem completedMellinCoefficient_tsum_primary_pairs (Ψ:Eis→*ℂ)
    (w:CompletedMellinIndex→ℂ) :
    (∑'p:CompletedMellinIndex,completedMellinCoefficient Ψ p*w p)=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          w (primaryCubePairToMellinIndex p) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p=>primaryCubePairToMellinIndex p.val)
  · exact primaryCubePairToMellinIndex_injective.comp Subtype.val_injective
  · intro p hp
    change completedMellinCoefficient Ψ p*w p≠0 at hp
    have hc:completedMellinCoefficient Ψ p≠0 := by
      intro hz
      exact hp (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=completedMellinCoefficient_support Ψ p hc
    let q:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}):=(⟨p.1.val,hs,hI⟩,⟨p.2.val,hJ⟩)
    have hq:primaryCubePairToMellinIndex q=p := by
      exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    refine ⟨⟨q,?_⟩,hq⟩
    change completedMellinCoefficient Ψ (primaryCubePairToMellinIndex q)*
      w (primaryCubePairToMellinIndex q)≠0
    simpa only [hq] using hp
  · intro p
    rfl

theorem completedBesselProfile_primary_pairs (Ψ:Eis→*ℂ) (q v:ℝ) :
    completedBesselProfile Ψ q v=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        (completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          (completedMellinLength (primaryCubePairToMellinIndex p):ℂ))*(v:ℂ)*
            CubicEisenstein.schlafliBesselK (1/3)
              (4*Real.pi*q*Real.sqrt (completedMellinLength (primaryCubePairToMellinIndex p))*v) := by
  unfold completedBesselProfile CubicEisenstein.radialBesselProfile
  simpa only [mul_assoc] using completedMellinCoefficient_tsum_primary_pairs Ψ
    (fun p=>(completedMellinLength p:ℂ)*(v:ℂ)*CubicEisenstein.schlafliBesselK (1/3)
      (4*Real.pi*q*Real.sqrt (completedMellinLength p)*v))

end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSourceConjugateFunction_levelTwo (G:levelTwo) (w:HyperbolicSpace) :
    cubicSourceConjugateFunction (integralComplexMatrix (G:SL(2,Eis)) • w)=
      star (levelTwoComplexCharacter G)*cubicSourceConjugateFunction w := by
  simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_automorphy,star_mul]
  ring

theorem cubicSourceConjugateFunction_cuspDerivative_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (star (levelTwoComplexCharacter G)*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceConjugateFunction (H • upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceConjugateFunction g H
    (star (levelTwoComplexCharacter G)) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceConjugateFunction_levelTwo]
  · exact cubicSourceConjugateFunction_translate_split_differentiableAt H _ (by positivity)

lemma cuspBarProfile_conjugate_reflection_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0) v=
      reflectedCuspProfile (-star (levelTwoComplexCharacter G)/(g 1 0)^2)
        (‖g 1 0‖^2)
        (cuspZProfile (fun w=>cubicSourceConjugateFunction (H • w)) (-g 1 1/g 1 0)) v := by
  have hdual:0<(‖g 1 0‖^2*v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv,reflectedCuspProfile,cuspZProfile_positive _ _ _ hdual]
  have he:=cubicSourceConjugateFunction_cuspDerivative_levelTwo G g H hfactor hc v hv
  have hp:(v:ℂ)^(-2:ℂ)=((v:ℂ)^2)⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hp]
  simp only [one_div] at he
  rw [he]
  ring

lemma conjugateSource_cuspRepresentative_zProfile_decay (j:Fin 3) (z:ℂ) :
    ∃deltaLoss:ℝ,0<deltaLoss ∧ cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) z
        =O[atTop] (fun v:ℝ=>Real.exp (-deltaLoss*v)) := by
  fin_cases j
  · refine ⟨residualCuspDecayRate,residualCuspDecayRate_pos,?_⟩
    simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero]
      using cuspZProfile_conjugate_isBigO z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO false z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO true z

theorem conjugateSource_levelTwo_three_cusp_mellin_entire (G:levelTwo)
    (j:Fin 3) (g:SL(2,ℂ))
    (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j))
    (hc:g 1 0≠0) :
    ((∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)))) ∧
    ((∀s:ℂ,MellinConvergent
      (cuspZProfile (fun w=>cubicSourceConjugateFunction
        (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)) s) ∧
      Differentiable ℂ (mellin
        (cuspZProfile (fun w=>cubicSourceConjugateFunction
          (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)))) := by
  have hchar:levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn:=norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hscalar:-star (levelTwoComplexCharacter G)/(g 1 0)^2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  obtain ⟨deltaLoss,hδ,hb⟩:=conjugateSource_cuspRepresentative_zProfile_decay j (-g 1 1/g 1 0)
  exact cusp_mellin_entire_both
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0))
    (-star (levelTwoComplexCharacter G)/(g 1 0)^2) hscalar (‖g 1 0‖^2)
    residualCuspDecayRate deltaLoss (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualCuspDecayRate_pos hδ
    (cuspBarProfile_conjugate_continuousOn _) (cuspZProfile_conjugate_translate_continuousOn _ _)
    (cuspBarProfile_conjugate_isBigO _) hb
    (fun v hv=>cuspBarProfile_conjugate_reflection_levelTwo G g _ hfactor hc v hv)

end

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_triangular_right_cusp_ratio (g T:SL(2,ℂ)) (hT:T 1 0=0)
    (hc:(g*T) 1 0≠0) :
    g 1 0≠0 ∧ (g*T) 0 0/(g*T) 1 0=g 0 0/g 1 0 := by
  have hcol (i:Fin 2) : (g*T) i 0=g i 0*T 0 0 := by
    change (∑k:Fin 2,g i k*T k 0)=_
    rw [Fin.sum_univ_two,hT,mul_zero,add_zero]
  have hn:g 1 0*T 0 0≠0:=by rwa [hcol] at hc
  have hg: g 1 0≠0:=(mul_ne_zero_iff.mp hn).1
  have ht:T 0 0≠0:=(mul_ne_zero_iff.mp hn).2
  refine ⟨hg,?_⟩
  rw [hcol,hcol]
  field_simp

theorem conjugateSource_integral_cusp_mellin_entire (M:SL(2,Eis)) (hc:M 1 0≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction
        (eisEmbedding (M 0 0)/eisEmbedding (M 1 0))) s) ∧
    Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction
      (eisEmbedding (M 0 0)/eisEmbedding (M 1 0)))) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
  let g:SL(2,ℂ):=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j)
  have he:integralComplexMatrix M=g*integralComplexMatrix T:=by
    rw [hM,map_mul,map_mul]
  have ht:integralComplexMatrix T 1 0=0:=by
    rw [integralComplexMatrix_apply,hT,map_zero]
  have hmc:(g*integralComplexMatrix T) 1 0≠0:=by
    rw [←he,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hc
  obtain ⟨hg,hratio⟩:=upper_triangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  have hresult:=(conjugateSource_levelTwo_three_cusp_mellin_entire G j g rfl hg).1
  rw [←hratio,←he] at hresult
  simpa only [integralComplexMatrix_apply] using hresult

lemma exists_integral_matrix_cusp_ratio (a c:Eis) (hc:c≠0) :
    ∃M:SL(2,Eis),M 1 0≠0 ∧
      eisEmbedding (M 0 0)/eisEmbedding (M 1 0)=eisEmbedding a/eisEmbedding c := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by
    intro hz
    exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by
    intro hz
    exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨u,v,huv⟩:=IsBezout.gcd_eq_sum a c
  change u*a+v*c=d at huv
  have hred:u*a'+v*c'=1:=by
    apply mul_left_cancel₀ hd
    calc
      d*(u*a'+v*c')=u*a+v*c:=by rw [ha,hc'];ring
      _=d:=huv
      _=d*1:=(mul_one d).symm
  let M:SL(2,Eis):=⟨!![a',-v;c',u],by
    rw [Matrix.det_fin_two_of]
    linear_combination hred⟩
  refine ⟨M,hcp,?_⟩
  change eisEmbedding a'/eisEmbedding c'=eisEmbedding a/eisEmbedding c
  rw [ha,hc',map_mul,map_mul]
  have hde:eisEmbedding d≠0:=eisEmbedding_ne_zero hd
  have hce:eisEmbedding c'≠0:=eisEmbedding_ne_zero hcp
  field_simp

theorem conjugateSource_rational_cusp_mellin_entire (a c:Eis) (hc:c≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (eisEmbedding a/eisEmbedding c)) s) ∧
    Differentiable ℂ (mellin
      (cuspBarProfile cubicSourceConjugateFunction (eisEmbedding a/eisEmbedding c))) := by
  obtain ⟨M,hM,hratio⟩:=exists_integral_matrix_cusp_ratio a c hc
  simpa only [hratio] using conjugateSource_integral_cusp_mellin_entire M hM

theorem conjugateSource_finite_twist_cusp_mellin_entire (h c:Eis) (hc:c≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (-3*eisEmbedding h/eisEmbedding c)) s) ∧
    Differentiable ℂ (mellin
      (cuspBarProfile cubicSourceConjugateFunction (-3*eisEmbedding h/eisEmbedding c))) := by
  simpa only [map_mul,map_neg,map_ofNat] using
    conjugateSource_rational_cusp_mellin_entire (-3*h) c hc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance signedOmegaUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def signedOmegaUnit (s:Bool) (j:Fin 3) :Eisˣ :=
  if s then -(ramifiedOmegaUnit^j.val) else ramifiedOmegaUnit^j.val

lemma signedOmegaUnit_val (s:Bool) (j:Fin 3) :
    (signedOmegaUnit s j:Eis)=if s then -(omega^j.val) else omega^j.val := by
  cases s <;> simp [signedOmegaUnit,ramifiedOmegaUnit_val]

lemma signedOmegaUnit_surjective : Function.Surjective (fun p:Bool×Fin 3=>signedOmegaUnit p.1 p.2) := by
  intro u
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega u
  · refine ⟨(false,j),Units.ext ?_⟩
    simpa only [signedOmegaUnit_val,Bool.false_eq_true,ite_false] using hj.symm
  · refine ⟨(true,j),Units.ext ?_⟩
    simpa only [signedOmegaUnit_val,ite_true] using hj.symm

def signedOmegaEquiv : (Bool×Fin 3)≃Eisˣ := Equiv.ofBijective
  (fun p=>signedOmegaUnit p.1 p.2)
  ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨signedOmegaUnit_surjective,by
    have hc:Fintype.card Eisˣ=6:=by
      simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
    simp [hc]⟩)

lemma cubicSymbol_norm_one (c n:Eis) (hn:lambda^2∣n-1) (hc:IsCoprime c n) :
    ‖eisEmbedding (symbol c n)‖=1 := by
  have hcube:(eisEmbedding (symbol c n))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime c n hn hc,map_one]
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm hcube

lemma arithmeticResidueSum_norm_mul_primary (h n:Eis) (hn:lambda^2∣n-1)
    (u:Eisˣ) (r:ℕ) (hr:2≤ r) :
    ‖arithmeticResidueSum (h*n) (u.val*lambda^r)‖=
      ‖arithmeticResidueSum h (u.val*lambda^r)‖ := by
  have hc: IsCoprime (u.val*lambda^r) n :=
    (ramified_primary_coprime u r n hn).of_mul_left_right
  have he:=congrArg norm (arithmeticResidueSum_frequency_twist h (u.val*lambda^r) n
    (ramifiedElement_ne_zero u r) (ramifiedElement_level u r hr)
    ⟨hc,three_dvd_lambda_sq.trans hn⟩)
  simpa only [norm_mul,cubicSymbol_norm_one _ n hn hc,one_mul] using he

def lowRamifiedFrequency (a r:Fin 3) : Eis := omega^a.val*lambda^(r.val+2)

lemma lowRamifiedFrequency_ne_zero (a r:Fin 3) : lowRamifiedFrequency a r≠0 := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_ne_zero (ramifiedOmegaUnit^a.val) (r.val+2)

lemma lowRamifiedFrequency_absNorm (a r:Fin 3) :
    Ideal.absNorm (Ideal.span {lowRamifiedFrequency a r})=3^(r.val+2) := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_absNorm (ramifiedOmegaUnit^a.val) (r.val+2)

lemma lowRamifiedFrequency_arithmetic_vanish (a r:Fin 3) (u:Eisˣ) (k:ℕ) (hk:5≤k) :
    arithmeticResidueSum (lowRamifiedFrequency a r) (u.val*lambda^(k+2))=0 := by
  by_contra hA
  have hb:=ramified_arithmetic_norm_bound _ (lowRamifiedFrequency_ne_zero a r) u (k+2) (by omega) hA
  rw [lowRamifiedFrequency_absNorm] at hb
  have hlo:(3:ℕ)^7≤3^(k+2):=Nat.pow_le_pow_right (by decide) (by omega)
  have hhi:(3:ℕ)^(r.val+2)≤3^4:=Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hlo hhi
  omega

lemma lowRamifiedFrequency_primary_vanish (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1)
    (u:Eisˣ) (k:ℕ) (hk:5≤k) :
    arithmeticResidueSum (lowRamifiedFrequency a r*n) (u.val*lambda^(k+2))=0 := by
  apply norm_eq_zero.mp
  rw [arithmeticResidueSum_norm_mul_primary _ n hn u (k+2) (by omega),
    lowRamifiedFrequency_arithmetic_vanish a r u k hk,norm_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedCoordinateUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedCoordMul (x y:ℤ×ℤ) :ℤ×ℤ := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def ramifiedCoordPow (x:ℤ×ℤ) :ℕ→ℤ×ℤ
  | 0=>(1,0)
  | n+1=>ramifiedCoordMul (ramifiedCoordPow x n) x

def lowRamifiedQuotientCoord (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5) :ℤ×ℤ :=
  let z:=ramifiedCoordMul (ramifiedCoordPow (0,1) (a.val+5-j.val))
    (ramifiedCoordPow (-1,1) (r.val+2-n.val))
  if s then z else (-z.1,-z.2)

def lowRamifiedSupport (a r:Fin 3) (p:Bool×Fin 3×Fin 5) :Prop :=
  p.2.2.val≤ r.val+2 ∧
  let z:=lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2
  (3:ℤ)∣2*(p.2.1.val:ℤ)+(p.2.2.val+2:ℕ)+z.2 ∧
  (3:ℤ)∣2*(p.2.1.val:ℤ)+z.1-z.2

instance lowRamifiedSupport_decidable (a r:Fin 3) (p:Bool×Fin 3×Fin 5) :
    Decidable (lowRamifiedSupport a r p) :=
  inferInstanceAs (Decidable (p.2.2.val≤ r.val+2 ∧
    (3:ℤ)∣2*(p.2.1.val:ℤ)+(p.2.2.val+2:ℕ)+(lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).2 ∧
    (3:ℤ)∣2*(p.2.1.val:ℤ)+(lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).1-
      (lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).2))

def lowRamifiedSupportSet (a r:Fin 3) :Finset (Bool×Fin 3×Fin 5) :=
  Finset.univ.filter (lowRamifiedSupport a r)

lemma lowRamifiedSupport_card (a r:Fin 3) : (lowRamifiedSupportSet a r).card≤5 := by
  decide +revert

lemma lowRamifiedSupport_exponent (a r:Fin 3) (p:Bool×Fin 3×Fin 5)
    (hp:lowRamifiedSupport a r p) : 1≤p.2.2.val := by
  decide +revert

lemma ramifiedCoordMul_eval (x y:ℤ×ℤ) :
    ActualEisensteinCoordinates.eval (ramifiedCoordMul x y).1 (ramifiedCoordMul x y).2=
      ActualEisensteinCoordinates.eval x.1 x.2*ActualEisensteinCoordinates.eval y.1 y.2 :=
  (ActualEisensteinCoordinates.eval_mul _ _ _ _).symm

lemma ramifiedCoordPow_eval (x:ℤ×ℤ) (n:ℕ) :
    ActualEisensteinCoordinates.eval (ramifiedCoordPow x n).1 (ramifiedCoordPow x n).2=
      (ActualEisensteinCoordinates.eval x.1 x.2)^n := by
  induction n with
  | zero => simp [ramifiedCoordPow,ActualEisensteinCoordinates.eval]
  | succ n ih => rw [ramifiedCoordPow,ramifiedCoordMul_eval,ih,pow_succ]

lemma lowRamifiedQuotientCoord_eval (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5) :
    ActualEisensteinCoordinates.eval (lowRamifiedQuotientCoord a r s j n).1
      (lowRamifiedQuotientCoord a r s j n).2=
      if s then omega^(a.val+5-j.val)*lambda^(r.val+2-n.val)
      else -(omega^(a.val+5-j.val)*lambda^(r.val+2-n.val)) := by
  have ho:ActualEisensteinCoordinates.eval 0 1=omega:=by
    simp [ActualEisensteinCoordinates.eval]; rfl
  have hl:ActualEisensteinCoordinates.eval (-1) 1=lambda:=by
    change ActualEisensteinCoordinates.eval (-1) 1=omega-1
    have he:ActualEisensteinCoordinates.eval (-1) 1=(-1:Eis)+ActualEisensteinCoordinates.eval 0 1:=by
      simp [ActualEisensteinCoordinates.eval]
    rw [he,ho]
    ring
  have he:∀x:ℤ×ℤ,ActualEisensteinCoordinates.eval (-x.1) (-x.2)=
      -ActualEisensteinCoordinates.eval x.1 x.2:=by
    intro x
    simp only [ActualEisensteinCoordinates.eval,Int.cast_neg]
    ring
  cases s <;> simp only [lowRamifiedQuotientCoord,Bool.false_eq_true,ite_false,ite_true,
    he,ramifiedCoordMul_eval,ramifiedCoordPow_eval,ho,hl]

lemma lowRamifiedQuotientCoord_relation (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5)
    (hn:n.val≤ r.val+2) :
    3*lowRamifiedFrequency a r=
      ((signedOmegaUnit s j:Eis)*lambda^(n.val+2))*
        ActualEisensteinCoordinates.eval (lowRamifiedQuotientCoord a r s j n).1
          (lowRamifiedQuotientCoord a r s j n).2 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  have h3:(3:Eis)=-omega^2*lambda^2:=by
    rw [hl]
    calc
      (3:Eis)=3*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
      _=_:=by ring
  have ho:omega^j.val*omega^(a.val+5-j.val)=omega^(a.val+2):=by
    rw [←pow_add,show j.val+(a.val+5-j.val)=a.val+5 by omega]
    rw [show a.val+5=(a.val+2)+3 by omega,pow_add,omega_primitive.pow_eq_one,mul_one]
  have hp:lambda^(n.val+2)*lambda^(r.val+2-n.val)=lambda^(r.val+4):=by
    rw [←pow_add]
    congr 1
    omega
  have he:3*lowRamifiedFrequency a r=
      -(omega^j.val*omega^(a.val+5-j.val))*(lambda^(n.val+2)*lambda^(r.val+2-n.val)):=by
    rw [ho,hp,lowRamifiedFrequency]
    conv_lhs => rw [h3]
    rw [show r.val+4=2+(r.val+2) by omega,pow_add,pow_add]
    ring
  rw [lowRamifiedQuotientCoord_eval,signedOmegaUnit_val]
  cases s <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linear_combination he

lemma lowRamifiedSupport_of_ne_zero (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5)
    (hA:arithmeticResidueSum (lowRamifiedFrequency a r)
      ((signedOmegaUnit s j:Eis)*lambda^(n.val+2))≠0) :
    lowRamifiedSupport a r (s,j,n) := by
  have hn:n.val≤ r.val+2:=by
    have hb:=ramified_arithmetic_norm_bound _ (lowRamifiedFrequency_ne_zero a r)
      (signedOmegaUnit s j) (n.val+2) (by omega) hA
    rw [lowRamifiedFrequency_absNorm] at hb
    have he:9*3^(r.val+2)=(3:ℕ)^(r.val+4):=by
      rw [show r.val+4=(r.val+2)+2 by omega,pow_add]
      ring
    rw [he] at hb
    have hh: n.val+2≤ r.val+4 := (Nat.pow_le_pow_iff_right (by decide : 1<(3:ℕ))).mp hb
    omega
  let z:=lowRamifiedQuotientCoord a r s j n
  have hu:(signedOmegaUnit s j:Eis)=omega^j.val ∨
      (signedOmegaUnit s j:Eis)=-(omega^j.val):=by
    cases s <;> simp [signedOmegaUnit_val]
  have he:=ramified_arithmetic_explicit_table (lowRamifiedFrequency a r)
    (ActualEisensteinCoordinates.eval z.1 z.2) (signedOmegaUnit s j) (n.val+2) j.val
    (by omega) hu (lowRamifiedQuotientCoord_relation a r s j n hn)
  have hz:ramifiedCongruence (ActualEisensteinCoordinates.eval z.1 z.2) j.val (n.val+2):=by
    by_contra hc
    rw [ite_eq_right hc] at he
    exact hA he
  exact ⟨hn,by simpa only [ramifiedCongruence,ShortDraftLatticeCount.coords_eval] using hz⟩

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedRawWeightUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedRawWeight (h:Eis) (u:Eisˣ) (k:ℕ) :ℂ :=
  ((3^(k+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h (u.val*lambda^(k+2))

lemma ramifiedRawWeight_norm_le (h:Eis) (u:Eisˣ) (k:ℕ) :
    ‖ramifiedRawWeight h u k‖≤ ramifiedDecayRatio^(k+2) := by
  rw [ramifiedRawWeight,norm_mul,
    arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (k+2) (by omega)]
  exact (mul_le_mul_of_nonneg_left (explicitRamifiedCoefficient_norm_le h u (k+2))
    (norm_nonneg _)).trans_eq (ramifiedWeight_norm_scalar _)

lemma ramifiedRawWeight_norm_mul_primary (h n:Eis) (hn:lambda^2∣n-1) (u:Eisˣ) (k:ℕ) :
    ‖ramifiedRawWeight (h*n) u k‖=‖ramifiedRawWeight h u k‖ := by
  simp only [ramifiedRawWeight,norm_mul,
    arithmeticResidueSum_norm_mul_primary h n hn u (k+2) (by omega)]

lemma ramifiedDecayRatio_cube : ramifiedDecayRatio^3=(1/3:ℝ) := by
  rw [ramifiedDecayRatio,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma lowRamifiedRawWeight_bound (a r:Fin 3) (s:Bool) (j:Fin 3) (k:Fin 5) :
    ‖ramifiedRawWeight (lowRamifiedFrequency a r) (signedOmegaUnit s j) k.val‖≤
      if lowRamifiedSupport a r (s,j,k) then (1/3:ℝ) else 0 := by
  split_ifs with hs
  · have hh:1≤k.val:=lowRamifiedSupport_exponent a r (s,j,k) hs
    have hb:ramifiedDecayRatio^(k.val+2)≤ ramifiedDecayRatio^3:=
      pow_le_pow_of_le_one ramifiedDecayRatio_pos.le ramifiedDecayRatio_lt_one.le (by omega)
    exact (ramifiedRawWeight_norm_le (lowRamifiedFrequency a r) (signedOmegaUnit s j) k.val).trans
      (hb.trans_eq ramifiedDecayRatio_cube)
  · have hz:arithmeticResidueSum (lowRamifiedFrequency a r)
        ((signedOmegaUnit s j:Eis)*lambda^(k.val+2))=0:=by
      by_contra hne
      exact hs (lowRamifiedSupport_of_ne_zero a r s j k hne)
    simp only [ramifiedRawWeight,hz,mul_zero,norm_zero,le_refl]

theorem lowRamifiedRawWeight_sum (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    (∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖)≤5/3 := by
  simp_rw [ramifiedRawWeight_norm_mul_primary _ n hn]
  have hu:(∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r) u k.val‖)=
      ∑p:Bool×Fin 3,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r)
        (signedOmegaUnit p.1 p.2) k.val‖ := by
    symm
    exact Fintype.sum_equiv signedOmegaEquiv _ _ (fun _=>rfl)
  rw [hu]
  calc
    _≤∑p:Bool×Fin 3,∑k:Fin 5,
        if lowRamifiedSupport a r (p.1,p.2,k) then (1/3:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum (fun k hk=>lowRamifiedRawWeight_bound a r p.1 p.2 k)
    _=∑p:Bool×Fin 3×Fin 5,if lowRamifiedSupport a r p then (1/3:ℝ) else 0:=by
      simp only [Fintype.sum_prod_type]
    _=(lowRamifiedSupportSet a r).card*(1/3:ℝ):=by
      rw [←Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,lowRamifiedSupportSet]
    _≤5/3:=by
      have hc:(lowRamifiedSupportSet a r).card≤5:=lowRamifiedSupport_card a r
      exact_mod_cast (show ((lowRamifiedSupportSet a r).card:ℝ)*(1/3:ℝ)≤5/3 by
        have hcr:((lowRamifiedSupportSet a r).card:ℝ)≤5:=by exact_mod_cast hc
        linarith)

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.RamifiedTransform -/

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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowRamifiedTransform (F:Eis→ℂ) (h:Eis) :ℂ :=
  3*F (9*h)+∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight h u k.val*
    F (h*(9*(u.val*lambda^(k.val+2))))

lemma principalArithmeticResidue_low (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    principalArithmeticResidue (lowRamifiedFrequency a r*n)=
      (∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
        unramifiedGaussResidue ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2)))))/
          ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  let h:=lowRamifiedFrequency a r*n
  have hh:h≠0:=mul_ne_zero (lowRamifiedFrequency_ne_zero a r) (primary_ne_zero n hn)
  let N:=max (ramifiedFrequencyBound h+1) 5
  rw [principalArithmeticResidue_eq_sum h hh N (le_max_left _ _)]
  apply congrArg (fun z:ℂ=>z/((9*Real.sqrt 3/2:ℝ):ℂ))
  apply Finset.sum_congr rfl
  intro u hu
  change (∑k∈Finset.range N,principalResidueTerm h u k)=
    ∑k:Fin 5,principalResidueTerm h u k.val
  rw [Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
  intro k hk hk5
  have hz:=lowRamifiedFrequency_primary_vanish a r n hn u k
    (by simpa only [Finset.mem_range,not_lt] using hk5)
  simp only [principalResidueTerm,h,hz,mul_zero,zero_mul]

lemma sourceRayPhase_of_three_dvd (h:Eis) (hh:(3:Eis)∣h) :
    ShortDraftTrace.breveE (cuspFrequency h)=1 := by
  obtain ⟨z,rfl⟩:=hh
  have he:cuspFrequency ((3:Eis)*z)=eisEmbedding z/eisLam:=by
    simp only [cuspFrequency,map_mul,map_ofNat]
    ring
  rw [he]
  exact breveE_embedding_div_traceLambda z

lemma lowRamifiedFrequency_three_dvd (a r:Fin 3) : (3:Eis)∣lowRamifiedFrequency a r := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_level (ramifiedOmegaUnit^a.val) (r.val+2) (by omega)

theorem lowRamifiedTransform_actual (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    lowRamifiedTransform unramifiedGaussResidue (lowRamifiedFrequency a r*n)=
      (4*((9*Real.sqrt 3/2:ℝ):ℂ))*sourceArithmeticResidue (lowRamifiedFrequency a r*n) := by
  rw [sourceArithmeticResidue,ite_eq_left (sourceRayPhase_of_three_dvd _
    (dvd_mul_of_dvd_left (lowRamifiedFrequency_three_dvd a r) n)),
    principalArithmeticResidue_low a r n hn]
  unfold lowRamifiedTransform
  field_simp [show ((9*Real.sqrt 3/2:ℝ):ℂ)≠0 by exact_mod_cast (show (9*Real.sqrt 3/2:ℝ)≠0 by positivity)]
  ; ring

lemma lowRamifiedTransform_sub (F G:Eis→ℂ) (h:Eis) :
    lowRamifiedTransform (fun x=>F x-G x) h=
      lowRamifiedTransform F h-lowRamifiedTransform G h := by
  simp only [lowRamifiedTransform,mul_sub,Finset.sum_sub_distrib]
  ring

lemma ramifiedRawWeight_frequency_cube (h p:Eis) (hp:lambda^2∣p-1) (u:Eisˣ) (k:ℕ) :
    ramifiedRawWeight (h*p^3) u k=ramifiedRawWeight h u k := by
  rw [ramifiedRawWeight,ramifiedRawWeight,arithmeticResidueSum_frequency_cube h _ p
    (ramifiedElement_ne_zero u (k+2)) (ramifiedElement_level u (k+2) (by omega)) hp
    (ramified_primary_coprime u (k+2) p hp).of_mul_left_right]

lemma lowRamifiedTransform_cube_comp (F:Eis→ℂ) (h p:Eis) (hp:lambda^2∣p-1) :
    lowRamifiedTransform (fun x=>F (x*p^3)) h=lowRamifiedTransform F (h*p^3) := by
  simp only [lowRamifiedTransform,ramifiedRawWeight_frequency_cube h p hp]
  have he:9*h*p^3=9*(h*p^3):=by ring
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ring_nf

theorem lowRamifiedTransform_cube_difference (p:Eis) (hp:Prime p) (hpp:lambda^2∣p-1)
    (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    lowRamifiedTransform (fun x=>unramifiedGaussResidue (x*p^3)-unramifiedGaussResidue x)
      (lowRamifiedFrequency a r*n)=0 := by
  rw [lowRamifiedTransform_sub,lowRamifiedTransform_cube_comp _ _ p hpp]
  have hnp:lambda^2∣n*p^3-1:=primary_mul n (p^3) hn (primary_pow_congruence p hpp 3)
  rw [mul_assoc,lowRamifiedTransform_actual a r (n*p^3) hnp,
    lowRamifiedTransform_actual a r n hn]
  rw [←mul_assoc,sourceArithmeticResidue_prime_cube p hp hpp _
    (mul_ne_zero (lowRamifiedFrequency_ne_zero a r) (primary_ne_zero n hn)),sub_self]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma ramifiedFunction_reduce (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (u:Eisˣ) (m:ℕ) :
    ∃j k:Fin 3,F (n*((u:Eis)*lambda^m))=F (n*omega^j.val*lambda^k.val) := by
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega u
  · refine ⟨j,⟨m%3,Nat.mod_lt _ (by decide)⟩,?_⟩
    rw [hj,←mul_assoc,hpow]
  · refine ⟨j,⟨m%3,Nat.mod_lt _ (by decide)⟩,?_⟩
    rw [hj,neg_mul,mul_neg,hneg,←mul_assoc,hpow]

lemma ramifiedFunction_family_bound (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (M:ℝ)
    (hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M) (u:Eisˣ) (m:ℕ) :
    ‖F (n*((u:Eis)*lambda^m))‖≤M := by
  obtain ⟨j,k,hjk⟩:=ramifiedFunction_reduce F hneg hpow n u m
  rw [hjk]
  exact hM j k

lemma ramifiedNine_eq : (9:Eis)=omega*lambda^4 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  calc
    (9:Eis)=9*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
    _=omega*((-3*omega)^2):=by ring
    _=omega*((lambda^2)^2):=by rw [hl]
    _=omega*lambda^4:=by ring

lemma lowRamified_inner_family (a r:Fin 3) (n:Eis) (u:Eisˣ) (k:ℕ) :
    (lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k+2)))=
      n*((↑(ramifiedOmegaUnit^(a.val+1)*u):Eis)*lambda^(r.val+k+8)) := by
  simp only [lowRamifiedFrequency,ramifiedNine_eq,Units.val_mul,Units.val_pow_eq_pow_val,
    ramifiedOmegaUnit_val]
  rw [show r.val+k+8=(r.val+2)+(4+(k+2)) by omega]
  simp only [pow_add,pow_one]
  ring

lemma lowRamifiedLeading (F:Eis→ℂ)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (j k:Fin 3) :
    F (9*(lowRamifiedFrequency ⟨(j.val+2)%3,Nat.mod_lt _ (by decide)⟩ k*n))=
      F (n*omega^j.val*lambda^k.val) := by
  have ho:omega^((j.val+2)%3+1)=omega^j.val:=by
    fin_cases j <;> norm_num [omega_primitive.pow_eq_one]
  have he:9*(lowRamifiedFrequency ⟨(j.val+2)%3,Nat.mod_lt _ (by decide)⟩ k*n)=
      (n*omega^j.val)*lambda^(k.val+6):=by
    simp only [lowRamifiedFrequency,ramifiedNine_eq]
    rw [show k.val+6=4+(k.val+2) by omega,pow_add,←ho,pow_succ]
    ring
  rw [he,hpow,show (k.val+6)%3=k.val by omega]

lemma lowRamified_remainder_bound (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (hn:lambda^2∣n-1)
    (M:ℝ) (hM0:0≤M) (hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M)
    (a r:Fin 3) :
    ‖∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
      F ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2))))‖≤(5/3)*M := by
  calc
    _≤∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
        F ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2))))‖:=by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u hu=>norm_sum_le _ _))
    _≤∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖*M:=by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul,lowRamified_inner_family]
      exact mul_le_mul_of_nonneg_left (ramifiedFunction_family_bound F hneg hpow n M hM _ _) (norm_nonneg _)
    _=(∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖)*M:=by
      simp only [Finset.sum_mul]
    _≤(5/3)*M:=mul_le_mul_of_nonneg_right (lowRamifiedRawWeight_sum a r n hn) hM0

theorem lowRamifiedTransform_injective (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (hn:lambda^2∣n-1)
    (hz:∀a r:Fin 3,lowRamifiedTransform F (lowRamifiedFrequency a r*n)=0) :
    ∀j k:Fin 3,F (n*omega^j.val*lambda^k.val)=0 := by
  obtain ⟨i,hi,himax⟩:=Finset.exists_max_image (Finset.univ:Finset (Fin 3×Fin 3))
    (fun i=>‖F (n*omega^i.1.val*lambda^i.2.val)‖) Finset.univ_nonempty
  let M:=‖F (n*omega^i.1.val*lambda^i.2.val)‖
  have hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M:=by
    intro j k
    exact himax (j,k) (Finset.mem_univ _)
  let a:Fin 3:=⟨(i.1.val+2)%3,Nat.mod_lt _ (by decide)⟩
  have hb:=lowRamified_remainder_bound F hneg hpow n hn M (norm_nonneg _) hM a i.2
  have he:=hz a i.2
  unfold lowRamifiedTransform at he
  have hlead:F (9*(lowRamifiedFrequency a i.2*n))=F (n*omega^i.1.val*lambda^i.2.val):=
    lowRamifiedLeading F hpow n i.1 i.2
  rw [hlead] at he
  have hnorm:3*M≤(5/3)*M:=by
    have heq:3*F (n*omega^i.1.val*lambda^i.2.val)=
        -(∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a i.2*n) u k.val*
          F ((lowRamifiedFrequency a i.2*n)*(9*(u.val*lambda^(k.val+2))))):=by
      linear_combination he
    have hh:=congrArg norm heq
    rw [norm_mul,Complex.norm_ofNat,norm_neg] at hh
    exact hh.le.trans hb
  have hmzero:M=0:=by have hm0:0≤M:=norm_nonneg _; nlinarith
  intro j k
  exact norm_eq_zero.mp (le_antisymm (hmzero ▸ hM j k) (norm_nonneg _))

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_lambda_factor (h:Eis) (hh:h≠0) :
    ∃n:Eis,∃u:Eisˣ,∃m:ℕ,lambda^2∣n-1 ∧ h=n*((u:Eis)*lambda^m) := by
  obtain ⟨⟨m,J⟩,hm⟩:=lambdaFactorMap_bijective.2
    ⟨Ideal.span {h},Ideal.span_singleton_eq_bot.not.mpr hh⟩
  have hi:ramifiedIdeal^m*J.val=Ideal.span {h}:=congrArg Subtype.val hm
  have hs:Ideal.span {lambda^m*primaryGenerator J.val}=Ideal.span {h}:=by
    rw [lambdaFactor_generator_span,hi]
  obtain ⟨u,hu⟩:=Ideal.span_singleton_eq_span_singleton.mp hs
  refine ⟨primaryGenerator J.val,u,m,(primaryGenerator_spec J.val J.property).2,?_⟩
  linear_combination -hu

theorem unramifiedGaussResidue_prime_cube (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) :
    unramifiedGaussResidue (h*p^3)=unramifiedGaussResidue h := by
  by_cases hh:h=0
  · simp only [hh,zero_mul]
  obtain ⟨n,u,m,hn,hfactor⟩:=exists_primary_unit_lambda_factor h hh
  let F:Eis→ℂ:=fun x=>unramifiedGaussResidue (x*p^3)-unramifiedGaussResidue x
  have hneg:∀x,F (-x)=F x:=by
    intro x
    dsimp only [F]
    rw [neg_mul,unramifiedGaussResidue_neg,unramifiedGaussResidue_neg]
  have hpow:∀x k,F (x*lambda^k)=F (x*lambda^(k%3)):=by
    intro x k
    dsimp only [F]
    have h1:unramifiedGaussResidue ((x*lambda^k)*p^3)=
        unramifiedGaussResidue ((x*lambda^(k%3))*p^3):=by
      rw [show (x*lambda^k)*p^3=(x*p^3)*lambda^k by ring,
        show (x*lambda^(k%3))*p^3=(x*p^3)*lambda^(k%3) by ring]
      exact unramifiedGaussResidue_lambda_pow (x*p^3) k
    exact congrArg₂ (fun a b:ℂ=>a-b) h1 (unramifiedGaussResidue_lambda_pow x k)
  have hz:∀j k:Fin 3,F (n*omega^j.val*lambda^k.val)=0:=
    lowRamifiedTransform_injective F hneg hpow n hn
      (fun a r=>lowRamifiedTransform_cube_difference p hp hpp a r n hn)
  obtain ⟨j,k,hjk⟩:=ramifiedFunction_reduce F hneg hpow n u m
  have hF:F h=0:=by rw [hfactor,hjk,hz]
  exact sub_eq_zero.mp hF

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma unramifiedGaussResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (_hh:h≠0) (n:ℕ) :
    unramifiedGaussResidue (h*p^n)=unramifiedGaussResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,unramifiedGaussResidue_prime_cube p hp hprimary _,
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem unramifiedGaussResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=unramifiedGaussResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    unramifiedGaussResidue_prime_cube p hp hprimary _] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem unramifiedGaussResidue_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
        primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have hrec:=unramifiedGaussResidue_prime_recurrence p hp hprimary h hph
  rw [unramifiedGaussResidue_prime_cube p hp hprimary h] at hrec
  have hrel:(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*
      primeCubicGauss p hp hprimary 1 h*unramifiedGaussResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue h:=by
    linear_combination hrec
  have hG:=primeCubicGauss_one_mul_two p hp hprimary h hph
  let q:ℂ:=(Ideal.absNorm (Ideal.span {p}):ℂ)
  have hq:q≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hpower:q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2=1:=by
    rw [←Complex.cpow_add _ _ hq,←Complex.cpow_natCast q 2,
      ←Complex.cpow_add _ _ hq]
    norm_num
  calc
    unramifiedGaussResidue (h*p)=
        (q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2)*unramifiedGaussResidue (h*p):=by rw [hpower,one_mul]
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*
        (q^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 h*unramifiedGaussResidue (h*p)):=by
      calc
        _=q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q*
          (primeCubicGauss p hp hprimary 1 h*primeCubicGauss p hp hprimary 2 h)*
          unramifiedGaussResidue (h*p):=by rw [hG];ring
        _=_:=by ring
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*(q⁻¹*unramifiedGaussResidue h):=by rw [hrel]
    _=_:=by
      change q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*(q⁻¹*unramifiedGaussResidue h)=
        q^(-(2/3:ℂ))*primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h
      field_simp [hq]

theorem unramifiedGaussResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    unramifiedGaussResidue (h*p^n)=
      if n%3=0 then unramifiedGaussResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [unramifiedGaussResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact unramifiedGaussResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,unramifiedGaussResidue_prime_square p hp hprimary h hph]

end

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def thetaFrequencyScale : ℂ := 1/((3:ℂ)*eisLam)
def thetaBesselScale : ℝ := ‖thetaFrequencyScale‖
def thetaDerivativeScalar : ℂ :=
  (-2*Real.pi*Complex.I)*star thetaFrequencyScale*infinityCoefficientScalar

lemma thetaFrequencyScale_ne_zero : thetaFrequencyScale≠0 := by
  exact one_div_ne_zero (mul_ne_zero (by norm_num) eisLam_ne_zero)

lemma thetaBesselScale_pos : 0<thetaBesselScale := norm_pos_iff.mpr thetaFrequencyScale_ne_zero

lemma thetaBesselScale_eq : thetaBesselScale=1/Real.sqrt 27 := by
  have hl : ‖eisLam‖^2=(3:ℝ) := by
    have h := congrArg norm TraceLambdaPhase.eisLam_sq
    norm_num only [norm_pow,norm_neg,Complex.norm_ofNat] at h
    exact h
  have hd : ‖(3:ℂ)*eisLam‖=Real.sqrt 27 := by
    rw [norm_mul,Complex.norm_ofNat]
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤27 by norm_num),
      Real.sqrt_nonneg (27:ℝ),norm_nonneg eisLam]
  rw [thetaBesselScale,thetaFrequencyScale,norm_div,norm_one,hd]

lemma thetaDerivativeScalar_ne_zero : thetaDerivativeScalar≠0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (star_ne_zero.mpr thetaFrequencyScale_ne_zero)) infinityCoefficientScalar_ne_zero

lemma cuspFrequency_eq_thetaFrequencyScale (h : Eis) :
    cuspFrequency h=thetaFrequencyScale*eisEmbedding h := by
  unfold cuspFrequency thetaFrequencyScale
  ring

lemma completedCoefficient_mul_length (Ψ : Eis→*ℂ) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0)
    (hsq : Squarefree I.val) :
    completedMellinCoefficient Ψ (I,J)*(completedMellinLength (I,J):ℂ)=
      star (eisEmbedding (primaryGenerator I.val*(primaryGenerator J.val)^3))*
        (‖eisEmbedding (primaryGenerator J.val)‖:ℂ)*gaussTwo I.val hI*
        Ψ (primaryGenerator I.val)*(Ψ (primaryGenerator J.val))^3 := by
  have hni : (Ideal.absNorm I.val:ℂ)=(‖eisEmbedding (primaryGenerator I.val)‖:ℂ)^2 := by
    exact_mod_cast (primaryGenerator_norm_sq I.val hI).symm
  have hnj : (Ideal.absNorm J.val:ℂ)=(‖eisEmbedding (primaryGenerator J.val)‖:ℂ)^2 := by
    exact_mod_cast (primaryGenerator_norm_sq J.val hJ).symm
  have hi0 : (‖eisEmbedding (primaryGenerator I.val)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hI))
  have hj0 : (‖eisEmbedding (primaryGenerator J.val)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hJ))
  rw [completedMellinCoefficient,columnWeight_eq Ψ I.val hsq hI]
  rw [show cubeWeight Ψ J.val=star (FiniteGaussPhase.angularFactor (primaryGenerator J.val))^3*
    Ψ (primaryGenerator J.val)^3/(Ideal.absNorm J.val:ℂ) from rfl]
  simp only [FiniteGaussPhase.angularFactor,completedMellinLength,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
    ←primaryGenerator_norm I.val hI,hni,hnj,map_mul,map_pow,star_mul,star_pow,
    Complex.star_def,map_div₀,Complex.conj_ofReal]
  field_simp [hi0,hj0]

lemma thetaPair_frequency_norm (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0) :
    ‖cuspFrequency (primaryGenerator I.val*(primaryGenerator J.val)^3)‖=
      thetaBesselScale*Real.sqrt (completedMellinLength (I,J)) := by
  rw [cuspFrequency_eq_thetaFrequencyScale,norm_mul,map_mul,map_pow,norm_mul,norm_pow]
  have he : completedMellinLength (I,J)=
      (‖eisEmbedding (primaryGenerator I.val)‖*‖eisEmbedding (primaryGenerator J.val)‖^3)^2 := by
    rw [completedMellinLength,←primaryGenerator_norm_sq I.val hI,←primaryGenerator_norm_sq J.val hJ]
    ring
  rw [he,Real.sqrt_sq (by positivity)]
  rfl

lemma thetaPair_derivative_coefficient (Ψ : Eis→*ℂ) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0)
    (hsq : Squarefree I.val) :
    (-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator I.val*(primaryGenerator J.val)^3)))*
      fixedThetaTwist Ψ (primaryGenerator I.val*(primaryGenerator J.val)^3)*
        star (sourceResidualFourierCoefficient (primaryGenerator I.val*(primaryGenerator J.val)^3))=
      thetaDerivativeScalar*(completedMellinCoefficient Ψ (I,J)*(completedMellinLength (I,J):ℂ)) := by
  have he := fixedThetaTwist_infinity_coefficient Ψ I.val J.val hI hJ hsq
  have he' := congrArg (fun z:ℂ=>infinityCoefficientScalar*z) he
  simp only [←mul_assoc,mul_inv_cancel₀ infinityCoefficientScalar_ne_zero,one_mul] at he'
  rw [completedCoefficient_mul_length Ψ I J hI hJ hsq,cuspFrequency_eq_thetaFrequencyScale,star_mul]
  unfold thetaDerivativeScalar
  calc
    _ = (-2*Real.pi*Complex.I*star thetaFrequencyScale)*
        star (eisEmbedding (primaryGenerator I.val*(primaryGenerator J.val)^3))*
          (star (sourceResidualFourierCoefficient (primaryGenerator I.val*(primaryGenerator J.val)^3))*
            fixedThetaTwist Ψ (primaryGenerator I.val*(primaryGenerator J.val)^3)) := by ring
    _ = _ := by rw [he'];ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def thetaTwistedSource (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv z

theorem thetaTwistedSource_wirtingerBar_eq_completedBesselProfile
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (thetaTwistedSource Ψ c hc v hv) 0=
      thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
  change horizontalWirtingerBar (traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv) 0 = _
  rw [traceTwistedConjugateSource_wirtingerBar_zero]
  simp only [fixedThetaQuotient_mk Ψ Q hΨ c hcQ]
  let w : Eis→ℂ := fun h=>(-2*Real.pi*Complex.I*star (cuspFrequency h))*
    fixedThetaTwist Ψ h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)
  have hw : ∀h:Eis,w h≠0→lambda^2∣h-1 := by
    intro h hwh
    by_contra hh
    exact hwh (by simp only [w,fixedThetaTwist_not_primary Ψ h hh,mul_zero,zero_mul])
  calc
    _ = ∑'h:Eis,w h*star (sourceResidualFourierCoefficient h) := by
      apply tsum_congr
      intro h
      dsimp only [w]
      ring
    _ = ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        w (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)*
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)) :=
      sourceFourier_tsum_primary_pairs w hw
    _ = thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
      rw [completedBesselProfile_primary_pairs,←tsum_mul_left]
      apply tsum_congr
      intro p
      let ip := primaryCubePairToMellinIndex p
      have he := thetaPair_derivative_coefficient Ψ ip.1 ip.2 p.1.property.2 p.2.property p.1.property.1
      have hn := thetaPair_frequency_norm ip.1 ip.2 p.1.property.2 p.2.property
      change (-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
          fixedThetaTwist Ψ (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)‖*v)*
          star (sourceResidualFourierCoefficient (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)) =
        thetaDerivativeScalar*((completedMellinCoefficient Ψ ip*(completedMellinLength ip:ℂ))*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v))
      rw [hn,show 4*Real.pi*(thetaBesselScale*Real.sqrt (completedMellinLength ip))*v=
        4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v by ring]
      calc
        _ = ((-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
            fixedThetaTwist Ψ (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)*
            star (sourceResidualFourierCoefficient (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
            (v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v) := by ring
        _ = _ := by rw [he];ring

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma horizontalWirtingerBar_finite_sum {ι : Type*} [Fintype ι]
    (f : ι→ℂ→ℂ) (weight : ι→ℂ) (z : ℂ)
    (h1 : ∀i,DifferentiableAt ℝ (fun t:ℝ=>f i (z+(t:ℂ))) 0)
    (hI : ∀i,DifferentiableAt ℝ (fun t:ℝ=>f i (z+(t:ℂ)*Complex.I)) 0) :
    horizontalWirtingerBar (fun w=>∑i,weight i*f i w) z=
      ∑i,weight i*horizontalWirtingerBar (f i) z := by
  unfold horizontalWirtingerBar
  rw [deriv_fun_sum (fun i hi=>(h1 i).const_mul (weight i)),
    deriv_fun_sum (fun i hi=>(hI i).const_mul (weight i))]
  simp only [deriv_const_mul_field,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma finiteConjugateSource_wirtingerBar_sum {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (finiteConjugateSource shift weight v hv) 0=
      ∑i,weight i*cuspBarProfile cubicSourceConjugateFunction (shift i) v := by
  have hd (i : ι) (direction : ℂ) : DifferentiableAt ℝ
      (fun t:ℝ=>cubicSourceConjugateFunction (upperPoint (((t:ℂ)*direction)+shift i) v hv)) 0 := by
    have he : (fun t:ℝ=>cubicSourceConjugateFunction (upperPoint (((t:ℂ)*direction)+shift i) v hv))=
        fun t:ℝ=>star (sourceBesselCoefficients.fullFunction ((3*(Real.pi:ℂ))*constantArithmeticResidue)
          (upperPoint (shift i+(t:ℂ)*direction) v hv)) := by
      funext t
      simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_eq_bessel,sourceBesselFunction,add_comm]
    rw [he]
    exact (sourceBesselCoefficients.fullFunction_horizontal_hasDerivAt _ v hv (shift i) direction 0).differentiableAt.star
  rw [show finiteConjugateSource shift weight v hv=
    fun w=>∑i,weight i*cubicSourceConjugateFunction (upperPoint (w+shift i) v hv) from rfl]
  rw [horizontalWirtingerBar_finite_sum _ weight 0
    (fun i=>by simpa only [zero_add,mul_one] using hd i 1)
    (fun i=>by simpa only [zero_add] using hd i Complex.I)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cuspBarProfile_positive _ _ _ hv]
  apply congrArg (fun z : ℂ => weight i * z)
  exact horizontalWirtingerBar_translate (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (shift i)

def thetaTwistedCuspProfile (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (v : ℝ) : ℂ :=
  ∑h:Eis⧸Ideal.span {c},finiteAdditiveFourierCoeff (quotientTrace c hc)
    (fixedThetaQuotient Ψ c) h*cuspBarProfile cubicSourceConjugateFunction (thetaFourierTranslation c h) v

theorem thetaTwistedCuspProfile_eq_completedBesselProfile
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
  rw [←thetaTwistedSource_wirtingerBar_eq_completedBesselProfile Ψ Q hΨ c hc hcQ v hv]
  exact (finiteConjugateSource_wirtingerBar_sum (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c)) v hv).symm

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.EntireMellinProfile -/

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
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma finite_mellin_entire {ι : Type*} [Fintype ι] (f : ι→ℝ→ℂ) (weight : ι→ℂ)
    (hf : ∀i,(∀s:ℂ,MellinConvergent (f i) s) ∧ Differentiable ℂ (mellin (f i))) :
    (∀s:ℂ,MellinConvergent (fun v=>∑i,weight i*f i v) s) ∧
      Differentiable ℂ (mellin (fun v=>∑i,weight i*f i v)) := by
  have hs (s : ℂ) (i : ι) : MellinConvergent (fun v=>weight i*f i v) s := by
    simpa only [smul_eq_mul] using (hf i).1 s |>.const_smul (weight i)
  have hsi (s : ℂ) (i : ι) : IntegrableOn (fun v:ℝ=>(v:ℂ)^(s-1)*(weight i*f i v)) (Set.Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul] using hs s i
  have he (s : ℂ) : mellin (fun v=>∑i,weight i*f i v) s=∑i,weight i*mellin (f i) s := by
    unfold mellin
    simp only [smul_eq_mul,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i hi=>hsi s i)]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [mellin,smul_eq_mul] using mellin_const_smul (f i) s (weight i)
  constructor
  · intro s
    change IntegrableOn (fun v:ℝ=>(v:ℂ)^(s-1)*(∑i,weight i*f i v)) (Set.Ioi 0)
    simpa only [IntegrableOn,Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i hi=>hsi s i)
  · rw [show mellin (fun v=>∑i,weight i*f i v)=(fun s=>∑i,weight i*mellin (f i) s) from funext he]
    exact Differentiable.fun_sum (fun i hi=>(hf i).2.const_mul (weight i))

lemma thetaTwistedCuspProfile_mellin_entire (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] :
    (∀s:ℂ,MellinConvergent (thetaTwistedCuspProfile Ψ c hc) s) ∧
      Differentiable ℂ (mellin (thetaTwistedCuspProfile Ψ c hc)) := by
  apply finite_mellin_entire
  intro h
  have he : thetaFourierTranslation c h=(-3:ℂ)*eisEmbedding (Quotient.out h)/eisEmbedding c := by
    rw [thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
  rw [he]
  exact conjugateSource_finite_twist_cusp_mellin_entire (Quotient.out h) c hc

theorem completedBesselProfile_mellin_entire_of_periodic
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) :
    (∀s:ℂ,MellinConvergent (completedBesselProfile Ψ thetaBesselScale) s) ∧
      Differentiable ℂ (mellin (completedBesselProfile Ψ thetaBesselScale)) := by
  have hf := thetaTwistedCuspProfile_mellin_entire Ψ c hc
  have he (v : ℝ) (hv : 0<v) :
      thetaDerivativeScalar⁻¹*thetaTwistedCuspProfile Ψ c hc v=
        completedBesselProfile Ψ thetaBesselScale v := by
    rw [thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hΨ c hc hcQ v hv,
      ←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]
  have hm (s : ℂ) : mellin (completedBesselProfile Ψ thetaBesselScale) s=
      thetaDerivativeScalar⁻¹*mellin (thetaTwistedCuspProfile Ψ c hc) s := by
    have hmul := mellin_const_smul (thetaTwistedCuspProfile Ψ c hc) s thetaDerivativeScalar⁻¹
    simp only [smul_eq_mul] at hmul
    rw [←hmul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp only [smul_eq_mul,he v hv]
  constructor
  · intro s
    have hi := (hf.1 s).const_smul thetaDerivativeScalar⁻¹
    apply hi.congr_fun _ measurableSet_Ioi
    intro v hv
    simp only [smul_eq_mul,he v hv]
  · rw [show mellin (completedBesselProfile Ψ thetaBesselScale)=
      (fun s=>thetaDerivativeScalar⁻¹*mellin (thetaTwistedCuspProfile Ψ c hc) s) from funext hm]
    exact hf.2.const_mul _

theorem completedBesselProfile_mellin_entire
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hQ : Q≠⊥)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) :
    (∀s:ℂ,MellinConvergent (completedBesselProfile Ψ (1/Real.sqrt 27)) s) ∧
      Differentiable ℂ (mellin (completedBesselProfile Ψ (1/Real.sqrt 27))) := by
  have h9 : (Ideal.span {(9:Eis)} : Ideal Eis)≠⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hN : Ideal.span {(9:Eis)}*Q≠⊥ := fun hz=>(Ideal.mul_eq_bot.mp hz).elim h9 hQ
  let c := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Q)
  have hc : c≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero _ hN
  let : Finite (Eis⧸Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  have hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  simpa only [thetaBesselScale_eq] using
    completedBesselProfile_mellin_entire_of_periodic Ψ Q hΨ c hc hcQ

end CubicEisenstein

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma mellin_eq_of_positive_eq (F G : ℝ→ℂ) (hFG : ∀v : ℝ,0<v→F v=G v) (s : ℂ) :
    mellin F s=mellin G s := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [hFG v hv]

lemma continuedBesselDirichlet_finite_sum {ι : Type*} [Fintype ι]
    (F : ι→ℝ→ℂ) (w : ι→ℂ) (q : ℝ) (s : ℂ)
    (hF : ∀i,MellinConvergent (F i) (2*s)) :
    continuedBesselDirichlet (fun v=>∑i,w i*F i v) q s=
      ∑i,w i*continuedBesselDirichlet (F i) q s := by
  have hi (i : ι) : IntegrableOn (fun v : ℝ=>(v:ℂ)^(2*s-1)*(w i*F i v)) (Set.Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul] using (hF i).const_smul (w i)
  have hm : mellin (fun v=>∑i,w i*F i v) (2*s)=∑i,w i*mellin (F i) (2*s) := by
    unfold mellin
    simp only [smul_eq_mul,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _=>hi i)]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mellin,smul_eq_mul] using mellin_const_smul (F i) (2*s) (w i)
  rw [continuedBesselDirichlet,hm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold continuedBesselDirichlet
  ring

lemma besselSmoothingIntegrand_finite_sum {ι : Type*} [Fintype ι]
    (F : ℝ→ℂ) (G : ι→ℝ→ℂ) (w : ι→ℂ)
    (hFG : ∀v : ℝ,0<v→F v=∑i,w i*G i v)
    (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ)
    (hG : ∀i,MellinConvergent (G i) (2*s)) :
    besselSmoothingIntegrand F q V X s=
      ∑i,w i*besselSmoothingIntegrand (G i) q V X s := by
  have hm := mellin_eq_of_positive_eq F (fun v=>∑i,w i*G i v) hFG (2*s)
  have hd : continuedBesselDirichlet F q s=
      continuedBesselDirichlet (fun v=>∑i,w i*G i v) q s := by
    simp only [continuedBesselDirichlet,hm]
  rw [besselSmoothingIntegrand,hd,continuedBesselDirichlet_finite_sum G w q s hG,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold besselSmoothingIntegrand
  ring

theorem besselSmoothingIntegrand_finite_integrable {ι : Type*} [Fintype ι]
    (F : ℝ→ℂ) (G : ι→ℝ→ℂ) (w : ι→ℂ)
    (hFG : ∀v : ℝ,0<v→F v=∑i,w i*G i v)
    (q : ℝ) (V : ℝ→ℂ) (X σ : ℝ)
    (hG : ∀i,∀t : ℝ,MellinConvergent (G i) (2*((σ:ℂ)+t*Complex.I)))
    (hi : ∀i,Integrable (fun t : ℝ=>besselSmoothingIntegrand (G i) q V X ((σ:ℂ)+t*Complex.I))) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((σ:ℂ)+t*Complex.I)) := by
  have hsum := integrable_finsetSum Finset.univ (fun i _=>(hi i).const_mul (w i))
  apply hsum.congr
  filter_upwards with t
  exact (besselSmoothingIntegrand_finite_sum F G w hFG q V X _ (fun i=>hG i t)).symm

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def unramifiedResidualCoefficient (h:Eis) :ℂ:=cubicBesselNormalizer h*unramifiedGaussResidue h

lemma primeCubicGauss_two_norm (p:Eis) (hp:Prime p) (hpp:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h) : ‖primeCubicGauss p hp hpp 2 h‖=‖eisEmbedding p‖ := by
  have he:=congrArg norm (primeCubicGauss_one_mul_two p hp hpp h hph)
  rw [norm_mul,primeCubicGauss_two_eq_star,norm_star,Complex.norm_natCast] at he
  have hn:=eisEmbedding_norm_sq_eq_absNorm_span p
  have hg:0≤‖primeCubicGauss p hp hpp 1 h‖:=norm_nonneg _
  have hr:0≤‖eisEmbedding p‖:=norm_nonneg _
  rw [primeCubicGauss_two_eq_star,norm_star]
  nlinarith

lemma unramifiedResidualCoefficient_prime_factor (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedResidualCoefficient (h*p)=
      (primeCubicGauss p hp hpp 2 h/(‖eisEmbedding p‖:ℂ))*unramifiedResidualCoefficient h := by
  rw [unramifiedResidualCoefficient,cubicBesselNormalizer_mul,
    unramifiedGaussResidue_prime_factor p hp hpp h hph,unramifiedResidualCoefficient]
  calc
    _=((‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ)))*
      primeCubicGauss p hp hpp 2 h*(cubicBesselNormalizer h*unramifiedGaussResidue h):=by ring
    _=_:=by rw [prime_normalizer_powers p hp.ne_zero]; ring

lemma unramifiedResidualCoefficient_prime_norm (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    ‖unramifiedResidualCoefficient (h*p)‖=‖unramifiedResidualCoefficient h‖ := by
  rw [unramifiedResidualCoefficient_prime_factor p hp hpp h hph,norm_mul,norm_div,
    primeCubicGauss_two_norm p hp hpp h hph,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)),one_mul]

theorem unramifiedGaussResidue_primary_cube (b:Eis) (hb:b≠0)
    (hbp:lambda^2∣b-1) (h:Eis) :
    unramifiedGaussResidue (h*b^3)=unramifiedGaussResidue h := by
  obtain ⟨s,hs,hpr⟩:=exists_primary_prime_factorization b hb hbp
  rw [←hs]
  clear hs hb hbp b
  induction s using Multiset.induction_on generalizing h with
  | empty=>simp
  | @cons p s ih=>
    have hp:=hpr p (Multiset.mem_cons_self _ _)
    have hs:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hpr q (Multiset.mem_cons_of_mem hq)
    rw [Multiset.prod_cons,show h*(p*s.prod)^3=(h*s.prod^3)*p^3 by ring,
      unramifiedGaussResidue_prime_cube p hp.1 hp.2]
    exact ih h hs

lemma unramifiedResidualCoefficient_primary_cube (b:Eis) (hb:b≠0)
    (hbp:lambda^2∣b-1) (h:Eis) :
    unramifiedResidualCoefficient (h*b^3)=
      (‖eisEmbedding b‖:ℂ)*unramifiedResidualCoefficient h := by
  rw [unramifiedResidualCoefficient,cubicBesselNormalizer_mul_cube h b hb,
    unramifiedGaussResidue_primary_cube b hb hbp h,unramifiedResidualCoefficient]
  ring

theorem unramifiedResidualCoefficient_prime_product_norm {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    ‖unramifiedResidualCoefficient (h*(∏i∈s,p i))‖=‖unramifiedResidualCoefficient h‖ := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      unramifiedResidualCoefficient_prime_norm (p i) hpi hpri _ hpb]
    exact ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))

theorem unramifiedResidualCoefficient_squarefree_cube_norm (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖=
      ‖eisEmbedding (primaryGenerator J)‖*‖unramifiedResidualCoefficient (u.val*lambda^m)‖ := by
  rw [unramifiedResidualCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  rw [primaryGenerator_squarefree_support I hI hsq]
  apply unramifiedResidualCoefficient_prime_product_norm
  · exact fun P hP=>primaryPrime_isPrime_of_mem I P hI hP
  · exact fun P hP=>(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  · exact primaryPrime_support_coprime I hI
  · intro P hP hd
    have hp:=primaryPrime_isPrime_of_mem I P hI hP
    have hpp:lambda^2∣primaryPrime P-1:=
      (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
    have hc:IsCoprime (u.val*lambda^m) (primaryPrime P):=
      (ramified_primary_coprime u m _ hpp).of_mul_left_right
    exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def threeRamifiedUnit :Eisˣ:=-(ramifiedOmegaUnit^2)
def traceRamifiedUnit :Eisˣ:=-ramifiedOmegaUnit

lemma three_eq_ramifiedUnit : (3:Eis)=(threeRamifiedUnit:Eis)*lambda^2 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  simp only [threeRamifiedUnit,Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,hl]
  calc
    (3:Eis)=3*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
    _=_:=by ring

lemma trace_eq_ramifiedUnit : ramifiedTraceLambda=(traceRamifiedUnit:Eis)*lambda := by
  have hw:=ramified_omega_relation
  simp only [traceRamifiedUnit,Units.val_neg,ramifiedOmegaUnit_val]
  change 1+2*omega=-omega*(omega-1)
  linear_combination hw

def ramifiedSixUnit (side:Bool) :RamifiedSixBranch→Eisˣ
  | .inl _=>threeRamifiedUnit*ramifiedCuspRoot side
  | .inr (.inl _)=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4*(-ramifiedCuspRoot side)
  | .inr (.inr (.inl _))=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4
  | .inr (.inr (.inr j))=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4*
      ramifiedCuspScaleUnit side*traceRamifiedUnit*ramifiedOmegaUnit^j.val

def ramifiedSixPower :RamifiedSixBranch→ℕ
  | .inl _=>2
  | .inr (.inl _)=>2
  | .inr (.inr (.inl _))=>2
  | .inr (.inr (.inr _))=>3

lemma ramifiedSixPower_bounds (i:RamifiedSixBranch) : 2≤ ramifiedSixPower i ∧ ramifiedSixPower i≤3 := by
  rcases i with i|i
  · norm_num [ramifiedSixPower]
  rcases i with i|i
  · norm_num [ramifiedSixPower]
  rcases i with i|i <;> norm_num [ramifiedSixPower]

lemma unitCuspUnramifiedIndex_multiplier (u t:Eisˣ) (h:Eis) :
    unitCuspUnramifiedIndex u t h=(3*(↑u⁻¹:Eis)^4*(t:Eis))*h := by
  unfold unitCuspUnramifiedIndex
  have ht:(t:Eis)*(↑t⁻¹:Eis)=1:=by simp
  calc
    _=(3*(↑u⁻¹:Eis)^4*(t:Eis)*h)*((t:Eis)*(↑t⁻¹:Eis)):=by ring
    _=_:=by rw [ht,mul_one]

theorem ramifiedSixIndex_multiplier (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ramifiedSixIndex side h hf i=
      ((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i))*h := by
  rcases i with i|i
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_one,inv_one,one_pow]
    rw [three_eq_ramifiedUnit]
    ring
  rcases i with i|i
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val]
    rw [three_eq_ramifiedUnit]
    ring
  rcases i with i|j
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_one,mul_one]
    rw [three_eq_ramifiedUnit]
    ring
  · have hh:=onceCuspFrequencyQuotient_spec (ramifiedCuspScaleUnit side) h hf j
    change 3*((↑(-ramifiedCuspRoot side)⁻¹:Eis)^2*
      (onceCuspScale (ramifiedCuspScaleUnit side)*omega^j.val))^2*
      onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf j=_
    calc
      _=3*(↑(-ramifiedCuspRoot side)⁻¹:Eis)^4*
          (onceCuspScale (ramifiedCuspScaleUnit side)*omega^j.val)*h:=by
        conv_rhs => rw [hh]
        ring
      _=_:=by
        simp only [ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val,
          ramifiedOmegaUnit_val,onceCuspScale]
        rw [three_eq_ramifiedUnit,trace_eq_ramifiedUnit]
        ring

theorem ramifiedBesselValue_prime_power_vanish (side:Bool) (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ) (hk:k%3=2) :
    ramifiedBesselValue side (h*p^k)=0 := by
  unfold ramifiedBesselValue
  split_ifs with hf
  · have hr:ramifiedArithmeticResidue side (h*p^k) hf=0:=by
      unfold ramifiedArithmeticResidue
      apply Finset.sum_eq_zero
      intro i hi
      rw [ramifiedSixIndex_multiplier]
      have hc:IsCoprime ((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i)) p:=
        (ramified_primary_coprime (ramifiedSixUnit side i) (ramifiedSixPower i) p hpp).of_mul_left_right
      have hnot:¬p∣((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i))*h:=by
        intro hd
        rcases hp.dvd_mul.mp hd with hd|hd
        · exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)
        · exact hph hd
      rw [←mul_assoc,unramifiedGaussResidue_prime_power_table p hp hpp _ hnot,hk]
      norm_num
    rw [hr,mul_zero,zero_div]
  · rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_norm_third (u:Eisˣ) (m:ℕ) :
    ‖eisEmbedding (u.val*lambda^m)‖^(1/3:ℝ)=(3:ℝ)^((m:ℝ)/6) := by
  have hs:‖eisEmbedding (u.val*lambda^m)‖^2=(3:ℝ)^m:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ramifiedElement_absNorm,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _=(‖eisEmbedding (u.val*lambda^m)‖^2)^(1/6:ℝ):=by
      rw [←Real.rpow_natCast_mul (norm_nonneg _)]
      congr 1
      norm_num
    _=((3:ℝ)^m)^(1/6:ℝ):=by rw [hs]
    _=(3:ℝ)^((m:ℝ)/6):=by
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)]
      congr 1
      ring

lemma cubicBesselNormalizer_ramified_mul_norm (h:Eis) (u:Eisˣ) (m:ℕ) :
    ‖cubicBesselNormalizer (h*(u.val*lambda^m))‖=
      ‖cubicBesselNormalizer h‖*(3:ℝ)^((m:ℝ)/6) := by
  have hp:0<‖eisEmbedding (u.val*lambda^m)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (ramifiedElement_ne_zero u m))
  rw [cubicBesselNormalizer_mul,norm_mul]
  have he:=Complex.norm_cpow_eq_rpow_re_of_pos hp (1/3:ℂ)
  have hre:(1/3:ℂ).re=(1/3:ℝ):=by norm_num
  rw [hre,ramified_norm_third] at he
  rw [he]
  ring

def unramifiedCoefficientBaseBound :ℝ:=
  ‖cubicBesselNormalizer 1‖*ramifiedResidueFamilyMass 1

lemma unramifiedCoefficientBaseBound_nonneg :0≤unramifiedCoefficientBaseBound:=
  mul_nonneg (norm_nonneg _) (ramifiedResidueFamilyMass_nonneg _)

lemma unramifiedResidualCoefficient_ramified_bound (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient (u.val*lambda^m)‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^((m:ℝ)/6) := by
  have hc:‖cubicBesselNormalizer (u.val*lambda^m)‖=
      ‖cubicBesselNormalizer 1‖*(3:ℝ)^((m:ℝ)/6):=by
    simpa only [one_mul] using cubicBesselNormalizer_ramified_mul_norm 1 u m
  rw [unramifiedResidualCoefficient,norm_mul,hc,unramifiedCoefficientBaseBound]
  have he:=mul_le_mul_of_nonneg_left (unramifiedGaussResidue_unit_lambda_norm_le u m)
    (mul_nonneg (norm_nonneg (cubicBesselNormalizer 1)) (Real.rpow_nonneg (show (0:ℝ)≤3 by norm_num) ((m:ℝ)/6)))
  exact he.trans_eq (by ring)

theorem unramifiedResidualCoefficient_squarefree_cube_bound (I J:Ideal Eis)
    (hI:CompletedGauss.primaryGenerator I≠0) (hJ:CompletedGauss.primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient ((u.val*lambda^m)*CompletedGauss.primaryGenerator I*
      (CompletedGauss.primaryGenerator J)^3)‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (CompletedGauss.primaryGenerator J)‖ := by
  rw [unramifiedResidualCoefficient_squarefree_cube_norm I J hI hJ hsq u m]
  exact (mul_le_mul_of_nonneg_left (unramifiedResidualCoefficient_ramified_bound u m)
    (norm_nonneg _)).trans_eq (by ring)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSixWeight_norm_le_one (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ‖ramifiedSixWeight side h hf i (4/3)‖≤1 := by
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  · unfold ramifiedSixWeight
    dsimp only
    split_ifs
    · simp only [norm_mul,breveE_norm,mul_one]
      norm_num only [norm_inv,norm_div,norm_one,Complex.norm_ofNat]
      have hw:=ramifiedWeight_norm_scalar 1
      norm_num only [pow_one,Nat.cast_ofNat] at hw
      have hb:=ramifiedDecayRatio_lt_one.le
      nlinarith [norm_nonneg ((3:ℂ)^(-(4/3:ℂ)))]
    · simp

lemma ramifiedSixIndex_squarefree_cube (side:Bool) (u:Eisˣ) (m:ℕ) (n b:Eis)
    (hf:(3:Eis)∣((u.val*lambda^m)*n*b^3)-onceCuspScale (ramifiedCuspScaleUnit side))
    (i:RamifiedSixBranch) :
    ramifiedSixIndex side ((u.val*lambda^m)*n*b^3) hf i=
      (((ramifiedSixUnit side i*u:Eisˣ):Eis)*lambda^(ramifiedSixPower i+m))*n*b^3 := by
  rw [ramifiedSixIndex_multiplier,Units.val_mul,pow_add]
  ring

lemma ramifiedSix_normalized_term_bound (side:Bool) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ)
    (hf:(3:Eis)∣((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)-
      onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ‖cubicBesselNormalizer ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)*
      unramifiedGaussResidue (ramifiedSixIndex side
        ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3) hf i)‖≤
      (unramifiedCoefficientBaseBound*(3:ℝ)^(1/2:ℝ))*(3:ℝ)^((m:ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖ := by
  let h:=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3
  let idx:=ramifiedSixIndex side h hf i
  have hc:‖cubicBesselNormalizer idx‖=
      ‖cubicBesselNormalizer h‖*(3:ℝ)^((ramifiedSixPower i:ℝ)/6):=by
    dsimp only [idx]
    rw [ramifiedSixIndex_multiplier,mul_comm]
    exact cubicBesselNormalizer_ramified_mul_norm h (ramifiedSixUnit side i) (ramifiedSixPower i)
  have hp:1≤(3:ℝ)^((ramifiedSixPower i:ℝ)/6):=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hcle:‖cubicBesselNormalizer h‖≤‖cubicBesselNormalizer idx‖:=by
    rw [hc]
    exact le_mul_of_one_le_right (norm_nonneg _) hp
  have hnorm:‖unramifiedResidualCoefficient idx‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖:=by
    dsimp only [idx,h]
    rw [ramifiedSixIndex_squarefree_cube]
    exact unramifiedResidualCoefficient_squarefree_cube_bound I J hI hJ hsq
      (ramifiedSixUnit side i*u) (ramifiedSixPower i+m)
  have hexp:((ramifiedSixPower i+m:ℕ):ℝ)/6≤(m:ℝ)/6+1/2:=by
    have hr:(ramifiedSixPower i:ℝ)≤3:=by exact_mod_cast (ramifiedSixPower_bounds i).2
    push_cast
    linarith
  have hpow:(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)≤
      (3:ℝ)^((m:ℝ)/6)*(3:ℝ)^(1/2:ℝ):=by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc
    _≤‖unramifiedResidualCoefficient idx‖:=by
      rw [unramifiedResidualCoefficient,norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right hcle (norm_nonneg _)
    _≤unramifiedCoefficientBaseBound*(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖:=hnorm
    _≤unramifiedCoefficientBaseBound*((3:ℝ)^((m:ℝ)/6)*(3:ℝ)^(1/2:ℝ))*
        ‖eisEmbedding (primaryGenerator J)‖:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow unramifiedCoefficientBaseBound_nonneg)
        (norm_nonneg _)
    _=_:=by ring

theorem ramifiedBesselValue_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(side:Bool) (I J:Ideal Eis),
      primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  let V:ℂ:=((9*Real.sqrt 3/2:ℝ):ℂ)
  let A:ℝ:=‖(3:ℂ)^(2/3:ℂ)‖*‖V⁻¹‖
  let B:ℝ:=unramifiedCoefficientBaseBound*(3:ℝ)^(1/2:ℝ)
  have hA:0≤A:=mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hB:0≤B:=mul_nonneg unramifiedCoefficientBaseBound_nonneg (Real.rpow_nonneg (by norm_num) _)
  refine ⟨1+6*A*B,by positivity,?_⟩
  intro side I J hI hJ hsq u m
  let h:=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3
  let D:ℝ:=B*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖
  have hD:0≤D:=by dsimp only [D]; positivity
  unfold ramifiedBesselValue
  split_ifs with hf
  · have hs:‖cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf‖≤6*D:=by
      have he:cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf=
          ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i (4/3)*
            (cubicBesselNormalizer h*unramifiedGaussResidue (ramifiedSixIndex side h hf i)):=by
        rw [ramifiedArithmeticResidue,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      calc
        _≤∑i:RamifiedSixBranch,‖ramifiedSixWeight side h hf i (4/3)*
            (cubicBesselNormalizer h*unramifiedGaussResidue (ramifiedSixIndex side h hf i))‖:=norm_sum_le _ _
        _≤∑i:RamifiedSixBranch,D:=by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (ramifiedSixWeight_norm_le_one side h hf i) (norm_nonneg _)).trans
            (by simpa only [one_mul,D,B,h] using ramifiedSix_normalized_term_bound side I J hI hJ hsq u m hf i)
        _=6*D:=by simp [RamifiedSixBranch]
    have he:‖(3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf/V‖≤A*(6*D):=by
      rw [div_eq_mul_inv,mul_assoc ((3:ℂ)^(2/3:ℂ)),norm_mul,norm_mul]
      dsimp only [A]
      nlinarith [mul_le_mul_of_nonneg_left hs (norm_nonneg ((3:ℂ)^(2/3:ℂ))),norm_nonneg (V⁻¹)]
    refine he.trans ?_
    dsimp only [A,B,D]
    have hnonneg:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
    nlinarith
  · rw [norm_zero]
    positivity

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.RamifiedValuation -/

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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedFunction_valuation_ne_two (F:Eis→ℂ)
    (hzero:∀(p:Eis),Prime p→lambda^2∣p-1→∀h:Eis,¬p∣h→∀k:ℕ,k%3=2→F (h*p^k)=0)
    (I P:Ideal Eis) (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (u:Eisˣ) (m:ℕ) (hF:F ((u.val*lambda^m)*primaryGenerator I)≠0) :
    (normalizedFactors I).count P%3≠2 := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hprime:=prime_of_normalized_factor P hP
  let p:=primaryPrime P
  have hp0:p≠0:=primaryPrime_factor_ne_zero I P hI hP
  have hps:=primaryPrime_spec P hp0
  have hp:Prime p:=primaryPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen:primaryGenerator I=p^(multiplicity P I)*primaryGenerator J:=by
    calc
      _=primaryGenerator (P^(multiplicity P I)*J):=congrArg primaryGenerator hJ
      _=p^(multiplicity P I)*primaryGenerator J:=by
        rw [primaryGenerator_mul,primaryGenerator_pow]
        have he:primaryGenerator P=p:=by
          rw [←hps.2.2.1,primaryGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hgJ:primaryGenerator J≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,mul_zero])
  have hpd:¬p∣primaryGenerator J:=by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le,←hps.2.2.1,←(primaryGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hbase:¬p∣(u.val*lambda^m)*primaryGenerator J:=by
    intro hd
    rcases hp.dvd_mul.mp hd with hd|hd
    · exact hp.not_isUnit (((ramified_primary_coprime u m p hps.2.2.2).of_mul_left_right).symm.isUnit_of_dvd hd)
    · exact hpd hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hF
  rw [hgen,show (u.val*lambda^m)*(p^(multiplicity P I)*primaryGenerator J)=
    ((u.val*lambda^m)*primaryGenerator J)*p^(multiplicity P I) by ring]
  exact hzero p hp hps.2.2.2 _ hbase _ hm

theorem ramifiedBesselValue_squarefree_cube_support (side:Bool) (h:Eis) (hh:h≠0)
    (hB:ramifiedBesselValue side h≠0) :
    ∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨n,u,m,hn,he⟩:=exists_primary_unit_lambda_factor h hh
  let T:Ideal Eis:=Ideal.span {n}
  have hT:primaryGenerator T=n:=primaryGenerator_span n (primary_ne_zero n hn) hn
  have hT0:primaryGenerator T≠0:=by rw [hT]; exact primary_ne_zero n hn
  have hFT:ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator T)≠0:=by
    rw [hT,mul_comm]
    rwa [←he]
  have hv:∀P∈normalizedFactors T,(normalizedFactors T).count P%3≠2:=by
    intro P hP
    exact ramifiedFunction_valuation_ne_two (ramifiedBesselValue side)
      (fun p hp hpp h hph k hk=>ramifiedBesselValue_prime_power_vanish side p hp hpp h hph k hk)
      T P hT0 hP u m hFT
  have hparts:=thetaParts_mul_cube T (primaryGenerator_ne_zero_ideal T hT0) hv
  have hgen:primaryGenerator T=primaryGenerator (thetaSquarefreePart T)*
      (primaryGenerator (thetaCubePart T))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart T*thetaCubePart T^3):=congrArg primaryGenerator hparts.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_mul])
  have hC:primaryGenerator (thetaCubePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  refine ⟨u,m,thetaSquarefreePart T,thetaCubePart T,thetaSquarefreePart_squarefree T,hA,hC,?_⟩
  rw [he,←hT,hgen]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma onceCuspScale_not_three_dvd (t:Eisˣ) : ¬(3:Eis)∣onceCuspScale t := by
  rintro ⟨z,hz⟩
  have hq:Ideal.absNorm (Ideal.span {onceCuspScale t})=3:=by
    simpa only [Fin.val_zero,pow_zero,mul_one] using onceCusp_q_absNorm t 0
  have he:=congrArg (fun x:Eis=>Ideal.absNorm (Ideal.span {x})) hz
  rw [hq,←Ideal.span_singleton_mul_span_singleton,map_mul,three_absNorm] at he
  omega

lemma onceCuspScale_lambda_dvd (t:Eisˣ) : lambda∣onceCuspScale t := by
  refine ⟨(t:Eis)*(traceRamifiedUnit:Eis),?_⟩
  rw [onceCuspScale,trace_eq_ramifiedUnit]
  ring

theorem ramifiedBesselValue_exact_lambda_valuation (side:Bool) (h:Eis)
    (hb:ramifiedBesselValue side h≠0) : lambda∣h ∧ ¬lambda^2∣h := by
  have hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side):=by
    by_contra hnot
    exact hb (by simp only [ramifiedBesselValue,dite_eq_right hnot])
  have hl3:lambda∣(3:Eis):=
    (dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
  constructor
  · have hd:=hl3.trans hf
    simpa only [sub_add_cancel] using dvd_add hd
      (onceCuspScale_lambda_dvd (ramifiedCuspScaleUnit side))
  · intro h2
    have h3:(3:Eis)∣h:=three_dvd_lambda_sq.trans h2
    have hq:(3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit side):=by
      convert dvd_sub h3 hf using 1 ; ring
    exact onceCuspScale_not_three_dvd _ hq

theorem ramifiedBesselValue_once_squarefree_cube_support (side:Bool) (h:Eis)
    (hb:ramifiedBesselValue side h≠0) :
    ∃(u:Eisˣ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨hl,hnot⟩:=ramifiedBesselValue_exact_lambda_valuation side h hb
  have hh:h≠0:=by intro hz; exact hnot (hz▸dvd_zero _)
  obtain ⟨u,m,I,J,hsq,hI,hJ,hfactor⟩:=ramifiedBesselValue_squarefree_cube_support side h hh hb
  have hm2:¬2≤ m:=by
    intro hm
    apply hnot
    rw [hfactor]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (pow_dvd_pow lambda hm) _) _) _
  have hm0:m≠0:=by
    intro hm
    subst m
    rw [pow_zero,mul_one] at hfactor
    have hu:IsCoprime lambda (u:Eis):=⟨0,(↑u⁻¹:Eis),by simp⟩
    have hni:IsCoprime lambda (primaryGenerator I):=coprime_of_dvd_sub_one lambda _
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec I hI).2)
    have hnj:IsCoprime lambda (primaryGenerator J):=coprime_of_dvd_sub_one lambda _
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec J hJ).2)
    have hc:IsCoprime lambda h:=by rw [hfactor]; exact (hu.mul_right hni).mul_right hnj.pow_right
    exact residue_lambda_prime.not_isUnit (hc.isUnit_of_dvd hl)
  have hm:m=1:=by omega
  exact ⟨u,I,J,hsq,hI,hJ,by simpa only [hm,pow_one] using hfactor⟩

theorem ramifiedBesselValue_once_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(side:Bool) (I J:Ideal Eis),
      primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→∀u:Eisˣ,
      ‖ramifiedBesselValue side ((u.val*lambda)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*‖eisEmbedding (primaryGenerator J)‖ := by
  obtain ⟨C,hC,hbound⟩:=ramifiedBesselValue_squarefree_cube_bound
  refine ⟨C*(3:ℝ)^(1/6:ℝ),by positivity,?_⟩
  intro side I J hI hJ hsq u
  simpa only [pow_one,Nat.cast_one] using hbound side I J hI hJ hsq u 1

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_prime_norm (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    ‖sourceResidualFourierCoefficient (h*p)‖=‖sourceResidualFourierCoefficient h‖ := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hpp hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hpp h hph,norm_mul,norm_div,
    primeCubicGauss_two_norm p hp hpp (9*h) hp9,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)),one_mul]

theorem sourceResidualFourierCoefficient_prime_product_norm {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    ‖sourceResidualFourierCoefficient (h*(∏i∈s,p i))‖=‖sourceResidualFourierCoefficient h‖ := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      sourceResidualFourierCoefficient_prime_norm (p i) hpi hpri _ hpb]
    exact ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))

lemma sourceResidualFourierCoefficient_ramified_bound (u:Eisˣ) (m:ℕ) :
    ‖sourceResidualFourierCoefficient (u.val*lambda^m)‖≤
      (‖cubicBesselNormalizer 1‖*(9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1))*
        (3:ℝ)^((m:ℝ)/6) := by
  have hc:‖cubicBesselNormalizer (u.val*lambda^m)‖=
      ‖cubicBesselNormalizer 1‖*(3:ℝ)^((m:ℝ)/6):=by
    simpa only [one_mul] using cubicBesselNormalizer_ramified_mul_norm 1 u m
  rw [sourceResidualFourierCoefficient,norm_mul,hc]
  exact (mul_le_mul_of_nonneg_left (sourceArithmeticResidue_unit_lambda_bound u m)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (show (0:ℝ)≤3 by norm_num) ((m:ℝ)/6)))).trans_eq (by ring)

lemma sourceResidualFourierCoefficient_squarefree_cube_norm (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖=
      ‖eisEmbedding (primaryGenerator J)‖*‖sourceResidualFourierCoefficient (u.val*lambda^m)‖ := by
  rw [sourceResidualFourierCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2 _
    (mul_ne_zero (ramifiedElement_ne_zero u m) hI),norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  rw [primaryGenerator_squarefree_support I hI hsq]
  apply sourceResidualFourierCoefficient_prime_product_norm
  · exact fun P hP=>primaryPrime_isPrime_of_mem I P hI hP
  · exact fun P hP=>(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  · exact primaryPrime_support_coprime I hI
  · intro P hP hd
    have hp:=primaryPrime_isPrime_of_mem I P hI hP
    have hpp:lambda^2∣primaryPrime P-1:=
      (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
    have hc:IsCoprime (u.val*lambda^m) (primaryPrime P):=
      (ramified_primary_coprime u m _ hpp).of_mul_left_right
    exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)

theorem sourceResidualFourierCoefficient_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→
      Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  let C:ℝ:=‖cubicBesselNormalizer 1‖*(9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1)
  have hC:0≤C:=by dsimp only [C]; exact mul_nonneg (norm_nonneg _) (mul_nonneg
    (mul_nonneg (by norm_num) ramifiedSourceFamilyConstant_nonneg) (ramifiedResidueFamilyMass_nonneg _))
  refine ⟨1+C,by positivity,?_⟩
  intro I J hI hJ hsq u m
  rw [sourceResidualFourierCoefficient_squarefree_cube_norm I J hI hJ hsq u m]
  have he:=mul_le_mul_of_nonneg_left (sourceResidualFourierCoefficient_ramified_bound u m)
    (norm_nonneg (eisEmbedding (primaryGenerator J)))
  have hz:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
  dsimp only [C] at *
  nlinarith

theorem three_cusp_coefficients_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→
      Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ ∧
      ∀side:Bool,‖ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  obtain ⟨Cs,hCs,hs⟩:=sourceResidualFourierCoefficient_squarefree_cube_bound
  obtain ⟨Cr,hCr,hr⟩:=ramifiedBesselValue_squarefree_cube_bound
  refine ⟨Cs+Cr,by positivity,?_⟩
  intro I J hI hJ hsq u m
  have hz:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
  constructor
  · exact (hs I J hI hJ hsq u m).trans (by nlinarith)
  · intro side
    exact (hr side I J hI hJ hsq u m).trans (by nlinarith)

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_prime_power_vanish (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ) (hk:k%3=2) :
    sourceResidualFourierCoefficient (h*p^k)=0 := by
  rw [sourceResidualFourierCoefficient,sourceArithmeticResidue_prime_power_table p hp hpp h hph k,hk]
  norm_num

theorem sourceResidualFourierCoefficient_full_squarefree_cube_support (h:Eis) (hh:h≠0)
    (hB:sourceResidualFourierCoefficient h≠0) :
    ∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨n,u,m,hn,he⟩:=exists_primary_unit_lambda_factor h hh
  let T:Ideal Eis:=Ideal.span {n}
  have hT:primaryGenerator T=n:=primaryGenerator_span n (primary_ne_zero n hn) hn
  have hT0:primaryGenerator T≠0:=by rw [hT]; exact primary_ne_zero n hn
  have hFT:sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator T)≠0:=by
    rw [hT,mul_comm]
    rwa [←he]
  have hv:∀P∈normalizedFactors T,(normalizedFactors T).count P%3≠2:=by
    intro P hP
    exact ramifiedFunction_valuation_ne_two (sourceResidualFourierCoefficient)
      (fun p hp hpp h hph k hk=>sourceResidualFourierCoefficient_prime_power_vanish p hp hpp h hph k hk)
      T P hT0 hP u m hFT
  have hparts:=thetaParts_mul_cube T (primaryGenerator_ne_zero_ideal T hT0) hv
  have hgen:primaryGenerator T=primaryGenerator (thetaSquarefreePart T)*
      (primaryGenerator (thetaCubePart T))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart T*thetaCubePart T^3):=congrArg primaryGenerator hparts.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_mul])
  have hC:primaryGenerator (thetaCubePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  refine ⟨u,m,thetaSquarefreePart T,thetaCubePart T,thetaSquarefreePart_squarefree T,hA,hC,?_⟩
  rw [he,←hT,hgen]
  ring

end

section
open scoped Classical BigOperators

open ActualEisensteinCubic CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev ThetaPrimaryCubePair :=
  {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
  {J:Ideal Eis // primaryGenerator J≠0}

def thetaPrimaryProduct (p : ThetaPrimaryCubePair) : GoodIdeal :=
  ⟨p.1.val*p.2.val^3,by
    rw [primaryGenerator_mul,primaryGenerator_pow]
    exact mul_ne_zero p.1.property.2 (pow_ne_zero 3 p.2.property)⟩

lemma thetaPrimaryProduct_injective : Function.Injective thetaPrimaryProduct := by
  intro p q he
  have hprod : p.1.val*p.2.val^3=q.1.val*q.2.val^3 := congrArg Subtype.val he
  have h := squarefree_cube_decomposition_unique
    (primaryGenerator_ne_zero_ideal _ p.2.property)
    (primaryGenerator_ne_zero_ideal _ q.2.property) p.1.property.1 q.1.property.1 hprod
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

abbrev ThetaFullIndex := Eisˣ × ℕ × ThetaPrimaryCubePair

def thetaFullFrequency (p : ThetaFullIndex) : Eis :=
  (p.1.val*lambda^p.2.1)*primaryGenerator p.2.2.1.val*
    (primaryGenerator p.2.2.2.val)^3

lemma thetaFullFrequency_product (p : ThetaFullIndex) :
    thetaFullFrequency p=p.1.val*(lambda^p.2.1*primaryGenerator (thetaPrimaryProduct p.2.2).val) := by
  simp only [thetaFullFrequency,thetaPrimaryProduct,primaryGenerator_mul,primaryGenerator_pow]
  ring

lemma thetaFullFrequency_ne_zero (p : ThetaFullIndex) : thetaFullFrequency p≠0 := by
  rw [thetaFullFrequency_product]
  exact mul_ne_zero p.1.ne_zero
    (mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      (thetaPrimaryProduct p.2.2).property)

lemma thetaFullFrequency_span (p : ThetaFullIndex) :
    Ideal.span {thetaFullFrequency p}=ramifiedIdeal^p.2.1*(thetaPrimaryProduct p.2.2).val := by
  rw [thetaFullFrequency_product,Ideal.span_singleton_mul_left_unit p.1.isUnit,
    lambdaFactor_generator_span]

theorem thetaFullFrequency_injective : Function.Injective thetaFullFrequency := by
  rintro ⟨u,m,p⟩ ⟨v,n,q⟩ he
  have hs := congrArg (fun x:Eis=>Ideal.span {x}) he
  rw [thetaFullFrequency_span,thetaFullFrequency_span] at hs
  have hmap : lambdaFactorMap (m,thetaPrimaryProduct p)=lambdaFactorMap (n,thetaPrimaryProduct q) :=
    Subtype.ext hs
  have hij := lambdaFactorMap_bijective.1 hmap
  have hmn : m=n := congrArg Prod.fst hij
  have hpq : p=q := thetaPrimaryProduct_injective (congrArg Prod.snd hij)
  subst n
  subst q
  have huv : u=v := by
    apply Units.ext
    have hh : lambda^m*primaryGenerator (thetaPrimaryProduct p).val≠0 :=
      mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
        (thetaPrimaryProduct p).property
    apply mul_right_cancel₀ hh
    simpa only [thetaFullFrequency_product] using he
  subst v
  rfl

end

section
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

structure SourceCuspDatum where
  gamma : levelTwo
  index : Fin 3
  lower_ne_zero :
    (integralComplexMatrix (gamma:SL(2,Eis))*integralComplexMatrix (cuspRepresentative index)) 1 0≠0

namespace SourceCuspDatum

def matrix (d : SourceCuspDatum) : SL(2,ℂ) :=
  integralComplexMatrix (d.gamma:SL(2,Eis))*integralComplexMatrix (cuspRepresentative d.index)
def point (d : SourceCuspDatum) : ℂ := d.matrix 0 0/d.matrix 1 0
def dualPoint (d : SourceCuspDatum) : ℂ := -d.matrix 1 1/d.matrix 1 0
def heightScale (d : SourceCuspDatum) : ℝ := ‖d.matrix 1 0‖^2
def multiplier (d : SourceCuspDatum) : ℂ := -star (levelTwoComplexCharacter d.gamma)/(d.matrix 1 0)^2

lemma heightScale_pos (d : SourceCuspDatum) : 0<d.heightScale :=
  sq_pos_of_pos (norm_pos_iff.mpr d.lower_ne_zero)

lemma multiplier_norm (d : SourceCuspDatum) : ‖d.multiplier‖=d.heightScale⁻¹ := by
  rw [multiplier,norm_div,norm_neg,norm_star,norm_levelTwoComplexCharacter,norm_pow,one_div]
  rfl

lemma multiplier_ne_zero (d : SourceCuspDatum) : d.multiplier≠0 := by
  intro hz
  have h:=d.multiplier_norm
  rw [hz,norm_zero] at h
  exact (inv_pos.mpr d.heightScale_pos).ne' h.symm

end SourceCuspDatum

lemma exists_sourceCuspDatum (a c : Eis) (hc : c≠0) :
    ∃d:SourceCuspDatum,d.point=eisEmbedding a/eisEmbedding c := by
  obtain ⟨M,hMc,hratio⟩:=exists_integral_matrix_cusp_ratio a c hc
  obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
  let g:SL(2,ℂ):=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j)
  have he:integralComplexMatrix M=g*integralComplexMatrix T:=by
    rw [hM,map_mul,map_mul]
  have ht:integralComplexMatrix T 1 0=0:=by rw [integralComplexMatrix_apply,hT,map_zero]
  have hmc:(g*integralComplexMatrix T) 1 0≠0:=by
    rw [←he,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hMc
  obtain ⟨hg,hr⟩:=upper_triangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  refine ⟨⟨G,j,hg⟩,?_⟩
  change g 0 0/g 1 0=_
  rw [←hr,←he]
  exact hratio

def rationalSourceCusp (a c : Eis) (hc : c≠0) : SourceCuspDatum :=
  (exists_sourceCuspDatum a c hc).choose

lemma rationalSourceCusp_point (a c : Eis) (hc : c≠0) :
    (rationalSourceCusp a c hc).point=eisEmbedding a/eisEmbedding c :=
  (exists_sourceCuspDatum a c hc).choose_spec

def sourceCuspZFamily (j : Fin 3) (z : ℂ) : ℝ→ℂ :=
  cuspZProfile (fun w=>cubicSourceConjugateFunction (integralComplexMatrix (cuspRepresentative j) • w)) z

theorem SourceCuspDatum.reflection (d : SourceCuspDatum) (v : ℝ) (hv : 0<v) :
    cuspBarProfile cubicSourceConjugateFunction d.point v=
      d.multiplier/(v:ℂ)^2*sourceCuspZFamily d.index d.dualPoint ((d.heightScale*v)⁻¹) := by
  have he:=cuspBarProfile_conjugate_reflection_levelTwo d.gamma d.matrix
    (integralComplexMatrix (cuspRepresentative d.index)) rfl d.lower_ne_zero v hv
  rw [reflectedCuspProfile_eq_inv_square] at he
  exact he

def finiteTwistCusp (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) : SourceCuspDatum :=
  rationalSourceCusp (-3*Quotient.out h) c hc

lemma finiteTwistCusp_point (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) :
    (finiteTwistCusp c hc h).point=thetaFourierTranslation c h := by
  rw [finiteTwistCusp,rationalSourceCusp_point,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
  simp only [map_mul,map_neg,map_ofNat]

theorem thetaTwistedCuspProfile_reflection_of_data (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd : ∀h,(d h).point=thetaFourierTranslation c h) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((d h).multiplier/(v:ℂ)^2*
          sourceCuspZFamily (d h).index (d h).dualPoint (((d h).heightScale*v)⁻¹)) := by
  unfold thetaTwistedCuspProfile
  apply Finset.sum_congr rfl
  intro h hh
  rw [←hd h,(d h).reflection v hv]

theorem thetaTwistedCuspProfile_reflection (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((finiteTwistCusp c hc h).multiplier/(v:ℂ)^2*
          sourceCuspZFamily (finiteTwistCusp c hc h).index (finiteTwistCusp c hc h).dualPoint
            (((finiteTwistCusp c hc h).heightScale*v)⁻¹)) := by
  exact thetaTwistedCuspProfile_reflection_of_data Ψ c hc (finiteTwistCusp c hc)
    (finiteTwistCusp_point c hc) v hv

theorem completedBesselProfile_finite_cusp_reflection
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (v : ℝ) (hv : 0<v) :
    thetaDerivativeScalar*CompletedGauss.completedBesselProfile Ψ thetaBesselScale v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((finiteTwistCusp c hc h).multiplier/(v:ℂ)^2*
          sourceCuspZFamily (finiteTwistCusp c hc h).index (finiteTwistCusp c hc h).dualPoint
            (((finiteTwistCusp c hc h).heightScale*v)⁻¹)) := by
  rw [←thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hΨ c hc hcQ v hv]
  exact thetaTwistedCuspProfile_reflection Ψ c hc v hv

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

local notation "Eis" => ActualEisensteinCubic.O

lemma horizontalPhaseMultiplier_scaled_bar (freq : ℂ) (r : ℝ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq (1/(r:ℂ))+
      Complex.I*horizontalPhaseMultiplier freq (Complex.I/(r:ℂ)))=
      2*Real.pi*Complex.I*star freq/(r:ℂ) := by
  simp only [horizontalPhaseMultiplier,star_mul,
    Complex.star_def,map_div₀,map_one,Complex.conj_ofReal,Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ; ring

namespace SubexponentialBesselCoefficients

lemma scaled_fullFunction_horizontal_hasDerivAt (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    HasDerivAt (fun t:ℝ=>coeff.fullFunction constant
      (upperPoint ((z+(t:ℂ)*direction)/(r:ℂ)) (v/r) (div_pos hv hr)))
      (∑'h:Eis,coeff.directionalTerm h (v/r) (z/(r:ℂ)) (direction/(r:ℂ))) 0 := by
  have h:=coeff.fullFunction_horizontal_hasDerivAt constant (v/r) (div_pos hv hr)
    (z/(r:ℂ)) (direction/(r:ℂ)) 0
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at h
  convert h using 1
  funext t
  congr 2
  ring

lemma scaled_fullFunction_wirtingerBar (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w=>coeff.fullFunction constant
      (upperPoint (w/(r:ℂ)) (v/r) (div_pos hv hr))) z=
      ∑'h:Eis,(2*Real.pi*Complex.I*star (cuspFrequency h)/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ)) := by
  have h1:=(coeff.scaled_fullFunction_horizontal_hasDerivAt constant r hr v hv z 1).deriv
  have hI:=(coeff.scaled_fullFunction_horizontal_hasDerivAt constant r hr v hv z Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar,h1,hI]
  have hs1:=coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (1/(r:ℂ))
  have hsI:=(coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (Complex.I/(r:ℂ))).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_add hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v/r,z/(r:ℂ))*horizontalPhaseMultiplier_scaled_bar (cuspFrequency h) r

def scaledConjugateZTerm (coeff : SubexponentialBesselCoefficients)
    (r v : ℝ) (z : ℂ) (h : Eis) : ℂ :=
  (-2*Real.pi*Complex.I*cuspFrequency h/(r:ℂ))*star (coeff.term h (v/r,z/(r:ℂ)))

theorem scaledConjugate_wirtingerZ (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w=>star (coeff.fullFunction constant
      (upperPoint (w/(r:ℂ)) (v/r) (div_pos hv hr)))) z=
      ∑'h:Eis,coeff.scaledConjugateZTerm r v z h := by
  rw [horizontalWirtingerZ_star,coeff.scaled_fullFunction_wirtingerBar constant r hr v hv z,tsum_star]
  apply tsum_congr
  intro h
  unfold scaledConjugateZTerm
  simp only [star_mul,Complex.star_def,map_div₀,map_mul,
    map_ofNat,Complex.conj_ofReal,Complex.conj_I,starRingEnd_self_apply]
  ring

theorem scaledConjugateZTerm_summable (coeff : SubexponentialBesselCoefficients)
    (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z : ℂ) :
    Summable (coeff.scaledConjugateZTerm r v z) := by
  have hs1:=coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (1/(r:ℂ))
  have hsI:=(coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (Complex.I/(r:ℂ))).mul_left Complex.I
  apply (((hs1.add hsI).mul_left (1/2:ℂ)).star).congr
  intro h
  simp only [directionalTerm]
  change star ((1/2:ℂ)*(horizontalPhaseMultiplier (cuspFrequency h) (1/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ))+
    Complex.I*(horizontalPhaseMultiplier (cuspFrequency h) (Complex.I/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ)))))=_
  rw [show (1/2:ℂ)*(horizontalPhaseMultiplier (cuspFrequency h) (1/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ))+
    Complex.I*(horizontalPhaseMultiplier (cuspFrequency h) (Complex.I/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ))))=
      ((1/2:ℂ)*(horizontalPhaseMultiplier (cuspFrequency h) (1/(r:ℂ))+
        Complex.I*horizontalPhaseMultiplier (cuspFrequency h) (Complex.I/(r:ℂ))))*coeff.term h (v/r,z/(r:ℂ)) by ring,
    horizontalPhaseMultiplier_scaled_bar]
  unfold scaledConjugateZTerm
  simp only [star_mul,Complex.star_def,map_div₀,map_mul,
    map_ofNat,Complex.conj_ofReal,Complex.conj_I,starRingEnd_self_apply]
  ring

lemma scaledConjugateZTerm_zero (coeff : SubexponentialBesselCoefficients)
    (r v : ℝ) (z : ℂ) : coeff.scaledConjugateZTerm r v z 0=0 := by
  simp only [scaledConjugateZTerm,cuspFrequency,map_zero,zero_div,mul_zero,zero_mul]

lemma scaledConjugateZTerm_bessel (coeff : SubexponentialBesselCoefficients)
    (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z : ℂ) (h : Eis) (hh : h≠0) :
    coeff.scaledConjugateZTerm r v z h=
      (-2*Real.pi*Complex.I*cuspFrequency h/(r:ℂ))*star (coeff.value h)*((v/r:ℝ):ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/r))*
          ShortDraftTrace.breveE (-cuspFrequency h*(z/(r:ℂ))) := by
  rw [scaledConjugateZTerm,coeff.term_bessel h hh (v/r) (div_pos hv hr) (z/(r:ℂ))]
  have hx : 0<4*Real.pi*‖cuspFrequency h‖*(v/r) :=
    mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))) (div_pos hv hr)
  rw [schlafliBesselK_cubic_real _ hx]
  simp only [star_mul,breveE_star,Complex.star_def,Complex.conj_ofReal,neg_mul]
  ring

end SubexponentialBesselCoefficients

end CubicEisenstein

end

end OAI

end

