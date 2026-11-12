module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Cusp.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part021

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ReflectionFibers -/

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
open scoped BigOperators Classical ContDiff MatrixGroups

open ActualEisensteinCubic CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

lemma stratum_model_coefficient (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    G.shape.amplitude u m I J*
      (star D.fixedFactor*A4BadPhase G.c0 G.denominator_ne_zero (D.matrix (fun _=>1) 1 1) D.U
        (G.dualNumerator u m I J))*D.bracketProduct hp hg j (G.dualNumerator u m I J)=
    D.modelRowPhase G.shape hp hg j u m*
      ∑e:ι→Fin 3,G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m I J*
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) :=
  D.model_coefficient G.shape hp G.denominator_ne_zero hg j u m I J

theorem reflectedValue_eq_model_series (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) :
    D.reflectedValue G.shape hp G.denominator_ne_zero hg j W X=
    fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
      ∑'t:ThetaFullIndex,
        (D.modelRowPhase G.shape hp hg j t.1 t.2.1*
          ∑e:ι→Fin 3,
            G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
              t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
            reflectedBranch (fun i=>Ideal.span {p i}) hg j e
              (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
          ((ramifiedScale 1 completedRamifiedStep t.2.1*
            Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
            (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3) := by
  unfold ControlledStratumArithmetic.reflectedValue
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  rw [fixed_stratum_kernel_scale]
  have he:=G.stratum_model_coefficient D hp hg j t.1 t.2.1 t.2.2.1.val t.2.2.2.val
  have hx:sourceCuspPhaseNumerator G.shape.index (G.shape.upper 0 0) (thetaFullFrequency t)=
      G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  rw [hx]
  let denominator:ℂ:=((ramifiedScale 1 completedRamifiedStep t.2.1*
    Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)
  let kernel:ℂ:=CubicReflectionKernel.paperKernel (Vstar W)
    ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
      (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)
  change _/denominator*kernel*_=_/denominator*kernel
  calc
    _=(G.shape.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      (star D.fixedFactor*A4BadPhase G.c0 G.denominator_ne_zero (D.matrix (fun _=>1) 1 1) D.U
        (G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val))*
      D.bracketProduct hp hg j (G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val))/denominator*kernel := by ring
    _=_:=by rw [he]

end FixedFourierGeometry
end

open ActualEisensteinCubic CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

abbrev CuspIdealIndex := Eisˣ×ℕ×NonzeroDualIdeal×NonzeroDualIdeal

def thetaFullToIdealIndex (t:ThetaFullIndex) : CuspIdealIndex :=
  (t.1,t.2.1,primaryCubePairToMellinIndex t.2.2)

lemma thetaFullToIdealIndex_injective : Function.Injective thetaFullToIdealIndex := by
  intro t v h
  apply Prod.ext
  · exact congrArg (fun x:CuspIdealIndex=>x.1) h
  · apply Prod.ext
    · exact congrArg (fun x:CuspIdealIndex=>x.2.1) h
    · apply primaryCubePairToMellinIndex_injective
      exact congrArg (fun x:CuspIdealIndex=>x.2.2) h

lemma fixedCuspArrayWithPhase_eligible (j:Fin 3) (u:Eisˣ)
    (φ:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayWithPhase j u φ m I J≠0) : fixedCuspArrayEligible I J := by
  by_contra he
  exact h (fixedCuspArrayWithPhase_zero j u φ m I J he)

theorem fixedCuspArrayWithPhase_tsum_primary_pairs (j:Fin 3) (u:Eisˣ)
    (φ:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (w:CompletedMellinIndex→ℂ) :
    (∑'t:CompletedMellinIndex,fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*w t)=
    ∑'t:ThetaPrimaryCubePair,fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*
      w (primaryCubePairToMellinIndex t) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun t=>primaryCubePairToMellinIndex t.val)
  · exact primaryCubePairToMellinIndex_injective.comp Subtype.val_injective
  · intro t ht
    change fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*w t≠0 at ht
    have ha:fixedCuspArrayWithPhase j u φ m t.1.val t.2.val≠0:=by
      intro hz
      exact ht (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=fixedCuspArrayWithPhase_eligible j u φ m t.1.val t.2.val ha
    let v:ThetaPrimaryCubePair:=(⟨t.1.val,hs,hI⟩,⟨t.2.val,hJ⟩)
    have hv:primaryCubePairToMellinIndex v=t:=Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    refine ⟨⟨v,?_⟩,hv⟩
    change fixedCuspArrayWithPhase j u φ m (primaryCubePairToMellinIndex v).1.val
      (primaryCubePairToMellinIndex v).2.val*w (primaryCubePairToMellinIndex v)≠0
    rwa [hv]
  · intro t
    rfl

theorem fixedCuspArrayWithPhase_tsum_full_index
    (j:Eisˣ→Fin 3) (φ:Eisˣ→ℕ→Ideal Eis→Ideal Eis→ℂ) (w:CuspIdealIndex→ℂ) :
    (∑'t:CuspIdealIndex,fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1)
      t.2.1 t.2.2.1.val t.2.2.2.val*w t)=
    ∑'t:ThetaFullIndex,fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1)
      t.2.1 t.2.2.1.val t.2.2.2.val*w (thetaFullToIdealIndex t) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun t=>thetaFullToIdealIndex t.val)
  · exact thetaFullToIdealIndex_injective.comp Subtype.val_injective
  · intro t ht
    change fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1) t.2.1 t.2.2.1.val t.2.2.2.val*w t≠0 at ht
    have ha:fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1) t.2.1 t.2.2.1.val t.2.2.2.val≠0:=by
      intro hz
      exact ht (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=fixedCuspArrayWithPhase_eligible _ _ _ _ _ _ ha
    let v:ThetaFullIndex:=(t.1,t.2.1,⟨t.2.2.1.val,hs,hI⟩,⟨t.2.2.2.val,hJ⟩)
    have hv:thetaFullToIdealIndex v=t:=
      Prod.ext rfl (Prod.ext rfl (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)))
    refine ⟨⟨v,?_⟩,hv⟩
    change fixedCuspArrayWithPhase (j (thetaFullToIdealIndex v).1) (thetaFullToIdealIndex v).1
      (φ (thetaFullToIdealIndex v).1) (thetaFullToIdealIndex v).2.1
      (thetaFullToIdealIndex v).2.2.1.val (thetaFullToIdealIndex v).2.2.2.val*
      w (thetaFullToIdealIndex v)≠0
    rwa [hv]
  · intro t
    rfl

end CubicEisenstein

open scoped Classical BigOperators

namespace CompletedGauss
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def mandatoryActiveEquiv (R:Finset ι) :
    {A:Finset ι // R⊆A}≃Finset {i:ι // i∉R} where
  toFun A:=A.val.subtype (fun i=>i∉R)
  invFun B:=⟨R∪B.image Subtype.val,Finset.subset_union_left⟩
  left_inv A:=by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_subtype]
    constructor
    · rintro (hi|⟨j,hj,rfl⟩)
      · exact A.property hi
      · exact hj
    · intro hi
      by_cases hr:i∈R
      · exact Or.inl hr
      · exact Or.inr ⟨⟨i,hr⟩,hi,rfl⟩
  right_inv B:=by
    ext i
    simp only [Finset.mem_subtype,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro (hi|⟨j,hj,hji⟩)
      · exact False.elim (i.property hi)
      · have he:j=i:=Subtype.ext hji
        simpa only [he] using hj
    · intro hi
      exact Or.inr ⟨i,hi,rfl⟩

lemma sum_mandatory_active {V:Type*} [AddCommMonoid V]
    (R:Finset ι) (F:Finset ι→V) (hz:∀A,¬R⊆A→F A=0) :
    (∑A:Finset ι,F A)=
      ∑B:Finset {i:ι // i∉R},F (R∪B.image Subtype.val) := by
  calc
    _=∑A:Finset ι,if R⊆A then F A else 0:=by
      apply Finset.sum_congr rfl
      intro A hA
      by_cases h:R⊆A
      · simp only [ite_eq_left h]
      · simp only [ite_eq_right h,hz A h]
    _=∑A:{A:Finset ι // R⊆A},F A.val:=by
      rw [←Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (fun A:Finset ι=>R⊆A)) (by simp) F
    _=_:=by
      apply Fintype.sum_equiv (mandatoryActiveEquiv R)
      intro A
      exact congrArg F (congrArg Subtype.val ((mandatoryActiveEquiv R).left_inv A)).symm

theorem inactive_weight_mandatory_active (R:Finset ι) (z:ι→ℂ)
    (hz:∀i∈R,z i=0) (F:Finset ι→ℂ) :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)*
          F (R∪B.image Subtype.val) := by
  apply sum_mandatory_active R
  intro A hA
  have hex:∃i∈R,i∉A:=by
    by_contra! hn
    exact hA hn
  obtain ⟨i,hi,hni⟩:=hex
  have hm:i∈(Finset.univ:Finset ι)\A:=by simp [hni]
  rw [Finset.prod_eq_zero hm (hz i hi),zero_mul]

lemma inactive_product_complement (R:Finset ι) (z:ι→ℂ)
    (B:Finset {i:ι // i∉R}) :
    (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)=
      ∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val := by
  symm
  apply Finset.prod_bij (fun i _=>i.val)
  · intro i hi
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and] at hi ⊢
    intro hmem
    rcases Finset.mem_union.mp hmem with hr|hb
    · exact i.property hr
    · obtain ⟨j,hj,hji⟩:=Finset.mem_image.mp hb
      exact hi ((Subtype.ext hji) ▸ hj)
  · intro i hi j hj he
    exact Subtype.ext he
  · intro i hi
    have hnot:i∉R∪B.image Subtype.val:=(Finset.mem_sdiff.mp hi).2
    have hr:i∉R:=fun h=>hnot (Finset.mem_union_left _ h)
    refine ⟨⟨i,hr⟩,?_,rfl⟩
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
    intro hb
    exact hnot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i,hr⟩,hb,rfl⟩))
  · intro i hi
    rfl

theorem inactive_weight_optional_active (R:Finset ι) (z:ι→ℂ)
    (hz:∀i∈R,z i=0) (F:Finset ι→ℂ) :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val)*
          F (R∪B.image Subtype.val) := by
  rw [inactive_weight_mandatory_active R z hz F]
  apply Finset.sum_congr rfl
  intro B hB
  rw [inactive_product_complement]

end CompletedGauss

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
local notation "Eis" => ActualEisensteinCubic.O

lemma excluded_prime_dvd_row_mask (q:ℕ) (m:Eis) (F P:Ideal Eis)
    (hP:P∈reflectionExcludedPrimes q) :
    P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F := by
  apply dvd_mul_of_dvd_left
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_le.mpr
  exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem _ hP))

lemma residual_prime_not_excluded (q:ℕ) (m:Eis) (F I P:Ideal Eis) (hP:Prime P)
    (hres:P∣rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) :
    P∉reflectionExcludedPrimes q := by
  intro hmem
  have hn:¬P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F:=
    ((prime_dvd_rowResidualPart_iff _ _ P hP).mp hres).2
  exact hn (excluded_prime_dvd_row_mask q m F P hmem)

lemma residual_coprime_fixed_conductor (q:ℕ) (hq:q≠0) (m:Eis) (F I:Ideal Eis) :
    IsCoprime (Ideal.span {reflectionConductor q})
      (rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) := by
  let Q:=Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
  apply Finset.disjoint_left.mpr
  intro P hfixed hres
  have hp:Prime P:=support_prime hfixed
  have hd:P∣Ideal.span {reflectionConductor q}:=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hfixed)
  have hr:P∣rowResidualPart I Q:=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hres)
  exact residual_prime_not_excluded q m F I P hp hr (reflectionConductor_prime_mem q hq P hp hd)

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def representativeRowFiber (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) : Finset (Ideal Eis) :=
  completedRowFiber rows Q (rowPowerfulPart I) (rowMaskPart I Q)

def reconstructFiberRow (I Q k:Ideal Eis) : Ideal Eis :=
  rowPowerfulPart I*rowMaskPart I Q*k

lemma reconstructFiberRow_ne_zero (I Q k:Ideal Eis) (hk:k≠0) : reconstructFiberRow I Q k≠0 :=
  mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) hk

lemma reconstructFiberRow_of_original (rows:Finset (Ideal Eis)) (I Q J:Ideal Eis)
    (hJ:J∈representativeRowFiber rows I Q) (hJ0:J≠0) :
    reconstructFiberRow I Q (rowResidualPart J Q)=J := by
  obtain ⟨_,hA,hT⟩:=Finset.mem_filter.mp hJ
  rw [reconstructFiberRow,←hA,←hT]
  exact row_powerful_mask_residual_product J Q hJ0

lemma residual_reconstructFiberRow (rows:Finset (Ideal Eis)) (I Q k:Ideal Eis)
    (hk:k≠0) (hmem:reconstructFiberRow I Q k∈representativeRowFiber rows I Q) :
    rowResidualPart (reconstructFiberRow I Q k) Q=k := by
  have he:=reconstructFiberRow_of_original rows I Q _ hmem (reconstructFiberRow_ne_zero I Q k hk)
  exact mul_left_cancel₀ (mul_ne_zero (rowPowerfulPart_ne_zero I)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) he

lemma representativeRowFiber_injective (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hrows:∀J∈rows,J≠0) :
    Set.InjOn (fun J=>rowResidualPart J Q) (representativeRowFiber rows I Q) :=
  rowResidualPart_injective_on_fiber rows Q (rowPowerfulPart I) (rowMaskPart I Q) hrows

def fiberResidualIndex (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) : idealRange (completedResidualScale K I Q) :=
  ⟨rowResidualPart J.val Q,completedRowFiber_residual_range rows Q
    (rowPowerfulPart I) (rowMaskPart I Q) hbad K hrows J.val J.property⟩

lemma fiberResidualIndex_injective (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K) :
    Function.Injective (fiberResidualIndex rows I Q K hbad hrows) := by
  intro J lengthScale he
  apply Subtype.ext
  apply representativeRowFiber_injective rows I Q (fun J hJ=>(hrows J hJ).1) J.property lengthScale.property
  exact congrArg Subtype.val he

def extendFiberRowScalar {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) : ℂ :=
  if h:reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q then
    scalar a ⟨reconstructFiberRow I Q k.val,h⟩ else 0

lemma extendFiberRowScalar_norm_le_one {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (hscalar:∀a J,‖scalar a J‖≤1)
    (a:α) (k:idealRange (completedResidualScale K I Q)) :
    ‖extendFiberRowScalar rows I Q K scalar a k‖≤1 := by
  unfold extendFiberRowScalar
  split_ifs
  · exact hscalar _ _
  · simp

lemma extendFiberRowScalar_zero {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q))
    (hk:reconstructFiberRow I Q k.val∉representativeRowFiber rows I Q) :
    extendFiberRowScalar rows I Q K scalar a k=0 := by
  simp only [extendFiberRowScalar,dite_eq_right hk]

lemma extendFiberRowScalar_at_original {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (J:representativeRowFiber rows I Q) :
    extendFiberRowScalar rows I Q K scalar a (fiberResidualIndex rows I Q K hbad hrows J)=scalar a J := by
  have hJ0:J.val≠0:=(hrows J.val (Finset.mem_filter.mp J.property).1).1
  have he:=reconstructFiberRow_of_original rows I Q J.val J.property hJ0
  simp only [extendFiberRowScalar,fiberResidualIndex,he,dite_eq_left J.property]

def extendSelectedFiberRowScalar {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (t:τ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) : ℂ :=
  extendFiberRowScalar rows I Q K (fun a J=>if selector a J=t then scalar a J else 0) a k

lemma extendSelectedFiberRowScalar_norm_le_one {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (hscalar:∀a J,‖scalar a J‖≤1)
    (t:τ) (a:α) (k:idealRange (completedResidualScale K I Q)) :
    ‖extendSelectedFiberRowScalar rows I Q K selector scalar t a k‖≤1 := by
  apply extendFiberRowScalar_norm_le_one
  intro a J
  split_ifs
  · exact hscalar a J
  · simp

lemma extendSelectedFiberRowScalar_at_original {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (t:τ) (a:α)
    (J:representativeRowFiber rows I Q) :
    extendSelectedFiberRowScalar rows I Q K selector scalar t a
      (fiberResidualIndex rows I Q K hbad hrows J)=
        if selector a J=t then scalar a J else 0 :=
  extendFiberRowScalar_at_original rows I Q K hbad hrows _ a J

lemma sum_extendSelectedFiberRowScalar {α τ:Type*} [Fintype τ] [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) :
    (∑t:τ,extendSelectedFiberRowScalar rows I Q K selector scalar t a k)=
      extendFiberRowScalar rows I Q K scalar a k := by
  by_cases hk:reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q
  · simp [extendSelectedFiberRowScalar,extendFiberRowScalar,hk]
  · simp only [extendSelectedFiberRowScalar,extendFiberRowScalar,dite_eq_right hk,Finset.sum_const_zero]

end

open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem reconstructFiberRow_valid_iff (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (k:idealRange (completedResidualScale K I Q)) :
    reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q ↔
      ∃J:representativeRowFiber rows I Q,fiberResidualIndex rows I Q K hbad hrows J=k := by
  constructor
  · intro hk
    refine ⟨⟨reconstructFiberRow I Q k.val,hk⟩,?_⟩
    apply Subtype.ext
    exact residual_reconstructFiberRow rows I Q k.val (mem_idealRange.mp k.property).1.1 hk
  · rintro ⟨J,rfl⟩
    have hJ0:J.val≠0:=(hrows J.val (Finset.mem_filter.mp J.property).1).1
    change reconstructFiberRow I Q (rowResidualPart J.val Q)∈representativeRowFiber rows I Q
    rw [reconstructFiberRow_of_original rows I Q J.val J.property hJ0]
    exact J.property

lemma representativeFiber_parts (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (J:representativeRowFiber rows I Q) :
    rowPowerfulPart J.val=rowPowerfulPart I ∧ rowMaskPart J.val Q=rowMaskPart I Q :=
  (Finset.mem_filter.mp J.property).2

lemma representativeFiber_pool (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) :
    completedReflectionPool J.val Q=completedReflectionPool I Q := by
  have hs:=representativeFiber_parts rows I Q J
  exact completedReflectionPool_eq_on_fiber J.val I Q
    (hrows J.val (Finset.mem_filter.mp J.property).1) hI hQ hs.1 hs.2

lemma representativeFiber_filtered_pool (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) (free:Ideal Eis → Prop) [DecidablePred free] :
    (completedReflectionPool J.val Q).filter free=(completedReflectionPool I Q).filter free := by
  rw [representativeFiber_pool rows I Q hI hQ hrows J]

lemma representativeFiber_exponent (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) (P:completedReflectionPool I Q) :
    completedLocalExponent J.val F P.val=completedLocalExponent I F P.val := by
  have hs:=representativeFiber_parts rows I Q J
  exact (completedReflectionPool_exponent_eq I J.val F Q hI
    (hrows J.val (Finset.mem_filter.mp J.property).1) hQ hs.1.symm hs.2.symm P).symm

lemma representativeFiber_extractedDivisor {ι:Type*} [Fintype ι]
    (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q)
    (P:ι → Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι → Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P (fun i=>completedLocalExponent J.val F (P i)) e v=
      reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e v := by
  have he:(fun i=>completedLocalExponent J.val F (P i))=
      (fun i=>completedLocalExponent I F (P i)):=by
    funext i
    exact representativeFiber_exponent rows I F Q hI hQ hrows J ⟨P i,hP i⟩
  rw [he]

lemma representativeFiber_residualScale (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (J:representativeRowFiber rows I Q) (K:ℝ) :
    completedResidualScale K J.val Q=completedResidualScale K I Q := by
  have hs:=representativeFiber_parts rows I Q J
  exact completedResidualScale_eq_on_fiber K J.val I Q hs.1 hs.2

lemma representativeFiber_branchScale {ι:Type*} [Fintype ι]
    (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q)
    (P:ι → Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι → Fin 3) (K X:ℝ) :
    completedBranchScale K X J.val F Q P e=completedBranchScale K X I F Q P e := by
  have hs:=representativeFiber_parts rows I Q J
  exact (completedBranchScale_eq_on_fiber K X I J.val F Q hI
    (hrows J.val (Finset.mem_filter.mp J.property).1) hQ hs.1.symm hs.2.symm P hP e).symm

end CompletedGauss

open scoped Classical BigOperators

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def fixedRayFiberFromRows (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount c hc) (fixedCuspLevelBound c) K I F Q :=
  fixedRayFiber c hc I F Q Q0 hI hQ K (fun _=>1) (by intro x;simp)
    (fun x m=>extendFiberRowScalar rows I Q K scalar (x,m))
    (fun x m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar (x,m))

lemma fixedRayFiberFromRows_rowPhase (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) (r:FixedReflectionRay c hc)
    (e:pool I Q Q0→Fin 6) (i:ℕ×ℕ×ℕ) :
    ((fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedReflectionRayEquiv c hc r,e)).rowPhase i
        (fiberResidualIndex rows I Q K hbad hrows J)=scalar ((r,e),i.1) J := by
  change extendFiberRowScalar rows I Q K scalar
    ((((fixedReflectionRayEquiv c hc).symm (fixedReflectionRayEquiv c hc r)),e),i.1)
    (fiberResidualIndex rows I Q K hbad hrows J)=_
  rw [Equiv.symm_apply_apply]
  exact extendFiberRowScalar_at_original rows I Q K hbad hrows scalar ((r,e),i.1) J

lemma fixedRayFiberFromRows_weight (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (r:FixedReflectionRay c hc) (e:pool I Q Q0→Fin 6) :
    (fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).weight
      (fixedReflectionRayEquiv c hc r,e)=reflectionSixInactiveWeight I F Q Q0 e := by
  change 1*reflectionSixInactiveWeight I F Q Q0 e=_
  exact one_mul _

end CompletedGauss.FreeReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.RowCompletion.ControlledPrimeStrata -/

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

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def freePrimaryPrime (I Q:Ideal Eis) (P:FreePrimeIndex I Q) : Eis := primaryPrime P.val.val

lemma freePrimaryPrime_ne_zero (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    freePrimaryPrime I Q P≠0 :=
  primaryPrime_ne_zero P.val.val
    (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_span (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    Ideal.span {freePrimaryPrime I Q P}=P.val.val :=
  (primaryPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.1

lemma freePrimaryPrime_primary (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    lambda^2∣freePrimaryPrime I Q P-1 :=
  (primaryPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.2

lemma freePrimaryPrime_maximal (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal := by
  rw [freePrimaryPrime_span I Q hI P]
  infer_instance

lemma freePrimaryPrime_good (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    lambda∉(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_odd (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    ringChar (Eis⧸Ideal.span {freePrimaryPrime I Q P})≠2 := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.2

lemma freePrimaryPrime_injective (I Q:Ideal Eis) (hI:Supported I) :
    Function.Injective (freePrimaryPrime I Q) := by
  intro P R he
  have hh:=congrArg (fun x:Eis=>(Ideal.span {x}:Ideal Eis)) he
  rw [freePrimaryPrime_span I Q hI P,freePrimaryPrime_span I Q hI R] at hh
  exact Subtype.ext (Subtype.ext hh)

lemma freePrimaryPrime_coprime (I Q:Ideal Eis) (hI:Supported I) :
    Pairwise (fun P R:FreePrimeIndex I Q =>
      IsCoprime (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) (Ideal.span {freePrimaryPrime I Q R})) := by
  intro P R hPR
  rw [freePrimaryPrime_span I Q hI P,freePrimaryPrime_span I Q hI R]
  exact freePrimeIndex_pairwise_coprime I Q hPR

lemma freePrimaryPrime_coprime_fixed (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    IsCoprime Q (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact freePrimeIndex_coprime I Q P

lemma freePrimaryPrime_product_span (I Q:Ideal Eis) (hI:Supported I) :
    Ideal.span {∏P:FreePrimeIndex I Q,freePrimaryPrime I Q P}=
      ∏P:FreePrimeIndex I Q,P.val.val := by
  rw [FiniteGaussPhase.span_finset_prod]
  apply Finset.prod_congr rfl
  intro P _
  exact freePrimaryPrime_span I Q hI P

lemma freePrimaryPrime_product_coprime_fixed (I Q:Ideal Eis) (hI:Supported I) :
    IsCoprime Q (Ideal.span {∏P:FreePrimeIndex I Q,freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_product_span I Q hI]
  exact freePrimeProduct_coprime I Q

lemma actualSextic_power_transport (P R:Ideal Eis) [P.IsMaximal] [R.IsMaximal]
    (hP:lambda∉P) (hR:lambda∉R) (he:P=R) (j:ℕ) (n:Eis) :
    (actualSextic P hP^j) (Ideal.Quotient.mk P n)=
      (actualSextic R hR^j) (Ideal.Quotient.mk R n) := by
  subst R
  rfl

theorem freePrimeRow_eq_primary_family (I Q:Ideal Eis) (hI:Supported I) (n:Eis) :
    letI : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
      freePrimaryPrime_maximal I Q hI
    freePrimeRow I hI Q n=
      finiteSexticRow (fun P:FreePrimeIndex I Q=>Ideal.span {freePrimaryPrime I Q P})
        (freePrimaryPrime_good I Q hI)
        (fun P=>(normalizedFactors I).count P.val.val%6) n := by
  let : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  unfold freePrimeRow finiteSexticRow
  apply Finset.prod_congr rfl
  intro P _
  exact actualSextic_power_transport _ _ _ _ (freePrimaryPrime_span I Q hI P).symm _ n

end CanonicalRowCompletion

namespace FixedRayActiveSet

theorem fourier_inversion_by_active_set {ι:Type*} [Fintype ι]
    (F:ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (ψ:∀i,AddChar (F i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (φ:∀i,F i→ℂ) (x:∀i,F i) :
    (∏i,φ i (x i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0)*
        (∑v:∀i:A,(F i.val)ˣ,
          (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
            (∏i:A,ψ i.val ((v i:F i.val)*x i.val))) := by
  let f:=fun i (a:F i)=>CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) a*ψ i (a*x i)
  have he: (∑h:∀i,F i,∏i,f i (h i))=∏i,φ i (x i):=by
    rw [←Fintype.prod_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact CubicEisenstein.finiteAdditiveFourier_inversion (ψ i) (hψ i) (φ i) (x i)
  rw [←he,sum_by_active_strata]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sum_active_stratum]
  have hz:(∏i∈(Finset.univ:Finset ι)\A,f i 0)=
      ∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0:=by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f,zero_mul,AddChar.map_zero_eq_one,mul_one]
  rw [hz,mul_comm]
  congr 1
  rw [show (∑v:∀i:A,(F i.val)ˣ,
      (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
        (∏i:A,ψ i.val ((v i:F i.val)*x i.val)))=
      ∑v:∀i:A,(F i.val)ˣ,∏i:A,f i.val (v i) by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.prod_mul_distrib).symm]
  calc
    _=∏i:A,∑u:(F i.val)ˣ,f i.val (u:F i.val):=
      (Finset.prod_coe_sort A (fun i=>∑u:(F i)ˣ,f i (u:F i))).symm
    _=_:=Fintype.prod_sum (fun (i:A) (u:(F i.val)ˣ)=>f i.val (u:F i.val))

end FixedRayActiveSet

open scoped BigOperators Classical ContDiff

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedBesselProfile_of_finite_cusp_multiplier
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hmult:∀n:Eis,(∑i,w i*ShortDraftTrace.breveE (-cuspFrequency n*(d i).point))=fixedThetaTwist Ψ n)
    (v:ℝ) (hv:0<v) :
    completedBesselProfile Ψ thetaBesselScale v=
      thetaDerivativeScalar⁻¹*∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v := by
  have hf:=finiteConjugateSource_wirtingerBar (fun i=>(d i).point) w v hv 0
  simp only [hmult] at hf
  have hcseries:=traceTwistedConjugateSource_wirtingerBar c hc (fixedThetaQuotient Ψ c) v hv 0
  simp only [fixedThetaQuotient_mk Ψ Q hperiod c hcQ] at hcseries
  have he:(∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v)=
      thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v:=by
    rw [←finiteConjugateSource_wirtingerBar_sum (fun i=>(d i).point) w v hv]
    calc
      _=horizontalWirtingerBar (traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv) 0:=
        hf.trans hcseries.symm
      _=_:=thetaTwistedSource_wirtingerBar_eq_completedBesselProfile Ψ Q hperiod c hc hcQ v hv
  rw [he,←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]

theorem completedT_of_finite_cusp_multiplier
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hmult:∀n:Eis,(∑i,w i*ShortDraftTrace.breveE (-cuspFrequency n*(d i).point))=fixedThetaTwist Ψ n)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*∑i,w i*(d i).smoothedKernel W X := by
  have hFG (v:ℝ) (hv:0<v) : completedBesselProfile Ψ thetaBesselScale v=
      ∑i,(thetaDerivativeScalar⁻¹*w i)*cuspBarProfile cubicSourceConjugateFunction (d i).point v:=by
    rw [completedBesselProfile_of_finite_cusp_multiplier Ψ Q hperiod c hc hcQ d w hmult v hv,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [completedT_of_finite_cusp_profiles Ψ hΨ Q hperiod c hc hcQ d
    (fun i=>thetaDerivativeScalar⁻¹*w i) hFG W lo hi hlo hsupp hW X hX,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end

open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma theta_lifted_phase (c:Eis) (hc:c≠0) (lift n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(eisLam^2*eisEmbedding lift/eisEmbedding c))=
      quotientTrace c hc (Ideal.Quotient.mk _ lift*Ideal.Quotient.mk _ n) := by
  rw [←map_mul]
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency
  rw [map_mul]
  have hc0:=eisEmbedding_ne_zero hc
  have hl:=eisLam_ne_zero
  field_simp
  linear_combination -(eisEmbedding n*eisEmbedding lift)*TraceLambdaPhase.eisLam_sq

lemma breveE_finset_sum {ι:Type*} (s:Finset ι) (z:ι→ℂ) :
    ShortDraftTrace.breveE (∑i∈s,z i)=∏i∈s,ShortDraftTrace.breveE (z i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

lemma ControlledStratumArithmetic.datum_fourier_phase {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
    (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(D.datum hN hr hbase s hp hc0 v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i,quotientTrace (p i) (hp i) ((v i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ n) := by
  rw [D.datum_point]
  have he:-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i))=
      -cuspFrequency n*(eisEmbedding a0/eisEmbedding c0)+
        ∑i,-cuspFrequency n*(eisLam^2*eisEmbedding (D.lift v i)/eisEmbedding (p i)):=by
    simp only [Finset.mul_sum,neg_mul,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,AddChar.map_add_eq_mul,breveE_finset_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [theta_lifted_phase,D.lift_residue]

end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def unextractedCuspCoefficient {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  σ m*η m I J*reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)/
    ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ)

lemma unextractedCuspCoefficient_norm {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (hρ:0<ρ) (hq:1≤q)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (hη:∀m I J,‖η m I J‖≤1) (hσ:∀m,‖σ m‖≤1)
    (m:ℕ) (I J:NonzeroDualIdeal) :
    ‖unextractedCuspCoefficient P hg j e ρ q η σ m I.val J.val‖≤
      (Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
        Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
        Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ))/ρ := by
  let C:ℝ:=Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
  have hC:0≤C:=by dsimp only [C];positivity
  have hr:0< ramifiedScale ρ q m:=ramifiedScale_pos ρ q hρ (lt_of_lt_of_le zero_lt_one hq) m
  have hn:1≤(Ideal.absNorm I.val:ℝ):=norm_at_least_one I.val I.property
  have hb:1≤(Ideal.absNorm J.val:ℝ):=norm_at_least_one J.val J.property
  have hs:1≤Real.sqrt (Ideal.absNorm I.val:ℝ):=by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    simpa using hn
  have hd:ρ≤ ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ) := by
    calc
      ρ≤ ramifiedScale ρ q m:=le_mul_of_one_le_right hρ.le (one_le_pow₀ hq)
      _≤ ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I.val:ℝ):=le_mul_of_one_le_right hr.le hs
      _≤_:=le_mul_of_one_le_right (by positivity) hb
  have hp:‖σ m‖*‖η m I.val J.val‖≤1:=(mul_le_of_le_one_left (norm_nonneg _)
    (hσ m)).trans (hη m I.val J.val)
  have hh:‖σ m‖*‖η m I.val J.val‖*
      ‖reflectedBranch P hg j e (primaryGenerator I.val) (primaryGenerator J.val)‖≤C := by
    have ht:=mul_le_mul hp (reflectedBranch_norm_bound P hg j e (primaryGenerator I.val) (primaryGenerator J.val))
      (norm_nonneg _) zero_le_one
    simpa only [one_mul] using ht
  rw [unextractedCuspCoefficient,norm_div,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  exact (div_le_div_of_nonneg_right hh (by positivity)).trans
    (div_le_div_of_nonneg_left hC hρ hd)

theorem unextractedCuspCoefficient_summable {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (hρ:0<ρ) (hq:1<q)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (hη:∀m I J,‖η m I J‖≤1) (hσ:∀m,‖σ m‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (scale:ℝ) (hscale:0<scale) :
    Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖rawDualKernelTerm (Vstar W) scale ρ q (unextractedCuspCoefficient P hg j e ρ q η σ) x‖) := by
  apply rawDualKernelTerm_summable_norm (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) scale ρ q
    ((Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ))/ρ)
    hscale hρ hq (by positivity)
  exact unextractedCuspCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ

end CompletedGauss

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

def stratumBranchTerm (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (e:ι→Fin 3) (W:ℝ→ℂ) (X:ℝ)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  rawDualKernelTerm (Vstar W) (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))
    1 completedRamifiedStep
    (unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j e 1 completedRamifiedStep
      (G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u)
      (D.modelRowPhase G.shape hp hg j u)) x

theorem stratumBranchTerm_summable (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (u:Eisˣ) (e:ι→Fin 3) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>‖G.stratumBranchTerm D hp hg j u e W X x‖) := by
  have hn:0<(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz=>
      (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
        (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hlevel:=G.levelScale_pos
  apply unextractedCuspCoefficient_summable (fun i=>Ideal.span {p i}) hg j e 1 completedRamifiedStep
    (by norm_num) completedRamifiedStep_gt_one _ _ (G.array_norm_le_one _ u)
    (fun m=>(D.modelRowPhase_norm hN hr G.primary G.shape hp hg hchar j hj u m).le)
    W a b ha hsupp hW _ (by positivity)

theorem stratumBranchTerm_fubini (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑'t:CuspIdealIndex,∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j t.1 e W X t.2)=
      ∑'u:Eisˣ,∑e:ι→Fin 3,∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        G.stratumBranchTerm D hp hg j u e W X x := by
  let:Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  have hs:=G.stratumBranchTerm_summable D hN hr hp hg hchar j hj
    (W:=W) (a:=a) (b:=b) (ha:=ha) (hsupp:=hsupp) (hW:=hW) (X:=X) (hX:=hX)
  have hu (u:Eisˣ):Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j u e W X x‖) := by
    have hb:Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ∑e:ι→Fin 3,‖G.stratumBranchTerm D hp hg j u e W X x‖) :=
      (hasSum_sum (fun e _=>(hs u e).hasSum)).summable
    exact hb.of_nonneg_of_le (fun _=>norm_nonneg _) (fun _=>norm_sum_le _ _)
  have hall:Summable (fun t:CuspIdealIndex=>
      ‖∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j t.1 e W X t.2‖) :=
    (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr ⟨hu,Summable.of_finite⟩
  rw [hall.of_norm.tsum_prod]
  apply tsum_congr
  intro u
  exact Summable.tsum_finsetSum (fun e _=>(hs u e).of_norm)

end FixedFourierGeometry
end

open ActualEisensteinCubic CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

theorem reflectedValue_eq_branch_sums (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.reflectedValue G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:ι→Fin 3,∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
          G.stratumBranchTerm D hp hg j u e W X x := by
  rw [G.reflectedValue_eq_model_series]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  rw [←G.stratumBranchTerm_fubini D hN hr hp hg hchar j hj W a b ha hsupp hW X hX]
  let v:G.PhaseResidue:=Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)
  let weight:CuspIdealIndex→ℂ:=fun t=>
    D.modelRowPhase G.shape hp hg j t.1 t.2.1*
      (∑e:ι→Fin 3,reflectedBranch (fun i=>Ideal.span {p i}) hg j e
        (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)
  calc
    _=∑'t:ThetaFullIndex,G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      weight (thetaFullToIdealIndex t) := by
        apply tsum_congr
        intro t
        dsimp only [weight,thetaFullToIdealIndex,primaryCubePairToMellinIndex]
        rw [←Finset.mul_sum]
        ring
    _=∑'t:CuspIdealIndex,G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val*weight t :=
      (fixedCuspArrayWithPhase_tsum_full_index (fun _=>G.shape.index) (G.staticPhase v) weight).symm
    _=_ := by
      apply tsum_congr
      intro t
      dsimp only [weight,stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient]
      simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [v,ramifiedScale]
      ring

theorem stratumBranchTerm_tsum_extract (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (j:ι→ℕ) (e:ι→Fin 3) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    let A:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1
    let B:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,G.stratumBranchTerm D hp hg j u e W X x)=
      ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        G.stratumBranchTerm D hp hg j u e W X (nonzeroDualDilation A B hA hB x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  dsimp only [stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient] at hx
  have hnum:= (div_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).1).1
  have hpair:G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u x.1 x.2.1.val x.2.2.val*
      reflectedBranch (fun i=>Ideal.span {p i}) hg j e
        (primaryGenerator x.2.1.val) (primaryGenerator x.2.2.val)≠0 :=
    mul_ne_zero (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnum).1).2 (mul_ne_zero_iff.mp hnum).2
  have hs:=fixedCuspBranchNumerator_support (fun i=>Ideal.span {p i}) hg hcop j e
    G.shape.index u (G.staticPhase (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u)
    x.1 x.2.1.val x.2.2.val hpair
  exact ⟨hs.1,hs.2.1⟩

theorem smoothedValue_eq_extracted_branch_sums
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0)
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr G.primary G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:ι→Fin 3,
          let A:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1
          let B:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2
          let hA:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 1
          let hB:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 2
          ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
            G.stratumBranchTerm D hp hg j u e W X (nonzeroDualDilation A B hA hB x) := by
  rw [D.smoothed_eq_reflected hN hr G.primary G.shape hp G.denominator_ne_zero hcop hg hchar
    j hj W a b ha hsupp hW X hX,
    G.reflectedValue_eq_branch_sums D hN hr hp hg hchar j hj W a b ha hsupp hW X hX]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro e he
  exact G.stratumBranchTerm_tsum_extract D hp hg hcop j e u W X

end FixedFourierGeometry
end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimaryPrime_coprime_completion (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (P:FreePrimeIndex I Q) : IsCoprime ((9:Eis)*c) (freePrimaryPrime I Q P) := by
  have h9:IsCoprime (9:Eis) (freePrimaryPrime I Q P):=
    (ShortDraftCRT.primary_coprime_nine _ (freePrimaryPrime_primary I Q hI P)).symm
  have h9ideal:IsCoprime (Ideal.span {(9:Eis)}:Ideal Eis)
      (Ideal.span {freePrimaryPrime I Q P}):=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h9
  have hcideal:IsCoprime (Ideal.span {c}:Ideal Eis)
      (Ideal.span {freePrimaryPrime I Q P}):=by
    rw [hcQ]
    exact h9ideal.mul_left (freePrimaryPrime_coprime_fixed I Q hI P)
  exact h9.mul_left ((Ideal.isCoprime_span_singleton_iff _ _).mp hcideal)

theorem exists_freePrimary_controlled_stratum (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex I Q)) :
    Nonempty (ControlledStratumArithmetic
      (fun i:A=>freePrimaryPrime I Q i.val) ((9:Eis)*c) G.a0 G.c0 G.mode) := by
  let : ∀i:A,(Ideal.span {freePrimaryPrime I Q i.val}:Ideal Eis).IsMaximal:=
    fun i=>freePrimaryPrime_maximal I Q hI i.val
  apply exists_controlledStratumArithmetic
    (fun i:A=>freePrimaryPrime I Q i.val)
    (fun i=>freePrimaryPrime_ne_zero I Q hI i.val)
  · intro i j hij
    exact freePrimaryPrime_coprime I Q hI (fun he=>hij (Subtype.ext he))
  · exact fun i=>freePrimaryPrime_primary I Q hI i.val
  · exact G.denominator_ne_zero
  · exact mul_dvd_mul_left 9 G.denominator_dvd
  · exact G.primary
  · exact G.coprime
  · exact fun i=>freePrimaryPrime_coprime_completion I Q hI c hcQ i.val

noncomputable def freePrimaryControlledStratum (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex I Q)) :
    ControlledStratumArithmetic
      (fun i:A=>freePrimaryPrime I Q i.val) ((9:Eis)*c) G.a0 G.c0 G.mode :=
  Classical.choice (exists_freePrimary_controlled_stratum I Q hI c hcQ h G A)

end CanonicalRowCompletion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.RowCompletion.FreePrimePools -/

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
open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def freePrimePool (lengthScale Q0:Ideal Eis) : Finset (Ideal Eis) :=
  (CompletedGauss.primeSupport lengthScale).filter (fun P=>¬Q0≤P)

lemma mem_freePrimePool (lengthScale Q0 P:Ideal Eis) :
    P∈freePrimePool lengthScale Q0 ↔ P∈CompletedGauss.primeSupport lengthScale ∧ ¬Q0≤P := by
  simp only [freePrimePool,Finset.mem_filter]

lemma residual_nonresidual_disjoint (I Q Q0:Ideal Eis) :
    Disjoint (CompletedGauss.primeSupport (rowResidualPart I Q)) (FreeReflection.pool I Q Q0) := by
  apply Finset.disjoint_left.mpr
  intro P hP ht
  exact FreeReflection.pool_nonresidual I Q Q0 ⟨P,ht⟩
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))

theorem freePrimePool_eq_residual_union (lengthScale I Q Q0:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hcop:IsCoprime Q0 (rowResidualPart I Q))
    (hs:CompletedGauss.primeSupport lengthScale=
      (CompletedGauss.primeSupport (I*Q)).filter
        (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2)) :
    freePrimePool lengthScale Q0=
      CompletedGauss.primeSupport (rowResidualPart I Q) ∪ FreeReflection.pool I Q Q0 := by
  have hk:=rowResidualPart_admissible I Q hbad
  ext P
  constructor
  · intro hP
    obtain ⟨hL,hfree⟩:=Finset.mem_filter.mp hP
    rw [hs] at hL
    obtain ⟨hprod,hgood,hodd⟩:=Finset.mem_filter.mp hL
    have hp:Prime P:=prime_of_normalized_factor P (Multiset.mem_toFinset.mp hprod)
    by_cases hr:P∣rowResidualPart I Q
    · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
        ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hk.1).mpr ⟨hp,hr⟩))
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hprod,hgood,hodd,hr⟩,hfree⟩
  · intro hP
    rcases Finset.mem_union.mp hP with hr|ht
    · have hfactor:=Multiset.mem_toFinset.mp hr
      have hp:Prime P:=prime_of_normalized_factor P hfactor
      have hrow:=rowResidualPart_prime_exponent I Q P hfactor
      have hgood:=hk.2.2 P hfactor
      have hfree:¬Q0≤P:=by
        intro hQP
        exact hp.not_isUnit (hcop.isUnit_of_dvd'
          (Ideal.dvd_iff_le.mpr hQP) (dvd_of_mem_normalizedFactors hfactor))
      apply Finset.mem_filter.mpr
      refine ⟨?_,hfree⟩
      rw [hs]
      apply Finset.mem_filter.mpr
      exact ⟨Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)).mpr
        ⟨hp,dvd_mul_of_dvd_left (dvd_of_mem_normalizedFactors hrow.1) Q⟩),hgood⟩
    · obtain ⟨hpool,hfree⟩:=Finset.mem_filter.mp ht
      obtain ⟨hprod,hgood,hodd,_⟩:=Finset.mem_filter.mp hpool
      apply Finset.mem_filter.mpr
      refine ⟨?_,hfree⟩
      rw [hs]
      exact Finset.mem_filter.mpr ⟨hprod,hgood,hodd⟩

def primeUnionToFree (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T) :
    PrimeIndex k ⊕ T → FreePrimeIndex lengthScale Q0 := fun P=>by
  have hm:(Sum.elim Subtype.val Subtype.val P)∈freePrimePool lengthScale Q0:=by
    rw [hs]
    cases P with
    | inl P=>exact Finset.mem_union_left _ P.property
    | inr P=>exact Finset.mem_union_right _ P.property
  exact ⟨⟨Sum.elim Subtype.val Subtype.val P,(Finset.mem_filter.mp hm).1⟩,
    (Finset.mem_filter.mp hm).2⟩

lemma primeUnionToFree_val (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T) (P:PrimeIndex k⊕T) :
    (primeUnionToFree lengthScale Q0 k T hs P).val.val=Sum.elim Subtype.val Subtype.val P := rfl

lemma primeUnionToFree_bijective (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) :
    Function.Bijective (primeUnionToFree lengthScale Q0 k T hs) := by
  constructor
  · intro P R he
    have hv:=congrArg (fun S:FreePrimeIndex lengthScale Q0=>S.val.val) he
    change Sum.elim Subtype.val Subtype.val P=Sum.elim Subtype.val Subtype.val R at hv
    cases P with
    | inl P=>cases R with
      | inl R=>exact congrArg Sum.inl (Subtype.ext hv)
      | inr R=>
        change P.val=R.val at hv
        exact (Finset.disjoint_left.mp hd P.property (hv.symm ▸ R.property)).elim
    | inr P=>cases R with
      | inl R=>
        change P.val=R.val at hv
        exact (Finset.disjoint_left.mp hd R.property (hv ▸ P.property)).elim
      | inr R=>exact congrArg Sum.inr (Subtype.ext hv)
  · intro P
    have hm:P.val.val∈CompletedGauss.primeSupport k∪T:=by
      rw [←hs]
      exact Finset.mem_filter.mpr ⟨P.val.property,P.property⟩
    rcases Finset.mem_union.mp hm with hl|hr
    · exact ⟨Sum.inl ⟨P.val.val,hl⟩,Subtype.ext (Subtype.ext rfl)⟩
    · exact ⟨Sum.inr ⟨P.val.val,hr⟩,Subtype.ext (Subtype.ext rfl)⟩

noncomputable def primeUnionEquiv (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) :
    PrimeIndex k⊕T ≃ FreePrimeIndex lengthScale Q0 :=
  Equiv.ofBijective (primeUnionToFree lengthScale Q0 k T hs) (primeUnionToFree_bijective lengthScale Q0 k T hs hd)

lemma primeUnionEquiv_val (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) (P:PrimeIndex k⊕T) :
    (primeUnionEquiv lengthScale Q0 k T hs hd P).val.val=Sum.elim Subtype.val Subtype.val P := rfl

theorem prod_freePrimeIndex_eq {M:Type*} [CommMonoid M]
    (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) (f:Ideal Eis → M) :
    (∏P:FreePrimeIndex lengthScale Q0,f P.val.val)=(∏P:PrimeIndex k,f P.val)*(∏P:T,f P.val) := by
  calc
    _=(∏P:PrimeIndex k⊕T,f (Sum.elim Subtype.val Subtype.val P)):=
      (Fintype.prod_equiv (primeUnionEquiv lengthScale Q0 k T hs hd) _ _ (fun P=>rfl)).symm
    _=_:=Fintype.prod_sum_type _

end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

variable (I F Q0:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))

include I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop

theorem goodMaskFreePrimePool :
    freePrimePool (goodMaskMovingIdeal g r) Q0=
      CompletedGauss.primeSupport (rowResidualPart I (Ideal.span {m}*F)) ∪
        FreeReflection.pool I (Ideal.span {m}*F) Q0 := by
  apply freePrimePool_eq_residual_union _ _ _ _ hI
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hbad hcop
  exact goodMaskMovingIdeal_primeSupport I F hI hF.ne_zero m f z hm0 hf hz
    um am bm g hg hm u a b r hr hx

noncomputable def goodMaskFreePrimeEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex (goodMaskMovingIdeal g r) Q0 :=
  primeUnionEquiv _ _ _ _
    (goodMaskFreePrimePool I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop)
    (residual_nonresidual_disjoint I (Ideal.span {m}*F) Q0)

lemma goodMaskFreePrimeEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop P).val.val=
      Sum.elim Subtype.val Subtype.val P := rfl

lemma goodMaskFreePrimeEquiv_residual_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop
        (Sum.inl P)).val.val%6=1 := by
  change (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=1
  have hp:=(rowResidualPart_admissible I (Ideal.span {m}*F) hbad).2.2
    P.val (Multiset.mem_toFinset.mp P.property)
  rw [goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val hp.1 hp.2]
  exact completedLocalExponent_residual I F _ (dvd_mul_left F (Ideal.span {m})) P

lemma goodMaskFreePrimeEquiv_nonresidual_exponent
    (P:FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop
        (Sum.inr P)).val.val%6=completedLocalExponent I F P.val := by
  change (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=completedLocalExponent I F P.val
  let:P.val.IsMaximal:=FreeReflection.pool_maximal I (Ideal.span {m}*F) Q0 P
  exact goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val
    (FreeReflection.pool_good I (Ideal.span {m}*F) Q0 P)
    (FreeReflection.pool_odd I (Ideal.span {m}*F) Q0 P)

theorem goodMaskFreePrimeEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop P).val.val%6=
      Sum.elim (fun _=>1) (fun R=>completedLocalExponent I F R.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeEquiv_residual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P
  | inr P=>
    exact goodMaskFreePrimeEquiv_nonresidual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P

end

section

variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) : Finset β :=
  Finset.univ.filter (fun b=>e (Sum.inr b)∈A)

omit [Fintype α] [Fintype γ] in
lemma mem_optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) (b:β) :
    b∈optionalPrimeActive e A ↔ e (Sum.inr b)∈A := by
  simp only [optionalPrimeActive,Finset.mem_filter,Finset.mem_univ,true_and]

def activePrimeUnionMap (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A → A :=
  Sum.elim (fun a=>⟨e (Sum.inl a),hA a⟩)
    (fun b=>⟨e (Sum.inr b.val),(mem_optionalPrimeActive e A b.val).mp b.property⟩)

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionMap_bijective (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : Function.Bijective (activePrimeUnionMap e A hA) := by
  constructor
  · intro x y hxy
    have hv:=congrArg Subtype.val hxy
    cases x with
    | inl x=>cases y with
      | inl y=>exact congrArg Sum.inl (Sum.inl.inj (e.injective hv))
      | inr y=>cases e.injective hv
    | inr x=>cases y with
      | inl y=>cases e.injective hv
      | inr y=>exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (e.injective hv)))
  · intro a
    obtain ⟨x,hx⟩:=e.surjective a.val
    cases x with
    | inl x=>exact ⟨Sum.inl x,Subtype.ext hx⟩
    | inr x=>
      have hm:x∈optionalPrimeActive e A:=(mem_optionalPrimeActive e A x).mpr (hx.symm ▸ a.property)
      exact ⟨Sum.inr ⟨x,hm⟩,Subtype.ext hx⟩

noncomputable def activePrimeUnionEquiv (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A ≃ A :=
  Equiv.ofBijective (activePrimeUnionMap e A hA) (activePrimeUnionMap_bijective e A hA)

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inl (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (a:α) :
    (activePrimeUnionEquiv e A hA (Sum.inl a)).val=e (Sum.inl a) := rfl

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inr (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (b:optionalPrimeActive e A) :
    (activePrimeUnionEquiv e A hA (Sum.inr b)).val=e (Sum.inr b.val) := rfl

omit [Fintype γ] in
theorem prod_activePrimeUnionEquiv {M:Type*} [CommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∏a:A,f a)=
      (∏a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))*
        (∏b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∏x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.prod_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.prod_sum_type _

omit [Fintype γ] in
theorem sum_activePrimeUnionEquiv {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∑a:A,f a)=
      (∑a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))+
        (∑b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∑x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.sum_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.sum_sum_type _

theorem sum_prime_active_sets {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (f:Finset γ → M) :
    (∑A:Finset γ,f A)=∑A:Finset (α⊕β),f (A.map e.toEmbedding) := by
  exact (Fintype.sum_equiv e.finsetCongr _ _ (fun _=>rfl)).symm

end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def nonresidualPoolEquiv (R I Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R Q=rowMaskPart I Q) :
    FreeReflection.pool R Q Q0 ≃ FreeReflection.pool I Q Q0 := by
  have he:=FreeReflection.pool_eq_on_fiber R I Q Q0 hR hI hQ hA hT
  exact {
    toFun:=fun P=>⟨P.val,he ▸ P.property⟩
    invFun:=fun P=>⟨P.val,he.symm ▸ P.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }

lemma nonresidualPoolEquiv_val (R I Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I) (hT:rowMaskPart R Q=rowMaskPart I Q)
    (P:FreeReflection.pool R Q Q0) :
    (nonresidualPoolEquiv R I Q Q0 hR hI hQ hA hT P).val=P.val := rfl

lemma nonresidualPoolEquiv_exponent (R I F Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I) (hT:rowMaskPart R Q=rowMaskPart I Q)
    (P:FreeReflection.pool R Q Q0) :
    completedLocalExponent I F (nonresidualPoolEquiv R I Q Q0 hR hI hQ hA hT P).val=
      completedLocalExponent R F P.val :=
  (completedReflectionPool_exponent_eq R I F Q hR hI hQ hA hT
    ⟨P.val,FreeReflection.pool_subset R Q Q0 P.property⟩).symm

variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT

noncomputable def goodMaskFreePrimeFiberEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex (goodMaskMovingIdeal g r) Q0 :=
  (Equiv.sumCongr (Equiv.refl _)
    (nonresidualPoolEquiv R I (Ideal.span {m}*F) Q0 hR hI
      (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT)).trans
    (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop)

lemma goodMaskFreePrimeFiberEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT P).val.val=Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

theorem goodMaskFreePrimeFiberEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
        hbad hcop hA hT P).val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeEquiv_residual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P
  | inr P=>
    exact (goodMaskFreePrimeEquiv_nonresidual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop
      (nonresidualPoolEquiv R I (Ideal.span {m}*F) Q0 hR hI
        (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P)).trans
      (nonresidualPoolEquiv_exponent R I F (Ideal.span {m}*F) Q0 hR hI
        (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P)

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

section
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT

local notation "splitIndex" => (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT)

noncomputable def goodMaskActivePrimeEquiv
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A) :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A ≃ A :=
  activePrimeUnionEquiv splitIndex A hactive

lemma goodMaskActivePrimeEquiv_residual_val
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) :
    (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT A hactive (Sum.inl P)).val.val.val=P.val := rfl

lemma goodMaskActivePrimeEquiv_nonresidual_val
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:optionalPrimeActive splitIndex A) :
    (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT A hactive (Sum.inr P)).val.val.val=P.val.val := rfl

theorem goodMaskActivePrimeEquiv_exponent
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
        hbad hcop hA hT A hactive P).val.val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop hA hT (Sum.inl P)
  | inr P=>
    exact goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop hA hT (Sum.inr P.val)

end

lemma reflection_row_mask_bad (q:ℕ) (m:Eis) (F:Ideal Eis) :
    ∀P∈fixedBadPrimes,P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F := by
  intro P hP
  exact excluded_prime_dvd_row_mask q m F P (reflectionExcludedPrimes_bad q hP)

lemma residual_coprime_free_base (q:ℕ) (hq:q≠0) (m:Eis) (F I:Ideal Eis) :
    IsCoprime (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)})
      (rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) := by
  have hc:=residual_coprime_fixed_conductor q hq m F I
  rw [reflectionConductor_ideal] at hc
  exact hc.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))

end CanonicalRowCompletion

local instance (priority := 2000) residualLabelDecidableEq (A B:Type*) : DecidableEq (A⊕B) :=
  Classical.decEq _
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
variable {α β:Type*} [Fintype α] [Fintype β]

def residualZeroLabel (e:β→Fin 3) : α⊕β→Fin 3 := Sum.elim (fun _=>0) e

theorem sum_labels_drop_residual (f:(α⊕β→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (Sum.inl i)≠0)→f e=0) :
    (∑e:α⊕β→Fin 3,f e)=∑e:β→Fin 3,f (residualZeroLabel e) := by
  rw [←(Equiv.sumArrowEquivProdArrow α β (Fin 3)).symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_eq_single (fun _ : α=>0)]
  · rfl
  · intro d hd hn
    apply hzero
    have hx:∃i:α,d i≠0:=by
      by_contra h
      push Not at h
      exact hn (funext h)
    obtain ⟨i,hi⟩:=hx
    exact ⟨i,hi⟩
  · simp

lemma reflectedBranch_residual_label_zero
    (P:α⊕β→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (hbad:∃i:α,e (Sum.inl i)≠0) (n b:Eis) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_eq_right hi]

lemma reflectionExtractedDivisor_drop_residual
    (P:α⊕β→Ideal Eis) (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j e v=
      reflectionExtractedDivisor (fun i:β=>P (Sum.inr i)) (fun i=>j (Sum.inr i))
        (fun i=>e (Sum.inr i)) v := by
  simp only [reflectionExtractedDivisor,Fintype.prod_sum_type]
  have hz:(∏i:α,reflectionExtractedPrime (P (Sum.inl i)) (j (Sum.inl i)) (e (Sum.inl i)) v)=1 := by
    simp only [hj,reflectionExtractedPrime,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,
      false_and,false_or,ite_false,Finset.prod_const_one]
  rw [hz,one_mul]

lemma reflectedBranch_drop_residual
    (P:α⊕β→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:β→Fin 3) (n b:Eis) :
    reflectedBranch P hg j (residualZeroLabel e) n b=
      (∏i:α,bracket (actualSextic (P (Sum.inl i)) (hg (Sum.inl i))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (Sum.inr i)) (fun i=>hg (Sum.inr i))
        (fun i=>j (Sum.inr i)) e n b := by
  simp only [reflectedBranch,Fintype.prod_sum_type,residualZeroLabel,Sum.elim_inl,Sum.elim_inr]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_true]

end CompletedGauss
end

open scoped BigOperators Classical

local instance (priority := 2000) residualEquivDecidableEq (A B:Type*) : DecidableEq (A⊕B) :=
  Classical.decEq _
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι]

def residualLabelVia (E:α⊕β≃ι) (e:β→Fin 3) : ι→Fin 3 :=
  residualZeroLabel e ∘ E.symm

omit [Fintype α] [Fintype β] [Fintype ι] in
lemma residualLabelVia_apply (E:α⊕β≃ι) (e:β→Fin 3) (i:α⊕β) :
    residualLabelVia E e (E i)=residualZeroLabel e i := by
  simp only [residualLabelVia,Function.comp_apply,Equiv.symm_apply_apply]

theorem sum_labels_drop_residual_equiv (E:α⊕β≃ι) (f:(ι→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0) :
    (∑e:ι→Fin 3,f e)=∑e:β→Fin 3,f (residualLabelVia E e) := by
  let e:=Equiv.arrowCongr E (Equiv.refl (Fin 3))
  rw [←e.sum_comp f]
  apply sum_labels_drop_residual
  intro l hl
  apply hzero
  obtain ⟨i,hi⟩:=hl
  refine ⟨i,?_⟩
  simpa only [e,Equiv.arrowCongr_apply,Function.comp_apply,Equiv.refl_apply,Equiv.symm_apply_apply] using hi

omit [Fintype α] [Fintype β] in
lemma reflectedBranch_residual_zero_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0) (n b:Eis) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (E (Sum.inl i)))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_eq_right hi]

lemma reflectionExtractedDivisor_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j (residualLabelVia E e) v=
      reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e v := by
  calc
    _=reflectionExtractedDivisor (fun i=>P (E i)) (fun i=>j (E i)) (residualZeroLabel e) v := by
      unfold reflectionExtractedDivisor
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectionExtractedDivisor_drop_residual _ _ hj _ _

lemma reflectedBranch_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (n b:Eis) :
    reflectedBranch P hg j (residualLabelVia E e) n b=
      (∏i:α,bracket (actualSextic (P (E (Sum.inl i))) (hg (E (Sum.inl i)))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (E (Sum.inr i))) (fun i=>hg (E (Sum.inr i)))
        (fun i=>j (E (Sum.inr i))) e n b := by
  calc
    _=reflectedBranch (fun i=>P (E i)) (fun i=>hg (E i)) (fun i=>j (E i)) (residualZeroLabel e) n b := by
      unfold reflectedBranch
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectedBranch_drop_residual _ _ _ hj _ _ _

end CompletedGauss

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence -/

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

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι]

lemma nonzeroDualDilation_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1) (e:β→Fin 3)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    nonzeroDualDilation
      (reflectionExtractedDivisor P j (residualLabelVia E e) 1)
      (reflectionExtractedDivisor P j (residualLabelVia E e) 2)
      (reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) j _ 1)
      (reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) j _ 2) x=
    nonzeroDualDilation
      (reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e 1)
      (reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e 2)
      (reflectionExtractedDivisor_ne_zero _ (fun _i=>NeZero.ne _) _ _ 1)
      (reflectionExtractedDivisor_ne_zero _ (fun _i=>NeZero.ne _) _ _ 2) x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> apply Subtype.ext <;>
      simp only [nonzeroDualDilation,reflectionExtractedDivisor_drop_residual_equiv E P j hj]

lemma unextractedCuspCoefficient_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1) (e:β→Fin 3)
    (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ) (m:ℕ) (I J:Ideal Eis) :
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m I J=
      (σ m*(∏i:α,LocalReflectionBrackets.bracket (actualSextic (P (E (Sum.inl i))) (hg (E (Sum.inl i)))) 1
        (Ideal.Quotient.mk _ (primaryGenerator I*(primaryGenerator J)^3)))*
        η m I J*reflectedBranch (fun i:β=>P (E (Sum.inr i))) (fun i=>hg (E (Sum.inr i)))
          (fun i=>j (E (Sum.inr i))) e (primaryGenerator I) (primaryGenerator J))/
        ((CompletedDyadic.ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hj]
  ring

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι] {p:ι→Eis} {N:Eis}

omit [Fintype α] [Fintype β] in
lemma stratumBranchTerm_residual_zero_equiv (E:α⊕β≃ι)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (hres:∀i:α,j (E (Sum.inl i))=1)
    (u:Eisˣ) (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0)
    (W:ℝ→ℂ) (X:ℝ) (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    G.stratumBranchTerm D hp hg j u e W X x=0 := by
  dsimp only [stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient]
  rw [reflectedBranch_residual_zero_equiv E _ hg j hres e hbad,mul_zero,zero_div,zero_mul]

theorem smoothedValue_eq_nonresidual_equiv (E:α⊕β≃ι)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0)
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6) (hres:∀i:α,j (E (Sum.inl i))=1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr G.primary G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:β→Fin 3,
          let P:β→Ideal Eis:=fun i=>Ideal.span {p (E (Sum.inr i))}
          let jβ:β→ℕ:=fun i=>j (E (Sum.inr i))
          let A:=reflectionExtractedDivisor P jβ e 1
          let B:=reflectionExtractedDivisor P jβ e 2
          let hA:=reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) jβ e 1
          let hB:=reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) jβ e 2
          ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
            G.stratumBranchTerm D hp hg j u (residualLabelVia E e) W X (nonzeroDualDilation A B hA hB x) := by
  rw [G.smoothedValue_eq_extracted_branch_sums D hN hr hp hcop hg hchar j hj W a b ha hsupp hW X hX]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro u
  let f:(ι→Fin 3)→ℂ:=fun e=>
    ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      G.stratumBranchTerm D hp hg j u e W X
        (nonzeroDualDilation
          (reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1)
          (reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2)
          (reflectionExtractedDivisor_ne_zero _ (fun i=>NeZero.ne _) j e 1)
          (reflectionExtractedDivisor_ne_zero _ (fun i=>NeZero.ne _) j e 2) x)
  change (∑e,f e)=_
  have hz:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0 := by
    intro e he
    calc
      f e=∑'(_x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal),(0:ℂ) := by
        apply tsum_congr
        intro x
        exact G.stratumBranchTerm_residual_zero_equiv E D hp hg j hres u e he W X _
      _=0:=tsum_zero
  rw [sum_labels_drop_residual_equiv E f hz]
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [f]
  apply tsum_congr
  intro x
  rw [nonzeroDualDilation_residual_equiv E _ j hres]

end FixedFourierGeometry
end CubicEisenstein

open scoped BigOperators Classical MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance primeQuotientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

def primeInactiveFourierWeight {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (A:Finset ι) : ℂ :=
  ∏i∈(Finset.univ:Finset ι)\A,
    finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun x=>(actualSextic (Ideal.span {p i}) (hg i)^j i) x) 0

lemma primeRow_fourier_by_active {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (n:Eis) :
    finiteSexticRow (fun i=>Ideal.span {p i}) hg j n=
    ∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
      ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
        ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
          (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
        ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n) := by
  let (i:ι) : Field (Eis⧸Ideal.span {p i}) := Ideal.Quotient.field _
  have hpow:(Finset.univ:Finset ι).powerset=(Finset.univ:Finset (Finset ι)):=by
    ext A
    simp only [Finset.mem_powerset,Finset.subset_univ,Finset.mem_univ]
  have hFourier:=FixedRayActiveSet.fourier_inversion_by_active_set
    (fun i=>Eis⧸Ideal.span {p i})
    (fun i=>quotientTrace (p i) (hp i))
    (fun i=>GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (fun i x=>(actualSextic (Ideal.span {p i}) (hg i)^j i) x)
    (fun i=>Ideal.Quotient.mk (Ideal.span {p i}) n)
  simpa only [hpow,finiteSexticRow,primeInactiveFourierWeight,
    ControlledStratumArithmetic.fourierWeight] using hFourier

def activeStratumDatum {ι:Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
    {N a0 c0:Eis} {mode:Bool}
    (D:∀A:Finset ι,ControlledStratumArithmetic (fun i:A=>p i.val) N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hc0:c0≠0)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (A:Finset ι) (v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ) : SourceCuspDatum :=
  (D A).datum hN (primary_finset_product Finset.univ (fun i:A=>p i.val)
    (fun i _=>hprimary i.val)) hbase s (fun i=>hp i.val) hc0 v

theorem activeStratum_fourier_multiplier {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {N a0 c0:Eis} {mode:Bool}
    (D:∀A:Finset ι,ControlledStratumArithmetic (fun i:A=>p i.val) N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hc0:c0≠0)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n:Eis) :
    (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
      ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
        ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
          (fun i=>j i.val) v*
        ShortDraftTrace.breveE (-cuspFrequency n*
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point))=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        finiteSexticRow (fun i=>Ideal.span {p i}) hg j n := by
  have hlocal (A:Finset ι) (v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ) :
      ShortDraftTrace.breveE (-cuspFrequency n*
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i:A=>p i.val) (fun i _=>hprimary i.val))
      hbase s (fun i=>hp i.val) hc0 v n
  calc
    _=∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
        ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
          ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
            (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
          (ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
            ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n)):=by
      apply Finset.sum_congr rfl
      intro A hA
      apply congrArg (fun z:ℂ=>primeInactiveFourierWeight p hp hg j A*z)
      apply Finset.sum_congr rfl
      intro v hv
      exact congrArg (fun z:ℂ=>ControlledStratumArithmetic.fourierWeight
        (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
        (fun i=>j i.val) v*z) (hlocal A v)
    _=ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
            ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
              (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
            ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _=_:=congrArg (fun z:ℂ=>
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*z)
      (primeRow_fourier_by_active p hp hg j n).symm

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota CubicJacobiGlobal
open CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance fixedActiveQuotientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

abbrev FixedActiveCuspIndex {ι:Type*} (c:Eis) (p:ι→Eis) :=
  Σ_h:Eis⧸Ideal.span {c},ΣA:Finset ι,∀i:A,(Eis⧸Ideal.span {p i.val})ˣ

variable {ι:Type*} [Fintype ι] (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
variable (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
variable (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
variable (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h) (N:Eis)
variable (hN:∀h,(9:Eis)*(G h).c0∣N)
variable (D:∀h:Eis⧸Ideal.span {c},∀A:Finset ι,
  ControlledStratumArithmetic (fun i:A=>p i.val) N (G h).a0 (G h).c0 (G h).mode)

def fixedActiveCuspDatum (t:FixedActiveCuspIndex c p) : SourceCuspDatum :=
  activeStratumDatum p hp hprimary (D t.1) (hN t.1) (G t.1).denominator_ne_zero
    (G t.1).primary (G t.1).shape t.2.1 t.2.2

def fixedActiveCuspWeight (φ:Eis→*ℂ) (t:FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1*primeInactiveFourierWeight p hp hg j t.2.1*
    ControlledStratumArithmetic.fourierWeight (p:=fun i:t.2.1=>p i.val)
      (fun i:t.2.1=>hp i.val) (fun i:t.2.1=>hg i.val) (fun i=>j i.val) t.2.2

theorem fixedActiveCusp_fourier_multiplier (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ)
    (hχ:∀n,χ n=finiteSexticRow (fun i=>Ideal.span {p i}) hg j n) (n:Eis) :
    (∑t:FixedActiveCuspIndex c p,fixedActiveCuspWeight p hp hg j c hc φ t*
      ShortDraftTrace.breveE (-cuspFrequency n*
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point))=
      fixedThetaTwist (φ*χ) n := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveCuspWeight,fixedActiveCuspDatum]
  rw [fixedThetaTwist_fixed_fourier c hc Q hcQ φ χ hφ n]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=fixedThetaRowCoeff c hc φ h*
        (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
            ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
              (fun i=>j i.val) v*
            ShortDraftTrace.breveE (-cuspFrequency n*
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _=fixedThetaRowCoeff c hc φ h*
        (ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding (G h).a0/eisEmbedding (G h).c0))*
          finiteSexticRow (fun i=>Ideal.span {p i}) hg j n):=by
      rw [activeStratum_fourier_multiplier p hp hprimary hg j (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n]
    _=fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*χ n:=by
      rw [(G h).point,←hχ n, fixedRowFourierPhase_translation]
      ring

theorem completedT_fixed_active_strata (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ)
    (hχ:∀n,χ n=finiteSexticRow (fun i=>Ideal.span {p i}) hg j n)
    (hφχ:∀n,‖(φ*χ) n‖≤1) (Qall:Ideal Eis)
    (hperiod:CanonicalCoefficientClass.FactorsModulo Qall (φ*χ))
    (call:Eis) (hcall:call≠0) [Fintype (Eis⧸Ideal.span {call})]
    (hcallQ:Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (φ*χ) W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*
        ∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          (D h A).smoothedValue (hN h)
            (primary_finset_product Finset.univ (fun i:A=>p i.val) (fun i _=>hprimary i.val))
            (G h).primary (G h).shape (fun i=>hp i.val) (G h).denominator_ne_zero
            (fun i=>hg i.val) (fun i=>j i.val) W X := by
  rw [completedT_of_finite_cusp_multiplier (φ*χ) hφχ Qall hperiod call hcall hcallQ
    (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveCuspWeight p hp hg j c hc φ)
    (fixedActiveCusp_fourier_multiplier p hp hprimary hg j c hc G N hN D Q hcQ φ χ hφ hχ)
    W lo hi hlo hsupp hW X hX]
  congr 1
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveCuspWeight,fixedActiveCuspDatum,
    ControlledStratumArithmetic.smoothedValue,activeStratumDatum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  ring

end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def actualControlledSource (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (φ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  exact thetaDerivativeScalar⁻¹*
    ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*
      ∑A:Finset (FreePrimeIndex I Q),
        primeInactiveFourierWeight (freePrimaryPrime I Q) (freePrimaryPrime_ne_zero I Q hI)
          (freePrimaryPrime_good I Q hI)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6) A*
        (freePrimaryControlledStratum I Q hI c hcQ h (G h) A).smoothedValue
          (mul_dvd_mul_left 9 (G h).denominator_dvd)
          (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime I Q P.val)
            (fun P _=>freePrimaryPrime_primary I Q hI P.val))
          (G h).primary (G h).shape (fun P=>freePrimaryPrime_ne_zero I Q hI P.val)
          (G h).denominator_ne_zero (fun P=>freePrimaryPrime_good I Q hI P.val)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val.val%6) W X

theorem fixedFree_completedT_eq_actualControlledSource (I Q:Ideal Eis) (hI:Supported I)
    (hQ:Q≠0) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (hφn:∀n,‖φ n‖≤1)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (φ*freePrimeRow I hI Q) W X=actualControlledSource I Q hI c hc hcQ G φ W X := by
  let : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  let Qall:Ideal Eis:=Q*(∏P:FreePrimeIndex I Q,P.val.val)
  have hQall:Qall≠0:=mul_ne_zero hQ
    (finite_prime_product_ne_bot (fun P:FreePrimeIndex I Q=>P.val.val))
  let call:=ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall:call≠0:=by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}):=ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}):=Fintype.ofFinite _
  have hcallQ:Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall:=by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact completedT_fixed_active_strata (freePrimaryPrime I Q) (freePrimaryPrime_ne_zero I Q hI)
    (freePrimaryPrime_primary I Q hI) (freePrimaryPrime_good I Q hI)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
    c hc G (9*c) (fun h=>mul_dvd_mul_left 9 (G h).denominator_dvd)
    (fun h A=>freePrimaryControlledStratum I Q hI c hcQ h (G h) A)
    Q hcQ.le φ (freePrimeRow I hI Q) hφ (freePrimeRow_eq_primary_family I Q hI)
    (fixedFreeRow_norm I hI Q φ hφn) Qall (fixedFreeRow_periodic I hI Q φ hφ)
    call hcall hcallQ W lo hi hlo hsupp hW X hX

theorem rowTwist_completedT_eq_actualControlledSource
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hQ:Q≠0)
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (Ψ:Eis→*ℂ) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedThetaRowCoeff c hc φ h‖≤1) ∧
      ∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→Function.support W⊆Set.Icc lo hi→ ContDiff ℝ ∞ W→
        ∀X:ℝ,0<X→ completedT (rowTwist Ψ m f z) W X=
          actualControlledSource I (Q*Ideal.span {(72:Eis)}) hI c hc hcQ G φ W X := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hmod,hperiod,hnorm,hT⟩:=
    exists_actual_coprime_completed_row Ψ Q hQ hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,fixedThetaRowCoeff_norm c hc φ hφn,?_⟩
  intro W lo hi hlo hsupp hW X hX
  rw [hT W X]
  apply fixedFree_completedT_eq_actualControlledSource I _ hI _ c hc hcQ G φ hφ hφn W lo hi hlo hsupp hW X hX
  apply mul_ne_zero hQ
  simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
  norm_num

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

structure GoodMaskRowData (m f z:Eis) where
  maskUnit:Eisˣ
  maskLambda:ℕ
  maskTwo:ℕ
  maskGood:Eis
  maskSupported:Supported (Ideal.span {maskGood})
  maskPrimary:lambda^2∣maskGood-1
  maskFactor:m=maskUnit.val*lambda^maskLambda*(2:Eis)^maskTwo*maskGood
  numeratorUnit:Eisˣ
  numeratorLambda:ℕ
  numeratorTwo:ℕ
  numeratorGood:Eis
  numeratorSupported:Supported (Ideal.span {numeratorGood})
  numeratorPrimary:lambda^2∣numeratorGood-1
  numeratorFactor:f^4*z=numeratorUnit.val*lambda^numeratorLambda*(2:Eis)^numeratorTwo*numeratorGood

theorem exists_goodMaskRowData (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) :
    Nonempty (GoodMaskRowData m f z) := by
  obtain ⟨um,am,bm,g,hg,hpg,hmf⟩:=exists_supported_numerator_factorization m hm
  obtain ⟨u,a,b,r,hr,hpr,hxf⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  exact ⟨⟨um,am,bm,g,hg,hpg,hmf,u,a,b,r,hr,hpr,hxf⟩⟩

noncomputable def goodMaskRowData (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) :
    GoodMaskRowData m f z := Classical.choice (exists_goodMaskRowData m f z hm hf hz)

namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

def movingIdeal : Ideal Eis := goodMaskMovingIdeal D.maskGood D.numeratorGood

lemma movingSupported : Supported D.movingIdeal :=
  goodMaskMovingIdeal_supported D.maskGood D.numeratorGood D.maskSupported D.numeratorSupported

def fixedFactor (Ψ:Eis→*ℂ) (Q:Ideal Eis) : Eis→*ℂ :=
  (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported)*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)})

lemma numeratorFactor_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖(Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
      D.numeratorSupported) n‖≤1 := by
  change ‖Ψ n*numeratorBadTwist _ _ _ _ _ n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (numeratorBadTwist_norm _ _ _ _ _ n)

lemma fixedFactor_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) :
    CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) (D.fixedFactor Ψ Q) := by
  have hn:=fixedNumeratorTwist_periodic Ψ Q hΨ D.numeratorUnit D.numeratorLambda
    D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported) x*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) x=
    (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported) y*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) y
  rw [hn x y hxy,basePrimeRow_periodic D.movingIdeal D.movingSupported _ x y hxy]

lemma fixedFactor_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖D.fixedFactor Ψ Q n‖≤1 := by
  change ‖((Ψ*numeratorBadTwist _ _ _ _ _) n)*(basePrimeRow _ _ _ n)‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (D.numeratorFactor_norm Ψ hΨ n)).trans (basePrimeRow_norm _ _ _ n)

theorem row_primary (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=D.fixedFactor Ψ Q n*
      freePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) n := by
  rw [rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn]
  change (Ψ*numeratorBadTwist _ _ _ _ _) n*idealRowHom n D.movingIdeal= _
  rw [idealRowHom_fixed_conductor_split D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) n]
  simp only [fixedFactor,MonoidHom.mul_apply]
  ring

theorem completedT_eq_fixedFactor (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (W:ℝ→ℂ) (X:ℝ) :
    completedT (rowTwist Ψ m f z) W X=
      completedT (D.fixedFactor Ψ Q*freePrimeRow D.movingIdeal D.movingSupported
        (Q*Ideal.span {(72:Eis)})) W X :=
  completedT_congr_primary _ _ (D.row_primary Ψ Q hmLam hm2) W X

lemma fixedCoefficient_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})] (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h‖≤1 :=
  fixedThetaRowCoeff_norm c hc _ (D.fixedFactor_norm Ψ Q hΨ) h

end GoodMaskRowData

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (hm:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

noncomputable def primeFiberEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex D.movingIdeal Q0 :=
  goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorFactor hbad hcop hA hT

lemma primeFiberEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

lemma primeFiberEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (normalizedFactors D.movingIdeal).count
      (D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val) P :=
  goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorFactor hbad hcop hA hT P

local notation "splitIndex" => D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

noncomputable def activePrimeEquiv (A:Finset (FreePrimeIndex D.movingIdeal Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A) :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A ≃ A :=
  activePrimeUnionEquiv splitIndex A hactive

lemma activePrimeEquiv_exponent (A:Finset (FreePrimeIndex D.movingIdeal Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A) :
    (normalizedFactors D.movingIdeal).count
      (D.activePrimeEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT A hactive P).val.val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val.val) P := by
  cases P with
  | inl P=>exact D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inl P)
  | inr P=>exact D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P.val)

end GoodMaskRowData

noncomputable def fiberGoodMaskRowData (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (m:Eis)
    (hm:m≠0) (hF:F≠0) (hrows:∀I∈rows,I≠0) (u:Eisˣ)
    (I:representativeRowFiber rows R (Ideal.span {m}*F)) :
    GoodMaskRowData m (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I.val) :=
  goodMaskRowData _ _ _ hm (ConcretePrimeRowBridge.idealGenerator_ne_zero F hF)
    (mul_ne_zero u.ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero I.val
      (hrows I.val (Finset.mem_filter.mp I.property).1)))

end CanonicalRowCompletion

end

end OAI

end

