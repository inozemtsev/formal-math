module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part021

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / RowCompletion / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.RowCompletion.RowAmplitudes -/

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

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (Q:Ideal Eis) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})))

abbrev activeStratum :=
  freePrimaryControlledStratum D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported c hcQ h G A

def sourceRowScalar (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ) : ℂ := by
  letI : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  exact fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
    G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)*
    (D.activeStratum Q c hcQ h G A).modelRowPhase G.shape
      (fun P=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val)
      (fun P=>freePrimaryPrime_good D.movingIdeal _ D.movingSupported P.val)
      (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6) u n

lemma sourceRowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (u:Eisˣ) (n:ℕ) :
    ‖D.sourceRowScalar Q c hc hcQ h G A Ψ u n‖≤1 := by
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  have hp:(G.c0*∏P:A,freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)≠0:=
    mul_ne_zero G.denominator_ne_zero (Finset.prod_ne_zero_iff.mpr
      (fun P _=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val))
  have hs:=G.shape.stratumShapeFactor_norm _ hp
  have hr:=(D.activeStratum Q c hcQ h G A).modelRowPhase_norm
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ
      (fun P:A=>freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)
      (fun P _=>freePrimaryPrime_primary D.movingIdeal _ D.movingSupported P.val))
    G.primary G.shape
    (fun P=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val)
    (fun P=>freePrimaryPrime_good D.movingIdeal _ D.movingSupported P.val)
    (fun P=>freePrimaryPrime_odd D.movingIdeal _ D.movingSupported P.val)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6)
    (fun _=>Nat.mod_lt _ (by decide)) u n
  unfold sourceRowScalar
  rw [norm_mul,norm_mul,hs,hr,mul_one,mul_one]
  exact D.fixedCoefficient_norm Ψ Q hΨ c hc h

def sourceRowResidue : G.PhaseResidue :=
  Ideal.Quotient.mk _ (-((D.activeStratum Q c hcQ h G A).matrix (fun _=>1) 1 1)*
    (D.activeStratum Q c hcQ h G A).U)

def selectedSourceRowScalar (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ)
    (rho:G.PhaseResidue) (k dN dB:Ideal Eis) : ℂ :=
  if rho=D.sourceRowResidue Q c hcQ h G A then
    D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB else 0

lemma selectedSourceRowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (u:Eisˣ) (n:ℕ)
    (rho:G.PhaseResidue) (k dN dB:Ideal Eis) :
    ‖D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB‖≤1 := by
  unfold selectedSourceRowScalar
  split_ifs
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (D.sourceRowScalar_norm Q c hc hcQ h G A Ψ hΨ u n)).trans (residualArgumentPhase_norm_le_one k 1 dN dB)
  · simp

lemma sum_selectedSourceRowScalar [Fintype G.PhaseResidue]
    (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ) (k dN dB:Ideal Eis) :
    (∑rho:G.PhaseResidue,D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB)=
      D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB := by
  simp only [selectedSourceRowScalar,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end GoodMaskRowData
end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

theorem completedT_eq_actualControlledSource
    (Q:Ideal Eis) (hQ:Q≠0) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (Ψ:Eis→*ℂ) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ m f z) W X=
      actualControlledSource D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported
        c hc hcQ G (D.fixedFactor Ψ Q) W X := by
  rw [D.completedT_eq_fixedFactor Ψ Q hmLam hm2 W X]
  apply fixedFree_completedT_eq_actualControlledSource D.movingIdeal _ D.movingSupported _
    c hc hcQ G (D.fixedFactor Ψ Q) (D.fixedFactor_periodic Ψ Q hΨ)
    (D.fixedFactor_norm Ψ Q hΨnorm) W lo hi hlo hsupp hW X hX
  apply mul_ne_zero hQ
  apply Ideal.span_singleton_eq_bot.not.mpr
  norm_num

end GoodMaskRowData
end

variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def residualActivePrimes (e:α⊕β ≃ γ) : Finset γ :=
  Finset.univ.image (fun a:α=>e (Sum.inl a))

omit [Fintype β] [Fintype γ] in
lemma residualActivePrimes_not_inr (e:α⊕β ≃ γ) (b:β) :
    e (Sum.inr b)∉residualActivePrimes e := by
  intro h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h
  cases e.injective ha

def nonresidualComplementMap (e:α⊕β ≃ γ) : β → {g:γ // g∉residualActivePrimes e} :=
  fun b=>⟨e (Sum.inr b),residualActivePrimes_not_inr e b⟩

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementMap_bijective (e:α⊕β ≃ γ) :
    Function.Bijective (nonresidualComplementMap e) := by
  constructor
  · intro a b hab
    exact Sum.inr.inj (e.injective (congrArg Subtype.val hab))
  · intro g
    obtain ⟨x,hx⟩:=e.surjective g.val
    cases x with
    | inl a=>
      exact (g.property (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,hx⟩)).elim
    | inr b=>exact ⟨b,Subtype.ext hx⟩

noncomputable def nonresidualComplementEquiv (e:α⊕β ≃ γ) :
    β ≃ {g:γ // g∉residualActivePrimes e} :=
  Equiv.ofBijective (nonresidualComplementMap e) (nonresidualComplementMap_bijective e)

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementEquiv_val (e:α⊕β ≃ γ) (b:β) :
    (nonresidualComplementEquiv e b).val=e (Sum.inr b) := rfl

omit [Fintype β] [Fintype γ] in
lemma complementActive_image (e:α⊕β ≃ γ) (B:Finset β) :
    (B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val=
      B.image (fun b=>e (Sum.inr b)) := by
  simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
    Equiv.toEmbedding_apply,nonresidualComplementEquiv_val]

lemma inactive_product_nonresidual (e:α⊕β ≃ γ) (z:γ → ℂ) (B:Finset β) :
    (∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
      B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)=
      ∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)) := by
  symm
  apply Finset.prod_equiv (nonresidualComplementEquiv e)
  · intro b
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_map_equiv,
      Equiv.symm_apply_apply]
  · intro b hb
    rfl

theorem inactive_weight_nonresidual_subsets (e:α⊕β ≃ γ) (z:γ → ℂ)
    (hz:∀a:α,z (e (Sum.inl a))=0) (F:Finset γ → ℂ) :
    (∑A:Finset γ,(∏g∈(Finset.univ:Finset γ)\A,z g)*F A)=
      ∑B:Finset β,(∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)))*
        F (residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))) := by
  have hres:∀g∈residualActivePrimes e,z g=0:=by
    intro g hg
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hg
    exact hz a
  rw [CompletedGauss.inactive_weight_optional_active (residualActivePrimes e) z hres F]
  symm
  apply Fintype.sum_equiv (nonresidualComplementEquiv e).finsetCongr
  intro B
  change _=(∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
    B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)*
    F (residualActivePrimes e∪(B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val)
  rw [inactive_product_nonresidual,complementActive_image]

end CanonicalRowCompletion

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma active_product_residual_equiv {ι β:Type*} [Fintype ι] [Fintype β]
    (I Q:Ideal Eis) (P:ι→Ideal Eis) (R:β→Ideal Eis)
    (E:PrimeIndex (rowResidualPart I Q)⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r) :
    (∏i,P i)=rowResidualPart I Q*∏i,R i := by
  rw [←E.prod_comp,Fintype.prod_sum_type]
  simp only [hres,hnonres]
  congr 1
  change (∏r:primeSupport (rowResidualPart I Q),r.val)=rowResidualPart I Q
  exact (Finset.prod_coe_sort (primeSupport (rowResidualPart I Q))
      (fun r : Ideal Eis => r)).trans
    (IdealMobiusDivisorSum.squarefree_support_product_self (rowResidualPart_squarefree I Q))

lemma actual_bracket_ideal_congr (P Q:Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hP:lambda∉P) (hQ:lambda∉Q) (hPQ:P=Q) (j:ℕ) (z:Eis) :
    bracket (actualSextic P hP) j (Ideal.Quotient.mk P z)=
      bracket (actualSextic Q hQ) j (Ideal.Quotient.mk Q z) := by
  subst Q
  rfl

theorem residual_equiv_coefficient {ι β:Type*} [Fintype ι] [Fintype β]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (R:β→Ideal Eis) [∀i,(R i).IsMaximal] (hR:∀i,lambda∉R i)
    (E:PrimeIndex (rowResidualPart I Q)⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r)
    (j:ι→ℕ) (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F (R r))
    (e:β→Fin 3) (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor R (fun r=>completedLocalExponent I F (R r)) e 1
    let B:=reflectionExtractedDivisor R (fun r=>completedLocalExponent I F (R r)) e 2
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m (A*n) (B*b)=
      4*canonicalRawBranchCoefficient R hR (fun r=>completedLocalExponent I F (R r)) e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>σ l*residualArgumentPhase (rowResidualPart I Q) 1 A B)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hjres]
  have hchar (r:PrimeIndex (rowResidualPart I Q)) (z:Eis) :
      bracket (actualSextic (P (E (Sum.inl r))) (hg (E (Sum.inl r)))) 1 (Ideal.Quotient.mk _ z)=
      bracket (actualSextic r.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) r))
        (completedLocalExponent I F r.val) (Ideal.Quotient.mk _ z) := by
    rw [completedLocalExponent_residual I F Q hFQ]
    exact actual_bracket_ideal_congr _ _ _ _ (hres r) 1 z
  have hnbranch (a b:Eis):
      reflectedBranch (fun r=>P (E (Sum.inr r))) (fun r=>hg (E (Sum.inr r)))
        (fun r=>j (E (Sum.inr r))) e a b=
      reflectedBranch R hR (fun r=>completedLocalExponent I F (R r)) e a b := by
    unfold reflectedBranch
    apply Finset.prod_congr rfl
    intro r hr
    change reflectedLocalPiece (P (E (Sum.inr r))) _ (j (E (Sum.inr r))) (e r) a b=_
    simp only [hnonres r,hjnonres r]
  simp_rw [hchar]
  rw [hnbranch]
  have ht:=residual_coefficient_eq_canonical_argument I F Q hFQ hbad R hR
    (fun r=>completedLocalExponent I F (R r)) e ρ q (fun _=>1) η σ m n b
  simp only [one_mul] at ht
  convert ht using 1 ; ring

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

theorem stratumBranchTerm_tsum_eq_rawValue
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {I F Q:Ideal Eis} {levelBound K:ℝ} (d:ReflectedBranchData levelBound K I F Q)
    (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q) (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q)) (hk:k.val=rowResidualPart I Q)
    (E:PrimeIndex (rowResidualPart I Q)⊕d.primes≃ι)
    (hres:∀r,Ideal.span {p (E (Sum.inl r))}=r.val)
    (hnonres:∀r,Ideal.span {p (E (Sum.inr r))}=r.val)
    (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F r.val)
    (hlevel:d.levelScale=G.levelScale) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    letI : ∀r:d.primes,r.val.IsMaximal:=d.maximal
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      G.stratumBranchTerm D hp hg j u (residualLabelVia E d.label) W X (nonzeroDualDilation A B hA hB x))=
      4*d.rawValue
        (fun m n b=>G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m (A*n) (B*b))
        (fun m k'=>D.modelRowPhase G.shape hp hg j u m*residualArgumentPhase k'.val 1 A B)
        W X 1 completedRamifiedStep k := by
  let : ∀r:d.primes,r.val.IsMaximal:=d.maximal
  dsimp only
  let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 1
  let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 2
  let η:=G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u
  let σ:=D.modelRowPhase G.shape hp hg j u
  have hfull:Ideal.span {∏i,p i}=k.val*∏r:d.primes,r.val := by
    rw [FiniteGaussPhase.span_finset_prod,hk]
    exact active_product_residual_equiv I Q (fun i=>Ideal.span {p i})
      (fun r:d.primes=>r.val) E hres hnonres
  have hk0:k.val≠0:=(mem_idealRange.mp k.property).1.1
  unfold ReflectedBranchData.rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  have hcoef:=residual_equiv_coefficient I F Q hFQ hbad (fun i=>Ideal.span {p i}) hg
    (fun r:d.primes=>r.val) d.good E hres hnonres j hjres hjnonres d.label
    1 completedRamifiedStep η σ x.1 x.2.1.val x.2.2.val
  have harg:
      (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm (A*x.2.1.val):ℝ)*
        (Ideal.absNorm (B*x.2.2.val):ℝ)^3=
      ((completedBranchScale K (X/d.levelScale) I F Q (fun r:d.primes=>r.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2)*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
        (Ideal.absNorm x.2.2.val:ℝ)^3 := by
    rw [hlevel,completedBranchScale_raw_argument K X G.levelScale (1*completedRamifiedStep^x.1)
      I F Q (fun r:d.primes=>r.val) d.label k.val x.2.1.val x.2.2.val hK G.levelScale_pos hk0]
    rw [hfull]
    simp only [map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  dsimp only [stratumBranchTerm,nonzeroDualDilation,rawDualKernelTerm]
  change unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j (residualLabelVia E d.label)
      1 completedRamifiedStep η σ x.1 (A*x.2.1.val) (B*x.2.2.val)*_=_
  rw [hcoef,harg,hk]
  exact mul_assoc _ _ _

end FixedFourierGeometry
end CubicEisenstein

open scoped Classical BigOperators ContDiff

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass
open ConcretePrimeRowBridge SecondPassArithmetic
local notation "Eis" => ActualEisensteinCubic.O

def HasFixedShellModels (S:Finset (Ideal Eis)) (base:Eis→*ℂ)
    (rays:ℕ) (scale:ℂ) (ρ q level:ℝ) : Prop :=
  ∀ Ψ:Eis→*ℂ,IsBaseRayTwist base Ψ→∀m:Eis,m≠0→
    ∀ F:ℝ,∀f:idealRange F,∀u:Eisˣ,∀ W:ℝ→ℂ,∀a b:ℝ,
      0<a→Function.support W⊆Set.Icc a b→ ContDiff ℝ ∞ W→
      ∀K X:ℝ,0<K→0<X→∀rows:Finset (Ideal Eis),
        (∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)→
        HasExactCompletedModels rays rows K X ρ q level f.val
          (Ideal.span {m*excludedGenerator S}*f.val) W
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) scale

lemma normTwistedSource_contDiff (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) :
    ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W t) := by
  have he:(CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t:ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t:=by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  rw [←he]
  exact (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t).smooth ⊤

theorem hasCanonicalThetaModels_of_fixed_shell_models
    (S:Finset (Ideal Eis)) (base:Eis→*ℂ) (rays:ℕ) (scale:ℂ) (ρ q level:ℝ)
    (hmodels:HasFixedShellModels S base rays scale ρ q level) :
    HasCanonicalThetaModels S base ρ q level := by
  intro A hA W hs hW κ hκ
  refine ⟨(rays:ℝ)^2*‖scale‖^2,by positivity,?_⟩
  intro Z K X F θ hZ hK hX hF hFZ Ψ hΨ m hm
  dsimp only
  intro hmargin
  refine ⟨rays,scale,?_,?_⟩
  · exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hκ.le)
  · intro u f H hH
    have hH0:H≠0:=((mem_shortCubeRange _ H).mp hH).1
    have hHN:(0:ℝ)<(Ideal.absNorm H:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hH0)
    have hXH:0<X/(Ideal.absNorm H:ℝ)^3:=by positivity
    have hsTw:Function.support (CompletedHeight.normTwistedSource W θ)⊆
        Set.Icc (Real.exp (-A)) (Real.exp A):=
      (CompletedHeight.normTwistedSource_support W θ).trans hs
    have hTw:=normTwistedSource_contDiff W (Real.exp (-A)) (Real.exp A)
      (Real.exp_pos _) hs hW θ
    let rows:=((firstFrequencyDisk (2*K)).erase 0).image (fun z:Eis=>Ideal.span {z})
    have hrows:∀I∈rows,I≠0:=by
      intro I hI
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
      exact Ideal.span_singleton_eq_bot.not.mpr (Finset.mem_erase.mp hz).1
    intro j hj
    exact hmodels Ψ hΨ m hm F f u (CompletedHeight.normTwistedSource W θ)
      (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) hsTw hTw
      ((2:ℝ)^j) (X/(Ideal.absNorm H:ℝ)^3) (by positivity) hXH
      (completedRowDyad rows j) (completedRowDyad_bounds rows j hrows)

end CanonicalRowCompletion

open scoped Classical BigOperators

namespace CompletedGauss.ReflectedBranchData
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
variable {levelBound K:ℝ} {I F Q:Ideal Eis}
variable (d:ReflectedBranchData levelBound K I F Q)
variable (η:ℕ→Ideal Eis→Ideal Eis→ℂ)
variable (σ τ:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
variable (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q))

lemma rawValue_congr_phase_at (h:∀m,σ m k=τ m k) :
    d.rawValue η σ W X ρ q k=d.rawValue η τ W X ρ q k := by
  unfold rawValue
  apply tsum_congr
  intro x
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,h]

lemma rawValue_zero_phase : d.rawValue η (fun _ _=>0) W X ρ q k=0 := by
  unfold rawValue
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,zero_mul,tsum_zero]

lemma rawValue_mul_phase_at (a:idealRange (completedResidualScale K I Q)→ℂ) :
    d.rawValue η (fun m l=>a l*σ m l) W X ρ q k=a k*d.rawValue η σ W X ρ q k := by
  unfold rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  unfold rawDualKernelTerm canonicalRawBranchCoefficient
  ring

lemma rawValue_select_phase_at (P:idealRange (completedResidualScale K I Q)→Prop)
    [DecidablePred P] :
    d.rawValue η (fun m l=>if P l then σ m l else 0) W X ρ q k=
      if P k then d.rawValue η σ W X ρ q k else 0 := by
  by_cases hp:P k
  · rw [ite_eq_left hp]
    exact d.rawValue_congr_phase_at η _ σ W X ρ q k (fun m=>ite_eq_left hp)
  · rw [ite_eq_right hp]
    calc
      _=d.rawValue η (fun _ _=>0) W X ρ q k:=
        d.rawValue_congr_phase_at η _ _ W X ρ q k (fun m=>ite_eq_right hp)
      _=0:=d.rawValue_zero_phase η W X ρ q k

end CompletedGauss.ReflectedBranchData

open scoped BigOperators Classical

namespace CanonicalRowCompletion
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) : Finset γ :=
  residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))

omit [Fintype β] [Fintype γ] in
lemma completeActiveSet_residual (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    e (Sum.inl a)∈completeActiveSet e B :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)

omit [Fintype γ] in
lemma optionalPrimeActive_completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) :
    optionalPrimeActive e (completeActiveSet e B)=B := by
  ext b
  rw [mem_optionalPrimeActive]
  change e (Sum.inr b)∈residualActivePrimes e∪B.image (fun b=>e (Sum.inr b)) ↔ b∈B
  simp only [Finset.mem_union,residualActivePrimes_not_inr,false_or,Finset.mem_image]
  constructor
  · rintro ⟨b',hb',he⟩
    have hb:b'=b:=Sum.inr.inj (e.injective he)
    exact hb ▸ hb'
  · intro hb
    exact ⟨b,hb,rfl⟩

noncomputable def selectedActiveEquiv (e:α⊕β ≃ γ) (B:Finset β) :
    α⊕B ≃ completeActiveSet e B := by
  let t : B ≃ optionalPrimeActive e (completeActiveSet e B):={
    toFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    invFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (Equiv.sumCongr (Equiv.refl _) t).trans
    (activePrimeUnionEquiv e (completeActiveSet e B) (completeActiveSet_residual e B))

omit [Fintype γ] in
lemma selectedActiveEquiv_inl (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    (selectedActiveEquiv e B (Sum.inl a)).val=e (Sum.inl a) := rfl

omit [Fintype γ] in
lemma selectedActiveEquiv_inr (e:α⊕β ≃ γ) (B:Finset β) (b:B) :
    (selectedActiveEquiv e B (Sum.inr b)).val=e (Sum.inr b.val) := rfl

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def maskElement (q:ℕ) (m:Eis) : Eis := m*excludedGenerator (reflectionExcludedPrimes q)
def maskIdeal (q:ℕ) (m:Eis) (F:Ideal Eis) : Ideal Eis := Ideal.span {maskElement q m}*F
def freeConductor (q:ℕ) : Ideal Eis := CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}
abbrev RowIndex (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis)) (R F:Ideal Eis) :=
  representativeRowFiber rows R (maskIdeal q m F)

lemma maskElement_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) : maskElement q m≠0 :=
  mul_ne_zero hm (reflectionExcludedGenerator_ne_zero q)
lemma maskIdeal_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) (F:Ideal Eis) (hF:F≠0) : maskIdeal q m F≠0 :=
  mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (maskElement_ne_zero q m hm)) hF
lemma mask_bad (q:ℕ) (m:Eis) (F:Ideal Eis) : ∀P∈fixedBadPrimes,P∣maskIdeal q m F :=
  reflection_row_mask_bad q m F

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)

noncomputable def data (J:RowIndex q m rows R F) :
    GoodMaskRowData (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val) :=
  fiberGoodMaskRowData rows R F (maskElement q m) (maskElement_ne_zero q m hm) hF.ne_zero hrows v J

noncomputable def splitIndex (J:RowIndex q m rows R F) :
    PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.pool R (maskIdeal q m F) (freeConductor q) ≃
      FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) := by
  have hJ:J.val≠0:=hrows J.val (Finset.mem_filter.mp J.property).1
  have hz:Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator J.val}=J.val:=by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
  have parts:=representativeFiber_parts rows R (maskIdeal q m F) J
  exact (data q m hm rows R F hF hrows v J).primeFiberEquiv R J.val F (freeConductor q)
    hR hJ hF (maskElement_ne_zero q m hm) (ConcretePrimeRowBridge.span_idealGenerator F) hz
    (mask_bad q m F) (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm

noncomputable def activeSet (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    Finset (FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)) :=
  completeActiveSet (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e)

def columnDivisor (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (side:Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor
    (fun P:FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e=>P.val)
    (fun P=>completedLocalExponent R F P.val)
    (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e) side

variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

noncomputable def rowScalar (Ψ:Eis→*ℂ)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) : ℂ :=
  (data q m hm rows R F hF hrows v J).selectedSourceRowScalar
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) Ψ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

lemma rowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) :
    ‖rowScalar q hq m hm rows R F hR hF hrows v Ψ x n J‖≤1 := by
  exact (data q m hm rows R F hF hrows v J).selectedSourceRowScalar_norm
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) Ψ hΨ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

noncomputable def reflectedFiber (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      (fixedCuspLevelBound (reflectionConductor q)) K R F (maskIdeal q m F) :=
  FreeReflection.fixedRayFiberFromRows (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)

lemma reflectedFiber_rowPhase (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq))
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6) (i:ℕ×ℕ×ℕ) :
    ((reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)).rowPhase i
        (fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
          (fun I hI=>⟨hrows I hI,hbound I hI⟩) J)=
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) i.1 J := by
  exact FreeReflection.fixedRayFiberFromRows_rowPhase _ _ _ _ _ _ _ _ _ _ _ _
    (mask_bad q m F) (fun I hI=>⟨hrows I hI,hbound I hI⟩) J ray e i

end CanonicalRowCompletion.ActualFiber

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.ActiveReindexing -/

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
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma active_product_admissible_equiv {ι β:Type*} [Fintype ι] [Fintype β]
    (k:Ideal Eis) (hk:Squarefree k) (P:ι→Ideal Eis) (R:β→Ideal Eis)
    (E:PrimeIndex k⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r) :
    (∏i,P i)=k*∏i,R i := by
  rw [←E.prod_comp,Fintype.prod_sum_type]
  simp only [hres,hnonres]
  congr 1
  change (∏r:primeSupport k,r.val)=k
  exact (Finset.prod_coe_sort (primeSupport k) (fun r:Ideal Eis=>r)).trans
    (IdealMobiusDivisorSum.squarefree_support_product_self hk)

theorem residual_bracket_extracted_admissible (k:Ideal Eis) (hk:Admissible k)
    (z:Eis) (A B n b:Ideal Eis) :
    (∏P:PrimeIndex k,
      bracket (actualSextic P.val (admissiblePrimeGood k hk P)) 1
        (Ideal.Quotient.mk P.val (z*primaryGenerator (A*n)*(primaryGenerator (B*b))^3)))=
      residualArgumentPhase k z A B*quadraticRow k (primaryGenerator (n*b)) := by
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex k hk,←quadraticRow_eq_primeIndex k hk]
  simp only [primaryGenerator_mul,residualArgumentPhase,canonical_quadraticRow_argument_mul k hk]
  ring

theorem residual_coefficient_eq_canonical_admissible {ι:Type*} [Fintype ι]
    (k:Ideal Eis) (hk:Admissible k)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (residualArgument:ℕ→Eis)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor P j e 1
    let B:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex k,
        bracket (actualSextic p.val (admissiblePrimeGood k hk p)) 1
          (Ideal.Quotient.mk p.val (residualArgument m*primaryGenerator (A*n)*(primaryGenerator (B*b))^3))) *
      η m (A*n) (B*b)*reflectedBranch P hg j e (primaryGenerator (A*n)) (primaryGenerator (B*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (A*n):ℝ)*(Ideal.absNorm (B*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>rowPhase l*residualArgumentPhase k (residualArgument l) A B) k m n b := by
  dsimp only
  rw [residual_bracket_extracted_admissible k hk]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

theorem residual_equiv_coefficient_admissible {ι β:Type*} [Fintype ι] [Fintype β]
    (k:Ideal Eis) (hk:Admissible k)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (R:β→Ideal Eis) [∀i,(R i).IsMaximal] (hR:∀i,lambda∉R i)
    (E:PrimeIndex k⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r)
    (j:ι→ℕ) (jβ:β→ℕ) (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=jβ r)
    (e:β→Fin 3) (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor R jβ e 1
    let B:=reflectionExtractedDivisor R jβ e 2
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m (A*n) (B*b)=
      4*canonicalRawBranchCoefficient R hR jβ e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>σ l*residualArgumentPhase k 1 A B) k m n b := by
  dsimp only
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hjres]
  have hchar (r:PrimeIndex k) (z:Eis) :
      bracket (actualSextic (P (E (Sum.inl r))) (hg (E (Sum.inl r)))) 1 (Ideal.Quotient.mk _ z)=
      bracket (actualSextic r.val (admissiblePrimeGood k hk r)) 1 (Ideal.Quotient.mk _ z) :=
    actual_bracket_ideal_congr _ _ _ _ (hres r) 1 z
  have hnbranch (a b:Eis):
      reflectedBranch (fun r=>P (E (Sum.inr r))) (fun r=>hg (E (Sum.inr r)))
        (fun r=>j (E (Sum.inr r))) e a b=reflectedBranch R hR jβ e a b := by
    unfold reflectedBranch
    apply Finset.prod_congr rfl
    intro r hr
    change reflectedLocalPiece (P (E (Sum.inr r))) _ (j (E (Sum.inr r))) (e r) a b=_
    simp only [hnonres r,hjnonres r]
  simp_rw [hchar]
  rw [hnbranch]
  have ht:=residual_coefficient_eq_canonical_admissible k hk R hR jβ e ρ q (fun _=>1) η σ m n b
  simp only [one_mul] at ht
  convert ht using 1 ; ring

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

theorem stratumBranchTerm_tsum_eq_rawValue_at_row
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {I F Q:Ideal Eis} {levelBound K:ℝ} (d:ReflectedBranchData levelBound K I F Q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (E:PrimeIndex k.val⊕d.primes≃ι)
    (hres:∀r,Ideal.span {p (E (Sum.inl r))}=r.val)
    (hnonres:∀r,Ideal.span {p (E (Sum.inr r))}=r.val)
    (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F r.val)
    (hlevel:d.levelScale=G.levelScale) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    letI : ∀r:d.primes,r.val.IsMaximal:=d.maximal
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      G.stratumBranchTerm D hp hg j u (residualLabelVia E d.label) W X (nonzeroDualDilation A B hA hB x))=
      4*d.rawValue
        (fun m n b=>G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m (A*n) (B*b))
        (fun m k'=>D.modelRowPhase G.shape hp hg j u m*residualArgumentPhase k'.val 1 A B)
        W X 1 completedRamifiedStep k := by
  let : ∀r:d.primes,r.val.IsMaximal:=d.maximal
  dsimp only
  let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 1
  let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 2
  let η:=G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u
  let σ:=D.modelRowPhase G.shape hp hg j u
  have hfull:Ideal.span {∏i,p i}=k.val*∏r:d.primes,r.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact active_product_admissible_equiv k.val (mem_idealRange.mp k.property).1.2.1 (fun i=>Ideal.span {p i})
      (fun r:d.primes=>r.val) E hres hnonres
  have hk0:k.val≠0:=(mem_idealRange.mp k.property).1.1
  unfold ReflectedBranchData.rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  have hcoef:=residual_equiv_coefficient_admissible k.val (mem_idealRange.mp k.property).1 (fun i=>Ideal.span {p i}) hg
    (fun r:d.primes=>r.val) d.good E hres hnonres j
    (fun r=>completedLocalExponent I F r.val) hjres hjnonres d.label
    1 completedRamifiedStep η σ x.1 x.2.1.val x.2.2.val
  have harg:
      (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm (A*x.2.1.val):ℝ)*
        (Ideal.absNorm (B*x.2.2.val):ℝ)^3=
      ((completedBranchScale K (X/d.levelScale) I F Q (fun r:d.primes=>r.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2)*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
        (Ideal.absNorm x.2.2.val:ℝ)^3 := by
    rw [hlevel,completedBranchScale_raw_argument K X G.levelScale (1*completedRamifiedStep^x.1)
      I F Q (fun r:d.primes=>r.val) d.label k.val x.2.1.val x.2.2.val hK G.levelScale_pos hk0]
    rw [hfull]
    simp only [map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  dsimp only [stratumBranchTerm,nonzeroDualDilation,rawDualKernelTerm]
  change unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j (residualLabelVia E d.label)
      1 completedRamifiedStep η σ x.1 (A*x.2.1.val) (B*x.2.2.val)*_=_
  rw [hcoef,harg]
  exact mul_assoc _ _ _

end FixedFourierGeometry
end CubicEisenstein

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

theorem sixPhaseFixedCuspBranch_value_eq_rawValue
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound
      e cusp u phaseArray hphase rowPhase hrow
    d.value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArrayWithPhase cusp u phaseArray) rowPhase W X ρ q k := by
  exact (sixReflectedBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase_value cusp u phaseArray hphase rowPhase hrow
      W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end CompletedGauss.FreeReflection
namespace CubicEisenstein.FixedFourierGeometry
open ActualEisensteinCubic CompletedGauss CompletedGauss.FreeReflection CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

theorem sixPhaseFixedCuspBranch_value_eq_geometric_rawValue
    {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (hbound:G.levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (v:G.PhaseResidue) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound G.levelScale G.levelScale_pos hbound
      e G.shape.index u (G.staticPhase v u) (G.staticPhase_norm_le_one v u) rowPhase hrow
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    d.value W X ρ q k=
      d.rawValue (fun m n b=>G.array v u m (A*n) (B*b)) rowPhase W X ρ q k := by
  exact sixPhaseFixedCuspBranch_value_eq_rawValue I F Q Q0 hI hQ K levelBound
    G.levelScale G.levelScale_pos hbound e G.shape.index u (G.staticPhase v u)
    (G.staticPhase_norm_le_one v u) rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end CubicEisenstein.FixedFourierGeometry

open scoped BigOperators Classical

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

def supportActivePoolEquiv (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6) :
    reflectionSixSupport e ≃ reflectionActivePool I Q Q0 e where
  toFun b:=⟨b.val.val,(mem_reflectionActivePool I Q Q0 e b.val).mpr
    (Finset.mem_filter.mp b.property).2⟩
  invFun P:=⟨⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_reflectionActivePool I Q Q0 e _).mp P.property⟩⟩
  left_inv _b:=rfl
  right_inv _P:=rfl

lemma supportActivePoolEquiv_val (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (b:reflectionSixSupport e) :
    (supportActivePoolEquiv I Q Q0 e b).val=b.val.val := rfl

lemma supportActivePoolEquiv_symm_val (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (P:reflectionActivePool I Q Q0 e) :
    ((supportActivePoolEquiv I Q Q0 e).symm P).val.val=P.val := rfl

lemma supportActivePoolEquiv_label (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (b:reflectionSixSupport e) :
    reflectionActiveLabel I Q Q0 e (supportActivePoolEquiv I Q Q0 e b)=
      reflectionSixLabel (e b.val) := rfl

def encodedActivePoolEquiv (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3) :
    B ≃ reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,l⟩) where
  toFun b:=⟨b.val.val,by
    rw [reflectionActivePool_encode]
    exact Finset.mem_image.mpr ⟨b.val,b.property,rfl⟩⟩
  invFun P:=⟨⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩,by
    have hp:P.val∈B.image Subtype.val:=by
      simpa only [reflectionActivePool_encode] using P.property
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hp
    have he':b=⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩:=Subtype.ext he
    exact he' ▸ hb⟩
  left_inv b:=rfl
  right_inv P:=rfl

lemma encodedActivePoolEquiv_val (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3)
    (b:B) : (encodedActivePoolEquiv I Q Q0 B l b).val=b.val.val := rfl

lemma encodedActivePoolEquiv_label (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3)
    (b:B) :
    reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,l⟩) (encodedActivePoolEquiv I Q Q0 B l b)=l b := by
  change reflectionSixLabel (encodeReflectionSix ⟨B,l⟩ b.val)=l b
  apply Fin.ext
  simp only [encodeReflectionSix,dite_eq_left b.property,reflectionSixLabel]
  change (3+(l b).val)%3=(l b).val
  have hlt:=(l b).isLt
  omega

lemma encodedActivePoolEquiv_divisor (I F Q Q0:Ideal Eis)
    (B:Finset (pool I Q Q0)) (l:B → Fin 3) (side:Fin 3) :
    reflectionExtractedDivisor
      (fun P:reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,l⟩)=>P.val)
      (fun P=>completedLocalExponent I F P.val)
      (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,l⟩)) side=
    reflectionExtractedDivisor (fun b:B=>b.val.val)
      (fun b=>completedLocalExponent I F b.val.val) l side := by
  unfold reflectionExtractedDivisor
  symm
  apply Fintype.prod_equiv (encodedActivePoolEquiv I Q Q0 B l)
  intro b
  rw [encodedActivePoolEquiv_label]
  rfl

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F)

noncomputable def activeModelPrimeEquiv :
    PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e ≃
        activeSet q hq m hm rows R F hR hF hrows v e J :=
  (Equiv.sumCongr (Equiv.refl _)
    (FreeReflection.supportActivePoolEquiv R (maskIdeal q m F) (freeConductor q) e).symm).trans
    (selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e))

lemma splitIndex_prime_val
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕ FreeReflection.pool R (maskIdeal q m F) (freeConductor q)) :
    (splitIndex q hq m hm rows R F hR hF hrows v J P).val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

lemma splitIndex_local_exponent
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕ FreeReflection.pool R (maskIdeal q m F) (freeConductor q)) :
    (UniqueFactorizationMonoid.normalizedFactors (data q m hm rows R F hF hrows v J).movingIdeal).count
      (splitIndex q hq m hm rows R F hR hF hrows v J P).val.val%6=
      Sum.elim (fun _=>1) (fun b=>completedLocalExponent R F b.val) P := by
  unfold splitIndex
  apply GoodMaskRowData.primeFiberEquiv_exponent

lemma activeModelPrimeEquiv_prime_val
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val.val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

lemma activeModelPrimeEquiv_span
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    Ideal.span {(freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)
      (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val)}=
      Sum.elim Subtype.val Subtype.val P := by
  rw [freePrimaryPrime_span _ _ (data q m hm rows R F hF hrows v J).movingSupported]
  exact activeModelPrimeEquiv_prime_val q hq m hm rows R F hR hF hrows v e J P

lemma activeModelPrimeEquiv_exponent
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    (UniqueFactorizationMonoid.normalizedFactors (data q m hm rows R F hF hrows v J).movingIdeal).count
      (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val.val.val%6=
      Sum.elim (fun _=>1) (fun b=>completedLocalExponent R F b.val) P := by
  cases P with
  | inl P=>exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inl P)
  | inr P=>
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J
      (Sum.inr ⟨P.val,FreeReflection.reflectionActivePool_subset R (maskIdeal q m F) (freeConductor q) e P.property⟩)

end CanonicalRowCompletion.ActualFiber

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance inactiveField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance inactiveFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

lemma finiteAdditiveFourierCoeff_zero {R:Type*} [Field R] [Fintype R]
    (ψ:AddChar R ℂ) (χ:MulChar R ℂ) (j:ℕ) :
    finiteAdditiveFourierCoeff ψ (fun x=>(χ^j) x) 0=zeroFourierCoefficient χ j := by
  simp only [finiteAdditiveFourierCoeff,zeroFourierCoefficient,neg_zero,zero_mul,
    AddChar.map_zero_eq_one,mul_one,div_eq_mul_inv]
  ring

lemma prime_zeroFourier_norm_formula (p:Eis) [(Ideal.span {p}).IsMaximal]
    (hp:p≠0) (hg:lambda∉Ideal.span {p}) (hodd:ringChar (Eis⧸Ideal.span {p})≠2)
    (j:ℕ) (hj:j<6) :
    finiteAdditiveFourierCoeff (quotientTrace p hp)
      (fun x=>(actualSextic (Ideal.span {p}) hg^j) x) 0=
      if j=0 then 1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ else 0 := by
  rw [finiteAdditiveFourierCoeff_zero]
  have he:=canonical_zeroFourierCoefficient (Ideal.span {p}) hg hodd j hj
  convert he using 1
  exact congrArg (fun n:ℕ=>(if j=0 then 1-(n:ℂ)⁻¹ else 0)) (by rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card])

end CubicEisenstein

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance inactivePoolMaximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal:=
  pool_maximal I Q Q0 P
noncomputable local instance inactivePoolField (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Field (Eis⧸P.val):=
  Ideal.Quotient.field P.val
noncomputable local instance inactivePoolFintype (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Fintype (Eis⧸P.val):=
  Fintype.ofFinite _

lemma reflectionInactiveStratumWeight_formula (I F Q Q0:Ideal Eis) (A:Finset (pool I Q Q0)) :
    reflectionInactiveStratumWeight I F Q Q0 A=
      ∏P∈(Finset.univ:Finset (pool I Q Q0))\A,
        if completedLocalExponent I F P.val=0 then 1-(Ideal.absNorm P.val:ℂ)⁻¹ else 0 := by
  unfold reflectionInactiveStratumWeight
  apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro P hP
  have he:=canonical_zeroFourierCoefficient P.val (pool_good I Q Q0 P) (pool_odd I Q Q0 P)
    (completedLocalExponent I F P.val) (Nat.mod_lt _ (by decide))
  convert he using 1
  exact congrArg (fun n:ℕ=>(if completedLocalExponent I F P.val=0 then 1-(n:ℂ)⁻¹ else 0))
    (by rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card])

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
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

theorem inactive_source_reindex (w:Finset (FreePrimeIndex D.movingIdeal Q0)→ℂ) :
    letI : ∀P:FreePrimeIndex D.movingIdeal Q0,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P}:Ideal Eis).IsMaximal:=
        freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported
    let E:=D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT
    (∑A:Finset (FreePrimeIndex D.movingIdeal Q0),
      primeInactiveFourierWeight (freePrimaryPrime D.movingIdeal Q0)
        (freePrimaryPrime_ne_zero D.movingIdeal Q0 D.movingSupported)
        (freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) A*w A)=
      ∑B:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0),
        FreeReflection.reflectionInactiveStratumWeight R F (Ideal.span {m}*F) Q0 B*
          w (residualActivePrimes E∪B.image (fun P=>E (Sum.inr P))) := by
  let : ∀P:FreePrimeIndex D.movingIdeal Q0,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P}:Ideal Eis).IsMaximal:=
        freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported
  dsimp only
  let E:=D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT
  let Z:FreePrimeIndex D.movingIdeal Q0→ℂ:=fun P=>
    if (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6=0 then
      1-(Ideal.absNorm P.val.val:ℂ)⁻¹ else 0
  have hzero (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) : Z (E (Sum.inl P))=0:=by
    dsimp only [Z]
    rw [D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inl P)]
    norm_num
  have hnonres (P:FreeReflection.pool R (Ideal.span {m}*F) Q0) :
      Z (E (Sum.inr P))=
        if completedLocalExponent R F P.val=0 then 1-(Ideal.absNorm P.val:ℂ)⁻¹ else 0:=by
    dsimp only [Z]
    rw [D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P),
      D.primeFiberEquiv_val R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P)]
    rfl
  have hw (A:Finset (FreePrimeIndex D.movingIdeal Q0)) :
      primeInactiveFourierWeight (freePrimaryPrime D.movingIdeal Q0)
        (freePrimaryPrime_ne_zero D.movingIdeal Q0 D.movingSupported)
        (freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) A=
      ∏P∈(Finset.univ:Finset (FreePrimeIndex D.movingIdeal Q0))\A,Z P:=by
    unfold primeInactiveFourierWeight
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    rw [prime_zeroFourier_norm_formula _ _ _ (freePrimaryPrime_odd D.movingIdeal Q0 D.movingSupported P)
      _ (Nat.mod_lt _ (by decide)),freePrimaryPrime_span D.movingIdeal Q0 D.movingSupported P]
  simp only [hw]
  have he:=inactive_weight_nonresidual_subsets E Z hzero w
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
    intro A hA
    congr 1
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    rfl
  apply Finset.sum_congr (by ext B; simp only [Finset.mem_univ])
  intro B hB
  congr 1
  · rw [FreeReflection.reflectionInactiveStratumWeight_formula]
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    exact hnonres P
  · apply congrArg w
    ext P
    simp only [E,residualActivePrimes,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]

end GoodMaskRowData
end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance rayUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

theorem sum_fixedReflectionRay {M:Type*} [AddCommMonoid M]
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    [∀h:Eis⧸Ideal.span {c},Fintype (fixedFourierGeometry c hc h).PhaseResidue]
    (F:FixedReflectionRay c hc → M) :
    (∑r:FixedReflectionRay c hc,F r)=
      ∑h:Eis⧸Ideal.span {c},∑rho:(fixedFourierGeometry c hc h).PhaseResidue,
        ∑u:Eisˣ,F ⟨h,rho,u⟩ := by
  let e : FixedReflectionRay c hc ≃
      (Σ h : Eis⧸Ideal.span {c}, (fixedFourierGeometry c hc h).PhaseResidue × Eisˣ) :=
    Equiv.refl _
  calc
    _ = ∑ r : (Σ h : Eis⧸Ideal.span {c},
        (fixedFourierGeometry c hc h).PhaseResidue × Eisˣ), F (e.symm r) :=
      Fintype.sum_equiv e _ _ (fun r => congrArg F (e.symm_apply_apply r).symm)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro h hh
      exact Fintype.sum_prod_type _

theorem sum_fixedReflectionRayFin {M:Type*} [AddCommMonoid M]
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    [∀h:Eis⧸Ideal.span {c},Fintype (fixedFourierGeometry c hc h).PhaseResidue]
    (F:Fin (fixedReflectionRayCount c hc) → M) :
    (∑i:Fin (fixedReflectionRayCount c hc),F i)=
      ∑h:Eis⧸Ideal.span {c},∑rho:(fixedFourierGeometry c hc h).PhaseResidue,
        ∑u:Eisˣ,F (fixedReflectionRayEquiv c hc ⟨h,rho,u⟩) := by
  calc
    _=∑r:FixedReflectionRay c hc,F (fixedReflectionRayEquiv c hc r):=
      (Fintype.sum_equiv (fixedReflectionRayEquiv c hc) _ _ (fun _=>rfl)).symm
    _=_:=sum_fixedReflectionRay c hc _

end CubicEisenstein

end

end OAI

end

