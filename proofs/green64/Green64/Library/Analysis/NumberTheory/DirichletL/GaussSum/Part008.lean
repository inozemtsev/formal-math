module

public import Green64.Library.Analysis.NumberTheory.DirichletL.ChineseRemainder.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / GaussSum / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.GaussSum.ReflectionPool -/

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
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximalCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q P
noncomputable local instance poolFieldCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintypeCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

lemma reflectionSixInactiveWeight_support (I F Q:Ideal Eis)
    (e:completedReflectionPool I Q→Fin 6) (hne:reflectionSixInactiveWeight I F Q e≠0)
    (P:completedReflectionPool I Q) (hj:completedLocalExponent I F P.val≠0) :
    reflectionSixActive (e P) := by
  have he:reflectionSixValid e:=by
    by_contra he
    exact hne (by simp [reflectionSixInactiveWeight,he])
  have hprod:reflectionInactiveStratumWeight I F Q (reflectionSixSupport e)≠0:=by
    simpa only [reflectionSixInactiveWeight,ite_eq_left he] using hne
  by_contra hP
  have hm:P∈(Finset.univ:Finset (completedReflectionPool I Q))\reflectionSixSupport e:=by
    simp [reflectionSixSupport,hP]
  have hp:zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
      (completedLocalExponent I F P.val)≠0:=
    (Finset.prod_ne_zero_iff.mp hprod) P hm
  have hz:=canonical_zeroFourierCoefficient P.val (completedReflectionPool_good I Q P)
    (completedReflectionPool_odd I Q P) (completedLocalExponent I F P.val)
    (Nat.mod_lt _ (by decide : 0<6))
  apply hp
  simpa only [actualSextic,ite_eq_right hj] using hz

lemma sixReflectionIndex_card (rays:ℕ) (I Q:Ideal Eis) :
    Fintype.card (SixReflectionIndex rays I Q)=rays*6^(completedReflectionPool I Q).card := by
  simp [SixReflectionIndex]

theorem completedReflectionPool_count_small_power (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀I Q:Ideal Eis,I≠0→Q≠0→
      (6:ℝ)^(2*(completedReflectionPool I Q).card)≤
        C*((Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ))^ε := by
  obtain ⟨C,hC,hbound⟩:=completed_branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro I Q hI hQ
  have h:=hbound (I*Q) (mul_ne_zero hI hQ)
    (fun P:completedReflectionPool I Q=>P.val) Subtype.val_injective
    (completedReflectionPool_divides I Q hI hQ)
  simpa only [Fintype.card_coe,map_mul,Nat.cast_mul] using h

end CompletedGauss

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma actualSextic_sixth_one (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    actualSextic P hg^6=1 := by
  apply MulChar.ext
  intro t
  obtain ⟨n,hn⟩:=Ideal.Quotient.mk_surjective (t:Eis⧸P)
  have hnot:n∉P:=by
    intro hm
    have ht:(t:Eis⧸P)=0:=by rw [←hn];exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
    exact t.ne_zero ht
  have h:=canonicalSextic_sixth_power_mask P hg n
  change actualSextic P hg (Ideal.Quotient.mk P (n^6))=_ at h
  rw [map_pow,map_pow,ite_eq_right hnot] at h
  rw [MulChar.pow_apply_coe,MulChar.one_apply_coe,←hn]
  exact h

lemma actualSextic_power_mod_six (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P)
    (k:ℕ) (hk:k≠0) (n:Eis) :
    actualSextic P hg (Ideal.Quotient.mk P n)^k=
      (actualSextic P hg^(k%6)) (Ideal.Quotient.mk P n) := by
  rw [←MulChar.pow_apply' _ hk,pow_eq_pow_mod _ (actualSextic_sixth_one P hg)]

lemma idealRowHom_eq_prime_count_product (I:Ideal Eis) (hI:Supported I) (n:Eis) :
    idealRowHom n I=∏P:PrimeIndex I,
      (actualSextic P.val ((supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1) ^
        ((normalizedFactors I).count P.val%6)) (Ideal.Quotient.mk P.val n) := by
  have he:I=∏P:PrimeIndex I,P.val^((normalizedFactors I).count P.val):=by
    change I=∏P:(normalizedFactors I).toFinset,P.val^((normalizedFactors I).count P.val)
    exact ((Ideal.prod_normalizedFactors_eq_self hI.1).symm.trans (Finset.prod_multiset_count _)).trans
      (Finset.prod_coe_sort (normalizedFactors I).toFinset (fun P=>P^((normalizedFactors I).count P))).symm
  calc
    idealRowHom n I = idealRowHom n (∏P:PrimeIndex I,P.val^((normalizedFactors I).count P.val)) :=
      congrArg (idealRowHom n) he
    _ = ∏P:PrimeIndex I,idealRowHom n P.val ^ ((normalizedFactors I).count P.val) := by
      simp only [map_prod,map_pow]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [idealRowHom_prime n P.val
        ((supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)]
      exact actualSextic_power_mod_six P.val _ _
        (Nat.ne_of_gt (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property))) n

lemma primeIndex_pairwise_coprime (I:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:PrimeIndex I=>P.val)) := by
  intro P Q hPQ
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))

theorem idealRowHom_eq_principalSexticRow (I:Ideal Eis) (hI:Supported I) (n:Eis) :
    idealRowHom n I=
      principalSexticRow (fun P:PrimeIndex I=>P.val) (primeIndex_pairwise_coprime I)
        (fun P=>(supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>(normalizedFactors I).count P.val%6)
        (finitePrimeModulus (fun P:PrimeIndex I=>P.val))
        (span_finitePrimeModulus _)
        (Ideal.Quotient.mk _ n) := by
  rw [principalSexticRow_mk]
  exact idealRowHom_eq_prime_count_product I hI n

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma coprimalityMask_good_part (u:Eisˣ) (a b:ℕ) (r n:Eis)
    (hn:Supported (Ideal.span {n})) :
    coprimalityMask (u.val*lambda^a*(2:Eis)^b*r) n=coprimalityMask r n := by
  have hl:IsCoprime lambda n:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr ((supported_span_iff n).mp hn).1
  have hneg2:IsCoprime (-2:Eis) n:=negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have h2:IsCoprime (2:Eis) n:=hneg2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have hu:IsCoprime u.val n:=⟨(u⁻¹).val,0,by simp⟩
  have hla:IsCoprime (lambda^a) n:=hl.pow_left
  have h2b:IsCoprime ((2:Eis)^b) n:=h2.pow_left
  change (if IsCoprime (u.val*lambda^a*(2:Eis)^b*r) n then (1:ℂ) else 0)=_
  rw [IsCoprime.mul_left_iff,IsCoprime.mul_left_iff,IsCoprime.mul_left_iff]
  simp only [hu,hla,h2b,true_and]
  rfl

lemma idealRowHom_sixth_denominator_mask (r n:Eis) (hr:Supported (Ideal.span {r})) :
    idealRowHom n ((Ideal.span {r})^6)=coprimalityMask r n := by
  rw [map_pow,←idealRowHom_argument_pow n 6 _ hr,idealRowHom_sixth_eq_mask n r hr]
  change (if IsCoprime n r then (1:ℂ) else 0)=(if IsCoprime r n then 1 else 0)
  rw [isCoprime_comm]

lemma mask_times_good_row (m:Eis) (um:Eisˣ) (am bm:ℕ) (g r n:Eis)
    (hg:Supported (Ideal.span {g})) (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (hn:Supported (Ideal.span {n})) :
    coprimalityMask m n*idealRowHom n (Ideal.span {r})=
      idealRowHom n ((Ideal.span {g})^6*Ideal.span {r}) := by
  rw [hm,coprimalityMask_good_part um am bm g n hn,map_mul,
    idealRowHom_sixth_denominator_mask g n hg]

theorem rowTwist_eq_fixed_times_good_row_primary
    (Ψ:Eis→*ℂ) (m f z:Eis) (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hpr:lambda^2∣r-1) (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n *
      idealRowHom n ((Ideal.span {g})^6*Ideal.span {r}) := by
  rw [rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx n hpn]
  by_cases hn:Supported (Ideal.span {n})
  · change ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*idealRowHom n (Ideal.span {r})=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [show ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*idealRowHom n (Ideal.span {r})=
      (Ψ n*numeratorBadTwist u a b r hr n)*(coprimalityMask m n*idealRowHom n (Ideal.span {r})) by ring,
      mask_times_good_row m um am bm g r n hg hm hn]
  · change ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*_=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn]
    simp only [mul_zero,zero_mul]

lemma fixedNumeratorTwist_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)})
      (Ψ*numeratorBadTwist u a b r hr) := by
  intro x y hxy
  change Ψ x*numeratorBadTwist u a b r hr x=Ψ y*numeratorBadTwist u a b r hr y
  rw [hΨ x y (Ideal.mul_le_left hxy),numeratorBadTwist_periodic u a b r hr x y (Ideal.mul_le_right hxy)]

theorem exists_fixed_twist_principal_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=φ n *
        principalSexticRow (fun P:PrimeIndex I=>P.val) (primeIndex_pairwise_coprime I)
          (fun P=>(supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val%6)
          (finitePrimeModulus (fun P:PrimeIndex I=>P.val)) (span_finitePrimeModulus _)
          (Ideal.Quotient.mk _ n)) := by
  obtain ⟨um,am,bm,g,hg,hpg,hmf⟩:=exists_supported_numerator_factorization m hm
  obtain ⟨u,a,b,r,hr,hpr,hxf⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  let I:Ideal Eis:=(Ideal.span {g})^6*Ideal.span {r}
  have hI:Supported I:=by
    change Supported ((Ideal.span {g})^6*Ideal.span {r})
    rw [supported_mul_iff]
    exact ⟨supported_pow hg 6,hr⟩
  refine ⟨I,hI,Ψ*numeratorBadTwist u a b r hr,
    fixedNumeratorTwist_periodic Ψ Q hΨ u a b r hr,?_,?_⟩
  · intro n
    change ‖Ψ n*numeratorBadTwist u a b r hr n‖≤1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hΨnorm n)).trans (numeratorBadTwist_norm u a b r hr n)
  · intro n hpn
    rw [←idealRowHom_eq_principalSexticRow I hI n]
    exact rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2 um am bm g hg hmf
      u a b r hr hpr hxf n hpn

theorem rowTwist_completedT_eq_periodic (Ψ:Eis→*ℂ) (m f z:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) (W:ℝ→ℂ) (X:ℝ) :
    completedT (rowTwist Ψ m f z) W X=completedT (actualPeriodicRow Ψ m u a b r hr) W X :=
  completedT_congr_primary _ _
    (rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx) W X

end CanonicalRowCompletion

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4unitsField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

theorem exists_A4_local_units {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (c0 U w:Eis) (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1) :
    ∃σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,(σ i:Eis⧸Ideal.span {p i})=
        Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)) ∧
      ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1 := by
  have hone (i:ι) : ∃σ ε:(Eis⧸Ideal.span {p i})ˣ,
      (σ:Eis⧸Ideal.span {p i})=Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i) ∧
      Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ:Eis⧸Ideal.span {p i})*(ε:Eis⧸Ideal.span {p i})=-1 := by
    let q:=Ideal.Quotient.mk (Ideal.span {p i})
    have hz:q (∏k,p k)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
    have hb:q (ramifiedTraceLambda^3*c0)*q w=1 := by
      have he:=congrArg q hbez
      simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at he
      simpa only [map_mul,map_pow,mul_assoc,mul_comm,mul_left_comm] using he
    have hb0:q (ramifiedTraceLambda^3*c0)≠0 := by
      intro he
      rw [he,zero_mul] at hb
      exact zero_ne_one hb
    have hc0:q (cofactor p i)≠0 := by
      intro he
      have hi:=productTraceShift_inverse p hp hcop i
      change q (cofactor p i)*_=1 at hi
      rw [he,zero_mul] at hi
      exact zero_ne_one hi
    have hB:q (ramifiedTraceLambda^3*c0*cofactor p i)≠0 := by
      rw [map_mul]
      exact mul_ne_zero hb0 hc0
    have hS:q (ramifiedTraceLambda^2*c0*cofactor p i)≠0 := by
      intro he
      apply hB
      calc
        _=q ramifiedTraceLambda*q (ramifiedTraceLambda^2*c0*cofactor p i) := by
          simp only [map_mul,map_pow]
          ring
        _=0:=by rw [he,mul_zero]
    let σ:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hS
    let B:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hB
    refine ⟨σ,-(B*σ)⁻¹,rfl,?_⟩
    have hcancel:=congrArg (fun u:(Eis⧸Ideal.span {p i})ˣ=>(u:Eis⧸Ideal.span {p i}))
      (mul_inv_cancel (B*σ))
    simpa only [B,Units.val_mk0,Units.val_mul,Units.val_one,Units.val_neg,mul_neg] using congrArg Neg.neg hcancel
  choose σ ε hσ hε using hone
  exact ⟨σ,ε,hσ,hε⟩

end ShortDraftCusp

section
open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss CubicKubota CubicJacobiGlobal LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance principalStratumField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance principalStratumFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem principal_stratum_multiplier {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w x:Eis) (hc0:c0≠0) (hr:lambda^2∣(∏i,p i)-1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (g:(∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree)
    (hC:∀v,(g v:SL(2,Eis)) 1 0=c0*∏i,p i)
    (hA:∀v,(9:Eis)*c0∣(g v:SL(2,Eis)) 0 0-(g (fun _=>1):SL(2,Eis)) 0 0)
    (hD:∀v,ramifiedTraceLambda^3*c0∣(g v:SL(2,Eis)) 1 1-(g (fun _=>1):SL(2,Eis)) 1 1)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) ((g v:SL(2,Eis)) 0 0)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6) :
    (∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
      star (complexCharacter (g v))*
      ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))) =
    (star (eisEmbedding (symbol c0 ((g (fun _=>1):SL(2,Eis)) 0 0)))*
      A4BadPhase c0 hc0 ((g (fun _=>1):SL(2,Eis)) 1 1) U x)*
    ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  let a0:=(g (fun _=>1):SL(2,Eis)) 0 0
  let d0:=(g (fun _=>1):SL(2,Eis)) 1 1
  let C:=star (eisEmbedding (symbol c0 a0))*A4BadPhase c0 hc0 d0 U x
  let f:=fun i (v:(Eis⧸Ideal.span {p i})ˣ)=>frequencyRow
    (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i)
    (σ i) (ε i) (Ideal.Quotient.mk _ x) v
  have hpoint (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
      star (complexCharacter (g v))*
      ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))=
      C*∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (v i) := by
    have hbad:A4BadPhase c0 hc0 ((g v:SL(2,Eis)) 1 1) U x=A4BadPhase c0 hc0 d0 U x := by
      apply A4BadPhase_eq_of_residue
      convert dvd_mul_of_dvd_left (hD v) U using 1 ; ring
    have hfixed:symbol c0 ((g v:SL(2,Eis)) 0 0)=symbol c0 a0 :=
      A3_fixed_factor_congr 9 c0 _ _ (dvd_refl _) (levelThree_primary (g v))
        (levelThree_primary (g (fun _=>1))) (hA v)
    have hdet:(g v:SL(2,Eis)) 0 0*(g v:SL(2,Eis)) 1 1-
        (g v:SL(2,Eis)) 0 1*(c0*∏i,p i)=1 := by
      rw [←hC v]
      simpa only [Matrix.det_fin_two] using (g v:SL(2,Eis)).property
    have hlocal:=A3_A4_frequency_product p hp hcop hg
      ((g v:SL(2,Eis)) 0 0) ((g v:SL(2,Eis)) 0 1) c0 ((g v:SL(2,Eis)) 1 1)
      U w x hc0 hdet hbez σ ε (fun i=>(v i:Eis⧸Ideal.span {p i})) (hfreq v) hε
    rw [A3_principal_character (g v) (g v).property c0 (∏i,p i) (hC v) hr,hfixed,star_mul]
    calc
      _=star (eisEmbedding (symbol c0 a0))*
          (star (eisEmbedding (symbol ((g v:SL(2,Eis)) 0 0) (∏i,p i)))*
            ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
              (eisEmbedding c0*eisEmbedding (∏i,p i)))) := by ring
      _=_ := by rw [hlocal,hbad];dsimp only [C];ring
  calc
    _=C*∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,∏i,f i (v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mul_assoc, hpoint]
      simp only [f,frequencyRow,Finset.prod_mul_distrib]
      ring
    _=C*∏i,∑v:(Eis⧸Ideal.span {p i})ˣ,f i v := by rw [Fintype.prod_sum]
    _=_ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact canonical_frequencyRow_units (Ideal.span {p i}) (hg i) (hchar i)
        (quotientTrace (p i) (hp i))
        (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) (j i) (hj i) (σ i) (ε i) _

end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspRepresentative_zero_eq_one : cuspRepresentative 0=(1:SL(2,Eis)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspRepresentative,cuspParameter,lowerCuspMatrix]

def principalCuspDatum (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) : SourceCuspDatum where
  gamma:=sourceLevelInclusion g
  index:=0
  lower_ne_zero:=by
    change (integralComplexMatrix (g:SL(2,Eis))*integralComplexMatrix (cuspRepresentative 0)) 1 0≠0
    rw [cuspRepresentative_zero_eq_one,map_one,mul_one,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hc

lemma principalCuspDatum_matrix (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).matrix=integralComplexMatrix (g:SL(2,Eis)) := by
  change integralComplexMatrix (g:SL(2,Eis))*integralComplexMatrix (cuspRepresentative 0)=_
  rw [cuspRepresentative_zero_eq_one,map_one,mul_one]

lemma principalCuspDatum_height (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).heightScale=‖eisEmbedding ((g:SL(2,Eis)) 1 0)‖^2 := by
  rw [SourceCuspDatum.heightScale,principalCuspDatum_matrix,integralComplexMatrix_apply]

lemma principalCuspDatum_dual (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).dualPoint=
      -eisEmbedding ((g:SL(2,Eis)) 1 1)/eisEmbedding ((g:SL(2,Eis)) 1 0) := by
  rw [SourceCuspDatum.dualPoint,principalCuspDatum_matrix]
  rfl

lemma principalCuspDatum_multiplier (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).multiplier=
      -star (complexCharacter g)/(eisEmbedding ((g:SL(2,Eis)) 1 0))^2 := by
  rw [SourceCuspDatum.multiplier,principalCuspDatum_matrix,integralComplexMatrix_apply]
  change -star (levelTwoComplexCharacter (sourceLevelInclusion g))/_=_
  rw [sourceLevelInclusion_character]

lemma infinity_phaseNumerator_embedding (h:Eis) :
    eisEmbedding (ramifiedTraceLambda*h)=-eisLam^4*cuspFrequency h := by
  rw [map_mul,ramifiedEmbedding_traceLambda,cuspFrequency]
  field_simp [eisLam_ne_zero]
  linear_combination eisEmbedding h*TraceLambdaPhase.eisLam_sq

lemma principalCuspDatum_phase (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) (h:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency h*(principalCuspDatum g hc).dualPoint)=
      ShortDraftTrace.breveE (-(eisEmbedding ((g:SL(2,Eis)) 1 1)*
        (eisEmbedding (ramifiedTraceLambda*h)/eisLam^4))/eisEmbedding ((g:SL(2,Eis)) 1 0)) := by
  rw [principalCuspDatum_dual,infinity_phaseNumerator_embedding]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc]

end CubicEisenstein
end

namespace CubicEisenstein
open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance smoothingField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance smoothingFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem principal_stratum_smoothed {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w:Eis) (hc0:c0≠0) (hr:lambda^2∣(∏i,p i)-1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (g:(∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree)
    (hC:∀v,(g v:SL(2,Eis)) 1 0=c0*∏i,p i)
    (hA:∀v,(9:Eis)*c0∣(g v:SL(2,Eis)) 0 0-(g (fun _=>1):SL(2,Eis)) 0 0)
    (hD:∀v,ramifiedTraceLambda^3*c0∣(g v:SL(2,Eis)) 1 1-(g (fun _=>1):SL(2,Eis)) 1 1)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) ((g v:SL(2,Eis)) 0 0)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    let c:=c0*∏i,p i
    let Q:ℝ:=‖eisEmbedding c‖^2
    let hc:∀v,(g v:SL(2,Eis)) 1 0≠0:=fun v=>by
      rw [hC v];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
    let weight:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>
      ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)
    (∑v,weight v*(principalCuspDatum (g v) (hc v)).smoothedKernel W X)=
    fixedRadialCoefficientScalar*∑'t:ThetaFullIndex,
      ((fixedConjugateCuspArray 0 t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
        sourceFrequencyAngle (thetaFullFrequency t))/
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency t)/(27*Q^2))*
      (-(Q:ℂ)/(eisEmbedding c)^2*
        ((star (eisEmbedding (symbol c0 ((g (fun _=>1):SL(2,Eis)) 0 0)))*
          A4BadPhase c0 hc0 ((g (fun _=>1):SL(2,Eis)) 1 1) U (ramifiedTraceLambda*thetaFullFrequency t))*
        ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
          phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
          bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
            (Ideal.Quotient.mk _ (ramifiedTraceLambda*thetaFullFrequency t)))) := by
  dsimp only
  let c:=c0*∏i,p i
  let Q:ℝ:=‖eisEmbedding c‖^2
  have hc:∀v,(g v:SL(2,Eis)) 1 0≠0:=fun v=>by
    rw [hC v];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  let d:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>principalCuspDatum (g v) (hc v)
  let weight:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>
    ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)
  have hheight:∀v,(d v).heightScale=Q:=by
    intro v
    rw [principalCuspDatum_height,hC v]
  have hcol:=sum_smoothedKernel_common_cusp d weight 0 Q (fun _=>rfl) hheight
    W lo hi hlo hsupp hW X hX
  change (∑v,weight v*(d v).smoothedKernel W X)=_
  rw [hcol]
  congr 1
  apply tsum_congr
  intro t
  simp only [sourceCuspScale,Matrix.cons_val_zero,Complex.ofReal_one,div_one,one_pow,mul_one]
  congr 1
  let x:=ramifiedTraceLambda*thetaFullFrequency t
  have hlocal:=principal_stratum_multiplier p hp hcop hg hchar c0 U w x hc0 hr hbez
    g hC hA hD σ ε hfreq hε j hj
  calc
    _=(-(Q:ℂ)/(eisEmbedding c)^2)*
        ∑v,weight v*star (complexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
            (eisEmbedding c0*eisEmbedding (∏i,p i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      change weight v*((principalCuspDatum (g v) (hc v)).multiplier*(Q:ℂ))*
        ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency t)*(principalCuspDatum (g v) (hc v)).dualPoint)=_
      rw [principalCuspDatum_multiplier,principalCuspDatum_phase,hC v,map_mul]
      dsimp only [c,x]
      rw [map_mul]
      ring
    _=_:=by rw [hlocal]

end CubicEisenstein

open scoped Classical BigOperators MatrixGroups

namespace ShortDraftCRT
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT PrimaryIdealUnitReindex
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_multiple (x:Eis) (hx:¬lambda∣x) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:primaryGenerator (Ideal.span {x})≠0:=primaryGenerator_span_ne_zero_iff x |>.mpr hx
  have hspec:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  rw [mul_comm,hu]
  exact hspec.2

lemma normalize_coprime_pair (a c:Eis) (hcop:IsCoprime a c) :
    ∃u:Eisˣ,IsCoprime (u.val*a) (u.val*c) ∧
      (lambda∣u.val*c→lambda^2∣u.val*a-1) ∧
      (¬lambda∣u.val*c→lambda^2∣u.val*c-1) := by
  have hunit (u:Eisˣ):IsCoprime (u.val*a) (u.val*c) := by
    obtain ⟨r,s,hrs⟩:=hcop
    refine ⟨r*(↑u⁻¹:Eis),s*(↑u⁻¹:Eis),?_⟩
    calc
      _=((↑u⁻¹:Eis)*u.val)*(r*a+s*c):=by ring
      _=1:=by rw [Units.inv_mul,hrs,mul_one]
  have hd (u:Eisˣ):lambda∣u.val*c↔lambda∣c := by
    constructor
    · intro h
      have hh:=dvd_mul_of_dvd_right h (↑u⁻¹:Eis)
      simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh
    · intro h
      exact dvd_mul_of_dvd_right h u.val
  by_cases hc:lambda∣c
  · have ha:¬lambda∣a:=fun h=>lambda_prime_actual.not_isUnit (hcop.isUnit_of_dvd' h hc)
    obtain ⟨u,hu⟩:=exists_primary_unit_multiple a ha
    exact ⟨u,hunit u,fun _=>hu,fun hn=>False.elim (hn ((hd u).mpr hc))⟩
  · obtain ⟨u,hu⟩:=exists_primary_unit_multiple c hc
    exact ⟨u,hunit u,fun h=>False.elim (hc ((hd u).mp h)),fun _=>hu⟩

theorem exists_normalized_rational_cusp (a c:Eis) (hc:c≠0) :
    ∃a0 c0:Eis,c0≠0 ∧ c0∣c ∧ IsCoprime a0 c0 ∧
      eisEmbedding a0/eisEmbedding c0=eisEmbedding a/eisEmbedding c ∧
      (lambda∣c0→lambda^2∣a0-1) ∧ (¬lambda∣c0→lambda^2∣c0-1) := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by intro hz; exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by intro hz; exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨r,s,hrs⟩:=IsBezout.gcd_eq_sum a c
  have hred:IsCoprime a' c':=by
    refine ⟨r,s,?_⟩
    apply mul_left_cancel₀ hd
    change d*(r*a'+s*c')=d*1
    calc
      _=r*a+s*c:=by rw [ha,hc'];ring
      _=d:=hrs
      _=_:=by ring
  obtain ⟨u,hu,hua,huc⟩:=normalize_coprime_pair a' c' hred
  refine ⟨u.val*a',u.val*c',mul_ne_zero u.ne_zero hcp,?_,hu,?_,hua,huc⟩
  · refine ⟨d*(↑u⁻¹:Eis),?_⟩
    rw [hc']
    calc
      d*c'=((u.val*(↑u⁻¹:Eis))*d)*c':=by rw [Units.mul_inv,one_mul]
      _=_:=by ring
  · rw [ha,hc',map_mul,map_mul,map_mul,map_mul]
    have he:=eisEmbedding_ne_zero hd
    have hf:=eisEmbedding_ne_zero hcp
    have hu0:=eisEmbedding_ne_zero u.ne_zero
    field_simp

end ShortDraftCRT

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.FixedConductor -/

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

open scoped Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

lemma divisor_principal_norm_le (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    (Ideal.absNorm (Ideal.span {c0}):ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ) := by
  have hp:0<Ideal.absNorm (Ideal.span {c}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hd:Ideal.absNorm (Ideal.span {c0})∣Ideal.absNorm (Ideal.span {c}) := by
    obtain ⟨d,hd⟩:=hdiv
    rw [hd,←Ideal.span_singleton_mul_span_singleton,map_mul]
    exact dvd_mul_right _ _
  exact_mod_cast Nat.le_of_dvd hp hd

def fixedCuspLevelBound (c:Eis) : ℝ :=
  243*(Ideal.absNorm (Ideal.span {c}):ℝ)^2

def fixedCuspLevelScale (j:Fin 3) (c0:Eis) : ℝ :=
  27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2

lemma fixedCuspLevelBound_ge_one (c:Eis) (hc:c≠0) : 1≤fixedCuspLevelBound c := by
  have hp:1≤Ideal.absNorm (Ideal.span {c}):=Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(1:ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ):=by exact_mod_cast hp
  unfold fixedCuspLevelBound
  nlinarith

lemma fixedCuspLevelScale_pos (j:Fin 3) (c0:Eis) (hc0:c0≠0) : 0<fixedCuspLevelScale j c0 := by
  have hp:0<Ideal.absNorm (Ideal.span {c0}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc0 (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(0:ℝ)<(Ideal.absNorm (Ideal.span {c0}):ℝ):=by exact_mod_cast hp
  have hs:=sourceCuspScale_pos j
  unfold fixedCuspLevelScale
  positivity

lemma fixedCuspLevelScale_le (j:Fin 3) (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    fixedCuspLevelScale j c0≤fixedCuspLevelBound c := by
  have hd:=divisor_principal_norm_le c0 c hc hdiv
  have hs:(sourceCuspScale j)^2≤9:=by fin_cases j <;> norm_num [sourceCuspScale]
  unfold fixedCuspLevelScale fixedCuspLevelBound
  calc
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2≤
      27*9*(Ideal.absNorm (Ideal.span {c}):ℝ)^2:=by gcongr
    _=_:=by ring

end

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_traceLambda_pow_four : ramifiedTraceLambda^4=(9:Eis) := by
  apply eisEmbedding_injective
  rw [map_pow,map_ofNat,ramifiedEmbedding_traceLambda]
  calc
    _=(eisLam^2)^2:=by ring
    _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num

structure PrincipalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) where
  lift : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ι→Eis
  lift_period : ∀v i,N^2∣lift v i
  lift_residue : ∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (lift v i)=(v i:Eis⧸Ideal.span {p i})
  U : Eis
  w : Eis
  bezout : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1
  sigma : ∀i,(Eis⧸Ideal.span {p i})ˣ
  epsilon : ∀i,(Eis⧸Ideal.span {p i})ˣ
  sigma_value : ∀i,(sigma i:Eis⧸Ideal.span {p i})=
    Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)
  epsilon_value : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
    (sigma i:Eis⧸Ideal.span {p i})*(epsilon i:Eis⧸Ideal.span {p i})=-1
  gamma : (∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree
  numerator : ∀v,(gamma v:SL(2,Eis)) 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,(gamma v:SL(2,Eis)) 1 0=c0*∏i,p i
  numerator_fixed : ∀v,(9:Eis)*c0∣(gamma v:SL(2,Eis)) 0 0-(gamma (fun _=>1):SL(2,Eis)) 0 0
  inverse_fixed : ∀v,ramifiedTraceLambda^3*c0∣(gamma v:SL(2,Eis)) 1 1-(gamma (fun _=>1):SL(2,Eis)) 1 1

theorem exists_principalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (N a0 c0:Eis) (hc0:c0≠0) (hc3:(3:Eis)∣c0)
    (hN:(9:Eis)*c0∣N) (ha0:lambda^2∣a0-1) (hac:IsCoprime a0 c0)
    (hNp:∀i,IsCoprime N (p i)) :
    Nonempty (PrincipalStratumArithmetic p N a0 c0) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  have hDN:ramifiedTraceLambda^3*c0∣N:=hD9.trans hN
  have hl9:ramifiedTraceLambda∣(9:Eis) := by
    rw [←A4_traceLambda_pow_four]
    exact dvd_pow_self _ (by decide)
  have hlN:ramifiedTraceLambda∣N:=hl9.trans h9N
  have hstdN:lambda^2∣N:=lambda_sq_dvd_three.trans
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N)
  let r:Eis:=∏i,p i
  have hr:lambda^2∣r-1:=primary_finset_product Finset.univ p (fun i _=>hprimary i)
  have hNr:IsCoprime N r:=IsCoprime.prod_right (fun i _=>hNp i)
  have hrNc:IsCoprime r (N*c0):=hNr.symm.mul_right
    (hNr.symm.of_isCoprime_of_dvd_right hcN)
  obtain ⟨U,w,huw⟩:=hNr.symm.of_isCoprime_of_dvd_right hDN
  have hbez:U*r+(ramifiedTraceLambda^3*w)*c0=1 := by
    linear_combination huw
  obtain ⟨σ,ε,hσ,hε⟩:=exists_A4_local_units p hp hcop c0 U w hbez
  have hlf (v:∀i,(Eis⧸Ideal.span {p i})ˣ):=
    exists_strong_unit_frequency_lifts N p hNp v
  choose lift hlift hres hlcop using hlf
  let a:=fun v=>finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  have hap:∀v,lambda^2∣a v-1 := by
    intro v
    have hfixed:N∣a v-a0*r:=finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (lift v)
      (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (hlift v i))
    have hbase:=primary_mul a0 r ha0 hr
    convert dvd_add (hstdN.trans hfixed) hbase using 1 ; ring
  have hpairs:Pairwise (Function.onFun IsCoprime p):=by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have hacop:∀v,IsCoprime (a v) (c0*r) := by
    intro v
    exact finiteCrossNumerator_coprime a0 c0 ramifiedTraceLambda p (lift v) hac hpairs
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hcN)
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hlN) (hlcop v)
  obtain ⟨b,d,C,hdet,hb,hd,hmat⟩:=exists_primary_numerator_sector_completions
    N c0 hc0 h9N (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
    hap (fun _=>hr) hacop (fun _=>hrNc)
    (fun v z _=>finiteCrossNumerator_fixed_sector N a0 c0 ramifiedTraceLambda p (lift v)
      p (lift z) hcN (hlift v) (hlift z) (by simp))
    (fun _ _ _=>by simp)
  let mat:=fun v=>controlledCompletionMatrix (a v) (b v) (c0*r) (d v) (hdet v)
  have hm:∀v,mat v∈levelThree:=by
    intro v
    apply A3_principal_mem_levelThree (mat v)
    · exact three_dvd_primary_sub_one (a v) (hap v)
    · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans (hb v)
    · exact dvd_mul_of_dvd_left hc3 r
    · exact hd v
  let gamma:=fun v=>(⟨mat v,hm v⟩:levelThree)
  have hentry (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i j:Fin 2):
      N∣(mat v) i j-(mat (fun _=>1)) i j := by
    have he:=congrArg (fun T:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})=>T i j)
      ((hmat v).trans (hmat (fun _=>1)).symm)
    change Ideal.Quotient.mk (Ideal.span {N}) ((mat v) i j)=
      Ideal.Quotient.mk (Ideal.span {N}) ((mat (fun _=>1)) i j) at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ⟨{
    lift := lift
    lift_period := hlift
    lift_residue := hres
    U := U
    w := w
    bezout := hbez
    sigma := σ
    epsilon := ε
    sigma_value := hσ
    epsilon_value := hε
    gamma := gamma
    numerator := fun _=>rfl
    denominator := fun _=>rfl
    numerator_fixed := fun v=>hN.trans (hentry v 0 0)
    inverse_fixed := fun v=>hDN.trans (hentry v 1 1)
  }⟩

lemma PrincipalStratumArithmetic.frequency_congruence {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} (D:PrincipalStratumArithmetic p N a0 c0)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) ((D.gamma v:SL(2,Eis)) 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

end

open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace PrincipalStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis}

noncomputable def datum (D:PrincipalStratumArithmetic p N a0 c0)
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  principalCuspDatum (D.gamma v) (by
    rw [D.denominator];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma datum_point (D:PrincipalStratumArithmetic p N a0 c0)
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [SourceCuspDatum.point,datum,principalCuspDatum_matrix,
    integralComplexMatrix_apply,integralComplexMatrix_apply,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    ShortDraftCRT.finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp

noncomputable def smoothedValue (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
    (D.datum hp hc0 v).smoothedKernel W X

noncomputable def reflectedValue (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  let c:=c0*∏i,p i
  let Q:ℝ:=‖eisEmbedding c‖^2
  exact fixedRadialCoefficientScalar*∑'t:ThetaFullIndex,
    ((fixedConjugateCuspArray 0 t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency t))/
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
    CubicReflectionKernel.paperKernel (Vstar W)
      (X*sourceCuspRadialLength (thetaFullFrequency t)/(27*Q^2))*
    (-(Q:ℂ)/(eisEmbedding c)^2*
      ((star (eisEmbedding (symbol c0 ((D.gamma (fun _=>1):SL(2,Eis)) 0 0)))*
        A4BadPhase c0 hc0 ((D.gamma (fun _=>1):SL(2,Eis)) 1 1) D.U (ramifiedTraceLambda*thetaFullFrequency t))*
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)*
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (ramifiedTraceLambda*thetaFullFrequency t))))

theorem smoothed_eq_reflected (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hr:lambda^2∣(∏i,p i)-1) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hp hc0 hg j W X=D.reflectedValue hp hc0 hg j W X := by
  simpa only [smoothedValue,reflectedValue,datum] using
    principal_stratum_smoothed p hp hcop hg hchar c0 D.U D.w hc0 hr D.bezout
      D.gamma D.denominator D.numerator_fixed D.inverse_fixed D.sigma D.epsilon
      D.frequency_congruence D.epsilon_value j hj W lo hi hlo hsupp hW X hX

end PrincipalStratumArithmetic

theorem exists_constructed_principal_reflection {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (N a0 c0:Eis) (hc0:c0≠0) (hc3:(3:Eis)∣c0)
    (hN:(9:Eis)*c0∣N) (ha0:lambda^2∣a0-1) (hac:IsCoprime a0 c0)
    (hNp:∀i,IsCoprime N (p i)) :
    ∃D:PrincipalStratumArithmetic p N a0 c0,
      ∀j:ι→ℕ,(∀i,j i<6)→∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→
        Function.support W⊆Set.Icc lo hi→ ContDiff ℝ ∞ W→∀X:ℝ,0<X→
        D.smoothedValue hp hc0 hg j W X=D.reflectedValue hp hc0 hg j W X := by
  obtain ⟨D⟩:=exists_principalStratumArithmetic p hp hcop hprimary N a0 c0 hc0 hc3 hN ha0 hac hNp
  refine ⟨D,?_⟩
  intro j hj W lo hi hlo hsupp hW X hX
  exact D.smoothed_eq_reflected hp hc0 hcop hg hchar
    (primary_finset_product Finset.univ p (fun i _=>hprimary i)) j hj W lo hi hlo hsupp hW X hX

end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

abbrev BasePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // Q≤P.val}
abbrev FreePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // ¬Q≤P.val}

def basePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:BasePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

def freePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:FreePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

lemma basePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma freePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖freePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:FreePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma basePrimeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) :
    CanonicalCoefficientClass.FactorsModulo Q (basePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:BasePrimeIndex I Q,_)=∏P:BasePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have he:Ideal.Quotient.mk P.val.val x=Ideal.Quotient.mk P.val.val y:=
    Ideal.Quotient.eq.mpr (P.property hxy)
  rw [he]

lemma idealRowHom_fixed_conductor_split (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    idealRowHom n I=basePrimeRow I hI Q n*freePrimeRow I hI Q n := by
  rw [idealRowHom_eq_prime_count_product I hI n]
  exact (Fintype.prod_subtype_mul_prod_subtype (fun P:PrimeIndex I=>Q≤P.val)
    (fun P:PrimeIndex I=>(actualSextic P.val ((supported_factors_good I hI P.val
      (Multiset.mem_toFinset.mp P.property)).2.1)^((normalizedFactors I).count P.val%6))
      (Ideal.Quotient.mk P.val n))).symm

lemma freePrimeIndex_pairwise_coprime (I Q:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:FreePrimeIndex I Q=>P.val.val)) := by
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPR (Subtype.ext (Subtype.ext he)))

lemma freePrimeIndex_coprime (I Q:Ideal Eis) (P:FreePrimeIndex I Q) :
    IsCoprime Q P.val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P.val.val=Q⊔P.val.val:=
    (show P.val.val.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact P.property (le_sup_left.trans he.symm.le)

lemma freePrimeProduct_coprime (I Q:Ideal Eis) :
    IsCoprime Q (∏P:FreePrimeIndex I Q,P.val.val) :=
  IsCoprime.prod_right (fun P _=>freePrimeIndex_coprime I Q P)

lemma freePrimeRow_eq_principalSexticRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    freePrimeRow I hI Q n=
      principalSexticRow (fun P:FreePrimeIndex I Q=>P.val.val) (freePrimeIndex_pairwise_coprime I Q)
        (fun P=>(supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1)
        (fun P=>(normalizedFactors I).count P.val.val%6)
        (finitePrimeModulus (fun P:FreePrimeIndex I Q=>P.val.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [principalSexticRow_mk]
  rfl

theorem fixed_conductor_absorb_shared_primes (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (hφn:∀n,‖φ n‖≤1) :
    CanonicalCoefficientClass.FactorsModulo Q (φ*basePrimeRow I hI Q) ∧
    (∀n,‖(φ*basePrimeRow I hI Q) n‖≤1) ∧
    IsCoprime Q (∏P:FreePrimeIndex I Q,P.val.val) ∧
    (∀n,φ n*idealRowHom n I=(φ*basePrimeRow I hI Q) n*freePrimeRow I hI Q n) := by
  refine ⟨?_,?_,freePrimeProduct_coprime I Q,?_⟩
  · intro x y hxy
    change φ x*basePrimeRow I hI Q x=φ y*basePrimeRow I hI Q y
    rw [hφ x y hxy,basePrimeRow_periodic I hI Q x y hxy]
  · intro n
    change ‖φ n*basePrimeRow I hI Q n‖≤1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφn n)).trans (basePrimeRow_norm I hI Q n)
  · intro n
    rw [idealRowHom_fixed_conductor_split I hI Q n]
    exact (mul_assoc _ _ _).symm

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) :
    CanonicalCoefficientClass.FactorsModulo (∏P:FreePrimeIndex I Q,P.val.val) (freePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:FreePrimeIndex I Q,_)=∏P:FreePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have hm:x-y∈P.val.val:=
    (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ P))) hxy
  rw [Ideal.Quotient.eq.mpr hm]

lemma fixedFreeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) :
    CanonicalCoefficientClass.FactorsModulo (Q*(∏P:FreePrimeIndex I Q,P.val.val))
      (φ*freePrimeRow I hI Q) := by
  intro x y hxy
  change φ x*freePrimeRow I hI Q x=φ y*freePrimeRow I hI Q y
  rw [hφ x y (Ideal.mul_le_left hxy),freePrimeRow_periodic I hI Q x y (Ideal.mul_le_right hxy)]

lemma fixedFreeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (n:Eis) : ‖(φ*freePrimeRow I hI Q) n‖≤1 := by
  change ‖φ n*freePrimeRow I hI Q n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hφ n)).trans (freePrimeRow_norm I hI Q n)

theorem exists_actual_coprime_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=φ n*freePrimeRow I hI (Q*Ideal.span {(72:Eis)}) n) := by
  obtain ⟨I,hI,φ,hφ,hφn,hrow⟩:=exists_fixed_twist_principal_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  obtain ⟨hperiod,hnorm,hcop,hprod⟩:=fixed_conductor_absorb_shared_primes I hI _ φ hφ hφn
  refine ⟨I,hI,φ*basePrimeRow I hI _,hperiod,hnorm,hcop,?_⟩
  intro n hpn
  rw [hrow n hpn,←idealRowHom_eq_principalSexticRow I hI n,hprod n]

theorem exists_actual_coprime_completed_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hQ:Q≠0) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (Q*Ideal.span {(72:Eis)}*(∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val))≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {(72:Eis)}*(∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val))
        (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) ∧
      (∀n,‖(φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) n‖≤1) ∧
      (∀W X,completedT (rowTwist Ψ m f z) W X=
        completedT (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) W X) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hrow⟩:=exists_actual_coprime_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,?_,fixedFreeRow_periodic I hI _ φ hφ,
    fixedFreeRow_norm I hI _ φ hφn,?_⟩
  · apply mul_ne_zero
    · apply mul_ne_zero hQ
      simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
      norm_num
    · exact finite_prime_product_ne_bot (fun P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)})=>P.val.val)
  · intro W X
    exact completedT_congr_primary _ _ hrow W X

def fixedQuotientValue (Q:Ideal Eis) (φ:Eis→*ℂ) (x:Eis⧸Q) : ℂ := φ (Quotient.out x)

lemma fixedQuotientValue_mk (Q:Ideal Eis) (φ:Eis→*ℂ)
    (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedQuotientValue Q φ (Ideal.Quotient.mk Q n)=φ n :=
  hφ _ _ (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out _))

lemma fixedQuotientValue_norm (Q:Ideal Eis) (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (x:Eis⧸Q) :
    ‖fixedQuotientValue Q φ x‖≤1 := hφ _

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

def goodMaskMovingIdeal (g r:Eis) : Ideal Eis := (Ideal.span {g})^6*Ideal.span {r}

lemma goodMaskMovingIdeal_supported (g r:Eis)
    (hg:Supported (Ideal.span {g})) (hr:Supported (Ideal.span {r})) :
    Supported (goodMaskMovingIdeal g r) := by
  exact (supported_mul_iff _ _).mpr ⟨supported_pow hg 6,hr⟩

lemma good_odd_prime_two_not_mem (P:Ideal Eis) [P.IsMaximal]
    (hodd:ringChar (Eis⧸P)≠2) : (2:Eis)∉P := by
  intro ht
  have he:=maximal_ideal_eq_span_of_mem P inferInstance (2:Eis) twoIdeal_maximal ht
  exact hodd (he ▸ twoIdeal_characteristic)

lemma count_span_eq_zero_of_not_mem (P:Ideal Eis) (x:Eis) (hx:x∉P) :
    (normalizedFactors (Ideal.span {x})).count P=0 := by
  apply Multiset.count_eq_zero.mpr
  intro hm
  have h0:(Ideal.span {x}:Ideal Eis)≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mpr
    intro he
    exact hx (he ▸ P.zero_mem)
  exact hx (Ideal.dvd_span_singleton.mp
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff h0).mp hm).2)

lemma good_factor_count (P:Ideal Eis) [P.IsMaximal]
    (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    (normalizedFactors (Ideal.span {u.val*lambda^a*(2:Eis)^b*r})).count P=
      (normalizedFactors (Ideal.span {r})).count P := by
  have hl:(Ideal.span {lambda}:Ideal Eis)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have ht:(Ideal.span {(2:Eis)}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hcl:=count_span_eq_zero_of_not_mem P lambda hgood
  have hct:=count_span_eq_zero_of_not_mem P 2 (good_odd_prime_two_not_mem P hodd)
  rw [show u.val*lambda^a*(2:Eis)^b*r=u.val*(lambda^a*(2:Eis)^b*r) by ring,
    Ideal.span_singleton_mul_left_unit u.isUnit,
    ←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_pow,←Ideal.span_singleton_pow,
    normalizedFactors_mul (mul_ne_zero (pow_ne_zero _ hl) (pow_ne_zero _ ht)) hr.1,
    normalizedFactors_mul (pow_ne_zero _ hl) (pow_ne_zero _ ht)]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,hcl,hct,mul_zero,zero_add]

theorem goodMaskMovingIdeal_count (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P=
      6*(normalizedFactors (Ideal.span {m})).count P+
        4*(normalizedFactors F).count P+(normalizedFactors I).count P := by
  have hmc:(normalizedFactors (Ideal.span {m})).count P=(normalizedFactors (Ideal.span {g})).count P:=by
    rw [hm]
    exact good_factor_count P hgood hodd um am bm g hg
  have hrc:(normalizedFactors (Ideal.span {r})).count P=
      4*(normalizedFactors F).count P+(normalizedFactors I).count P:=by
    have hh:=good_factor_count P hgood hodd u a b r hr
    rw [←hx,←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,hf,hz,
      normalizedFactors_mul (pow_ne_zero 4 hF) hI] at hh
    simpa only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul] using hh.symm
  rw [goodMaskMovingIdeal,normalizedFactors_mul (pow_ne_zero 6 hg.1) hr.1]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,←hmc,hrc]
  omega

lemma squarefree_prime_count_indicator (F P:Ideal Eis) (hF:Squarefree F) (hP:Prime P) :
    (normalizedFactors F).count P=if P∣F then 1 else 0 := by
  have hle:=Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hF.ne_zero).mp hF) P
  by_cases hPF:P∣F
  · rw [ite_eq_left hPF]
    have hp:=Multiset.count_pos.mpr
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mpr ⟨hP,hPF⟩)
    omega
  · rw [ite_eq_right hPF]
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hPF ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mp hm).2

theorem goodMaskMovingIdeal_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  rw [goodMaskMovingIdeal_count I F hI hF.ne_zero m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    squarefree_prime_count_indicator F P hF (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)]
  unfold completedLocalExponent
  omega

theorem goodMaskMovingIdeal_generator_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m:Eis) (v:Eisˣ)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:(idealGenerator F)^4*(v.val*idealGenerator I)=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  exact goodMaskMovingIdeal_exponent I F hI hF m (idealGenerator F) (v.val*idealGenerator I)
    (span_idealGenerator F) (by rw [Ideal.span_singleton_mul_left_unit v.isUnit,span_idealGenerator])
    um am bm g hg hm u a b r hr hx P hgood hodd

end CanonicalRowCompletion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.RowCompletion.FixedCuspBranches -/

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
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_iff_factor_count_pos (P A:Ideal Eis) (hP:Prime P) (hA:A≠0) :
    P∣A ↔ 0<(normalizedFactors A).count P := by
  simp only [Multiset.count_pos,UniqueFactorizationMonoid.mem_normalizedFactors_iff hA,hP,true_and]

theorem goodMaskMovingIdeal_dvd_iff (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    P∣goodMaskMovingIdeal g r ↔ P∣I*(Ideal.span {m}*F) := by
  have hP:Prime P:=Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hmI:(Ideal.span {m}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm0
  rw [prime_dvd_iff_factor_count_pos P _ hP (goodMaskMovingIdeal_supported g r hg hr).1,
    prime_dvd_iff_factor_count_pos P _ hP (mul_ne_zero hI (mul_ne_zero hmI hF)),
    goodMaskMovingIdeal_count I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    normalizedFactors_mul hI (mul_ne_zero hmI hF),normalizedFactors_mul hmI hF]
  simp only [Multiset.count_add]
  omega

theorem goodMaskMovingIdeal_primeSupport (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    IdealMobiusDivisorSum.primeSupport (goodMaskMovingIdeal g r)=
      (IdealMobiusDivisorSum.primeSupport (I*(Ideal.span {m}*F))).filter
        (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2) := by
  have hs:=goodMaskMovingIdeal_supported g r hg hr
  have hmI:(Ideal.span {m}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm0
  have hprod:=mul_ne_zero hI (mul_ne_zero hmI hF)
  ext P
  simp only [IdealMobiusDivisorSum.primeSupport,Finset.mem_filter,Multiset.mem_toFinset]
  constructor
  · intro hP
    obtain ⟨hmax,hgood,hodd⟩:=supported_factors_good _ hs P hP
    let:P.IsMaximal:=hmax
    have hp:Prime P:=prime_of_normalized_factor P hP
    have hd: P∣goodMaskMovingIdeal g r:=
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.1).mp hP).2
    exact ⟨(UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mpr ⟨hp,
      (goodMaskMovingIdeal_dvd_iff I F hI hF m f z hm0 hf hz um am bm g hg hm
        u a b r hr hx P hgood hodd).mp hd⟩,hgood,hodd⟩
  · rintro ⟨hP,hgood,hodd⟩
    have hp:Prime P:=prime_of_normalized_factor P hP
    let:P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hd:=((UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mp hP).2
    exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.1).mpr ⟨hp,
      (goodMaskMovingIdeal_dvd_iff I F hI hF m f z hm0 hf hz um am bm g hg hm
        u a b r hr hx P hgood hodd).mpr hd⟩

def goodMaskNonresidualPool (I F:Ideal Eis) (m g r:Eis) : Finset (Ideal Eis) :=
  (IdealMobiusDivisorSum.primeSupport (goodMaskMovingIdeal g r)).filter
    (fun P=>¬P∣rowResidualPart I (Ideal.span {m}*F))

theorem goodMaskNonresidualPool_eq (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    goodMaskNonresidualPool I F m g r=completedReflectionPool I (Ideal.span {m}*F) := by
  rw [goodMaskNonresidualPool,
    goodMaskMovingIdeal_primeSupport I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx]
  ext P
  simp only [Finset.mem_filter,completedReflectionPool]
  tauto

theorem goodMaskNonresidualPool_eq_on_fiber (I J F:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hF:F≠0) (m f z w:Eis) (hm0:m≠0)
    (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I) (hw:Ideal.span {w}=J)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (u':Eisˣ) (a' b':ℕ) (r':Eis) (hr':Supported (Ideal.span {r'}))
    (hx':f^4*w=u'.val*lambda^a'*(2:Eis)^b'*r')
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I (Ideal.span {m}*F)=rowMaskPart J (Ideal.span {m}*F)) :
    goodMaskNonresidualPool I F m g r=goodMaskNonresidualPool J F m g r' := by
  rw [goodMaskNonresidualPool_eq I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx,
    goodMaskNonresidualPool_eq J F hJ hF m f w hm0 hf hw um am bm g hg hm u' a' b' r' hr' hx']
  exact completedReflectionPool_eq_on_fiber I J (Ideal.span {m}*F) hI hJ
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF) hA hT

theorem goodMaskNonresidualPool_free_eq (I F Q0:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    (goodMaskNonresidualPool I F m g r).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I (Ideal.span {m}*F)).filter (fun P=>¬Q0≤P) := by
  rw [goodMaskNonresidualPool_eq I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx]

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

theorem goodMaskMovingIdeal_principal_row (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) (n:Eis) :
    idealRowHom n (goodMaskMovingIdeal g r)=
      principalSexticRow (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val)
        (primeIndex_pairwise_coprime (goodMaskMovingIdeal g r))
        (fun P=>(supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
          P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>completedLocalExponent I F P.val)
        (finitePrimeModulus (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [idealRowHom_eq_principalSexticRow _ (goodMaskMovingIdeal_supported g r hg hr)]
  have he:(fun P:PrimeIndex (goodMaskMovingIdeal g r)=>(normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6)=
      (fun P=>completedLocalExponent I F P.val):=by
    funext P
    have hdata:=supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
      P.val (Multiset.mem_toFinset.mp P.property)
    exact goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm
      u a b r hr hx P.val hdata.2.1 hdata.2.2
  rw [he]

theorem rowTwist_eq_computed_principal_row
    (Ψ:Eis→*ℂ) (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hpr:lambda^2∣r-1) (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n *
      principalSexticRow (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val)
        (primeIndex_pairwise_coprime (goodMaskMovingIdeal g r))
        (fun P=>(supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
          P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>completedLocalExponent I F P.val)
        (finitePrimeModulus (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2 um am bm g hg hm
    u a b r hr hpr hx n hpn]
  change _*idealRowHom n (goodMaskMovingIdeal g r)=_
  rw [goodMaskMovingIdeal_principal_row I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx n]

theorem goodMaskMovingIdeal_exponent_eq_on_fiber
    (I J F:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hF:Squarefree F)
    (m f z w:Eis) (hm0:m≠0)
    (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I) (hw:Ideal.span {w}=J)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (u':Eisˣ) (a' b':ℕ) (r':Eis) (hr':Supported (Ideal.span {r'}))
    (hx':f^4*w=u'.val*lambda^a'*(2:Eis)^b'*r')
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I (Ideal.span {m}*F)=rowMaskPart J (Ideal.span {m}*F))
    (P:completedReflectionPool I (Ideal.span {m}*F)) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=
      (normalizedFactors (goodMaskMovingIdeal g r')).count P.val%6 := by
  let:P.val.IsMaximal:=completedReflectionPool_maximal I (Ideal.span {m}*F) P
  have hgood:=completedReflectionPool_good I (Ideal.span {m}*F) P
  have hodd:=completedReflectionPool_odd I (Ideal.span {m}*F) P
  rw [goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val hgood hodd,
    goodMaskMovingIdeal_exponent J F hJ hF m f w hf hw um am bm g hg hm u' a' b' r' hr' hx' P.val hgood hodd]
  exact completedReflectionPool_exponent_eq I J F (Ideal.span {m}*F) hI hJ
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P

end CanonicalRowCompletion

namespace CubicEisenstein

section
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma amplitude_source_nonzero (p:ThetaFullIndex)
    (hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val≠0) :
    (sourceCuspCoefficients s.index).value (thetaFullFrequency p)≠0 := by
  intro hz
  apply hp
  have hz':(sourceCuspCoefficients s.index).value
      (fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val)=0:=by
    simpa only [thetaFullFrequency_eq_fixedCuspArrayIndex] using hz
  simp only [amplitude,fixedConjugateCuspArray,fixedCuspArray,hz',zero_div,ite_self,
    star_zero,zero_mul]

lemma amplitude_integral_phase (p:ThetaFullIndex) (c d:Eis) (hc:c≠0) :
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding d/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (-(eisEmbedding d*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  by_cases hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val=0
  · rw [hp,zero_mul,zero_mul]
  · rw [sourceCuspPhaseNumerator_phase s.index (s.upper 0 0) (thetaFullFrequency p) c d hc
      (s.amplitude_source_nonzero p hp)]

lemma datum_integral_phase (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) (p:ThetaFullIndex) :
    (fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency p))*
      ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
        ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      ShortDraftTrace.breveE (-(eisEmbedding (((g:SL(2,Eis))*H) 1 1)*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  have hphase:=s.datum_additive_phase g (by rwa [hg])
    (cuspFrequency (thetaFullFrequency p)) (sourceCuspScale s.index:ℂ)
  simp only [hg] at hphase
  calc
    _=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) := by
      rw [show -cuspFrequency (thetaFullFrequency p)*
          ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))=
        -cuspFrequency (thetaFullFrequency p)*(s.datum g (by rwa [hg])).dualPoint/
          (sourceCuspScale s.index:ℂ) by ring,hphase]
      unfold amplitude
      rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
      ring
    _=_:=s.amplitude_integral_phase p c _ hc

def stratumShapeFactor (c:Eis) : ℂ :=
  -star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2*
    ((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)/eisEmbedding c^2

lemma datum_common_row_factor (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) :
    (s.datum g (by rwa [hg])).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)=
      s.stratumShapeFactor c*star (levelTwoComplexCharacter g) := by
  have hm:=s.smoothed_row_factor g (by rwa [hg])
  simp only [s.datum_heightScale,hg,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hm
  rw [hm]
  unfold stratumShapeFactor
  ring

end FixedCuspShape
end

open scoped Classical BigOperators ContDiff MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

theorem sum_smoothedKernel_integral_phase {ι:Type*} [Fintype ι]
    (g:ι→levelTwo) (c:Eis) (hc:c≠0) (hC:∀v,((g v:SL(2,Eis))*H) 1 0=c)
    (w:ι→ℂ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑v,w v*(s.datum (g v) (by rw [hC v];exact hc)).smoothedKernel W X)=
      fixedRadialCoefficientScalar*s.stratumShapeFactor c*
      ∑'p:ThetaFullIndex,
        (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val /
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)*
        (∑v,w v*star (levelTwoComplexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
              eisEmbedding c)) := by
  let d:ι→SourceCuspDatum:=fun v=>s.datum (g v) (by rw [hC v];exact hc)
  have hindex:∀v,(d v).index=s.index:=fun _=>rfl
  have hheight:∀v,(d v).heightScale=(Ideal.absNorm (Ideal.span {c}):ℝ):=by
    intro v
    dsimp only [d]
    rw [s.datum_heightScale,hC v,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  have he:=sum_smoothedKernel_common_cusp d w s.index (Ideal.absNorm (Ideal.span {c}):ℝ)
    hindex hheight W a b ha hsupp hW X hX
  rw [he]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*z)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [sourceCusp_full_index_kernel_argument p s.index (Ideal.absNorm (Ideal.span {c}):ℝ) X]
  let A:ℂ:=fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
    sourceFrequencyAngle (thetaFullFrequency p)
  let B:ℂ:=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val
  let lengthScale:ι→ℂ:=fun v=>w v*((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
    ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*((d v).dualPoint/(sourceCuspScale s.index:ℂ)))
  let R:ι→ℂ:=fun v=>w v*star (levelTwoComplexCharacter (g v))*
    ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
      (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c)
  have hs:A*(∑v,lengthScale v)=s.stratumShapeFactor c*B*(∑v,R v):=by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [lengthScale,R]
    calc
      _=w v*(((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
          (A*ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d v).dualPoint/(sourceCuspScale s.index:ℂ))))):=by ring
      _=w v*((s.stratumShapeFactor c*star (levelTwoComplexCharacter (g v)))*
          (B*ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c))):=by
        rw [s.datum_common_row_factor (g v) c hc (hC v),s.datum_integral_phase (g v) c hc (hC v) p]
      _=_:=by ring
  let D:ℂ:=((ramifiedScale 1 completedRamifiedStep p.2.1*
    Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)
  let K:ℂ:=CubicReflectionKernel.paperKernel (Vstar W)
    ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
      (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)
  change A/D*K*(∑v,lengthScale v)=s.stratumShapeFactor c*(B/D*K*(∑v,R v))
  calc
    _=(A*(∑v,lengthScale v))/D*K:=by ring
    _=(s.stratumShapeFactor c*B*(∑v,R v))/D*K:=by rw [hs]
    _=_:=by ring

lemma stratumShapeFactor_norm (c:Eis) (hc:c≠0) : ‖s.stratumShapeFactor c‖=1 := by
  have hu:‖eisEmbedding (s.upper 0 0)‖=1:=by
    rcases s.upper_unit with ⟨u,hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hn:‖eisEmbedding c‖^2≠0:=pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc))
  rw [stratumShapeFactor,norm_div,norm_mul,norm_mul,norm_neg,norm_star,
    norm_levelTwoComplexCharacter,norm_pow,hu,one_pow,one_mul,one_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  exact div_self hn

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CompletedGauss

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspArrayWithPhase (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  phaseArray m n b*fixedConjugateCuspArray cusp u m n b

lemma fixedCuspArrayWithPhase_norm_le_one (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖fixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 := by
  rw [fixedCuspArrayWithPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m n b)).trans (fixedConjugateCuspArray_norm_le_one cusp u m n b)

lemma fixedCuspArrayWithPhase_zero (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible n b) : fixedCuspArrayWithPhase cusp u phaseArray m n b=0 := by
  simp only [fixedCuspArrayWithPhase,fixedConjugateCuspArray,
    fixedCuspArray_zero_of_ineligible _ _ _ _ _ h,star_zero,mul_zero]

namespace ReflectedBranchData

def extractedFixedCuspArrayWithPhase {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase cusp u phaseArray m
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1*n)
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2*b)

lemma extractedFixedCuspArrayWithPhase_norm_le_one {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 :=
  fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m _ _

lemma extractedFixedCuspArrayWithPhase_eq {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) :
    d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b=
      phaseArray m
        (reflectionExtractedDivisor (fun p:d.primes=>p.val)
          (fun p=>completedLocalExponent I F p.val) d.label 1*n)
        (reflectionExtractedDivisor (fun p:d.primes=>p.val)
          (fun p=>completedLocalExponent I F p.val) d.label 2*b)*
      d.extractedFixedCuspArray cusp u m n b := rfl

lemma extractedFixedCuspArrayWithPhase_zero {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 1*n)
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 2*b)) :
    d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b=0 :=
  fixedCuspArrayWithPhase_zero cusp u phaseArray m _ _ h

def withExtractedFixedCuspArrayWithPhase {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b=>d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow

lemma withExtractedFixedCuspArrayWithPhase_amplitude {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    (d.withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow).amplitude i n b=
      d.extractedFixedCuspArrayWithPhase cusp u phaseArray i.1 n b := rfl

theorem withExtractedFixedCuspArrayWithPhase_value {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow).value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArrayWithPhase cusp u phaseArray) rowPhase W X ρ q k :=
  d.withCanonicalCuspArray_value (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b=>d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end ReflectedBranchData
end
section

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow

lemma sixPhaseFixedCuspBranch_primes (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow).primes=reflectionActivePool I Q e := rfl

lemma sixPhaseFixedCuspBranch_amplitude (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    let d:=sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    let D:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1
    let E:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2
    d.amplitude i n b=phaseArray i.1 (D*n) (E*b)*fixedConjugateCuspArray cusp u i.1 (D*n) (E*b) := rfl

lemma sixPhaseFixedCuspBranch_scale (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q e=>P.val) (reflectionActiveLabel I Q e) := rfl

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspFiber (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=completedReflectionPool I Q
  maximal:=completedReflectionPool_maximal I Q
  divides:=completedReflectionPool_divides I Q hI hQ
  branch:=fun x=>sixPhaseFixedCuspBranch I F Q hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (phaseArray x) (hphase x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q x.2)

theorem sixPhaseFixedCuspFiber_value (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixPhaseFixedCuspFiber rays I F Q hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit phaseArray hphase rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*
      (rayWeight (t,e)*(sixPhaseFixedCuspBranch I F Q hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (phaseArray (t,e)) (hphase (t,e)) (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixPhaseFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixPhaseFixedCuspFiber]
      exact (mul_assoc _ _ _).symm

end CompletedGauss

end

end OAI

end

