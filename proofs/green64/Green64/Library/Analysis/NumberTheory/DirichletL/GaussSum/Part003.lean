module

public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part001
public import Green64.Library.OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / GaussSum / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.GaussSum.MixedConversion -/

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

open scoped BigOperators Classical

namespace MixedGaussConversion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase

def localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (canonicalSextic (Ideal.span {p}) hg ^ j)

def localCoefficient (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  star (angularFactor p) * localGauss p hp hg 2

def localG (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  breveLocalG (Ideal.span {p}) hg p rfl hp

theorem norm_localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) : ‖localGauss p hp hg j‖ = 1 := by
  let q : Unit → O := fun _ => p
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})) := by
    intro i k hik
    exact (hik (Subsingleton.elim i k)).elim
  have h := norm_canonicalProductGauss q (fun _ => hp) hcop (fun _ => hg)
    (fun _ => hchar) (fun _ => j) (fun _ => hj0) (fun _ => hj6)
  rw [canonicalProductGauss_constant_power q (fun _ => hp) hcop (fun _ => hg) j hj0] at h
  simpa only [q, Fintype.prod_unique, Finset.univ_unique, Finset.erase_singleton,
    Finset.prod_empty, Finset.prod_singleton, one_pow, one_mul, localGauss] using h

theorem canonicalSextic_fifth_eq_inverse (p : O) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    canonicalSextic (Ideal.span {p}) hg ^ 5 = (canonicalSextic (Ideal.span {p}) hg)⁻¹ := by
  apply DFunLike.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), ← MulChar.star_apply',
    canonicalSextic_conj_as_row_label]
  ring

theorem localGauss_five_eq (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    localGauss p hp hg 5 = breveGammaMinus1 (Ideal.span {p}) hg p rfl hp := by
  rw [localGauss, canonicalSextic_fifth_eq_inverse]
  rfl

theorem local_sign_conversion (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    (-localGauss p hp hg 1) * star (localG p hp hg) = star (localCoefficient p hp hg) ∧
    (-localGauss p hp hg 5) * localG p hp hg =
      canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
        localCoefficient p hp hg := by
  have h := first_poisson_prime_sign_pairing (Ideal.span {p}) hg hchar p rfl hp hprimary 1
  dsimp only at h
  simp only [map_one, mul_one, inv_one] at h
  constructor
  · simpa only [localGauss, localG, localCoefficient, angularFactor, pow_one,
      ConcreteBreveE.normalizedTraceGauss, breveGamma1, breveGamma2, star_mul, star_star,
      mul_comm] using h.2.2.1
  · rw [localGauss_five_eq]
    exact h.2.1

theorem norm_localG (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) : ‖localG p hp hg‖ = 1 := by
  have h := congrArg norm (local_sign_conversion p hp hg hchar hprimary).1
  simp only [norm_mul, norm_neg, norm_star, localCoefficient] at h
  rw [norm_localGauss p hp hg hchar 1 (by decide) (by decide), one_mul,
    norm_angularFactor p hp,
    norm_localGauss p hp hg hchar 2 (by decide) (by decide), one_mul] at h
  exact h

def convertedLocal (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (inverse : Bool) : ℂ :=
  if inverse then
    (canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
      localCoefficient p hp hg) / localG p hp hg
  else star (localCoefficient p hp hg) / star (localG p hp hg)

theorem neg_localGauss_eq_converted (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) (inverse : Bool) :
    -localGauss p hp hg (if inverse then 5 else 1) = convertedLocal p hp hg inverse := by
  have hG : localG p hp hg ≠ 0 := by
    intro hz
    have hn := norm_localG p hp hg hchar hprimary
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  cases inverse
  · exact (eq_div_iff (star_ne_zero.mpr hG)).mpr
      (local_sign_conversion p hp hg hchar hprimary).1
  · exact (eq_div_iff hG).mpr (local_sign_conversion p hp hg hchar hprimary).2

theorem moebius_mixed_gauss_conversion {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (inverse : ι → Bool) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      canonicalProductGauss p hp hcop hgood (fun i => if inverse i then 5 else 1) =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ (if inverse i then 5 else 1))
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ∏ i, convertedLocal (p i) (hp i) (hgood i) (inverse i) := by
  rw [product_moebius_eq_sign p hcop, canonicalProductGauss_cross_factors]
  have hprod : (-1 : ℂ) ^ Fintype.card ι *
      (∏ i, localGauss (p i) (hp i) (hgood i) (if inverse i then 5 else 1)) =
      ∏ i, convertedLocal (p i) (hp i) (hgood i) (inverse i) := by
    rw [← Finset.card_univ, ← Finset.prod_neg]
    apply Finset.prod_congr rfl
    intro i _
    exact neg_localGauss_eq_converted (p i) (hp i) (hgood i) (hchar i) (hprimary i) (inverse i)
  calc
    _ = (∏ i, ∏ k ∈ Finset.univ.erase i,
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ (if inverse i then 5 else 1))
            (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ((-1 : ℂ) ^ Fintype.card ι *
          ∏ i, localGauss (p i) (hp i) (hgood i) (if inverse i then 5 else 1)) := by
      unfold localGauss
      ring
    _ = _ := by rw [hprod]

end MixedGaussConversion

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion

theorem pair_moebius_eq_active
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (S T : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ) =
      (UniqueFactorizationMonoid.moebius
        (Ideal.span {∏ i : activeSupport S T, p i.val}) : ℂ) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hcop := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  rw [prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj T,
    product_moebius_eq_sign (fun i : activeSupport S T => p i.val) hcop, ← pow_add]
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have ha : Fintype.card (activeSupport S T) = (S \ T).card + (T \ S).card := by
    rw [Fintype.card_coe, activeSupport, Finset.card_union_of_disjoint hd]
  have hs := Finset.card_sdiff_add_card_inter S T
  have ht := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at ht
  have hcard : S.card + T.card = Fintype.card (activeSupport S T) + 2 * (S ∩ T).card := by omega
  rw [hcard, pow_add, pow_mul]
  norm_num

def activeConvertedGauss
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) : ℂ :=
  (∏ i : activeSupport S T,
    ∏ k ∈ @Finset.erase (activeSupport S T)
      (fun a b => Classical.propDecidable (a = b)) Finset.univ i,
    (canonicalSextic (Ideal.span {p i.val}) (hgood i.val) ^ activeExponent S T i)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) *
    ∏ i : activeSupport S T,
      convertedLocal (p i.val) (hp i.val) (hgood i.val) (decide (i.val ∈ S \ T))

def activePairDualSeries
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let row := finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
    (fun i => hgood i.val) (activeExponent S T)
  let n := ∏ i : activeSupport S T, p i.val
  ∑ E ∈ (S ∩ T).powerset,
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, star (row h) * paperRadialFourier W
        (scale * ‖eisEmbedding h‖ ^ 2 /
          (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

def convertedPairPoissonKernel
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  ((scale : ℂ) / (‖eisEmbedding (∏ i : activeSupport S T, p i.val)‖ : ℂ)) *
    activeConvertedGauss p hp hgood S T * activePairDualSeries p hgood S T W scale

theorem moebius_squarefreePairPoissonKernel_conversion
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ)) *
      squarefreePairPoissonKernel (fun i => Ideal.span {p i}) hinj hgood S T W scale =
      convertedPairPoissonKernel p hp hgood S T W scale := by
  let q : activeSupport S T → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  have hg : (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
      canonicalProductGauss q (fun i => hp i.val) hQ (fun i => hgood i.val)
        (activeExponent S T) = activeConvertedGauss p hp hgood S T := by
    have he : activeExponent S T =
        (fun i : activeSupport S T => if decide (i.val ∈ S \ T) then 5 else 1) := by
      funext i
      simp only [activeExponent, decide_eq_true_eq]
    unfold activeConvertedGauss
    rw [he]
    exact moebius_mixed_gauss_conversion q (fun i => hp i.val) hQ (fun i => hgood i.val)
      (fun i => hchar i.val) (fun i => hprimary i.val) (fun i => decide (i.val ∈ S \ T))
  rw [pair_moebius_eq_active p hinj S T, squarefreePairPoissonKernel_eq_product p hp hinj hgood]
  change (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
      (((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ
        (fun i => hgood i.val) (activeExponent S T) / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
          activePairDualSeries p hgood S T W scale) = _
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
        ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
          canonicalProductGauss q (fun i => hp i.val) hQ (fun i => hgood i.val)
            (activeExponent S T)) * activePairDualSeries p hgood S T W scale := by ring
    _ = _ := by rw [hg]; rfl

theorem moebius_pair_radial_poisson_converted
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ)) *
      (∑' z : O, (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood S z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood T z) *
          W (‖eisEmbedding z‖ ^ 2 / scale)) =
      convertedPairPoissonKernel p hp hgood S T W scale := by
  rw [finiteSquarefreeRow_pair_radial_poisson (fun i => Ideal.span {p i}) hinj hgood hchar
    S T W scale hscale]
  exact moebius_squarefreePairPoissonKernel_conversion p hp hinj hgood hchar hprimary S T W scale

theorem moebius_pair_kernel_conversion_of_generators
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (p : ι → O) (hP : ∀ i, P i = Ideal.span {p i}) (hp : ∀ i, p i ≠ 0)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    letI : ∀ i, (Ideal.span {p i}).IsMaximal := fun i =>
      (hP i) ▸ (inferInstance : (P i).IsMaximal)
    let hg : ∀ i, lambda ∉ Ideal.span {p i} := fun i => (hP i) ▸ hgood i
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, P i) : ℂ)) *
      squarefreePairPoissonKernel P hinj hgood S T W scale =
      convertedPairPoissonKernel p hp hg S T W scale := by
  have hPeq : P = fun i => Ideal.span {p i} := funext hP
  subst P
  exact moebius_squarefreePairPoissonKernel_conversion p hp hinj hgood hchar hprimary S T W scale

end GaussGeneratorTransport

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def mobiusIdealColumn (C : Ideal O → ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * C I

noncomputable def conjugateIdealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (y : O) : ℂ :=
  ∑ I ∈ F, mobiusIdealColumn C I * star (idealSexticRow F hFpos hFgood I y)

theorem conjugateIdealRowSum_eq_star
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (y : O) :
    conjugateIdealRowSum F hFpos hFgood C y =
      star (∑ I ∈ F, star (mobiusIdealColumn C I) * idealSexticRow F hFpos hFgood I y) := by
  simp only [conjugateIdealRowSum, star_sum, star_mul, star_star, mul_comm]

theorem conjugateIdealRowSum_smoothed_summable
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun y : O => W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) := by
  simp_rw [conjugateIdealRowSum_eq_star, norm_star]
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_smoothed_mean_square_summable
    (fun i : primePool F => i.val) (primePool_good F hFgood)
    F (idealSupport F) (fun I => star (mobiusIdealColumn C I)) W scale hscale

theorem conjugateIdealRowSum_smoothed_poisson
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonKernel F hFpos hFgood J I W scale := by
  simp_rw [conjugateIdealRowSum_eq_star, norm_star]
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  change (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
    (↑(‖∑ I ∈ F, star (mobiusIdealColumn C I) *
      finiteSquarefreeRow (fun i : primePool F => i.val) (primePool_good F hFgood)
        (idealSupport F I) y‖ ^ 2) : ℂ)) = _
  rw [finiteSquarefreeRow_smoothed_mean_square_expand
    (fun i : primePool F => i.val) (primePool_good F hFgood)
    F (idealSupport F) (fun I => star (mobiusIdealColumn C I)) W scale hscale,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteSquarefreeRow_pair_radial_poisson
    (fun i : primePool F => i.val) Subtype.val_injective (primePool_good F hFgood)
    hchar (idealSupport F J) (idealSupport F I) W scale hscale, star_star]
  rw [mul_comm (mobiusIdealColumn C J)]
  rfl

theorem mobiusIdealColumn_eq_zero_of_not_squarefree
    (C : Ideal O → ℂ) {I : Ideal O} (hI : ¬ Squarefree I) :
    mobiusIdealColumn C I = 0 := by
  simp only [mobiusIdealColumn, UniqueFactorizationMonoid.moebius_of_not_squarefree hI,
    Int.cast_zero, zero_mul]

theorem conjugateIdealRowSum_zeroMode_offDiagonal
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F) (hIJ : I ≠ J)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
      idealPairPoissonZeroMode F hFpos hFgood J I W scale = 0 := by
  by_cases hsI : Squarefree I
  · by_cases hsJ : Squarefree J
    · have hsupport : idealSupport F J ≠ idealSupport F I := fun h =>
        hIJ (idealSupport_injective_on_squarefree F hJ hI hsJ hsI h).symm
      let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
      have hz : idealPairPoissonZeroMode F hFpos hFgood J I W scale = 0 :=
        squarefreePairPoissonZeroMode_eq_zero_of_ne (fun i : primePool F => i.val)
          Subtype.val_injective (primePool_good F hFgood) hsupport W scale
      rw [hz, mul_zero]
    · simp [mobiusIdealColumn_eq_zero_of_not_squarefree C hsJ]
  · simp [mobiusIdealColumn_eq_zero_of_not_squarefree C hsI]

theorem conjugateIdealRowSum_zeroMode_formula
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale) =
    (scale : ℂ) * paperRadialFourier W 0 *
      ∑ I ∈ F, (↑(‖mobiusIdealColumn C I‖ ^ 2) : ℂ) * idealPrimeDensity F I := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single I]
  · rw [idealPairPoissonZeroMode_diag, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    change (star _ * _) * _ = _ * ((star _ * _) * _)
    ring
  · intro J hJ hJI
    exact conjugateIdealRowSum_zeroMode_offDiagonal F hFpos hFgood C hI hJ hJI.symm W scale
  · exact fun h => (h hI).elim

theorem conjugateIdealRowSum_smoothed_poisson_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) =
    (scale : ℂ) * paperRadialFourier W 0 *
      (∑ I ∈ F, (↑(‖mobiusIdealColumn C I‖ ^ 2) : ℂ) * idealPrimeDensity F I) +
      ∑ I ∈ F, ∑ J ∈ F,
        (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
          idealPairPoissonNonzeroMode F hFpos hFgood J I W scale := by
  rw [conjugateIdealRowSum_smoothed_poisson F hFpos hFgood hchar C W scale hscale]
  simp_rw [idealPairPoissonKernel_zero_split F hFpos hFgood _ _ W scale hscale,
    mul_add, Finset.sum_add_distrib]
  rw [conjugateIdealRowSum_zeroMode_formula F hFpos hFgood C W scale]

theorem norm_mobiusIdealColumn_le (C : Ideal O → ℂ) (I : Ideal O) :
    ‖mobiusIdealColumn C I‖ ≤ ‖C I‖ := by
  by_cases hI : Squarefree I
  · simp only [mobiusIdealColumn, hI.moebius_eq, Int.cast_pow, Int.cast_neg,
      Int.cast_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_refl]
  · rw [mobiusIdealColumn_eq_zero_of_not_squarefree C hI, norm_zero]
    exact norm_nonneg _

theorem norm_conjugateIdealRowSum_zeroMode_le
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale‖ ≤
      (|scale| * ‖paperRadialFourier W 0‖) * ∑ I ∈ F, ‖C I‖ ^ 2 := by
  rw [conjugateIdealRowSum_zeroMode_formula F hFpos hFgood C W scale,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (idealPrimeDensity_mem_Icc F hFpos I).1]
  calc
    _ ≤ ‖mobiusIdealColumn C I‖ ^ 2 := mul_le_of_le_one_right
      (sq_nonneg _) (idealPrimeDensity_mem_Icc F hFpos I).2
    _ ≤ ‖C I‖ ^ 2 := by gcongr; exact norm_mobiusIdealColumn_le C I

theorem norm_secondPoisson_zeroMode_fixed_factors
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (ξ ρ : Ideal O → ℂ) (A : ℕ → ℂ)
    (hξ : ∀ I ∈ F, ‖ξ I‖ ≤ 1) (hρ : ∀ I ∈ F, ‖ρ I‖ ≤ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    let C : Ideal O → ℂ := fun I => ξ I * ρ I * A (Ideal.absNorm I)
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale‖ ≤
      (|scale| * ‖paperRadialFourier W 0‖) * ∑ I ∈ F, ‖A (Ideal.absNorm I)‖ ^ 2 := by
  dsimp only
  refine (norm_conjugateIdealRowSum_zeroMode_le F hFpos hFgood
    (fun I => ξ I * ρ I * A (Ideal.absNorm I)) W scale).trans ?_
  gcongr with I hI
  simp only [norm_mul]
  calc
    ‖ξ I‖ * ‖ρ I‖ * ‖A (Ideal.absNorm I)‖ ≤
        1 * 1 * ‖A (Ideal.absNorm I)‖ := by gcongr; exact hξ I hI; exact hρ I hI
    _ = _ := by ring

end ConcretePrimeRowBridge

open MeasureTheory Set
open scoped BigOperators

namespace EisensteinSchwartzPoisson

theorem scaled_cauchy_antitone (b : ℝ) :
    AntitoneOn (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg b, sq_nonneg (y - x),
    mul_nonneg (sq_nonneg b) (show 0 ≤ y ^ 2 - x ^ 2 by nlinarith)]

theorem scaled_cauchy_nat_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / (2 * b) := by
  have hi := (integrable_inv_one_add_mul_sq hb.ne').integrableOn (s := Ioi 0)
  have ht := (scaled_cauchy_antitone b).tsum_le_integral hi
    (fun t ht => by positivity)
  have he : (∫ x : ℝ in Ioi 0, (1 + (b * x) ^ 2)⁻¹) = Real.pi / (2 * b) := by
    rw [integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero,
      smul_eq_mul]
    ring
  simpa [he] using ht

theorem summable_scaled_cauchy_nat (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℕ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  exact (scaled_cauchy_antitone b).summable_of_integrableOn_Ioi_zero
    (integrable_inv_one_add_mul_sq hb.ne').integrableOn (fun _ _ => by positivity)

theorem summable_scaled_cauchy_int (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_scaled_cauchy_nat b hb
  · simpa [mul_neg] using summable_scaled_cauchy_nat b hb

theorem scaled_cauchy_int_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / b := by
  have hs := summable_scaled_cauchy_nat b hb
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hneg : Summable (fun n : ℕ =>
      (1 + (b * ((-(n + 1) : ℤ) : ℝ)) ^ 2)⁻¹) := by
    convert hs1 using 1
    ext n
    push_cast
    congr 1
    ring
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹)
    (by simpa only [Int.cast_natCast] using hs) hneg]
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, mul_neg,
    neg_sq]
  have hz := hs.tsum_eq_zero_add
  have he : (∑' n : ℕ, (1 + (b * (↑n + 1)) ^ 2)⁻¹) =
      (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hz.symm
  rw [he]
  have := scaled_cauchy_nat_bound b hb
  have hh : Real.pi / (2 * b) = (Real.pi / b) / 2 := by ring
  rw [hh] at this
  linarith

open ConcreteTraceCRT ActualEisensteinCubic

theorem scaled_eisenstein_cauchy_summable (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  apply (latticeCoordEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hp.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (b * (p.1 : ℝ)) (b * (p.2 : ℝ))
    (K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) (by positivity)
  change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
    K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
  rw [eisEmbedding_eval_norm_sq]
  push_cast
  nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]

theorem scaled_eisenstein_cauchy_bound (K : ℝ) (hK : 0 < K) :
    (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi / Real.sqrt K) ^ 2 := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  have he : (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) =
      ∑' p : ℤ × ℤ, ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹ :=
    (latticeCoordEquiv.symm.tsum_eq _).symm
  rw [he]
  calc
    _ ≤ ∑' p : ℤ × ℤ, 4 * ((1 + (b * (p.1 : ℝ)) ^ 2)⁻¹ *
          (1 + (b * (p.2 : ℝ)) ^ 2)⁻¹) := by
      apply ((latticeCoordEquiv.symm.summable_iff).mpr
        (scaled_eisenstein_cauchy_summable K hK)).tsum_le_tsum _ (hp.mul_left 4)
      intro p
      apply inverse_square_le_cauchy_product _ _ _ (by positivity)
      change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
        K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
      rw [eisEmbedding_eval_norm_sq]
      push_cast
      nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]
    _ = 4 * (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ^ 2 := by
      rw [tsum_mul_left, ← hs.tsum_mul_tsum hs hp, pow_two]
    _ ≤ 4 * (1 + Real.pi / b) ^ 2 := by
      gcongr
      exact scaled_cauchy_int_bound b hb

theorem scaled_eisenstein_cauchy_small (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    K * (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi) ^ 2 := by
  have hs := scaled_eisenstein_cauchy_bound K hK
  have hb : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hb1 : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
  have hsq := Real.sq_sqrt hK.le
  calc
    _ ≤ K * (4 * (1 + Real.pi / Real.sqrt K) ^ 2) :=
      mul_le_mul_of_nonneg_left hs hK.le
    _ = 4 * (Real.sqrt K + Real.pi) ^ 2 := by
      nth_rw 1 [← hsq]
      field_simp
    _ ≤ _ := by gcongr

theorem one_le_eisenstein_norm_sq (h : O) (hh : h ≠ 0) :
    1 ≤ ‖eisEmbedding h‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {h}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hh)

theorem cauchy_large_scale_pointwise (K q : ℝ) (hK : 1 ≤ K) (hq : 1 ≤ q) :
    K * ((1 + K * q) ^ 2)⁻¹ ≤ 4 * ((1 + q) ^ 2)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hqp : 0 < q := by linarith
  have h1 : K * (1 + q) ≤ 2 * (1 + K * q) := by nlinarith
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ K * (1 + q)) h1 2
  have h3 : K * (1 + q) ^ 2 ≤ K ^ 2 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (1 + q)]
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + K * q) ^ 2)
    (by positivity : 0 < (1 + q) ^ 2)).mpr
  nlinarith

theorem lattice_profile_nonzero_scaled_bound
    (F : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 2 * ‖F t‖ ≤ B)
    (K : ℝ) (hK : 0 < K) :
    K * (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * B := by
  have hm (h : O) : ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      B * ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hF (K * ‖eisEmbedding h‖ ^ 2) (by positivity)
  have hs := scaled_eisenstein_cauchy_summable K hK
  have hf : Summable (fun h : O => ‖F (K * ‖eisEmbedding h‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hm (hs.mul_left B)
  have hsub := hf.subtype (fun h : O => h ≠ 0)
  have hc := eisenstein_cauchy_summable.subtype (fun h : O => h ≠ 0)
  by_cases hK1 : K ≤ 1
  · have htotal : (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        ∑' h : O, ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ :=
      hsub.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hf
    have hbound := hf.tsum_le_tsum hm (hs.mul_left B)
    rw [tsum_mul_left] at hbound
    calc
      _ ≤ K * (B * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (htotal.trans hbound) hK.le
      _ = B * (K * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by ring
      _ ≤ B * (4 * (1 + Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_left (scaled_eisenstein_cauchy_small K hK hK1) hB
      _ ≤ _ := by nlinarith [eisensteinCauchyMass_nonneg]
  · have hp (h : {h : O // h ≠ 0}) :
        K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
          (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
      calc
        _ ≤ K * (B * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hm h.val) hK.le
        _ = B * (K * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
        _ ≤ B * (4 * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (cauchy_large_scale_pointwise K _
            (le_of_not_ge hK1) (one_le_eisenstein_norm_sq h.val h.property)) hB
        _ = _ := by ring
    calc
      _ = ∑' h : {h : O // h ≠ 0}, K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left.symm
      _ ≤ ∑' h : {h : O // h ≠ 0}, (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
        (hsub.mul_left K).tsum_le_tsum hp (hc.mul_left (4 * B))
      _ = (4 * B) * ∑' h : {h : O // h ≠ 0}, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
      _ ≤ (4 * B) * eisensteinCauchyMass := mul_le_mul_of_nonneg_left
        (eisensteinCauchyMass_subtype (fun h : O => h ≠ 0)) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (1 + Real.pi)]

theorem paperRadialFourier_nonzero_lattice_uniform :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (K : ℝ), 0 < K →
        K * (∑' h : {h : O // h ≠ 0},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
            C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨s, (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * C, ?_, ?_⟩
  · have := eisensteinCauchyMass_nonneg
    have := Real.pi_pos
    positivity
  · intro W K hK
    simpa only [mul_assoc] using lattice_profile_nonzero_scaled_bound
      (paperRadialFourier W) (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
        (by positivity) (hb W) K hK

end EisensteinSchwartzPoisson

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization -/

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

namespace ActualEisensteinCubic

theorem primary_associated_eq (x y : O) (hxy : Associated x y)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) : x = y := by
  obtain ⟨u, hu⟩ := hxy
  have huprimary : lambda ^ 2 ∣ (u : O) - 1 := by
    have heq : (u : O) - 1 = (y - 1) - (x - 1) * (u : O) := by
      rw [← hu]
      ring
    rw [heq]
    exact dvd_sub hy (dvd_mul_of_dvd_left hx _)
  have huone : (u : O) = 1 := A3_primary_unit_eq_one _ u.isUnit huprimary
  simpa only [huone, mul_one] using hu

theorem primary_multiset_prod (s : Multiset O)
    (hs : ∀ x ∈ s, lambda ^ 2 ∣ x - 1) : lambda ^ 2 ∣ s.prod - 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have hb := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.prod_cons]
    have heq : a * s.prod - 1 = (a - 1) * s.prod + (s.prod - 1) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

theorem primary_maximal_divisor_good (t : O) (ht : lambda ^ 2 ∣ t - 1)
    (P : Ideal O) [P.IsMaximal] (htP : t ∈ P) : lambda ∉ P := by
  intro hlam
  have hlam2 : lambda ^ 2 ∈ P := by
    simpa only [pow_two] using P.mul_mem_left lambda hlam
  have hsub : t - 1 ∈ P := Ideal.mem_of_dvd P ht hlam2
  have hone : (1 : O) ∈ P := by simpa using P.sub_mem htP hsub
  exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
    ((Ideal.eq_top_iff_one _).mpr hone)

theorem exists_primary_prime_factorization (t : O) (ht0 : t ≠ 0)
    (ht : lambda ^ 2 ∣ t - 1) :
    ∃ s : Multiset O, s.prod = t ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
  classical
  obtain ⟨f, hf, hft⟩ := UniqueFactorizationMonoid.exists_prime_factors t ht0
  have hfgood : ∀ r ∈ f, lambda ∉ (Ideal.span {r} : Ideal O) := by
    intro r hr
    have hp := hf r hr
    let : (Ideal.span {r} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    apply primary_maximal_divisor_good t ht
    exact Ideal.mem_span_singleton.mpr ((Multiset.dvd_prod hr).trans hft.dvd)
  have hreplace : ∃ s : Multiset O, Associated s.prod f.prod ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
    clear hft
    induction f using Multiset.induction_on with
    | empty => exact ⟨0, Associated.refl _, by simp⟩
    | @cons a f ih =>
      have ha := hf a (Multiset.mem_cons_self _ _)
      let : (Ideal.span {a} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible ha.irreducible
      obtain ⟨r, hrspan, hrprimary, _⟩ := cubicJacobi_exists_primary_generator
        (Ideal.span {a}) (hfgood a (Multiset.mem_cons_self _ _))
      have har : Associated a r := Ideal.span_singleton_eq_span_singleton.mp hrspan
      obtain ⟨s, hsf, hs⟩ := ih
        (fun r hr => hf r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hfgood r (Multiset.mem_cons_of_mem hr))
      refine ⟨r ::ₘ s, ?_, ?_⟩
      · simpa only [Multiset.prod_cons] using har.symm.mul_mul hsf
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ⟨har.prime_iff.mp ha, hrprimary⟩
        · exact hs x hx
  obtain ⟨s, hsf, hs⟩ := hreplace
  refine ⟨s, ?_, hs⟩
  exact primary_associated_eq _ _ (hsf.trans hft)
    (primary_multiset_prod s (fun r hr => (hs r hr).2)) ht

theorem residue_char_mem (P : Ideal O) :
    (ringChar (O ⧸ P) : O) ∈ P := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_natCast]
  exact CharP.cast_eq_zero (O ⧸ P) (ringChar (O ⧸ P))

theorem maximal_eq_or_eq_of_same_residue_char
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (hRP : ringChar (O ⧸ R) = ringChar (O ⧸ P)) : R = P ∨ R = Q := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  obtain ⟨a, b, _, _, _, _, hcover⟩ := rational_prime_ideal_cover
    (ringChar (O ⧸ P)) (CharP.char_is_prime (O ⧸ P) _)
  have hp := hcover P inferInstance (residue_char_mem P)
  have hq := hcover Q inferInstance (by rw [← hPQ]; exact residue_char_mem Q)
  have hr := hcover R inferInstance (by rw [← hRP]; exact residue_char_mem R)
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    rcases hr with hr | hr <;> simp_all

theorem prime_divisor_residue_char_ne
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (t : O) (htP : t ∉ P) (htQ : t ∉ Q) (htR : t ∈ R) :
    ringChar (O ⧸ R) ≠ ringChar (O ⧸ P) := by
  intro hRP
  rcases maximal_eq_or_eq_of_same_residue_char P Q R hne hPQ hRP with rfl | rfl
  · exact htP htR
  · exact htQ htR

theorem lambda_sq_dvd_three : lambda ^ 2 ∣ (3 : O) := by
  have hlam : lambda ^ 2 = -3 * omega := by
    change (omega - 1) ^ 2 = -3 * omega
    linear_combination omega_sq_for_norm
  refine ⟨-omega ^ 2, ?_⟩
  rw [hlam]
  calc
    (3 : O) = 3 * omega ^ 3 := by rw [omega_primitive.pow_eq_one]; ring
    _ = -3 * omega * -omega ^ 2 := by ring

theorem neg_two_primary : lambda ^ 2 ∣ (-2 : O) - 1 := by
  convert dvd_neg.mpr lambda_sq_dvd_three using 1 ; ring

theorem neg_add_primary (p q : O)
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1) :
    lambda ^ 2 ∣ -(p + q) - 1 := by
  have hd := dvd_neg.mpr (dvd_add (dvd_add hp hq) lambda_sq_dvd_three)
  convert hd using 1 ; ring

theorem prime_generator_not_mem_of_ne (P Q : Ideal O)
    [P.IsMaximal] [Q.IsMaximal] (hne : P ≠ Q)
    (q : O) (hQ : Q = Ideal.span {q}) : q ∉ P := by
  intro hq
  have hle : Q ≤ P := by
    rw [hQ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hq
  exact hne (Ideal.IsMaximal.eq_of_le (inferInstance : Q.IsMaximal)
    (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) hle).symm

theorem cubic_reciprocity_equal_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hne : P ≠ Q) (hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  classical
  let t : O := -(p + q)
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hqP : q ∉ P := prime_generator_not_mem_of_ne P Q hne q hQ
  have hpQ : p ∉ Q := prime_generator_not_mem_of_ne Q P hne.symm p hP
  have htP : t ∉ P := by
    intro ht
    have hs : p + q ∈ P := by simpa only [t, neg_neg] using P.neg_mem ht
    exact hqP (by simpa only [add_sub_cancel_left] using P.sub_mem hs hpP)
  have htQ : t ∉ Q := by
    intro ht
    have hs : p + q ∈ Q := by simpa only [t, neg_neg] using Q.neg_mem ht
    exact hpQ (by simpa only [add_sub_cancel_right] using Q.sub_mem hs hqQ)
  have ht0 : t ≠ 0 := fun h => htP (h ▸ P.zero_mem)
  obtain ⟨s, hst, hs⟩ := exists_primary_prime_factorization t ht0
    (neg_add_primary p q hpprimary hqprimary)
  have hlocal : ∀ r ∈ s,
      cubicChar P hPgood (Ideal.Quotient.mk P r) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q r) := by
    intro r hr
    let R : Ideal O := Ideal.span {r}
    let : R.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hs r hr).1.irreducible
    have hrR : r ∈ R := Ideal.subset_span (by simp)
    have htR : t ∈ R := Ideal.mem_span_singleton.mpr (hst ▸ Multiset.dvd_prod hr)
    have hRgood : lambda ∉ R := primary_maximal_divisor_good t
      (neg_add_primary p q hpprimary hqprimary) R htR
    have hRP := prime_divisor_residue_char_ne P Q R hne hchar t htP htQ htR
    have hRQ : ringChar (O ⧸ R) ≠ ringChar (O ⧸ Q) := by rwa [hchar]
    rw [cubic_reciprocity_distinct_residue_char P R hPgood hRgood hRP
      p r hP rfl hpprimary (hs r hr).2,
      cubic_reciprocity_distinct_residue_char Q R hQgood hRgood hRQ
      q r hQ rfl hqprimary (hs r hr).2]
    have hsum : Ideal.Quotient.mk R p + Ideal.Quotient.mk R q = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr htR
      simpa only [t, map_neg, map_add, neg_eq_zero] using hz
    have heq : Ideal.Quotient.mk R p = -Ideal.Quotient.mk R q := eq_neg_of_add_eq_zero_left hsum
    rw [heq, ← neg_one_mul (Ideal.Quotient.mk R q), map_mul,
      A3_cubicChar_neg_one, one_mul]
  have hmul : ∀ f : Multiset O,
      (∀ r ∈ f, cubicChar P hPgood (Ideal.Quotient.mk P r) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q r)) →
      cubicChar P hPgood (Ideal.Quotient.mk P f.prod) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q f.prod) := by
    intro f
    induction f using Multiset.induction_on with
    | empty => intro _; simp
    | @cons r f ih =>
      intro hf
      simp only [Multiset.prod_cons, map_mul]
      rw [hf r (Multiset.mem_cons_self _ _), ih
        (fun x hx => hf x (Multiset.mem_cons_of_mem hx))]
  have htval := hmul s hlocal
  rw [hst] at htval
  have hpzero : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hqzero : Ideal.Quotient.mk Q q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqQ
  simp only [t, map_neg, map_add, hpzero, hqzero, zero_add, add_zero] at htval
  rw [← neg_one_mul (Ideal.Quotient.mk P q), map_mul, A3_cubicChar_neg_one, one_mul,
    ← neg_one_mul (Ideal.Quotient.mk Q p), map_mul, A3_cubicChar_neg_one, one_mul] at htval
  exact htval

theorem cubic_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  by_cases hPQ : P = Q
  · have hqP : q ∈ P := by rw [hPQ, hQ]; exact Ideal.subset_span (by simp)
    have hpQ : p ∈ Q := by rw [← hPQ, hP]; exact Ideal.subset_span (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqP,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpQ, MulChar.map_zero, MulChar.map_zero]
  · by_cases hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P)
    · exact cubic_reciprocity_equal_residue_char P Q hPgood hQgood hPQ hchar
        p q hP hQ hpprimary hqprimary
    · exact cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
        p q hP hQ hpprimary hqprimary

theorem canonicalSextic_sq_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_primary P Q hPgood hQgood p q hP hQ hpprimary hqprimary]

def cubicTwoIdeal : Ideal O := Ideal.span {(-2 : O)}

instance cubicTwoIdeal_isMaximal : cubicTwoIdeal.IsMaximal := by
  rcases rational_prime_factor_cases 2 Nat.prime_two with hm |
      ⟨a, b, _, _, _, ha, _, _, _⟩
  · simpa only [cubicTwoIdeal, Ideal.span_singleton_neg, Nat.cast_ofNat] using hm
  · have hin : (Ideal.span {a} : Ideal O) ∈ {I : Ideal O | Ideal.absNorm I = 2} := by
      change Ideal.absNorm (Ideal.span {a}) = 2
      rwa [← qNat_eq_absNorm_span]
    rw [ShortDraftHeckeBridge.norm_p_fiber_inert Nat.prime_two (by decide)] at hin
    exact False.elim hin

theorem cubicTwoIdeal_good : lambda ∉ cubicTwoIdeal := by
  apply primary_maximal_divisor_good (-2 : O) neg_two_primary
  exact Ideal.subset_span (by simp)

theorem cubicTwoIdeal_residue_char : ringChar (O ⧸ cubicTwoIdeal) = 2 := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field cubicTwoIdeal
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  have hmem : (2 : O) ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.subset_span (by simp)
  have hz : (2 : O ⧸ cubicTwoIdeal) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ cubicTwoIdeal) _)
    Nat.prime_two).mp ((ringChar.spec (O ⧸ cubicTwoIdeal) 2).mp hz)

theorem canonicalSextic_four_eq_fixed_two
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)) =
      ConcreteTraceCRT.eisEmbedding
        (cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal p)) := by
  have hfour : Ideal.Quotient.mk P (4 : O) = (Ideal.Quotient.mk P (-2 : O)) ^ 2 := by
    simp only [map_ofNat, map_neg]
    ring
  rw [hfour, map_pow, ← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
    canonicalSextic_pow_two]
  change ConcreteTraceCRT.eisEmbedding (cubicChar P hgood (Ideal.Quotient.mk P (-2 : O))) = _
  congr 1
  exact cubic_reciprocity_primary P cubicTwoIdeal hgood cubicTwoIdeal_good
    p (-2) hP rfl hprimary neg_two_primary

theorem canonicalSextic_four_prod_eq_fixed_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) =
      ConcreteTraceCRT.eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
        (Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i))) := by
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_four_eq_fixed_two (P i) (hgood i) (p i) (hP i hi) (hprimary i hi)

theorem canonicalSextic_four_prod_eq_one_of_mod_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hmod : (2 : O) ∣ (∏ i ∈ s, p i) - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) = 1 := by
  have hmem : (∏ i ∈ s, p i) - 1 ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.mem_span_singleton.mpr hmod
  have heq : Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i) = 1 := by
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  rw [canonicalSextic_four_prod_eq_fixed_two s P hgood p hP hprimary, heq, map_one, map_one]

end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem sum_square_phase_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) :
    (∑ x : T, ψ (x ^ 2)) =
      ∏ i, ∑ y : R i, coordinateAddChar R e ψ i (y ^ 2) := by
  calc
    _ = ∑ x : T, ∏ i, coordinateAddChar R e ψ i ((e x i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ (x ^ 2)]
      simp only [map_pow, Pi.pow_apply]
    _ = ∑ x : ∀ i, R i, ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2) :=
      Equiv.sum_comp e.toEquiv
        (fun x : ∀ i, R i => ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2))
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => coordinateAddChar R e ψ i (x ^ 2))).symm

theorem quadratic_gauss_finite_crt_eq_square_sum {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ)
    (hψ : ψ.IsPrimitive) (hchar : ∀ i, ringChar (R i) ≠ 2) :
    (∑ x : T, (∏ i, ((quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) (e x i)) * ψ x) =
      ∑ x : T, ψ (x ^ 2) := by
  rw [gauss_sum_finite_crt R e
    (fun i => (quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) ψ,
    sum_square_phase_finite_crt R e ψ]
  apply Finset.prod_congr rfl
  intro i _
  have hp := coordinateAddChar_isPrimitive R e ψ hψ i
  have hn : coordinateAddChar R e ψ i ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hp (a := 1) one_ne_zero
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase _ (hchar i) hn

end IdealGaussCRT

namespace QuadraticGaussRay

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem canonicalProductGauss_three_eq_quadraticGamma
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticGammaO (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let e := productElementCRT p hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ Ideal.span {p i}) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) hchar

theorem I_zpow_eq_of_mod_four {a b : ℤ} (h : (a : ZMod 4) = b) :
    Complex.I ^ a = Complex.I ^ b := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a 4).mp h.symm
  have ha : a = b + 4 * k := by omega
  rw [ha, zpow_add₀ Complex.I_ne_zero, zpow_mul]
  norm_num

theorem fourTerms_eq_of_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    breveGaussianFourTerms a b = breveGaussianFourTerms c d := by
  have hn : ((-b : ℤ) : ZMod 4) = (-d : ℤ) := by simpa using congrArg Neg.neg hb
  have hs : ((b-a : ℤ) : ZMod 4) = (d-c : ℤ) := by
    push_cast
    rw [ha, hb]
  rw [breveGaussianFourTerms_formula, breveGaussianFourTerms_formula,
    I_zpow_eq_of_mod_four ha, I_zpow_eq_of_mod_four hn, I_zpow_eq_of_mod_four hs]

def quadraticRayValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  breveGaussianFourTerms (r.1.val : ℤ) (r.2.val : ℤ)

theorem quadraticGammaO_eq_rayValue (c : O) (hc : c ≠ 0) :
    quadraticGammaO c hc = quadraticRayValue (residue c) := by
  have h := quadraticGammaO_eq_fourTerms (coords c).1 (coords c).2 (by rwa [eval_coords])
  have h' : quadraticGammaO c hc = breveGaussianFourTerms (coords c).1 (coords c).2 := by
    simpa only [eval_coords] using h
  rw [h']
  unfold quadraticRayValue residue
  exact fourTerms_eq_of_mod_four (by simp) (by simp)

theorem quadraticGammaO_eq_of_residue_eq (c d : O) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : residue c = residue d) : quadraticGammaO c hc = quadraticGammaO d hd := by
  rw [quadraticGammaO_eq_rayValue, quadraticGammaO_eq_rayValue, h]

theorem canonicalProductGauss_three_eq_rayValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticRayValue (residue (∏ i, p i)) := by
  rw [canonicalProductGauss_three_eq_quadraticGamma p hp hcop hgood hchar,
    quadraticGammaO_eq_rayValue]

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem fixed_two_mk_eq_residue_lift (c : O) :
    Ideal.Quotient.mk cubicTwoIdeal c =
      Ideal.Quotient.mk cubicTwoIdeal (lift (residue c)) := by
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq (residue_lift (residue c)).symm
  apply Ideal.Quotient.eq.mpr
  rw [cubicTwoIdeal, Ideal.mem_span_singleton]
  refine ⟨(-2 : O) * z, ?_⟩
  calc
    c - lift (residue c) = 4 * z := hz
    _ = (-2 : O) * (-2 * z) := by ring

def fixedGValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  (eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
    (Ideal.Quotient.mk cubicTwoIdeal (lift r))))⁻¹ * quadraticRayValue r

theorem residue_eq_of_four_dvd_sub (c d : O) (h : (4 : O) ∣ c - d) :
    residue c = residue d := by
  obtain ⟨z, hz⟩ := h
  have he : c = eval ((coords d).1 + 4 * (coords z).1)
      ((coords d).2 + 4 * (coords z).2) := by
    calc
      c = d + 4 * z := by linear_combination hz
      _ = eval (coords d).1 (coords d).2 + 4 * eval (coords z).1 (coords z).2 := by
        rw [eval_coords, eval_coords]
      _ = _ := by simp only [eval]; push_cast; ring
  rw [he, residue_eval]
  simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]

theorem residue_eq_of_quotient_four_eq (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) : residue c = residue d :=
  residue_eq_of_four_dvd_sub c d (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h))

def residueQuotientFour : (O ⧸ Ideal.span {(4 : O)}) → EisensteinEPrimaryPhase.Coord :=
  Quotient.lift residue (fun c d h => residue_eq_of_quotient_four_eq c d (Quotient.sound h))

@[simp] theorem residueQuotientFour_mk (c : O) :
    residueQuotientFour (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c) = residue c := rfl

def fixedGQuotientValue (r : O ⧸ Ideal.span {(4 : O)}) : ℂ :=
  fixedGValue (residueQuotientFour r)

theorem canonicalProductG_eq_fixedGValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood = fixedGValue (residue (∏ i, p i)) := by
  rw [canonicalProductG,
    canonicalSextic_four_prod_eq_fixed_two Finset.univ (fun i => Ideal.span {p i}) hgood p
      (fun i _ => rfl) (fun i _ => hprimary i),
    canonicalProductGauss_three_eq_rayValue p hp hcop hgood hchar,
    fixed_two_mk_eq_residue_lift]
  rfl

theorem canonicalProductG_eq_of_residue_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (kcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (kgood : ∀ i, lambda ∉ Ideal.span {q i})
    (kchar : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (kprimary : ∀ i, lambda ^ 2 ∣ q i - 1)
    (hres : residue (∏ i, p i) = residue (∏ i, q i)) :
    canonicalProductG p hp hcop hgood = canonicalProductG q hq kcop kgood := by
  rw [canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary,
    canonicalProductG_eq_fixedGValue q hq kcop kgood kchar kprimary, hres]

theorem canonicalProductG_eq_fixed_quotient
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i, p i)) :=
  canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary

end QuadraticGaussRay

end

end OAI

end

