module

public import Green64.Library.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
public import Green64.Library.Analysis.NumberTheory.DirichletL.GaussSum.Part002

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / PrimeRows / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization -/

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

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT

theorem idealRowSum_smoothed_summable
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun u : O => W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_smoothed_mean_square_summable
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    F (idealSupport F) (fun I => baseChangeWeight χ I * A (Ideal.absNorm I))
    W scale hscale

theorem idealRowSum_smoothed_expand
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
          (baseChangeWeight χ J * A (Ideal.absNorm J))) *
        ∑' u : O, (star (idealSexticRow F hFpos hFgood I u) *
          idealSexticRow F hFpos hFgood J u) * W (‖eisEmbedding u‖ ^ 2 / scale) := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_smoothed_mean_square_expand
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    F (idealSupport F) (fun I => baseChangeWeight χ I * A (Ideal.absNorm I))
    W scale hscale

end ConcretePrimeRowBridge

open scoped BigOperators Classical
namespace ActualEisensteinCubic

def activeSupport {α : Type*} [DecidableEq α] (S T : Finset α) : Finset α :=
  (S \ T) ∪ (T \ S)

abbrev activePrimes {α : Type*} [DecidableEq α]
    (P : α → Ideal O) (S T : Finset α) (i : activeSupport S T) : Ideal O := P i.val

def activeExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 5 else 1

theorem activeExponent_ne_zero {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : activeExponent S T i ≠ 0 := by
  unfold activeExponent
  split_ifs <;> decide

theorem activeExponent_lt_six {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : activeExponent S T i < 6 := by
  unfold activeExponent
  split_ifs <;> decide

theorem activePrimes_injective {α : Type*} [DecidableEq α]
    (P : α → Ideal O) (hinj : Function.Injective P) (S T : Finset α) :
    Function.Injective (activePrimes P S T) := by
  intro a b h
  apply Subtype.ext
  exact hinj h

theorem activePrimes_pairwise_isCoprime {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S T : Finset α) :
    Pairwise (Function.onFun IsCoprime (activePrimes P S T)) := by
  intro a b hab
  exact Ideal.isCoprime_of_isMaximal (fun h => hab (activePrimes_injective P hinj S T h))

theorem finiteSexticRow_activeSupport {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset α) (u : O) :
    finiteSexticRow (activePrimes P S T) (fun i => hgood i.val) (activeExponent S T) u =
      star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  classical
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hpow5 (i : α) :
      (canonicalSextic (P i) (hgood i) ^ 5) (Ideal.Quotient.mk (P i) u) =
        star (canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)) := by
    rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0)]
    rw [canonicalSextic_conj_as_row_label]
    ring
  unfold finiteSexticRow activePrimes activeExponent
  let f : α → ℂ := fun i =>
    (canonicalSextic (P i) (hgood i) ^ (if i ∈ S \ T then 5 else 1))
      (Ideal.Quotient.mk (P i) u)
  change (∏ i : activeSupport S T, f i.val) = _
  rw [Finset.prod_coe_sort (s := activeSupport S T) (f := f)]
  change (∏ i ∈ (S \ T) ∪ (T \ S),
    (canonicalSextic (P i) (hgood i) ^ (if i ∈ S \ T then 5 else 1))
      (Ideal.Quotient.mk (P i) u)) = _
  rw [Finset.prod_union hd]
  simp only [finiteSquarefreeRow, star_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_left hi, hpow5]
  · apply Finset.prod_congr rfl
    intro i hi
    have hnot : i ∉ S \ T := fun h => Finset.disjoint_left.mp hd h hi
    rw [ite_eq_right hnot, pow_one]

theorem finiteSquarefreeRow_pair_activeSupport {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset α) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u =
      rowCoprimeMask P (S ∩ T) u *
        finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
          (activeExponent S T) u := by
  rw [finiteSexticRow_activeSupport P hgood S T u]
  have hk := finiteSquarefreeRow_pair_kernel P hgood S T u
  simpa only [mul_assoc] using hk

open ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def squarefreePairPoissonKernel
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))

theorem finiteSquarefreeRow_pair_radial_poisson
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, (star (finiteSquarefreeRow P hgood S u) *
      finiteSquarefreeRow P hgood T u) * W (‖eisEmbedding u‖ ^ 2 / scale)) =
      squarefreePairPoissonKernel P hinj hgood S T W scale := by
  calc
    _ = ∑' u : O, rowCoprimeMask P (S ∩ T) u *
        finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
          (activeExponent S T) u * W (‖eisEmbedding u‖ ^ 2 / scale) := by
      apply tsum_congr
      intro u
      rw [finiteSquarefreeRow_pair_activeSupport]
    _ = _ := canonical_masked_radial_poisson_collected P hinj (S ∩ T)
      (activePrimes P S T) (activePrimes_pairwise_isCoprime P hinj S T)
      (fun i => hgood i.val) (fun i => hchar i.val)
      (activeExponent S T) (activeExponent_ne_zero S T) (activeExponent_lt_six S T)
      W scale hscale

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def idealPairPoissonKernel
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonKernel (fun i : primePool F => i.1)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem idealRowSum_smoothed_poisson
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.1) ≠ 2)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
          (baseChangeWeight χ J * A (Ideal.absNorm J))) *
        idealPairPoissonKernel F hFpos hFgood I J W scale := by
  rw [idealRowSum_smoothed_expand F hFpos hFgood χ A W scale hscale]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_pair_radial_poisson
    (fun i : primePool F => i.1) Subtype.val_injective (primePool_good F hFgood)
    hchar (idealSupport F I) (idealSupport F J) W scale hscale

end ConcretePrimeRowBridge

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem gauss_sum_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ x) =
      ∏ i, gaussSum (χ i) (coordinateAddChar R e ψ i) := by
  classical
  calc
    _ = ∑ x : T, ∏ i, χ i (e x i) * coordinateAddChar R e ψ i (e x i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ x, Finset.prod_mul_distrib]
    _ = ∑ x : ∀ i, R i, ∏ i, χ i (x i) * coordinateAddChar R e ψ i (x i) :=
      Equiv.sum_comp e.toEquiv (fun x : ∀ i, R i =>
        ∏ i, χ i (x i) * coordinateAddChar R e ψ i (x i))
    _ = _ := by
      simpa only [gaussSum] using
        (Fintype.prod_sum (fun i (x : R i) => χ i x * coordinateAddChar R e ψ i x)).symm

end IdealGaussCRT

namespace FiniteGaussPhase

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def cofactor {ι : Type*} [Fintype ι] (p : ι → O) (i : ι) : O :=
  ∏ k ∈ Finset.univ.erase i, p k

theorem prime_mul_cofactor {ι : Type*} [Fintype ι]
    (p : ι → O) (i : ι) : p i * cofactor p i = ∏ k, p k :=
  Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)

theorem span_finset_prod {ι : Type*} (s : Finset ι) (p : ι → O) :
    Ideal.span {∏ i ∈ s, p i} = ∏ i ∈ s, Ideal.span {p i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ← Ideal.span_singleton_mul_span_singleton, ih]

theorem cofactor_coprime {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) : IsCoprime (Ideal.span {p i}) (Ideal.span {cofactor p i}) := by
  rw [cofactor, span_finset_prod]
  exact IsCoprime.prod_right (fun k hk => hcop (Ne.symm (Finset.mem_erase.mp hk).1))

def productElementCRT {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    (O ⧸ Ideal.span {∏ i, p i}) ≃+* ∀ i, O ⧸ Ideal.span {p i} :=
  (Ideal.quotEquivOfEq (span_finset_prod Finset.univ p)).trans
    (IdealGaussCRT.quotientProdEquivPi (fun i => Ideal.span {p i}) hcop)

@[simp] theorem productElementCRT_mk {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (a : O) (i : ι) :
    productElementCRT p hcop (Ideal.Quotient.mk (Ideal.span {∏ k, p k}) a) i =
      Ideal.Quotient.mk (Ideal.span {p i}) a := by
  simp only [productElementCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    IdealGaussCRT.quotientProdEquivPi_mk]

theorem productElementCRT_axis {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (u v : O) (hbez : u * p i + v * cofactor p i = 1) (x : O) :
    (productElementCRT p hcop).symm (Pi.single i (Ideal.Quotient.mk (Ideal.span {p i}) x)) =
      Ideal.Quotient.mk (Ideal.span {∏ k, p k}) (x * v * cofactor p i) := by
  apply (productElementCRT p hcop).injective
  rw [RingEquiv.apply_symm_apply]
  funext k
  rw [productElementCRT_mk]
  by_cases hk : k = i
  · subst k
    simp only [Pi.single_eq_same, map_mul]
    have hlocal := IdealGaussCRT.bezout_inverse_left hbez
    calc
      Ideal.Quotient.mk (Ideal.span {p i}) x =
          Ideal.Quotient.mk (Ideal.span {p i}) x *
            (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i) *
              Ideal.Quotient.mk (Ideal.span {p i}) v) := by rw [hlocal, mul_one]
      _ = _ := by ring
  · have hd : p k ∣ cofactor p i := Finset.dvd_prod_of_mem p (by simp [hk])
    have hz : Ideal.Quotient.mk (Ideal.span {p k}) (cofactor p i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    simp only [Pi.single_eq_of_ne hk, map_mul, hz, mul_zero]

theorem coordinate_trace_character {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (u v : O) (hbez : u * p i + v * cofactor p i = 1) :
    IdealGaussCRT.coordinateAddChar (fun i => O ⧸ Ideal.span {p i}) (productElementCRT p hcop)
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (∏ k, p k) (Finset.prod_ne_zero_iff.mpr (fun k _ => hp k))) i =
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (p i) (hp i)).mulShift (Ideal.Quotient.mk (Ideal.span {p i}) v) := by
  classical
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  change eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      (∏ k, p k) (Finset.prod_ne_zero_iff.mpr (fun k _ => hp k)) ((productElementCRT p hcop).symm
        (Pi.single i (Ideal.Quotient.mk (Ideal.span {p i}) x))) =
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      (p i) (hp i) (Ideal.Quotient.mk (Ideal.span {p i}) v *
        Ideal.Quotient.mk (Ideal.span {p i}) x)
  rw [productElementCRT_axis p hcop i u v hbez x, ← map_mul,
    eisTraceModChar_eq_paperE, eisTraceModChar_eq_paperE]
  congr 1
  have hb : eisEmbedding (cofactor p i) ≠ 0 :=
    eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k _ => hp k))
  rw [← prime_mul_cofactor p i]
  simp only [map_mul]
  field_simp

theorem gauss_sum_product_element {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    [Fintype (O ⧸ Ideal.span {∏ i, p i})] [∀ i, Fintype (O ⧸ Ideal.span {p i})]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    (∑ x : O ⧸ Ideal.span {∏ i, p i},
      (∏ i, χ i (productElementCRT p hcop x i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) x) =
      ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)) *
        gaussSum (χ i) (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i)) := by
  rw [IdealGaussCRT.gauss_sum_finite_crt]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨u, v, hbez⟩ := IdealGaussCRT.bezout_of_principal_coprime (cofactor_coprime p hcop i)
  rw [coordinate_trace_character p hp hcop i u v hbez]
  exact IdealGaussCRT.gauss_shift_bezout_left hbez (χ i) _

def normalizedProductTraceGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) : ℂ := by
  let hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  letI : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  exact (∑ x : O ⧸ Ideal.span {∏ i, p i},
    (∏ i, χ i (productElementCRT p hcop x i)) *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) hpall x) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)

theorem normalizedProductTraceGauss_crt {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    normalizedProductTraceGauss p hp hcop χ =
      ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)) *
        ConcreteBreveE.normalizedTraceGauss (p i) (hp i) (χ i) := by
  let hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let (i : ι) : Finite (O ⧸ Ideal.span {p i}) := finite_quotient_span (hp i)
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have hn : (‖eisEmbedding (∏ i, p i)‖ : ℂ) = ∏ i, (‖eisEmbedding (p i)‖ : ℂ) := by
    rw [map_prod, norm_prod]
    norm_cast
  change (∑ x : O ⧸ Ideal.span {∏ i, p i},
    (∏ i, χ i (productElementCRT p hcop x i)) *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) hpall x) / (‖eisEmbedding (∏ i, p i)‖ : ℂ) = _
  rw [gauss_sum_product_element p hp hcop χ, hn, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change (_ * _) / _ = _ * (_ / _)
  ring

theorem normalizedProductTraceGauss_cross_factors {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    normalizedProductTraceGauss p hp hcop χ =
      (∏ i, ∏ k ∈ Finset.univ.erase i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ∏ i, ConcreteBreveE.normalizedTraceGauss (p i) (hp i) (χ i) := by
  rw [normalizedProductTraceGauss_crt, Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [cofactor, map_prod]

def canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) : ℂ :=
  normalizedProductTraceGauss p hp hcop (fun i => canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i)

theorem canonicalProductGauss_cross_factors {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    canonicalProductGauss p hp hcop hgood j =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ∏ i, ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i) :=
  normalizedProductTraceGauss_cross_factors p hp hcop _

theorem canonicalProductGauss_constant_power {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ℕ) (hj : j ≠ 0) :
    canonicalProductGauss p hp hcop hgood (fun _ => j) =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        canonicalSextic (Ideal.span {p i}) (hgood i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) ^ j *
        ∏ i, ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j) := by
  rw [canonicalProductGauss_cross_factors]
  simp only [MulChar.pow_apply' _ hj, Finset.prod_pow]

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def angularFactor (a : O) : ℂ := eisEmbedding a / (‖eisEmbedding a‖ : ℂ)

theorem angularFactor_prod {ι : Type*} [Fintype ι] (p : ι → O) :
    angularFactor (∏ i, p i) = ∏ i, angularFactor (p i) := by
  unfold angularFactor
  rw [map_prod, norm_prod, Complex.ofReal_prod, Finset.prod_div_distrib]

def canonicalCrossFactor {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  ∏ i, ∏ k ∈ Finset.univ.erase i,
    canonicalSextic (Ideal.span {p i}) (hgood i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (p k))

theorem prime_generator_not_mem_other {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : p k ∉ Ideal.span {p i} := by
  intro h
  have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
  have ht := (hcop hik).sup_eq
  rw [sup_eq_left.mpr hle] at ht
  exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht

theorem canonicalCrossFactor_pow_six {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalCrossFactor p hgood ^ 6 = 1 := by
  unfold canonicalCrossFactor
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hnot := prime_generator_not_mem_other p hcop i k
    (Ne.symm (Finset.mem_erase.mp hk).1)
  simpa only [map_pow, ite_eq_right hnot] using
    (canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hgood i) (p k))

def canonicalProductCoefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  star (angularFactor (∏ i, p i)) * canonicalProductGauss p hp hcop hgood (fun _ => 2)

theorem canonicalProductCoefficient_crt {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalProductCoefficient p hp hcop hgood =
      canonicalCrossFactor p hgood ^ 2 *
        ∏ i, star (angularFactor (p i)) *
          ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
            (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2) := by
  rw [canonicalProductCoefficient, canonicalProductGauss_constant_power p hp hcop hgood 2
    (by decide), angularFactor_prod, star_prod, Finset.prod_mul_distrib]
  unfold canonicalCrossFactor
  ring

theorem product_moebius_eq_sign {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) =
      (-1 : ℂ) ^ Fintype.card ι := by
  have hinj : Function.Injective (fun i => Ideal.span {p i}) := by
    intro i k h
    by_contra hik
    have ht := (hcop hik).sup_eq
    rw [h, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p k}).IsMaximal).ne_top ht
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [span_finset_prod]
  simpa only [Finset.card_univ] using
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj Finset.univ

theorem canonicalProductGauss_two_cube {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductGauss p hp hcop hgood (fun _ => 2) ^ 3 =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        angularFactor (∏ i, p i) := by
  have hlocal (i : ι) :
      ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2) ^ 3 =
        -angularFactor (p i) := by
    change breveGamma2 (Ideal.span {p i}) (hgood i) (p i) rfl (hp i) ^ 3 = _
    simpa only [angularFactor, neg_div] using
      breveGamma2_cube (Ideal.span {p i}) (hgood i) (p i) rfl (hp i) (hprimary i)
  rw [canonicalProductGauss_constant_power p hp hcop hgood 2 (by decide),
    mul_pow, ← pow_mul]
  change canonicalCrossFactor p hgood ^ 6 * _ = _
  rw [canonicalCrossFactor_pow_six p hcop hgood, one_mul, ← Finset.prod_pow]
  simp_rw [hlocal]
  rw [Finset.prod_neg, product_moebius_eq_sign p hcop, angularFactor_prod]
  rfl

def canonicalProductG {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  (∏ i, canonicalSextic (Ideal.span {p i}) (hgood i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
    canonicalProductGauss p hp hcop hgood (fun _ => 3)

theorem canonicalProductGauss_one_two_relation {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductGauss p hp hcop hgood (fun _ => 1) *
      canonicalProductGauss p hp hcop hgood (fun _ => 2) =
      canonicalProductG p hp hcop hgood *
        canonicalProductGauss p hp hcop hgood (fun _ => 2) ^ 3 := by
  let g (j : ℕ) (i : ι) := ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
    (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j)
  let v (i : ι) := canonicalSextic (Ideal.span {p i}) (hgood i)
    (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O))
  have hlocal (i : ι) : g 1 i * g 2 i = (v i)⁻¹ * g 3 i * (g 2 i) ^ 3 := by
    simpa only [g, v, pow_one, ConcreteBreveE.normalizedTraceGauss,
      breveGamma1, breveGamma2, breveGamma3] using
      breveGamma1_gamma2_relation (Ideal.span {p i}) (hgood i) (hchar i)
        (p i) rfl (hp i) (hprimary i)
  have hprod : (∏ i, g 1 i) * (∏ i, g 2 i) =
      (∏ i, v i)⁻¹ * (∏ i, g 3 i) * (∏ i, g 2 i) ^ 3 := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [hlocal]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, Finset.prod_pow]
  rw [canonicalProductG,
    canonicalProductGauss_constant_power p hp hcop hgood 1 (by decide),
    canonicalProductGauss_constant_power p hp hcop hgood 2 (by decide),
    canonicalProductGauss_constant_power p hp hcop hgood 3 (by decide)]
  change (canonicalCrossFactor p hgood ^ 1 * ∏ i, g 1 i) *
    (canonicalCrossFactor p hgood ^ 2 * ∏ i, g 2 i) =
    ((∏ i, v i)⁻¹ * (canonicalCrossFactor p hgood ^ 3 * ∏ i, g 3 i)) *
      (canonicalCrossFactor p hgood ^ 2 * ∏ i, g 2 i) ^ 3
  rw [mul_pow, ← pow_mul]
  change _ = _ * (canonicalCrossFactor p hgood ^ 6 * _)
  rw [canonicalCrossFactor_pow_six p hcop hgood, one_mul]
  calc
    _ = canonicalCrossFactor p hgood ^ 3 * ((∏ i, g 1 i) * ∏ i, g 2 i) := by ring
    _ = _ := by rw [hprod]; ring

theorem canonicalProductGauss_one_two_eq_moebius {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductGauss p hp hcop hgood (fun _ => 1) *
      canonicalProductGauss p hp hcop hgood (fun _ => 2) =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        angularFactor (∏ i, p i) * canonicalProductG p hp hcop hgood := by
  rw [canonicalProductGauss_one_two_relation p hp hcop hgood hchar hprimary,
    canonicalProductGauss_two_cube p hp hcop hgood hprimary]
  ring

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

theorem angularFactor_mul_star (a : O) (ha : a ≠ 0) :
    angularFactor a * star (angularFactor a) = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj', norm_angularFactor a ha]
  norm_num

theorem norm_canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) :
    ‖canonicalProductGauss p hp hcop hgood j‖ = 1 := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let e := productElementCRT p hcop
  let χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ := fun i =>
    canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  have hχ : ∀ i, χ i ≠ 1 := fun i =>
    canonicalSextic_pow_ne_one (Ideal.span {p i}) (hgood i) (hchar i) (hj0 i) (hj6 i)
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq
    (fun i => O ⧸ Ideal.span {p i}) e χ ψ hχ
    (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun i => O ⧸ Ideal.span {p i}) e ψ hψ i)
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      using eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  have hnorm := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq
  change ‖(∑ x : O ⧸ Ideal.span {c}, (∏ i, χ i (e x i)) * ψ x) /
    (‖eisEmbedding c‖ : ℂ)‖ = 1
  rw [norm_div, hnorm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc))

theorem norm_canonicalProductG {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    ‖canonicalProductG p hp hcop hgood‖ = 1 := by
  have h := congrArg norm
    (canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary)
  simp only [norm_mul, product_moebius_eq_sign p hcop, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_angularFactor _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))] at h
  rw [norm_canonicalProductGauss p hp hcop hgood hchar (fun _ => 1)
      (by intro; decide) (by intro; decide),
    norm_canonicalProductGauss p hp hcop hgood hchar (fun _ => 2)
      (by intro; decide) (by intro; decide), one_mul] at h
  exact h.symm

theorem canonicalProductCoefficient_mul_gauss_one {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductCoefficient p hp hcop hgood *
      canonicalProductGauss p hp hcop hgood (fun _ => 1) =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        canonicalProductG p hp hcop hgood := by
  have hα := angularFactor_mul_star (∏ i, p i)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  unfold canonicalProductCoefficient
  calc
    _ = star (angularFactor (∏ i, p i)) *
        (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
          canonicalProductGauss p hp hcop hgood (fun _ => 2)) := by ring
    _ = _ := by
      rw [canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary]
      calc
        _ = (angularFactor (∏ i, p i) * star (angularFactor (∏ i, p i))) *
            ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
              canonicalProductG p hp hcop hgood) := by ring
        _ = _ := by rw [hα, one_mul]

theorem moebius_star_gauss_one_eq_coefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) =
      (canonicalProductG p hp hcop hgood)⁻¹ * canonicalProductCoefficient p hp hcop hgood := by
  have hα := angularFactor_mul_star (∏ i, p i)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hg : canonicalProductGauss p hp hcop hgood (fun _ => 1) *
      star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj',
      norm_canonicalProductGauss p hp hcop hgood hchar (fun _ => 1)
        (by intro; decide) (by intro; decide)]
    norm_num
  have hG : canonicalProductG p hp hcop hgood ≠ 0 := by
    intro hz
    have hn := norm_canonicalProductG p hp hcop hgood hchar hprimary
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hA : canonicalProductCoefficient p hp hcop hgood =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
          canonicalProductG p hp hcop hgood := by
    unfold canonicalProductCoefficient
    calc
      _ = star (angularFactor (∏ i, p i)) *
          star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
            (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
              canonicalProductGauss p hp hcop hgood (fun _ => 2)) := by
        calc
          _ = (star (angularFactor (∏ i, p i)) *
              canonicalProductGauss p hp hcop hgood (fun _ => 2)) * 1 := by ring
          _ = _ := by rw [← hg]; ring
      _ = _ := by
        rw [canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary]
        calc
          _ = (angularFactor (∏ i, p i) * star (angularFactor (∏ i, p i))) *
              ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
                star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
                  canonicalProductG p hp hcop hgood) := by ring
          _ = _ := by rw [hα, one_mul]
  rw [hA]
  field_simp

end FiniteGaussPhase

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.ActiveConductor -/

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

namespace ActualEisensteinCubic

section

 theorem activeSupport_nonempty_of_ne {α : Type*} [DecidableEq α]
    {S T : Finset α} (h : S ≠ T) : (activeSupport S T).Nonempty := by
  by_contra hn
  apply h
  have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  ext i
  simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
  exact ⟨fun hi => he.1 hi, fun hi => he.2 hi⟩

 theorem activeRow_zero_of_ne {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) {S T : Finset α} (h : S ≠ T) :
    finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) 0 = 0 := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne h).to_subtype
  exact finiteSexticRow_zero _ _ _

open ConcreteTraceCRT EisensteinSchwartzPoisson

 theorem finiteSexticRow_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 1 := by
  simp [finiteSexticRow]

 theorem finitePrimeModulus_norm_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) : ‖eisEmbedding (finitePrimeModulus P)‖ = 1 := by
  have h := finitePrimeModulus_norm_sq P
  simp only [Finset.univ_eq_empty, Finset.prod_empty, map_one, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (finitePrimeModulus P))]

 theorem canonicalGaussSum_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalGaussSum P hcop hgood j = 1 := by
  let c := finitePrimeModulus P
  have hc : Ideal.span {c} = ⊤ := by
    simpa only [c, Finset.univ_eq_empty, Finset.prod_empty, Ideal.one_eq_top] using
      span_finitePrimeModulus P
  have hzero (r : O ⧸ Ideal.span {c}) : r = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hc]; trivial)
  let : Subsingleton (O ⧸ Ideal.span {c}) := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  unfold canonicalGaussSum
  change (∑ r : O ⧸ Ideal.span {c}, _ ) = 1
  rw [Fintype.sum_subsingleton _ 0]
  simp [principalSexticRow, finiteSexticQuotientRow]

 theorem canonicalNormalizedGauss_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j = 1 := by
  rw [canonicalNormalizedGauss, canonicalGaussSum_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, div_one]

noncomputable def squarefreePairPoissonZeroMode
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        (star (row 0) * paperRadialFourier W 0)

 theorem squarefreePairPoissonZeroMode_eq_zero_of_ne
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    {S T : Finset ι} (hST : S ≠ T) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S T W scale = 0 := by
  simp only [squarefreePairPoissonZeroMode, activeRow_zero_of_ne P hgood hST,
    star_zero, zero_mul, mul_zero, Finset.sum_const_zero]

 theorem squarefreePairPoissonZeroMode_diag
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S S W scale =
      (scale : ℂ) * paperRadialFourier W 0 *
        ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ) := by
  have hempty : activeSupport S S = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport S S) := ⟨fun x => by simpa [hempty] using x.property⟩
  simp only [squarefreePairPoissonZeroMode, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    Finset.inter_self, finiteSexticRow_of_isEmpty, star_one, one_mul]
  rw [← Finset.sum_mul]
  have hn (E : Finset ι) : ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
      (ConcretePrimeRowBridge.span_idealGenerator _)
  simp_rw [hn, Complex.ofReal_natCast]
  ring

end

open EisensteinSchwartzPoisson

theorem primeSubset_moebius_norm_sum
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    (∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) =
      ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  simp only [Finset.prod_const_one, mul_one,  map_prod, Nat.cast_prod,
    Finset.prod_inv_distrib, div_eq_mul_inv, one_mul]

theorem primeDensity_nonneg_le_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    0 ≤ (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ∧
      (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ≤ 1 := by
  have hfactor (i : ι) : 0 ≤ 1 - (1 : ℝ) / Ideal.absNorm (P i) ∧
      1 - (1 : ℝ) / Ideal.absNorm (P i) ≤ 1 := by
    have hnorm : (1 : ℝ) ≤ Ideal.absNorm (P i) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne (P i)))
    constructor
    · exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hnorm)
    · have : 0 ≤ (1 : ℝ) / Ideal.absNorm (P i) := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun i _ => (hfactor i).1),
    Finset.prod_le_one₀ (fun i _ => (hfactor i).1) (fun i _ => (hfactor i).2)⟩

theorem squarefreePairPoissonZeroMode_diag_product
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S S W scale =
      (scale : ℂ) * paperRadialFourier W 0 *
        ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [squarefreePairPoissonZeroMode_diag, primeSubset_moebius_norm_sum P hprime hinj]

theorem norm_squarefreePairPoissonZeroMode_diag_le
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖squarefreePairPoissonZeroMode P hinj hgood S S W scale‖ ≤
      |scale| * ‖paperRadialFourier W 0‖ := by
  rw [squarefreePairPoissonZeroMode_diag_product P hprime]
  have hp : (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) =
      ((∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) : ℝ) := by
    simp only [Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hp, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeDensity_nonneg_le_one P S).1]
  exact mul_le_of_le_one_right (by positivity) (primeDensity_nonneg_le_one P S).2

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

noncomputable def idealPairPoissonZeroMode
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonZeroMode (fun i : primePool F => i.1)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem weighted_idealPairPoissonZeroMode_eq_zero_of_ne
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F) (hIJ : I ≠ J)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale = 0 := by
  by_cases hsI : Squarefree I
  · by_cases hsJ : Squarefree J
    · have hsupport : idealSupport F I ≠ idealSupport F J := fun h =>
        hIJ (idealSupport_injective_on_squarefree F hI hJ hsI hsJ h)
      let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
      have hz : idealPairPoissonZeroMode F hFpos hFgood I J W scale = 0 :=
        squarefreePairPoissonZeroMode_eq_zero_of_ne (fun i : primePool F => i.1)
          Subtype.val_injective (primePool_good F hFgood) hsupport W scale
      rw [hz, mul_zero]
    · simp [baseChangeWeight_eq_zero_of_not_squarefree χ hsJ]
  · simp [baseChangeWeight_eq_zero_of_not_squarefree χ hsI]

theorem idealRowSum_zeroMode_diagonal
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale) =
    ∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
      idealPairPoissonZeroMode F hFpos hFgood I I W scale := by
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single I]
  · rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  · intro J hJ hJI
    exact weighted_idealPairPoissonZeroMode_eq_zero_of_ne F hFpos hFgood
      χ A hI hJ hJI.symm W scale
  · exact fun h => (h hI).elim

theorem norm_idealRowSum_zeroMode_le
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale‖ ≤
    (|scale| * ‖paperRadialFourier W 0‖) *
      ∑ I ∈ F, ‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2 := by
  rw [idealRowSum_zeroMode_diagonal F hFpos hFgood χ A W scale, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.val := by
    obtain ⟨I, hI, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  have hb : ‖idealPairPoissonZeroMode F hFpos hFgood I I W scale‖ ≤
      |scale| * ‖paperRadialFourier W 0‖ :=
    norm_squarefreePairPoissonZeroMode_diag_le (fun i : primePool F => i.val)
      hprime Subtype.val_injective (primePool_good F hFgood) (idealSupport F I) W scale
  nlinarith [mul_le_mul_of_nonneg_left hb
    (sq_nonneg ‖baseChangeWeight χ I * A (Ideal.absNorm I)‖)]

end ConcretePrimeRowBridge

open scoped BigOperators Classical SchwartzMap ContDiff
namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem activeRow_norm_le_one
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι) (h : O) :
    ‖finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) h‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (finiteSquarefreeRow_norm_le_one P hgood (S \ T) h)
      (finiteSquarefreeRow_norm_le_one P hgood (T \ S) h) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

theorem activeRow_paperFourier_summable
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun h : O => star (finiteSexticRow (activePrimes P S T)
      (fun i => hgood i.val) (activeExponent S T) h) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W scale hscale)
  intro h
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (activeRow_norm_le_one P hgood S T h)

theorem activeRow_paperFourier_zero_split
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) (den : ℝ) (hden : 0 < den) :
    let row := finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T)
    (∑' h : O, star (row h) * paperRadialFourier W
      (scale * ‖eisEmbedding h‖ ^ 2 / den)) =
      star (row 0) * paperRadialFourier W 0 +
        ∑' h : O, if h = 0 then 0 else star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / den) := by
  dsimp only
  have hs := activeRow_paperFourier_summable P hgood S T W
    (scale / den) (div_pos hscale hden)
  have heq (h : O) : scale / den * ‖eisEmbedding h‖ ^ 2 =
      scale * ‖eisEmbedding h‖ ^ 2 / den := by ring
  simp_rw [heq] at hs
  simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_div] using hs.tsum_eq_add_tsum_ite 0

noncomputable def squarefreePairPoissonNonzeroMode
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, if h = 0 then 0 else star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))

theorem squarefreePairPoissonKernel_zero_split
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    squarefreePairPoissonKernel P hinj hgood S T W scale =
      squarefreePairPoissonZeroMode P hinj hgood S T W scale +
        squarefreePairPoissonNonzeroMode P hinj hgood S T W scale := by
  unfold squarefreePairPoissonKernel squarefreePairPoissonZeroMode
    squarefreePairPoissonNonzeroMode
  dsimp only
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  have hden : 0 < ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 *
      ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr
      (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))
      (sq_pos_of_pos (norm_pos_iff.mpr
        (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero (activePrimes P S T)))))
  rw [activeRow_paperFourier_zero_split P hgood S T W scale hscale _ hden, mul_add]

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def idealPrimeDensity (F : Finset (Ideal O)) (I : Ideal O) : ℝ :=
  ∏ i ∈ idealSupport F I, (1 - (1 : ℝ) / Ideal.absNorm i.val)

theorem idealPrimeDensity_mem_Icc
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥) (I : Ideal O) :
    idealPrimeDensity F I ∈ Set.Icc (0 : ℝ) 1 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact primeDensity_nonneg_le_one (fun i : primePool F => i.val) (idealSupport F I)

theorem idealPairPoissonZeroMode_diag
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    idealPairPoissonZeroMode F hFpos hFgood I I W scale =
      (scale : ℂ) * paperRadialFourier W 0 * idealPrimeDensity F I := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.val := by
    obtain ⟨J, hJ, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  have heq := squarefreePairPoissonZeroMode_diag_product
    (fun i : primePool F => i.val) hprime Subtype.val_injective
    (primePool_good F hFgood) (idealSupport F I) W scale
  simpa only [idealPairPoissonZeroMode, idealPrimeDensity, Complex.ofReal_prod,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_natCast] using heq

theorem idealRowSum_zeroMode_formula
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale) =
    (scale : ℂ) * paperRadialFourier W 0 *
      ∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
        idealPrimeDensity F I := by
  rw [idealRowSum_zeroMode_diagonal F hFpos hFgood χ A W scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [idealPairPoissonZeroMode_diag]
  ring

noncomputable def idealPairPoissonNonzeroMode
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonNonzeroMode (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem idealPairPoissonKernel_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    idealPairPoissonKernel F hFpos hFgood I J W scale =
      idealPairPoissonZeroMode F hFpos hFgood I J W scale +
        idealPairPoissonNonzeroMode F hFpos hFgood I J W scale := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonKernel_zero_split (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale hscale

theorem idealRowSum_smoothed_poisson_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) =
    (scale : ℂ) * paperRadialFourier W 0 *
      (∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
        idealPrimeDensity F I) +
      ∑ I ∈ F, ∑ J ∈ F,
        (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
          (baseChangeWeight χ J * A (Ideal.absNorm J))) *
        idealPairPoissonNonzeroMode F hFpos hFgood I J W scale := by
  rw [idealRowSum_smoothed_poisson F hFpos hFgood hchar χ A W scale hscale]
  simp_rw [idealPairPoissonKernel_zero_split F hFpos hFgood _ _ W scale hscale,
    mul_add, Finset.sum_add_distrib]
  rw [idealRowSum_zeroMode_formula F hFpos hFgood χ A W scale]

end ConcretePrimeRowBridge

namespace ShortDraftHeckeBridge

theorem norm_baseChangeWeight_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  by_cases hI : Squarefree I
  · simp only [baseChangeWeight, hI.moebius_eq, Int.cast_pow, Int.cast_neg,
      Int.cast_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact χ.norm_le_one _
  · rw [ConcretePrimeRowBridge.baseChangeWeight_eq_zero_of_not_squarefree χ hI, norm_zero]
    exact zero_le_one

end ShortDraftHeckeBridge

namespace ConcretePrimeRowBridge

section
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

theorem norm_idealRowSum_zeroMode_le_test_mass
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale‖ ≤
    (|scale| * ‖paperRadialFourier W 0‖) *
      ∑ I ∈ F, ‖A (Ideal.absNorm I)‖ ^ 2 := by
  refine (norm_idealRowSum_zeroMode_le F hFpos hFgood χ A W scale).trans ?_
  gcongr with I hI
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_baseChangeWeight_le_one χ I)

end

open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_image_eq_factors
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) :
    (idealSupport F I).image Subtype.val =
      (UniqueFactorizationMonoid.normalizedFactors I).toFinset := by
  ext P
  simp only [Finset.mem_image, Multiset.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_idealSupport_iff F I p).mp hp
  · intro hP
    let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨I, hI, hP⟩⟩
    exact ⟨p, (mem_idealSupport_iff F I p).mpr hP, rfl⟩

theorem idealSupport_product_eq
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) (hsI : Squarefree I) :
    (∏ i ∈ idealSupport F I, i.val) = I := by
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    hsI.ne_zero).mp hsI
  calc
    _ = ∏ P ∈ (idealSupport F I).image Subtype.val, P := by
      rw [Finset.prod_image]
      exact fun a ha b hb h => Subtype.val_injective h
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P := by
      rw [idealSupport_image_eq_factors F hI]
    _ = (UniqueFactorizationMonoid.normalizedFactors I).prod := by
      change ((UniqueFactorizationMonoid.normalizedFactors I).toFinset.val.map id).prod = _
      rw [Multiset.map_id, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    _ = I := Ideal.prod_normalizedFactors_eq_self hsI.ne_zero

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic

theorem activeSupport_product_mul_common_sq
    {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (P : ι → M) (S T : Finset ι) :
    (∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i) ^ 2 =
      (∏ i ∈ S, P i) * (∏ i ∈ T, P i) := by
  have hset : activeSupport S T = (S ∪ T) \ (S ∩ T) := by
    ext i
    simp only [activeSupport, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsub : S ∩ T ⊆ S ∪ T := Finset.inter_subset_left.trans Finset.subset_union_left
  calc
    _ = ((∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i)) *
      (∏ i ∈ S ∩ T, P i) := by rw [pow_two, mul_assoc]
    _ = (∏ i ∈ S ∪ T, P i) * (∏ i ∈ S ∩ T, P i) := by
      rw [hset, Finset.prod_sdiff hsub]
    _ = _ := Finset.prod_union_inter

theorem activePrimeModulus_norm_sq
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S T : Finset ι) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ activeSupport S T, P i) : ℝ) := by
  rw [finitePrimeModulus_norm_sq]
  congr 2
  exact Finset.prod_coe_sort (activeSupport S T) P

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_active_conductor_mul_common_sq
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J) :
    (∏ i ∈ activeSupport (idealSupport F I) (idealSupport F J), i.val) *
      (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) ^ 2 = I * J := by
  rw [primeSubsetProduct, activeSupport_product_mul_common_sq,
    idealSupport_product_eq F hI hsI, idealSupport_product_eq F hJ hsJ]

theorem idealPairPoisson_conductor_norm_sq
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus
      (activePrimes (fun i : primePool F => i.val) (idealSupport F I) (idealSupport F J)))‖ ^ 2 *
      (Ideal.absNorm (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) : ℝ) ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [activePrimeModulus_norm_sq]
  have hn := congrArg (fun K : Ideal O => (Ideal.absNorm K : ℝ))
    (idealSupport_active_conductor_mul_common_sq F hI hJ hsI hsJ)
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using hn

theorem idealPairPoisson_conductor_norm_sq_of_weight_ne_zero
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hwI : baseChangeWeight χ I ≠ 0) (hwJ : baseChangeWeight χ J ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus
      (activePrimes (fun i : primePool F => i.val) (idealSupport F I) (idealSupport F J)))‖ ^ 2 *
      (Ideal.absNorm (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) : ℝ) ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  have hsI : Squarefree I := by
    by_contra h
    exact hwI (baseChangeWeight_eq_zero_of_not_squarefree χ h)
  have hsJ : Squarefree J := by
    by_contra h
    exact hwJ (baseChangeWeight_eq_zero_of_not_squarefree χ h)
  exact idealPairPoisson_conductor_norm_sq F hI hJ hsI hsJ

end ConcretePrimeRowBridge

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.CubicTrace -/

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

namespace ActualEisensteinCubic

theorem cubicChar_reduce_ne_one (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q) :
    (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q) ≠ 1 := by
  intro hred
  apply cubicChar_ne_one P hPgood
  apply MulChar.ext
  intro u
  apply cubic_roots_reduce_injective Q hQgood
  · rw [← (cubicChar P hPgood).pow_apply_coe, cubicChar_pow_three]
    exact MulChar.one_apply_coe u
  · simp
  · have h := congrArg (fun χ : MulChar (O ⧸ P) (O ⧸ Q) => χ (u : O ⧸ P)) hred
    simpa only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one] using h

theorem cubicGauss_cube_of_nontrivial {E : Type*} [Field E] (ι : O →+* E)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1)
    (hξ : (cubicChar P hgood).ringHomComp ι ≠ 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hξ3 : ξ ^ 3 = 1 := by
    rw [MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
  have hξ2 : ξ * ξ ≠ 1 := by
    intro h2
    apply hξ
    calc
      ξ = ξ * (ξ * ξ) := by rw [h2, mul_one]
      _ = ξ ^ 3 := by rw [pow_succ, pow_two]; ac_rfl
      _ = 1 := hξ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hξ3
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hξneg : ξ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hξ3
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξ hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary, map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring

theorem cubicGauss_cube_reduce {E : Type*} [Field E]
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1)
    (η : (O ⧸ Q) →+* E) (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hPgood).ringHomComp (η.comp (Ideal.Quotient.mk Q))) ψ ^ 3 =
      -(η (Ideal.Quotient.mk Q p)) * (Nat.card (O ⧸ P) : E) := by
  apply cubicGauss_cube_of_nontrivial _ P hPgood p hP hprimary _ ψ hψ
  have h := (MulChar.ringHomComp_ne_one_iff η.injective).mpr
    (cubicChar_reduce_ne_one P Q hPgood hQgood)
  exact h

end ActualEisensteinCubic

namespace CubicFrobenius

theorem card_cast_ne_zero (F F' : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] (hchar : ringChar F' ≠ ringChar F) :
    (Fintype.card F : F') ≠ 0 := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  rw [hcard, Nat.cast_pow]
  apply pow_ne_zero
  intro hz
  have hd := (CharP.cast_eq_zero_iff F' (ringChar F') (ringChar F)).mp hz
  exact hchar ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F' _) hp).mp hd)

theorem gaussSum_pow_card (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (χ : MulChar F F') (ψ : AddChar F E) :
    gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ Fintype.card F' =
      gaussSum (χ.ringHomComp (algebraMap F' E))
        (ψ.mulShift (Fintype.card F' : F)) := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F' (ringChar F')
  have hchar := Algebra.ringChar_eq F' E
  have hpE : (ringChar E).Prime := hchar ▸ hp
  let : Fact (ringChar E).Prime := ⟨hpE⟩
  have hcardE : Fintype.card F' = ringChar E ^ (n : ℕ) := by simpa only [hchar] using hcard
  unfold gaussSum
  rw [hcardE, sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_pow, ← hcardE]
  change (algebraMap F' E (χ x)) ^ Fintype.card F' * ψ x ^ Fintype.card F' = _
  rw [← map_pow, FiniteField.pow_card, ← AddChar.mulShift_spec']
  rfl

theorem gauss_cube_residue_relation (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (hchar : ringChar F' ≠ ringChar F)
    (χ : MulChar F F') (hχ : χ ≠ 1) (ψ : AddChar F E) (hψ : ψ.IsPrimitive)
    (a : F') (m : ℕ) (hm : Fintype.card F' = 3 * m + 1)
    (hcube : gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ 3 = algebraMap F' E a) :
    χ (Fintype.card F' : F) * a ^ m = 1 := by
  let ξ := χ.ringHomComp (algebraMap F' E)
  have hξ : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (algebraMap F' E).injective).mpr hχ
  have hcard : (Fintype.card F : E) ≠ 0 := by
    rw [← map_natCast (algebraMap F' E)]
    exact (map_ne_zero (algebraMap F' E)).mpr (card_cast_ne_zero F F' hchar)
  have hg : gaussSum ξ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hξ hψ
  have hq : (Fintype.card F' : F) ≠ 0 := card_cast_ne_zero F' F hchar.symm
  let u : Fˣ := (isUnit_iff_ne_zero.mpr hq).unit
  have hu : (u : F) = Fintype.card F' := (isUnit_iff_ne_zero.mpr hq).unit_spec
  have hshift := gaussSum_mulShift ξ ψ u
  rw [hu, ← gaussSum_pow_card F F' E χ ψ] at hshift
  have hp : gaussSum ξ ψ ^ Fintype.card F' =
      algebraMap F' E (a ^ m) * gaussSum ξ ψ := by
    rw [hm, pow_succ, pow_mul, hcube, map_pow]
  rw [hp] at hshift
  have hone : ξ (Fintype.card F' : F) * algebraMap F' E (a ^ m) = 1 := by
    apply mul_right_cancel₀ hg
    simpa only [mul_assoc, one_mul] using hshift
  apply (algebraMap F' E).injective
  simpa only [ξ, map_mul, map_one, MulChar.ringHomComp_apply] using hone

end CubicFrobenius

namespace ActualEisensteinCubic

theorem cubic_primary_frobenius_relation (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O))) = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Field (O ⧸ Q) := Ideal.Quotient.field Q
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fintype (O ⧸ Q) := Fintype.ofFinite _
  let ψ := AddChar.FiniteField.primitiveChar (O ⧸ P) (O ⧸ Q) hchar
  let E := CyclotomicField ψ.n (O ⧸ Q)
  let η : (O ⧸ Q) →+* E := algebraMap (O ⧸ Q) E
  let χ := (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q)
  let a : O ⧸ Q := -(Ideal.Quotient.mk Q p) * (Fintype.card (O ⧸ P) : O ⧸ Q)
  let m := (Fintype.card (O ⧸ Q) - 1) / 3
  have hqdiv : 3 ∣ Fintype.card (O ⧸ Q) - 1 := by
    simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three Q hQgood
  have hqpos : 0 < Fintype.card (O ⧸ Q) := Fintype.card_pos
  have hm : Fintype.card (O ⧸ Q) = 3 * m + 1 := by
    dsimp [m]
    omega
  have hcube : gaussSum (χ.ringHomComp η) ψ.char ^ 3 = η a := by
    have hc := cubicGauss_cube_reduce P Q hPgood hQgood p hP hprimary η ψ.char ψ.prim
    convert hc using 1
    · rfl
    · simp only [a, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card]
  have hrel := CubicFrobenius.gauss_cube_residue_relation (O ⧸ P) (O ⧸ Q) E
    hchar χ (cubicChar_reduce_ne_one P Q hPgood hQgood) ψ.char ψ.prim a m hm hcube
  have heuler := cubicChar_reduce Q hQgood
    (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))
  have heuler' : Ideal.Quotient.mk Q
      (cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = a ^ m := by
    simpa only [a, m, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card] using heuler
  rw [← heuler'] at hrel
  change Ideal.Quotient.mk Q (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) *
    Ideal.Quotient.mk Q (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = 1 at hrel
  have hx : (Fintype.card (O ⧸ Q) : O ⧸ P) ≠ 0 :=
    CubicFrobenius.card_cast_ne_zero (O ⧸ Q) (O ⧸ P) hchar.symm
  have hy : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) ≠ 0 := by
    intro hz
    rw [hz, MulChar.map_zero, map_zero, mul_zero] at hrel
    exact zero_ne_one hrel
  have hxcube : (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  have hycube : (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)
  have hprod : cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O))) = 1 := by
    apply cubic_roots_reduce_injective Q hQgood
    · rw [mul_pow, hxcube, hycube, mul_one]
    · simp
    · simpa only [map_mul, map_one] using hrel
  have hminus : cubicChar Q hQgood (-1 : O ⧸ Q) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (cubicChar_pow_three Q hQgood)
  have hneg : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) =
      (-1) * Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O)) := by
    simp only [map_mul, map_neg, map_natCast]
    ring
  rw [hneg, map_mul, hminus, one_mul] at hprod
  simpa only [Nat.card_eq_fintype_card] using hprod

theorem cubic_reciprocity_distinct_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  have hPQ := cubic_primary_frobenius_relation P Q hPgood hQgood hchar p hP hpprimary
  have hQP := cubic_primary_frobenius_relation Q P hQgood hPgood hchar.symm q hQ hqprimary
  simp only [map_mul, map_natCast] at hPQ hQP
  let U := cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P)
  let V := cubicChar Q hQgood (Nat.card (O ⧸ P) : O ⧸ Q)
  have hB : cubicChar Q hQgood (Ideal.Quotient.mk Q p) * (U * V) = 1 := by
    simpa only [U, V, mul_comm, mul_left_comm, mul_assoc] using hPQ
  have hA : cubicChar P hPgood (Ideal.Quotient.mk P q) * (U * V) = 1 := by
    simpa only [U, V, mul_comm, mul_left_comm, mul_assoc] using hQP
  have hUV : U * V ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hA
    exact zero_ne_one hA
  exact mul_right_cancel₀ hUV (hA.trans hB.symm)

theorem canonicalSextic_sq_reciprocity_distinct_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
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
  rw [hP2, hQ2, cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
    p q hP hQ hpprimary hqprimary]

end ActualEisensteinCubic

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem norm_eisEmbedding_unit (u : Oˣ) : ‖eisEmbedding (u : O)‖ = 1 := by
  have h := eisEmbedding_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (u : O))]

@[simp] theorem norm_eisEmbedding_unit_mul (u : Oˣ) (a : O) :
    ‖eisEmbedding ((u : O) * a)‖ = ‖eisEmbedding a‖ := by
  rw [map_mul, norm_mul, norm_eisEmbedding_unit, one_mul]

theorem finiteSexticRow_unit_mul_star {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (u : Oˣ) :
    finiteSexticRow P hgood j (u : O) * star (finiteSexticRow P hgood j (u : O)) = 1 := by
  unfold finiteSexticRow
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk (P i)))

def principalNormalizedGauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) /
      (‖eisEmbedding c‖ : ℂ)

theorem canonicalNormalizedGauss_eq_principal {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j =
      principalNormalizedGauss P hcop hgood j (finitePrimeModulus P)
        (span_finitePrimeModulus P) (finitePrimeModulus_ne_zero P) := rfl

theorem principal_gauss_sum_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n)
    [Fintype (O ⧸ Ideal.span {c})] [Fintype (O ⧸ Ideal.span {n})] :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) =
      finiteSexticRow P hgood j (u : O) *
        ∑ r : O ⧸ Ideal.span {n}, principalSexticRow P hcop hgood j n hn r *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0 r := by
  let e₀ := Ideal.quotEquivOfEq (hn.trans hc.symm)
  let ū : (O ⧸ Ideal.span {n})ˣ := Units.map (Ideal.Quotient.mk (Ideal.span {n})).toMonoidHom u
  let e : (O ⧸ Ideal.span {n}) ≃ (O ⧸ Ideal.span {c}) := ū.mulLeft.trans e₀.toEquiv
  have he (a : O) : e (Ideal.Quotient.mk (Ideal.span {n}) a) =
      Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a) := by
    change e₀ (Ideal.Quotient.mk (Ideal.span {n}) (u : O) *
      Ideal.Quotient.mk (Ideal.span {n}) a) = _
    rw [← map_mul, Ideal.quotEquivOfEq_mk]
  rw [← Equiv.sum_comp e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [he, principalSexticRow_mk, principalSexticRow_mk, finiteSexticRow_mul]
  have hphase : eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
      (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a)) =
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0
        (Ideal.Quotient.mk (Ideal.span {n}) a) := by
    rw [eisTraceModChar_eq_paperE, eisTraceModChar_eq_paperE, hcn, map_mul, map_mul]
    congr 1
    field_simp [eisEmbedding_ne_zero u.ne_zero]
  rw [hphase]
  ring

theorem principalNormalizedGauss_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n) :
    principalNormalizedGauss P hcop hgood j c hc hc0 =
      finiteSexticRow P hgood j (u : O) *
        principalNormalizedGauss P hcop hgood j n hn hn0 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {n}) := finite_quotient_span hn0
  let : Fintype (O ⧸ Ideal.span {n}) := Fintype.ofFinite _
  unfold principalNormalizedGauss
  rw [principal_gauss_sum_unit_change P hcop hgood j c n hc hn hc0 hn0 u hcn]
  rw [hcn, norm_eisEmbedding_unit_mul]
  ring

theorem principalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    principalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j (∏ i, p i)
      (span_finset_prod Finset.univ p) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) =
      canonicalProductGauss p hp hcop hgood j := rfl

theorem exists_modulus_unit {ι : Type*} [Fintype ι] (p : ι → O) :
    ∃ u : Oˣ, finitePrimeModulus (fun i => Ideal.span {p i}) = (u : O) * ∏ i, p i := by
  have hs : Ideal.span {∏ i, p i} =
      Ideal.span {finitePrimeModulus (fun i => Ideal.span {p i})} := by
    rw [span_finitePrimeModulus, span_finset_prod]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def modulusUnit {ι : Type*} [Fintype ι] (p : ι → O) : Oˣ :=
  Classical.choose (exists_modulus_unit p)

theorem modulusUnit_spec {ι : Type*} [Fintype ι] (p : ι → O) :
    finitePrimeModulus (fun i => Ideal.span {p i}) = (modulusUnit p : O) * ∏ i, p i :=
  Classical.choose_spec (exists_modulus_unit p)

theorem canonicalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j =
      finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
        canonicalProductGauss p hp hcop hgood j := by
  rw [canonicalNormalizedGauss_eq_principal,
    principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hgood j
      (finitePrimeModulus (fun i => Ideal.span {p i})) (∏ i, p i)
      (span_finitePrimeModulus _) (span_finset_prod Finset.univ p)
      (finitePrimeModulus_ne_zero _) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      (modulusUnit p) (modulusUnit_spec p), principalNormalizedGauss_eq_product]

theorem canonicalNormalizedGauss_frequency_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (h : O) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j ((modulusUnit p : O) * h)) =
      canonicalProductGauss p hp hcop hgood j *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood j,
    finiteSexticRow_mul, star_mul]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O))) *
        (canonicalProductGauss p hp hcop hgood j *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h)) := by ring
    _ = _ := by rw [finiteSexticRow_unit_mul_star, one_mul]

theorem gauss_weighted_radial_sum_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
        F (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F (‖eisEmbedding h‖ ^ 2)) := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  calc
    _ = ∑' h : O, canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        (star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j
          ((modulusUnit p : O) * h)) * F (‖eisEmbedding ((modulusUnit p : O) * h)‖ ^ 2)) :=
      ((modulusUnit p).mulLeft.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro h
      rw [norm_eisEmbedding_unit_mul, ← mul_assoc,
        canonicalNormalizedGauss_frequency_transport p hp hcop hgood j, mul_assoc]

theorem gauss_weighted_finite_radial_sum_transport {ι κ : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (D : Finset κ) (a : κ → ℂ) (F : κ → ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑ k ∈ D, a k * ∑' h : O,
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑ k ∈ D, a k * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            F k (‖eisEmbedding h‖ ^ 2)) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = a k * (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [gauss_weighted_radial_sum_transport p hp hcop hgood j]; ring

theorem finitePrimeModulus_norm_eq_product {ι : Type*} [Fintype ι] (p : ι → O) :
    ‖eisEmbedding (finitePrimeModulus (fun i => Ideal.span {p i}))‖ =
      ‖eisEmbedding (∏ i, p i)‖ := by
  rw [modulusUnit_spec p, norm_eisEmbedding_unit_mul]

theorem canonical_radial_poisson_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, finiteSexticRow (fun i => Ideal.span {p i}) hgood j z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalProductGauss p hp hcop hgood j /
        (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, p i)‖ ^ 2) := by
  have h := canonical_radial_poisson_normalized (fun i => Ideal.span {p i})
    hcop hgood hchar j hj0 hj6 W scale hscale
  dsimp only at h
  rw [finitePrimeModulus_norm_eq_product p] at h
  rw [h]
  have ht := gauss_weighted_radial_sum_transport p hp hcop hgood j
    (fun t => paperRadialFourier W (scale * t / ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
          ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            paperRadialFourier W
              (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by ring
    _ = _ := by rw [ht]; ring

theorem moebius_star_canonicalNormalizedGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      star (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood (fun _ => 1)) =
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) (modulusUnit p : O)) *
        ((canonicalProductG p hp hcop hgood)⁻¹ * canonicalProductCoefficient p hp hcop hgood) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood (fun _ => 1), star_mul]
  calc
    _ = star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) (modulusUnit p : O)) *
        ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
          star (canonicalProductGauss p hp hcop hgood (fun _ => 1))) := by ring
    _ = _ := by rw [moebius_star_gauss_one_eq_coefficient p hp hcop hgood hchar hprimary]

theorem moebius_gauss_frequency_conversion {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (h : O) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood (fun _ => 1) *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1)
          ((modulusUnit p : O) * h))) =
      (star (canonicalProductG p hp hcop hgood))⁻¹ *
        star (canonicalProductCoefficient p hp hcop hgood) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) h) := by
  rw [canonicalNormalizedGauss_frequency_transport p hp hcop hgood (fun _ => 1)]
  have hc := congrArg (fun z : ℂ => star z)
    (moebius_star_gauss_one_eq_coefficient p hp hcop hgood hchar hprimary)
  simp only [star_mul, star_star, star_inv₀, star_intCast] at hc
  calc
    _ = (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
        (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ)) *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) h) := by ring
    _ = _ := by rw [hc]; ring

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

def squarefreePairProductPoissonKernel
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let q : activeSupport S T → O := fun i => p i.val
  let Q := activePrimes (fun i => Ideal.span {p i}) S T
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let n := ∏ i, q i
  ((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ
      (fun i => hgood i.val) (activeExponent S T) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem squarefreePairPoissonKernel_eq_product
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonKernel (fun i => Ideal.span {p i}) hinj hgood S T W scale =
      squarefreePairProductPoissonKernel p hp hinj hgood S T W scale := by
  let q : activeSupport S T → O := fun i => p i.val
  let Q := activePrimes (fun i => Ideal.span {p i}) S T
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  let hg : ∀ i : activeSupport S T, lambda ∉ Q i := fun i => hgood i.val
  let j := activeExponent S T
  let row := finiteSexticRow Q hg j
  let n := ∏ i, q i
  let a : Finset ι → ℂ := fun E =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)
  let F : Finset ι → ℝ → ℂ := fun E t =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    paperRadialFourier W (scale * t / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  have hc : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    finitePrimeModulus_norm_eq_product q
  unfold squarefreePairPoissonKernel squarefreePairProductPoissonKernel
  dsimp only
  change ((scale : ℂ) * canonicalNormalizedGauss Q hQ hg j /
      (‖eisEmbedding (finitePrimeModulus Q)‖ : ℂ)) * _ = _
  rw [hc]
  change ((scale : ℂ) * canonicalNormalizedGauss Q hQ hg j / (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2)) =
    ((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ hg j /
      (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2))
  have ht := gauss_weighted_finite_radial_sum_transport q (fun i => hp i.val)
    hQ hg j (S ∩ T).powerset a F
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ hg j *
          (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2))) := by ring
    _ = _ := by rw [ht]; ring

theorem finiteSquarefreeRow_pair_radial_poisson_product
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood S z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood T z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      squarefreePairProductPoissonKernel p hp hinj hgood S T W scale := by
  rw [finiteSquarefreeRow_pair_radial_poisson (fun i => Ideal.span {p i}) hinj hgood hchar
    S T W scale hscale, squarefreePairPoissonKernel_eq_product p hp hinj hgood]

end GaussGeneratorTransport

end

end OAI

end

