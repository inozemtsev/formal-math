module

public import Green64.Library.OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Arithmetic / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius -/

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

namespace IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

def idealDivisors (I : Ideal O) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) (Ideal.absNorm I)).toFinset.filter
    (fun J => J ∣ I)

theorem mem_idealDivisors {I J : Ideal O} (hI : I ≠ ⊥) :
    J ∈ idealDivisors I ↔ J ∣ I := by
  simp only [idealDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro hJI
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI), hJI⟩

def primeSupport (I : Ideal O) : Finset (Ideal O) := (normalizedFactors I).toFinset

theorem support_prime {I : Ideal O} {P : Ideal O} (hP : P ∈ primeSupport I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _P hP => (support_prime (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => support_prime (hS hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem squarefree_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : Squarefree (∏ P ∈ S, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hS)).mpr
  rw [factors_support_product hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal O} (hI : I ≠ ⊥) {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (support_product_ne_zero hS) hI).mpr
  rw [factors_support_product hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem moebius_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) :
    (moebius (∏ P ∈ S, P) : ℂ) = (-1 : ℂ) ^ S.card := by
  rw [(squarefree_support_product hS).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hS]
  simp

theorem support_product_injective {I : Ideal O}
    {S T : Finset (Ideal O)} (hS : S ⊆ primeSupport I) (hT : T ⊆ primeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal O} (hI : I ≠ ⊥)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport J ⊆ primeSupport I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_support_product_self {J : Ideal O} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport J, P) = J := by
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport J).val = normalizedFactors J := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).filter Squarefree =
      (primeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  ext J
  simp only [Finset.mem_filter, mem_idealDivisors hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨primeSupport J, squarefree_divisor_support hI hJ hJI,
      squarefree_support_product_self hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨support_product_dvd hI hS, squarefree_support_product hS⟩

theorem primeSupport_empty_iff (I : Ideal O) (hI : I ≠ ⊥) :
    primeSupport I = ∅ ↔ I = ⊤ := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := by
      apply Multiset.toFinset_eq_empty.mp
      exact h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    simpa only [Ideal.one_eq_top] using hp.symm
  · intro h
    subst I
    simp [primeSupport, ← Ideal.one_eq_top]

theorem sum_moebius_divisors (I : Ideal O) (hI : I ≠ ⊥) :
    (∑ J ∈ idealDivisors I, (moebius J : ℂ)) = if I = ⊤ then 1 else 0 := by
  have hfilter : (∑ J ∈ idealDivisors I, (moebius J : ℂ)) =
      ∑ J ∈ (idealDivisors I).filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa [hJ] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  · have heq : (∑ S ∈ (primeSupport I).powerset, (moebius (∏ P ∈ S, P) : ℂ)) =
        ∑ S ∈ (primeSupport I).powerset, (-1 : ℂ) ^ S.card := by
      exact Finset.sum_congr rfl (fun S hS => moebius_support_product (Finset.mem_powerset.mp hS))
    rw [heq, CoprimeMobiusExtension.sum_subset_sign]
    simp only [primeSupport_empty_iff I hI]
  · intro S hS T hT hST
    exact support_product_injective (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

end IdealMobiusDivisorSum

open scoped BigOperators Classical

namespace CompletedGauss

section

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic

def primaryPrime (P : Ideal O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    (cubicJacobi_exists_primary_generator P h.2).choose
  else 0

theorem primaryPrime_spec (P : Ideal O) (h : primaryPrime P ≠ 0) :
    P.IsMaximal ∧ lambda ∉ P ∧
      Ideal.span {primaryPrime P} = P ∧ lambda ^ 2 ∣ primaryPrime P - 1 := by
  classical
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    have hs := (cubicJacobi_exists_primary_generator P hg.2).choose_spec
    simpa only [primaryPrime, dite_eq_left hg] using ⟨hg.1, hg.2, hs.1.symm, hs.2.1⟩
  · simp only [primaryPrime, dite_eq_right hg, ne_eq, not_true_eq_false] at h

theorem primaryPrime_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) :
    primaryPrime P ≠ 0 := by
  classical
  have hs := (cubicJacobi_exists_primary_generator P hg).choose_spec
  have htest : P.IsMaximal ∧ lambda ∉ P := ⟨inferInstance, hg⟩
  intro hz
  have hp0 : (cubicJacobi_exists_primary_generator P hg).choose = 0 := by
    simpa only [primaryPrime, dite_eq_left htest] using hz
  rw [hp0] at hs
  exact (NeZero.ne P) (by simpa using hs.1)

def primaryGenerator (I : Ideal O) : O :=
  if I = 0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map primaryPrime).prod

@[simp] theorem primaryGenerator_zero : primaryGenerator 0 = 0 := by rw [primaryGenerator, ite_eq_left rfl]

@[simp] theorem primaryGenerator_bot : primaryGenerator ⊥ = 0 := primaryGenerator_zero

@[simp] theorem primaryGenerator_one : primaryGenerator 1 = 1 := by
  rw [primaryGenerator, ite_eq_right one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl

theorem primaryGenerator_mul (I J : Ideal O) :
    primaryGenerator (I * J) = primaryGenerator I * primaryGenerator J := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [primaryGenerator, ite_eq_right hI, ite_eq_right hJ, ite_eq_right (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

def primaryGeneratorHom : Ideal O →*₀ O where
  toFun := primaryGenerator
  map_zero' := primaryGenerator_zero
  map_one' := primaryGenerator_one
  map_mul' := primaryGenerator_mul

theorem primaryGenerator_ne_zero_ideal (I : Ideal O) (h : primaryGenerator I ≠ 0) : I ≠ 0 := by
  intro hI
  exact h (by simp [hI])

theorem primaryPrime_factor_ne_zero (I P : Ideal O) (hI : primaryGenerator I ≠ 0)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) : primaryPrime P ≠ 0 := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hprod : ((UniqueFactorizationMonoid.normalizedFactors I).map primaryPrime).prod ≠ 0 := by
    simpa only [primaryGenerator, ite_eq_right hI0] using hI
  intro hz
  exact hprod (Multiset.prod_eq_zero_iff.mpr (Multiset.mem_map.mpr ⟨P, hP, hz⟩))

theorem span_multiset_prod (s : Multiset O) :
    Ideal.span {s.prod} = (s.map (fun x => Ideal.span {x})).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.prod_cons, Multiset.map_cons,
      ← Ideal.span_singleton_mul_span_singleton, ih]

theorem primaryGenerator_spec (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    Ideal.span {primaryGenerator I} = I ∧ lambda ^ 2 ∣ primaryGenerator I - 1 := by
  classical
  have hI0 := primaryGenerator_ne_zero_ideal I h
  have hprime : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Ideal.span {primaryPrime P} = P ∧ lambda ^ 2 ∣ primaryPrime P - 1 := by
    intro P hP
    exact (primaryPrime_spec P (primaryPrime_factor_ne_zero I P h hP)).2.2
  rw [primaryGenerator, ite_eq_right hI0]
  constructor
  · rw [span_multiset_prod, Multiset.map_map]
    have hm : (UniqueFactorizationMonoid.normalizedFactors I).map
        ((fun x => Ideal.span {x}) ∘ primaryPrime) =
        UniqueFactorizationMonoid.normalizedFactors I := by
      calc
        _ = (UniqueFactorizationMonoid.normalizedFactors I).map id :=
          Multiset.map_congr rfl (fun P hP => (hprime P hP).1)
        _ = _ := Multiset.map_id' _
    rw [hm]
    exact Ideal.prod_normalizedFactors_eq_self hI0
  · apply primary_multiset_prod
    intro r hr
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hr
    exact (hprime P hP).2

theorem primaryGenerator_span (n : O) (hn : n ≠ 0)
    (hprimary : lambda ^ 2 ∣ n - 1) : primaryGenerator (Ideal.span {n}) = n := by
  classical
  have hI0 : (Ideal.span {n} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hn
  have hgen : primaryGenerator (Ideal.span {n}) ≠ 0 := by
    rw [primaryGenerator, ite_eq_right hI0]
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨P, hP, hz⟩ := Multiset.mem_map.mp hzero
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
    have hnP : n ∈ P := hle (Ideal.subset_span (by simp))
    exact primaryPrime_ne_zero P (primary_maximal_divisor_good n hprimary P hnP) hz
  have hspec := primaryGenerator_spec (Ideal.span {n}) hgen
  exact primary_associated_eq _ _ (Ideal.span_singleton_eq_span_singleton.mp hspec.1)
    hspec.2 hprimary

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

open ActualEisensteinCubic

theorem compact_window_bound (W : ℝ → ℂ) (hW : HasCompactSupport W) :
    ∃ B : ℝ, 0 < B ∧ ∀ y, W y ≠ 0 → y ≤ B := by
  obtain ⟨B, hB⟩ := hW.bddAbove
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  exact (hB (subset_tsupport W hy)).trans (le_max_left _ _)

theorem norm_at_least_one (I : Ideal O) (hI : I ≠ 0) :
    (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_scale_bounds (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b ^ 3 * c ^ 3 ∧ b ≤ a * b ^ 3 * c ^ 3 ∧ c ≤ a * b ^ 3 * c ^ 3 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hc3 : 1 ≤ c ^ 3 := one_le_pow₀ hc
  constructor
  · calc a = a * 1 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  constructor
  · calc b ≤ b ^ 3 := le_self_pow₀ hb (by decide)
         _ = 1 * b ^ 3 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  · calc c ≤ c ^ 3 := le_self_pow₀ hc (by decide)
         _ = 1 * 1 * c ^ 3 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr

theorem finite_support_norm_triple (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (F : Ideal O × Ideal O × Ideal O → ℂ)
    (hzero : ∀ I J H, I = 0 ∨ J = 0 ∨ H = 0 → F (I, J, H) = 0)
    (hwindow : ∀ I J H,
      W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
        (Ideal.absNorm H : ℝ) ^ 3 / X) = 0 → F (I, J, H) = 0) :
    (Function.support F).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * X)
  let S := {I : Ideal O | Ideal.absNorm I ≤ M}
  have hS : S.Finite := Ideal.finite_setOfPred_absNorm_le M
  apply (hS.prod (hS.prod hS)).subset
  rintro ⟨I, J, H⟩ hF
  have hF0 : F (I, J, H) ≠ 0 := hF
  have hI : I ≠ 0 := fun h => hF0 (hzero I J H (Or.inl h))
  have hJ : J ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inl h)))
  have hH : H ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inr h)))
  have hw : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
      (Ideal.absNorm H : ℝ) ^ 3 / X) ≠ 0 := fun h => hF0 (hwindow I J H h)
  have hsize := (div_le_iff₀ hX).mp (hbound _ hw)
  have hb := triple_scale_bounds _ _ _ (norm_at_least_one I hI)
    (norm_at_least_one J hJ) (norm_at_least_one H hH)
  have hIM : Ideal.absNorm I ≤ M := by exact_mod_cast (hb.1.trans hsize).trans hM.le
  have hJM : Ideal.absNorm J ≤ M := by exact_mod_cast (hb.2.1.trans hsize).trans hM.le
  have hHM : Ideal.absNorm H ≤ M := by exact_mod_cast (hb.2.2.trans hsize).trans hM.le
  exact ⟨hIM, hJM, hHM⟩

end
section

open ActualEisensteinCubic ConcreteTraceCRT

def primeSupport (I : Ideal O) : Finset (Ideal O) :=
  (UniqueFactorizationMonoid.normalizedFactors I).toFinset

abbrev PrimeIndex (I : Ideal O) := {P : Ideal O // P ∈ primeSupport I}

instance primeIndexMaximal (I : Ideal O) (P : PrimeIndex I) : P.val.IsMaximal := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp P.property)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primeIndex_good (I : Ideal O) (hI : primaryGenerator I ≠ 0) (P : PrimeIndex I) :
    lambda ∉ P.val :=
  (primaryPrime_spec P.val (primaryPrime_factor_ne_zero I P.val hI
    (Multiset.mem_toFinset.mp P.property))).2.1

theorem primeIndex_le (I : Ideal O) (hI : I ≠ 0) (P : PrimeIndex I) : I ≤ P.val :=
  ((Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp P.property)).2

def cubicRow (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O ⧸ I) : ℂ :=
  ∏ P : PrimeIndex I,
    (canonicalSextic P.val (primeIndex_good I hI P) ^ 2)
      (Ideal.Quotient.factor (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI) P) x)

def gaussTwo (I : Ideal O) (hI : primaryGenerator I ≠ 0) : ℂ := by
  let n := primaryGenerator I
  letI : Finite (O ⧸ Ideal.span {n}) := finite_quotient_span hI
  letI : Fintype (O ⧸ Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  exact (∑ x : O ⧸ Ideal.span {n}, cubicRow I hI (e x) * ψ x) / (‖eisEmbedding n‖ : ℂ)

def squarefreeGaussCoefficient (I : Ideal O) : ℂ :=
  if h : Squarefree I ∧ primaryGenerator I ≠ 0 then
    star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I h.2
  else 0

@[simp] theorem squarefreeGaussCoefficient_zero : squarefreeGaussCoefficient 0 = 0 := by
  simp [squarefreeGaussCoefficient]

@[simp] theorem squarefreeGaussCoefficient_bot : squarefreeGaussCoefficient ⊥ = 0 :=
  squarefreeGaussCoefficient_zero

theorem squarefreeGaussCoefficient_eq (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    squarefreeGaussCoefficient I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I hI := by
  rw [squarefreeGaussCoefficient, dite_eq_left ⟨hs, hI⟩]

theorem angularFactor_mul (a b : O) :
    FiniteGaussPhase.angularFactor (a * b) =
      FiniteGaussPhase.angularFactor a * FiniteGaussPhase.angularFactor b := by
  simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul]
  ring

def cubeWeight (Ψ : O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (FiniteGaussPhase.angularFactor (primaryGenerator I)) ^ 3 *
    Ψ (primaryGenerator I) ^ 3 / (Ideal.absNorm I : ℂ)
  map_one' := by
    simp only [primaryGenerator_one, FiniteGaussPhase.angularFactor, map_one,
      norm_one, Complex.ofReal_one, div_one, star_one, one_pow, one_mul, Nat.cast_one]
  map_mul' I J := by
    simp only [primaryGenerator_mul, angularFactor_mul, map_mul, star_mul, mul_pow, Nat.cast_mul]
    ring

@[simp] theorem cubeWeight_zero (Ψ : O →* ℂ) : cubeWeight Ψ 0 = 0 := by
  simp [cubeWeight, FiniteGaussPhase.angularFactor]

@[simp] theorem cubeWeight_bot (Ψ : O →* ℂ) : cubeWeight Ψ ⊥ = 0 := cubeWeight_zero Ψ

def columnWeight (Ψ : O →* ℂ) (I : Ideal O) : ℂ :=
  squarefreeGaussCoefficient I * Ψ (primaryGenerator I)

@[simp] theorem columnWeight_zero (Ψ : O →* ℂ) : columnWeight Ψ 0 = 0 := by
  simp [columnWeight]

@[simp] theorem columnWeight_bot (Ψ : O →* ℂ) : columnWeight Ψ ⊥ = 0 := columnWeight_zero Ψ

def Vstar (W : ℝ → ℂ) (y : ℝ) : ℂ := (Real.sqrt y : ℂ) * W y

def summand (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) * cubeWeight Ψ J *
    Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X)

def completedT (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, ∑' J : Ideal O, summand Ψ W X I J

theorem summand_zero_left (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (J : Ideal O) :
    summand Ψ W X 0 J = 0 := by simp [summand]

theorem summand_zero_right (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I : Ideal O) :
    summand Ψ W X I 0 = 0 := by simp [summand]

theorem summand_zero_window (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O)
    (h : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X) = 0) :
    summand Ψ W X I J = 0 := by simp [summand, Vstar, h]

theorem cubicRow_mk (I : Ideal O) (hI : primaryGenerator I ≠ 0) (a : O) :
    cubicRow I hI (Ideal.Quotient.mk I a) =
      ∏ P : PrimeIndex I, (canonicalSextic P.val (primeIndex_good I hI P) ^ 2)
        (Ideal.Quotient.mk P.val a) := by
  simp only [cubicRow, Ideal.Quotient.factor_mk]

theorem cubicRow_zero_iff (I : Ideal O) (hI : primaryGenerator I ≠ 0) (a : O) :
    cubicRow I hI (Ideal.Quotient.mk I a) = 0 ↔
      ∃ P ∈ primeSupport I, a ∈ P := by
  rw [cubicRow_mk, Finset.prod_eq_zero_iff]
  have hlocal (P : PrimeIndex I) :
      (canonicalSextic P.val (primeIndex_good I hI P) ^ 2) (Ideal.Quotient.mk P.val a) = 0 ↔ a ∈ P.val := by
    let : Field (O ⧸ P.val) := Ideal.Quotient.field P.val
    rw [MulChar.apply_eq_zero_iff]
    simp only [isUnit_iff_ne_zero, not_not, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · rintro ⟨P, _, hP⟩
    exact ⟨P.val, P.property, (hlocal P).mp hP⟩
  · rintro ⟨P, hP, ha⟩
    exact ⟨⟨P, hP⟩, Finset.mem_univ _, (hlocal ⟨P, hP⟩).mpr ha⟩

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem cubeWeight_span (Ψ : O →* ℂ) (n : O) (hn : n ≠ 0)
    (hp : lambda ^ 2 ∣ n - 1) :
    cubeWeight Ψ (Ideal.span {n}) =
      star (FiniteGaussPhase.angularFactor n) ^ 3 * Ψ n ^ 3 /
        (ShortDraftLatticeCount.qNat n : ℂ) := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator (Ideal.span {n}))) ^ 3 *
    Ψ (primaryGenerator (Ideal.span {n})) ^ 3 / (Ideal.absNorm (Ideal.span {n}) : ℂ) = _
  rw [primaryGenerator_span n hn hp, qNat_eq_absNorm_span]

theorem columnWeight_eq (Ψ : O →* ℂ) (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    columnWeight Ψ I = star (FiniteGaussPhase.angularFactor (primaryGenerator I)) *
      gaussTwo I hI * Ψ (primaryGenerator I) := by
  rw [columnWeight, squarefreeGaussCoefficient_eq I hs hI]

theorem columnWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : columnWeight Ψ I = 0 := by
  simp only [columnWeight, h, mul_zero]

theorem cubeWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : cubeWeight Ψ I = 0 := by
  change _ * Ψ (primaryGenerator I) ^ 3 / _ = 0
  rw [h, zero_pow (by decide), mul_zero, zero_div]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

def MulFiber (B : Ideal O) := {p : Ideal O × Ideal O // p.1 * p.2 = B}

def mulFiberDivisorEquiv (B : Ideal O) (hB : B ≠ 0) :
    MulFiber B ≃ {D : Ideal O // D ∈ idealDivisors B} := by
  let f : MulFiber B → {D : Ideal O // D ∈ idealDivisors B} :=
    fun p => ⟨p.val.1, (mem_idealDivisors hB).mpr ⟨p.val.2, p.property.symm⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext hfst
    have hn : p.val.1 ≠ 0 := by
      intro hz
      have he := p.property
      rw [hz, zero_mul] at he
      exact hB he.symm
    apply mul_left_cancel₀ hn
    rw [p.property, hfst, q.property]
  · intro D
    obtain ⟨J, hJ⟩ := (mem_idealDivisors hB).mp D.property
    exact ⟨⟨(D.val, J), hJ.symm⟩, rfl⟩

theorem mulFiber_moebius_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) =
      if B = 1 then 1 else 0 := by
  let e := mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B},
        (UniqueFactorizationMonoid.moebius D.val : ℂ) := by
      exact e.tsum_eq (fun D => (UniqueFactorizationMonoid.moebius D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (UniqueFactorizationMonoid.moebius D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun D => Iff.rfl)
        (fun D => (UniqueFactorizationMonoid.moebius D : ℂ))).symm
    _ = if B = 1 then 1 else 0 := by
      simpa only [Ideal.one_eq_top] using sum_moebius_divisors B hB

theorem ideal_cube_convolution (c : Ideal O →* ℂ) (hc0 : c 0 = 0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2))).Finite) :
    (∑' H : Ideal O, ∑' J : Ideal O,
      (UniqueFactorizationMonoid.moebius H : ℂ) * c (H * J) * f (H * J)) = f 1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2)
  have hF : Summable F := summable_of_hasFiniteSupport hfinite
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.val) =
      if B = 1 then f 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have heach : ∀ p : MulFiber 0, F p.val = 0 := by
        intro p
        dsimp [F]
        rw [p.property, hc0, mul_zero, zero_mul]
      simp only [heach, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = ∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) * (c B * f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property, mul_assoc]
        _ = (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) * (c B * f B) := by
          rw [tsum_mul_right]
        _ = if B = 1 then f 1 else 0 := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with h
          · subst B; simp only [map_one, one_mul]
          · simp
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.val) (∑' p, F p) at hs
  simp_rw [hfiber] at hs
  have hsum : (∑' p, F p) = f 1 := by
    have he := hs.tsum_eq.symm
    simpa only [tsum_ite_eq, one_ne_zero] using he
  rw [← hF.tsum_prod]
  exact hsum

end CompletedGauss

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion -/

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

open scoped BigOperators Classical

namespace CompletedGauss

open ActualEisensteinCubic

def expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X))

theorem finite_support_expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O × Ideal O =>
      expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite := by
  apply finite_support_norm_triple W hW X hX
  · intro I H J hz
    rcases hz with rfl | rfl | rfl <;> simp [expandedTerm]
  · intro I H J hw
    simp [expandedTerm, Vstar, hw]

theorem expandedTerm_scale (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J = expandedTerm Ψ W X I H J := by
  have harg : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 /
      (X / (Ideal.absNorm H : ℝ) ^ 3) =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X := by
    rw [div_div_eq_mul_div]
    ring
  simp only [summand, expandedTerm, harg, map_mul]
  ring

theorem expandedTerm_one (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) :
    expandedTerm Ψ W X I 1 J = summand Ψ W X I J := by
  simp only [expandedTerm, summand, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    one_mul, map_one, Nat.cast_one, one_pow, mul_one]
  ring

theorem completedT_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2)).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hinj : Function.Injective (fun p : Ideal O × Ideal O => (p.1, (1 : Ideal O), p.2)) := by
    intro a b hab
    exact Prod.ext (Prod.mk.inj hab).1 (Prod.mk.inj (Prod.mk.inj hab).2).2
  have hp := Set.Finite.preimage hinj.injOn hf
  change (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X p.1 1 p.2)).Finite at hp
  simpa only [expandedTerm_one] using hp

theorem completedT_summable (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2) :=
  summable_of_hasFiniteSupport (completedT_finite_support Ψ W hW X hX)

theorem weighted_completedT_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (H : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) =
      ∑' I : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
  simp only [completedT, ← tsum_mul_left, expandedTerm_scale]

theorem cube_inverse_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun H : Ideal O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3))).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, expandedTerm Ψ W X I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_completedT_reopen]
  simp only [hzero, tsum_zero]

theorem cube_inner_inverse (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    (∑' H : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J) =
      columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X) := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        expandedTerm Ψ W X I H J := by
    simp only [f, expandedTerm, map_mul, Nat.cast_mul, mul_pow, mul_assoc]
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hp : (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I, p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O =>
        expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem completed_cube_inverse_vstar (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (∑' H : Ideal O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3)) =
    ∑' I : Ideal O, columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p => expandedTerm Ψ W X p.1 p.2.1 p.2.2
  have hF : Summable F := summable_of_hasFiniteSupport (finite_support_expandedTerm Ψ W hW X hX)
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O, ∑' I : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
      simp only [completedT, ← tsum_mul_left, expandedTerm_scale]
    _ = ∑' p : Ideal O × Ideal O × Ideal O, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O, F p := e.tsum_eq F
    _ = ∑' I : Ideal O, ∑' H : Ideal O, ∑' J : Ideal O, expandedTerm Ψ W X I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (cube_inner_inverse Ψ W hW X hX)

theorem vstar_source_normalization (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) =
      (Real.sqrt X : ℂ)⁻¹ * columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X) := by
  by_cases hI : I = 0
  · subst I; simp
  have hN : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)
  have hsN : (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hN).ne'
  have hsX : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hX).ne'
  rw [Vstar, Real.sqrt_div hN.le, Complex.ofReal_div]
  field_simp

theorem completed_cube_inverse (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal O, columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal O, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      completedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) := by
  rw [completed_cube_inverse_vstar Ψ W hW X hX, ← tsum_mul_left]
  apply tsum_congr
  intro I
  simpa only [mul_assoc] using (vstar_source_normalization Ψ W X hX I).symm

open ActualEisensteinCubic ConcreteTraceCRT

theorem normalizedFactors_product {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] :
    UniqueFactorizationMonoid.normalizedFactors (Ideal.span {∏ i, p i}) =
      Finset.univ.val.map (fun i => Ideal.span {p i}) := by
  have hp (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    (m := Finset.univ.val.map (fun i => Ideal.span {p i})) (by
      intro P hP
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hP
      exact hp i)
  rw [FiniteGaussPhase.span_finset_prod]
  exact h

theorem product_primary {ι : Type*} [Fintype ι] (p : ι → O)
    (hp : ∀ i, lambda ^ 2 ∣ p i - 1) : lambda ^ 2 ∣ (∏ i, p i) - 1 := by
  apply primary_multiset_prod (Finset.univ.val.map p)
  intro r hr
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
  exact hp i

def productPrimeIndexEquiv {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    ι ≃ PrimeIndex (Ideal.span {∏ i, p i}) := by
  have hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal O)) := by
    intro i j hij
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hij, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
  have hmem (i : ι) : (Ideal.span {p i} : Ideal O) ∈ primeSupport (Ideal.span {∏ i, p i}) := by
    rw [primeSupport, normalizedFactors_product]
    exact Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let f : ι → PrimeIndex (Ideal.span {∏ i, p i}) := fun i => ⟨Ideal.span {p i}, hmem i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact hinj (congrArg Subtype.val hij)
  · intro P
    have hm := Multiset.mem_toFinset.mp P.property
    rw [normalizedFactors_product] at hm
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hm
    exact ⟨i, Subtype.ext hi⟩

theorem cubicRow_product_mk {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) (a : O) :
    cubicRow (Ideal.span {∏ i, p i}) hI (Ideal.Quotient.mk (Ideal.span {∏ i, p i}) a) =
      ∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (Ideal.Quotient.mk (Ideal.span {p i}) a) := by
  rw [cubicRow_mk]
  symm
  exact (productPrimeIndexEquiv p hcop).prod_comp (fun P =>
    (canonicalSextic P.val (primeIndex_good _ hI P) ^ 2) (Ideal.Quotient.mk P.val a))

theorem gaussTwo_eq_canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) :
    gaussTwo (Ideal.span {∏ i, p i}) hI =
      FiniteGaussPhase.canonicalProductGauss p hp hcop hgood (fun _ => 2) := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := finite_quotient_span hI
  let : Fintype (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec (Ideal.span {∏ i, p i}) hI).1
  have hsum :
      (∑ x : O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})},
        cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (primaryGenerator (Ideal.span {∏ i, p i})) hI x) =
      (∑ x : O ⧸ Ideal.span {∏ i, p i},
        (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
          (FiniteGaussPhase.productElementCRT p hcop x i)) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (∏ i, p i) hpall x) := by
    apply Fintype.sum_equiv e.toEquiv
    intro x
    change cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (primaryGenerator (Ideal.span {∏ i, p i})) hI x =
      (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (FiniteGaussPhase.productElementCRT p hcop (e x) i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) hpall (e x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [e, Ideal.quotEquivOfEq_mk, cubicRow_product_mk p hcop hgood hI,
      FiniteGaussPhase.productElementCRT_mk, eisTraceModChar, IdealGaussCRT.traceModChar_mk, hgen]
  change _ / _ = _ / _
  rw [hsum, hgen]

theorem squarefreeGaussCoefficient_eq_canonicalProductCoefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    squarefreeGaussCoefficient (Ideal.span {∏ i, p i}) =
      FiniteGaussPhase.canonicalProductCoefficient p hp hcop hgood := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  have hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0 := by rwa [hgen]
  have hsq : Squarefree (Ideal.span {∏ i, p i}) := by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (Ideal.span_singleton_eq_bot.not.mpr hpall)).mpr
    rw [normalizedFactors_product]
    apply Multiset.Nodup.map
    · intro i j hij
      by_contra hne
      have ht := (hcop hne).sup_eq
      rw [hij, sup_idem] at ht
      exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
    · exact Finset.univ.nodup
  rw [squarefreeGaussCoefficient_eq _ hsq hI,
    gaussTwo_eq_canonicalProductGauss p hp hcop hgood hprimary hI, hgen]
  rfl

end CompletedGauss

namespace FiniteRayExpansion

variable {R : Type*} [CommRing R] [Fintype R]
noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

def unitFourierCoeff (f : Rˣ → ℂ) (χ : MulChar R ℂ) : ℂ :=
  (∑ u : Rˣ, f u * star (χ (u : R))) / (Fintype.card Rˣ : ℂ)

theorem unit_fourier_inversion (f : Rˣ → ℂ) (v : Rˣ) :
    (∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ (v : R)) = f v := by
  have hN : (Fintype.card Rˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [unitFourierCoeff, div_mul_eq_mul_div, Finset.sum_mul, mul_assoc]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteRingSieve.unit_char_orthogonal]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_div_cancel_right₀ (f v) hN

theorem norm_char_unit (χ : MulChar R ℂ) (u : Rˣ) : ‖χ (u : R)‖ = 1 := by
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

theorem norm_char_le_one (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    exact (norm_char_unit χ u).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem unitFourierCoeff_norm_le_average (f : Rˣ → ℂ) (χ : MulChar R ℂ) :
    ‖unitFourierCoeff f χ‖ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := by
  rw [unitFourierCoeff, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ u : Rˣ, ‖f u * star (χ (u : R))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_star, norm_char_unit, mul_one]

theorem unitFourierCoeff_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) (χ : MulChar R ℂ) : ‖unitFourierCoeff f χ‖ ≤ B := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := unitFourierCoeff_norm_le_average f χ
    _ ≤ (∑ _u : Rˣ, B) / (Fintype.card Rˣ : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hf u)) (by positivity)
    _ = B := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem character_card_eq_units : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ

theorem unitFourierCoeff_sum_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ (Fintype.card Rˣ : ℝ) * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le f B hf χ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]

theorem unitFourierCoeff_sum_norm_le_sum (f : Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ ∑ u : Rˣ, ‖f u‖ := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le_average f χ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      field_simp

def zeroExtendUnits (f : Rˣ → ℂ) (r : R) : ℂ :=
  if hr : IsUnit r then f hr.unit else 0

@[simp] theorem zeroExtendUnits_unit (f : Rˣ → ℂ) (u : Rˣ) :
    zeroExtendUnits f (u : R) = f u := by
  rw [zeroExtendUnits, dite_eq_left u.isUnit]
  congr 1
  exact Units.ext u.isUnit.unit_spec

@[simp] theorem zeroExtendUnits_nonunit (f : Rˣ → ℂ) (r : R) (hr : ¬ IsUnit r) :
    zeroExtendUnits f r = 0 := dite_eq_right hr

theorem zeroExtendUnits_fourier (f : Rˣ → ℂ) (r : R) :
    zeroExtendUnits f r = ∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    rw [zeroExtendUnits_unit]
    exact (unit_fourier_inversion f u).symm
  · rw [zeroExtendUnits_nonunit f r hr]
    simp only [MulChar.map_nonunit _ hr, mul_zero, Finset.sum_const_zero]

theorem zeroExtendUnits_restrict (f : R → ℂ) (r : R) :
    zeroExtendUnits (fun u : Rˣ => f (u : R)) r = (if IsUnit r then 1 else 0) * f r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnits_unit, u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]

def unitTensorCoeff (f : Rˣ → Rˣ → ℂ) (χ η : MulChar R ℂ) : ℂ :=
  unitFourierCoeff (fun u => unitFourierCoeff (f u) η) χ

theorem unit_tensor_fourier_inversion (f : Rˣ → Rˣ → ℂ) (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ (u : R) * η (v : R)) = f u v := by
  calc
    _ = ∑ η : MulChar R ℂ,
        (∑ χ : MulChar R ℂ, unitTensorCoeff f χ η * χ (u : R)) * η (v : R) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ η : MulChar R ℂ, unitFourierCoeff (f u) η * η (v : R) := by
      apply Finset.sum_congr rfl
      intro η _
      change (∑ χ : MulChar R ℂ,
        unitFourierCoeff (fun a => unitFourierCoeff (f a) η) χ * χ (u : R)) * η (v : R) = _
      rw [unit_fourier_inversion]
    _ = _ := unit_fourier_inversion (f u) v

theorem unitTensorCoeff_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) (χ η : MulChar R ℂ) :
    ‖unitTensorCoeff f χ η‖ ≤ B :=
  unitFourierCoeff_norm_le _ B (fun u => unitFourierCoeff_norm_le (f u) B (hf u) η) χ

theorem unitTensorCoeff_sum_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      (Fintype.card Rˣ : ℝ) ^ 2 * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, ∑ _η : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun η _ => unitTensorCoeff_norm_le f B hf χ η))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      ring

theorem unitTensorCoeff_sum_norm_le_sum (f : Rˣ → Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      ∑ u : Rˣ, ∑ v : Rˣ, ‖f u v‖ := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ η : MulChar R ℂ, ∑ u : Rˣ, ‖unitFourierCoeff (f u) η‖ :=
      Finset.sum_le_sum (fun η _ => unitFourierCoeff_sum_norm_le_sum (fun u => unitFourierCoeff (f u) η))
    _ = ∑ u : Rˣ, ∑ η : MulChar R ℂ, ‖unitFourierCoeff (f u) η‖ := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun u _ => unitFourierCoeff_sum_norm_le_sum (f u))

def zeroExtendUnitPair (f : Rˣ → Rˣ → ℂ) (r s : R) : ℂ :=
  zeroExtendUnits (fun u => zeroExtendUnits (f u) s) r

theorem zeroExtendUnitPair_fourier (f : Rˣ → Rˣ → ℂ) (r s : R) :
    zeroExtendUnitPair f r s = ∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ r * η s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    by_cases hs : IsUnit s
    · obtain ⟨v, rfl⟩ := hs
      simp only [zeroExtendUnitPair, zeroExtendUnits_unit]
      exact (unit_tensor_fourier_inversion f u v).symm
    · simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_nonunit _ _ hs,
        MulChar.map_nonunit _ hs, mul_zero, Finset.sum_const_zero]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr,
      MulChar.map_nonunit _ hr, mul_zero, zero_mul, Finset.sum_const_zero]

theorem zeroExtendUnitPair_restrict (f : R → R → ℂ) (r s : R) :
    zeroExtendUnitPair (fun u v : Rˣ => f (u : R) (v : R)) r s =
      (if IsUnit r then 1 else 0) * (if IsUnit s then 1 else 0) * f r s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_restrict,
      u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]

end FiniteRayExpansion

open scoped BigOperators Classical

namespace RayFourExpansion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

abbrev RayRing := O ⧸ Ideal.span {(4 : O)}

noncomputable instance rayRingFintype : Fintype RayRing := by
  letI : Finite RayRing := finite_quotient_span (by norm_num : (4 : O) ≠ 0)
  exact Fintype.ofFinite _

abbrev RayCharacter := MulChar RayRing ℂ
noncomputable instance rayCharacterFintype : Fintype RayCharacter := Fintype.ofFinite _

def rayCharacter (χ : RayCharacter) (a : O) : ℂ :=
  χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)

theorem rayCharacter_mul (χ : RayCharacter) (a b : O) :
    rayCharacter χ (a * b) = rayCharacter χ a * rayCharacter χ b := by
  simp only [rayCharacter, map_mul]

theorem rayCharacter_eq_of_mod_four (χ : RayCharacter) (a b : O) (h : (4 : O) ∣ a - b) :
    rayCharacter χ a = rayCharacter χ b := by
  unfold rayCharacter
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

def rayMask (a : O) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) then 1 else 0

theorem rayRing_card : Fintype.card RayRing = 16 := by
  have h := rational_modulus_card 4 (by decide)
  simpa only [Nat.card_eq_fintype_card, Nat.cast_ofNat, show (4 : ℕ) ^ 2 = 16 by decide] using h

theorem rayUnit_card_le : Fintype.card RayRingˣ ≤ 16 := by
  calc
    _ ≤ Fintype.card RayRing := Fintype.card_le_of_injective _ Units.val_injective
    _ = 16 := rayRing_card

theorem rayCharacter_card_le : Fintype.card RayCharacter ≤ 16 := by
  rw [character_card_eq_units]
  exact rayUnit_card_le

def phaseCoeff (f : RayRing → ℂ) (χ : RayCharacter) : ℂ :=
  unitFourierCoeff (fun u : RayRingˣ => f (u : RayRing)) χ

theorem phase_expansion (f : RayRing → ℂ) (a : O) :
    rayMask a * f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, phaseCoeff f χ * rayCharacter χ a := by
  rw [rayMask, ← zeroExtendUnits_restrict]
  exact zeroExtendUnits_fourier _ _

theorem phaseCoeff_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) (χ : RayCharacter) :
    ‖phaseCoeff f χ‖ ≤ B := unitFourierCoeff_norm_le _ B hf χ

theorem phaseCoeff_sum_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ‖phaseCoeff f χ‖) ≤ 16 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1)
  exact (unitFourierCoeff_sum_norm_le _ B hf).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast rayUnit_card_le) hB)

def pairCoeff (f : RayRing → RayRing → ℂ) (χ η : RayCharacter) : ℂ :=
  unitTensorCoeff (fun u v : RayRingˣ => f (u : RayRing) (v : RayRing)) χ η

theorem pair_phase_expansion (f : RayRing → RayRing → ℂ) (a b : O) :
    rayMask a * rayMask b *
      f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) b) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        pairCoeff f χ η * rayCharacter χ a * rayCharacter η b := by
  rw [rayMask, rayMask, ← zeroExtendUnitPair_restrict]
  exact zeroExtendUnitPair_fourier _ _ _

theorem pairCoeff_norm_le (f : RayRing → RayRing → ℂ) (B : ℝ)
    (hf : ∀ u v : RayRingˣ, ‖f (u : RayRing) (v : RayRing)‖ ≤ B) (χ η : RayCharacter) :
    ‖pairCoeff f χ η‖ ≤ B := unitTensorCoeff_norm_le _ B hf χ η

theorem pairCoeff_sum_norm_le (f : RayRing → RayRing → ℂ) (B : ℝ)
    (hf : ∀ u v : RayRingˣ, ‖f (u : RayRing) (v : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖pairCoeff f χ η‖) ≤ 256 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1 1)
  have hcard : (Fintype.card RayRingˣ : ℝ) ^ 2 ≤ 256 := by
    have h : (Fintype.card RayRingˣ : ℝ) ≤ 16 := by exact_mod_cast rayUnit_card_le
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card RayRingˣ)]
  exact (unitTensorCoeff_sum_norm_le _ B hf).trans (mul_le_mul_of_nonneg_right hcard hB)

theorem quadraticRayValue_bounds (r : EisensteinEPrimaryPhase.Coord) :
    ‖quadraticRayValue r‖ ≤ 2 ∧ ‖(quadraticRayValue r)⁻¹‖ ≤ 1 := by
  rcases r with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [quadraticRayValue, breveGaussianFourTerms_formula, zpow_neg,
      Complex.I_sq, Complex.I_pow_three, Complex.inv_I,
      ZMod.val] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.inv_I]

theorem fixedGQuotientValue_norm_le_two (r : RayRing) : ‖fixedGQuotientValue r‖ ≤ 2 := by
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ cubicTwoIdeal) ℂ :=
    (cubicChar cubicTwoIdeal cubicTwoIdeal_good).ringHomComp eisEmbedding
  let x := Ideal.Quotient.mk cubicTwoIdeal (lift (residueQuotientFour r))
  have hc : ‖(χ x)⁻¹‖ ≤ 1 := by
    simpa only [MulChar.inv_apply_eq_inv'] using norm_char_le_one (χ⁻¹) x
  change ‖(χ x)⁻¹ * quadraticRayValue (residueQuotientFour r)‖ ≤ 2
  rw [norm_mul]
  calc
    _ ≤ 1 * 2 := mul_le_mul hc (quadraticRayValue_bounds _).1 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

def gCoeff : RayCharacter → ℂ := phaseCoeff fixedGQuotientValue

theorem gCoeff_norm_le_two (χ : RayCharacter) : ‖gCoeff χ‖ ≤ 2 :=
  phaseCoeff_norm_le _ 2 (fun u => fixedGQuotientValue_norm_le_two u) χ

theorem gCoeff_sum_norm_le : (∑ χ : RayCharacter, ‖gCoeff χ‖) ≤ 32 := by
  exact (phaseCoeff_sum_norm_le _ 2 (fun u => fixedGQuotientValue_norm_le_two u)).trans_eq (by norm_num)

theorem fixedG_character_expansion (a : O) :
    rayMask a * fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ a := phase_expansion _ a

def crossQuotientPhase (r s : RayRing) : ℂ :=
  MixedCrossSeparation.quadraticRayPair (residueQuotientFour r) (residueQuotientFour s)

theorem crossQuotientPhase_norm_le_two (r s : RayRing) : ‖crossQuotientPhase r s‖ ≤ 2 := by
  unfold crossQuotientPhase MixedCrossSeparation.quadraticRayPair
  rw [div_eq_mul_inv, mul_inv_rev, norm_mul, norm_mul]
  calc
    _ ≤ 2 * (1 * 1) :=
      mul_le_mul (quadraticRayValue_bounds _).1
        (mul_le_mul (quadraticRayValue_bounds _).2 (quadraticRayValue_bounds _).2
          (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 2 := by norm_num

def crossCoeff : RayCharacter → RayCharacter → ℂ := pairCoeff crossQuotientPhase

theorem crossCoeff_norm_le_two (χ η : RayCharacter) : ‖crossCoeff χ η‖ ≤ 2 :=
  pairCoeff_norm_le _ 2 (fun u v => crossQuotientPhase_norm_le_two u v) χ η

theorem crossCoeff_sum_norm_le :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) ≤ 512 := by
  exact (pairCoeff_sum_norm_le _ 2 (fun u v => crossQuotientPhase_norm_le_two u v)).trans_eq (by norm_num)

theorem quadraticRayPair_character_expansion (a b : O) :
    rayMask a * rayMask b * MixedCrossSeparation.quadraticRayPair (residue a) (residue b) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ a * rayCharacter η b := by
  simpa only [crossCoeff, crossQuotientPhase, residueQuotientFour_mk] using
    pair_phase_expansion crossQuotientPhase a b

end RayFourExpansion

end

end OAI

end

