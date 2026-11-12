module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part009
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part007
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.SecondDescent
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part008
public import Mathlib.Data.Int.Interval
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part023
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part006

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.Partition -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartition
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A]
theorem fullModulusCorrelation_swap (u v h : A)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ) :
    fullModulusCorrelation u v χ ψ h = star (fullModulusCorrelation v u ψ χ (-h)) := by
  simp only [fullModulusCorrelation, fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have he : u * v ∣ v * x - u * y - h ↔ v * u ∣ u * y - v * x - (-h) := by
    rw [mul_comm v u, show u * y - v * x - (-h) = -(v * x - u * y - h) by ring,
      dvd_neg]
  simp only [scaledResidue_congruence]
  by_cases hc : u * v ∣ v * x - u * y - h
  · simp only [hc, he.mp hc, ite_true, star_mul, star_star]
  · simp only [hc, (not_congr he).mp hc, ite_false, star_zero]
end Domain

open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentSupportedCorrelation CenteredMomentUnequal CenteredMomentLocal
open CenteredMomentProductCRT
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem actualCorrelation_norm_swap (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v})) (h : O) :
    ‖actualCorrelation u v hu hv h‖ = ‖actualCorrelation v u hv hu (-h)‖ := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  change ‖fullModulusCorrelation u v _ _ h‖ = ‖fullModulusCorrelation v u _ _ (-h)‖
  rw [fullModulusCorrelation_swap, norm_star]

theorem prime_power_norm_le_min (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O) :
    ‖actualCorrelation (p ^ c) (p ^ d) (supported_power p hp c) (supported_power p hp d)
      (p ^ min c d * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ min c d := by
  rcases lt_trichotomy c d with hcd | heq | hdc
  · have he : c + (d - c) = d := Nat.add_sub_of_le hcd.le
    have h := unequal_prime_power_norm_le p hp hg hc (show 1 ≤ d - c by omega) (-k)
    rw [actualCorrelation_norm_swap]
    simpa only [← pow_add, he, min_eq_left hcd.le, mul_neg] using h
  · subst d
    simpa only [min_self] using equal_prime_power_norm_le p hp hg hchar hc k
  · have he : d + (c - d) = c := Nat.add_sub_of_le hdc.le
    have h := unequal_prime_power_norm_le p hp hg hd (show 1 ≤ c - d by omega) k
    simpa only [← pow_add, he, min_eq_right hdc.le] using h

theorem prime_power_partition_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O) (save : Prop) [Decidable save]
    (hsave : save → c = d ∧ ¬ 6 ∣ c ∧ ¬ p ∣ k) :
    ‖actualCorrelation (p ^ c) (p ^ d) (supported_power p hp c) (supported_power p hp d)
      (p ^ min c d * k)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (min c d - if save then 1 else 0) := by
  by_cases hs : save
  · obtain ⟨rfl, hc6, hk⟩ := hsave hs
    simp only [min_self, ite_eq_left hs]
    exact (equal_prime_power_unit_norm p hp hg hchar hc hc6 k hk).le
  · simpa only [ite_eq_right hs, Nat.sub_zero] using prime_power_norm_le_min p hp hg hchar hc hd k

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem supported_product (a : ι → O) (ha : ∀ i, Supported (Ideal.span {a i})) :
    Supported (Ideal.span {∏ i, a i}) := by
  have hs (S : Finset ι) : Supported (Ideal.span {∏ i ∈ S, a i}) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Ideal.span_singleton_one]
      rw [← Ideal.one_eq_top]
      change Supported (1 : Ideal O)
      refine ⟨one_ne_zero, ?_⟩
      intro P hP
      simp only [UniqueFactorizationMonoid.normalizedFactors_one,
        Multiset.notMem_zero] at hP
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact supported_mul_elements _ _ (ha i) ih
  exact hs Finset.univ

def partitionNormalizer (p : ι → O) (c d : ι → ℕ) (U : Finset ι) : ℝ :=
  ∏ i, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ (min (c i) (d i) - if i ∈ U then 1 else 0)

def dividedFrequency (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) : O :=
  cofactor (fun j => p j ^ min (c j) (d j)) i * w

theorem commonFrequency_factor (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) :
    (∏ j, p j ^ min (c j) (d j)) * w = p i ^ min (c i) (d i) * dividedFrequency p c d w i := by
  rw [dividedFrequency, ← mul_assoc, factor_mul_cofactor (fun j => p j ^ min (c j) (d j)) i]

theorem actual_partition_norm_le (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (w : O)
    (hU : ∀ i ∈ U, c i = d i ∧ ¬ 6 ∣ c i ∧ ¬ p i ∣ dividedFrequency p c d w i) :
    ‖actualCorrelation (∏ i, p i ^ c i) (∏ i, p i ^ d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i ^ min (c i) (d i)) * w)‖ ≤ partitionNormalizer p c d U := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ c i})) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ d i})) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ c i * p i ^ d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add, ← pow_add]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  rw [actualCorrelation_product_norm (fun i => p i ^ c i) (fun i => p i ^ d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab]
  unfold partitionNormalizer
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [commonFrequency_factor p c d w i]
  exact prime_power_partition_norm_le (p i) (hp i) (hg i) (hchar i) (hc i) (hd i)
    (dividedFrequency p c d w i) (i ∈ U) (hU i)

theorem normalized_partition_norm_le_one (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (part : O → Prop) (w : O)
    (hpart : part w → ∀ i ∈ U, c i = d i ∧ ¬ 6 ∣ c i ∧ ¬ p i ∣ dividedFrequency p c d w i) :
    ‖if part w then
      actualCorrelation (∏ i, p i ^ c i) (∏ i, p i ^ d i)
        (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
        (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
        ((∏ i, p i ^ min (c i) (d i)) * w) / (partitionNormalizer p c d U : ℂ)
      else 0‖ ≤ 1 := by
  by_cases hw : part w
  · rw [ite_eq_left hw, norm_div, Complex.norm_real]
    have hN : 0 < partitionNormalizer p c d U := by
      unfold partitionNormalizer
      apply Finset.prod_pos
      intro i hi
      apply pow_pos
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    rw [Real.norm_of_nonneg hN.le]
    exact (div_le_one hN).mpr (actual_partition_norm_le p hp hg hchar hcop c d hc hd U w (hpart hw))
  · simp only [ite_eq_right hw, norm_zero, zero_le_one]

end Product

end SevenEighths.CenteredMomentPartition

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PartitionNorm -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartitionNorm
open CenteredMomentPartition CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonIdeal (p : ι → O) (c d : ι → ℕ) : Ideal O :=
  ∏ i, Ideal.span {p i} ^ min (c i) (d i)

def unitIdeal (p : ι → O) (U : Finset ι) : Ideal O := ∏ i ∈ U, Ideal.span {p i}

omit [DecidableEq ι] in
theorem commonIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) : 0 < (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  apply Finset.prod_pos
  intro i hi
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

omit [Fintype ι] [DecidableEq ι] in
theorem unitIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (U : Finset ι) : 0 < (Ideal.absNorm (unitIdeal p U) : ℝ) := by
  simp only [unitIdeal, map_prod, Nat.cast_prod]
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

theorem partitionNormalizer_mul_unit_norm (p : ι → O) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U * (Ideal.absNorm (unitIdeal p U) : ℝ) =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [unitIdeal, commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  have hU : (∏ i ∈ U, (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∏ i, if i ∈ U then (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 1 := by simp
  rw [hU, partitionNormalizer, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hmem : i ∈ U
  · simp only [ite_eq_left hmem]
    rw [← pow_succ, Nat.sub_add_cancel (le_min (hc i) (hd i))]
  · simp only [ite_eq_right hmem, Nat.sub_zero, mul_one]

theorem partitionNormalizer_eq_norm_ratio (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) / Ideal.absNorm (unitIdeal p U) := by
  apply (eq_div_iff (unitIdeal_norm_pos p hp U).ne').mpr
  exact partitionNormalizer_mul_unit_norm p c d hc hd U

theorem partitionNormalizer_eq_log_scale (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι)
    (Z : ℝ) (hZ : 1 < Z) :
    partitionNormalizer p c d U =
      Z ^ (Real.logb Z (Ideal.absNorm (commonIdeal p c d)) -
        Real.logb Z (Ideal.absNorm (unitIdeal p U))) := by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (commonIdeal_norm_pos p hp c d),
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (unitIdeal_norm_pos p hp U)]
  exact partitionNormalizer_eq_norm_ratio p hp c d hc hd U

end SevenEighths.CenteredMomentPartitionNorm

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Forcing -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentForcing
open UniqueFactorizationMonoid CenteredExceptionalCount CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def movingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  (∏ i, P i ^ min (c i) (d i)) * ∏ i ∈ V, P i

def forcingSet (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  V.filter (fun i => c i = 1 ∧ d i = 1)

def forcingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ forcingSet c d V, P i

omit [Fintype ι] in
theorem valuation_product (S : Finset ι) (I : ι → Ideal O)
    (hI : ∀ i ∈ S, I i ≠ 0) (Q : Ideal O) :
    valuation (∏ i ∈ S, I i) Q = ∑ i ∈ S, valuation (I i) Q := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,valuation,normalizedFactors_one,Multiset.count_zero]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      valuation_mul _ _ _ (hI i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hI j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))]

theorem valuation_prime (P Q : Ideal O) (hP : Prime P) :
    valuation P Q = if P = Q then 1 else 0 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro R hR; simpa only [Multiset.mem_singleton.mp hR] using hP))
  simp only [valuation,hf,Multiset.count_singleton]
  simp only [eq_comm]

omit [Fintype ι] in
theorem valuation_prime_product (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    valuation (∏ j ∈ S, P j) (P i) = if i ∈ S then 1 else 0 := by
  rw [valuation_product S P (fun j _ => (hp j).ne_zero)]
  simp only [valuation_prime _ _ (hp _), hinj.eq_iff]
  simp

theorem valuation_prime_power_product (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (n : ι → ℕ) (i : ι) :
    valuation (∏ j, P j ^ n j) (P i) = n i := by
  rw [valuation_product Finset.univ _ (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  simp only [valuation_pow,valuation_prime _ _ (hp _),hinj.eq_iff,mul_ite,mul_one,mul_zero]
  simp

omit [DecidableEq ι] in
theorem movingIdeal_ne_zero (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) : movingIdeal P c d V ≠ 0 := by
  unfold movingIdeal
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))

theorem movingIdeal_valuation (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι) :
    valuation (movingIdeal P c d V) (P i) = min (c i) (d i) + if i ∈ V then 1 else 0 := by
  rw [movingIdeal,valuation_mul _ _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)),
    valuation_prime_power_product P hp hinj, valuation_prime_product P hp hinj]

theorem forcing_valuation_two (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι)
    (i : ι) (hi : i ∈ forcingSet c d V) : valuation (movingIdeal P c d V) (P i) = 2 := by
  obtain ⟨hiV,hc,hd⟩ := Finset.mem_filter.mp hi
  rw [movingIdeal_valuation P hp hinj c d V i,hc,hd,ite_eq_left hiV]
  norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem forcingIdeal_squarefree (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (forcingIdeal P c d V) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    let : (P i).IsMaximal := (Ideal.isPrime_of_prime (hp i)).isMaximal (hp i).ne_zero
    let : (P j).IsMaximal := (Ideal.isPrime_of_prime (hp j)).isMaximal (hp j).ne_zero
    exact (Ideal.isCoprime_of_isMaximal (hinj.ne hij)).isRelPrime
  · intro i hi
    exact (hp i).squarefree

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_prime_mem (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Q : Ideal O)
    (hQ : Q ∈ normalizedFactors (forcingIdeal P c d V)) :
    ∃ i ∈ forcingSet c d V, Q = P i := by
  have hf : normalizedFactors (forcingIdeal P c d V) =
      (forcingSet c d V).val.map P := by
    apply normalizedFactors_prod_of_prime
    intro R hR
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hR
    exact hp i
  rw [hf] at hQ
  obtain ⟨i,hi,hPi⟩ := Multiset.mem_map.mp hQ
  exact ⟨i,hi,hPi.symm⟩

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_norm_scale (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Z ^ ((2 * Real.logb Z (Ideal.absNorm (forcingIdeal P c d V))) / 2) =
      (Ideal.absNorm (forcingIdeal P c d V) : ℝ) := by
  rw [show (2 * Real.logb Z (Ideal.absNorm (forcingIdeal P c d V))) / 2 =
    Real.logb Z (Ideal.absNorm (forcingIdeal P c d V)) by ring]
  exact Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (norm_pos (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)))

def movingElement (p : ι → O) (c d : ι → ℕ) (V : Finset ι) : O :=
  (∏ i, p i ^ min (c i) (d i)) * ∏ i ∈ V, p i

omit [DecidableEq ι] in
theorem movingElement_span (p : ι → O) (c d : ι → ℕ) (V : Finset ι) :
    Ideal.span {movingElement p c d V} = movingIdeal (fun i => Ideal.span {p i}) c d V := by
  simp only [movingElement,movingIdeal,Ideal.span_singleton_pow,
    Ideal.prod_span_singleton,Ideal.span_singleton_mul_span_singleton]

theorem actual_forcing_exceptional_count (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι)
    (η : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m e : O) (hm : m ≠ 0) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (he : HeckeFamily.elementCoeff η e ≠ 0) (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, CenteredExceptionalProfile.FixedInducingRow
      (CenteredMomentChildRows.childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2 : O) ∉ Ideal.span {p i} ∧
      IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e})
    (Z C M : ℝ) (hZ : 1 < Z) (hC : 0 ≤ C)
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) *
        Z ^ ((M - 4 * Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V))) / 6) := by
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  have hb := CenteredMomentChildRows.separated_exceptional_count η χ Q hQ0 hQ hQ72
    m (movingElement p c d V) e hm hA hmLam hm2 he T hT hex
    (forcingIdeal (fun i => Ideal.span {p i}) c d V)
    (forcingIdeal_squarefree _ hp hinj c d V) (by
      intro P hP
      obtain ⟨i,hi,rfl⟩ := forcing_prime_mem _ hp c d V P hP
      obtain ⟨hg,h2,hQP,hPe⟩ := hgood i hi
      refine ⟨hg,h2,hQP,hPe,?_⟩
      rw [movingElement_span,forcing_valuation_two _ hp hinj c d V i hi])
    Z C M (2 * Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))
    (zero_lt_one.trans hZ) hC (forcing_norm_scale _ hp c d V Z hZ).le hN
  convert hb using 1 ; congr 1 ; ring_nf

end SevenEighths.CenteredMomentForcing

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.HeckeExceptionalEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExceptionalEnergy
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem forcing_finite_energy (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι) (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (m e : O) (hm : m ≠ 0) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (he : elementCoeff η e ≠ 0) (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
      (childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2:O) ∉ Ideal.span {p i} ∧
      IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e})
    (Z C M D : ℝ) (hZ : 1 < Z) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ C*Z^M)
    (f : O → ℂ) (hf : ∀ z ∈ rows, ‖f z‖ ≤ D) :
    (∑ z ∈ rows, ‖f z‖^2) ≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*C^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))/6))*D^2 := by
  have hc := actual_forcing_exceptional_count p hp hinj c d V η χ Q hQ0 hQ hQ72
    m e hm hmLam hm2 he rows hrows hex hgood Z C M hZ hC hN
  calc
    _ ≤ ∑ _z ∈ rows, D^2 := Finset.sum_le_sum (fun z hz =>
      pow_le_pow_left₀ (norm_nonneg _) (hf z hz) 2)
    _ = (rows.card:ℝ)*D^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg D)

theorem exceptional_slots_energy (Q : Ideal O) (hQ0 : Q ≠ 0)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ (p : ι → O), (∀ i, Prime (Ideal.span {p i})) →
      Function.Injective (fun i => Ideal.span {p i}) →
      ∀ (c d : ι → ℕ) (V : Finset ι) (η : Character) (χ : RayFourExpansion.RayCharacter),
      ∀ m e : O, m ≠ 0 → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      elementCoeff η e ≠ 0 → ∀ rows : Finset O,
      (∀ z ∈ rows, z ≠ 0) →
      (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
        (childCharacter η χ) Q m (movingElement p c d V) z) →
      (∀ z ∈ rows, (HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1
        (movingElement p c d V*z):ℝ) ≤ Z^B) →
      (∀ i ∈ forcingSet c d V,
        ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2:O) ∉ Ideal.span {p i} ∧
        IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e}) →
      ∀ Cr Mrow : ℝ, 0 ≤ Cr →
      (∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Cr*Z^Mrow) →
      ∀ (S : κ → Finset (Ideal O)) (β : κ → Ideal O → ℂ) (P b Ms : κ → ℝ),
      (∀ i, 0 < P i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ Ms i) →
      (∀ i, ∀ I ∈ S i, ‖β i I‖ ≤ Ms i) →
      (∀ i, ∀ I ∈ S i, β i I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ b i*P i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      (∑ z ∈ rows, ‖centeredSlotRow (childCharacter η χ) m (movingElement p c d V) z
        W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2) ≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((Mrow-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))/6))*
        (C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*Ms i)*(Real.sqrt (T*∏ i,P i)/L))^2 := by
  obtain ⟨J,hJ⟩ := exceptional_slots_estimate (ι := κ) Q hQ0 a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ p hp hinj c d V η χ m e hm hmLam hm2 he rows hrows hex hcond hgood
    Cr Mrow hCr hN S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  refine forcing_finite_energy p hp hinj c d V η χ Q hQ0 hQ hQ72
    m e hm hmLam hm2 he rows hrows hex hgood Z Cr Mrow _ hZ hCr ?_ hN _ ?_
  · have hprod : 0 ≤ ∏ i,128*b i*Ms i :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hMs i))
    positivity
  · intro z hz
    exact hbound Z hZ.le (childCharacter η χ) m (movingElement p c d V) z hm hA (hrows z hz)
      hmLam hm2 (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentHeckeExceptionalEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondLedger -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondLedger
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentPartition CenteredMomentProductCRT ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem nonzero_unequal_min_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (hcd : c ≠ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) : 6 ∣ min c d := by
  by_contra h6
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hc
      (show 1 ≤ d-c by omega) (by simpa only [min_eq_left hlt.le] using h6) (-k)
    have he : c+(d-c)=d := Nat.add_sub_of_le hlt.le
    have hn := norm_ne_zero_iff.mpr hne
    rw [actualCorrelation_norm_swap] at hn
    have hz' : actualCorrelation (p^d) (p^c) (supported_power p hp d) (supported_power p hp c)
        (-(p^min c d*k)) = 0 := by
      simpa only [← pow_add,he,min_eq_left hlt.le,mul_neg] using hz
    exact hn (by rw [hz',norm_zero])
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hd
      (show 1 ≤ c-d by omega) (by simpa only [min_eq_right hgt.le] using h6) k
    have he : d+(c-d)=c := Nat.add_sub_of_le hgt.le
    exact hne (by simpa only [← pow_add,he,min_eq_right hgt.le] using hz)

def localSaving (c d : ℕ) (nonunit : Prop) : ℝ :=
  (c+d : ℝ) - 5*(min c d : ℝ)/6 - 1 +
    (if c=d ∧ ¬6∣c ∧ ¬nonunit then 1 else 0) +
    (if c=d ∧ ¬6∣c ∧ nonunit then 1/6 else 0) +
    (if c=d ∧ c=1 ∧ nonunit then 1/3 else 0)

theorem localSaving_lower (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (huneq : c ≠ d → 6 ∣ min c d) (nonunit : Prop) :
    ((c:ℝ)+d)/3 ≤ localSaving c d nonunit := by
  by_cases hcd : c=d
  · subst d
    by_cases h6 : 6∣c
    · have hc6 : 6 ≤ c := Nat.le_of_dvd (by omega) h6
      have hn1 : c ≠ 1 := by omega
      simp only [localSaving,min_self,h6,not_true_eq_false,false_and,and_false,
        ite_false,hn1,add_zero]
      have hcr : (6:ℝ) ≤ c := by exact_mod_cast hc6
      linarith
    · by_cases hu : nonunit
      · by_cases hc1 : c=1
        · subst c
          norm_num [localSaving,hu]
        · have hc2 : 2 ≤ c := by omega
          simp only [localSaving,min_self,h6,not_false_eq_true,hu,not_true_eq_false,
            and_self,and_false,false_and,ite_false,ite_true,hc1,add_zero]
          have hcr : (2:ℝ) ≤ c := by exact_mod_cast hc2
          linarith
      · simp only [localSaving,min_self,h6,not_false_eq_true,hu,and_false,
          and_true,ite_false,ite_true,add_zero]
        have hcr : (1:ℝ) ≤ c := by exact_mod_cast hc
        linarith
  · have hmin : 6 ≤ min c d := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (le_min hc hd)) (huneq hcd)
    have hmr : (6:ℝ) ≤ min c d := by exact_mod_cast hmin
    have hmc : ((min c d : ℕ) : ℝ) ≤ c := by exact_mod_cast min_le_left c d
    have hmd : ((min c d : ℕ) : ℝ) ≤ d := by exact_mod_cast min_le_right c d
    simp only [Nat.cast_min] at hmr hmc hmd
    simp only [localSaving,hcd,false_and,ite_false,add_zero]
    linarith

theorem actual_localSaving_lower (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) :
    ((c:ℝ)+d)/3 ≤ localSaving c d (p ∣ k) :=
  localSaving_lower c d hc hd (fun hcd => nonzero_unequal_min_six p hp hg hchar c d hc hd hcd k hne) _

section Global
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem local_nonzero_of_global (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ) (w : O)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) (i : ι) :
    actualCorrelation (p i^c i) (p i^d i) (supported_power (p i) (hp i) (c i))
      (supported_power (p i) (hp i) (d i))
      (p i^min (c i) (d i)*dividedFrequency p c d w i) ≠ 0 := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^d i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i*p i^d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add,← pow_add]
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hn := norm_ne_zero_iff.mpr hne
  rw [actualCorrelation_product_norm (fun i => p i^c i) (fun i => p i^d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab] at hn
  have hi := (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
  rw [commonFrequency_factor p c d w i] at hi
  exact norm_ne_zero_iff.mp hi

omit [DecidableEq ι] in
theorem log_norm_power_product (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c : ι → ℕ) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) =
      ∑ i, (c i : ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]
  rw [Real.logb_prod _ _ (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)))]
  simp only [Real.logb_pow]

def secondSaving (p : ι → O) (c d : ι → ℕ) (w : O) (Z : ℝ) : ℝ :=
  ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) *
    localSaving (c i) (d i) (p i ∣ dividedFrequency p c d w i)

def actualUnitSet (p : ι → O) (c d : ι → ℕ) (w : O) : Finset ι :=
  Finset.univ.filter (fun i => c i=d i ∧ ¬6∣c i ∧ ¬p i∣dividedFrequency p c d w i)

def actualNonunitSet (p : ι → O) (c d : ι → ℕ) (w : O) : Finset ι :=
  Finset.univ.filter (fun i => c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i)

omit [Fintype ι] [DecidableEq ι] in
theorem log_norm_radical (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (S : Finset ι) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) =
      ∑ i ∈ S, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,Nat.cast_prod]
  exact Real.logb_prod _ _ (fun i _ => Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))

theorem secondSaving_eq_norm_ledger (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ) (w : O) (Z : ℝ) :
    secondSaving p c d w Z =
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) +
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ) -
      5*Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.commonIdeal p c d) : ℝ)/6 -
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) +
      Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.unitIdeal p (actualUnitSet p c d w)) : ℝ) +
      Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.unitIdeal p (actualNonunitSet p c d w)) : ℝ)/6 +
      Real.logb Z (Ideal.absNorm (CenteredMomentForcing.forcingIdeal
        (fun i => Ideal.span {p i}) c d (actualNonunitSet p c d w)) : ℝ)/3 := by
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d]
  simp only [CenteredMomentPartitionNorm.commonIdeal,CenteredMomentPartitionNorm.unitIdeal,
    CenteredMomentForcing.forcingIdeal]
  rw [log_norm_power_product p hp,log_norm_radical p hp,log_norm_radical p hp,
    log_norm_radical p hp,log_norm_radical p hp]
  simp only [actualUnitSet,actualNonunitSet,CenteredMomentForcing.forcingSet,
    Finset.filter_filter,Finset.sum_filter,]
  unfold secondSaving
  have hf (i : ι) :
      (if (c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i) ∧ c i=1 ∧ d i=1
       then Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 0) =
      (if c i=d i ∧ c i=1 ∧ p i∣dividedFrequency p c d w i
       then Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 0) := by
    have he : ((c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i) ∧ c i=1 ∧ d i=1) ↔
        (c i=d i ∧ c i=1 ∧ p i∣dividedFrequency p c d w i) := by
      constructor
      · rintro ⟨⟨hcd,h6,hn⟩,hc,hd⟩
        exact ⟨hcd,hc,hn⟩
      · rintro ⟨hcd,hc,hn⟩
        exact ⟨⟨hcd,by omega,hn⟩,hc,by omega⟩
    simp only [he]
  simp_rw [hf]
  rw [show (∑ i, (c i:ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)) +
      (∑ i, (d i:ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∑ i, ((c i:ℝ)+(d i:ℝ))*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) by
      simp only [add_mul,Finset.sum_add_distrib]]
  simp only [Finset.mul_sum,Finset.sum_div]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [localSaving,Nat.cast_min]
  split_ifs <;> ring

theorem actual_secondSaving_lower (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i})) (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (w : O) (Z : ℝ) (hZ : 1 < Z)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) :
    (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) +
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/3 ≤ secondSaving p c d w Z := by
  calc
    _ = ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)*(((c i:ℝ)+d i)/3) := by
      rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
        ← Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
        (actual_localSaving_lower (p i) (hp i) (hg i) (hchar i) (c i) (d i) (hc i) (hd i)
          (dividedFrequency p c d w i) (local_nonzero_of_global p hp hcop c d w hne i))
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

end Global

end SevenEighths.CenteredMomentSecondLedger

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonAllowance -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonAllowance
open CenteredMomentActive CenteredMomentSecondLedger CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def activeIndicator (c d : ℕ) : ℝ := if netExponent c d ≠ 0 then 1 else 0

theorem netExponent_self (c : ℕ) : netExponent c c = 0 := by
  unfold netExponent
  have h : c+5*c=6*c := by omega
  rw [h, Nat.mul_mod_right]

theorem local_allowance (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    max (3*(c:ℝ)-5*(d:ℝ)-activeIndicator c d) 0 / 6 +
      max (3*(d:ℝ)-5*(c:ℝ)-activeIndicator c d) 0 / 6 ≤
      (c:ℝ)+(d:ℝ)-2-activeIndicator c d := by
  have hc' : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold activeIndicator
  split_ifs with he
  · have hne : c ≠ d := by rintro rfl; exact he (netExponent_self c)
    have hgap : (c:ℝ)+1 ≤ d ∨ (d:ℝ)+1 ≤ c := by
      rcases lt_or_gt_of_ne hne with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    rcases hgap with hgap | hgap <;>
      rw [max_def,max_def] <;> split_ifs <;> linarith
  · rw [max_def,max_def]; split_ifs <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem weighted_positive_part (a w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (∑ i, a i*w i) 0 ≤ ∑ i, max (a i) 0*w i := by
  apply max_le
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hw i)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (hw i)

omit [DecidableEq ι] in
theorem weighted_allowance (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hd : ∀ i, 1 ≤ d i) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (3*(∑ i, (c i:ℝ)*w i)-5*(∑ i, (d i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 +
    max (3*(∑ i, (d i:ℝ)*w i)-5*(∑ i, (c i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 ≤
      (∑ i, (c i:ℝ)*w i)+(∑ i, (d i:ℝ)*w i)-
        2*(∑ i, w i)-(∑ i, activeIndicator (c i) (d i)*w i) := by
  have h₁ := weighted_positive_part (fun i => 3*(c i:ℝ)-5*(d i:ℝ)-activeIndicator (c i) (d i)) w hw
  have h₂ := weighted_positive_part (fun i => 3*(d i:ℝ)-5*(c i:ℝ)-activeIndicator (c i) (d i)) w hw
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (local_allowance (c i) (d i) (hc i) (hd i)) (hw i))
  simp only [sub_mul, add_mul, div_mul_eq_mul_div, mul_assoc,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    ] at h₁ h₂ hsum ⊢
  simp only [← Finset.sum_div] at hsum
  linarith

omit [DecidableEq ι] in
theorem actual_common_support_allowance (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (Z : ℝ) (hZ : 1 < Z) :
    let C := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)
    let D := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ)
    let P := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ)
    let R := Real.logb Z (Ideal.absNorm
      (∏ i ∈ activeSupport Finset.univ c d, Ideal.span {p i}) : ℝ)
    max (3*C-5*D-R) 0/6 + max (3*D-5*C-R) 0/6 ≤ C+D-2*P-R := by
  dsimp only
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
    log_norm_radical p hp,log_norm_radical p hp]
  simpa only [activeSupport,Finset.sum_filter,activeIndicator,ite_mul,one_mul,zero_mul]
    using weighted_allowance c d hc hd
      (fun i => Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ))
      (fun i => Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))))

end SevenEighths.CenteredMomentCommonAllowance

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DescentLedger -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentSecondLedger CenteredMomentPartitionNorm
local notation "O" => ActualEisensteinCubic.O

def firstSaving (c D₀ w q wo B g ell : ℝ) : ℝ :=
  c/6+5*D₀/6+w/3+q/6+wo+B-5*g/6+ell

theorem firstSaving_lower (c d D₀ w q R wo B g ell σ δ : ℝ)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hq : 0 ≤ q) (hwo : 0 ≤ wo)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hR : R ≤ q) (hBcost : max (3*c-5*d-R) 0/6 ≤ B)
    (hD : d-δ ≤ D₀) (hg : g ≤ max (D₀-c-2*w+wo) 0+2*σ)
    (hell : 0 ≤ ell) (hwσ : w ≤ 7*σ/3) :
    2*(c+w)/3-3*σ-5*δ/6 ≤ firstSaving c D₀ w q wo B g ell := by
  have hraw : 3*c-5*d-R ≤ 6*B := by
    have hm := le_max_left (3*c-5*d-R) 0
    linarith
  have hmax : max (3*c-5*D₀) 0/6-5*δ/6 ≤ B+q/6 := by
    apply (max_le_iff.mpr ⟨?_,?_⟩ : max (3*c-5*D₀) 0 ≤ 6*(B+q/6)+5*δ) |> fun h => by linarith
    · linarith
    · positivity
  unfold firstSaving
  by_cases hJ : 0 ≤ D₀-c-2*w+wo
  · rw [max_eq_left hJ] at hg
    linarith
  · rw [max_eq_right (le_of_not_ge hJ)] at hg
    have hm := le_max_left (3*c-5*D₀) 0
    linarith

section ActualSecond
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_log_ge_unit (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (unitIdeal p U) : ℝ) ≤
      Real.logb Z (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  rw [unitIdeal,log_norm_radical p hp,commonIdeal,log_norm_power_product p hp]
  calc
    _ ≤ ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro i hi hni
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
        Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
      have hm : (1:ℝ) ≤ (min (c i) (d i) : ℕ) := by exact_mod_cast le_min (hc i) (hd i)
      nlinarith

omit [DecidableEq ι] in
theorem half_product_log_ge_radical (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) ≤
      (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)+
       Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/2 := by
  rw [log_norm_radical p hp,log_norm_power_product p hp,log_norm_power_product p hp,
    ← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
  have hcr : (1:ℝ) ≤ c i := by exact_mod_cast hc i
  have hdr : (1:ℝ) ≤ d i := by exact_mod_cast hd i
  nlinarith
end ActualSecond

theorem declared_width_drop (M J g g₂ t₂ σ m' q' δ : ℝ)
    (hwidth : m'+q'=M+J-g-g₂+t₂) (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂)
    (hnonempty : 0 ≤ m'+δ) :
    max 0 (m'+δ)+q' ≤ M-σ+δ := by
  rw [max_eq_right hnonempty]
  linarith

theorem child_allowance_lower (b₂ p₂ w B ell : ℝ)
    (hbp : p₂ ≤ b₂) (hB : 0 ≤ B) :
    w+ell ≤ b₂-p₂+w+B+ell := by linarith

theorem exceptional_excess_identity
    (A m q c d R E K w wo B g ell b₂ p₂ g₂ t₂ V f : ℝ) :
    let a₀ := A-c-w
    let K₀ := 2*A-c-d+R+E-m
    let m' := 2*a₀-K-g-g₂-V
    let q' := q+R+E+wo+t₂+V
    (m'-f)/6+a₀-b₂-(m'+q'+(b₂-p₂+w+B+ell)) =
      A-5*(m+q)/6-firstSaving c (d+K₀-K) w (q+R+E) wo B g ell -
        (2*b₂-5*g₂/6-p₂+t₂+V/6+f/6) := by
  dsimp only [firstSaving]
  ring

theorem inner_allowance_identity
    (a₀ q wo w B s₀ K g ell p₂ g₂ t₂ b₂ V : ℝ) :
    (a₀+q+wo+w+B-s₀)-(K+g-ell-a₀+p₂-s₀+g₂-t₂-b₂) =
      (2*a₀-K-g-g₂-V)+(q+wo+t₂+V)+(b₂-p₂+w+B+ell) := by ring

theorem exceptional_excess_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ A-5*M/6-2*(c+w+b₂)/3+3*σ+5*δ/6 := by linarith

theorem uncentered_exceptional_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hA : A ≤ 5*M/6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb : 0 ≤ b₂)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ 3*σ+5*δ/6 := by
  have hh := exceptional_excess_bound A M c w b₂ F₁ F₂ σ δ hF₁ hF₂
  linarith

end SevenEighths.CenteredMomentDescentLedger

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FinalStageLedger -/

section

namespace OAI

noncomputable section
namespace SevenEighths.CenteredMomentFinalStageLedger

theorem capped_loss (M v : ℝ) : M/6≤2*v/3+max (M/4-v) 0 := by
  by_cases h : 0≤M/4-v
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem final_exponent (A M v loss₁ loss₂ : ℝ) :
    A-5*M/6-2*v/3-max (M/4-v) 0+loss₁+loss₂≤
      max (A-M) 0+loss₁+loss₂ := by
  have h:=capped_loss M v
  have hm:=le_max_left (A-M) (0:ℝ)
  linarith

theorem saving_exponent (A M v F₁ F₂ loss₁ loss₂ : ℝ)
    (h₁:2*v/3-loss₁≤F₁) (h₂:max (M/4-v) 0-loss₂≤F₂) :
    A-5*M/6-F₁-F₂≤ max (A-M) 0+loss₁+loss₂ := by
  linarith [final_exponent A M v loss₁ loss₂]

theorem saving_power (Z A M v F₁ F₂ loss₁ loss₂ : ℝ) (hZ:1≤Z)
    (h₁:2*v/3-loss₁≤F₁) (h₂:max (M/4-v) 0-loss₂≤F₂) :
    Z^(A-5*M/6-F₁-F₂)≤Z^(max (A-M) 0+loss₁+loss₂) :=
  Real.rpow_le_rpow_of_exponent_le hZ (saving_exponent A M v F₁ F₂ loss₁ loss₂ h₁ h₂)

end SevenEighths.CenteredMomentFinalStageLedger

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondScaled -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondScaled
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentProductCRT CenteredMomentUnequal CenteredMomentPartition
local notation "O" => ActualEisensteinCubic.O

def movingCoefficient {α : Type*} (A : O) (a : α → O) (c : α → ℂ) (i : α) : ℂ :=
  c i*idealRowHom A (Ideal.span {a i})

theorem divisorCoefficient_moving {α : Type*} (L : Ideal O) (A : O) (a : α → O)
    (c : α → ℂ) (χ : RayCharacter) (i : α) :
    divisorCoefficient L a (movingCoefficient A a c) χ i =
      divisorCoefficient L a c χ i*idealRowHom A (Ideal.span {a i}) := by
  unfold divisorCoefficient movingCoefficient
  split_ifs <;> ring

theorem actual_child_column {α : Type*} (L : Ideal O) (η : HeckeFamily.Character)
    (χ : RayCharacter) (m A₀ h : O) (a : α → O) (β : α → ℂ) (i : α)
    (ha : Supported (Ideal.span {a i}))
    (hp : ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) :
    divisorCoefficient L a (movingCoefficient A₀ a
      (fun j => β j*HeckeFamily.elementCoeff η (a j)*coprimalityMask m (a j))) χ i *
      idealRowHom h (Ideal.span {a i}) =
    (if L ∣ Ideal.span {a i} then β i else 0) *
      rowTwist (HeckeRowClosure.elementHom (CenteredMomentChildRows.childCharacter η χ))
        m 1 (A₀*h) (a i) := by
  rw [CenteredMomentChildRows.child_row_primary η χ m A₀ h (a i) ha hp]
  simp only [divisorCoefficient,movingCoefficient,idealRowHom_argument_mul]
  split_ifs <;> ring

theorem scaled_partition_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (part : O → Prop) (V₀ h : O)
    (hpart : part (V₀*h) → ∀ i ∈ U, c i=d i ∧ ¬6∣c i ∧
      ¬p i∣CenteredMomentPartition.dividedFrequency p c d (V₀*h) i) :
    ‖(if part (V₀*h) then (1:ℂ)/(CenteredMomentPartition.partitionNormalizer p c d U : ℂ) else 0) *
      actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
        (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
        (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
        (((∏ i, p i^min (c i) (d i))*V₀)*h)‖ ≤ 1 := by
  have hb := CenteredMomentPartition.normalized_partition_norm_le_one
    p hp hg hchar hcop c d hc hd U part (V₀*h) hpart
  by_cases hh : part (V₀*h)
  · simpa only [ite_eq_left hh,one_div,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,one_mul] using hb
  · simp only [ite_eq_right hh,zero_mul,norm_zero,zero_le_one]

theorem actual_scaled_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E A₀ : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda^2 ∣ D-1)
    (hpE : ConcretePrimeRowBridge.goodLambda^2 ∣ E-1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE (A₀*z)) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -(A₀*z)=A₀*(-z) by ring]
  simp only [idealRowHom_argument_mul,divisorCoefficient_moving,star_mul]
  ring

theorem whole_kernel_scaled_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ),
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (rowEnergy S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K).re ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (rowEnergy T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K).re ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_plain_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondScaled

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondChildProfile -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondChildProfile
open HeckeFamily HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentChildAssembly
open CenteredMomentSecondScaled CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

theorem child_ideal_primary (η : Character) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (childCharacter η χ) I=idealCoeff η I*rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hc := idealCoeff_span (childCharacter η χ) hn
  have he := idealCoeff_span η hn
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by rw [hs];exact hI)
    (CompletedGauss.primaryGenerator_spec I hn).2,←he]

theorem exists_second_height_character (η : Character) (χ : RayCharacter) (m A : O)
    (hm : m≠0) (hA : A≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : Character,τ.modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
          rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) m 1 A hm one_ne_zero hA hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he := idealCoeff_eq_row (childCharacter η χ) τ m 1 A hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom A I*rayCharacter χ (CompletedGauss.primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem second_divisor_column (η τ : Character) (χ : RayCharacter) (m A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
        rayCharacter χ (CompletedGauss.primaryGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
      (movingCoefficient A (fun J : Ideal O => CompletedGauss.primaryGenerator J)
        (fun J => β J*rowWeight η m 1 1 t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

end SevenEighths.CenteredMomentSecondChildProfile

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondHeightFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentSecondChildProfile CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled RayFourExpansion ConcretePrimeRowBridge ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

def fixedBadMask : O := goodLambda*2

theorem fixedBadMask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero (by norm_num)

theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo

theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [ite_eq_left hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

theorem exists_second_family (η : Character) (χ : RayCharacter) (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤HeckeRowClosure.rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_second_height_character η χ fixedBadMask A fixedBadMask_ne_zero hA
    (by exact dvd_mul_right goodLambda (2:O)) (by exact dvd_mul_left (2:O) goodLambda)
  refine ⟨τ,hN,?_⟩
  intro I hI t
  rw [hτ I hI t,←heightCoeff_eq_fixed_rowWeight η t I hI]

theorem second_height_divisor_column (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryGenerator J)
      (movingCoefficient A (fun J : Ideal O => primaryGenerator J)
        (fun J => β J*heightCoeff η t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

end SevenEighths.CenteredMomentSecondHeightFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondFamilyTransport
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredExceptionalProfile CenteredMomentRestrictedEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem row_presentation_height (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  have he := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1 A hτ I
  have he' : heightCoeff τ t I=rowWeight (childCharacter η χ) fixedBadMask 1 A t I := by
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [he]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,one_pow,one_mul,mul_one]
  rw [he',rowWeight_split,←heightCoeff_eq_fixed_rowWeight (childCharacter η χ) t I hI]
  simp only [heightCoeff,child_ideal_primary η χ I hI]
  ring

theorem exists_second_family_presentation (η : Character) (χ : RayCharacter)
    (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤ rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      (∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) fixedBadMask 1 A
    fixedBadMask_ne_zero one_ne_zero hA (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨τ,hN,hτ,fun I hI t => row_presentation_height η τ χ A hτ I hI t⟩

theorem row_presentation_twist (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (z n : O) :
    rowTwist (elementHom τ) fixedBadMask 1 z n=
      rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hc : coprimalityMask fixedBadMask n=1 := by
      change (if IsCoprime fixedBadMask n then (1:ℂ) else 0)=1
      rw [ite_eq_left (fixedBadMask_coprime n hn)]
    have ht := hτ n
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn] at ht
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn,rowTwist_extract_sixth_mask _ _ _ _ n hn]
    change elementCoeff τ n*coprimalityMask fixedBadMask n*idealRowHom (1^4*z) (Ideal.span {n})=_
    rw [ht,hc]
    simp only [one_pow,one_mul,mul_one,idealRowHom_argument_mul]
    ring
  · have hmLam : ConcretePrimeRowBridge.goodLambda∣fixedBadMask := dvd_mul_right _ _
    have hm2 : (2:O)∣fixedBadMask := dvd_mul_left _ _
    exact (rowTwist_zero_of_not_supported (elementHom τ) fixedBadMask 1 z n hmLam hm2 hn).trans
      (rowTwist_zero_of_not_supported (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n hmLam hm2 hn).symm

theorem fixedInducingRow_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    FixedInducingRow τ Q fixedBadMask 1 z ↔
      FixedInducingRow (childCharacter η χ) Q fixedBadMask A z := by
  unfold FixedInducingRow
  simp only [one_mul,row_presentation_twist η τ χ A hτ]

theorem nonexceptional_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    nonexceptional η χ Q fixedBadMask A z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [nonexceptional,fixedInducingRow_transport η τ χ A hτ Q z]

end SevenEighths.CenteredMomentSecondFamilyTransport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondNonexceptional -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptional
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentSecondScaled CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem whole_kernel_nonexceptional_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η₀ : HeckeFamily.Character) (χ₀ : RayCharacter)
        (Q : Ideal O) (m : O),
      (Q ≤ Ideal.span {(72:O)}) → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ z ∈ rows, nonexceptional η₀ χ₀ Q m A₀ z) →
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ χ Q m A₀) S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K) ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ ξ Q m A₀) T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K) ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_restricted_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x η₀ χ₀ Q m hQ hmLam hm2 hrows hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z))
    (nonexceptional η₀ χ Q m A₀) (nonexceptional η₀ (ξ⁻¹) Q m A₀)
    (fun z hz => (nonexceptional_ray_independent η₀ χ₀ χ Q hQ m A₀ z hmLam hm2).mp (hrows z hz))
    (fun z hz => (nonexceptional_reflection η₀ χ₀ (ξ⁻¹) Q hQ m A₀ z hmLam hm2).mp (hrows z hz)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondNonexceptional

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SectorLocalization -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2-2*x)

theorem cutoff_one (x : ℝ) (hx : x ≤ 1/2) : cutoff x=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_zero (x : ℝ) (hx : 1 ≤ x) : cutoff x=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

def annulus (x : ℝ) : ℝ := cutoff x-cutoff (2*x)

theorem annulus_zero_low (x : ℝ) (hx : x ≤ 1/4) : annulus x=0 := by
  rw [annulus, cutoff_one x (by linarith),cutoff_one (2*x) (by linarith),sub_self]

theorem annulus_zero_high (x : ℝ) (hx : 1 ≤ x) : annulus x=0 := by
  rw [annulus,cutoff_zero x hx,cutoff_zero (2*x) (by linarith),sub_self]

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem annulus_smooth : ContDiff ℝ ∞ annulus := by
  have hc : ContDiff ℝ ∞ cutoff :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact hc.sub (hc.comp (contDiff_const.mul contDiff_id))

def dyadicScale (n : ℤ) : ℝ := (2:ℝ)^n

theorem dyadicScale_pos (n : ℤ) : 0 < dyadicScale n := by
  unfold dyadicScale
  positivity

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

def dyadicWeight (n : ℤ) (q : ℝ) : ℝ := annulus (q/dyadicScale n)

theorem dyadicWeight_smooth (n : ℤ) : ContDiff ℝ ∞ (dyadicWeight n) :=
  annulus_smooth.comp (contDiff_id.div_const _)

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_zero_low (n : ℤ) (q : ℝ) (hq : q ≤ dyadicScale n/4) :
    dyadicWeight n q=0 := by
  apply annulus_zero_low
  apply (div_le_iff₀ (dyadicScale_pos n)).mpr
  linarith

theorem dyadicWeight_zero_high (n : ℤ) (q : ℝ) (hq : dyadicScale n ≤ q) :
    dyadicWeight n q=0 := by
  apply annulus_zero_high
  exact (le_div_iff₀ (dyadicScale_pos n)).mpr (by simpa using hq)

theorem dyadicWeight_support (n : ℤ) :
    Function.support (dyadicWeight n) ⊆ Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  intro q hq
  constructor
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_low n q h))
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_high n q h))

theorem dyadicWeight_tsupport (n : ℤ) :
    tsupport (dyadicWeight n) ⊆ Set.Icc (dyadicScale n/4) (dyadicScale n) :=
  closure_minimal (fun _ h => Set.Ioo_subset_Icc_self (dyadicWeight_support n h)) isClosed_Icc

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_finite (q : ℝ) : (Function.support (fun n => dyadicWeight n q)).Finite := by
  by_cases hq : 0 < q
  · obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
    apply (Set.toFinite (({k+1,k+2} : Finset ℤ) : Set ℤ)).subset
    intro n hn
    by_contra hh
    exact hn (dyadicWeight_outside_pair q k hlo hhi n hh)
  · have hz : ∀ n,dyadicWeight n q=0 := fun n =>
      dyadicWeight_zero_low n q ((le_of_not_gt hq).trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))
    simp [hz]

theorem dyadicWeight_summable (q : ℝ) : Summable (fun n => dyadicWeight n q) :=
  summable_of_hasFiniteSupport (dyadicWeight_finite q)

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

def Retained (R : ℝ) (n : ℤ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q ≤ R ∧ q ∈ tsupport (dyadicWeight n)

def retainedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then dyadicWeight n q else 0

def discardedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then 0 else dyadicWeight n q

theorem retained_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then dyadicWeight n q else 0) :=
  (dyadicWeight_summable q).indicator {n | Retained R n}

theorem discarded_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then 0 else dyadicWeight n q) := by
  have h := (dyadicWeight_summable q).sub (retained_summable R q)
  convert h using 1
  ext n
  split_ifs <;> simp

theorem retained_add_discarded (R q : ℝ) (hq : 0 < q) :
    retainedWeight R q+discardedWeight R q=1 := by
  rw [retainedWeight,discardedWeight,← (retained_summable R q).tsum_add (discarded_summable R q)]
  convert dyadicWeight_partition q hq using 1
  apply tsum_congr
  intro n
  split_ifs <;> simp

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem discardedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : discardedWeight R q=0 := by
  simp [discardedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_nonneg (R q : ℝ) : 0 ≤ retainedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact (dyadicWeight_bounds n q).1
  · exact le_rfl

theorem discardedWeight_nonneg (R q : ℝ) : 0 ≤ discardedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact (dyadicWeight_bounds n q).1

theorem retainedWeight_bounds (R q : ℝ) : 0 ≤ retainedWeight R q ∧ retainedWeight R q ≤ 1 := by
  refine ⟨retainedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := discardedWeight_nonneg R q
    linarith
  · rw [retainedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_bounds (R q : ℝ) : 0 ≤ discardedWeight R q ∧ discardedWeight R q ≤ 1 := by
  refine ⟨discardedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := retainedWeight_nonneg R q
    linarith
  · rw [discardedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem retained_scale_le (R : ℝ) (n : ℤ) (hn : Retained R n) : dyadicScale n ≤ 4*R := by
  obtain ⟨q,hq,hqR,hs⟩ := hn
  have hb := (dyadicWeight_tsupport n hs).1
  linarith

theorem retainedWeight_zero_above (R q : ℝ) (hq : 4*R ≤ q) : retainedWeight R q=0 := by
  unfold retainedWeight
  trans ∑' _n : ℤ, (0:ℝ)
  · apply tsum_congr
    intro n
    split_ifs with hn
    · exact dyadicWeight_zero_high n q ((retained_scale_le R n hn).trans hq)
    · rfl
  · exact tsum_zero

theorem retainedWeight_enclosure (R q : ℝ) (hq : retainedWeight R q ≠ 0) : 0 < q ∧ q ≤ 4*R := by
  constructor
  · exact lt_of_not_ge (fun h => hq (retainedWeight_zero_nonpos R q h))
  · exact le_of_not_gt (fun h => hq (retainedWeight_zero_above R q h.le))

theorem discardedWeight_zero_below (R q : ℝ) (hq : q ≤ R) : discardedWeight R q=0 := by
  by_cases hp : 0 < q
  · unfold discardedWeight
    trans ∑' _n : ℤ, (0:ℝ)
    · apply tsum_congr
      intro n
      split_ifs with hn
      · rfl
      · by_contra hne
        exact hn ⟨q,hp,hq,subset_tsupport _ hne⟩
    · exact tsum_zero
  · exact discardedWeight_zero_nonpos R q (le_of_not_gt hp)

theorem discardedWeight_support (R q : ℝ) (hq : discardedWeight R q ≠ 0) : R < q :=
  lt_of_not_ge (fun h => hq (discardedWeight_zero_below R q h))

theorem retainedWeight_one_below (R q : ℝ) (hq : 0 < q) (hR : q ≤ R) : retainedWeight R q=1 := by
  have h := retained_add_discarded R q hq
  rwa [discardedWeight_zero_below R q hR,add_zero] at h

theorem finite_retained_integral_dyads (R : ℝ) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, 1 ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc (1:ℤ) (k:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have : (2:ℝ)^(0:ℤ) < (2:ℝ)^n := by simpa [dyadicScale] using hq.trans_lt hs
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp this
    omega
  · have h : (2:ℝ)^n < (2:ℝ)^(k:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hk
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
    omega

theorem annulus_pos (x : ℝ) (hlo : 1/4 < x) (hhi : x < 1) : 0 < annulus x := by
  by_cases hx : x ≤ 1/2
  · rw [annulus,cutoff_one x hx]
    have h := Real.smoothTransition.lt_one_of_lt_one (by linarith : 2-2*(2*x) < 1)
    exact sub_pos.mpr h
  · rw [annulus,cutoff_zero (2*x) (by linarith),sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith)

theorem dyadicWeight_support_eq (n : ℤ) :
    Function.support (dyadicWeight n)=Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  apply Set.Subset.antisymm (dyadicWeight_support n)
  intro q hq
  apply ne_of_gt
  apply annulus_pos
  · apply (lt_div_iff₀ (dyadicScale_pos n)).mpr
    linarith [hq.1]
  · exact (div_lt_one (dyadicScale_pos n)).mpr hq.2

theorem dyadicWeight_tsupport_eq (n : ℤ) :
    tsupport (dyadicWeight n)=Set.Icc (dyadicScale n/4) (dyadicScale n) := by
  rw [tsupport,dyadicWeight_support_eq,closure_Ioo]
  linarith [dyadicScale_pos n]

theorem retained_iff_scale (R : ℝ) (n : ℤ) : Retained R n ↔ dyadicScale n ≤ 4*R := by
  refine ⟨retained_scale_le R n,fun hn => ?_⟩
  refine ⟨dyadicScale n/4,div_pos (dyadicScale_pos n) (by norm_num),by linarith,?_⟩
  rw [dyadicWeight_tsupport_eq]
  exact ⟨le_rfl,by linarith [dyadicScale_pos n]⟩

theorem retained_boundary (n : ℤ) : Retained (dyadicScale n/4) n := by
  rw [retained_iff_scale]
  linarith

def normValue (h : O) : ℝ := Ideal.absNorm (Ideal.span {h})

theorem normValue_eq_embedding (h : O) : normValue h=‖eisEmbedding h‖^2 :=
  (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span h).symm

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem retained_pullback (R : ℝ) (v h : O) :
    retainedWeight R (normValue (v*h))=retainedWeight R (normValue v*normValue h) := by
  rw [normValue_mul]

theorem retained_norm_enclosure (R : ℝ) (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : normValue h ≤ 4*R/normValue v := by
  have hb := (retainedWeight_enclosure R _ hne).2
  rw [normValue_mul] at hb
  apply (le_div_iff₀ (normValue_pos v hv)).mpr
  nlinarith

def frequencyRadius (Tsec Z ξ : ℝ) : ℝ := Tsec*Z^(ξ/2)

def frequencyLoss (Z Csec ξ : ℝ) : ℝ := ξ/2+Real.logb Z (4*Csec)

theorem frequencyLoss_nonneg (Z Csec ξ : ℝ) (hZ : 1 < Z) (hC : 1 ≤ Csec) (hξ : 0 ≤ ξ) :
    0 ≤ frequencyLoss Z Csec ξ := by
  have hlog := Real.logb_nonneg hZ (show 1 ≤ 4*Csec by linarith)
  unfold frequencyLoss
  linarith

theorem source_enclosure_power (Z Csec L ξ Nv : ℝ) (hZ : 1 < Z) (hC : 0 < Csec) (hNv : 0 < Nv) :
    4*(Csec*Z^L)*Z^(ξ/2)/Nv=Z^(L-Real.logb Z Nv+frequencyLoss Z Csec ξ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [frequencyLoss,show L-Real.logb Z Nv+(ξ/2+Real.logb Z (4*Csec))=
    (L+ξ/2)+Real.logb Z (4*Csec)-Real.logb Z Nv by ring,
    Real.rpow_sub hz,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz (ne_of_gt hZ),Real.rpow_logb hz (ne_of_gt hZ)]
  · ring
  · exact hNv
  · positivity

theorem actual_retained_row_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ) := by
  have hb := retained_norm_enclosure (frequencyRadius Tsec Z ξ) v h hv hne
  apply hb.trans
  rw [← source_enclosure_power Z Csec L ξ (normValue v) hZ hC (normValue_pos v hv)]
  apply div_le_div_of_nonneg_right _ (normValue_pos v hv).le
  dsimp only [frequencyRadius]
  nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]

theorem actual_nonempty_width (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  have he := (normValue_ge_one h hh).trans (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hne)
  by_contra hn
  have hh := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hn)
  linarith

theorem actual_declared_width_drop (Tsec Z Csec L ξ M J g g₂ t₂ σ q' : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0)
    (hwidth : (L-Real.logb Z (normValue v))+q'=M+J-g-g₂+t₂)
    (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂) :
    max 0 (L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)+q' ≤
      M-σ+frequencyLoss Z Csec ξ :=
  CenteredMomentDescentLedger.declared_width_drop M J g g₂ t₂ σ _ q' _ hwidth hg hcommon
    (actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne)

theorem retained_first_dyad_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n) ≤ L+frequencyLoss Z Csec ξ := by
  have hb := retained_scale_le _ n hn
  have hp := source_enclosure_power Z Csec L ξ 1 hZ hC (by norm_num)
  simp only [Real.logb_one,sub_zero,div_one] at hp
  have he : dyadicScale n ≤ Z^(L+frequencyLoss Z Csec ξ) := by
    rw [← hp]
    dsimp only [frequencyRadius] at hb
    nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]
  have hl := Real.logb_le_logb_of_le hZ (dyadicScale_pos n) he
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hl

def kernelReference (Tsec H : ℝ) : ℝ := Real.exp (-2*H)/Tsec

theorem kernelReference_pos (Tsec H : ℝ) (hT : 0 < Tsec) : 0 < kernelReference Tsec H :=
  div_pos (Real.exp_pos _) hT

theorem frequencyLoss_lt (Z Csec H ξ : ℝ) (hZ : 1 < Z) (hH : 0 ≤ H) (hξ : 0 < ξ)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) :
    frequencyLoss Z Csec ξ < ξ := by
  have h := div_nonneg (show 0 ≤ 2*H by linarith) (Real.log_pos hZ).le
  unfold frequencyLoss Real.logb
  linarith

theorem discarded_kernel_argument (Tsec Z Csec H ξ q : ℝ)
    (hT : 0 < Tsec) (hZ : 1 < Z) (hC : 1 ≤ Csec)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4)
    (hne : discardedWeight (frequencyRadius Tsec Z ξ) q ≠ 0) :
    Z^(ξ/4) ≤ kernelReference Tsec H*q := by
  have hlog := Real.log_nonneg (show 1 ≤ 4*Csec by linarith)
  have hlogdiv := div_nonneg hlog (Real.log_pos hZ).le
  have he : 2*H < ξ/4*Real.log Z :=
    (div_lt_iff₀ (Real.log_pos hZ)).mp (by linarith : 2*H/Real.log Z < ξ/4)
  have hs : Z^(ξ/4) ≤ Real.exp (-2*H)*Z^(ξ/2) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ),Real.rpow_def_of_pos (zero_lt_one.trans hZ),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hq := (discardedWeight_support _ q hne).le
  have hm := mul_le_mul_of_nonneg_left hq (kernelReference_pos Tsec H hT).le
  have hid : kernelReference Tsec H*frequencyRadius Tsec Z ξ=Real.exp (-2*H)*Z^(ξ/2) := by
    unfold kernelReference frequencyRadius
    field_simp
  rw [hid] at hm
  exact hs.trans hm

theorem retained_pullback_zero_extension (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) :
    retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) =
      if normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)
      then retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) else 0 := by
  split_ifs with hb
  · rfl
  · by_contra hn
    exact hb (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hn)

theorem actual_discarded_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K B : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*
        paperRadialFourier W (K*normValue h)‖ ≤
      B*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := CenteredMomentTail.uniform_sector_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K B hT hZ hCsec hthreshold hK hB c hc
  let D : Set O := {h | discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0}
  have hb := ht W D (kernelReference Tsec H) (Z^(ξ/4)) B
    (kernelReference_pos Tsec H hT) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hB
    (fun h hh => by
      rw [← normValue_eq_embedding]
      exact discarded_kernel_argument Tsec Z Csec H ξ (normValue h) hT hZ hCsec hthreshold hh)
    K hK c (fun h => (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ))
    (fun h _ => hc h) (fun h _ => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg _ _)]
      exact (discardedWeight_bounds _ _).2)
  simp_rw [← normValue_eq_embedding] at hb
  have he := tsum_subtype_eq_of_support_subset (f := fun h : O =>
    (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*paperRadialFourier W (K*normValue h))
    (s := D) (by
      intro h hh
      change discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0
      intro hz
      exact hh (by simp [hz]))
  rwa [he] at hb

theorem actual_discarded_second_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        CenteredMomentSupportedCorrelation.actualCorrelation u v hu hv (-h)*
        paperRadialFourier W (K*normValue h)‖ ≤
      (normValue u*normValue v)*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK u v hu hv
  exact ht W Tsec Z Csec H ξ K (normValue u*normValue v) hT hZ hCsec hthreshold hK
    (by unfold normValue; positivity) _ (fun h => CenteredMomentTail.actualCorrelation_norm_le u v hu hv (-h))

theorem actual_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
        (_hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ)
        (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ),
      let r := CenteredMomentInitial.activeModulus P B c d
      let χr := CenteredMomentInitial.commonCharacter P hinj hg B c d
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        (normalizedResidueGauss r (CenteredMomentInitial.activeModulus_ne_zero P B c d) χr
            (Ideal.Quotient.mk _ h)*
          (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h)/
            (Real.sqrt (normValue a):ℂ))*
          star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h))/
            (Real.sqrt (normValue b):ℂ)))*paperRadialFourier W (K*normValue h)‖ ≤
      (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK ι P _ hinj hg hchar B c d a b ha hb χa χb
  dsimp only
  simpa only [one_mul] using ht W Tsec Z Csec H ξ K 1 hT hZ hCsec hthreshold hK zero_le_one _ (by
    intro h
    rw [norm_mul,norm_mul,norm_star]
    calc
      _ ≤ (1*1)*1 := mul_le_mul
        (mul_le_mul (CenteredMomentInitial.common_gauss_norm_le_one P hinj hg hchar B c d h)
          (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one a ha χa _)
          (norm_nonneg _) zero_le_one)
        (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one b hb χb _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num)

theorem retained_product_ne_zero (R : ℝ) (v h : O)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : v ≠ 0 ∧ h ≠ 0 := by
  have hp := (retainedWeight_enclosure R _ hne).1
  constructor <;> intro hz <;> simp [hz,normValue] at hp

theorem actual_nonempty_width_of_weight (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L) (v h : O)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  obtain ⟨hv,hh⟩ := retained_product_ne_zero _ v h hne
  exact actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne

theorem actual_second_pullback (R : ℝ) (Gc V h : O) :
    retainedWeight R (normValue ((Gc*V)*h))=
      retainedWeight R ((normValue Gc*normValue V)*normValue h) := by
  simp only [normValue_mul]

theorem retained_integral_empty (R : ℝ) (hR : 4*R < 1) (h : O) :
    retainedWeight R (normValue h)=0 := by
  by_contra hn
  have hh : h ≠ 0 := by
    intro hz
    subst h
    exact hn (by simpa [normValue] using retainedWeight_zero_nonpos R 0 le_rfl)
  have hb := (retainedWeight_enclosure R _ hn).2
  linarith [normValue_ge_one h hh]

theorem finite_retained_above (R a : ℝ) (ha : 0 < a) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, a ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk,_⟩ := exists_mem_Ico_zpow ha (by norm_num : (1:ℝ) < 2)
  obtain ⟨l,hl⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc k (l:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have h : (2:ℝ)^k < (2:ℝ)^n := hk.trans_lt (hq.trans_lt hs)
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le
  · have h : (2:ℝ)^n < (2:ℝ)^(l:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hl
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le

theorem retainedWeight_finite_formula (R a : ℝ) (ha : 0 < a) :
    ∃ S : Finset ℤ, ∀ q : ℝ, a ≤ q →
      retainedWeight R q=∑ n ∈ S, if Retained R n then dyadicWeight n q else 0 := by
  let hs := finite_retained_above R a ha
  refine ⟨hs.toFinset,fun q hq => ?_⟩
  apply tsum_eq_sum
  intro n hn
  split_ifs with hr
  · by_contra hne
    exact hn (hs.mem_toFinset.mpr ⟨hr,q,hq,hne⟩)
  · rfl

theorem retainedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (retainedWeight R) q := by
  obtain ⟨S,hS⟩ := retainedWeight_finite_formula R (q/2) (by linarith)
  have hc : ContDiff ℝ ∞ (fun x : ℝ => ∑ n ∈ S, if Retained R n then dyadicWeight n x else 0) := by
    apply ContDiff.sum
    intro n hn
    by_cases hr : Retained R n
    · simpa [hr] using dyadicWeight_smooth n
    · simpa [hr] using (contDiff_const : ContDiff ℝ ∞ (fun _x : ℝ => (0:ℝ)))
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show q/2 < q by linarith)] with x hx
  exact hS x hx.le

theorem discardedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (discardedWeight R) q := by
  have hc : ContDiffAt ℝ ∞ (fun x => (1:ℝ)-retainedWeight R x) q :=
    contDiffAt_const.sub (retainedWeight_smooth_positive R q hq)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  have he := retained_add_discarded R x hx
  linarith

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DyadicCount -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

def indices (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈Real.logb 2 a⌉ ⌊Real.logb 2 (4*b)⌋

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0<a) (hb : 0<b) (n : ℤ) :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma mem_indices_iff_whole_support (a b : ℝ) (ha : 0<a) (hab : a≤b) (n : ℤ) :
    n∈indices a b ↔ ∃q∈Icc a b,q∈tsupport (dyadicWeight n) := by
  rw [mem_indices_iff_scale a b ha (ha.trans_le hab) n]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨max a (dyadicScale n/4),⟨le_max_left _ _,max_le hab (by linarith)⟩,?_⟩
    rw [dyadicWeight_tsupport_eq]
    exact ⟨le_max_right _ _,max_le hlo (by linarith [dyadicScale_pos n])⟩
  · rintro ⟨q,hq,hq'⟩
    have hh := dyadicWeight_tsupport n hq'
    exact ⟨hq.1.trans hh.2,by linarith [hq.2,hh.1]⟩

lemma support_indices (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b)
    (n : ℤ) (hne : dyadicWeight n q≠0) : n∈indices a b :=
  (mem_indices_iff_whole_support a b ha (hq.1.trans hq.2) n).mpr
    ⟨q,hq,subset_tsupport _ hne⟩

lemma finite_active_indices (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    {n : ℤ | ∃q∈Icc a b,q∈tsupport (dyadicWeight n)}.Finite := by
  apply (indices a b).finite_toSet.subset
  intro n hn
  exact (mem_indices_iff_whole_support a b ha hab n).mpr hn

lemma logb_four_mul (b : ℝ) (hb : 0<b) :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indices_card_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

theorem scaled_indices_card_bound (a b T : ℝ) (ha : 0<a) (hab : a≤b) (hT : 0<T) :
    ((indices (a/T) (b/T)).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have h := indices_card_bound (a/T) (b/T) (div_pos ha hT)
    (div_le_div_of_nonneg_right hab hT.le)
  have he : (b/T)/(a/T)=b/a := by field_simp
  rwa [he] at h

lemma dyadic_partition_on_interval (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b) :
    (∑n∈indices a b,dyadicWeight n q)=1 := by
  rw [←dyadicWeight_partition q (ha.trans_le hq.1)]
  symm
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  exact hn (support_indices a b q ha hq n hne)

theorem four_indices_card_bound (a b : Fin 4→ℝ)
    (ha : ∀j,0<a j) (hab : ∀j,a j≤b j) :
    (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤
      ∏j:Fin 4,(3+Real.logb 2 (b j/a j)) := by
  rw [Fintype.card_pi]
  push_cast
  apply Finset.prod_le_prod₀
  · intro j hj
    positivity
  · intro j hj
    simpa only [Fintype.card_coe] using indices_card_bound (a j) (b j) (ha j) (hab j)

lemma retained_integral_mem (R q : ℝ) (hq : 1≤q) (n : ℤ)
    (hr : Retained R n) (hne : dyadicWeight n q≠0) :
    n∈indices 1 (max 1 R) := by
  rw [mem_indices_iff_scale 1 (max 1 R) (by norm_num) (by positivity) n]
  exact ⟨hq.trans (dyadicWeight_support n hne).2.le,
    (retained_scale_le R n hr).trans (by linarith [le_max_right (1:ℝ) R])⟩

theorem indices_card_log_bound (C R Z a b : ℝ) (hC : 1≤C) (hR : 0≤R)
    (hZ : 1≤Z) (ha : 0<a) (hab : a≤b) (hratio : b/a≤C*Z^R) :
    ((indices a b).card:ℝ)≤
      (3+Real.logb 2 C+R/Real.log 2)*(1+Real.log Z) := by
  have hb := ha.trans_le hab
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (div_pos hb ha) hratio
  rw [Real.logb_mul hCp.ne' (Real.rpow_pos_of_pos hZp R).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hZp] at hlog
  apply (indices_card_bound a b ha hab).trans
  have hc0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
  have hz0 := Real.log_nonneg hZ
  have hr0 : 0≤R/Real.log 2 := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hp := mul_nonneg (show 0≤3+Real.logb 2 C by linarith) hz0
  have he : R*Real.logb 2 Z=(R/Real.log 2)*Real.log Z := by unfold Real.logb;ring
  rw [he] at hlog
  nlinarith

theorem four_indices_subpower (C R ε : ℝ) (hC : 1≤C) (hR : 0≤R) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ∀a b : Fin 4→ℝ,(∀j,0<a j) → (∀j,a j≤b j) →
      (∀j,b j/a j≤C*Z^R) →
      (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤D*Z^ε := by
  let K : ℝ := 3+Real.logb 2 C+R/Real.log 2
  have hK : 0<K := by
    have hc := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
    have hr := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [K]
    linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨16*K^4,by positivity,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop (Real.exp 1),Filter.eventually_ge_atTop (1:ℝ)] with Z hlog hZexp hZ
  intro a b ha hab hratio
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hz : 1≤Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^4≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZp.le _),one_mul] using hlog
  have hcard : (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤(K*(1+Real.log Z))^4 := by
    rw [Fintype.card_pi]
    push_cast
    calc
      _ ≤ ∏j:Fin 4,K*(1+Real.log Z) := by
        apply Finset.prod_le_prod₀ (by intros;positivity)
        intro j hj
        simpa only [Fintype.card_coe] using indices_card_log_bound C R Z (a j) (b j) hC hR hZ (ha j) (hab j) (hratio j)
      _ = _ := by simp
  calc
    _ ≤ (K*(1+Real.log Z))^4 := hcard
    _ ≤ (K*(2*Real.log Z))^4 := by gcongr;linarith
    _ = (16*K^4)*(Real.log Z)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentDyadicCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssembly -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis" => ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

abbrev Windows (a b : Fin 4→ℝ) := ∀ i:Fin 4,↥(indices (a i) (b i))

def exponent (Z:ℝ) (k:ℤ) : ℝ := Real.logb Z (dyadicScale k)

def cutoff : Fin 4→ℝ→ℂ := fun _ y=>(annulus y:ℂ)

def weight (k:Fin 4→ℤ) (q:Fin 4→ℝ) : ℂ :=
  ∏i:Fin 4,(dyadicWeight (k i) (q i):ℂ)

theorem exponent_scale (Z:ℝ) (hZ:1<Z) (k:ℤ) :
    Z^(exponent Z k)=dyadicScale k :=
  Real.rpow_logb (by positivity) (ne_of_gt hZ) (dyadicScale_pos k)

theorem weight_partition (a b q:Fin 4→ℝ) (ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    (∑k:Windows a b,weight (fun i=>(k i).val) q)=1 := by
  unfold weight
  rw [←Fintype.prod_sum (fun (i:Fin 4) (k:↥(indices (a i) (b i)))=>(dyadicWeight k.val (q i):ℂ))]
  have he (i:Fin 4) : (∑k:↥(indices (a i) (b i)),(dyadicWeight k.val (q i):ℂ))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun k=>(dyadicWeight k (q i):ℂ))]
    exact_mod_cast dyadic_partition_on_interval (a i) (b i) (q i) (ha i) (hq i)
  simp only [he,Finset.prod_const_one]

theorem weight_eq_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ) (q:Fin 6→ℝ) :
    weight k (fun i=>q (outerIndex i)) =
      outerCutoff cutoff (relativeNorm q Z D (exponent Z (k 0))
        (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))) := by
  simp [weight,Fin.prod_univ_succ,dyadicWeight,outerIndex,outerCutoff,cutoff,
    relativeNorm,secondRelativeNorm,exponent_scale Z hZ,mul_assoc]

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceNorms (x:Source (ι:=ι) 0) : Fin 4→ℝ :=
  fun i=>coordinates p (sourcePoint x ∅ ∅) (outerIndex i)

omit [DecidableEq ι] in
theorem source_weight_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ)
    (x:Source (ι:=ι) 0) :
    weight k (sourceNorms p x)=outerCutoff cutoff
      (sourceRelative p x Z D (exponent Z (k 0)) (exponent Z (k 2))
        (exponent Z (k 1)) (exponent Z (k 3))) :=
  weight_eq_cutoff Z D hZ k _

omit [DecidableEq ι] in
theorem sourceNorms_one_le (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal] (x:Source (ι:=ι) 0)
    (hf:x.frequency≠0) : ∀i,1≤ sourceNorms p x i := by
  have hi (I:Ideal Eis) (hI:I≠0) : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · change 1≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hi _ (by change Ideal.span {x.frequency}≠⊥; exact Ideal.span_singleton_eq_bot.not.mpr hf)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*weight (fun i=>(k i).val) (sourceNorms p x))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨s,hsS,hx⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply,erase_sourcePoint]
  rw [←Finset.sum_mul,←Finset.mul_sum,weight_partition a b _ ha (hs s hsS),mul_one]

theorem physicalBlock_window_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg
      (pointSource pool (windowSource p S cutoff Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))
      ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  rw [physicalBlock_partition p hp hcop hg pool S a b ha hs]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [source_weight_cutoff p Z D hZ]
  exact physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m w Ψ j marks W₁ W₂ Φ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyBounds -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

theorem windows_card_log (a b:Fin 4→ℝ)(ha:∀i,0<a i)(hab:∀i,a i≤b i) :
    (Fintype.card (Windows a b):ℝ)≤∏i:Fin 4,(3+Real.logb 2 (b i/a i)) :=
  four_indices_card_bound a b ha hab

theorem windows_card_subpower (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀a b:Fin 4→ℝ,(∀i,0<a i)→(∀i,a i≤b i)→(∀i,b i/a i≤C*Z^R)→
        (Fintype.card (Windows a b):ℝ)≤A*Z^ε :=
  four_indices_subpower C R ε hC hR hε

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def windowBlock (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(k:Fin 4→ℤ) : ℂ :=
  physicalBlock p hp hcop hg
    (pointSource pool (windowSource p S cutoff Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))
    ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))∘erasePoint)
    Ψ j marks W₁ W₂ Φ Z D m

theorem physicalBlock_norm_le_windows
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (E:ℝ)(hblock:∀k:Windows a b,
      ‖windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m
        (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_window_partition p hp hcop hg pool S a b ha hs w Ψ j marks W₁ W₂ Φ Z D m hZ]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k:Windows a b,E := Finset.sum_le_sum (fun k hk=>hblock k)
    _ = _ := by simp

omit p hp hcop hg [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in

theorem physicalBlock_uniform_subpower
    (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀{κ:Type*}[DecidableEq κ](p:κ→Eis)(hp:∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
        (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
        (pool:Finset κ)(S:Finset (Source (ι:=κ) 0))
        (a b:Fin 4→ℝ),(∀i,0<a i)→(∀i,a i≤b i)→
        (∀i,b i/a i≤C*Z^R)→
        (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))→
      ∀(w:Source (ι:=κ) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset κ→ℂ)
        (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(D m E:ℝ),0≤E→
        (∀k:Windows a b,‖windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m
          (fun i=>(k i).val)‖≤E)→
        ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
          Ψ j marks W₁ W₂ Φ Z D m‖≤A*Z^ε*E := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower C R ε hC hR hε
  refine ⟨A,hA,?_⟩
  filter_upwards [hcount,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro κ _ p hp _ hcop hg pool S a b ha hab hr hs w Ψ j marks W₁ W₂ Φ D m E hE hb
  exact (physicalBlock_norm_le_windows p hp hcop hg pool S a b ha hs w Ψ j marks W₁ W₂ Φ Z D m hZ E hb).trans
    (mul_le_mul_of_nonneg_right (hc a b ha hab hr) hE)

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyLive -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def cappedSource (S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>∀i,sourceNorms p x i∈Set.Icc (a i) (b i))

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_cap_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (cappedSource p S a b))
      (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,cappedSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    simp only [Function.comp_apply,erase_sourcePoint]
    by_contra hn
    exact hb (hcap x hx N hN M hM ρ hn)

theorem physicalBlock_live_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_window_partition p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ

theorem physicalBlock_live_norm
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (E:ℝ)(he:∀k:Windows a b,‖windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_norm_le_windows p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ E he

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblySourceCaps -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem sourceNorms_fresh (x:Source (ι:=ι) 0)(N M:Finset ι)(i:Fin 4) :
    sourceNorms p x i=coordinates p (sourcePoint x N M) (outerIndex i) := by
  fin_cases i <;> simp only [sourceNorms,coordinates,sourcePoint,physicalCoordinates,
    outerIndex,Fin.castLE,Matrix.cons_val_zero',Matrix.cons_val_succ']

def physicalCaps (b Z D T:ℝ) : Fin 4→ℝ := ![b*Z^D,b*Z^D,b*Z^D,T]

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_live_caps
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T:ℝ)(hZ:0<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T)
    (x:Source (ι:=ι) 0)(hx:x∈S)(N:Finset ι)(hN:N∈(pool\x.overlap).powerset)
    (M:Finset ι)(hM:M∈(pool\x.overlap).powerset)(ρ:SecondRayIndex)
    (hn:w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m (sourcePoint x N M) ρ≠0) :
    ∀i,sourceNorms p x i∈Set.Icc 1 (physicalCaps b Z D T i) := by
  have hpnt:sourcePoint x N M∈pointSource pool S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    exact Finset.mem_image.mpr ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
  have hv:=pointSource_valid pool S hdiv hf _ hpnt
  have hc:=InverseInitialRetainedSupport.live_ideal_caps p hp hcop hg hpr Ψ j marks W₁ W₂ Φ
    Z D m b hZ hW₁ hW₂ (sourcePoint x N M) hv ρ (mul_ne_zero_iff.mp hn).2
  intro i
  refine ⟨sourceNorms_one_le p hp x (hf x hx) i,?_⟩
  fin_cases i
  · change sourceNorms p x 0≤b*Z^D
    rw [sourceNorms_fresh p x N M 0]
    exact hc.1
  · change sourceNorms p x 1≤b*Z^D
    rw [sourceNorms_fresh p x N M 1]
    exact hc.2.1
  · change sourceNorms p x 2≤b*Z^D
    rw [sourceNorms_fresh p x N M 2]
    exact hc.2.2.1
  · exact hT x hx

theorem actual_physical_partition
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows (fun _=>1) (physicalCaps b Z D T),
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  exact physicalBlock_live_partition p hp hcop hg pool S (fun _=>1) (physicalCaps b Z D T)
    (by intro i; norm_num) w Ψ j marks W₁ W₂ Φ Z D m hZ
    (actual_live_caps p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ Z D m b T
      (by linarith) hW₁ hW₂ hT)

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyWindows -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff
namespace SevenEighths.InverseInitialDyadicAssembly
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

theorem cutoff_smooth (i:Fin 4) : ContDiff ℝ ∞ (cutoff i) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

theorem cutoff_norm_le (i:Fin 4)(x:ℝ) : ‖cutoff i x‖≤1 := by
  simpa only [cutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (annulus_bounds x).1] using (annulus_bounds x).2

theorem cutoff_support (i:Fin 4) :
    Function.support (cutoff i)⊆Set.Ioo (1/4:ℝ) 1 := by
  intro x hx
  have hn:annulus x≠0 := by simpa only [Function.mem_support,cutoff,ne_eq,Complex.ofReal_eq_zero] using hx
  exact ⟨lt_of_not_ge (fun h=>hn (annulus_zero_low x h)),
    lt_of_not_ge (fun h=>hn (annulus_zero_high x h))⟩

theorem cutoff_tsupport (i:Fin 4) :
    tsupport (cutoff i)⊆Set.Icc (1/4:ℝ) 1 :=
  closure_minimal (fun _ hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx)) isClosed_Icc

theorem cutoff_eventual_width (η:ℝ)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀i:Fin 4,
      tsupport (cutoff i)⊆Set.Icc (Z^(-η)) (Z^η) := by
  have ht:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro i x hx
  have hs:=cutoff_tsupport i hx
  have hlo:Z^(-η)≤(1/4:ℝ) := by
    rw [Real.rpow_neg (by positivity)]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) ht
  exact ⟨hlo.trans hs.1,hs.2.trans (by linarith)⟩

theorem window_exponent_nonneg (Z b:ℝ)(hZ:1<Z)(hb:0<b)
    (k:ℤ)(hk:k∈indices 1 b) : 0≤exponent Z k := by
  have hs:1≤dyadicScale k := ((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).1
  exact Real.logb_nonneg hZ hs

theorem window_exponent_eventual_upper (C η:ℝ)(_hC:0<C)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(b R:ℝ),0<b→b≤C*Z^R→
      ∀k:ℤ,k∈indices 1 b→exponent Z k∈Set.Icc 0 (R+η) := by
  have ht:∀ᶠZ:ℝ in atTop,4*C≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (4*C))
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro b R hb hbR k hk
  refine ⟨window_exponent_nonneg Z b hZ hb k hk,?_⟩
  have hs:=((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).2
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [exponent_scale Z hZ,Real.rpow_add (by positivity)]
  calc
    dyadicScale k≤4*b:=hs
    _≤4*(C*Z^R):=mul_le_mul_of_nonneg_left hbR (by norm_num)
    _=(4*C)*Z^R:=by ring
    _≤Z^η*Z^R:=mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (by positivity) _)
    _=Z^R*Z^η:=mul_comm _ _

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end

