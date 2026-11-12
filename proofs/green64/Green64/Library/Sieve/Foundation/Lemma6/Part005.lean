module

public import Green64.Library.Sieve.Foundation.Lemma6.Part004
public import Green64.Library.Sieve.Foundation.Lemma6.Part001
public import Green64.Library.Sieve.Foundation.LargeSieve.Part001
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

@[expose] public section

/-!
# Sieve / Foundation / Lemma6 / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma6.PairLargeSieve -/

section

/-
The character-large-sieve input for the prime-pair polynomial in equations
(19) and (20).  The first step is the uniqueness of the ordered product
`p₁ p₂` on Chen's prime-pair range.
-/

open Real
open scoped Classical

namespace Chen

theorem chenPair_fst_lt_snd
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x) : q.1 < q.2 := by
  have hqdata := (Finset.mem_filter.mp hq).2
  rcases hqdata with ⟨hq1p, hq2p, hq1lo, hq1hi, hq2lo, hq2hi⟩
  have hreal : (q.1 : ℝ) < q.2 :=
    hq1hi.trans_lt hq2lo
  exact_mod_cast hreal

theorem pairProduct_injective_on_chenPairs
    {x : ℕ} {q r : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hr : r ∈ chenPairs x)
    (hprod : q.1 * q.2 = r.1 * r.2) : q = r := by
  have hqdata := (Finset.mem_filter.mp hq).2
  have hrdata := (Finset.mem_filter.mp hr).2
  rcases hqdata with ⟨hq1p, hq2p, hq1lo, hq1hi, hq2lo, hq2hi⟩
  rcases hrdata with ⟨hr1p, hr2p, hr1lo, hr1hi, hr2lo, hr2hi⟩
  have hdiv : q.1 ∣ r.1 * r.2 := by
    rw [← hprod]
    exact dvd_mul_right q.1 q.2
  rcases hq1p.dvd_mul.mp hdiv with hdiv | hdiv
  · have hfirst : q.1 = r.1 :=
      (Nat.prime_dvd_prime_iff_eq hq1p hr1p).mp hdiv
    have hsecond : q.2 = r.2 := by
      exact Nat.mul_left_cancel hq1p.pos (by simpa only [hfirst] using hprod)
    exact Prod.ext hfirst hsecond
  · have hcross : q.1 = r.2 :=
      (Nat.prime_dvd_prime_iff_eq hq1p hr2p).mp hdiv
    have hother : q.2 = r.1 := by
      exact Nat.mul_left_cancel hq1p.pos (by
        calc
          q.1 * q.2 = r.1 * r.2 := hprod
          _ = q.1 * r.1 := by rw [hcross]; ring)
    have hqr := chenPair_fst_lt_snd hq
    have hrr := chenPair_fst_lt_snd hr
    omega

/-- Real lower endpoint `2^k x^(13/30)` of the `k`-th pair-product block. -/
noncomputable def lemma6PairDyadicScale (x k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (x : ℝ) ^ ((13 : ℝ) / 30)

/-- Integer lower endpoint used by the character large sieve. -/
noncomputable def lemma6PairLowerCutoff (x k : ℕ) : ℕ :=
  ⌊lemma6PairDyadicScale x k⌋₊

/-- Integer upper endpoint used by the character large sieve. -/
noncomputable def lemma6PairUpperCutoff (x k : ℕ) : ℕ :=
  ⌈lemma6PairDyadicScale x (k + 1)⌉₊

theorem lemma6PairLowerCutoff_le_upperCutoff (x k : ℕ) :
    lemma6PairLowerCutoff x k ≤ lemma6PairUpperCutoff x k := by
  have hxpow : 0 ≤ (x : ℝ) ^ ((13 : ℝ) / 30) :=
    Real.rpow_nonneg (by positivity) _
  have hlower :
      (lemma6PairLowerCutoff x k : ℝ) ≤ lemma6PairDyadicScale x k := by
    unfold lemma6PairLowerCutoff lemma6PairDyadicScale
    exact Nat.floor_le (by positivity)
  have hscale : lemma6PairDyadicScale x k ≤
      lemma6PairDyadicScale x (k + 1) := by
    unfold lemma6PairDyadicScale
    apply mul_le_mul_of_nonneg_right _ hxpow
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hupper : lemma6PairDyadicScale x (k + 1) ≤
      (lemma6PairUpperCutoff x k : ℝ) := by
    unfold lemma6PairUpperCutoff
    exact Nat.le_ceil _
  exact_mod_cast hlower.trans (hscale.trans hupper)

/-- Every admissible pair in block `k` has product in the integer interval
used for its character-large-sieve estimate. -/
theorem lemma6AdmissiblePairBlock_product_mem_Ioc
    {x m k : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ lemma6AdmissiblePairBlock x m k) :
    q.1 * q.2 ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
      (lemma6PairUpperCutoff x k) := by
  have hqpair : q ∈ lemma6PairBlock x k :=
    (Finset.mem_filter.mp hq).2
  have hqdata := (Finset.mem_filter.mp hqpair).2
  rw [Finset.mem_Ioc]
  constructor
  · apply (Nat.floor_lt (by
      unfold lemma6PairDyadicScale
      positivity)).2
    simpa only [lemma6PairDyadicScale] using hqdata.1
  · have hceil : lemma6PairDyadicScale x (k + 1) ≤
        (lemma6PairUpperCutoff x k : ℝ) := by
      unfold lemma6PairUpperCutoff
      exact Nat.le_ceil _
    exact_mod_cast (show ((q.1 * q.2 : ℕ) : ℝ) ≤
        lemma6PairDyadicScale x (k + 1) by
      simpa only [lemma6PairDyadicScale] using hqdata.2).trans hceil

/-- Coefficient obtained by grouping the pair polynomial by the product
`n = p₁p₂`. -/
noncomputable def lemma6PairCoefficient
    (x : ℕ) (pairs : Finset (ℕ × ℕ)) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ _q ∈ pairs.filter (fun q => q.1 * q.2 = n),
    1 / ((n : ℂ) ^ s *
      (Real.log ((x : ℝ) / (n : ℝ)) : ℂ))

/-- Regroup the pair polynomial as an ordinary Dirichlet polynomial on a
product interval. -/
theorem lemma6PairDirichletPolynomial_eq_sum_coeff
    {d M Q : ℕ} (x : ℕ) (pairs : Finset (ℕ × ℕ)) (s : ℂ)
    (χ : DirichletCharacter ℂ d)
    (hsupp : ∀ q ∈ pairs, q.1 * q.2 ∈ Finset.Ioc M Q) :
    lemma6PairDirichletPolynomial x pairs s χ =
      ∑ n ∈ Finset.Ioc M Q, lemma6PairCoefficient x pairs s n * χ n := by
  let prod : ℕ × ℕ → ℕ := fun q => q.1 * q.2
  let term : ℕ × ℕ → ℂ := fun q =>
    χ (q.1 * q.2 : ZMod d) /
      (((q.1 * q.2 : ℕ) : ℂ) ^ s *
        (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))
  have hfiber := Finset.sum_fiberwise_eq_sum_filter pairs (Finset.Ioc M Q)
    prod term
  rw [Finset.filter_eq_self.mpr (by
    intro q hq
    exact hsupp q hq)] at hfiber
  unfold lemma6PairDirichletPolynomial
  calc
    (∑ q ∈ pairs,
        χ (q.1 * q.2 : ZMod d) /
          (((q.1 * q.2 : ℕ) : ℂ) ^ s *
            (Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))) =
      ∑ n ∈ Finset.Ioc M Q,
        ∑ q ∈ pairs.filter (fun q => q.1 * q.2 = n), term q :=
      hfiber.symm
    _ = ∑ n ∈ Finset.Ioc M Q,
        lemma6PairCoefficient x pairs s n * χ n := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold lemma6PairCoefficient
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hprod := (Finset.mem_filter.mp hq).2
      dsimp only [term]
      rw [hprod]
      rw [← Nat.cast_mul, hprod]
      ring

/-- The actual `(k,m)` pair block in the interval required by the dyadic
character large sieve. -/
theorem lemma6PairBlockPolynomial_eq_sum_coeff
    {d : ℕ} (x m k : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ d) :
    lemma6PairBlockPolynomial x m k s χ =
      ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k),
        lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s n * χ n := by
  unfold lemma6PairBlockPolynomial
  apply lemma6PairDirichletPolynomial_eq_sum_coeff
  intro q hq
  exact lemma6AdmissiblePairBlock_product_mem_Ioc hq

/-- On Chen's ordered prime-pair range, each product fibre contains at most
one pair. -/
theorem card_lemma6AdmissiblePairBlock_productFiber_le_one
    (x m k n : ℕ) :
    ((lemma6AdmissiblePairBlock x m k).filter
      (fun q => q.1 * q.2 = n)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro q r hq hr
  have hqmem := (Finset.mem_filter.mp hq)
  have hrmem := (Finset.mem_filter.mp hr)
  have hqchen : q ∈ chenPairs x :=
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp hqmem.1).1).1
  have hrchen : r ∈ chenPairs x :=
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp hrmem.1).1).1
  apply pairProduct_injective_on_chenPairs hqchen hrchen
  exact hqmem.2.trans hrmem.2.symm

/-- Uniqueness of the prime factorization removes any multiplicity loss
when the pair polynomial is regrouped by its product. -/
theorem norm_lemma6PairCoefficient_sq_le
    (x m k : ℕ) (s : ℂ) (n : ℕ) :
    ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 ≤
      ‖1 / ((n : ℂ) ^ s *
        (Real.log ((x : ℝ) / (n : ℝ)) : ℂ))‖ ^ 2 := by
  let fiber := (lemma6AdmissiblePairBlock x m k).filter
    (fun q => q.1 * q.2 = n)
  have hcard := card_lemma6AdmissiblePairBlock_productFiber_le_one x m k n
  have hcases : fiber.card = 0 ∨ fiber.card = 1 := by
    dsimp only [fiber]
    omega
  rcases hcases with hzero | hone
  · have hfiber : fiber = ∅ := Finset.card_eq_zero.mp hzero
    simp [lemma6PairCoefficient, fiber, hfiber]
    positivity
  · obtain ⟨q, hfiber⟩ := Finset.card_eq_one.mp hone
    simp [lemma6PairCoefficient, fiber, hfiber]

/-- The prime-pair range leaves at least `x^(1/3)` in the complementary
quotient.  This is the elementary lower bound for the logarithmic
denominator in equations (19) and (20). -/
theorem lemma6_rpow_third_lt_pairQuotient
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    (x : ℝ) ^ ((1 : ℝ) / 3) <
      (x : ℝ) / ((q.1 : ℝ) * q.2) := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with
    ⟨hp₁, hp₂, _hp₁lo, _hp₁hi, hp₂lo, hp₂hi⟩
  have hp₁pos : (0 : ℝ) < q.1 := by exact_mod_cast hp₁.pos
  have hp₂pos : (0 : ℝ) < q.2 := by exact_mod_cast hp₂.pos
  have hdiv0 : 0 ≤ (x : ℝ) / (q.1 : ℝ) := by positivity
  rw [← Real.sqrt_eq_rpow] at hp₂hi
  have hp₂sq :
      (q.2 : ℝ) ^ 2 ≤ (x : ℝ) / (q.1 : ℝ) := by
    nlinarith [Real.sq_sqrt hdiv0]
  have hprodSq :
      (q.1 : ℝ) * (q.2 : ℝ) ^ 2 ≤ (x : ℝ) := by
    simpa [mul_comm] using (le_div_iff₀ hp₁pos).mp hp₂sq
  apply (lt_div_iff₀ (mul_pos hp₁pos hp₂pos)).2
  calc
    (x : ℝ) ^ ((1 : ℝ) / 3) * ((q.1 : ℝ) * q.2) <
        (q.2 : ℝ) * ((q.1 : ℝ) * q.2) :=
      mul_lt_mul_of_pos_right hp₂lo (mul_pos hp₁pos hp₂pos)
    _ = (q.1 : ℝ) * (q.2 : ℝ) ^ 2 := by ring
    _ ≤ (x : ℝ) := hprodSq

/-- Once `log x ≥ 3`, the logarithmic denominator attached to every
admissible prime pair is at least one. -/
theorem lemma6_one_le_pairLog
    {x : ℕ} {q : ℕ × ℕ} (hxlog : 3 ≤ Real.log (x : ℝ))
    (hq : q ∈ chenPairs x) :
    1 ≤ Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) := by
  have hxpos : (0 : ℝ) < x := by
    by_contra hx
    have hx0 : (x : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hx) (Nat.cast_nonneg x)
    have : x = 0 := by exact_mod_cast hx0
    subst x
    norm_num at hxlog
  have hquot := lemma6_rpow_third_lt_pairQuotient hq
  have hpowpos : 0 < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hlogLower :
      (1 : ℝ) / 3 * Real.log x ≤
        Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) := by
    calc
      (1 : ℝ) / 3 * Real.log x =
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) := by
        rw [Real.log_rpow hxpos]
      _ ≤ Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hquot)) hquot.le
  nlinarith

/-- At Chen's `β`-line, uniqueness of `p₁p₂` and the logarithmic
denominator give the coefficient bound `|a_n|² ≤ 1/n`. -/
theorem norm_lemma6PairCoefficient_beta_sq_le_inv
    (x m k : ℕ) (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ)) (n : ℕ) :
    ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k)
        (lemma6BetaPoint x ν) n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
  let fiber := (lemma6AdmissiblePairBlock x m k).filter
    (fun q => q.1 * q.2 = n)
  have hcard := card_lemma6AdmissiblePairBlock_productFiber_le_one x m k n
  have hcases : fiber.card = 0 ∨ fiber.card = 1 := by
    dsimp only [fiber]
    omega
  rcases hcases with hzero | hone
  · have hfiber : fiber = ∅ := Finset.card_eq_zero.mp hzero
    simp [lemma6PairCoefficient, fiber, hfiber]
  · obtain ⟨q, hfiber⟩ := Finset.card_eq_one.mp hone
    have hqfiber : q ∈ fiber := by simp [hfiber]
    have hqmem := Finset.mem_filter.mp hqfiber
    have hqchen : q ∈ chenPairs x :=
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp hqmem.1).1).1
    have hqdata := (Finset.mem_filter.mp hqchen).2
    have hnposNat : 0 < n := by
      rw [← hqmem.2]
      exact Nat.mul_pos hqdata.1.pos hqdata.2.1.pos
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnposNat
    have hlogx : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hxlog
    have hbeta :
        (1 : ℝ) / 2 ≤ (lemma6BetaPoint x ν).re := by
      rw [lemma6BetaPoint_re]
      have : 0 ≤ (1 : ℝ) / Real.log x := by positivity
      linarith
    have hpow :
        (n : ℝ) ^ ((1 : ℝ) / 2) ≤
          (n : ℝ) ^ (lemma6BetaPoint x ν).re :=
      Real.rpow_le_rpow_of_exponent_le hn1 hbeta
    have hlog :
        1 ≤ Real.log ((x : ℝ) / (n : ℝ)) := by
      rw [← hqmem.2]
      simpa only [Nat.cast_mul] using
        (lemma6_one_le_pairLog hxlog hqchen)
    have hden :
        Real.sqrt n ≤
          (n : ℝ) ^ (lemma6BetaPoint x ν).re *
            Real.log ((x : ℝ) / (n : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      exact hpow.trans
        (le_mul_of_one_le_right (Real.rpow_nonneg hnpos.le _) hlog)
    have hden0 :
        0 ≤ (n : ℝ) ^ (lemma6BetaPoint x ν).re *
          Real.log ((x : ℝ) / (n : ℝ)) := by positivity
    have hdenSq :
        (n : ℝ) ≤
          ((n : ℝ) ^ (lemma6BetaPoint x ν).re *
            Real.log ((x : ℝ) / (n : ℝ))) ^ 2 := by
      calc
        (n : ℝ) = (Real.sqrt n) ^ 2 := (Real.sq_sqrt hnpos.le).symm
        _ ≤ ((n : ℝ) ^ (lemma6BetaPoint x ν).re *
            Real.log ((x : ℝ) / (n : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hden 2
    have hinv := one_div_le_one_div_of_le hnpos hdenSq
    have hset :
        (lemma6AdmissiblePairBlock x m k).filter
            (fun q => q.1 * q.2 = n) = {q} := by
      simpa only [fiber] using hfiber
    simp only [lemma6PairCoefficient, hset, Finset.sum_singleton]
    rw [norm_div, norm_one, norm_mul,
      Complex.norm_natCast_cpow_of_pos hnposNat]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hlog)]
    simpa only [one_div, inv_pow] using hinv

/-- On Chen's `α`-line the same argument gains a full extra factor of
`1/n`: `|a_n|² ≤ 1/n²`.  This is the coefficient estimate actually used
in the `A` part of equation (19). -/
theorem norm_lemma6PairCoefficient_alpha_sq_le_inv_sq
    (x m k : ℕ) (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ)) (n : ℕ) :
    ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k)
        (lemma6AlphaPoint x ν) n‖ ^ 2 ≤ ((n : ℝ) ^ 2)⁻¹ := by
  let fiber := (lemma6AdmissiblePairBlock x m k).filter
    (fun q => q.1 * q.2 = n)
  have hcard := card_lemma6AdmissiblePairBlock_productFiber_le_one x m k n
  have hcases : fiber.card = 0 ∨ fiber.card = 1 := by
    dsimp only [fiber]
    omega
  rcases hcases with hzero | hone
  · have hfiber : fiber = ∅ := Finset.card_eq_zero.mp hzero
    simp [lemma6PairCoefficient, fiber, hfiber]
  · obtain ⟨q, hfiber⟩ := Finset.card_eq_one.mp hone
    have hqfiber : q ∈ fiber := by simp [hfiber]
    have hqmem := Finset.mem_filter.mp hqfiber
    have hqchen : q ∈ chenPairs x :=
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp hqmem.1).1).1
    have hqdata := (Finset.mem_filter.mp hqchen).2
    have hnposNat : 0 < n := by
      rw [← hqmem.2]
      exact Nat.mul_pos hqdata.1.pos hqdata.2.1.pos
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnposNat
    have halpha :
        (1 : ℝ) ≤ (lemma6AlphaPoint x ν).re := by
      rw [lemma6AlphaPoint_re]
      have hlogx : 0 < Real.log (x : ℝ) :=
        lt_of_lt_of_le (by norm_num) hxlog
      have : 0 ≤ (1 : ℝ) / Real.log x := by positivity
      linarith
    have hpow :
        (n : ℝ) ≤ (n : ℝ) ^ (lemma6AlphaPoint x ν).re := by
      calc
        (n : ℝ) = (n : ℝ) ^ (1 : ℝ) :=
          (Real.rpow_one (n : ℝ)).symm
        _ ≤ (n : ℝ) ^ (lemma6AlphaPoint x ν).re :=
          Real.rpow_le_rpow_of_exponent_le hn1 halpha
    have hlog :
        1 ≤ Real.log ((x : ℝ) / (n : ℝ)) := by
      rw [← hqmem.2]
      simpa only [Nat.cast_mul] using
        (lemma6_one_le_pairLog hxlog hqchen)
    have hden :
        (n : ℝ) ≤
          (n : ℝ) ^ (lemma6AlphaPoint x ν).re *
            Real.log ((x : ℝ) / (n : ℝ)) :=
      hpow.trans (le_mul_of_one_le_right
        (Real.rpow_nonneg hnpos.le _) hlog)
    have hden0 :
        0 ≤ (n : ℝ) ^ (lemma6AlphaPoint x ν).re *
          Real.log ((x : ℝ) / (n : ℝ)) := by positivity
    have hdenSq :
        (n : ℝ) ^ 2 ≤
          ((n : ℝ) ^ (lemma6AlphaPoint x ν).re *
            Real.log ((x : ℝ) / (n : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hnpos.le hden 2
    have hinv := one_div_le_one_div_of_le (sq_pos_of_pos hnpos) hdenSq
    have hset :
        (lemma6AdmissiblePairBlock x m k).filter
            (fun q => q.1 * q.2 = n) = {q} := by
      simpa only [fiber] using hfiber
    simp only [lemma6PairCoefficient, hset, Finset.sum_singleton]
    rw [norm_div, norm_one, norm_mul,
      Complex.norm_natCast_cpow_of_pos hnposNat]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hlog)]
    simpa only [one_div, inv_pow] using hinv

/-- The coefficient square sum in equation (19) has at most a harmless
harmonic loss.  A later dyadic endpoint simplification can sharpen this to
an absolute constant, as in the printed proof. -/
theorem lemma6_pairCoefficient_sum_sq_beta_le_harmonic
    (x m k : ℕ) (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ)) :
    (∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k),
      ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k)
        (lemma6BetaPoint x ν) n‖ ^ 2) ≤
      (harmonic (lemma6PairUpperCutoff x k) : ℝ) := by
  calc
    (∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k),
      ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k)
        (lemma6BetaPoint x ν) n‖ ^ 2) ≤
        ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k), (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_lemma6PairCoefficient_beta_sq_le_inv x m k ν hxlog n
    _ ≤ ∑ n ∈ Finset.Icc 1 (lemma6PairUpperCutoff x k),
          (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        rw [Finset.mem_Icc]
        omega
      · intro n hn hnot
        positivity
    _ = (harmonic (lemma6PairUpperCutoff x k) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- A convenient logarithmic form of the preceding coefficient bound. -/
theorem lemma6_pairCoefficient_sum_sq_beta_le_log
    (x m k : ℕ) (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ)) :
    (∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k),
      ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k)
        (lemma6BetaPoint x ν) n‖ ^ 2) ≤
      1 + Real.log (lemma6PairUpperCutoff x k) := by
  exact (lemma6_pairCoefficient_sum_sq_beta_le_harmonic
    x m k ν hxlog).trans (harmonic_le_one_add_log _)


/-- Raw character-large-sieve estimate for the actual prime-pair polynomial
on one modulus interval and one pair-product block. -/
theorem lemma6_pairPolynomial_large_sieve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q x m k : ℕ) (s : ℂ), 1 ≤ D → D ≤ Q →
        ∑ d ∈ Finset.Ioc D Q, (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2 else 0) ≤
          C * ((Q : ℝ) +
              ((lemma6PairUpperCutoff x k -
                lemma6PairLowerCutoff x k : ℕ) : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
              (lemma6PairUpperCutoff x k),
                ‖lemma6PairCoefficient x
                  (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q x m k s hD hDQ
  let M := lemma6PairLowerCutoff x k
  let U := lemma6PairUpperCutoff x k
  let N := U - M
  let a : ℕ → ℂ := fun n =>
    lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s n
  have hMU : M ≤ U := lemma6PairLowerCutoff_le_upperCutoff x k
  have hMN : M + N = U := by
    dsimp only [N]
    exact Nat.add_sub_of_le hMU
  have hraw := hlarge D Q M N a hD hDQ
  simpa only [M, U, N, a, hMN,
    lemma6PairBlockPolynomial_eq_sum_coeff] using hraw

/-- The coefficient square sum has no product-fibre multiplicity loss. -/
theorem lemma6_pairCoefficient_sum_sq_le
    (x m k : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k),
      ‖lemma6PairCoefficient x
        (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2) ≤
      ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k),
        ‖1 / ((n : ℂ) ^ s *
          (Real.log ((x : ℝ) / (n : ℝ)) : ℂ))‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  exact norm_lemma6PairCoefficient_sq_le x m k s n

/-- Dirichlet-convolution coefficient of the square of the pair polynomial
on one product block. -/
noncomputable def lemma6PairSquareCoefficient
    (x m k : ℕ) (s : ℂ) (r : ℕ) : ℂ :=
  let S := Finset.Ioc (lemma6PairLowerCutoff x k)
    (lemma6PairUpperCutoff x k)
  ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = r),
    lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s p.1 *
      lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s p.2

/-- A product fibre in the squared pair polynomial is a subset of the
divisor antidiagonal of its product. -/
theorem card_lemma6PairSquareFiber_le_divisors
    (x k r : ℕ) (hr : r ≠ 0) :
    (((Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k)) ×ˢ
      Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k)).filter
          (fun p => p.1 * p.2 = r)).card ≤
      r.divisorsAntidiagonal.card := by
  apply Finset.card_le_card
  intro p hp
  have hpdata := Finset.mem_filter.mp hp
  exact Nat.mem_divisorsAntidiagonal.mpr ⟨hpdata.2, hr⟩

/-- On the `β`-line, Cauchy--Schwarz on each product fibre bounds the
squared-convolution coefficient by `τ(r)²/r`. -/
theorem norm_lemma6PairSquareCoefficient_beta_sq_le
    (x m k : ℕ) (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ)) (r : ℕ) :
    ‖lemma6PairSquareCoefficient x m k (lemma6BetaPoint x ν) r‖ ^ 2 ≤
      (r.divisorsAntidiagonal.card : ℝ) ^ 2 / (r : ℝ) := by
  let S := Finset.Ioc (lemma6PairLowerCutoff x k)
    (lemma6PairUpperCutoff x k)
  let fiber := (S ×ˢ S).filter (fun p => p.1 * p.2 = r)
  let a : ℕ → ℂ := fun n =>
    lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k)
      (lemma6BetaPoint x ν) n
  by_cases hr : r = 0
  · subst r
    have hcoeff :
        lemma6PairSquareCoefficient x m k (lemma6BetaPoint x ν) 0 = 0 := by
      unfold lemma6PairSquareCoefficient
      apply Finset.sum_eq_zero
      intro p hp
      have hpdata := Finset.mem_filter.mp hp
      have hpmem := Finset.mem_product.mp hpdata.1
      have hp1 := (Finset.mem_Ioc.mp hpmem.1).1
      have hp2 := (Finset.mem_Ioc.mp hpmem.2).1
      rcases Nat.mul_eq_zero.mp hpdata.2 with hp1zero | hp2zero <;> omega
    rw [hcoeff]
    simp
  · have hrposNat : 0 < r := Nat.pos_of_ne_zero hr
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hrposNat
    have hcard : fiber.card ≤ r.divisorsAntidiagonal.card := by
      dsimp only [fiber, S]
      exact card_lemma6PairSquareFiber_le_divisors x k r hr
    have hterm : ∀ p ∈ fiber,
        ‖a p.1 * a p.2‖ ^ 2 ≤ (r : ℝ)⁻¹ := by
      intro p hp
      have hpdata := Finset.mem_filter.mp hp
      have hpmem := Finset.mem_product.mp hpdata.1
      have h1 := norm_lemma6PairCoefficient_beta_sq_le_inv
        x m k ν hxlog p.1
      have h2 := norm_lemma6PairCoefficient_beta_sq_le_inv
        x m k ν hxlog p.2
      calc
        ‖a p.1 * a p.2‖ ^ 2 =
            ‖a p.1‖ ^ 2 * ‖a p.2‖ ^ 2 := by
          rw [norm_mul, mul_pow]
        _ ≤ (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹ :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (r : ℝ)⁻¹ := by
          rw [← mul_inv, ← Nat.cast_mul, hpdata.2]
    have hsumTerms :
        (∑ p ∈ fiber, ‖a p.1 * a p.2‖ ^ 2) ≤
          (fiber.card : ℝ) * (r : ℝ)⁻¹ := by
      calc
        (∑ p ∈ fiber, ‖a p.1 * a p.2‖ ^ 2) ≤
            ∑ _p ∈ fiber, (r : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro p hp
          exact hterm p hp
        _ = (fiber.card : ℝ) * (r : ℝ)⁻¹ := by simp
    have hnormSum :
        ‖∑ p ∈ fiber, a p.1 * a p.2‖ ≤
          ∑ p ∈ fiber, ‖a p.1 * a p.2‖ :=
      norm_sum_le _ _
    have hcauchy :
        (∑ p ∈ fiber, ‖a p.1 * a p.2‖) ^ 2 ≤
          (fiber.card : ℝ) *
            ∑ p ∈ fiber, ‖a p.1 * a p.2‖ ^ 2 := by
      simpa using (Finset.sum_mul_sq_le_sq_mul_sq fiber
        (fun _p => (1 : ℝ)) (fun p => ‖a p.1 * a p.2‖))
    unfold lemma6PairSquareCoefficient
    dsimp only [S, fiber, a] at hcard hterm hsumTerms hnormSum hcauchy ⊢
    calc
      ‖∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = r),
          a p.1 * a p.2‖ ^ 2 ≤
          (∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = r),
            ‖a p.1 * a p.2‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnormSum 2
      _ ≤ (((S ×ˢ S).filter (fun p => p.1 * p.2 = r)).card : ℝ) *
          ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = r),
            ‖a p.1 * a p.2‖ ^ 2 := hcauchy
      _ ≤ (((S ×ˢ S).filter (fun p => p.1 * p.2 = r)).card : ℝ) *
          ((((S ×ˢ S).filter (fun p => p.1 * p.2 = r)).card : ℝ) *
            (r : ℝ)⁻¹) := by
        gcongr
      _ = (((S ×ˢ S).filter (fun p => p.1 * p.2 = r)).card : ℝ) ^ 2 /
          (r : ℝ) := by ring
      _ ≤ (r.divisorsAntidiagonal.card : ℝ) ^ 2 / (r : ℝ) := by
        gcongr

/-- Summing the preceding pointwise estimate invokes the divisor-square
mean already proved for equation (15).  Thus the coefficient sum in the
pair fourth moment costs only four logarithms. -/
theorem lemma6_pairSquareCoefficient_sum_sq_beta_le_log_four :
    ∃ C : ℝ, 0 < C ∧ ∀ (x m k : ℕ) (ν : ℝ),
      3 ≤ Real.log (x : ℝ) → 2 ≤ lemma6PairUpperCutoff x k ^ 2 →
      (∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        ‖lemma6PairSquareCoefficient x m k
          (lemma6BetaPoint x ν) r‖ ^ 2) ≤
        C * (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by
  rcases lemma6_divisorSquare_over_n_le_log_four with ⟨C, hC, hdiv⟩
  refine ⟨C, hC, ?_⟩
  intro x m k ν hxlog hU
  calc
    (∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        ‖lemma6PairSquareCoefficient x m k
          (lemma6BetaPoint x ν) r‖ ^ 2) ≤
      ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        (r.divisorsAntidiagonal.card : ℝ) ^ 2 / (r : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact norm_lemma6PairSquareCoefficient_beta_sq_le
        x m k ν hxlog r
    _ = ∑ r ∈ Finset.Icc 1 (lemma6PairUpperCutoff x k ^ 2),
        (r.divisorsAntidiagonal.card : ℝ) ^ 2 / (r : ℝ) := by
      congr 1
    _ ≤ C * (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 :=
      hdiv _ hU

/-- Exact expansion of the squared pair polynomial.  Its product support is
contained in `(0,U²]`, where `U` is the integer upper endpoint of the pair
block. -/
theorem lemma6PairBlockPolynomial_sq_eq_sum_coeff
    {d : ℕ} (x m k : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ d) :
    lemma6PairBlockPolynomial x m k s χ ^ 2 =
      ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        lemma6PairSquareCoefficient x m k s r * χ r := by
  let S := Finset.Ioc (lemma6PairLowerCutoff x k)
    (lemma6PairUpperCutoff x k)
  let P := S ×ˢ S
  let R := Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2)
  let a : ℕ → ℂ := fun n =>
    lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s n
  let term : ℕ × ℕ → ℂ := fun p => a p.1 * a p.2 * χ (p.1 * p.2)
  have hprod_mem (p : ℕ × ℕ) (hp : p ∈ P) : p.1 * p.2 ∈ R := by
    have hpmem := Finset.mem_product.mp hp
    have hp1 := Finset.mem_Ioc.mp hpmem.1
    have hp2 := Finset.mem_Ioc.mp hpmem.2
    rw [Finset.mem_Ioc]
    constructor
    · exact Nat.mul_pos (by omega) (by omega)
    · simpa only [pow_two] using Nat.mul_le_mul hp1.2 hp2.2
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P R
    (fun p : ℕ × ℕ => p.1 * p.2) term
  rw [Finset.filter_eq_self.mpr hprod_mem] at hfiber
  rw [lemma6PairBlockPolynomial_eq_sum_coeff]
  unfold lemma6PairSquareCoefficient
  dsimp only [S, P, R, a]
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
  calc
    (∑ p ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k) ×ˢ
        Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k),
        (lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s p.1 *
          χ p.1) *
        (lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k) s p.2 *
          χ p.2)) =
      ∑ p ∈ P, term p := by
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [term, a]
      rw [map_mul]
      ring
    _ = ∑ r ∈ R,
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = r), term p := hfiber.symm
    _ = ∑ r ∈ R,
        (∑ p ∈ P.filter (fun p => p.1 * p.2 = r),
          a p.1 * a p.2) * χ r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hprod := (Finset.mem_filter.mp hp).2
      dsimp only [term]
      have hcast : (p.1 : ZMod d) * (p.2 : ZMod d) = (r : ZMod d) := by
        rw [← Nat.cast_mul, hprod]
      rw [hcast]
    _ = ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        (let S := Finset.Ioc (lemma6PairLowerCutoff x k)
            (lemma6PairUpperCutoff x k)
          ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = r),
            lemma6PairCoefficient x
                (lemma6AdmissiblePairBlock x m k) s p.1 *
              lemma6PairCoefficient x
                (lemma6AdmissiblePairBlock x m k) s p.2) * χ r := by rfl

/-- Primitive-character fourth moment of the actual pair polynomial. -/
noncomputable def lemma6PairFourthTerm
    (x m k q : ℕ) (s : ℂ) : ℝ :=
  primSum q (fun χ => ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 4)

/-- Write the pair fourth moment as the second moment of its squared
Dirichlet polynomial, ready for the large sieve in equation (20). -/
theorem lemma6PairFourthTerm_eq_squarePolynomial
    (x m k q : ℕ) (s : ℂ) :
    lemma6PairFourthTerm x m k q s =
      ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
        ‖∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
          lemma6PairSquareCoefficient x m k s r * χ r‖ ^ 2
      else 0 := by
  unfold lemma6PairFourthTerm primSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    rw [← lemma6PairBlockPolynomial_sq_eq_sum_coeff]
    rw [norm_pow]
    ring
  · simp [hp]

/-- Rewrite the pair fourth moment on the dependent character block. -/
theorem lemma6_pairFourth_characterBlock_eq
    {x l m k : ℕ} (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 4) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          lemma6PairFourthTerm x m k d s := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [lemma6PrimitiveBaseWeight, lemma6PairBlockNorm,
    lemma6PairFourthTerm, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

/-- Replace `|μ(d)|/d` by `1/φ(d)` in the pair fourth moment. -/
theorem lemma6_pairFourth_characterBlock_le_inv_totient
    {x l m k : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6PairFourthTerm x m k d s := by
  rw [lemma6_pairFourth_characterBlock_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hterm : 0 ≤ lemma6PairFourthTerm x m k d s := by
    unfold lemma6PairFourthTerm primSum
    rw [tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

/-- Equation (20)'s pair-polynomial fourth moment, obtained by applying the
dyadic character large sieve to the squared polynomial of length `U²`. -/
theorem lemma6_pair_fourth_moment_characterBlock :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x l m k : ℕ) (s : ℂ), 1 ≤ Real.log (x : ℝ) →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k s i ^ 4) ≤
          C * ((lemma6ModulusCutoff x l : ℝ) +
              (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
                (lemma6ModulusLowerCutoff x l : ℝ)) *
            ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
              ‖lemma6PairSquareCoefficient x m k s r‖ ^ 2 := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro x l m k s hxlog
  let D := lemma6ModulusLowerCutoff x l
  let Q := lemma6ModulusCutoff x l
  let U2 := lemma6PairUpperCutoff x k ^ 2
  let a : ℕ → ℂ := lemma6PairSquareCoefficient x m k s
  have hD : 1 ≤ D := lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : D ≤ Q := lemma6ModulusLowerCutoff_le_cutoff x l
  have hraw := hlarge D Q 0 U2 a hD hDQ
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6PairFourthTerm x m k d s :=
      lemma6_pairFourth_characterBlock_le_inv_totient hxlog s
    _ = ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ r ∈ Finset.Ioc 0 U2, a r * χ r‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [lemma6PairFourthTerm_eq_squarePolynomial]
    _ ≤ ∑ d ∈ Finset.Ioc D Q,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ r ∈ Finset.Ioc 0 U2, a r * χ r‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [D, Q] using
          (lemma6ModulusBlock_subset_Ioc_cutoffs (x := x) (l := l))
      · intro d hd hnot
        positivity
    _ ≤ C * ((Q : ℝ) + (U2 : ℝ) / (D : ℝ)) *
          ∑ r ∈ Finset.Ioc 0 U2, ‖a r‖ ^ 2 := by
      simpa only [zero_add] using hraw
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
        ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
          ‖lemma6PairSquareCoefficient x m k s r‖ ^ 2 := by
      simp only [D, Q, U2, a, Nat.cast_pow]

/-- Rewrite the prime-pair second moment on the dependent character block
as a sum of primitive-character moments over its moduli. -/
theorem lemma6_pairSecond_characterBlock_eq
    {x l m k : ℕ} (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 2) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          primSum d (fun χ =>
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2) := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [lemma6PrimitiveBaseWeight, lemma6PairBlockNorm,
    primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

/-- Replace `|μ(d)|/d` by the large-sieve weight `1/φ(d)` in the pair
second moment. -/
theorem lemma6_pairSecond_characterBlock_le_inv_totient
    {x l m k : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          primSum d (fun χ =>
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2) := by
  rw [lemma6_pairSecond_characterBlock_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hterm : 0 ≤ primSum d (fun χ =>
      ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2) := by
    unfold primSum
    rw [tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

/-- The prime-pair second moment appearing in equation (19), now directly
bounded by the dyadic character large sieve on the actual modulus block. -/
theorem lemma6_pair_second_moment_characterBlock :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x l m k : ℕ) (s : ℂ), 1 ≤ Real.log (x : ℝ) →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k s i ^ 2) ≤
          C * ((lemma6ModulusCutoff x l : ℝ) +
              ((lemma6PairUpperCutoff x k -
                lemma6PairLowerCutoff x k : ℕ) : ℝ) /
                (lemma6ModulusLowerCutoff x l : ℝ)) *
            ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
              (lemma6PairUpperCutoff x k),
                ‖lemma6PairCoefficient x
                  (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 := by
  rcases lemma6_pairPolynomial_large_sieve with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro x l m k s hxlog
  let D := lemma6ModulusLowerCutoff x l
  let Q := lemma6ModulusCutoff x l
  have hD : 1 ≤ D := lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : D ≤ Q := lemma6ModulusLowerCutoff_le_cutoff x l
  have hraw := hlarge D Q x m k s hD hDQ
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k s i ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          primSum d (fun χ =>
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2) :=
      lemma6_pairSecond_characterBlock_le_inv_totient hxlog s
    _ = ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [primSum, tsum_fintype]
    _ ≤ ∑ d ∈ Finset.Ioc D Q,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖lemma6PairBlockPolynomial x m k s χ‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [D, Q] using
          (lemma6ModulusBlock_subset_Ioc_cutoffs (x := x) (l := l))
      · intro d hd hnot
        positivity
    _ ≤ C * ((Q : ℝ) +
          ((lemma6PairUpperCutoff x k -
            lemma6PairLowerCutoff x k : ℕ) : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k),
            ‖lemma6PairCoefficient x
              (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 := hraw
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          ((lemma6PairUpperCutoff x k -
            lemma6PairLowerCutoff x k : ℕ) : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
        ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
          (lemma6PairUpperCutoff x k),
            ‖lemma6PairCoefficient x
              (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2 := by rfl

end Chen

end

/-! ## ChenTheorem.Lemma6.Equation19 -/

section

/-
Assembly of the three moment estimates in equation (19) of Chen's proof.
-/

open Real Filter
open scoped Classical

namespace Chen

/-- Insert independent bounds for the pair second moment, mollifier fourth
moment, and `L'` fourth moment into the `2,4,4` Hölder inequality (19). -/
theorem lemma6_equation19_B_of_moment_bounds
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) (P M L : ℝ)
    (hpair :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2) ≤ P)
    (hmollifier :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) ≤ M)
    (hderiv :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤ L) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l * P) ^ 2 * M * L := by
  have hpair0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (sq_nonneg _)
  have hmollifier0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
  have hderiv0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
  have hP0 : 0 ≤ P := hpair0.trans hpair
  have hM0 : 0 ≤ M := hmollifier0.trans hmollifier
  have hL0 : 0 ≤ L := hderiv0.trans hderiv
  have hE0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2) ^ 2 *
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 :=
      lemma6_equation19_B_holder hxlarge m k H ν
    _ ≤ (lemma6ExceptionalFactorAt x l * P) ^ 2 * M * L := by
      gcongr

/-- Large-sieve majorant for the pair-polynomial second moment. -/
noncomputable def lemma6PairSecondMajorant
    (x l m k : ℕ) (s : ℂ) : ℝ :=
  ((lemma6ModulusCutoff x l : ℝ) +
      ((lemma6PairUpperCutoff x k -
        lemma6PairLowerCutoff x k : ℕ) : ℝ) /
        (lemma6ModulusLowerCutoff x l : ℝ)) *
    ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
      (lemma6PairUpperCutoff x k),
        ‖lemma6PairCoefficient x
          (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2

/-- The pair second-moment majorant on the `β`-line after the coefficient
sum is reduced to a scalar logarithm. -/
theorem lemma6PairSecondMajorant_beta_le_log
    (x l m k : ℕ) (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ)) :
    lemma6PairSecondMajorant x l m k (lemma6BetaPoint x ν) ≤
      ((lemma6ModulusCutoff x l : ℝ) +
          ((lemma6PairUpperCutoff x k -
            lemma6PairLowerCutoff x k : ℕ) : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
        (1 + Real.log (lemma6PairUpperCutoff x k)) := by
  unfold lemma6PairSecondMajorant
  apply mul_le_mul_of_nonneg_left
    (lemma6_pairCoefficient_sum_sq_beta_le_log x m k ν hxlog)
  positivity

/-- Equation-(15) majorant for the mollifier fourth moment. -/
noncomputable def lemma6MollifierFourthMajorant
    (x l H : ℕ) : ℝ :=
  ((lemma6ModulusCutoff x l : ℝ) +
      ((H * H : ℕ) : ℝ) / (lemma6ModulusLowerCutoff x l : ℝ)) *
    (Real.log ((H * H : ℕ) : ℝ)) ^ 4

/-- Lemma-3/Cauchy majorant for the fourth moment of `L'`. -/
noncomputable def lemma6DerivativeFourthMajorant
    (x l : ℕ) (ν : ℝ) : ℝ :=
  (2 : ℝ) ^ l * (Real.log x) ^ 110 *
    ‖lemma6BetaPoint x ν‖ ^ 2 * (1 + ν ^ 2) ^ 2

/-- Formula (19), with all three moment inputs instantiated by the results
proved in `PairLargeSieve`, `MomentConnection`, and `FourthMoment`.

The remaining work for the printed numerical exponent is now elementary:
bound the three displayed majorants for Chen's choices of `H`, `k`, and
`l`, then integrate in `ν`. -/
theorem lemma6_equation19_B_with_large_sieve_moments_of_deriv_fourth_moment
    (hfourth : Lemma6DerivativeFourthMoment) :
    ∃ Cp Cm Cd : ℝ, 0 < Cp ∧ 0 < Cm ∧ 0 < Cd ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ (l m k H : ℕ) (ν : ℝ), 1 ≤ l → 2 ≤ H →
          (∑ i ∈ lemma6CharacterBlock x l,
              lemma6PrimitiveBaseWeight i *
                (3 : ℝ) ^ distinctPrimeFactors i.1 *
                lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
                lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
                lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
            (lemma6ExceptionalFactorAt x l *
              (Cp * lemma6PairSecondMajorant x l m k
                (lemma6BetaPoint x ν))) ^ 2 *
              (Cm * lemma6MollifierFourthMajorant x l H) *
                (Cd * lemma6DerivativeFourthMajorant x l ν) := by
  rcases lemma6_pair_second_moment_characterBlock with
    ⟨Cp, hCp, hpair⟩
  rcases lemma6_mollifier_fourth_moment_characterBlock with
    ⟨Cm, hCm, hmollifier⟩
  rcases lemma6_deriv_fourth_moment_characterBlock_of hfourth with
    ⟨Cd, hCd, hderiv⟩
  refine ⟨Cp, Cm, Cd, hCp, hCm, hCd, ?_⟩
  have hlogReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlog : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hderiv, hlog,
    eventually_exp_exp_one_le_log_pow_hundred] with x hxderiv hxlog hxlarge
  intro l m k H ν hl hH
  apply lemma6_equation19_B_of_moment_bounds hxlarge m k H ν
      (Cp * lemma6PairSecondMajorant x l m k (lemma6BetaPoint x ν))
      (Cm * lemma6MollifierFourthMajorant x l H)
      (Cd * lemma6DerivativeFourthMajorant x l ν)
  · simpa only [lemma6PairSecondMajorant, mul_assoc] using
      hpair x l m k (lemma6BetaPoint x ν) hxlog
  · simpa only [lemma6MollifierFourthMajorant, mul_assoc] using
      hmollifier x l H ν hxlog hH
  · simpa only [lemma6DerivativeFourthMajorant, mul_assoc] using
      hxderiv l ν hl

end Chen

end

/-! ## ChenTheorem.Lemma6.Equation20 -/

section

/-
Assembly of the three moment estimates in equation (20) of Chen's proof.
-/

open Real Filter
open scoped Classical

namespace Chen

/-- Insert bounds for the mollifier second moment, `L'` fourth moment, and
pair-polynomial fourth moment into the `2,4,4` Hölder ordering of (20). -/
theorem lemma6_equation20_B_of_moment_bounds
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) (S2 L4 P4 : ℝ)
    (hmollifier :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ≤ S2)
    (hderiv :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤ L4)
    (hpair :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 4) ≤ P4) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l * S2) ^ 2 * L4 * P4 := by
  have hmollifier0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (sq_nonneg _)
  have hderiv0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
  have hpair0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 4 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
  have hS20 : 0 ≤ S2 := hmollifier0.trans hmollifier
  have hL40 : 0 ≤ L4 := hderiv0.trans hderiv
  have hP40 : 0 ≤ P4 := hpair0.trans hpair
  have hI0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ^ 2 *
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 4 :=
      lemma6_equation20_B_holder hxlarge m k H ν
    _ ≤ (lemma6ExceptionalFactorAt x l * S2) ^ 2 * L4 * P4 := by
      gcongr

/-- Large-sieve majorant for the mollifier second moment in (20). -/
noncomputable def lemma6MollifierSecondMajorant
    (x l H : ℕ) : ℝ :=
  ((lemma6ModulusCutoff x l : ℝ) +
      (H : ℝ) / (lemma6ModulusLowerCutoff x l : ℝ)) *
    (1 + Real.log H)

/-- Large-sieve majorant for the pair-polynomial fourth moment in (20). -/
noncomputable def lemma6PairFourthMajorant
    (x l m k : ℕ) (s : ℂ) : ℝ :=
  ((lemma6ModulusCutoff x l : ℝ) +
      (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
        (lemma6ModulusLowerCutoff x l : ℝ)) *
  ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
      ‖lemma6PairSquareCoefficient x m k s r‖ ^ 2

/-- The pair fourth-moment majorant after the squared coefficients are
controlled by the divisor-square mean. -/
theorem lemma6PairFourthMajorant_beta_le_log_four :
    ∃ C : ℝ, 0 < C ∧ ∀ (x l m k : ℕ) (ν : ℝ),
      3 ≤ Real.log (x : ℝ) → 2 ≤ lemma6PairUpperCutoff x k ^ 2 →
      lemma6PairFourthMajorant x l m k (lemma6BetaPoint x ν) ≤
        C * ((lemma6ModulusCutoff x l : ℝ) +
          (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
          (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by
  rcases lemma6_pairSquareCoefficient_sum_sq_beta_le_log_four with
    ⟨C, hC, hcoeff⟩
  refine ⟨C, hC, ?_⟩
  intro x l m k ν hxlog hU
  unfold lemma6PairFourthMajorant
  calc
    ((lemma6ModulusCutoff x l : ℝ) +
        (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
          (lemma6ModulusLowerCutoff x l : ℝ)) *
      ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        ‖lemma6PairSquareCoefficient x m k
          (lemma6BetaPoint x ν) r‖ ^ 2 ≤
      ((lemma6ModulusCutoff x l : ℝ) +
        (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
          (lemma6ModulusLowerCutoff x l : ℝ)) *
        (C * (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4) := by
      gcongr
      exact hcoeff x m k ν hxlog hU
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
        (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by ring

/-- Formula (20) with all three moments instantiated.  The remaining
paper-specific work is to simplify the two coefficient majorants under the
third regime returned by `lemma6_occupied_pair_modulus_regime_split` and
to perform the `ν` integral. -/
theorem lemma6_equation20_B_with_large_sieve_moments_of_deriv_fourth_moment
    (hfourth : Lemma6DerivativeFourthMoment) :
    ∃ Cs Cd Cp : ℝ, 0 < Cs ∧ 0 < Cd ∧ 0 < Cp ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ (l m k H : ℕ) (ν : ℝ), 1 ≤ l →
          (∑ i ∈ lemma6CharacterBlock x l,
              lemma6PrimitiveBaseWeight i *
                (3 : ℝ) ^ distinctPrimeFactors i.1 *
                lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
                lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
                lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
            (lemma6ExceptionalFactorAt x l *
              (Cs * lemma6MollifierSecondMajorant x l H)) ^ 2 *
              (Cd * lemma6DerivativeFourthMajorant x l ν) *
                (Cp * lemma6PairFourthMajorant x l m k
                  (lemma6BetaPoint x ν)) := by
  rcases lemma6_mollifier_second_moment_characterBlock with
    ⟨Cs, hCs, hmollifier⟩
  rcases lemma6_deriv_fourth_moment_characterBlock_of hfourth with
    ⟨Cd, hCd, hderiv⟩
  rcases lemma6_pair_fourth_moment_characterBlock with
    ⟨Cp, hCp, hpair⟩
  refine ⟨Cs, Cd, Cp, hCs, hCd, hCp, ?_⟩
  have hlogReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlog : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hderiv, hlog,
    eventually_exp_exp_one_le_log_pow_hundred] with x hxderiv hxlog hxlarge
  intro l m k H ν hl
  apply lemma6_equation20_B_of_moment_bounds hxlarge m k H ν
      (Cs * lemma6MollifierSecondMajorant x l H)
      (Cd * lemma6DerivativeFourthMajorant x l ν)
      (Cp * lemma6PairFourthMajorant x l m k (lemma6BetaPoint x ν))
  · simpa only [lemma6MollifierSecondMajorant, mul_assoc] using
      hmollifier x l H ν hxlog
  · simpa only [lemma6DerivativeFourthMajorant, mul_assoc] using
      hxderiv l ν hl
  · simpa only [lemma6PairFourthMajorant, mul_assoc] using
      hpair x l m k (lemma6BetaPoint x ν) hxlog

end Chen

end

/-! ## ChenTheorem.Lemma6.RemainderConnection -/

section

/-
The exact analytic connection behind equation (14) in Chen's proof.

The finite convolution identity in `Mollifier.lean` concerns a truncated
Dirichlet polynomial.  The factor occurring in equation (16), however, is
the actual Dirichlet `L`-function.  This file separates its absolutely
convergent series into the finite part and a genuine tail, and records the
resulting exact remainder identity.  Estimating the tail is then a separate
analytic step, exactly as in the paper.
-/

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- The completely multiplicative Dirichlet-series phase
`χ(n) / n^s`. -/
noncomputable def lemma6DirichletPhase
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  χ n / (n : ℂ) ^ s

/-- The first `H` terms of the Dirichlet series for `L(s,χ)`. -/
noncomputable def lemma6TruncatedLAt
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H, lemma6DirichletPhase χ s n

/-- The genuine complement of the first `H` terms in the Dirichlet series.
The complement also contains `n = 0`, whose `LSeries.term` is zero. -/
noncomputable def lemma6LSeriesTail
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' n : {n : ℕ // n ∉ Finset.Icc 1 H},
    LSeries.term (fun n : ℕ => χ n) s n

/-- Unit-size phase which puts the real factor `1/n` in exactly the form
expected by the character large sieve in equation (14). -/
noncomputable def lemma6RemainderPhase (s : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) / (n : ℂ) ^ s

theorem norm_lemma6RemainderPhase_le_one
    {s : ℂ} (hs : 1 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖lemma6RemainderPhase s n‖ ≤ 1 := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold lemma6RemainderPhase
  rw [norm_div, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos hnpos]
  apply (div_le_one (Real.rpow_pos_of_pos hnR _)).2
  calc
    (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    _ ≤ (n : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hnOne hs

/-- Elementary bound `|S(H,s,χ)| ≤ harmonic H` on `Re s ≥ 1`. -/
theorem norm_lemma6MollifierAt_le_harmonic
    {q H : ℕ} {s : ℂ} (hs : 1 ≤ s.re)
    (χ : DirichletCharacter ℂ q) :
    ‖lemma6MollifierAt H s χ‖ ≤ (harmonic H : ℝ) := by
  unfold lemma6MollifierAt
  calc
    ‖∑ n ∈ Finset.Icc 1 H,
        (ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s‖ ≤
      ∑ n ∈ Finset.Icc 1 H,
        ‖(ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 H, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnNat : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : 0 < n := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hnum :
          ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖χ n‖ ≤ 1 := by
        nlinarith [norm_nonneg (ArithmeticFunction.moebius n : ℂ),
          norm_nonneg (χ n), χ.norm_le_one n]
      have hden : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
        calc
          (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ (n : ℝ) ^ s.re :=
            Real.rpow_le_rpow_of_exponent_le hnOne hs
      rw [norm_div, norm_mul,
        Complex.norm_natCast_cpow_of_pos hnpos]
      calc
        ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖χ n‖ /
            (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hnR.le _)
        _ ≤ 1 / (n : ℝ) :=
          one_div_le_one_div_of_le hnR hden
        _ = (n : ℝ)⁻¹ := one_div _
    _ = (harmonic H : ℝ) := by
      simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- The analytic truncation estimate used, but not proved, in the paragraph
preceding equation (14).  It is a Pólya--Vinogradov/partial-summation input
and is logically independent of Chen's Lemma 3. -/
def Lemma6LFunctionTruncation : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {q H : ℕ} [NeZero q] {s : ℂ},
    2 ≤ q → 1 ≤ H → 1 ≤ s.re →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ‖lemma6LSeriesTail H s χ‖ ≤
        C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H

theorem lemma6TruncatedLAt_eq_polynomial
    {q H : ℕ} (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6TruncatedLAt H s χ =
      lemma6TruncatedLPolynomial H (lemma6DirichletPhase χ s) := by
  rfl

theorem lemma6MollifierAt_eq_polynomial
    {q H : ℕ} (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6MollifierAt H s χ =
      lemma6MollifierPolynomial H (lemma6DirichletPhase χ s) := by
  unfold lemma6MollifierAt lemma6MollifierPolynomial lemma6DirichletPhase
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The finite `C_H` polynomial is supported on `H < n ≤ H²`. -/
theorem lemma6MollifierRemainderPolynomial_eq_sum_Ioc
    {H : ℕ} (hH : 1 ≤ H) (a : ℕ → ℂ) :
    lemma6MollifierRemainderPolynomial H a =
      ∑ n ∈ Finset.Ioc H (H * H),
        (lemma6MollifierCoeff H n : ℂ) * a n := by
  unfold lemma6MollifierRemainderPolynomial
  symm
  apply Finset.sum_subset
  · intro n hn
    have hndata := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hndata.2⟩
  · intro n hnIcc hnNot
    have hndata := Finset.mem_Icc.mp hnIcc
    have hnH : n ≤ H := by
      by_contra h
      exact hnNot (Finset.mem_Ioc.mpr ⟨lt_of_not_ge h, hndata.2⟩)
    rw [lemma6MollifierCoeff_eq_zero_of_le hH hndata.1 hnH]
    simp

/-- Rewriting of the finite remainder polynomial into the exact coefficient
normalization consumed by `lemma6_mollifier_large_sieve`. -/
theorem lemma6MollifierRemainderPolynomial_eq_largeSieve_sum
    {q H : ℕ} (hH : 1 ≤ H) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s) =
      ∑ n ∈ Finset.Ioc H (H * H),
        (((lemma6MollifierCoeff H n : ℂ) *
          lemma6RemainderPhase s n / (n : ℂ)) * χ n) := by
  rw [lemma6MollifierRemainderPolynomial_eq_sum_Ioc hH]
  apply Finset.sum_congr rfl
  intro n hn
  have hndata := Finset.mem_Ioc.mp hn
  have hnpos : (n : ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  unfold lemma6DirichletPhase lemma6RemainderPhase
  field_simp

theorem lemma6DirichletPhase_one
    {q : ℕ} (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6DirichletPhase χ s 1 = 1 := by
  simp [lemma6DirichletPhase]

theorem lemma6DirichletPhase_mul
    {q : ℕ} (s : ℂ) (χ : DirichletCharacter ℂ q)
    (m n : ℕ) (_hm : 1 ≤ m) (_hn : 1 ≤ n) :
    lemma6DirichletPhase χ s (m * n) =
      lemma6DirichletPhase χ s m * lemma6DirichletPhase χ s n := by
  have hχ : χ ((m * n : ℕ) : ZMod q) =
      χ (m : ZMod q) * χ (n : ZMod q) := by
    rw [Nat.cast_mul, map_mul]
  have hpow : ((m * n : ℕ) : ℂ) ^ s =
      (m : ℂ) ^ s * (n : ℂ) ^ s := by
    simpa only [Nat.cast_mul] using
      Complex.natCast_mul_natCast_cpow m n s
  unfold lemma6DirichletPhase
  rw [hχ, hpow]
  ring

/-- In the half-plane of absolute convergence, the actual `L`-function is
the finite Dirichlet polynomial plus the genuine series tail. -/
theorem lemma6LFunction_eq_truncated_add_tail
    {q : ℕ} [NeZero q] (H : ℕ) {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    DirichletCharacter.LFunction χ s =
      lemma6TruncatedLAt H s χ + lemma6LSeriesTail H s χ := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hsum : Summable
      (LSeries.term (fun n : ℕ => χ n) s) := by
    simpa only [LSeriesSummable] using
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hfinite :
      (∑ n ∈ Finset.Icc 1 H,
          LSeries.term (fun n : ℕ => χ n) s n) =
        lemma6TruncatedLAt H s χ := by
    unfold lemma6TruncatedLAt lemma6DirichletPhase
    apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_of_ne_zero (by
      have := (Finset.mem_Icc.mp hn).1
      omega)]
  have hsplit := hsum.sum_add_tsum_subtype_compl (Finset.Icc 1 H)
  rw [hfinite] at hsplit
  exact hsplit.symm

/-- Exact form of the first display preceding equation (14): the finite
`C_H` polynomial and the analytic truncation tail are kept separate. -/
theorem lemma6_one_sub_LFunction_mul_mollifierAt
    {q H : ℕ} [NeZero q] (hH : 1 ≤ H) {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ =
      lemma6MollifierRemainderPolynomial H
          (lemma6DirichletPhase χ s) -
        lemma6LSeriesTail H s χ * lemma6MollifierAt H s χ := by
  rw [lemma6LFunction_eq_truncated_add_tail H hs χ,
    lemma6TruncatedLAt_eq_polynomial,
    lemma6MollifierAt_eq_polynomial]
  have hfinite := lemma6_one_sub_truncated_product_eq_remainder hH
    (lemma6DirichletPhase χ s)
    (lemma6DirichletPhase_one s χ)
    (lemma6DirichletPhase_mul s χ)
  calc
    1 - (lemma6TruncatedLPolynomial H (lemma6DirichletPhase χ s) +
          lemma6LSeriesTail H s χ) *
          lemma6MollifierPolynomial H (lemma6DirichletPhase χ s) =
        (1 - lemma6TruncatedLPolynomial H (lemma6DirichletPhase χ s) *
          lemma6MollifierPolynomial H (lemma6DirichletPhase χ s)) -
          lemma6LSeriesTail H s χ *
            lemma6MollifierPolynomial H (lemma6DirichletPhase χ s) := by ring
    _ = lemma6MollifierRemainderPolynomial H
          (lemma6DirichletPhase χ s) -
        lemma6LSeriesTail H s χ *
          lemma6MollifierPolynomial H (lemma6DirichletPhase χ s) := by
      rw [hfinite]

/-- Triangle-inequality form of the exact remainder identity.  This is the
pointwise estimate whose two square terms become the polynomial large-sieve
term and the truncation-error term in equation (14). -/
theorem norm_one_sub_LFunction_mul_mollifierAt_le
    {q H : ℕ} [NeZero q] (hH : 1 ≤ H) {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    ‖1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ‖ ≤
      ‖lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s)‖ +
      ‖lemma6LSeriesTail H s χ‖ * ‖lemma6MollifierAt H s χ‖ := by
  rw [lemma6_one_sub_LFunction_mul_mollifierAt hH hs χ]
  exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])

/-- Squared form used after summing over primitive characters in (14). -/
theorem norm_one_sub_LFunction_mul_mollifierAt_sq_le
    {q H : ℕ} [NeZero q] (hH : 1 ≤ H) {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    ‖1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ‖ ^ 2 ≤
      2 * ‖lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s)‖ ^ 2 +
      2 * (‖lemma6LSeriesTail H s χ‖ ^ 2 *
        ‖lemma6MollifierAt H s χ‖ ^ 2) := by
  let a := ‖lemma6MollifierRemainderPolynomial H
    (lemma6DirichletPhase χ s)‖
  let b := ‖lemma6LSeriesTail H s χ‖ * ‖lemma6MollifierAt H s χ‖
  have hab :
      ‖1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ‖ ≤
        a + b := by
    simpa only [a, b] using
      norm_one_sub_LFunction_mul_mollifierAt_le hH hs χ
  calc
    ‖1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ‖ ^ 2 ≤
        (a + b) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hab 2
    _ ≤ 2 * (a ^ 2 + b ^ 2) := add_sq_le
    _ = 2 * ‖lemma6MollifierRemainderPolynomial H
          (lemma6DirichletPhase χ s)‖ ^ 2 +
        2 * (‖lemma6LSeriesTail H s χ‖ ^ 2 *
          ‖lemma6MollifierAt H s χ‖ ^ 2) := by
      dsimp only [a, b]
      ring

/-- Equation-(14) pointwise remainder bound after inserting the explicit
Dirichlet-series truncation estimate.  The first term is ready for the
character large sieve; the second is the paper's analytic error term. -/
theorem norm_one_sub_LFunction_mul_mollifierAt_sq_le_of_truncation
    (htrunc : Lemma6LFunctionTruncation) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q H : ℕ} [NeZero q] {s : ℂ},
      2 ≤ q → 1 ≤ H → 1 < s.re →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        ‖1 - DirichletCharacter.LFunction χ s *
            lemma6MollifierAt H s χ‖ ^ 2 ≤
          2 * ‖lemma6MollifierRemainderPolynomial H
            (lemma6DirichletPhase χ s)‖ ^ 2 +
          2 * ((C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H) ^ 2 *
            (harmonic H : ℝ) ^ 2) := by
  rcases htrunc with ⟨C, hC, htail⟩
  refine ⟨C, hC, ?_⟩
  intro q H _ s hq hH hs χ hχ
  have htail' := htail hq hH hs.le χ hχ
  have hmoll := norm_lemma6MollifierAt_le_harmonic (H := H) hs.le χ
  have hharm : 0 ≤ (harmonic H : ℝ) := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    positivity
  have herror :
      ‖lemma6LSeriesTail H s χ‖ ^ 2 *
          ‖lemma6MollifierAt H s χ‖ ^ 2 ≤
        (C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H) ^ 2 *
          (harmonic H : ℝ) ^ 2 := by
    gcongr
  exact (norm_one_sub_LFunction_mul_mollifierAt_sq_le hH hs χ).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left herror (by norm_num)) _)

end Chen

end

/-! ## ChenTheorem.Lemma6.LFunctionTruncation -/

section

/-
The Pólya--Vinogradov/partial-summation truncation estimate used in
equation (14).  The Fourier--Gauss estimate in `PolyaVinogradov.lean`
gives a uniform bound for character prefixes; Abel summation then turns
that bound into the required `L`-series tail estimate.
-/

open scoped Classical
open Finset Filter Asymptotics MeasureTheory

namespace Chen

noncomputable def lemma6TailCoeff {q : ℕ} (H : ℕ)
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n ≤ H then 0 else χ n

theorem lemma6TailCoeff_sum_eq_zero_of_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) {H n : ℕ}
    (hn : n ≤ H) :
    ∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [lemma6TailCoeff, if_pos]
  exact (mem_Icc.mp hk).2.trans hn

theorem lemma6TailCoeff_sum_norm_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (H n : ℕ) :
    ‖∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k‖ ≤
      6 * Real.sqrt q * Real.log (2 * q) := by
  by_cases hn : n ≤ H
  · rw [lemma6TailCoeff_sum_eq_zero_of_le χ hn, norm_zero]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  · have hHn : H ≤ n := le_of_not_ge hn
    have hsum : ∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k =
        ∑ k ∈ Ioc H n, χ k := by
      calc
        ∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k =
            ∑ k ∈ Ioc H n, lemma6TailCoeff H χ k := by
          symm
          apply Finset.sum_subset
          · intro k hk
            have hk' := mem_Ioc.mp hk
            exact mem_Icc.mpr ⟨by omega, hk'.2⟩
          · intro k hk hkn
            rw [lemma6TailCoeff, if_pos]
            have hkdata := mem_Icc.mp hk
            by_contra h
            exact hkn (mem_Ioc.mpr ⟨lt_of_not_ge h, hkdata.2⟩)
        _ = ∑ k ∈ Ioc H n, χ k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [lemma6TailCoeff, if_neg]
          exact not_le.mpr (mem_Ioc.mp hk).1
    rw [hsum]
    have hunion : Icc 0 n = Icc 0 H ∪ Ioc H n := by
      ext k
      simp only [mem_Icc, mem_union, mem_Ioc]
      omega
    have hdisj : Disjoint (Icc 0 H) (Ioc H n) := by
      rw [Finset.disjoint_left]
      intro k hk₁ hk₂
      simp only [mem_Icc] at hk₁
      simp only [mem_Ioc] at hk₂
      omega
    have hsplit : (∑ k ∈ Icc 0 H, χ k) +
        ∑ k ∈ Ioc H n, χ k = ∑ k ∈ Icc 0 n, χ k := by
      rw [← Finset.sum_union hdisj, ← hunion]
    have hsetH : Icc 0 H = range (H + 1) := by
      ext k
      simp only [mem_Icc, mem_range]
      omega
    have hsetn : Icc 0 n = range (n + 1) := by
      ext k
      simp only [mem_Icc, mem_range]
      omega
    rw [hsetH, hsetn] at hsplit
    have hdiff : ∑ k ∈ Ioc H n, χ k =
        (∑ k ∈ range (n + 1), χ k) -
          ∑ k ∈ range (H + 1), χ k := by
      rw [← hsplit]
      abel
    rw [hdiff]
    calc
      ‖(∑ k ∈ range (n + 1), χ k) -
          ∑ k ∈ range (H + 1), χ k‖ ≤
          ‖∑ k ∈ range (n + 1), χ k‖ +
            ‖∑ k ∈ range (H + 1), χ k‖ := norm_sub_le _ _
      _ ≤ 3 * Real.sqrt q * Real.log (2 * q) +
          3 * Real.sqrt q * Real.log (2 * q) := by
        gcongr
        · exact primitive_character_prefix_sum_norm_le hχ hq (n + 1)
        · exact primitive_character_prefix_sum_norm_le hχ hq (H + 1)
      _ = 6 * Real.sqrt q * Real.log (2 * q) := by ring

theorem lemma6TailCoeff_sum_isBigO
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (H : ℕ) :
    (fun n ↦ ∑ k ∈ Icc 1 n, lemma6TailCoeff H χ k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ) := by
  simp only [Real.rpow_zero]
  exact Asymptotics.isBigO_one_nat_atTop_iff.mpr
    ⟨6 * Real.sqrt q * Real.log (2 * q),
      lemma6TailCoeff_sum_norm_le hχ hq H⟩

theorem lemma6TailCoeff_LSeries_eq_tail
    {q H : ℕ} [NeZero q] {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    LSeries (lemma6TailCoeff H χ) s = lemma6LSeriesTail H s χ := by
  have hcoeff : ∀ n : ℕ, ‖lemma6TailCoeff H χ n‖ ≤ 1 := by
    intro n
    unfold lemma6TailCoeff
    split
    · simp
    · exact χ.norm_le_one n
  have hMask : LSeriesSummable (lemma6TailCoeff H χ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ ↦ hcoeff n) hs
  have hMaskTerms : Summable
      (LSeries.term (lemma6TailCoeff H χ) s) := hMask
  have hsplit := hMaskTerms.sum_add_tsum_subtype_compl (Icc 1 H)
  have hfinite : ∑ n ∈ Icc 1 H,
      LSeries.term (lemma6TailCoeff H χ) s n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [LSeries.term_of_ne_zero (by
      have := (mem_Icc.mp hn).1
      omega)]
    rw [lemma6TailCoeff, if_pos (mem_Icc.mp hn).2, zero_div]
  have htail : (∑' n : {n : ℕ // n ∉ Icc 1 H},
      LSeries.term (lemma6TailCoeff H χ) s n) =
      lemma6LSeriesTail H s χ := by
    unfold lemma6LSeriesTail
    apply tsum_congr
    intro n
    by_cases hn0 : (n : ℕ) = 0
    · simp only [hn0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0,
        LSeries.term_of_ne_zero hn0]
      rw [lemma6TailCoeff, if_neg]
      intro hnH
      exact n.property (mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hn0, hnH⟩)
  unfold LSeries
  rw [← hsplit, hfinite, zero_add, htail]

theorem lemma6LSeriesTail_norm_le_of_one_lt_re
    {q H : ℕ} [NeZero q] {s : ℂ}
    (hq : 2 ≤ q) (hH : 1 ≤ H) (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖lemma6LSeriesTail H s χ‖ ≤
      6 * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H := by
  let C : ℝ := 6 * Real.sqrt q * Real.log (2 * q)
  let A : ℝ → ℂ := fun t ↦
    ∑ k ∈ Icc 1 ⌊t⌋₊, lemma6TailCoeff H χ k
  let g : ℝ → ℝ := fun t ↦
    (Set.Ioi (H : ℝ)).indicator (fun u ↦ C * u ^ (-2 : ℝ)) t
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hgreal : Integrable g := by
    dsimp only [g]
    exact (integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ))
        (c := (H : ℝ)) (by norm_num) hHpos).const_mul C)
  have hg : Integrable g (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hgreal.mono_measure Measure.restrict_le_self
  have hpoint : ∀ t ∈ Set.Ioi (1 : ℝ),
      ‖A t * (t : ℂ) ^ (-(s + 1))‖ ≤ g t := by
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    by_cases htH : (H : ℝ) < t
    · have hgval : g t = C * t ^ (-2 : ℝ) := by
        dsimp only [g]
        rw [Set.indicator_of_mem
          (show t ∈ Set.Ioi (H : ℝ) from htH)]
      rw [hgval]
      have hA : ‖A t‖ ≤ C := by
        exact lemma6TailCoeff_sum_norm_le hχ hq H ⌊t⌋₊
      have htone : (1 : ℝ) ≤ t := ht.le
      have hpow : ‖(t : ℂ) ^ (-(s + 1))‖ ≤
          t ^ (-2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
        have hexp : (-(s + 1)).re = -(s.re + 1) := by simp
        rw [hexp]
        exact Real.rpow_le_rpow_of_exponent_le htone (by linarith)
      rw [norm_mul]
      exact mul_le_mul hA hpow
        (norm_nonneg _) hC
    · have htHle : t ≤ H := le_of_not_gt htH
      have hfloorR : (⌊t⌋₊ : ℝ) ≤ H :=
        (Nat.floor_le htpos.le).trans htHle
      have hfloor : ⌊t⌋₊ ≤ H := by exact_mod_cast hfloorR
      have hAzero : A t = 0 := by
        exact lemma6TailCoeff_sum_eq_zero_of_le χ hfloor
      rw [hAzero, zero_mul, norm_zero]
      have hgzero : g t = 0 := by
        dsimp only [g]
        simp [Set.indicator, htH]
      rw [hgzero]
  have hO := lemma6TailCoeff_sum_isBigO hχ hq H
  have hsum : LSeriesSummable (lemma6TailCoeff H χ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n hn
      unfold lemma6TailCoeff
      split
      · simp
      · exact χ.norm_le_one n
    · exact hs
  have hrepr := LSeries_eq_mul_integral (lemma6TailCoeff H χ)
    (r := 0) (s := s) le_rfl (by linarith) hsum hO
  rw [← lemma6TailCoeff_LSeries_eq_tail hs χ, hrepr, norm_mul]
  calc
    ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ),
        A t * (t : ℂ) ^ (-(s + 1))‖ ≤
        ‖s‖ * ∫ t in Set.Ioi (1 : ℝ), g t := by
      gcongr
      exact MeasureTheory.norm_integral_le_of_norm_le hg
        ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall hpoint))
    _ = ‖s‖ * (C / H) := by
      congr 1
      rw [show (∫ t in Set.Ioi (1 : ℝ), g t) =
          ∫ t in Set.Ioi (H : ℝ), C * t ^ (-2 : ℝ) by
        rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
        simp only [g, Set.indicator_indicator]
        have hinter : Set.Ioi (1 : ℝ) ∩ Set.Ioi (H : ℝ) =
            Set.Ioi (H : ℝ) := by
          ext t
          simp only [Set.mem_inter_iff, Set.mem_Ioi]
          constructor
          · exact fun h ↦ h.2
          · intro ht
            exact ⟨(show (1 : ℝ) ≤ H by exact_mod_cast hH).trans_lt ht, ht⟩
        rw [hinter, MeasureTheory.integral_indicator measurableSet_Ioi]]
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num) hHpos]
      have hpow : (H : ℝ) ^ ((-2 : ℝ) + 1) = (H : ℝ)⁻¹ := by
        norm_num
        rw [Real.rpow_neg_one]
      rw [hpow]
      field_simp
      ring
    _ = 6 * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H := by
      dsimp only [C]
      ring

theorem lemma6LSeriesTail_eq_zero_of_re_eq_one
    {q H : ℕ} [NeZero q] {s : ℂ} (hs : s.re = 1)
    (χ : DirichletCharacter ℂ q) :
    lemma6LSeriesTail H s χ = 0 := by
  have hfull : ¬Summable
      (LSeries.term (fun n : ℕ ↦ χ n) s) := by
    intro h
    have hL : LSeriesSummable (fun n : ℕ ↦ χ n) s := h
    rw [DirichletCharacter.LSeriesSummable_iff
      (s := s) (NeZero.ne q) χ] at hL
    linarith
  have htail : ¬Summable (fun n : {n : ℕ // n ∉ Icc 1 H} ↦
      LSeries.term (fun n : ℕ ↦ χ n) s n) := by
    intro ht
    apply hfull
    let S : Set ℕ := {n : ℕ | n ∉ Icc 1 H}
    have hmasked : Summable (S.indicator
        (LSeries.term (fun n : ℕ ↦ χ n) s)) :=
      (summable_subtype_iff_indicator (s := S)).mp ht
    apply Summable.congr_atTop hmasked
    filter_upwards [eventually_ge_atTop (H + 1)] with n hn
    rw [Set.indicator_of_mem]
    dsimp only [S]
    simp only [Set.mem_setOf_eq]
    intro hmem
    have hnH := (mem_Icc.mp hmem).2
    omega
  unfold lemma6LSeriesTail
  exact tsum_eq_zero_of_not_summable htail

theorem lemma6LFunctionTruncation : Lemma6LFunctionTruncation := by
  refine ⟨6, by norm_num, ?_⟩
  intro q H hqInst s hq hH hs χ hχ
  obtain hsEq | hsLt := hs.eq_or_lt
  · have hzero := lemma6LSeriesTail_eq_zero_of_re_eq_one
      (H := H) hsEq.symm χ
    rw [hzero, norm_zero]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    positivity
  · exact lemma6LSeriesTail_norm_le_of_one_lt_re hq hH hsLt χ hχ

end Chen

end

/-! ## ChenTheorem.Lemma6.RemainderDyadic -/

section

/-
Dyadic assembly of the finite `C_H` polynomial in equation (14).

`RemainderConnection.lean` identifies the exact finite polynomial supported
on `H < n ≤ H²`; `MollifierLargeSieve.lean` estimates one interval
`M < n ≤ 2M`.  This file supplies the missing finite partition and the
Cauchy--Schwarz loss incurred when those intervals are put back together.
-/

open scoped Classical

namespace Chen

/-- The `i`-th dyadic interval above `H`. -/
def lemma6RemainderDyadicBlock (H i : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ i * H) (2 ^ (i + 1) * H)

/-- There are enough blocks to cover `H < n ≤ H²`. -/
def lemma6RemainderDyadicIndices (H : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 H + 1)

theorem lemma6RemainderDyadicBlocks_pairwiseDisjoint (H : ℕ) :
    Set.PairwiseDisjoint (lemma6RemainderDyadicIndices H)
      (lemma6RemainderDyadicBlock H) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  rw [lemma6RemainderDyadicBlock, Finset.mem_Ioc] at hni hnj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hpow : 2 ^ (i + 1) ≤ 2 ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    have hsep := Nat.mul_le_mul_right H hpow
    omega
  · have hpow : 2 ^ (j + 1) ≤ 2 ^ i :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    have hsep := Nat.mul_le_mul_right H hpow
    omega

/-- Every integer in the support interval of `C_H` belongs to one of the
dyadic blocks above `H`. -/
theorem lemma6RemainderSupport_subset_dyadicBlocks
    {H : ℕ} (hH : 1 ≤ H) :
    Finset.Ioc H (H * H) ⊆
      (lemma6RemainderDyadicIndices H).biUnion
        (lemma6RemainderDyadicBlock H) := by
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_biUnion]
  refine ⟨Nat.log 2 ((n - 1) / H), ?_, ?_⟩
  · rw [lemma6RemainderDyadicIndices, Finset.mem_range,
      Nat.lt_succ_iff]
    apply Nat.log_mono_right
    apply (Nat.div_le_iff_le_mul (by omega : 0 < H)).2
    omega
  · rw [lemma6RemainderDyadicBlock, Finset.mem_Ioc]
    constructor
    · have hr : 0 < (n - 1) / H := Nat.div_pos (by omega) (by omega)
      have hp := Nat.pow_log_le_self 2 hr.ne'
      have hmul : 2 ^ Nat.log 2 ((n - 1) / H) * H ≤ n - 1 := by
        calc
          2 ^ Nat.log 2 ((n - 1) / H) * H ≤
              ((n - 1) / H) * H :=
            Nat.mul_le_mul_right H hp
          _ ≤ n - 1 := Nat.div_mul_le_self _ _
      omega
    · have hp : (n - 1) / H <
          2 ^ (Nat.log 2 ((n - 1) / H) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
      have hmul : n - 1 <
          2 ^ (Nat.log 2 ((n - 1) / H) + 1) * H :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < H)).mp hp
      omega

/-- The summand in equation (14), normalized for the character large
sieve. -/
noncomputable def lemma6RemainderDyadicTerm
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q)
    (n : ℕ) : ℂ :=
  ((lemma6MollifierCoeff H n : ℂ) * lemma6RemainderPhase s n /
      (n : ℂ)) * χ n

theorem lemma6RemainderDyadicTerm_eq_zero_of_sq_lt
    {q H n : ℕ} (hH : 1 ≤ H) (hn : H * H < n) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    lemma6RemainderDyadicTerm H s χ n = 0 := by
  unfold lemma6RemainderDyadicTerm
  rw [lemma6MollifierCoeff_eq_zero_of_sq_lt hH hn]
  simp

/-- The dyadic blocks may extend beyond `H²`, but `C_H` vanishes there;
their sum is therefore exactly the finite remainder polynomial. -/
theorem lemma6MollifierRemainderPolynomial_eq_sum_dyadic
    {q H : ℕ} (hH : 1 ≤ H) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s) =
      ∑ i ∈ lemma6RemainderDyadicIndices H,
        ∑ n ∈ lemma6RemainderDyadicBlock H i,
          lemma6RemainderDyadicTerm H s χ n := by
  rw [lemma6MollifierRemainderPolynomial_eq_largeSieve_sum hH]
  let U := (lemma6RemainderDyadicIndices H).biUnion
    (lemma6RemainderDyadicBlock H)
  have hsubset : Finset.Ioc H (H * H) ⊆ U := by
    simpa only [U] using lemma6RemainderSupport_subset_dyadicBlocks hH
  change (∑ n ∈ Finset.Ioc H (H * H),
      lemma6RemainderDyadicTerm H s χ n) = _
  calc
    (∑ n ∈ Finset.Ioc H (H * H),
        lemma6RemainderDyadicTerm H s χ n) =
        ∑ n ∈ U, lemma6RemainderDyadicTerm H s χ n := by
      apply Finset.sum_subset hsubset
      intro n hnU hnNot
      have hnH : H < n := by
        change n ∈ (lemma6RemainderDyadicIndices H).biUnion
          (lemma6RemainderDyadicBlock H) at hnU
        rw [Finset.mem_biUnion] at hnU
        obtain ⟨i, _hi, hni⟩ := hnU
        rw [lemma6RemainderDyadicBlock, Finset.mem_Ioc] at hni
        have hpow : H ≤ 2 ^ i * H := by
          have hone : 1 ≤ (2 : ℕ) ^ i := one_le_pow₀ (by norm_num)
          simpa only [one_mul] using Nat.mul_le_mul_right H hone
        omega
      have hnHH : H * H < n := by
        by_contra h
        exact hnNot (Finset.mem_Ioc.mpr ⟨hnH, le_of_not_gt h⟩)
      exact lemma6RemainderDyadicTerm_eq_zero_of_sq_lt hH hnHH s χ
    _ = ∑ i ∈ lemma6RemainderDyadicIndices H,
          ∑ n ∈ lemma6RemainderDyadicBlock H i,
            lemma6RemainderDyadicTerm H s χ n :=
      Finset.sum_biUnion (lemma6RemainderDyadicBlocks_pairwiseDisjoint H)

/-- Finite Cauchy--Schwarz for reconstructing the remainder polynomial
from its dyadic pieces.  Its cardinal factor is the paper's logarithmic
loss in the display preceding equation (14). -/
theorem norm_lemma6MollifierRemainderPolynomial_sq_le_sum_dyadic
    {q H : ℕ} (hH : 1 ≤ H) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    ‖lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s)‖ ^ 2 ≤
      (lemma6RemainderDyadicIndices H).card *
        ∑ i ∈ lemma6RemainderDyadicIndices H,
          ‖∑ n ∈ lemma6RemainderDyadicBlock H i,
            lemma6RemainderDyadicTerm H s χ n‖ ^ 2 := by
  rw [lemma6MollifierRemainderPolynomial_eq_sum_dyadic hH]
  let b : ℕ → ℂ := fun i =>
    ∑ n ∈ lemma6RemainderDyadicBlock H i,
      lemma6RemainderDyadicTerm H s χ n
  change ‖∑ i ∈ lemma6RemainderDyadicIndices H, b i‖ ^ 2 ≤ _
  have htriangle : ‖∑ i ∈ lemma6RemainderDyadicIndices H, b i‖ ≤
      ∑ i ∈ lemma6RemainderDyadicIndices H, ‖b i‖ :=
    norm_sum_le _ _
  calc
    ‖∑ i ∈ lemma6RemainderDyadicIndices H, b i‖ ^ 2 ≤
        (∑ i ∈ lemma6RemainderDyadicIndices H, ‖b i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (∑ i ∈ lemma6RemainderDyadicIndices H, (1 : ℝ) ^ 2) *
          ∑ i ∈ lemma6RemainderDyadicIndices H, ‖b i‖ ^ 2 := by
      simpa only [one_mul] using
        (Finset.sum_mul_sq_le_sq_mul_sq
          (lemma6RemainderDyadicIndices H)
          (fun _ => (1 : ℝ)) (fun i => ‖b i‖))
    _ = (lemma6RemainderDyadicIndices H).card *
          ∑ i ∈ lemma6RemainderDyadicIndices H, ‖b i‖ ^ 2 := by
      simp

theorem lemma6RemainderDyadicBlock_eq_Ioc_double (H i : ℕ) :
    lemma6RemainderDyadicBlock H i =
      Finset.Ioc (2 ^ i * H) (2 ^ i * H + 2 ^ i * H) := by
  unfold lemma6RemainderDyadicBlock
  congr 1
  rw [pow_succ]
  ring

/-- The finite `C_H` part of equation (14), after summing the dyadic
large-sieve estimate over all occupied `n`-blocks.  The right side is kept
as the exact finite dyadic sum; the following scalar step turns it into
Chen's `(Q/H + 1/D) (log x)^5` expression. -/
theorem lemma6_mollifier_remainder_large_sieve_dyadic :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q H : ℕ) (s : ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ H → 1 ≤ s.re →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖lemma6MollifierRemainderPolynomial H
                (lemma6DirichletPhase χ s)‖ ^ 2 else 0) ≤
          C * (lemma6RemainderDyadicIndices H).card *
            ∑ i ∈ lemma6RemainderDyadicIndices H,
              ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
                (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 := by
  rcases lemma6_mollifier_large_sieve_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q H s hD hDQ hH hs
  let J := lemma6RemainderDyadicIndices H
  let B : (i q : ℕ) → DirichletCharacter ℂ q → ℝ := fun i q χ =>
    ‖∑ n ∈ lemma6RemainderDyadicBlock H i,
      lemma6RemainderDyadicTerm H s χ n‖ ^ 2
  have hpoint (q : ℕ) (χ : DirichletCharacter ℂ q) :
      ‖lemma6MollifierRemainderPolynomial H
          (lemma6DirichletPhase χ s)‖ ^ 2 ≤
        J.card * ∑ i ∈ J, B i q χ := by
    simpa only [J, B] using
      norm_lemma6MollifierRemainderPolynomial_sq_le_sum_dyadic hH s χ
  have hblocks : ∀ i ∈ J,
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            B i q χ else 0) ≤
        C * ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
          (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 := by
    intro i hi
    have hM : 1 ≤ 2 ^ i * H := by
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.one_le_iff_ne_zero.mp hH))
    have hphase : ∀ n ∈ Finset.Ioc (2 ^ i * H)
        (2 ^ i * H + 2 ^ i * H), ‖lemma6RemainderPhase s n‖ ≤ 1 := by
      intro n hn
      exact norm_lemma6RemainderPhase_le_one hs
        (hM.trans (Finset.mem_Ioc.mp hn).1.le)
    have hb := hlarge D Q (2 ^ i * H) H
      (lemma6RemainderPhase s) hD hDQ hM hphase
    simpa only [B, lemma6RemainderDyadicTerm,
      lemma6RemainderDyadicBlock_eq_Ioc_double] using hb
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma6MollifierRemainderPolynomial H
            (lemma6DirichletPhase χ s)‖ ^ 2 else 0) ≤
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          J.card * ∑ i ∈ J, B i q χ else 0) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro χ hχ
          split_ifs
          · exact hpoint q χ
          · exact le_rfl
        · positivity
    _ = J.card * ∑ i ∈ J,
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            B i q χ else 0) := by
      simp only [mul_ite, mul_zero, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      split_ifs
      · apply Finset.sum_congr rfl
        intro j hj
        ring
      · simp
    _ ≤ J.card * ∑ i ∈ J,
        C * ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
          (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 := by
      gcongr with i hi
      exact hblocks i hi
    _ = C * J.card * ∑ i ∈ J,
        ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
          (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem card_lemma6RemainderDyadicIndices (H : ℕ) :
    (lemma6RemainderDyadicIndices H).card = Nat.log 2 H + 1 := by
  simp [lemma6RemainderDyadicIndices]

theorem lemma6RemainderDyadicBlock_top_le_sq
    {H i : ℕ} (hH : 1 ≤ H)
    (hi : i ∈ lemma6RemainderDyadicIndices H) :
    2 ^ i * H + 2 ^ i * H ≤ 2 * H * H := by
  have hiLog : i ≤ Nat.log 2 H := by
    simpa only [lemma6RemainderDyadicIndices, Finset.mem_range,
      Nat.lt_succ_iff] using hi
  have hpowLog : (2 : ℕ) ^ Nat.log 2 H ≤ H :=
    Nat.pow_log_le_self 2 (by omega)
  have hpow : (2 : ℕ) ^ i ≤ H :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hiLog).trans hpowLog
  nlinarith

theorem lemma6RemainderDyadic_log_le_log_sq
    {H i : ℕ} (hH : 1 ≤ H)
    (hi : i ∈ lemma6RemainderDyadicIndices H) :
    Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ) ≤
      Real.log ((2 * H * H : ℕ) : ℝ) := by
  have htop := lemma6RemainderDyadicBlock_top_le_sq hH hi
  have hleft : (0 : ℝ) < (2 ^ i * H + 2 ^ i * H : ℕ) := by
    exact_mod_cast (show 0 < 2 ^ i * H + 2 ^ i * H by
      have : 0 < H := by omega
      positivity)
  have hright : (0 : ℝ) < (2 * H * H : ℕ) := by
    exact_mod_cast (show 0 < 2 * H * H by positivity)
  exact Real.strictMonoOn_log.monotoneOn hleft
    hright (by exact_mod_cast htop)

theorem lemma6RemainderDyadic_inv_sum_le_two_div
    {H : ℕ} (hH : 1 ≤ H) :
    ∑ i ∈ lemma6RemainderDyadicIndices H,
        ((2 ^ i * H : ℕ) : ℝ)⁻¹ ≤ 2 / H := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  calc
    ∑ i ∈ lemma6RemainderDyadicIndices H,
        ((2 ^ i * H : ℕ) : ℝ)⁻¹ =
      (H : ℝ)⁻¹ * ∑ i ∈ Finset.range (Nat.log 2 H + 1),
        (1 / (2 : ℝ)) ^ i := by
      unfold lemma6RemainderDyadicIndices
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      rw [mul_inv, div_pow]
      norm_num
      ring
    _ ≤ (H : ℝ)⁻¹ * 2 := by
      apply mul_le_mul_of_nonneg_left
        (sum_geometric_two_le (Nat.log 2 H + 1))
      positivity
    _ = 2 / H := by
      rw [div_eq_mul_inv]
      ring

/-- Scalar form of the polynomial part of equation (14).  It displays
exactly the two logarithmic losses: one from Cauchy--Schwarz and one from
summing the `D⁻¹` contribution over the dyadic blocks. -/
theorem lemma6_mollifier_remainder_large_sieve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q H : ℕ) (s : ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ H → 1 ≤ s.re →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖lemma6MollifierRemainderPolynomial H
                (lemma6DirichletPhase χ s)‖ ^ 2 else 0) ≤
          C * (Nat.log 2 H + 1) *
            (2 * (Q : ℝ) / H +
              (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
  rcases lemma6_mollifier_remainder_large_sieve_dyadic with
    ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q H s hD hDQ hH hs
  have hlog0 : 0 ≤ Real.log ((2 * H * H : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * H * H by nlinarith)
  have hsum :
      ∑ i ∈ lemma6RemainderDyadicIndices H,
          ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
            (Real.log ((2 ^ i * H + 2 ^ i * H : ℕ) : ℝ)) ^ 3 ≤
        (2 * (Q : ℝ) / H +
          (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
          (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
    calc
      _ ≤ ∑ i ∈ lemma6RemainderDyadicIndices H,
          ((Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
        apply Finset.sum_le_sum
        intro i hi
        have hfactor : 0 ≤
            (Q : ℝ) / (2 ^ i * H : ℕ) + (D : ℝ)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by
              have hpos : (0 : ℝ) <
                  (2 ^ i * H + 2 ^ i * H : ℕ) := by
                exact_mod_cast (show 0 < 2 ^ i * H + 2 ^ i * H by
                  have : 0 < H := by omega
                  nlinarith [show 0 < (2 : ℕ) ^ i by exact pow_pos (by norm_num) _])
              exact Real.log_nonneg (by
                exact_mod_cast (show 1 ≤ 2 ^ i * H + 2 ^ i * H by
                  have : 0 < H := by omega
                  nlinarith [show 0 < (2 : ℕ) ^ i by exact pow_pos (by norm_num) _])))
            (lemma6RemainderDyadic_log_le_log_sq hH hi) 3)
          hfactor
      _ = ((Q : ℝ) *
            ∑ i ∈ lemma6RemainderDyadicIndices H,
              ((2 ^ i * H : ℕ) : ℝ)⁻¹ +
          (lemma6RemainderDyadicIndices H).card * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (Q : ℝ) / H +
          (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3 := by
        rw [card_lemma6RemainderDyadicIndices]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlog0 3)
        have hQ0 : 0 ≤ (Q : ℝ) := by positivity
        calc
          (Q : ℝ) * ∑ i ∈ lemma6RemainderDyadicIndices H,
                ((2 ^ i * H : ℕ) : ℝ)⁻¹ +
              (Nat.log 2 H + 1 : ℕ) * (D : ℝ)⁻¹ ≤
            (Q : ℝ) * (2 / H) +
              (Nat.log 2 H + 1 : ℕ) * (D : ℝ)⁻¹ := by
                gcongr
                exact lemma6RemainderDyadic_inv_sum_le_two_div hH
          _ = 2 * (Q : ℝ) / H +
              (Nat.log 2 H + 1 : ℕ) * (D : ℝ)⁻¹ := by ring
          _ = 2 * (Q : ℝ) / H +
              ((Nat.log 2 H : ℝ) + 1) * (D : ℝ)⁻¹ := by
            norm_num only [Nat.cast_add, Nat.cast_one]
      _ = _ := by norm_num only [Nat.cast_add, Nat.cast_one]
  exact (hlarge D Q H s hD hDQ hH hs).trans <| by
    rw [card_lemma6RemainderDyadicIndices]
    have hcard0 : (0 : ℝ) ≤ (Nat.log 2 H + 1 : ℕ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg hC.le hcard0)
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hmul

end Chen

end

/-! ## ChenTheorem.Lemma6.Equation14 -/

section

/-
Assembly of equation (14): combine the exact `L`-series truncation with
the dyadic large-sieve estimate for the finite `C_H` polynomial.
-/

open scoped Classical

namespace Chen

/-- The analytic truncation-error summand left after the primitive
character count cancels the weight `1 / φ(q)`. -/
noncomputable def lemma6Equation14ErrorTerm
    (C : ℝ) (H : ℕ) (s : ℂ) (q : ℕ) : ℝ :=
  2 * ((C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H) ^ 2 *
    (harmonic H : ℝ) ^ 2)

theorem lemma6Equation14ErrorTerm_nonneg
    (C : ℝ) (H : ℕ) (s : ℂ) (q : ℕ) :
    0 ≤ lemma6Equation14ErrorTerm C H s q := by
  unfold lemma6Equation14ErrorTerm
  positivity

theorem lemma6Equation14ErrorTerm_le_at_Q
    {C : ℝ} (hC : 0 ≤ C) {D Q H q : ℕ} {s : ℂ}
    (hH : 1 ≤ H) (hDQ : D ≤ Q) (hq : q ∈ Finset.Ioc D Q) :
    lemma6Equation14ErrorTerm C H s q ≤
      2 * ((C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
        (harmonic H : ℝ) ^ 2) := by
  have hqQ : q ≤ Q := (Finset.mem_Ioc.mp hq).2
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hsqrt : Real.sqrt q ≤ Real.sqrt Q := Real.sqrt_le_sqrt (by exact_mod_cast hqQ)
  have hlog : Real.log (2 * (q : ℝ)) ≤ Real.log (2 * (Q : ℝ)) := by
    by_cases hqzero : q = 0
    · subst q
      have hqD := (Finset.mem_Ioc.mp hq).1
      omega
    · have hqpos : (0 : ℝ) < 2 * q := by
        exact_mod_cast (show 0 < 2 * q by
          exact Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hqzero))
      have hQposNat : 0 < Q := lt_of_lt_of_le (Nat.pos_of_ne_zero hqzero) hqQ
      have hQpos : (0 : ℝ) < 2 * Q := by
        exact_mod_cast (show 0 < 2 * Q by
          exact Nat.mul_pos (by norm_num) hQposNat)
      exact Real.strictMonoOn_log.monotoneOn hqpos hQpos
        (by exact_mod_cast Nat.mul_le_mul_left 2 hqQ)
  have hnum :
      C * ‖s‖ * Real.sqrt q * Real.log (2 * q) ≤
        C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) := by
    have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) := by
      have hqone : 1 ≤ q := by
        have hqD := (Finset.mem_Ioc.mp hq).1
        omega
      exact Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ 2 * q by nlinarith))
    gcongr
  unfold lemma6Equation14ErrorTerm
  have hleft0 : 0 ≤
      C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg hC (norm_nonneg _))
        (Real.sqrt_nonneg _)) (Real.log_nonneg (by
          have hqD := (Finset.mem_Ioc.mp hq).1
          exact_mod_cast (show 1 ≤ 2 * q by omega)))
    · positivity
  have hright0 : 0 ≤
      C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg hC (norm_nonneg _))
        (Real.sqrt_nonneg _)) (Real.log_nonneg (by
          have hqD := (Finset.mem_Ioc.mp hq).1
          exact_mod_cast (show 1 ≤ 2 * Q by omega)))
    · positivity
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (sq_le_sq₀ hleft0 hright0 |>.2
        (div_le_div_of_nonneg_right hnum (by positivity)))
      (sq_nonneg (harmonic H : ℝ))) (by norm_num)

theorem sum_lemma6Equation14ErrorTerm_le
    {C : ℝ} (hC : 0 ≤ C) {D Q H : ℕ} {s : ℂ}
    (_hD : 1 ≤ D) (hDQ : D ≤ Q) (hH : 1 ≤ H) :
    ∑ q ∈ Finset.Ioc D Q, lemma6Equation14ErrorTerm C H s q ≤
      (Q : ℝ) *
        (2 * ((C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
          (harmonic H : ℝ) ^ 2)) := by
  calc
    ∑ q ∈ Finset.Ioc D Q, lemma6Equation14ErrorTerm C H s q ≤
        (Finset.Ioc D Q).card •
          (2 * ((C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
            (harmonic H : ℝ) ^ 2)) :=
      Finset.sum_le_card_nsmul _ _ _
        (fun q hq => lemma6Equation14ErrorTerm_le_at_Q hC hH hDQ hq)
    _ ≤ Q *
        (2 * ((C * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
          (harmonic H : ℝ) ^ 2)) := by
      simp only [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · have : (Finset.Ioc D Q).card ≤ Q := by simp
        exact_mod_cast this
      · positivity

/-- Total primitive-character left side at a fixed modulus, extended by
zero at the formal modulus `q = 0` where `LFunction` is not defined. -/
noncomputable def lemma6Equation14LeftTerm
    (H q : ℕ) (s : ℂ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
      ‖1 - DirichletCharacter.LFunction χ s *
        lemma6MollifierAt H s χ‖ ^ 2 else 0

theorem lemma6Equation14LeftTerm_eq
    {q : ℕ} (hq : q ≠ 0) (H : ℕ) (s : ℂ) :
    lemma6Equation14LeftTerm H q s =
      letI : NeZero q := ⟨hq⟩
      ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
        ‖1 - DirichletCharacter.LFunction χ s *
          lemma6MollifierAt H s χ‖ ^ 2 else 0 := by
  simp [lemma6Equation14LeftTerm, hq]

/-- At most `φ(q)` characters are primitive, so a constant primitive
character sum is cancelled by the outer `1/φ(q)` weight. -/
theorem inv_totient_mul_primitive_const_sum_le
    {q : ℕ} (hq : 1 ≤ q) {A : ℝ} (hA : 0 ≤ A) :
    (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then A else 0) ≤ A := by
  letI : NeZero q := ⟨by omega⟩
  have hsum :
      (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then A else 0) ≤
        ∑ _χ : DirichletCharacter ℂ q, A := by
    apply Finset.sum_le_sum
    intro χ hχ
    split_ifs
    · exact le_rfl
    · exact hA
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have htot : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  calc
    (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then A else 0) ≤
      (q.totient : ℝ)⁻¹ *
        ∑ _χ : DirichletCharacter ℂ q, A := by
          exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htot.le)
    _ = (q.totient : ℝ)⁻¹ *
        (Fintype.card (DirichletCharacter ℂ q) : ℝ) * A := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring
    _ = A := by rw [hcard]; field_simp

/-- Equation (14) before the last scalar simplification.  The first term
is the fully assembled dyadic large-sieve bound; the second is precisely
the Pólya--Vinogradov truncation error summed over moduli. -/
theorem lemma6_equation14_of_truncation
    (htrunc : Lemma6LFunctionTruncation) :
    ∃ Cp Ct : ℝ, 0 < Cp ∧ 0 < Ct ∧
      ∀ (D Q H : ℕ) (s : ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ H → 1 < s.re →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            lemma6Equation14LeftTerm H q s ≤
          2 * (Cp * (Nat.log 2 H + 1) *
            (2 * (Q : ℝ) / H +
              (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3) +
          ∑ q ∈ Finset.Ioc D Q,
            lemma6Equation14ErrorTerm Ct H s q := by
  rcases lemma6_mollifier_remainder_large_sieve with
    ⟨Cp, hCp, hpoly⟩
  rcases norm_one_sub_LFunction_mul_mollifierAt_sq_le_of_truncation
      htrunc with ⟨Ct, hCt, hpoint⟩
  refine ⟨Cp, Ct, hCp, hCt, ?_⟩
  intro D Q H s hD hDQ hH hs
  have hpolyBound := hpoly D Q H s hD hDQ hH hs.le
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        lemma6Equation14LeftTerm H q s ≤
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          (2 * ‖lemma6MollifierRemainderPolynomial H
              (lemma6DirichletPhase χ s)‖ ^ 2 +
            lemma6Equation14ErrorTerm Ct H s q) else 0) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqD := (Finset.mem_Ioc.mp hq).1
        have hq0 : q ≠ 0 := by omega
        letI : NeZero q := ⟨hq0⟩
        rw [lemma6Equation14LeftTerm_eq hq0]
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro χ hχ
          split_ifs with hp
          · simpa only [lemma6Equation14ErrorTerm] using
              hpoint (by omega : 2 ≤ q) hH hs χ hp
          · exact le_rfl
        · positivity
    _ ≤ 2 * (∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            ‖lemma6MollifierRemainderPolynomial H
              (lemma6DirichletPhase χ s)‖ ^ 2 else 0)) +
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            lemma6Equation14ErrorTerm Ct H s q else 0) := by
      apply le_of_eq
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      have hqD := (Finset.mem_Ioc.mp hq).1
      letI : NeZero q := ⟨by omega⟩
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      conv_rhs =>
        rhs
        rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro χ hχ
      split_ifs <;> ring
    _ ≤ 2 * (Cp * (Nat.log 2 H + 1) *
          (2 * (Q : ℝ) / H +
            (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
          (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3) +
        ∑ q ∈ Finset.Ioc D Q,
          lemma6Equation14ErrorTerm Ct H s q := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hpolyBound (by norm_num)
      · apply Finset.sum_le_sum
        intro q hq
        have hqD := (Finset.mem_Ioc.mp hq).1
        exact inv_totient_mul_primitive_const_sum_le
          (by omega : 1 ≤ q)
          (lemma6Equation14ErrorTerm_nonneg Ct H s q)

/-- Fully scalar equation (14).  This is the exact formal counterpart of
Chen's displayed estimate before replacing harmonic and dyadic logarithms
by powers of `log x`. -/
theorem lemma6_equation14
    : ∃ Cp Ct : ℝ, 0 < Cp ∧ 0 < Ct ∧
      ∀ (D Q H : ℕ) (s : ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ H → 1 < s.re →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            lemma6Equation14LeftTerm H q s ≤
          2 * (Cp * (Nat.log 2 H + 1) *
            (2 * (Q : ℝ) / H +
              (Nat.log 2 H + 1) * (D : ℝ)⁻¹) *
            (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3) +
          (Q : ℝ) *
            (2 * ((Ct * ‖s‖ * Real.sqrt Q * Real.log (2 * Q) / H) ^ 2 *
              (harmonic H : ℝ) ^ 2)) := by
  rcases lemma6_equation14_of_truncation lemma6LFunctionTruncation with
    ⟨Cp, Ct, hCp, hCt, hbound⟩
  refine ⟨Cp, Ct, hCp, hCt, ?_⟩
  intro D Q H s hD hDQ hH hs
  apply (hbound D Q H s hD hDQ hH hs).trans
  exact add_le_add_right
    (sum_lemma6Equation14ErrorTerm_le (s := s) hCt.le hD hDQ hH) _

end Chen

end

