module

public import Green64.Library.ChenTheorem.Lemma5.Core
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.SelbergSieve

@[expose] public section

/-!
# Sieve / Foundation / Lemma5 / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma5.Arithmetic -/

section

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- Every index retained by the smoothed `M` sum gives an integer argument
at most `x`. -/
theorem smoothedMArgument_le
    {x n : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    (hn : n ∈ smoothedMIndices x q) :
    q.1 * q.2 * n ≤ x := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with ⟨hp₁, hp₂, _⟩
  have hden : 0 < (q.1 : ℝ) * q.2 :=
    mul_pos (by exact_mod_cast hp₁.pos) (by exact_mod_cast hp₂.pos)
  have hn' := hn
  simp only [smoothedMIndices, Finset.mem_filter,
    Finset.mem_range] at hn'
  have hreal :
      (n : ℝ) * ((q.1 : ℝ) * q.2) ≤ x :=
    (le_div_iff₀ hden).mp hn'.2
  have hnat : n * (q.1 * q.2) ≤ x := by
    exact_mod_cast hreal
  simpa [mul_assoc, mul_comm, mul_left_comm] using hnat

/-- The divisor factor in equation (11) is uniformly bounded on the
smoothed range.  The zero displacement is harmless because `0.divisors` is
empty. -/
theorem displacement_divisors_card_le
    {m x : ℕ} (hm : m ≤ x) :
    ((Int.natAbs ((m : ℤ) - x)).divisors.card : ℝ) ≤
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 24) := by
  let a := Int.natAbs ((m : ℤ) - x)
  by_cases ha0 : a = 0
  · simp only [a, ha0, Nat.divisors_zero, Finset.card_empty,
      Nat.cast_zero]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_nonneg
      (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  · have hcard := card_divisors_cast_le_rpow ha0
    have haeq : a = x - m := by
      simpa only [a] using
        (Int.natAbs_natCast_sub_natCast_of_le hm)
    have hale : a ≤ x := by omega
    have hpow :
        (a : ℝ) ^ ((1 : ℝ) / 24) ≤
          (x : ℝ) ^ ((1 : ℝ) / 24) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hale)
        (by norm_num)
    exact hcard.trans
      (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- If a prime power divides the argument of the primitive-character
majorant, coprimality removes every conductor divisible by its base prime. -/
theorem primitiveAssociateMajorant_le_primeFilter
    {d x m p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hpm : p ^ e ∣ m) :
    primitiveAssociateMajorant d x m ≤
      ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
        (Nat.gcd (Int.natAbs ((m : ℤ) - x)) k : ℝ) := by
  rw [primitiveAssociateMajorant]
  have hsum :
      (∑ k : ↥d.divisors,
          if k.1 = 1 then 0
          else if m.Coprime k.1 then
            (Nat.gcd (Int.natAbs ((m : ℤ) - x)) k.1 : ℝ)
          else 0) =
        ∑ k ∈ d.divisors,
          if k = 1 then 0
          else if m.Coprime k then
            (Nat.gcd (Int.natAbs ((m : ℤ) - x)) k : ℝ)
          else 0 := by
    symm
    exact Finset.sum_subtype d.divisors (by simp)
      (fun k =>
        if k = 1 then 0
        else if m.Coprime k then
          (Nat.gcd (Int.natAbs ((m : ℤ) - x)) k : ℝ)
        else 0)
  rw [hsum]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk1 : k = 1
  · subst k
    simp [hp.ne_one]
  · rw [if_neg hk1]
    by_cases hmk : m.Coprime k
    · rw [if_pos hmk]
      have hpowcop : (p ^ e).Coprime k :=
        Nat.Coprime.of_dvd_left hpm hmk
      have hpcop : p.Coprime k :=
        (Nat.coprime_pow_left_iff he p k).mp hpowcop
      rw [if_pos (hp.coprime_iff_not_dvd.mp hpcop)]
    · rw [if_neg hmk]
      positivity

/-- Equation (11), before summing over the two outer prime variables and the
smoothed von Mangoldt index: a fixed `(q,n)` contribution is controlled by
the least prime factor of `n` and the divisor count of its displacement from
`x`. -/
theorem mFiveArithmetic_inner_le
    {x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : 0 ≤ ε)
    (q : ℕ × ℕ) (n : ℕ) :
    ∑ d ∈ sieveModuli x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d x (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((Int.natAbs
                (((q.1 * q.2 * n : ℕ) : ℤ) - x)).divisors.card : ℝ)) := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  · have hnpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, e, hp, he, hn⟩ := (isPrimePow_nat_iff n).mp hnpp
    subst n
    have hminfac : (p ^ e).minFac = p := by
      rw [Nat.pow_minFac he.ne', hp.minFac_eq]
    rw [hminfac]
    let a := Int.natAbs
      (((q.1 * q.2 * p ^ e : ℕ) : ℤ) - x)
    have hbad :
        ∀ d : ℕ, ¬(p ^ e).Coprime d ↔ p ∣ d := by
      intro d
      rw [Nat.coprime_pow_left_iff he p d,
        hp.coprime_iff_not_dvd]
      tauto
    have hassoc :
        ∀ d : ℕ,
          primitiveAssociateMajorant d x
              (q.1 * q.2 * p ^ e) ≤
            ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
              (Nat.gcd a k : ℝ) := by
      intro d
      exact primitiveAssociateMajorant_le_primeFilter
        hp he (by exact dvd_mul_left (p ^ e) (q.1 * q.2))
    calc
      ∑ d ∈ sieveModuli x ε,
          (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              (3 : ℝ) ^ distinctPrimeFactors d /
                (Nat.totient d : ℝ)) *
            (if ¬(p ^ e).Coprime d then
              ArithmeticFunction.vonMangoldt (p ^ e) *
                primitiveAssociateMajorant d x
                  (q.1 * q.2 * p ^ e)
            else 0) ≤
        ∑ d ∈ sieveModuli x ε,
          ((6 : ℝ) ^ (46656 : ℝ) *
              (d : ℝ) ^ (-(5 : ℝ) / 6)) *
            (if p ∣ d then
              ArithmeticFunction.vonMangoldt (p ^ e) *
                ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                  (Nat.gcd a k : ℝ)
            else 0) := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hpd : p ∣ d
          · rw [if_pos ((hbad d).2 hpd), if_pos hpd]
            exact mul_le_mul
              (sieveCoefficient_le_decay_uniform d)
              (mul_le_mul_of_nonneg_left (hassoc d)
                ArithmeticFunction.vonMangoldt_nonneg)
              (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (primitiveAssociateMajorant_nonneg _ _ _))
              (mul_nonneg (by positivity)
                (Real.rpow_nonneg (by positivity) _))
          · simp [hpd, (hbad d).not.mpr hpd]
      _ = (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ∑ d ∈ (sieveModuli x ε).filter (p ∣ ·),
              (d : ℝ) ^ (-(5 : ℝ) / 6) *
                ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                  (Nat.gcd a k : ℝ) := by
          symm
          calc
            (6 : ℝ) ^ (46656 : ℝ) *
                ArithmeticFunction.vonMangoldt (p ^ e) *
                ∑ d ∈ (sieveModuli x ε).filter (p ∣ ·),
                  (d : ℝ) ^ (-(5 : ℝ) / 6) *
                    ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                      (Nat.gcd a k : ℝ) =
              ∑ d ∈ (sieveModuli x ε).filter (p ∣ ·),
                (6 : ℝ) ^ (46656 : ℝ) *
                  ArithmeticFunction.vonMangoldt (p ^ e) *
                  ((d : ℝ) ^ (-(5 : ℝ) / 6) *
                    ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                      (Nat.gcd a k : ℝ)) := by
                rw [Finset.mul_sum]
            _ = ∑ d ∈ sieveModuli x ε,
                ((6 : ℝ) ^ (46656 : ℝ) *
                    (d : ℝ) ^ (-(5 : ℝ) / 6)) *
                  (if p ∣ d then
                    ArithmeticFunction.vonMangoldt (p ^ e) *
                      ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                        (Nat.gcd a k : ℝ)
                  else 0) := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hpd : p ∣ d
                · simp only [if_pos hpd]
                  ring
                · simp [hpd]
      _ ≤ (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ((x : ℝ) ^ ((1 : ℝ) / 12) *
              (p : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
                (a.divisors.card : ℝ)) :=
          by
            by_cases ha0 : a = 0
            · have heq :
                  q.1 * q.2 * p ^ e = x := by
                have hz :
                    (((q.1 * q.2 * p ^ e : ℕ) : ℤ) - x) = 0 := by
                  exact Int.natAbs_eq_zero.mp (by
                    simpa only [a] using ha0)
                exact_mod_cast (sub_eq_zero.mp hz)
              have hpx : p ∣ x := by
                rw [← heq]
                exact dvd_mul_of_dvd_right
                  (dvd_pow_self p he.ne') (q.1 * q.2)
              have hDempty :
                  (sieveModuli x ε).filter (p ∣ ·) = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro d hd
                have hd' := Finset.mem_filter.mp hd
                have hddata := (Finset.mem_filter.mp hd'.1).2
                have hpone := Nat.eq_one_of_dvd_coprimes
                  hddata.2.1 hd'.2 hpx
                exact hp.ne_one hpone
              simp [hDempty, ha0]
            · exact mul_le_mul_of_nonneg_left
                (modulus_conductor_gcd_sum_le hx1 hp ha0 hε)
                (mul_nonneg (by positivity)
                  ArithmeticFunction.vonMangoldt_nonneg)
      _ = (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ((x : ℝ) ^ ((1 : ℝ) / 12) *
              (p : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
                (a.divisors.card : ℝ)) := rfl

/-- Uniform form of the fixed-index estimate, after applying the
`n^(1/24)` divisor bound to the displacement. -/
theorem mFiveArithmetic_inner_le_uniform
    {x : ℕ} {ε : ℝ} (hx : 2 ≤ x) (hε : 0 ≤ ε)
    {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    {n : ℕ} (hn : n ∈ smoothedMIndices x q) :
    ∑ d ∈ sieveModuli x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d x (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 8) *
            (harmonic x : ℝ) ^ 2 *
              (ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹) := by
  have hx1 : 1 ≤ x := by omega
  have hxpos : 0 < (x : ℝ) := by positivity
  have hm : q.1 * q.2 * n ≤ x :=
    smoothedMArgument_le hq hn
  have hdiv := displacement_divisors_card_le hm
  calc
    ∑ d ∈ sieveModuli x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d x (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((Int.natAbs
                (((q.1 * q.2 * n : ℕ) : ℤ) - x)).divisors.card : ℝ)) :=
      mFiveArithmetic_inner_le hx1 hε q n
    _ ≤ (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
                (x : ℝ) ^ ((1 : ℝ) / 24))) := by
      gcongr
    _ = (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 8) *
            (harmonic x : ℝ) ^ 2 *
              (ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹) := by
      have hexp :
          (1 : ℝ) / 8 = (1 : ℝ) / 12 + (1 : ℝ) / 24 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      ring

/-- Explicit version of Chen's equation (11).  The arithmetic part of `M₅`
has exponent `23/24`; the remaining factors are a fixed constant and three
harmonic/logarithmic losses. -/
theorem mFiveArithmeticMajorant_le_explicit
    {x : ℕ} {ε : ℝ} (hx : 2 ≤ x) (hε : 0 ≤ ε) :
    mFiveArithmeticMajorant x ε ≤
      9 * (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((23 : ℝ) / 24) *
            (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ) ^ 3 := by
  let A : ℝ :=
    (6 : ℝ) ^ (46656 : ℝ) *
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 8) *
          (harmonic x : ℝ) ^ 2
  let B : ℝ :=
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
      Real.log x * (harmonic x : ℝ)
  have hx1 : 1 ≤ x := by omega
  have hxpos : 0 < (x : ℝ) := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast hx1)
  have hH : 0 ≤ (harmonic x : ℝ) := by
    exact_mod_cast (show 0 ≤ harmonic x by
      rw [harmonic]
      positivity)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _))
      (sq_nonneg _)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (by positivity) hlogx)
      hH
  have hsum :
      mFiveArithmeticMajorant x ε ≤
        ((chenPairs x).card : ℝ) * A * B := by
    rw [mFiveArithmeticMajorant]
    calc
      ∑ q ∈ chenPairs x,
          ∑ n ∈ smoothedMIndices x q,
            ∑ d ∈ sieveModuli x ε,
              (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                  (3 : ℝ) ^ distinctPrimeFactors d /
                    (Nat.totient d : ℝ)) *
                (if ¬n.Coprime d then
                  ArithmeticFunction.vonMangoldt n *
                    primitiveAssociateMajorant d x (q.1 * q.2 * n)
                else 0) ≤
        ∑ q ∈ chenPairs x, A * B := by
          apply Finset.sum_le_sum
          intro q hq
          calc
            ∑ n ∈ smoothedMIndices x q,
                ∑ d ∈ sieveModuli x ε,
                  (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                      (3 : ℝ) ^ distinctPrimeFactors d /
                        (Nat.totient d : ℝ)) *
                    (if ¬n.Coprime d then
                      ArithmeticFunction.vonMangoldt n *
                        primitiveAssociateMajorant d x
                          (q.1 * q.2 * n)
                    else 0) ≤
              ∑ n ∈ smoothedMIndices x q,
                A * (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
                    apply Finset.sum_le_sum
                    intro n hn
                    simpa only [A] using
                      mFiveArithmetic_inner_le_uniform hx hε hq hn
            _ = A * ∑ n ∈ smoothedMIndices x q,
                ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹ := by
                    rw [Finset.mul_sum]
            _ ≤ A * B := by
                    exact mul_le_mul_of_nonneg_left
                      (by
                        simpa only [B] using
                          sum_smoothedMIndices_vonMangoldt_div_minFac_le
                            hx q)
                      hA
      _ = ((chenPairs x).card : ℝ) * A * B := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  have hcard := chenPairs_card_cast_le x hx1
  calc
    mFiveArithmeticMajorant x ε ≤
        ((chenPairs x).card : ℝ) * A * B := hsum
    _ ≤ (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * A * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard hA) hB
    _ = 9 * (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((23 : ℝ) / 24) *
            (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ) ^ 3 := by
      have hexp :
          (23 : ℝ) / 24 = (5 : ℝ) / 6 + (1 : ℝ) / 8 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      dsimp only [A, B]
      ring

/-- The five logarithmic factors in the explicit `M₅` estimate are
eventually absorbed by `x^(1/100)`. -/
theorem eventually_log_pow_five_le_rpow :
    ∀ᶠ n : ℕ in atTop,
      (Real.log n) ^ 5 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := by
  have hδ : (0 : ℝ) < 1 / 100 := by norm_num
  have hreal :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log x ^ (5 : ℝ)‖ ≤
          ‖x ^ ((1 : ℝ) / 100)‖ :=
    (isLittleO_log_rpow_rpow_atTop (5 : ℝ) hδ).eventuallyLE
  have hnat :
      ∀ᶠ n : ℕ in atTop,
        ‖Real.log (n : ℝ) ^ (5 : ℝ)‖ ≤
          ‖(n : ℝ) ^ ((1 : ℝ) / 100)‖ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_gt_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn1)
  have hn' :
      (Real.log n) ^ 5 ≤
        |(n : ℝ) ^ ((1 : ℝ) / 100)| := by
    simpa [Real.rpow_natCast, abs_of_nonneg hlogpos.le]
      using hn
  rw [abs_of_nonneg
    (Real.rpow_nonneg hnpos.le ((1 : ℝ) / 100))] at hn'
  exact hn'

/-- The fixed positive constant left after absorbing all logarithmic losses
in equation (11). -/
noncomputable def mFivePowerConstant : ℝ :=
  72 * (6 : ℝ) ^ (46656 : ℝ) *
    (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
      ((Real.log 2)⁻¹ + 1)

theorem mFivePowerConstant_pos : 0 < mFivePowerConstant := by
  rw [mFivePowerConstant]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The three harmonic factors, the logarithm, and the ceiling in equation
(11) cost at most five powers of `log x`. -/
theorem mFive_log_loss_le
    {x : ℕ} (hlogOne : 1 ≤ Real.log (x : ℝ)) :
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
        Real.log x * (harmonic x : ℝ) ^ 3 ≤
      8 * ((Real.log 2)⁻¹ + 1) * (Real.log x) ^ 5 := by
  let L : ℝ := Real.log x
  let H : ℝ := harmonic x
  let K : ℝ := (Real.log 2)⁻¹ + 1
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    linarith
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    positivity
  have hHle : H ≤ 2 * L := by
    dsimp only [H, L]
    have hH := harmonic_le_one_add_log x
    linarith
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hceil :
      (⌈L / Real.log 2⌉₊ : ℝ) ≤ K * L := by
    have hy0 : 0 ≤ L / Real.log 2 := by positivity
    calc
      (⌈L / Real.log 2⌉₊ : ℝ) ≤ L / Real.log 2 + 1 :=
        (Nat.ceil_lt_add_one hy0).le
      _ = (Real.log 2)⁻¹ * L + 1 := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ (Real.log 2)⁻¹ * L + L := by
        linarith
      _ = K * L := by
        dsimp only [K]
        ring
  calc
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
        Real.log x * (harmonic x : ℝ) ^ 3 =
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ^ 3 := by rfl
    _ ≤ (K * L) * L * (2 * L) ^ 3 := by gcongr
    _ = 8 * K * L ^ 5 := by ring
    _ = 8 * ((Real.log 2)⁻¹ + 1) * (Real.log x) ^ 5 := by
      rfl

/-- Fixed-exponent form of equation (11), after absorbing its five
logarithmic factors by `x^(1/100)`. -/
theorem mFiveArithmeticMajorant_le_fixed_rpow
    {x : ℕ} {ε : ℝ} (hx : 2 ≤ x) (hε : 0 ≤ ε)
    (hlogOne : 1 ≤ Real.log (x : ℝ))
    (hlogFive :
      (Real.log x) ^ 5 ≤ (x : ℝ) ^ ((1 : ℝ) / 100)) :
    mFiveArithmeticMajorant x ε ≤
      mFivePowerConstant * (x : ℝ) ^ ((581 : ℝ) / 600) := by
  let P : ℝ :=
    9 * (6 : ℝ) ^ (46656 : ℝ) *
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((23 : ℝ) / 24)
  let K : ℝ := (Real.log 2)⁻¹ + 1
  have hxpos : 0 < (x : ℝ) := by positivity
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  calc
    mFiveArithmeticMajorant x ε ≤
        P * ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) ^ 3) := by
      simpa only [P, mul_assoc] using
        (mFiveArithmeticMajorant_le_explicit
          (x := x) (ε := ε) hx hε)
    _ ≤ P * (8 * K * (Real.log x) ^ 5) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [K] using mFive_log_loss_le hlogOne) hP0
    _ ≤ P * (8 * K *
        (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogFive
          (mul_nonneg (by norm_num) hK0)) hP0
    _ = mFivePowerConstant *
        (x : ℝ) ^ ((581 : ℝ) / 600) := by
      have hexp :
          (581 : ℝ) / 600 =
            (23 : ℝ) / 24 + (1 : ℝ) / 100 := by
        norm_num
      rw [mFivePowerConstant, hexp, Real.rpow_add hxpos]
      dsimp only [P, K]
      ring

/-- The explicit equation-(11) bound implies the `x^(1-ε/3)` saving used
in the final assembly of Lemma 5. -/
theorem eventually_mFiveArithmeticMajorant_le_rpow
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop,
      mFiveArithmeticMajorant x ε ≤
        mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
  have hlogOneReal :
      ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [eventually_log_pow_five_le_rpow, hlogOne,
    eventually_ge_atTop 2] with x hlogFive hlogOne hx2
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  calc
    mFiveArithmeticMajorant x ε ≤
        mFivePowerConstant * (x : ℝ) ^ ((581 : ℝ) / 600) :=
      mFiveArithmeticMajorant_le_fixed_rpow
        hx2 hε0.le hlogOne hlogFive
    _ ≤ mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hxone (by linarith))
        mFivePowerConstant_pos.le

/-- `M₅` itself has the power saving required by Lemma 5. -/
theorem eventually_mFive_le_rpow
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, Even x →
      mFive x ε ≤
        mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
  have hxlargeEventually :
      ∀ᶠ x : ℕ in atTop, Real.exp 3 ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 3))
  filter_upwards
      [eventually_mFiveArithmeticMajorant_le_rpow hε0 hε1,
        hxlargeEventually] with x hmajor hxlarge
  intro hxeven
  exact (mFive_le_arithmeticMajorant hxeven hxlarge).trans hmajor

/-- Equations (6)–(11), with the formula-(5) smoothing error deliberately
kept separate: the smoothed sieve expansion is bounded by `M₁ + M₂` plus a
fixed power saving. -/
theorem smoothedSieveExpansion_power_bound
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      smoothedSieveExpansion x ε ≤
        mOne x ε + mTwo x ε +
          C * (x : ℝ) ^ (1 - ε / 3) := by
  obtain ⟨C₃, hC₃, hthree⟩ :=
    abs_mThree_power_bound hε0 hε1
  let C : ℝ := C₃ + mFivePowerConstant
  refine ⟨C, add_pos hC₃ mFivePowerConstant_pos, ?_⟩
  filter_upwards [hthree, eventually_mFive_le_rpow hε0 hε1,
    eventually_ge_atTop 1] with x hthree hfive hx1
  intro hxeven
  have hsmooth :=
    smoothedSieveExpansion_le hxeven hx1 hε0.le
  have hfour := mFour_le_mTwo_add_mFive x ε
  calc
    smoothedSieveExpansion x ε ≤
        mOne x ε + |mThree x ε| + mFour x ε := hsmooth
    _ ≤ mOne x ε +
        C₃ * (x : ℝ) ^ (1 - ε / 3) +
          (mTwo x ε + mFive x ε) := by
      gcongr
      exact hthree hxeven
    _ ≤ mOne x ε +
        C₃ * (x : ℝ) ^ (1 - ε / 3) +
          (mTwo x ε +
            mFivePowerConstant *
              (x : ℝ) ^ (1 - ε / 3)) := by
      gcongr
      exact hfive hxeven
    _ = mOne x ε + mTwo x ε +
        C * (x : ℝ) ^ (1 - ε / 3) := by
      dsimp only [C]
      ring

end Chen

end

/-! ## ChenTheorem.Lemma5.Smoothing -/

section

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-! ### Formula (5): smoothing and the square-sieve expansion -/

/-- The first term on the right of formula (5), before the roughness
indicator is replaced by the square of the Selberg divisor sum. -/
noncomputable def smoothedRoughM (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ sieveMIndices x q,
        ArithmeticFunction.vonMangoldt n *
          chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n))

/-- The exact loss incurred when inserting Chen's smoothing function into
`M`.  Keeping it as a positive finite sum makes the analytic content of
formula (5) explicit. -/
noncomputable def sieveMSmoothingError (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ sieveMIndices x q,
        ArithmeticFunction.vonMangoldt n *
          (1 - chenPhi x
            ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)))

/-- Inserting `Φ` is an exact decomposition of `M` into its smoothed part
and the smoothing loss. -/
theorem sieveM_eq_smoothedRoughM_add_smoothingError (x : ℕ) :
    sieveM x = smoothedRoughM x + sieveMSmoothingError x := by
  unfold sieveM smoothedRoughM sieveMSmoothingError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The smoothing loss is nonnegative once the pair logarithms are
positive and Lemma 1 supplies `Φ ≤ 1`. -/
theorem sieveMSmoothingError_nonneg
    {x : ℕ} (hx : 1 < x) :
    0 ≤ sieveMSmoothingError x := by
  unfold sieveMSmoothingError
  apply Finset.sum_nonneg
  intro q hq
  have hY : 1 < (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    one_lt_pairQuotient hq
  have hlog : 0 < Real.log
      ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
    Real.log_pos hY
  apply mul_nonneg (inv_nonneg.mpr hlog.le)
  apply Finset.sum_nonneg
  intro n hn
  have hy : 0 ≤
      (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (sub_nonneg.mpr (chenPhi_le_one x
      (by exact_mod_cast hx) hy))

/-- The thin upper-end interval in which Lemma 1 does not yet give
`1 - Φ ≤ x⁻⁰·¹`. -/
noncomputable def smoothingBoundaryIndices
    (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (sieveMIndices x q).filter fun n =>
    (x : ℝ) / ((q.1 : ℝ) * q.2 * n) <
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))

/-- Weighted rough mass in the transition interval of the smoothing
kernel. -/
noncomputable def smoothingBoundaryMass (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ smoothingBoundaryIndices x q,
        ArithmeticFunction.vonMangoldt n

/-- Transition mass whose von Mangoldt index has small base prime. -/
noncomputable def smoothingBoundarySmallBaseMass (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ (smoothingBoundaryIndices x q).filter fun n =>
          (n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100),
        ArithmeticFunction.vonMangoldt n

/-- Transition mass with base prime larger than `x^(1/100)`.  This is the
part to which the two-dimensional upper-bound sieve is applied. -/
noncomputable def smoothingBoundaryLargeBaseMass (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ∑ n ∈ (smoothingBoundaryIndices x q).filter fun n =>
          ¬(n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100),
        ArithmeticFunction.vonMangoldt n

/-- Exact small/large-base partition of the transition mass. -/
theorem smoothingBoundaryMass_eq_small_add_large (x : ℕ) :
    smoothingBoundaryMass x =
      smoothingBoundarySmallBaseMass x +
        smoothingBoundaryLargeBaseMass x := by
  unfold smoothingBoundaryMass smoothingBoundarySmallBaseMass
    smoothingBoundaryLargeBaseMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add]
  congr 1
  simpa only using (Finset.sum_filter_add_sum_filter_not
    (s := smoothingBoundaryIndices x q)
    (p := fun n =>
      (n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100))
    (f := fun n => ArithmeticFunction.vonMangoldt n)).symm

/-- Lemma 1 splits the smoothing loss into a global `x⁻⁰·¹ M` term and
the genuinely short transition interval. -/
theorem sieveMSmoothingError_le_interior_add_boundary
    {x : ℕ} (hx1 : 1 < x)
    (hxlog : (10 : ℝ) ^ 4 ≤ Real.log x) :
    sieveMSmoothingError x ≤
      (x : ℝ) ^ (-(0.1 : ℝ)) * sieveM x +
        smoothingBoundaryMass x := by
  unfold sieveMSmoothingError sieveM smoothingBoundaryMass
  calc
    ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n *
              (1 - chenPhi x
                ((x : ℝ) / ((q.1 : ℝ) * q.2 * n))) ≤
      ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ((x : ℝ) ^ (-(0.1 : ℝ)) *
              ∑ n ∈ sieveMIndices x q,
                ArithmeticFunction.vonMangoldt n +
            ∑ n ∈ smoothingBoundaryIndices x q,
              ArithmeticFunction.vonMangoldt n) := by
      apply Finset.sum_le_sum
      intro q hq
      have hY : 1 < (x : ℝ) / ((q.1 : ℝ) * q.2) :=
        one_lt_pairQuotient hq
      have hlogY : 0 < Real.log
          ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
        Real.log_pos hY
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlogY.le)
      rw [Finset.mul_sum]
      rw [show
          (∑ n ∈ smoothingBoundaryIndices x q,
              ArithmeticFunction.vonMangoldt n) =
            ∑ n ∈ sieveMIndices x q,
              if (x : ℝ) / ((q.1 : ℝ) * q.2 * n) <
                  Real.exp
                    (2 * (Real.log x) ^ (-(0.1 : ℝ)))
              then ArithmeticFunction.vonMangoldt n
              else 0 by
        unfold smoothingBoundaryIndices
        rw [Finset.sum_filter]]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro n hn
      let y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2 * n)
      have hy0 : 0 ≤ y := by
        dsimp only [y]
        positivity
      have hphi0 : 0 ≤ chenPhi x y :=
        chenPhi_nonneg x (by exact_mod_cast hx1) hy0
      by_cases hboundary :
          y < Real.exp
            (2 * (Real.log x) ^ (-(0.1 : ℝ)))
      · rw [if_pos hboundary]
        change ArithmeticFunction.vonMangoldt n *
            (1 - chenPhi x y) ≤
          (x : ℝ) ^ (-(0.1 : ℝ)) *
              ArithmeticFunction.vonMangoldt n +
            ArithmeticFunction.vonMangoldt n
        have hloss : 1 - chenPhi x y ≤ 1 := by linarith
        calc
          ArithmeticFunction.vonMangoldt n *
              (1 - chenPhi x y) ≤
            ArithmeticFunction.vonMangoldt n * 1 :=
              mul_le_mul_of_nonneg_left hloss
                ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ (x : ℝ) ^ (-(0.1 : ℝ)) *
                ArithmeticFunction.vonMangoldt n +
              ArithmeticFunction.vonMangoldt n := by
            have hnonneg :
                0 ≤ (x : ℝ) ^ (-(0.1 : ℝ)) *
                  ArithmeticFunction.vonMangoldt n :=
              mul_nonneg (Real.rpow_nonneg (by positivity) _)
                ArithmeticFunction.vonMangoldt_nonneg
            linarith
      · rw [if_neg hboundary]
        change ArithmeticFunction.vonMangoldt n *
            (1 - chenPhi x y) ≤
          (x : ℝ) ^ (-(0.1 : ℝ)) *
              ArithmeticFunction.vonMangoldt n + 0
        have hylarge :
            Real.exp
                (2 * (Real.log x) ^ (-(0.1 : ℝ))) ≤ y :=
          le_of_not_gt hboundary
        have hphi :=
          chenPhi_ge (x := (x : ℝ)) (y := y)
            (by exact_mod_cast hx1) hxlog hylarge
        have hloss :
            1 - chenPhi x y ≤
              (x : ℝ) ^ (-(0.1 : ℝ)) := by
          linarith
        simpa only [add_zero, mul_comm] using
          mul_le_mul_of_nonneg_left hloss
            ArithmeticFunction.vonMangoldt_nonneg
    _ = (x : ℝ) ^ (-(0.1 : ℝ)) *
          ∑ q ∈ chenPairs x,
            (Real.log
              ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
              ∑ n ∈ sieveMIndices x q,
                ArithmeticFunction.vonMangoldt n +
        ∑ q ∈ chenPairs x,
          (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
            ∑ n ∈ smoothingBoundaryIndices x q,
              ArithmeticFunction.vonMangoldt n := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- A deliberately crude bound for `M`; after multiplication by
`x⁻⁰·¹` it is already a fixed power saving. -/
theorem sieveM_le_crude
    {x : ℕ} (hx2 : 2 ≤ x)
    (hxlarge : Real.exp 3 ≤ (x : ℝ)) :
    sieveM x ≤
      ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
        18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
          Real.log x := by
  unfold sieveM
  have hxpos : (0 : ℝ) < x := (Real.exp_pos 3).trans_le hxlarge
  have hxone : (1 : ℝ) ≤ x := by
    have h : (1 : ℝ) < Real.exp 3 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (h.trans_le hxlarge).le
  have hlogx : (3 : ℝ) ≤ Real.log x := by
    calc
      (3 : ℝ) = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (Real.exp_pos 3))
        (Set.mem_Ioi.mpr hxpos) hxlarge
  have hpair :
      ∀ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n ≤
        (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x) := by
    intro q hq
    let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
    have hY : (x : ℝ) ^ ((1 : ℝ) / 3) < Y :=
      rpow_third_lt_pairQuotient hq
    have hlogY : (1 : ℝ) ≤ Real.log Y := by
      have hlogpow :
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) =
            (1 : ℝ) / 3 * Real.log x := by
        rw [Real.log_rpow hxpos]
      have hpowpos :
          0 < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
      have hmono :
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤
            Real.log Y :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
      rw [hlogpow] at hmono
      nlinarith
    have hinvnonneg : 0 ≤ (Real.log Y)⁻¹ := by positivity
    have hinvle : (Real.log Y)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hlogY
    have hsubset :
        sieveMIndices x q ⊆ smoothedMIndices x q := by
      intro n hn
      have hn' := hn
      simp only [sieveMIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      simp only [smoothedMIndices, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨hn'.1, hn'.2.1⟩
    have hrough :
        ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n ≤
          ∑ n ∈ smoothedMIndices x q,
            ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _ _ =>
          ArithmeticFunction.vonMangoldt_nonneg)
    have hmass :
        ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n ≤
          (Y + 2) * Real.log x :=
      hrough.trans (by
        simpa only [Y] using
          sum_smoothedMIndices_vonMangoldt_le hx2 q)
    have hmass0 :
        0 ≤ ∑ n ∈ sieveMIndices x q,
          ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_nonneg
      intro n hn
      exact ArithmeticFunction.vonMangoldt_nonneg
    calc
      (Real.log
          ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n =
        (Real.log Y)⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n := by rfl
      _ ≤ 1 * ((Y + 2) * Real.log x) :=
        mul_le_mul hinvle hmass hmass0 (by norm_num)
      _ = ((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x := by simp only [Y, one_mul]
  calc
    ∑ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q,
            ArithmeticFunction.vonMangoldt n ≤
      ∑ q ∈ chenPairs x,
        (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x) := by
      apply Finset.sum_le_sum
      exact hpair
    _ = (∑ q ∈ chenPairs x,
          ((x : ℝ) / ((q.1 : ℝ) * q.2) + 2)) *
        Real.log x := by rw [Finset.sum_mul]
    _ ≤ ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
          2 * ((chenPairs x).card : ℝ)) *
        Real.log x := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hYsum :
          ∑ q ∈ chenPairs x,
              (x : ℝ) / ((q.1 : ℝ) * q.2) ≤
            (x : ℝ) * (harmonic x : ℝ) ^ 2 := by
        simpa only [sub_zero, zero_div, Real.rpow_one] using
        (sum_pairQuotient_rpow_le_harmonic
          x (ε := 0) (by norm_num))
      calc
        (∑ q ∈ chenPairs x,
            (x : ℝ) / ((q.1 : ℝ) * q.2)) +
              ((chenPairs x).card : ℝ) * 2 =
            2 * ((chenPairs x).card : ℝ) +
              ∑ q ∈ chenPairs x,
                (x : ℝ) / ((q.1 : ℝ) * q.2) := by ring
        _ ≤ 2 * ((chenPairs x).card : ℝ) +
              (x : ℝ) * (harmonic x : ℝ) ^ 2 :=
          add_le_add_right hYsum _
        _ = (x : ℝ) * (harmonic x : ℝ) ^ 2 +
              2 * ((chenPairs x).card : ℝ) := by ring
    _ ≤ ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
          18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
        Real.log x := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard := chenPairs_card_cast_le x
        (show 1 ≤ x by omega)
      have hcard' :
          2 * ((chenPairs x).card : ℝ) ≤
            18 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
        nlinarith
      simpa [add_comm] using
        add_le_add_left hcard'
          ((x : ℝ) * (harmonic x : ℝ) ^ 2)

/-- If the base prime of a prime power is at most `z`, its von Mangoldt
weight is controlled by `z · Λ(n)/minFac(n)`. -/
theorem vonMangoldt_le_rpow_mul_div_minFac
    {x n : ℕ}
    (hsmall :
      (n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100)) :
    ArithmeticFunction.vonMangoldt n ≤
      (x : ℝ) ^ ((1 : ℝ) / 100) *
        (ArithmeticFunction.vonMangoldt n *
          (n.minFac : ℝ)⁻¹) := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  · have hn1 : n ≠ 1 := by
      intro hn
      subst n
      simp at hΛ
    have hp : n.minFac.Prime := Nat.minFac_prime hn1
    have hp0 : (n.minFac : ℝ) ≠ 0 := by
      exact_mod_cast hp.ne_zero
    have hterm :
        0 ≤ ArithmeticFunction.vonMangoldt n *
          (n.minFac : ℝ)⁻¹ :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (inv_nonneg.mpr (by positivity))
    calc
      ArithmeticFunction.vonMangoldt n =
          (n.minFac : ℝ) *
            (ArithmeticFunction.vonMangoldt n *
              (n.minFac : ℝ)⁻¹) := by
        field_simp
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 100) *
          (ArithmeticFunction.vonMangoldt n *
            (n.minFac : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hsmall hterm

/-- The small-base-prime part of the smoothing transition is already a
fixed power saving. -/
theorem smoothingBoundarySmallBaseMass_le_explicit
    {x : ℕ} (hx2 : 2 ≤ x)
    (hxlarge : Real.exp 3 ≤ (x : ℝ)) :
    smoothingBoundarySmallBaseMass x ≤
      9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
        (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) := by
  unfold smoothingBoundarySmallBaseMass
  have hxpos : (0 : ℝ) < x := (Real.exp_pos 3).trans_le hxlarge
  have hxone : (1 : ℝ) ≤ x := by
    have h : (1 : ℝ) < Real.exp 3 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (h.trans_le hxlarge).le
  have hlogx : (3 : ℝ) ≤ Real.log x := by
    calc
      (3 : ℝ) = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (Real.exp_pos 3))
        (Set.mem_Ioi.mpr hxpos) hxlarge
  let B : ℝ :=
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
      Real.log x * (harmonic x : ℝ)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hH : 0 ≤ (harmonic x : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      positivity
    exact mul_nonneg
      (mul_nonneg (by positivity) (by linarith)) hH
  have hpair :
      ∀ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (smoothingBoundaryIndices x q).filter
              (fun n => (n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
    intro q hq
    let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
    have hY : (x : ℝ) ^ ((1 : ℝ) / 3) < Y :=
      rpow_third_lt_pairQuotient hq
    have hlogY : (1 : ℝ) ≤ Real.log Y := by
      have hlogpow :
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) =
            (1 : ℝ) / 3 * Real.log x := by
        rw [Real.log_rpow hxpos]
      have hpowpos :
          0 < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
      have hmono :
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤
            Real.log Y :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
      rw [hlogpow] at hmono
      nlinarith
    have hinv0 : 0 ≤ (Real.log Y)⁻¹ := by positivity
    have hinvle : (Real.log Y)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hlogY
    let S : Finset ℕ :=
      (smoothingBoundaryIndices x q).filter
        (fun n => (n.minFac : ℝ) ≤
          (x : ℝ) ^ ((1 : ℝ) / 100))
    have hSsubset : S ⊆ smoothedMIndices x q := by
      intro n hn
      have hnBoundary :=
        (Finset.mem_filter.mp hn).1
      have hnSieve :=
        (Finset.mem_filter.mp hnBoundary).1
      have hn' := hnSieve
      simp only [sieveMIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      simp only [smoothedMIndices, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨hn'.1, hn'.2.1⟩
    have hsum :
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            ∑ n ∈ smoothedMIndices x q,
              ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹ := by
      calc
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
            ∑ n ∈ S,
              (x : ℝ) ^ ((1 : ℝ) / 100) *
                (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro n hn
          exact vonMangoldt_le_rpow_mul_div_minFac
            (Finset.mem_filter.mp hn).2
        _ ≤ ∑ n ∈ smoothedMIndices x q,
              (x : ℝ) ^ ((1 : ℝ) / 100) *
                (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSsubset
          intro n hn _
          exact mul_nonneg
            (Real.rpow_nonneg hxpos.le _)
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (inv_nonneg.mpr (by positivity)))
        _ = (x : ℝ) ^ ((1 : ℝ) / 100) *
            ∑ n ∈ smoothedMIndices x q,
              ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
    have hsumB :
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B :=
      hsum.trans (mul_le_mul_of_nonneg_left
        (by simpa only [B] using
          (sum_smoothedMIndices_vonMangoldt_div_minFac_le
            hx2 q))
        (Real.rpow_nonneg hxpos.le _))
    have hsum0 :
        0 ≤ ∑ n ∈ S,
          ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_nonneg
      intro n hn
      exact ArithmeticFunction.vonMangoldt_nonneg
    have hmul :
        (Real.log Y)⁻¹ *
            ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
      calc
        (Real.log Y)⁻¹ *
            ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          1 * ∑ n ∈ S,
            ArithmeticFunction.vonMangoldt n :=
          mul_le_mul_of_nonneg_right hinvle hsum0
        _ ≤ 1 * ((x : ℝ) ^ ((1 : ℝ) / 100) * B) :=
          mul_le_mul_of_nonneg_left hsumB (by norm_num)
        _ = (x : ℝ) ^ ((1 : ℝ) / 100) * B := one_mul _
    simpa only [Y, S] using hmul
  calc
    ∑ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (smoothingBoundaryIndices x q).filter
              (fun n => (n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
      ∑ q ∈ chenPairs x,
        (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
      apply Finset.sum_le_sum
      exact hpair
    _ = ((chenPairs x).card : ℝ) *
        ((x : ℝ) ^ ((1 : ℝ) / 100) * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
        ((x : ℝ) ^ ((1 : ℝ) / 100) * B) := by
      exact mul_le_mul_of_nonneg_right
        (chenPairs_card_cast_le x (show 1 ≤ x by omega))
        (mul_nonneg (Real.rpow_nonneg hxpos.le _) hB0)
    _ = 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
        (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) := by
      have hexp :
          (253 : ℝ) / 300 =
            (5 : ℝ) / 6 + (1 : ℝ) / 100 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      dsimp only [B]
      ring

/-- The small-base-prime transition mass is negligible in the logarithmic
error scale of Lemma 5. -/
theorem eventually_smoothingBoundarySmallBaseMass_le :
    ∀ᶠ x : ℕ in atTop,
      smoothingBoundarySmallBaseMass x ≤
        (18 * ((Real.log 2)⁻¹ + 1)) *
          (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  have hlogOneReal :
      ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  have hxlargeEventually :
      ∀ᶠ x : ℕ in atTop, Real.exp 3 ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 3))
  filter_upwards [eventually_log_pow_five_le_rpow, hlogOne,
    hxlargeEventually, eventually_ge_atTop 2,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 10) (r := (2.01 : ℝ))
        (by norm_num)] with
      x hlogFive hlogOne hxlarge hx2 hpower
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := zero_lt_one.trans_le hxone
  let L : ℝ := Real.log x
  let H : ℝ := harmonic x
  let K : ℝ := (Real.log 2)⁻¹ + 1
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    linarith
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    positivity
  have hHle : H ≤ 2 * L := by
    dsimp only [H, L]
    have hH := harmonic_le_one_add_log x
    linarith
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hceil :
      (⌈L / Real.log 2⌉₊ : ℝ) ≤ K * L := by
    have hy0 : 0 ≤ L / Real.log 2 := by positivity
    calc
      (⌈L / Real.log 2⌉₊ : ℝ) ≤ L / Real.log 2 + 1 :=
        (Nat.ceil_lt_add_one hy0).le
      _ = (Real.log 2)⁻¹ * L + 1 := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ (Real.log 2)⁻¹ * L + L := by
        linarith
      _ = K * L := by
        dsimp only [K]
        ring
  have hlogs :
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ≤
        2 * K * L ^ 5 := by
    calc
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ≤
          (K * L) * L * (2 * L) := by gcongr
      _ = 2 * K * L ^ 3 := by ring
      _ ≤ 2 * K * L ^ 5 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (show 1 ≤ L by
            simpa only [L] using hlogOne) (by norm_num))
          (mul_nonneg (by norm_num) hK0)
  have hexplicit :=
    smoothingBoundarySmallBaseMass_le_explicit hx2 hxlarge
  calc
    smoothingBoundarySmallBaseMass x ≤
        9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          ((⌈L / Real.log 2⌉₊ : ℝ) * L * H) := by
      simpa only [L, H, mul_assoc] using hexplicit
    _ ≤ 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          (2 * K * L ^ 5) := by
      gcongr
    _ ≤ 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          (2 * K * (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      dsimp only [L] at hlogFive ⊢
      gcongr
    _ = (18 * K) * (x : ℝ) ^ ((64 : ℝ) / 75) := by
      have hexp :
          (64 : ℝ) / 75 =
            (253 : ℝ) / 300 + (1 : ℝ) / 100 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      ring
    _ ≤ (18 * K) * (x : ℝ) ^ (1 - (1 : ℝ) / 10) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
      · exact mul_nonneg (by norm_num) hK0
    _ ≤ (18 * K) *
        ((x : ℝ) / (Real.log x) ^ (2.01 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hpower
        (mul_nonneg (by norm_num) hK0)
    _ = (18 * ((Real.log 2)⁻¹ + 1)) *
        (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [K]
      ring

/-- The global `x⁻⁰·¹ M` part of the smoothing loss is negligible compared
with `x / (log x)^2.01`. -/
theorem eventually_smoothingInterior_le :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (-(0.1 : ℝ)) * sieveM x ≤
        19 * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
  have hlogOneReal :
      ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  have hxlargeEventually :
      ∀ᶠ x : ℕ in atTop, Real.exp 3 ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 3))
  have hδ01 : (0 : ℝ) < 1 / 100 := by norm_num
  have hδ08 : (0 : ℝ) < 8 / 100 := by norm_num
  filter_upwards [eventually_harmonic_sq_le_rpow hδ01,
    eventually_log_pow_four_le_rpow, hlogOne,
    hxlargeEventually, eventually_ge_atTop 2,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (8 : ℝ) / 100) (r := (2.01 : ℝ)) hδ08] with
      x hH hlogFour hlogOne hxlarge hx2 hpower
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := zero_lt_one.trans_le hxone
  have hpow01one :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.one_le_rpow hxone (by norm_num)
  have hlog :
      Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
    calc
      Real.log x ≤ (Real.log x) ^ 4 := by
        nlinarith [sq_nonneg (Real.log x),
          sq_nonneg ((Real.log x) ^ 2 - Real.log x)]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := hlogFour
  have h56 :
      (x : ℝ) ^ ((5 : ℝ) / 6) ≤ (x : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)).trans_eq
      (Real.rpow_one x)
  have hM := sieveM_le_crude hx2 hxlarge
  have hxx :
      (x : ℝ) ≤ (x : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 100) :=
    le_mul_of_one_le_right hxpos.le hpow01one
  have hinside :
      (x : ℝ) * (harmonic x : ℝ) ^ 2 +
          18 * (x : ℝ) ^ ((5 : ℝ) / 6) ≤
        (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 100) +
          18 * ((x : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100)) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hH hxpos.le)
      (mul_le_mul_of_nonneg_left (h56.trans hxx) (by norm_num))
  have hM' :
      sieveM x ≤
        19 * (x : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            (x : ℝ) ^ ((1 : ℝ) / 100) := by
    calc
      sieveM x ≤
          ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
            18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
              Real.log x := hM
      _ ≤ ((x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 100) +
            18 * ((x : ℝ) *
              (x : ℝ) ^ ((1 : ℝ) / 100))) *
              (x : ℝ) ^ ((1 : ℝ) / 100) := by
        exact mul_le_mul hinside hlog
          (by linarith) (by positivity)
      _ = 19 * (x : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            (x : ℝ) ^ ((1 : ℝ) / 100) := by ring
  calc
    (x : ℝ) ^ (-(0.1 : ℝ)) * sieveM x ≤
        (x : ℝ) ^ (-(0.1 : ℝ)) *
          (19 * (x : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100) *
              (x : ℝ) ^ ((1 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hM'
        (Real.rpow_nonneg hxpos.le _)
    _ = 19 * ((x : ℝ) ^ (-(0.1 : ℝ)) *
          (x : ℝ) ^ (1 : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100) *
              (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      rw [Real.rpow_one]
      ring
    _ = 19 * (x : ℝ) ^ ((92 : ℝ) / 100) := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos,
        ← Real.rpow_add hxpos]
      congr 2
      norm_num
    _ ≤ 19 * ((x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [show (92 : ℝ) / 100 =
          1 - (8 : ℝ) / 100 by norm_num] using hpower
    _ = 19 * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by ring

/-- The Selberg divisor sum over positive divisors of `a` which are coprime
to `x`.  The finite ambient range contains the support of every sieve
weight used below. -/
noncomputable def sieveDivisorSum
    (x : ℕ) (ε : ℝ) (a : ℕ) : ℝ :=
  ∑ d ∈ (Finset.range (x + 1)).filter fun d =>
      1 ≤ d ∧ d.Coprime x ∧ d ∣ a,
    sieveWeight x ε d

/-- Positive divisor indices, coprime to `x`, in the common finite ambient
range used to expand the square sieve. -/
def sieveDivisorUniverse (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun d => 1 ≤ d ∧ d.Coprime x

/-- Indicator form of the divisor sum, convenient for expanding its
square. -/
theorem sieveDivisorSum_eq_sum_universe
    (x : ℕ) (ε : ℝ) (a : ℕ) :
    sieveDivisorSum x ε a =
      ∑ d ∈ sieveDivisorUniverse x,
        if d ∣ a then sieveWeight x ε d else 0 := by
  unfold sieveDivisorSum sieveDivisorUniverse
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdpos : 1 ≤ d
  · by_cases hdcop : d.Coprime x
    · by_cases hda : d ∣ a
      · simp [hdpos, hda]
      · simp [hdpos, hda]
    · simp [hdpos, hdcop]
  · simp [hdpos]

/-- A pair of nonzero sieve weights in the divisor universe has its lcm in
the collected modulus range. -/
theorem lcm_mem_sieveModuli_of_sieveWeight_mul_ne_zero
    {x d₁ d₂ : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hd₁ : d₁ ∈ sieveDivisorUniverse x)
    (hd₂ : d₂ ∈ sieveDivisorUniverse x)
    (hweight :
      sieveWeight x ε d₁ * sieveWeight x ε d₂ ≠ 0) :
    d₁.lcm d₂ ∈ sieveModuli x ε := by
  have hd₁data := (Finset.mem_filter.mp hd₁).2
  have hd₂data := (Finset.mem_filter.mp hd₂).2
  have hd₁pos : 0 < d₁ := by omega
  have hd₂pos : 0 < d₂ := by omega
  have hweight₁ : sieveWeight x ε d₁ ≠ 0 := by
    intro h
    exact hweight (by rw [h, zero_mul])
  have hweight₂ : sieveWeight x ε d₂ ≠ 0 := by
    intro h
    exact hweight (by rw [h, mul_zero])
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hexp0 : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
  have hRone :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) :=
    Real.one_le_rpow hxone hexp0
  have hd₁cut :
      (d₁ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rcases sieveWeight_support hweight₁ with h | h
    · simpa only [h, Nat.cast_one] using hRone
    · exact h
  have hd₂cut :
      (d₂ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rcases sieveWeight_support hweight₂ with h | h
    · simpa only [h, Nat.cast_one] using hRone
    · exact h
  have hlcmpos : 0 < d₁.lcm d₂ := by
    apply Nat.pos_of_ne_zero
    intro h
    have hz := Nat.lcm_eq_zero_iff.mp h
    omega
  have hlcmcop : (d₁.lcm d₂).Coprime x :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul d₁ d₂)
      (hd₁data.2.mul_left hd₂data.2)
  have hlcmle : d₁.lcm d₂ ≤ d₁ * d₂ :=
    Nat.lcm_le_mul hd₁pos hd₂pos
  have hprod :
      ((d₁ * d₂ : ℕ) : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    norm_num only [Nat.cast_mul]
    exact mul_le_mul hd₁cut hd₂cut (by positivity) (by positivity)
  have hpow :
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) =
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hlcmcut :
      (d₁.lcm d₂ : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    calc
      (d₁.lcm d₂ : ℝ) ≤ (d₁ * d₂ : ℕ) := by
        exact_mod_cast hlcmle
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := hprod
      _ = (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hpow
  have hexp_le : (1 : ℝ) / 2 - ε ≤ 1 := by linarith
  have hlcmx : d₁.lcm d₂ ≤ x := by
    have hpowx :
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ x := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hxone hexp_le
    exact_mod_cast hlcmcut.trans hpowx
  simp only [sieveModuli, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by exact ⟨by omega, hlcmcop, hlcmcut⟩⟩

/-- Collecting the expanded square of the divisor sum by
`lcm(d₁,d₂)` gives exactly `sieveLcmCoeff`. -/
theorem sieveDivisorSum_sq_eq_lcm_sum
    {x a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    (sieveDivisorSum x ε a) ^ 2 =
      ∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d *
          (if d ∣ a then 1 else 0) := by
  let U : Finset ℕ := sieveDivisorUniverse x
  let P : Finset (ℕ × ℕ) := U ×ˢ U
  let f : ℕ × ℕ → ℝ := fun q =>
    (if q.1 ∣ a then sieveWeight x ε q.1 else 0) *
      (if q.2 ∣ a then sieveWeight x ε q.2 else 0)
  have hsquare :
      (sieveDivisorSum x ε a) ^ 2 =
        ∑ q ∈ P, f q := by
    rw [sieveDivisorSum_eq_sum_universe, pow_two,
      Finset.sum_mul_sum]
    simp only [P, U, f, Finset.sum_product]
  have hsupport :
      ∑ q ∈ P, f q =
        ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ sieveModuli x ε),
            f q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hlcm :
        q.1.lcm q.2 ∈ sieveModuli x ε
    · simp [hlcm]
    · rw [if_neg hlcm]
      by_contra hf
      have hqdata := Finset.mem_product.mp hq
      have hweight :
          sieveWeight x ε q.1 *
            sieveWeight x ε q.2 ≠ 0 := by
        apply mul_ne_zero
        · intro hw
          apply hf
          dsimp only [f]
          simp [hw]
        · intro hw
          apply hf
          dsimp only [f]
          simp [hw]
      exact hlcm
        (lcm_mem_sieveModuli_of_sieveWeight_mul_ne_zero
          hx1 hε0 hεhalf
          (by simpa only [U] using hqdata.1)
          (by simpa only [U] using hqdata.2) hweight)
  have hfiber :
      ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ sieveModuli x ε),
            f q =
        ∑ d ∈ sieveModuli x ε,
          ∑ q ∈ P.filter (fun q => q.1.lcm q.2 = d),
            f q := by
    symm
    exact Finset.sum_fiberwise_eq_sum_filter P
      (sieveModuli x ε) (fun q => q.1.lcm q.2) f
  calc
    (sieveDivisorSum x ε a) ^ 2 =
        ∑ q ∈ P, f q := hsquare
    _ = ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ sieveModuli x ε),
            f q := hsupport
    _ = ∑ d ∈ sieveModuli x ε,
          ∑ q ∈ P.filter (fun q => q.1.lcm q.2 = d),
            f q := hfiber
    _ = ∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d *
          (if d ∣ a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hddata := (Finset.mem_filter.mp hd).2
      have hdpos : 0 < d := by omega
      have hdle : d ≤ x := by
        have hdrange := (Finset.mem_filter.mp hd).1
        have hdlt := Finset.mem_range.mp hdrange
        omega
      have hfin :
          P.filter (fun q => q.1.lcm q.2 = d) =
            (d.divisors ×ˢ d.divisors).filter
              (fun q => q.1.lcm q.2 = d) := by
        ext q
        simp only [P, U, sieveDivisorUniverse,
          Finset.mem_filter, Finset.mem_product,
          Finset.mem_range]
        constructor
        · intro h
          rcases h with
            ⟨⟨⟨hq₁range, hq₁pos, hq₁cop⟩,
              ⟨hq₂range, hq₂pos, hq₂cop⟩⟩, hlcm⟩
          have hq₁d : q.1 ∣ d := by
            rw [← hlcm]
            exact Nat.dvd_lcm_left q.1 q.2
          have hq₂d : q.2 ∣ d := by
            rw [← hlcm]
            exact Nat.dvd_lcm_right q.1 q.2
          exact ⟨⟨Nat.mem_divisors.mpr ⟨hq₁d, hdpos.ne'⟩,
            Nat.mem_divisors.mpr ⟨hq₂d, hdpos.ne'⟩⟩, hlcm⟩
        · intro h
          rcases h with ⟨⟨hq₁mem, hq₂mem⟩, hlcm⟩
          have hq₁d := Nat.dvd_of_mem_divisors hq₁mem
          have hq₂d := Nat.dvd_of_mem_divisors hq₂mem
          have hq₁pos : 1 ≤ q.1 :=
            Nat.pos_of_dvd_of_pos hq₁d hdpos
          have hq₂pos : 1 ≤ q.2 :=
            Nat.pos_of_dvd_of_pos hq₂d hdpos
          have hq₁cop :=
            Nat.Coprime.of_dvd_left hq₁d hddata.2.1
          have hq₂cop :=
            Nat.Coprime.of_dvd_left hq₂d hddata.2.1
          have hq₁le : q.1 ≤ d := Nat.le_of_dvd hdpos hq₁d
          have hq₂le : q.2 ≤ d := Nat.le_of_dvd hdpos hq₂d
          exact
            ⟨⟨⟨by omega, hq₁pos, hq₁cop⟩,
              ⟨by omega, hq₂pos, hq₂cop⟩⟩, hlcm⟩
      rw [hfin, sieveLcmCoeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hlcm := (Finset.mem_filter.mp hq).2
      have hqdiv := Finset.mem_product.mp
        (Finset.mem_filter.mp hq).1
      have hq₁d := Nat.dvd_of_mem_divisors hqdiv.1
      have hq₂d := Nat.dvd_of_mem_divisors hqdiv.2
      by_cases hda : d ∣ a
      · have hq₁a : q.1 ∣ a := dvd_trans hq₁d hda
        have hq₂a : q.2 ∣ a := dvd_trans hq₂d hda
        simp [f, hda, hq₁a, hq₂a]
      · have hnotboth : ¬(q.1 ∣ a ∧ q.2 ∣ a) := by
          intro h
          apply hda
          rw [← hlcm]
          exact Nat.lcm_dvd h.1 h.2
        rcases not_and_or.mp hnotboth with hq₁a | hq₂a
        · simp [f, hda, hq₁a]
        · simp [f, hda, hq₂a]

/-- On an `x^(1/4)`-rough integer, the only nonzero divisor weight is
`λ₁ = 1`. -/
theorem sieveDivisorSum_eq_one_of_rough
    {x a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (ha : chenRough x a) :
    sieveDivisorSum x ε a = 1 := by
  unfold sieveDivisorSum
  let S : Finset ℕ :=
    (Finset.range (x + 1)).filter fun d =>
      1 ≤ d ∧ d.Coprime x ∧ d ∣ a
  have h1S : 1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simp⟩
  calc
    ∑ d ∈ (Finset.range (x + 1)).filter (fun d =>
        1 ≤ d ∧ d.Coprime x ∧ d ∣ a),
        sieveWeight x ε d =
      ∑ d ∈ S, sieveWeight x ε d := by rfl
    _ = sieveWeight x ε 1 := by
      apply Finset.sum_eq_single 1
      · intro d hdS hd1
        by_contra hweight
        have hddata := (Finset.mem_filter.mp hdS).2
        have hdpos : 0 < d := by omega
        obtain ⟨p, hp, hpd⟩ :=
          Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        have hp_le_d : p ≤ d := Nat.le_of_dvd hdpos hpd
        have hdcut := (sieveWeight_support hweight).resolve_left hd1
        have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx1
        have hexp :
            (1 : ℝ) / 4 - ε / 2 ≤ (1 : ℝ) / 4 := by
          linarith
        have hdquarter :
            (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
          hdcut.trans
            (Real.rpow_le_rpow_of_exponent_le hxone hexp)
        have hpquarter :
            (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
          (show (p : ℝ) ≤ d by exact_mod_cast hp_le_d).trans
            hdquarter
        exact ha p hp hpquarter
          (dvd_trans hpd hddata.2.2)
      · intro hnot
        exact (hnot h1S).elim
    _ = 1 := sieveWeight_one x ε

/-- Every smoothed kernel is nonnegative on an admissible prime pair. -/
theorem smoothedMKernel_nonneg
    {x n : ℕ} {q : ℕ × ℕ} (hx : 1 < x)
    (hq : q ∈ chenPairs x) :
    0 ≤ smoothedMKernel x q n := by
  unfold smoothedMKernel
  have hY : 1 < (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    one_lt_pairQuotient hq
  have hlog : 0 < Real.log
      ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
    Real.log_pos hY
  have hy : 0 ≤
      (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr hlog.le)
      ArithmeticFunction.vonMangoldt_nonneg)
    (chenPhi_nonneg x (by exact_mod_cast hx) hy)

/-- Formula (5) before collecting the two divisor variables by their lcm. -/
noncomputable def squareSieveExpansion
    (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ chenPairs x,
    ∑ n ∈ smoothedMIndices x q,
      smoothedMKernel x q n *
        (sieveDivisorSum x ε (x - q.1 * q.2 * n)) ^ 2

/-- The smoothed rough sum is the same finite sum written with
`smoothedMKernel`. -/
theorem smoothedRoughM_eq_kernel_sum (x : ℕ) :
    smoothedRoughM x =
      ∑ q ∈ chenPairs x,
        ∑ n ∈ sieveMIndices x q,
          smoothedMKernel x q n := by
  unfold smoothedRoughM smoothedMKernel
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The square Selberg divisor sum majorizes the roughness indicator
pointwise. -/
theorem smoothedRoughM_le_squareSieveExpansion
    {x : ℕ} {ε : ℝ} (hx : 1 < x) (hε0 : 0 ≤ ε) :
    smoothedRoughM x ≤ squareSieveExpansion x ε := by
  rw [smoothedRoughM_eq_kernel_sum]
  unfold squareSieveExpansion
  apply Finset.sum_le_sum
  intro q hq
  have hsubset :
      sieveMIndices x q ⊆ smoothedMIndices x q := by
    intro n hn
    have hn' := hn
    simp only [sieveMIndices, Finset.mem_filter,
      Finset.mem_range] at hn'
    simp only [smoothedMIndices, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨hn'.1, hn'.2.1⟩
  calc
    ∑ n ∈ sieveMIndices x q, smoothedMKernel x q n =
        ∑ n ∈ sieveMIndices x q,
          smoothedMKernel x q n *
            (sieveDivisorSum x ε
              (x - q.1 * q.2 * n)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := hn
      simp only [sieveMIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      rw [sieveDivisorSum_eq_one_of_rough
        (show 1 ≤ x by omega) hε0 hn'.2.2]
      ring
    _ ≤ ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            (sieveDivisorSum x ε
              (x - q.1 * q.2 * n)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn _hnrough
      exact mul_nonneg (smoothedMKernel_nonneg hx hq) (sq_nonneg _)

/-- The uncollected square-sieve expansion is exactly the existing
`smoothedSieveExpansion`, whose divisor pairs are collected by their lcm. -/
theorem squareSieveExpansion_eq_smoothedSieveExpansion
    {x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    squareSieveExpansion x ε =
      smoothedSieveExpansion x ε := by
  unfold squareSieveExpansion smoothedSieveExpansion
  calc
    ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            (sieveDivisorSum x ε
              (x - q.1 * q.2 * n)) ^ 2 =
      ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            ∑ d ∈ sieveModuli x ε,
              sieveLcmCoeff x ε d *
                (if x ≡ q.1 * q.2 * n [MOD d]
                  then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro n hn
      have hm : q.1 * q.2 * n ≤ x :=
        smoothedMArgument_le hq hn
      have hsquare :=
        sieveDivisorSum_sq_eq_lcm_sum
          (x := x) (a := x - q.1 * q.2 * n)
          (ε := ε) hx1 hε0 hεhalf
      rw [hsquare]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hiff :
          x ≡ q.1 * q.2 * n [MOD d] ↔
            d ∣ x - q.1 * q.2 * n :=
        Nat.ModEq.comm.trans (Nat.modEq_iff_dvd' hm)
      by_cases hmod : x ≡ q.1 * q.2 * n [MOD d]
      · have hdvd := hiff.mp hmod
        simp [hmod, hdvd]
      · have hndvd : ¬d ∣ x - q.1 * q.2 * n := by
          intro hdvd
          exact hmod (hiff.mpr hdvd)
        simp [hmod, hndvd]
    _ = ∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d *
          ∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              smoothedMKernel x q n *
                (if x ≡ q.1 * q.2 * n [MOD d]
                  then 1 else 0) := by
      calc
        (∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              smoothedMKernel x q n *
                ∑ d ∈ sieveModuli x ε,
                  sieveLcmCoeff x ε d *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) =
          ∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              ∑ d ∈ sieveModuli x ε,
                smoothedMKernel x q n *
                  (sieveLcmCoeff x ε d *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro q hq
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
        _ =
          ∑ q ∈ chenPairs x,
            ∑ d ∈ sieveModuli x ε,
              ∑ n ∈ smoothedMIndices x q,
                smoothedMKernel x q n *
                  (sieveLcmCoeff x ε d *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.sum_comm]
        _ = ∑ d ∈ sieveModuli x ε,
            ∑ q ∈ chenPairs x,
              ∑ n ∈ smoothedMIndices x q,
                smoothedMKernel x q n *
                  (sieveLcmCoeff x ε d *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            rw [Finset.sum_comm]
        _ = ∑ d ∈ sieveModuli x ε,
            sieveLcmCoeff x ε d *
              ∑ q ∈ chenPairs x,
                ∑ n ∈ smoothedMIndices x q,
                  smoothedMKernel x q n *
                    (if x ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
    _ = ∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d *
          ∑ z ∈ smoothedMTriples x,
            smoothedMKernel x z.1 z.2 *
              (if x ≡ smoothedMArgument z [MOD d]
                then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      exact (sum_smoothedMTriples_eq_nested x
        (fun q n =>
          smoothedMKernel x q n *
            (if x ≡ q.1 * q.2 * n [MOD d]
              then 1 else 0))).symm

/-- Finite square-sieve form of the second inequality in formula (5). -/
theorem smoothedRoughM_le_smoothedSieveExpansion
    {x : ℕ} {ε : ℝ} (hx : 1 < x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    smoothedRoughM x ≤ smoothedSieveExpansion x ε := by
  calc
    smoothedRoughM x ≤ squareSieveExpansion x ε :=
      smoothedRoughM_le_squareSieveExpansion hx hε0
    _ = smoothedSieveExpansion x ε :=
      squareSieveExpansion_eq_smoothedSieveExpansion
        (show 1 ≤ x by omega) hε0 hεhalf

/-- Formula (5) with its analytic smoothing error left explicit. -/
theorem sieveM_le_smoothedSieveExpansion_add_smoothingError
    {x : ℕ} {ε : ℝ} (hx : 1 < x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    sieveM x ≤
      smoothedSieveExpansion x ε + sieveMSmoothingError x := by
  rw [sieveM_eq_smoothedRoughM_add_smoothingError]
  simpa [add_comm] using
    add_le_add_right
      (smoothedRoughM_le_smoothedSieveExpansion
        hx hε0 hεhalf) (sieveMSmoothingError x)

end Chen

end

/-! ## ChenTheorem.Lemma5.Boundary.Sieve -/

section

namespace Chen

open scoped Classical

noncomputable def transitionSieveCutoff (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((1 : ℝ) / 100)⌋₊

noncomputable def transitionSieveProduct (x : ℕ) : ℕ :=
  primorial (transitionSieveCutoff x)

theorem transitionSieveProduct_squarefree (x : ℕ) :
    Squarefree (transitionSieveProduct x) := by
  unfold transitionSieveProduct primorial
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2).2 hpq
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.squarefree

theorem transitionSieveProduct_ne_zero (x : ℕ) :
    transitionSieveProduct x ≠ 0 :=
  (transitionSieveProduct_squarefree x).ne_zero

theorem prime_le_transitionThreshold_of_dvd
    {x p : ℕ} (hp : p.Prime)
    (hpdvd : p ∣ transitionSieveProduct x) :
    (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
  have hpcut : p ≤ transitionSieveCutoff x := by
    exact hp.dvd_primorial_iff.mp hpdvd
  calc
    (p : ℝ) ≤ transitionSieveCutoff x := by exact_mod_cast hpcut
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

theorem largeBase_coprime_transitionSieveProduct
    {x n : ℕ}
    (hlarge :
      ¬(n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100)) :
    n.Coprime (transitionSieveProduct x) := by
  rw [Nat.coprime_comm]
  apply Nat.coprime_of_dvd
  intro p hp hpdvd hpn
  have hmin : n.minFac ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le hpn
  have hpbound :=
    prime_le_transitionThreshold_of_dvd hp hpdvd
  apply hlarge
  have hminR : (n.minFac : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hmin
  exact hminR.trans hpbound

theorem chenRough_coprime_transitionSieveProduct
    {x a : ℕ} (hx : 1 ≤ x) (hrough : chenRough x a) :
    a.Coprime (transitionSieveProduct x) := by
  rw [Nat.coprime_comm]
  apply Nat.coprime_of_dvd
  intro p hp hpdvd hpa
  apply hrough p hp
  · have hpone :
        (x : ℝ) ^ ((1 : ℝ) / 100) ≤
          (x : ℝ) ^ ((1 : ℝ) / 4) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hx) (by norm_num)
    exact (prime_le_transitionThreshold_of_dvd hp hpdvd).trans hpone
  · exact hpa

/-- The unsifted transition interval; unlike `smoothingBoundaryIndices`,
this drops the roughness condition so that congruence classes can be counted
directly. -/
noncomputable def smoothingTransitionInterval
    (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (smoothedMIndices x q).filter fun n =>
    (x : ℝ) / ((q.1 : ℝ) * q.2 * n) <
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))

/-- The dimension-two polynomial used in the transition sieve. -/
def smoothingTransitionArgument
    (x : ℕ) (q : ℕ × ℕ) (n : ℕ) : ℕ :=
  n * (x - q.1 * q.2 * n)

/-- The part of the transition interval surviving the small-prime
dimension-two sieve. -/
noncomputable def smoothingTransitionSiftedIndices
    (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (smoothingTransitionInterval x q).filter fun n =>
    (smoothingTransitionArgument x q n).Coprime
      (transitionSieveProduct x)

theorem smoothingBoundaryIndices_subset_transitionInterval
    (x : ℕ) (q : ℕ × ℕ) :
    smoothingBoundaryIndices x q ⊆
      smoothingTransitionInterval x q := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  have hnSieve := Finset.mem_filter.mp hn'.1
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨hnSieve.1, hnSieve.2.1⟩
  · exact hn'.2

theorem smoothingBoundaryLargeBase_subset_sifted
    {x : ℕ} (hx : 1 ≤ x) (q : ℕ × ℕ) :
    (smoothingBoundaryIndices x q).filter
        (fun n =>
          ¬(n.minFac : ℝ) ≤
            (x : ℝ) ^ ((1 : ℝ) / 100)) ⊆
      smoothingTransitionSiftedIndices x q := by
  intro n hn
  have hnlarge := Finset.mem_filter.mp hn
  have hnBoundary := hnlarge.1
  have hnSieve :=
    Finset.mem_filter.mp
      (Finset.mem_filter.mp hnBoundary).1
  have hrough : chenRough x (x - q.1 * q.2 * n) :=
    hnSieve.2.2
  apply Finset.mem_filter.mpr
  constructor
  · exact smoothingBoundaryIndices_subset_transitionInterval
      x q hnBoundary
  · unfold smoothingTransitionArgument
    exact (largeBase_coprime_transitionSieveProduct
      hnlarge.2).mul_left
        (chenRough_coprime_transitionSieveProduct hx hrough)

theorem vonMangoldt_le_log_of_mem_smoothedMIndices
    {x n : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hn : n ∈ smoothedMIndices x q) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
  have hnrange : n < x + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hlog0 : 0 ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  by_cases hn0 : n = 0
  · simp [hn0, hlog0]
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr
          (by exact_mod_cast Nat.pos_of_ne_zero hn0))
        (Set.mem_Ioi.mpr
          (by exact_mod_cast (by omega : 0 < x)))
        (by exact_mod_cast (by omega : n ≤ x)))

theorem smoothingBoundaryLargeBase_inner_le_siftedCard
    {x : ℕ} (hx : 2 ≤ x) (q : ℕ × ℕ) :
    ∑ n ∈ (smoothingBoundaryIndices x q).filter
        (fun n =>
          ¬(n.minFac : ℝ) ≤
            (x : ℝ) ^ ((1 : ℝ) / 100)),
        ArithmeticFunction.vonMangoldt n ≤
      Real.log x *
        (smoothingTransitionSiftedIndices x q).card := by
  let S :=
    (smoothingBoundaryIndices x q).filter
      (fun n =>
        ¬(n.minFac : ℝ) ≤
          (x : ℝ) ^ ((1 : ℝ) / 100))
  let T := smoothingTransitionSiftedIndices x q
  have hST : S ⊆ T :=
    smoothingBoundaryLargeBase_subset_sifted
      (show 1 ≤ x by omega) q
  calc
    ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
        ∑ n ∈ S, Real.log x := by
      apply Finset.sum_le_sum
      intro n hn
      apply vonMangoldt_le_log_of_mem_smoothedMIndices hx
      have hnBoundary :=
        (Finset.mem_filter.mp hn).1
      exact
        (Finset.mem_filter.mp
          (smoothingBoundaryIndices_subset_transitionInterval
            x q hnBoundary)).1
    _ ≤ ∑ _n ∈ T, Real.log x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro n hnT hnS
      exact Real.log_nonneg
        (by exact_mod_cast (show 1 ≤ x by omega))
    _ = Real.log x * T.card := by
      simp [mul_comm]

/-! ### A finite truncated Selberg sieve for an indexed polynomial -/

/-- Divisors of `P` retained at Selberg level `R`. -/
def truncatedSieveDivisors (P R : ℕ) : Finset ℕ :=
  P.divisors.filter fun d => d ≤ R

/-- A general truncated divisor sum.  It is stated independently of the
transition polynomial so its square expansion can be reused. -/
noncomputable def truncatedSieveDivisorSum
    (P R : ℕ) (w : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ d ∈ truncatedSieveDivisors P R,
    if d ∣ a then w d else 0

theorem one_mem_truncatedSieveDivisors
    {P R : ℕ} (hP : P ≠ 0) (hR : 1 ≤ R) :
    1 ∈ truncatedSieveDivisors P R := by
  simp [truncatedSieveDivisors, hP, hR]

/-- On an integer coprime to the prime product, a truncated divisor sum
whose first coefficient is one equals one. -/
theorem truncatedSieveDivisorSum_eq_one_of_coprime
    {P R a : ℕ} {w : ℕ → ℝ}
    (hP : P ≠ 0) (hR : 1 ≤ R) (hw : w 1 = 1)
    (ha : a.Coprime P) :
    truncatedSieveDivisorSum P R w a = 1 := by
  unfold truncatedSieveDivisorSum
  let D := truncatedSieveDivisors P R
  have h1D : 1 ∈ D :=
    one_mem_truncatedSieveDivisors hP hR
  calc
    ∑ d ∈ truncatedSieveDivisors P R,
        (if d ∣ a then w d else 0) =
      ∑ d ∈ D, (if d ∣ a then w d else 0) := by rfl
    _ = if 1 ∣ a then w 1 else 0 := by
      apply Finset.sum_eq_single 1
      · intro d hdD hd1
        have hdP : d ∣ P :=
          Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hdD).1
        by_cases hda : d ∣ a
        · have hdgcd : d ∣ Nat.gcd a P :=
            Nat.dvd_gcd hda hdP
          have hdOne : d ∣ 1 := by
            simpa [ha] using hdgcd
          exact (hd1 (Nat.dvd_one.mp hdOne)).elim
        · simp [hda]
      · intro hnot
        exact (hnot h1D).elim
    _ = 1 := by simp [hw]

/-- Indexed sifted set for an arbitrary finite family and arithmetic
argument. -/
def indexedSiftedSet
    (S : Finset ℕ) (F : ℕ → ℕ) (P : ℕ) : Finset ℕ :=
  S.filter fun n => (F n).Coprime P

/-- The elementary pointwise Λ² upper-bound sieve inequality. -/
theorem indexedSifted_card_le_squareSum
    {S : Finset ℕ} {F : ℕ → ℕ} {P R : ℕ}
    {w : ℕ → ℝ}
    (hP : P ≠ 0) (hR : 1 ≤ R) (hw : w 1 = 1) :
    ((indexedSiftedSet S F P).card : ℝ) ≤
      ∑ n ∈ S, (truncatedSieveDivisorSum P R w (F n)) ^ 2 := by
  let T := indexedSiftedSet S F P
  have hTS : T ⊆ S := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  calc
    (T.card : ℝ) = ∑ _n ∈ T, (1 : ℝ) := by simp
    _ = ∑ n ∈ T,
          (truncatedSieveDivisorSum P R w (F n)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hcop := (Finset.mem_filter.mp hn).2
      rw [truncatedSieveDivisorSum_eq_one_of_coprime
        hP hR hw hcop]
      norm_num
    _ ≤ ∑ n ∈ S,
          (truncatedSieveDivisorSum P R w (F n)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hTS
      intro n hnS hnT
      exact sq_nonneg _

/-- Exact lcm expansion of the indexed square sieve. -/
theorem indexedSquareSum_eq_lcmCount
    (S : Finset ℕ) (F : ℕ → ℕ)
    (P R : ℕ) (w : ℕ → ℝ) :
    ∑ n ∈ S, (truncatedSieveDivisorSum P R w (F n)) ^ 2 =
      ∑ d₁ ∈ truncatedSieveDivisors P R,
        ∑ d₂ ∈ truncatedSieveDivisors P R,
          w d₁ * w d₂ *
            ((S.filter fun n => d₁.lcm d₂ ∣ F n).card : ℝ) := by
  unfold truncatedSieveDivisorSum
  rw [Finset.sum_comm]
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d₂ hd₂
  calc
    ∑ n ∈ S,
        (if d₁ ∣ F n then w d₁ else 0) *
          (if d₂ ∣ F n then w d₂ else 0) =
      ∑ n ∈ S,
        w d₁ * w d₂ *
          (if d₁.lcm d₂ ∣ F n then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h₁ : d₁ ∣ F n
      · by_cases h₂ : d₂ ∣ F n
        · simp [h₁, h₂, Nat.lcm_dvd h₁ h₂]
        · have hnot : ¬d₁.lcm d₂ ∣ F n := by
            intro h
            exact h₂ (Nat.dvd_trans
              (Nat.dvd_lcm_right d₁ d₂) h)
          simp [h₁, h₂, hnot]
      · have hnot : ¬d₁.lcm d₂ ∣ F n := by
          intro h
          exact h₁ (Nat.dvd_trans
            (Nat.dvd_lcm_left d₁ d₂) h)
        simp [h₁, hnot]
    _ = w d₁ * w d₂ *
        ∑ n ∈ S,
          (if d₁.lcm d₂ ∣ F n then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
    _ = w d₁ * w d₂ *
        ((S.filter fun n => d₁.lcm d₂ ∣ F n).card : ℝ) := by
      congr 1
      rw [← Finset.sum_filter]
      simp
    _ = w d₂ * w d₁ *
        ((S.filter fun n => d₂.lcm d₁ ∣ F n).card : ℝ) := by
      rw [Nat.lcm_comm]
      ring

theorem smoothingTransitionSiftedIndices_eq_indexed
    (x : ℕ) (q : ℕ × ℕ) :
    smoothingTransitionSiftedIndices x q =
      indexedSiftedSet (smoothingTransitionInterval x q)
        (smoothingTransitionArgument x q)
        (transitionSieveProduct x) := by
  rfl

/-- The transition count is reduced exactly to lcm-divisibility counts.
The remaining choice of `w` is the analytic Selberg optimization. -/
theorem smoothingTransitionSifted_card_le_lcmCount
    (x : ℕ) (q : ℕ × ℕ) (R : ℕ) (w : ℕ → ℝ)
    (hR : 1 ≤ R) (hw : w 1 = 1) :
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
      ∑ d₁ ∈ truncatedSieveDivisors
          (transitionSieveProduct x) R,
        ∑ d₂ ∈ truncatedSieveDivisors
            (transitionSieveProduct x) R,
          w d₁ * w d₂ *
            (((smoothingTransitionInterval x q).filter fun n =>
              d₁.lcm d₂ ∣
                smoothingTransitionArgument x q n).card : ℝ) := by
  rw [smoothingTransitionSiftedIndices_eq_indexed]
  calc
    ((indexedSiftedSet (smoothingTransitionInterval x q)
        (smoothingTransitionArgument x q)
        (transitionSieveProduct x)).card : ℝ) ≤
      ∑ n ∈ smoothingTransitionInterval x q,
        (truncatedSieveDivisorSum
          (transitionSieveProduct x) R w
            (smoothingTransitionArgument x q n)) ^ 2 :=
      indexedSifted_card_le_squareSum
        (transitionSieveProduct_ne_zero x) hR hw
    _ = _ := indexedSquareSum_eq_lcmCount
      (smoothingTransitionInterval x q)
      (smoothingTransitionArgument x q)
      (transitionSieveProduct x) R w

/-! ### Local roots of the transition polynomial -/

/-- Residue classes modulo `d` on which
`r (x - p₁p₂ r)` vanishes.  The expression is evaluated in `ZMod d`, so
there is no truncated-natural-subtraction issue. -/
def smoothingTransitionRootResidues
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun r =>
    (r : ZMod d) *
      ((x : ZMod d) -
        (q.1 * q.2 : ℕ) * (r : ZMod d)) = 0

def smoothingTransitionRootCount
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℕ :=
  (smoothingTransitionRootResidues x q d).card

/-- The same local roots represented intrinsically in `ZMod d`. -/
noncomputable def smoothingTransitionZModRoots
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) [NeZero d] :
    Finset (ZMod d) :=
  Finset.univ.filter fun r =>
    r * ((x : ZMod d) -
      (q.1 * q.2 : ℕ) * r) = 0

theorem smoothingTransitionRootResidues_image_eq_zmodRoots
    {x d : ℕ} {q : ℕ × ℕ} (hd : 0 < d) :
    letI : NeZero d := ⟨hd.ne'⟩
    (smoothingTransitionRootResidues x q d).image
        (fun r : ℕ => (r : ZMod d)) =
      smoothingTransitionZModRoots x q d := by
  letI : NeZero d := ⟨hd.ne'⟩
  ext z
  simp only [Finset.mem_image, smoothingTransitionRootResidues,
    smoothingTransitionZModRoots, Finset.mem_filter,
    Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, ⟨hrlt, hrroot⟩, rfl⟩
    exact hrroot
  · intro hz
    refine ⟨z.val, ⟨z.val_lt, ?_⟩, ?_⟩
    · simpa only [ZMod.natCast_zmod_val] using hz
    · exact ZMod.natCast_zmod_val z

theorem smoothingTransitionRootCount_eq_zmodRoots_card
    {x d : ℕ} {q : ℕ × ℕ} (hd : 0 < d) :
    letI : NeZero d := ⟨hd.ne'⟩
    smoothingTransitionRootCount x q d =
      (smoothingTransitionZModRoots x q d).card := by
  letI : NeZero d := ⟨hd.ne'⟩
  have himage :=
    smoothingTransitionRootResidues_image_eq_zmodRoots
      (x := x) (q := q) hd
  have hinj : Set.InjOn
      (fun r : ℕ => (r : ZMod d))
      (smoothingTransitionRootResidues x q d : Set ℕ) := by
    intro r hr s hs hrs
    have hrlt : r < d :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hslt : s < d :=
      Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have hval := congrArg ZMod.val hrs
    simpa [ZMod.val_natCast_of_lt hrlt,
      ZMod.val_natCast_of_lt hslt] using hval
  unfold smoothingTransitionRootCount
  calc
    (smoothingTransitionRootResidues x q d).card =
        ((smoothingTransitionRootResidues x q d).image
          (fun r : ℕ => (r : ZMod d))).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (smoothingTransitionZModRoots x q d).card := by
      rw [himage]

/-- Over a prime modulus not dividing `p₁p₂`, the roots are exactly zero
and `(p₁p₂)⁻¹x`. -/
theorem smoothingTransitionRootResidues_image_prime
    {x p : ℕ} {q : ℕ × ℕ} (hp : p.Prime)
    (hpb : ¬p ∣ q.1 * q.2) :
    (smoothingTransitionRootResidues x q p).image
        (fun r : ℕ => (r : ZMod p)) =
      {0, ((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
        (x : ZMod p)} := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpb₁ : ¬p ∣ q.1 := fun h =>
    hpb (dvd_mul_of_dvd_left h q.2)
  have hpb₂ : ¬p ∣ q.2 := fun h =>
    hpb (dvd_mul_of_dvd_right h q.1)
  have hbZ :
      (q.1 : ZMod p) * (q.2 : ZMod p) ≠ 0 := by
    exact mul_ne_zero
      (by simpa [ZMod.natCast_eq_zero_iff] using hpb₁)
      (by simpa [ZMod.natCast_eq_zero_iff] using hpb₂)
  ext z
  simp only [Finset.mem_image, smoothingTransitionRootResidues,
    Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, ⟨hrlt, hrroot⟩, rfl⟩
    rw [mul_eq_zero] at hrroot
    rcases hrroot with hr | hr
    · exact Or.inl hr
    · right
      rw [eq_inv_mul_iff_mul_eq₀ hbZ]
      simpa [Nat.cast_mul, mul_assoc] using
        (sub_eq_zero.mp hr).symm
  · intro hz
    let c : ZMod p :=
      ((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
        (x : ZMod p)
    rcases hz with hz | hz
    · refine ⟨0, ⟨hp.pos, by simp⟩, ?_⟩
      simpa using hz.symm
    · refine ⟨c.val, ?_, ?_⟩
      · constructor
        · exact c.val_lt
        · rw [ZMod.natCast_zmod_val, mul_eq_zero]
          right
          apply sub_eq_zero.mpr
          dsimp only [c]
          rw [Nat.cast_mul, ← mul_assoc,
            mul_inv_cancel₀ hbZ, one_mul]
      · rw [ZMod.natCast_zmod_val]
        exact hz.symm

/-- The local dimension is one at primes dividing `x` and two otherwise. -/
theorem smoothingTransitionRootCount_prime
    {x p : ℕ} {q : ℕ × ℕ} (hp : p.Prime)
    (hpb : ¬p ∣ q.1 * q.2) :
    smoothingTransitionRootCount x q p =
      if p ∣ x then 1 else 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpb₁ : ¬p ∣ q.1 := fun h =>
    hpb (dvd_mul_of_dvd_left h q.2)
  have hpb₂ : ¬p ∣ q.2 := fun h =>
    hpb (dvd_mul_of_dvd_right h q.1)
  have hbZ :
      (q.1 : ZMod p) * (q.2 : ZMod p) ≠ 0 := by
    exact mul_ne_zero
      (by simpa [ZMod.natCast_eq_zero_iff] using hpb₁)
      (by simpa [ZMod.natCast_eq_zero_iff] using hpb₂)
  have himage :=
    smoothingTransitionRootResidues_image_prime
      (x := x) (q := q) hp hpb
  have hinj : Set.InjOn
      (fun r : ℕ => (r : ZMod p))
      (smoothingTransitionRootResidues x q p : Set ℕ) := by
    intro r hr s hs hrs
    have hrlt : r < p :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hslt : s < p :=
      Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have hval := congrArg ZMod.val hrs
    simpa [ZMod.val_natCast_of_lt hrlt,
      ZMod.val_natCast_of_lt hslt] using hval
  calc
    smoothingTransitionRootCount x q p =
        ((smoothingTransitionRootResidues x q p).image
          (fun r : ℕ => (r : ZMod p))).card := by
      unfold smoothingTransitionRootCount
      exact (Finset.card_image_of_injOn hinj).symm
    _ = ({0, ((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
          (x : ZMod p)} : Finset (ZMod p)).card := by
      rw [himage]
    _ = if p ∣ x then 1 else 2 := by
      by_cases hx : p ∣ x
      · have hxZ : (x : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff x p).mpr hx
        simp [hx, hxZ]
      · have hxZ : (x : ZMod p) ≠ 0 :=
          (ZMod.natCast_eq_zero_iff x p).not.mpr hx
        have hc :
            ((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
                (x : ZMod p) ≠ 0 :=
          mul_ne_zero (inv_ne_zero hbZ) hxZ
        rw [if_neg hx]
        have hzero :
            (0 : ZMod p) ∉
              ({((q.1 : ZMod p) * (q.2 : ZMod p))⁻¹ *
                (x : ZMod p)} : Finset (ZMod p)) := by
          simpa only [Finset.mem_singleton] using hc.symm
        rw [Finset.card_insert_of_notMem hzero]
        simp

/-- Every sieving prime is smaller than both primes in an admissible Chen
pair, hence it does not divide their product. -/
theorem transitionSievePrime_not_dvd_pair
    {x p : ℕ} {q : ℕ × ℕ} (hx : 1 < x)
    (hq : q ∈ chenPairs x) (hp : p.Prime)
    (hpdvd : p ∣ transitionSieveProduct x) :
    ¬p ∣ q.1 * q.2 := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with
    ⟨hp₁, hp₂, hp₁lo, hp₁hi, hp₂lo, hp₂hi⟩
  have hxR : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hpow :
      (x : ℝ) ^ ((1 : ℝ) / 100) <
        (x : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.rpow_lt_rpow_of_exponent_lt hxR (by norm_num)
  have hpq₁R : (p : ℝ) < (q.1 : ℝ) :=
    (prime_le_transitionThreshold_of_dvd hp hpdvd).trans_lt
      (hpow.trans hp₁lo)
  have hpq₁ : p < q.1 := by exact_mod_cast hpq₁R
  have hq₁q₂R : (q.1 : ℝ) < (q.2 : ℝ) :=
    hp₁hi.trans_lt hp₂lo
  have hpq₂ : p < q.2 := by
    exact_mod_cast hpq₁R.trans hq₁q₂R
  intro hpdiv
  rcases hp.dvd_mul.mp hpdiv with hpdiv | hpdiv
  · have heq : p = q.1 :=
      (Nat.prime_dvd_prime_iff_eq hp hp₁).mp hpdiv
    omega
  · have heq : p = q.2 :=
      (Nat.prime_dvd_prime_iff_eq hp hp₂).mp hpdiv
    omega

theorem pairProduct_mul_le_of_mem_transitionInterval
    {x n : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x)
    (hn : n ∈ smoothingTransitionInterval x q) :
    q.1 * q.2 * n ≤ x := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  have hp₁pos : (0 : ℝ) < q.1 := by
    exact_mod_cast hq'.2.1.pos
  have hp₂pos : (0 : ℝ) < q.2 := by
    exact_mod_cast hq'.2.2.1.pos
  have hnSmoothed := (Finset.mem_filter.mp hn).1
  have hnle :
      (n : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    (Finset.mem_filter.mp hnSmoothed).2
  have hprod :
      ((q.1 : ℝ) * q.2) * n ≤ (x : ℝ) :=
    by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (le_div_iff₀ (mul_pos hp₁pos hp₂pos)).mp hnle
  exact_mod_cast hprod

/-- Divisibility of an actual transition value forces its residue to be
one of the polynomial roots modulo the divisor. -/
theorem mod_mem_smoothingTransitionRootResidues
    {x n d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d)
    (hn : n ∈ smoothingTransitionInterval x q)
    (hdiv : d ∣ smoothingTransitionArgument x q n) :
    n % d ∈ smoothingTransitionRootResidues x q d := by
  have hprod :
      q.1 * q.2 * n ≤ x :=
    pairProduct_mul_le_of_mem_transitionInterval hq hn
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_range.mpr (Nat.mod_lt n hd)
  · rw [ZMod.natCast_mod]
    have hzero :
        (smoothingTransitionArgument x q n : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff
        (smoothingTransitionArgument x q n) d).mpr hdiv
    unfold smoothingTransitionArgument at hzero
    rw [Nat.cast_mul, Nat.cast_sub hprod,
      Nat.cast_mul, Nat.cast_mul] at hzero
    simpa only [Nat.cast_mul, mul_assoc] using hzero

theorem dvd_transitionArgument_iff_mod_mem_roots
    {x n d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d)
    (hn : n ∈ smoothingTransitionInterval x q) :
    d ∣ smoothingTransitionArgument x q n ↔
      n % d ∈ smoothingTransitionRootResidues x q d := by
  constructor
  · exact mod_mem_smoothingTransitionRootResidues hq hd hn
  · intro hroot
    have hprod :
        q.1 * q.2 * n ≤ x :=
      pairProduct_mul_le_of_mem_transitionInterval hq hn
    have hrootData := (Finset.mem_filter.mp hroot).2
    rw [ZMod.natCast_mod] at hrootData
    have hzero :
        (smoothingTransitionArgument x q n : ZMod d) = 0 := by
      unfold smoothingTransitionArgument
      rw [Nat.cast_mul, Nat.cast_sub hprod,
        Nat.cast_mul, Nat.cast_mul]
      simpa only [Nat.cast_mul, mul_assoc] using hrootData
    exact (ZMod.natCast_eq_zero_iff
      (smoothingTransitionArgument x q n) d).mp hzero

/-! ### Counting divisibility classes in a short integer interval -/

/-- If every solution modulo `d` lands in a prescribed finite root set,
then the number of solutions in `(L,U]` is at most the number of roots
times the number of possible quotients. -/
theorem card_filter_dvd_le_rootCard_mul_intervalQuotients
    {S roots : Finset ℕ} {F : ℕ → ℕ}
    {d L U : ℕ} (hd : 0 < d) (hLU : L ≤ U)
    (hbounds : ∀ n ∈ S, L < n ∧ n ≤ U)
    (hroot : ∀ n ∈ S, d ∣ F n → n % d ∈ roots) :
    ((S.filter fun n => d ∣ F n).card : ℕ) ≤
      roots.card * ((U - L) / d + 2) := by
  let A := S.filter fun n => d ∣ F n
  let enc : ℕ → ℕ × ℕ := fun n => (n % d, n / d)
  let box : Finset (ℕ × ℕ) :=
    roots ×ˢ Finset.Icc (L / d) (U / d)
  have hencinj : Function.Injective enc := by
    intro n m h
    have hmod : n % d = m % d := congrArg Prod.fst h
    have hdiv : n / d = m / d := congrArg Prod.snd h
    calc
      n = n % d + d * (n / d) := (Nat.mod_add_div n d).symm
      _ = m % d + d * (m / d) := by rw [hmod, hdiv]
      _ = m := Nat.mod_add_div m d
  have himage : A.image enc ⊆ box := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hnA, rfl⟩
    have hnS := (Finset.mem_filter.mp hnA).1
    have hndiv := (Finset.mem_filter.mp hnA).2
    have hnBounds := hbounds n hnS
    apply Finset.mem_product.mpr
    constructor
    · exact hroot n hnS hndiv
    · apply Finset.mem_Icc.mpr
      exact ⟨Nat.div_le_div_right hnBounds.1.le,
        Nat.div_le_div_right hnBounds.2⟩
  have hquot :
      U / d + 1 - L / d ≤ (U - L) / d + 2 := by
    have hU : U = L + (U - L) := by omega
    have hadd :
        (L + (U - L)) / d ≤
          L / d + (U - L) / d + 1 := by
      rw [Nat.add_div hd]
      split <;> omega
    have hadd' :
        U / d ≤ L / d + (U - L) / d + 1 := by
      calc
        U / d = (L + (U - L)) / d :=
          congrArg (fun t : ℕ => t / d) hU
        _ ≤ L / d + (U - L) / d + 1 := hadd
    apply tsub_le_iff_left.mpr
    omega
  calc
    A.card = (A.image enc).card :=
      (Finset.card_image_of_injective A hencinj).symm
    _ ≤ box.card := Finset.card_le_card himage
    _ = roots.card * (U / d + 1 - L / d) := by
      simp only [box, Finset.card_product, Nat.card_Icc]
    _ ≤ roots.card * ((U - L) / d + 2) :=
      Nat.mul_le_mul_left roots.card hquot

/-- A single residue class occurs in `(L,U]` within one unit (we retain a
two-unit symmetric bound) of the quotient `(U-L)/d`. -/
theorem Ioc_modFiber_card_div_bounds
    {L U d r : ℕ} (hd : 0 < d) (hLU : L ≤ U)
    (hr : r < d) :
    let N :=
      ((Finset.Ioc L U).filter fun n => n % d = r).card
    let Q := (U - L) / d
    Q ≤ N + 1 ∧ N ≤ Q + 2 := by
  let FU :=
    (Finset.range (U + 1)).filter fun n => n % d = r
  let FL :=
    (Finset.range (L + 1)).filter fun n => n % d = r
  have hFLFU : FL ⊆ FU := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hn'.1).trans_le (by omega)), hn'.2⟩
  have hinterval :
      (Finset.Ioc L U).filter (fun n => n % d = r) =
        FU \ FL := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, FU, FL, Finset.mem_range]
    omega
  have hFU :
      FU.card = (U + 1) / d +
        if r % d < (U + 1) % d then 1 else 0 := by
    simpa only [FU] using
      (show ((Finset.range (U + 1)).filter fun n =>
          n % d = r).card =
          (U + 1) / d +
            if r % d < (U + 1) % d then 1 else 0 by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hr,
          Nat.count_eq_card_filter_range] using
            Nat.count_modEq_card (U + 1) hd r)
  have hFL :
      FL.card = (L + 1) / d +
        if r % d < (L + 1) % d then 1 else 0 := by
    simpa only [FL] using
      (show ((Finset.range (L + 1)).filter fun n =>
          n % d = r).card =
          (L + 1) / d +
            if r % d < (L + 1) % d then 1 else 0 by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hr,
          Nat.count_eq_card_filter_range] using
            Nat.count_modEq_card (L + 1) hd r)
  have hcard :
      ((Finset.Ioc L U).filter fun n => n % d = r).card =
        FU.card - FL.card := by
    rw [hinterval, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hFLFU]
  have hcardle : FL.card ≤ FU.card :=
    Finset.card_le_card hFLFU
  have hNadd :
      ((Finset.Ioc L U).filter fun n => n % d = r).card +
          FL.card = FU.card := by
    rw [hcard, Nat.sub_add_cancel hcardle]
  have hsum : U + 1 = (L + 1) + (U - L) := by omega
  have hqlo :
      (L + 1) / d + (U - L) / d ≤ (U + 1) / d := by
    rw [hsum]
    exact Nat.div_add_div_le_add_div
  have hqhi :
      (U + 1) / d ≤
        (L + 1) / d + (U - L) / d + 1 := by
    rw [hsum, Nat.add_div hd]
    split <;> omega
  dsimp only
  rw [hFU, hFL] at hNadd
  split_ifs at hNadd <;> omega

/-! ### The actual smoothing transition as a short integer interval -/

noncomputable def smoothingTransitionLower
    (x : ℕ) (q : ℕ × ℕ) : ℕ :=
  ⌊((x : ℝ) / ((q.1 : ℝ) * q.2)) /
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))⌋₊

noncomputable def smoothingTransitionUpper
    (x : ℕ) (q : ℕ × ℕ) : ℕ :=
  ⌊(x : ℝ) / ((q.1 : ℝ) * q.2)⌋₊

noncomputable def positiveSmoothingTransitionInterval
    (x : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (smoothingTransitionInterval x q).erase 0

theorem mem_positiveSmoothingTransitionInterval_bounds
    {x n : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x)
    (hn : n ∈ positiveSmoothingTransitionInterval x q) :
    smoothingTransitionLower x q < n ∧
      n ≤ smoothingTransitionUpper x q := by
  have hnErase := Finset.mem_erase.mp hn
  have hn0 : n ≠ 0 := hnErase.1
  have hnTransition := hnErase.2
  have hnData := Finset.mem_filter.mp hnTransition
  have hnSmoothed := hnData.1
  have hnle :
      (n : ℝ) ≤
        (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    (Finset.mem_filter.mp hnSmoothed).2
  have hnposR : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  have hp₁pos : (0 : ℝ) < q.1 := by
    exact_mod_cast hq'.2.1.pos
  have hp₂pos : (0 : ℝ) < q.2 := by
    exact_mod_cast hq'.2.2.1.pos
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  let E : ℝ :=
    Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))
  have hEpos : 0 < E := by
    dsimp only [E]
    positivity
  have hboundary : Y / n < E := by
    dsimp only [Y, E]
    simpa only [div_div, mul_assoc] using hnData.2
  have hYlt : Y < E * n :=
    (div_lt_iff₀ hnposR).mp hboundary
  have hlowerR : Y / E < n :=
    (div_lt_iff₀ hEpos).mpr (by
      simpa only [mul_comm] using hYlt)
  constructor
  · have hfloor :
        (smoothingTransitionLower x q : ℝ) ≤ Y / E := by
      unfold smoothingTransitionLower
      dsimp only [Y, E]
      exact Nat.floor_le (by positivity)
    have hltR :
        (smoothingTransitionLower x q : ℝ) < n :=
      hfloor.trans_lt hlowerR
    exact_mod_cast hltR
  · unfold smoothingTransitionUpper
    exact Nat.le_floor hnle

theorem positiveSmoothingTransitionInterval_eq_Ioc
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    positiveSmoothingTransitionInterval x q =
      Finset.Ioc (smoothingTransitionLower x q)
        (smoothingTransitionUpper x q) := by
  ext n
  constructor
  · intro hn
    exact Finset.mem_Ioc.mpr
      (mem_positiveSmoothingTransitionInterval_bounds hq hn)
  · intro hn
    have hnBounds := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by omega
    have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hq' := hq
    simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hq'
    have hp₁pos : (0 : ℝ) < q.1 := by
      exact_mod_cast hq'.2.1.pos
    have hp₂pos : (0 : ℝ) < q.2 := by
      exact_mod_cast hq'.2.2.1.pos
    have hp₁one : (1 : ℝ) ≤ q.1 := by
      exact_mod_cast hq'.2.1.one_le
    have hp₂one : (1 : ℝ) ≤ q.2 := by
      exact_mod_cast hq'.2.2.1.one_le
    let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
    let E : ℝ :=
      Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ)))
    have hEpos : 0 < E := by
      dsimp only [E]
      positivity
    have hupperFloor :
        (smoothingTransitionUpper x q : ℝ) ≤ Y := by
      unfold smoothingTransitionUpper
      dsimp only [Y]
      exact Nat.floor_le (by positivity)
    have hnleY : (n : ℝ) ≤ Y := by
      have hnUpperR :
          (n : ℝ) ≤ smoothingTransitionUpper x q := by
        exact_mod_cast hnBounds.2
      exact hnUpperR.trans hupperFloor
    have hYleX : Y ≤ (x : ℝ) := by
      dsimp only [Y]
      have hdenom :
          (1 : ℝ) ≤ (q.1 : ℝ) * q.2 := by
        calc
          (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ (q.1 : ℝ) * q.2 :=
            mul_le_mul hp₁one hp₂one (by norm_num) (by norm_num)
      exact div_le_self (by positivity)
        hdenom
    have hnleX : n ≤ x := by
      exact_mod_cast hnleY.trans hYleX
    have hlowerCast :
        Y / E <
          (smoothingTransitionLower x q : ℝ) + 1 := by
      unfold smoothingTransitionLower
      dsimp only [Y, E]
      exact Nat.lt_floor_add_one _
    have hsucc :
        smoothingTransitionLower x q + 1 ≤ n := by omega
    have hlower : Y / E < (n : ℝ) := by
      exact hlowerCast.trans_le (by exact_mod_cast hsucc)
    have hYlt : Y < E * n :=
      by
        simpa only [mul_comm] using
          (div_lt_iff₀ hEpos).mp hlower
    have hboundary : Y / n < E :=
      (div_lt_iff₀ hnposR).mpr (by
        simpa only [mul_comm] using hYlt)
    apply Finset.mem_erase.mpr
    refine ⟨by omega, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), hnleY⟩
    · dsimp only [Y, E] at hboundary
      simpa only [div_div, mul_assoc] using hboundary

theorem smoothingTransitionLower_le_upper
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    smoothingTransitionLower x q ≤
      smoothingTransitionUpper x q := by
  by_cases hS :
      positiveSmoothingTransitionInterval x q = ∅
  · unfold smoothingTransitionLower smoothingTransitionUpper
    apply Nat.floor_mono
    have hEone :
        1 ≤ Real.exp
          (2 * (Real.log x) ^ (-(0.1 : ℝ))) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      positivity
    exact div_le_self (by positivity) hEone
  · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hb :=
      mem_positiveSmoothingTransitionInterval_bounds hq hn
    omega

/-- Congruence counting for the positive part of the actual transition
interval, with the exact local root count. -/
theorem positiveTransition_dvd_card_le
    {x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    (((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card : ℕ) ≤
      smoothingTransitionRootCount x q d *
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q) / d + 2) := by
  unfold smoothingTransitionRootCount
  apply card_filter_dvd_le_rootCard_mul_intervalQuotients
    hd (smoothingTransitionLower_le_upper hq)
  · intro n hn
    exact mem_positiveSmoothingTransitionInterval_bounds hq hn
  · intro n hn hdiv
    apply mod_mem_smoothingTransitionRootResidues hq hd
    · exact (Finset.mem_erase.mp hn).2
    · exact hdiv

/-- Exact decomposition of a transition divisibility count into its
admissible residue classes. -/
theorem positiveTransition_dvd_card_eq_sum_rootFibers
    {x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    (((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card : ℕ) =
      ∑ r ∈ smoothingTransitionRootResidues x q d,
        ((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card := by
  let S := positiveSmoothingTransitionInterval x q
  let roots := smoothingTransitionRootResidues x q d
  have hfiber :=
    Finset.sum_card_fiberwise_eq_card_filter
      S roots (fun n => n % d)
  calc
    ((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card =
      ((positiveSmoothingTransitionInterval x q).filter fun n =>
        n % d ∈ smoothingTransitionRootResidues x q d).card := by
      apply congrArg Finset.card
      ext n
      simp only [Finset.mem_filter]
      constructor
      · intro hn
        exact ⟨hn.1,
          (dvd_transitionArgument_iff_mod_mem_roots
            hq hd (Finset.mem_erase.mp hn.1).2).mp hn.2⟩
      · intro hn
        exact ⟨hn.1,
          (dvd_transitionArgument_iff_mod_mem_roots
            hq hd (Finset.mem_erase.mp hn.1).2).mpr hn.2⟩
    _ = ∑ r ∈ smoothingTransitionRootResidues x q d,
        ((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card := by
      simpa only [S, roots] using hfiber.symm

theorem positiveTransition_rootFiber_abs_sub_density_le
    {x d r : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d)
    (hr : r ∈ smoothingTransitionRootResidues x q d) :
    |(((positiveSmoothingTransitionInterval x q).filter fun n =>
          n % d = r).card : ℝ) -
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) / d| ≤ 3 := by
  let L := smoothingTransitionLower x q
  let U := smoothingTransitionUpper x q
  let N :=
    ((Finset.Ioc L U).filter fun n => n % d = r).card
  let Q := (U - L) / d
  have hLU : L ≤ U :=
    smoothingTransitionLower_le_upper hq
  have hrlt : r < d :=
    Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hbounds := Ioc_modFiber_card_div_bounds hd hLU hrlt
  have hNQ :
      |(N : ℝ) - (Q : ℝ)| ≤ 2 := by
    have hlowR : (Q : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast hbounds.1
    have huppR : (N : ℝ) ≤ (Q : ℝ) + 2 := by
      exact_mod_cast hbounds.2
    rw [abs_le]
    constructor <;> linarith
  have hQle :
      (Q : ℝ) ≤ ((U - L : ℕ) : ℝ) / d := by
    dsimp only [Q]
    exact Nat.cast_div_le
  have hdivlt :
      ((U - L : ℕ) : ℝ) / d < (Q : ℝ) + 1 := by
    have hfloor :=
      Nat.lt_floor_add_one
        (((U - L : ℕ) : ℝ) / (d : ℝ))
    rw [Nat.floor_div_eq_div] at hfloor
    simpa only [Q, Nat.cast_add, Nat.cast_one] using hfloor
  have hQdiv :
      |(Q : ℝ) - ((U - L : ℕ) : ℝ) / d| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [positiveSmoothingTransitionInterval_eq_Ioc hq]
  change |(N : ℝ) - ((U - L : ℕ) : ℝ) / d| ≤ 3
  calc
    |(N : ℝ) - ((U - L : ℕ) : ℝ) / d| =
        |((N : ℝ) - Q) +
          ((Q : ℝ) - ((U - L : ℕ) : ℝ) / d)| := by
      congr 1
      ring
    _ ≤ |(N : ℝ) - Q| +
        |(Q : ℝ) - ((U - L : ℕ) : ℝ) / d| :=
      abs_add_le _ _
    _ ≤ 2 + 1 := add_le_add hNQ hQdiv
    _ = 3 := by norm_num

noncomputable def positiveTransitionDivisibilityCount
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  (((positiveSmoothingTransitionInterval x q).filter fun n =>
    d ∣ smoothingTransitionArgument x q n).card : ℝ)

noncomputable def positiveTransitionDivisibilityRemainder
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  positiveTransitionDivisibilityCount x q d -
    (smoothingTransitionRootCount x q d : ℝ) *
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) / d

/-- The short interval has an absolute distribution remainder bounded by
three times the exact number of local roots. -/
theorem abs_positiveTransitionDivisibilityRemainder_le
    {x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    |positiveTransitionDivisibilityRemainder x q d| ≤
      3 * smoothingTransitionRootCount x q d := by
  let roots := smoothingTransitionRootResidues x q d
  let H : ℝ :=
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ)
  have hcount :=
    positiveTransition_dvd_card_eq_sum_rootFibers hq hd
  have hcountR :
      positiveTransitionDivisibilityCount x q d =
        ∑ r ∈ roots,
          (((positiveSmoothingTransitionInterval x q).filter
            fun n => n % d = r).card : ℝ) := by
    unfold positiveTransitionDivisibilityCount
    exact_mod_cast hcount
  have hmain :
      (smoothingTransitionRootCount x q d : ℝ) * H / d =
        ∑ _r ∈ roots, H / d := by
    unfold smoothingTransitionRootCount
    simp only [roots, Finset.sum_const, nsmul_eq_mul]
    ring
  unfold positiveTransitionDivisibilityRemainder
  rw [hcountR, hmain, ← Finset.sum_sub_distrib]
  calc
    |∑ r ∈ roots,
        ((((positiveSmoothingTransitionInterval x q).filter
            fun n => n % d = r).card : ℝ) - H / d)| ≤
      ∑ r ∈ roots,
        |(((positiveSmoothingTransitionInterval x q).filter
            fun n => n % d = r).card : ℝ) - H / d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ roots, 3 := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [H] using
        positiveTransition_rootFiber_abs_sub_density_le
          hq hd hr
    _ = 3 * smoothingTransitionRootCount x q d := by
      unfold smoothingTransitionRootCount
      simp only [roots, Finset.sum_const, nsmul_eq_mul]
      ring

theorem zero_mem_smoothingTransitionInterval
    (x : ℕ) (q : ℕ × ℕ) :
    0 ∈ smoothingTransitionInterval x q := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · simpa only [Nat.cast_zero] using
        div_nonneg
          (show (0 : ℝ) ≤ (x : ℝ) by positivity)
          (show (0 : ℝ) ≤ (q.1 : ℝ) * q.2 by positivity)
  · simpa using
      (Real.exp_pos
        (2 * (Real.log x) ^ (-(0.1 : ℝ))))

theorem transitionDivisibilityCount_eq_positive_add_one
    {x d : ℕ} {q : ℕ × ℕ} :
    (((smoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card : ℕ) =
      ((positiveSmoothingTransitionInterval x q).filter fun n =>
        d ∣ smoothingTransitionArgument x q n).card + 1 := by
  let A :=
    (smoothingTransitionInterval x q).filter fun n =>
      d ∣ smoothingTransitionArgument x q n
  let B :=
    (positiveSmoothingTransitionInterval x q).filter fun n =>
      d ∣ smoothingTransitionArgument x q n
  have h0A : 0 ∈ A := by
    apply Finset.mem_filter.mpr
    exact ⟨zero_mem_smoothingTransitionInterval x q,
      by simp [smoothingTransitionArgument]⟩
  have herase : A.erase 0 = B := by
    ext n
    simp only [A, B, positiveSmoothingTransitionInterval,
      Finset.mem_erase, Finset.mem_filter]
    tauto
  calc
    A.card = (A.erase 0).card + 1 :=
      (Finset.card_erase_add_one h0A).symm
    _ = B.card + 1 := by rw [herase]

noncomputable def transitionDivisibilityCount
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  (((smoothingTransitionInterval x q).filter fun n =>
    d ∣ smoothingTransitionArgument x q n).card : ℝ)

noncomputable def transitionDivisibilityRemainder
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) : ℝ :=
  transitionDivisibilityCount x q d -
    (smoothingTransitionRootCount x q d : ℝ) *
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) / d

/-- Adding back the exceptional index `n = 0` costs exactly one in every
modulus, so the full transition remainder is still uniformly bounded. -/
theorem abs_transitionDivisibilityRemainder_le
    {x d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) (hd : 0 < d) :
    |transitionDivisibilityRemainder x q d| ≤
      3 * smoothingTransitionRootCount x q d + 1 := by
  have hcountNat :=
    transitionDivisibilityCount_eq_positive_add_one
      (x := x) (q := q) (d := d)
  have hcount :
      transitionDivisibilityCount x q d =
        positiveTransitionDivisibilityCount x q d + 1 := by
    unfold transitionDivisibilityCount
      positiveTransitionDivisibilityCount
    exact_mod_cast hcountNat
  have hpositive :=
    abs_positiveTransitionDivisibilityRemainder_le hq hd
  unfold transitionDivisibilityRemainder
  rw [hcount]
  have hrearrange :
      positiveTransitionDivisibilityCount x q d + 1 -
          (smoothingTransitionRootCount x q d : ℝ) *
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) / d =
        positiveTransitionDivisibilityRemainder x q d + 1 := by
    unfold positiveTransitionDivisibilityRemainder
    ring
  rw [hrearrange]
  calc
    |positiveTransitionDivisibilityRemainder x q d + 1| ≤
        |positiveTransitionDivisibilityRemainder x q d| + |(1 : ℝ)| :=
      abs_add_le _ _
    _ ≤ 3 * smoothingTransitionRootCount x q d + 1 := by
      simpa using add_le_add_right hpositive 1

theorem transitionDivisibilityCount_eq_main_add_remainder
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) :
    transitionDivisibilityCount x q d =
      (smoothingTransitionRootCount x q d : ℝ) *
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) / d +
        transitionDivisibilityRemainder x q d := by
  unfold transitionDivisibilityRemainder
  ring

noncomputable def transitionMainQuadratic
    (x : ℕ) (q : ℕ × ℕ) (R : ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R,
    ∑ d₂ ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R,
      w d₁ * w d₂ *
        ((smoothingTransitionRootCount x q (d₁.lcm d₂) : ℝ) /
          (d₁.lcm d₂ : ℝ))

noncomputable def transitionErrorQuadratic
    (x : ℕ) (q : ℕ × ℕ) (R : ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R,
    ∑ d₂ ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R,
      |w d₁ * w d₂| *
        (3 * smoothingTransitionRootCount x q (d₁.lcm d₂) + 1)

/-- Selberg's indexed Λ² inequality with the congruence counts split into
their exact main quadratic form and a nonnegative error majorant. -/
theorem smoothingTransitionSifted_card_le_main_add_error
    {x R : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    (w : ℕ → ℝ) (hR : 1 ≤ R) (hw : w 1 = 1) :
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) *
        transitionMainQuadratic x q R w +
      transitionErrorQuadratic x q R w := by
  let D :=
    truncatedSieveDivisors (transitionSieveProduct x) R
  let H : ℝ :=
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ)
  have hsieve :=
    smoothingTransitionSifted_card_le_lcmCount
      x q R w hR hw
  calc
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
      ∑ d₁ ∈ D, ∑ d₂ ∈ D,
        w d₁ * w d₂ *
          transitionDivisibilityCount x q (d₁.lcm d₂) := by
      simpa only [D, transitionDivisibilityCount] using hsieve
    _ = H * transitionMainQuadratic x q R w +
        ∑ d₁ ∈ D, ∑ d₂ ∈ D,
          w d₁ * w d₂ *
            transitionDivisibilityRemainder x q
              (d₁.lcm d₂) := by
      simp_rw [transitionDivisibilityCount_eq_main_add_remainder,
        mul_add, Finset.sum_add_distrib]
      unfold transitionMainQuadratic
      simp only [D]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d₁ hd₁
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d₂ hd₂
      ring
    _ ≤ H * transitionMainQuadratic x q R w +
        transitionErrorQuadratic x q R w := by
      apply add_le_add_right
      unfold transitionErrorQuadratic
      simp only [D]
      apply Finset.sum_le_sum
      intro d₁ hd₁
      apply Finset.sum_le_sum
      intro d₂ hd₂
      have hd₁pos : 0 < d₁ :=
        Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hd₁).1)
          (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
      have hd₂pos : 0 < d₂ :=
        Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hd₂).1)
          (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
      have hlcmpos : 0 < d₁.lcm d₂ := by
        exact Nat.lcm_pos hd₁pos hd₂pos
      have hrem :=
        abs_transitionDivisibilityRemainder_le hq hlcmpos
      calc
        w d₁ * w d₂ *
            transitionDivisibilityRemainder x q
              (d₁.lcm d₂) ≤
          |w d₁ * w d₂ *
            transitionDivisibilityRemainder x q
              (d₁.lcm d₂)| := le_abs_self _
        _ = |w d₁ * w d₂| *
            |transitionDivisibilityRemainder x q
              (d₁.lcm d₂)| := abs_mul _ _
        _ ≤ |w d₁ * w d₂| *
            (3 * smoothingTransitionRootCount x q
              (d₁.lcm d₂) + 1) :=
          mul_le_mul_of_nonneg_left hrem (abs_nonneg _)

end Chen

end

