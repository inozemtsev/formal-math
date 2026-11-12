module

public import Mathlib

@[expose] public section

/-!
# Analysis / Estimates / SourceDivisorPrimePowerComparison

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceDivisorPrimePowerComparison -/

section

/-! An unconditional majorant for squared natural divisor counts.
The core local inequality at prime powers is elementary:
(k+1)(i-k+1) >= i+1, for 0<=k<=i.
-/

namespace Green64Analytic.CorrelationMellin

private theorem source_pow_div_pow (p i k : ℕ) (hp : 0 < p) (hk : k ≤ i) :
    p^i / p^k = p^(i-k) := by
  have heq : p^i = p^(i-k) * p^k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [heq]
  rw [mul_comm (p^(i-k)) (p^k)]
  exact Nat.mul_div_cancel_left (p^(i-k)) (Nat.pow_pos hp)

private theorem source_prime_power_factor_point (i k : ℕ) (hk : k ≤ i) :
    i+1 ≤ (k+1)*(i-k+1) := by
  have hsum : k+(i-k)=i := by omega
  nlinarith [Nat.zero_le (k*(i-k))]
/-- `tau(p^i)^2` is dominated by the genuinely fourfold divisor
convolution, without any squarefreeness assumption. -/
theorem source_sigma_square_prime_pow_le_fourfold
    (p i : ℕ) (hp : Nat.Prime p) :
    (ArithmeticFunction.sigma 0 (p^i))^2 ≤
      ((ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0)) (p^i) := by
  have hconv :
      ((ArithmeticFunction.sigma 0)*(ArithmeticFunction.sigma 0)) (p^i) =
      ∑ k ∈ Finset.range (i+1), (k+1)*(i-k+1) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal
        (fun a b => ArithmeticFunction.sigma 0 a * ArithmeticFunction.sigma 0 b),
      Nat.sum_divisors_prime_pow hp]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLe : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [source_pow_div_pow p i k hp.pos hkLe,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp, hconv]
  calc
    (i+1)^2 = ∑ _k ∈ Finset.range (i+1), (i+1) := by simp [pow_two]
    _ ≤ ∑ k ∈ Finset.range (i+1), (k+1)*(i-k+1) := by
      apply Finset.sum_le_sum
      intro k hk
      exact source_prime_power_factor_point i k
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
end Green64Analytic.CorrelationMellin

end

