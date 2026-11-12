module

public import Green64

@[expose] public section

open scoped ArithmeticFunction.Omega

-- The exact proposition, with the underlying Mathlib function written explicitly.
example : Set.Infinite
    {p : ℕ | Nat.Prime p ∧ Odd (ArithmeticFunction.cardFactors (p - 2))} :=
  Green64.green_64

-- Every bound has a witness; subtraction is taken in the natural numbers.
example (M : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ Odd (ArithmeticFunction.cardFactors (p - 2)) ∧
      0 < p - 2 ∧ M < p :=
  Green64.primes_unbounded M

-- Multiplicities matter: 9 has two prime factors, both equal to 3.
example : ¬ Odd (Ω 9) := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num,
    ArithmeticFunction.cardFactors_apply_prime_pow (by norm_num)]
  decide
