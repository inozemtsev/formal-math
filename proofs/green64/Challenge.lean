module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Set.Finite.Basic

/-!
Ben Green posed this question as Problem 64 in 100 Open Problems (p. 31).
https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.64
-/

public section

open scoped ArithmeticFunction.Omega

namespace Green64

/-- For infinitely many primes `p`, the integer `p - 2` has an odd number of
prime factors, counted with multiplicity. -/
theorem green_64 : {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))}.Infinite := by
  sorry

end Green64
