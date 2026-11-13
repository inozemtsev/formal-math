module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Set.Finite.Basic

/-!
# Green's Problem 64

For a natural number `n`, Mathlib's `Ω n` counts prime factors with multiplicity.
The set of primes `p` for which `Ω (p - 2)` is odd is infinite.

Subtraction is natural-number subtraction. Mathlib sets `Ω 0 = Ω 1 = 0`, so
neither `p = 2` nor `p = 3` contributes to this set. There are no hypotheses.

The question is Problem 64 in Ben Green's *100 Open Problems*:
https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.64

This statement module imports only Mathlib. Its deliberate proof hole specifies
the claim compared with the separately compiled `Solution` module.
-/

public section

open scoped ArithmeticFunction.Omega

namespace Green64

/-- Infinitely many primes have an odd number of prime factors in `p - 2`,
counted with multiplicity. -/
theorem green_64 : {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))}.Infinite := by
  sorry

end Green64
