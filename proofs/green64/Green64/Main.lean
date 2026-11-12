module

/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
public import Green64.Infinitude

@[expose] public section

/-!
# Green's Problem 64

There are infinitely many primes `p` for which `p - 2` has an odd number of
prime factors, counted with multiplicity.

The weighted sieve provides such a prime above every natural bound.
`Green64.Infinitude` proves that statement from the positive prime mass estimate.
-/

open scoped ArithmeticFunction.Omega

namespace Green64

/-- There is a prime with odd shifted prime-factor parity above every bound. -/
theorem primes_unbounded (M : ℕ) :
    ∃ p : ℕ, p.Prime ∧ Odd (Ω (p - 2)) ∧ 0 < p - 2 ∧ M < p :=
  Green64Analytic.Parity.prime_witnesses_unbounded M

/-- Infinitely many primes `p` have `Ω (p - 2)` odd, with multiplicities counted. -/
theorem green_64 : {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨p, hp, hparity, _, hlarge⟩ := primes_unbounded M
  exact ⟨p, ⟨hp, hparity⟩, hlarge⟩

end Green64
