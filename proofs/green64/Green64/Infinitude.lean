module

public import Green64.PrimeExtraction
public import Green64.Localization

@[expose] public section

/-!
# Arbitrarily large witnesses and infinitude

Apply the prime-extraction theorem to the fixed smooth cutoff. Its support
places the shifted prime above `exp L`; choosing `L` large enough gives a
witness above any prescribed natural bound.
-/

section

set_option maxHeartbeats 2200000
set_option autoImplicit false
open Filter ArithmeticFunction
open scoped BigOperators Classical Topology ContDiff ArithmeticFunction.Omega
namespace Green64Analytic.Parity
open SourceBlockSieve

/-- A prime of the required shifted parity above every natural bound. -/
theorem prime_witnesses_unbounded (M : ℕ) :
    ∃ p : ℕ, p.Prime ∧ Odd (Ω (p - 2)) ∧ 0 < p - 2 ∧ M < p := by
  have hCandidates := negative_parity_prime_candidates
    localizingBump localizingBump_smooth
    localizingBump_support localizingBump_nonneg
    localizingBump_le_one localizingBump_interior
  have hExp : ∀ᶠ L : ℝ in atTop, (M : ℝ) < Real.exp L :=
    Real.tendsto_exp_atTop.eventually (eventually_gt_atTop (M : ℝ))
  obtain ⟨L, hCandidate, hLarge⟩ := (hCandidates.and hExp).exists
  obtain ⟨u, hu, hA, hPsi, hLo, hHi, huPos, hPrime, hOdd⟩ := hCandidate
  have hM : M < u := by exact_mod_cast hLarge.trans_le hLo
  refine ⟨u + 2, hPrime, ?_, ?_, by omega⟩
  · simpa only [Nat.add_sub_cancel] using hOdd
  · simpa only [Nat.add_sub_cancel] using huPos

/-- The set of primes with odd shifted prime-factor count is infinite. -/
theorem prime_witnesses_infinite :
    {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨p, hPrime, hOdd, hPositive, hLarge⟩ :=
    prime_witnesses_unbounded M
  exact ⟨p, ⟨hPrime, hOdd⟩, hLarge⟩

end Green64Analytic.Parity

end
