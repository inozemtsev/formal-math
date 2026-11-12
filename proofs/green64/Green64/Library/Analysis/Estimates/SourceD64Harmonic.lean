module

public import Green64.Library.Weights.Part033

@[expose] public section

/-!
# Analysis / Estimates / SourceD64Harmonic

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceD64Harmonic -/

section

open scoped ArithmeticFunction.zeta BigOperators

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1250000

/-- Universal harmonic-weighted moment of the GENUINE (k+1)-fold
Dirichlet zeta convolution. Follows from the exact nonnegative
arithmetic Dirichlet-convolution hyperbola inequality. -/
theorem source_zeta_power_reciprocal_harmonic434 (Z : ℕ) :
    ∀ (k : ℕ),
      (∑ n ∈ Finset.Ioc 0 Z,
         ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1)) n : ℕ):ℝ) /
           (n:ℝ)) ≤
        (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Z)^(k+1) := by
  intro k
  induction k with
  | zero =>
      have heq := Green64Analytic.SourceDivisorMoment.zeta_reciprocal_eq_harmonic Z
      simpa only [Nat.zero_add, pow_one, le_refl] using heq.le
  | succ k ih =>
      let H := Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Z
      have hH : 0 ≤ H :=
        Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_nonneg Z
      have hConv := Green64Analytic.SourceDivisorMoment.reciprocal_convolution_le_product
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1))
        ArithmeticFunction.zeta Z
      have hZeta := Green64Analytic.SourceDivisorMoment.zeta_reciprocal_eq_harmonic Z
      calc
        (∑ n ∈ Finset.Ioc 0 Z,
           ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k.succ+1)) n : ℕ):ℝ)/(n:ℝ))
          = (∑ n ∈ Finset.Ioc 0 Z,
              (((((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1)) *
                 ArithmeticFunction.zeta) n : ℕ):ℝ)/(n:ℝ)) := by
              simp only [Nat.succ_eq_add_one, pow_succ]
        _ ≤ (∑ n ∈ Finset.Ioc 0 Z,
              ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1)) n : ℕ):ℝ)/(n:ℝ)) *
            (∑ n ∈ Finset.Ioc 0 Z,
              ((ArithmeticFunction.zeta n : ℕ):ℝ)/(n:ℝ)) := hConv
        _ = (∑ n ∈ Finset.Ioc 0 Z,
              ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1)) n : ℕ):ℝ)/(n:ℝ)) *
            H := by rw [hZeta]
        _ ≤ H^(k+1)*H := mul_le_mul_of_nonneg_right ih hH
        _ = H^(k.succ+1) := by
              simp only [Nat.succ_eq_add_one, pow_succ]
end Green64Analytic.CorrelationSquare

end

