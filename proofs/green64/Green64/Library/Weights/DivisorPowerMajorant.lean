module

public import Mathlib
public import Green64.Library.Weights.Part033

@[expose] public section

/-!
# Weights / DivisorPowerMajorant

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## DivisorPowerMajorant -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceDivisorMoment
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The elementary divisor submultiplicativity already used inside the
inherited global moment proof, exposed here for the genuine convolution. -/
private theorem b593_divisors_card_mul_le (a b : ℕ) :
    (a*b).divisors.card ≤ a.divisors.card*b.divisors.card := by
  by_cases ha : a=0
  · simp [ha]
  by_cases hb : b=0
  · simp [hb]
  have hsub : (a*b).divisors ⊆
      (a.divisors ×ˢ b.divisors).image (fun p=>p.1*p.2) := by
    intro d hd
    rcases Nat.dvd_mul.mp (Nat.mem_divisors.mp hd).1 with ⟨u,v,hu,hv,he⟩
    exact Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hu,ha⟩,Nat.mem_divisors.mpr ⟨hv,hb⟩⟩,he⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans_eq (Finset.card_product _ _))

private theorem b593_divisor_power_convolution (n r : ℕ) :
    n.divisors.card^(r+1) ≤
      ∑ d ∈ n.divisors, d.divisors.card^r*(n/d).divisors.card^r := by
  calc
    _ = ∑ d ∈ n.divisors, n.divisors.card^r := by
      simp [Finset.sum_const,pow_succ,Nat.mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      have hh := b593_divisors_card_mul_le d (n/d)
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1] at hh
      simpa only [mul_pow] using Nat.pow_le_pow_left hh r

/-- All-integer natural divisor powers are bounded by the actual
2^r-fold Dirichlet convolution, with no squarefree restriction. -/
theorem b593_divisor_power_le_zeta_power434 (r n : ℕ) (hn : n ≠ 0) :
    n.divisors.card^r ≤ (ArithmeticFunction.zeta^(2^r)) n := by
  induction r generalizing n with
  | zero => simp [ArithmeticFunction.zeta_apply_ne hn]
  | succ r ih =>
    calc
      n.divisors.card^(r+1) ≤
          ∑ d ∈ n.divisors, d.divisors.card^r*(n/d).divisors.card^r :=
        b593_divisor_power_convolution n r
      _ ≤ ∑ d ∈ n.divisors,
          (ArithmeticFunction.zeta^(2^r)) d *
          (ArithmeticFunction.zeta^(2^r)) (n/d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdn := (Nat.mem_divisors.mp hd).1
        have hnpos : 0<n := Nat.pos_of_ne_zero hn
        have hdpos : 0<d := Nat.pos_of_dvd_of_pos hdn hnpos
        have hdivpos : 0<n/d := Nat.div_pos (Nat.le_of_dvd hnpos hdn) hdpos
        exact Nat.mul_le_mul (ih d (Nat.ne_of_gt hdpos))
          (ih (n/d) (Nat.ne_of_gt hdivpos))
      _ = ((ArithmeticFunction.zeta^(2^r)) *
            (ArithmeticFunction.zeta^(2^r))) n := by
        rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal
          (fun a b => (ArithmeticFunction.zeta^(2^r)) a *
            (ArithmeticFunction.zeta^(2^r)) b)]
      _ = (ArithmeticFunction.zeta^(2^(r+1))) n := by
        rw [←pow_add]
        congr 2
        rw [pow_succ]
        omega

/-- The exact d16 majorant needed by the two original stripped Q cores. -/
theorem b593_actual_tau_four_le_d16_434 (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card^4 ≤ (ArithmeticFunction.zeta^16) n := by
  simpa using b593_divisor_power_le_zeta_power434 4 n hn

/-- All positive zeta-convolution harmonic sums, reusing the inherited
nonnegative convolution-product inequality. -/
theorem b593_zeta_power_harmonic434 (N r : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((ArithmeticFunction.zeta^(r+1)) n:ℝ)/(n:ℝ)) ≤
      (reciprocalHarmonic N)^(r+1) := by
  induction r with
  | zero => simp only [zero_add,pow_one]; rw [zeta_reciprocal_eq_harmonic]
  | succ r ih =>
    have hH := reciprocalHarmonic_nonneg N
    calc
      _ = ∑ n ∈ Finset.Ioc 0 N,
          (((ArithmeticFunction.zeta^(r+1))*ArithmeticFunction.zeta) n:ℝ)/(n:ℝ) := by
        rw [pow_succ]
      _ ≤ (∑ n ∈ Finset.Ioc 0 N,
          ((ArithmeticFunction.zeta^(r+1)) n:ℝ)/(n:ℝ))*
          (∑ n ∈ Finset.Ioc 0 N,(ArithmeticFunction.zeta n:ℝ)/(n:ℝ)) :=
        reciprocal_convolution_le_product (ArithmeticFunction.zeta^(r+1))
          ArithmeticFunction.zeta N
      _ = (∑ n ∈ Finset.Ioc 0 N,
          ((ArithmeticFunction.zeta^(r+1)) n:ℝ)/(n:ℝ))*reciprocalHarmonic N := by
        rw [zeta_reciprocal_eq_harmonic]
      _ ≤ (reciprocalHarmonic N)^(r+1)*reciprocalHarmonic N :=
        mul_le_mul_of_nonneg_right ih hH
      _ = _ := by simp only [pow_succ]

/-- The unweighted positive-convolution count saves one harmonic power;
it is used for the explicit lattice-error term, not a global AP cap. -/
theorem b593_zeta_power_unweighted434 (N r : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((ArithmeticFunction.zeta^(r+2)) n:ℝ)) ≤
      (N:ℝ)*(reciprocalHarmonic N)^(r+1) := by
  have heq : ArithmeticFunction.zeta^(r+2) =
      (ArithmeticFunction.zeta^(r+1))*ArithmeticFunction.zeta := by rw [pow_succ]
  simp_rw [heq]
  exact (sum_mul_zeta_le_reciprocal (ArithmeticFunction.zeta^(r+1)) N).trans
    (mul_le_mul_of_nonneg_left (b593_zeta_power_harmonic434 N r) (Nat.cast_nonneg N))
end Green64Analytic.SourceDivisorMoment

end

end

