module

public import Green64.Library.Correlation.PrimeReturnHilbertSchur
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-!
# Weights / RetiredFactorialMoment

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRetiredFactorialMoment -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Polynomial
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The factorial moment functional. It will be applied to the
generating polynomial of the literal retired-prime register. -/
def sourceOriginalRetiredMoment434 : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => (n.factorial : ℝ) • LinearMap.id)

@[simp]
theorem source_original_RETIRED_moment_monomial434 (n : ℕ) (a : ℝ) :
    sourceOriginalRetiredMoment434 (Polynomial.monomial n a) =
      a * (n.factorial : ℝ) := by
  simp [sourceOriginalRetiredMoment434, Polynomial.lsum_apply,
    Polynomial.sum_monomial_index, mul_comm]

@[simp]
theorem source_original_RETIRED_moment_C434 (a : ℝ) :
    sourceOriginalRetiredMoment434 (Polynomial.C a) = a := by
  simpa only [Polynomial.monomial_zero_left, Nat.factorial_zero,
    Nat.cast_one, mul_one] using source_original_RETIRED_moment_monomial434 0 a

@[simp]
theorem source_original_RETIRED_moment_C_mul434 (a : ℝ) (p : ℝ[X]) :
    sourceOriginalRetiredMoment434 (Polynomial.C a * p) =
      a * sourceOriginalRetiredMoment434 p := by
  rw [← Polynomial.smul_eq_C_mul, map_smul]
  rfl

@[simp]
theorem source_original_RETIRED_moment_C_X_pow434 (a : ℝ) (n : ℕ) :
    sourceOriginalRetiredMoment434 (Polynomial.C a * Polynomial.X ^ n) =
      a * (n.factorial : ℝ) := by
  rw [Polynomial.C_mul_X_pow_eq_monomial,
    source_original_RETIRED_moment_monomial434]

/-- Positivity is coefficientwise; no order on polynomials is used. -/
theorem source_original_RETIRED_moment_nonneg434
    (p : ℝ[X]) (hp : ∀ n, 0 ≤ p.coeff n) :
    0 ≤ sourceOriginalRetiredMoment434 p := by
  change 0 ≤ ∑ n ∈ p.support, (n.factorial : ℝ) * p.coeff n
  exact Finset.sum_nonneg (fun n hn => mul_nonneg (Nat.cast_nonneg _) (hp n))

theorem source_original_RETIRED_moment_mono434
    (p q : ℝ[X]) (h : ∀ n, p.coeff n ≤ q.coeff n) :
    sourceOriginalRetiredMoment434 p ≤ sourceOriginalRetiredMoment434 q := by
  have hh := source_original_RETIRED_moment_nonneg434 (q-p)
    (fun n => by simpa only [Polynomial.coeff_sub] using sub_nonneg.mpr (h n))
  rw [map_sub] at hh
  exact sub_nonneg.mp hh

/-- Integration by parts in purely finite polynomial form. -/
theorem source_original_RETIRED_moment_derivative434 (p : ℝ[X]) :
    sourceOriginalRetiredMoment434 p =
      p.coeff 0 + sourceOriginalRetiredMoment434 (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, Polynomial.coeff_add, hp, hq]
      ring
  | monomial n a =>
      cases n with
      | zero => simp
      | succ n =>
          simp only [Polynomial.derivative_monomial,
            source_original_RETIRED_moment_monomial434,
            Polynomial.coeff_monomial, Nat.succ_ne_zero, if_false,
            Nat.succ_sub_one, zero_add, Nat.factorial_succ, Nat.cast_mul,
            Nat.cast_add, Nat.cast_one]
          ring

private theorem coeff_mul_nonneg (p q : ℝ[X])
    (hp : ∀ n, 0 ≤ p.coeff n) (hq : ∀ n, 0 ≤ q.coeff n) :
    ∀ n, 0 ≤ (p*q).coeff n := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun ij hij => mul_nonneg (hp _) (hq _))

private theorem coeff_one_add_nonneg (w : ℝ) (hw : 0 ≤ w) :
    ∀ n, 0 ≤ ((1 : ℝ[X]) + Polynomial.C w * Polynomial.X).coeff n := by
  intro n
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X]
  positivity

private theorem coeff_product_nonneg {U : Type} [DecidableEq U]
    (s : Finset U) (w : U → ℝ) (hw : ∀ p ∈ s, 0 ≤ w p) :
    ∀ n, 0 ≤ (∏ p ∈ s, ((1 : ℝ[X]) + Polynomial.C (w p) * Polynomial.X)).coeff n := by
  induction s using Finset.induction_on with
  | empty =>
      intro n
      simp only [Finset.prod_empty, Polynomial.coeff_one]
      split_ifs <;> norm_num
  | @insert p s hp ih =>
      rw [Finset.prod_insert hp]
      exact coeff_mul_nonneg _ _
        (coeff_one_add_nonneg _ (hw p (Finset.mem_insert_self _ _)))
        (ih (fun q hq => hw q (Finset.mem_insert_of_mem hq)))

private theorem product_erase_moment_le {U : Type} [DecidableEq U]
    (s : Finset U) (w : U → ℝ) (hw : ∀ p ∈ s, 0 ≤ w p)
    (p : U) (hp : p ∈ s) :
    sourceOriginalRetiredMoment434
        (∏ q ∈ s.erase p, ((1 : ℝ[X]) + Polynomial.C (w q) * Polynomial.X)) ≤
      sourceOriginalRetiredMoment434
        (∏ q ∈ s, ((1 : ℝ[X]) + Polynomial.C (w q) * Polynomial.X)) := by
  let f := fun q => (1 : ℝ[X]) + Polynomial.C (w q) * Polynomial.X
  change sourceOriginalRetiredMoment434 (∏ q ∈ s.erase p, f q) ≤
    sourceOriginalRetiredMoment434 (∏ q ∈ s, f q)
  rw [← Finset.mul_prod_erase s f hp]
  dsimp only [f]
  rw [add_mul, one_mul, map_add]
  have hn : ∀ n, 0 ≤
      ((Polynomial.C (w p) * Polynomial.X) *
        ∏ q ∈ s.erase p, ((1 : ℝ[X]) + Polynomial.C (w q) * Polynomial.X)).coeff n := by
    apply coeff_mul_nonneg
    · intro n
      have hwp := hw p hp
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X]
      positivity
    · exact coeff_product_nonneg _ w (fun q hq => hw q (Finset.mem_of_mem_erase hq))
  exact le_add_of_nonneg_right (source_original_RETIRED_moment_nonneg434 _ hn)

/-- All distinct retired histories have bounded total factorial mass
when their TRUE total weight is less than one. The bound has no
prime-pool cardinality and no time-horizon factor. -/
theorem source_original_RETIRED_partition_bound434
    {U : Type} [DecidableEq U] (s : Finset U) (w : U → ℝ)
    (hw : ∀ p ∈ s, 0 ≤ w p) (hM : ∑ p ∈ s, w p < 1) :
    sourceOriginalRetiredMoment434
        (∏ p ∈ s, ((1 : ℝ[X]) + Polynomial.C (w p) * Polynomial.X)) ≤
      1 / (1 - ∑ p ∈ s, w p) := by
  let P := ∏ p ∈ s, ((1 : ℝ[X]) + Polynomial.C (w p) * Polynomial.X)
  have h0 : P.coeff 0 = 1 := by
    simp [P, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  have hd : sourceOriginalRetiredMoment434 (Polynomial.derivative P) ≤
      (∑ p ∈ s, w p) * sourceOriginalRetiredMoment434 P := by
    dsimp only [P]
    rw [Polynomial.derivative_prod_finset, map_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    simp only [map_add, Polynomial.derivative_one, Polynomial.derivative_C_mul,
      Polynomial.derivative_X, mul_one, zero_add]
    rw [mul_comm, source_original_RETIRED_moment_C_mul434]
    exact mul_le_mul_of_nonneg_left (product_erase_moment_le s w hw p hp) (hw p hp)
  have hi := source_original_RETIRED_moment_derivative434 P
  rw [h0] at hi
  apply (le_div_iff₀ (sub_pos.mpr hM)).mpr
  nlinarith

/-- Exact finite exponential appearing in a retired column. -/
theorem source_original_RETIRED_shifted_power_exact434 (a : ℝ) (n : ℕ) :
    sourceOriginalRetiredMoment434 ((Polynomial.C a + Polynomial.X)^n) =
      (n.factorial : ℝ) * ∑ j ∈ Finset.range (n+1), a^j / (j.factorial : ℝ) := by
  rw [add_pow, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpoly :
      Polynomial.C a ^ j * Polynomial.X ^ (n-j) * (n.choose j : ℝ[X]) =
        Polynomial.C (a^j * (n.choose j : ℝ)) * Polynomial.X^(n-j) := by
    have hcast : (n.choose j : ℝ[X]) = Polynomial.C (n.choose j : ℝ) := by simp
    rw [hcast, ← Polynomial.C_pow, Polynomial.C_mul]
    ring
  rw [hpoly, source_original_RETIRED_moment_C_X_pow434]
  have hc : (n.choose j : ℝ) * (j.factorial : ℝ) * ((n-j).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp
  calc
    a^j * (n.choose j : ℝ) * ((n-j).factorial : ℝ) * (j.factorial : ℝ) =
        a^j * ((n.choose j : ℝ) * (j.factorial : ℝ) * ((n-j).factorial : ℝ)) := by ring
    _ = a^j * (n.factorial : ℝ) := by rw [hc]

/-- The column cost stays exponential in eta*V/t, independently
of the number of retired primes. -/
theorem source_original_RETIRED_shifted_power_bound434
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    sourceOriginalRetiredMoment434 ((Polynomial.C a + Polynomial.X)^n) ≤
      Real.exp a * (n.factorial : ℝ) := by
  rw [source_original_RETIRED_shifted_power_exact434, mul_comm (Real.exp a)]
  exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg ha (n+1))
    (Nat.cast_nonneg _)

end Green64Analytic.CorrelationSquare

end

end

