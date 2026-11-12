module

public import Mathlib

@[expose] public section

/-!
# Analysis / Estimates / LargePrimeBonferroni

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualLargePrimeBonferroni -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceSieveBarrier
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The actual large-prime subband of the original y=exp(aL) sieve. -/
def b610ActualLargePrimeBand434 (a theta L : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp (a*L)⌋₊).filter
    (fun p=>p.Prime ∧ Real.exp (a*theta*L)≤(p:ℝ))

/-- The exact elementary coefficient in the finite CRT local-density product. -/
def b610Elementary434 (P : Finset ℕ) (w : ℕ→ℝ) (r : ℕ) : ℝ :=
  ∑S∈P.powersetCard r,∏p∈S,w p

/-- Complete Bonferroni truncation by degree, before any lattice-error bound. -/
def b610Bonferroni434 (P : Finset ℕ) (w : ℕ→ℝ) (R : ℕ) : ℝ :=
  ∑r∈Finset.range (R+1),(-1:ℝ)^r*b610Elementary434 P w r

/-- Every local-density coefficient is nonnegative. -/
theorem b610_elementary_nonneg434 (P : Finset ℕ) (w : ℕ→ℝ)
    (hw : ∀p∈P,0≤w p) (r : ℕ) : 0≤b610Elementary434 P w r := by
  apply Finset.sum_nonneg
  intro S hS
  apply Finset.prod_nonneg
  intro p hp
  exact hw p ((Finset.mem_powersetCard.mp hS).1 hp)

/-- Adjacent complete truncations differ by the full next elementary
coefficient, not an asymptotic or an assumed error term. -/
theorem b610_adjacent_bonferroni_difference434
    (P : Finset ℕ) (w : ℕ→ℝ) (R : ℕ) :
    b610Bonferroni434 P w (R+1)-b610Bonferroni434 P w R =
      (-1:ℝ)^(R+1)*b610Elementary434 P w (R+1) := by
  unfold b610Bonferroni434
  rw [Finset.sum_range_succ]
  ring

/-- The exact interval width for nonnegative CRT local root probabilities. -/
theorem b610_adjacent_bonferroni_width434
    (P : Finset ℕ) (w : ℕ→ℝ) (hw : ∀p∈P,0≤w p) (R : ℕ) :
    |b610Bonferroni434 P w (R+1)-b610Bonferroni434 P w R| =
      b610Elementary434 P w (R+1) := by
  rw [b610_adjacent_bonferroni_difference434,abs_mul,abs_pow]
  simp only [abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (b610_elementary_nonneg434 P w hw (R+1))]

/-- Literal one-root or two-root sieve specialization; no arbitrary normalized
probability is substituted for nu/p. -/
theorem b610_actual_prime_band_width434 (a theta L : ℝ) (nu R : ℕ) :
    |b610Bonferroni434 (b610ActualLargePrimeBand434 a theta L)
        (fun p=>(nu:ℝ)/(p:ℝ)) (R+1)-
      b610Bonferroni434 (b610ActualLargePrimeBand434 a theta L)
        (fun p=>(nu:ℝ)/(p:ℝ)) R| =
    b610Elementary434 (b610ActualLargePrimeBand434 a theta L)
      (fun p=>(nu:ℝ)/(p:ℝ)) (R+1) := by
  apply b610_adjacent_bonferroni_width434
  intro p hp
  positivity

private theorem exp_nat_mul (u : ℝ) (n : ℕ) :
    Real.exp (u*(n:ℝ))=(Real.exp u)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_add,Nat.cast_one,mul_add,mul_one,Real.exp_add,pow_succ,ih]

/-- An actual prime-subband divisor which fits the explicit exp(cL)
CRT level has bounded degree. This derives the depth gate from the
literal primes and multiplicative modulus, not from a desired estimate. -/
theorem b610_actual_prime_band_product_depth434
    (a theta L c : ℝ) (ha : 0<a) (htheta : 0<theta) (hL : 0<L)
    (S : Finset ℕ) (hS : S⊆b610ActualLargePrimeBand434 a theta L)
    (hlevel : ((∏p∈S,p:ℕ):ℝ)≤Real.exp (c*L)) :
    (S.card:ℝ)≤ c/(a*theta) := by
  have hp (p : ℕ) (hp : p∈S) : Real.exp (a*theta*L)≤(p:ℝ) :=
    (Finset.mem_filter.mp (hS hp)).2.2
  have hprod : (Real.exp (a*theta*L))^S.card≤Real.exp (c*L) := by
    calc
      _ = ∏_p∈S,Real.exp (a*theta*L) := by simp
      _ ≤ ∏p∈S,(p:ℝ) := Finset.prod_le_prod₀ (fun _ _=>Real.exp_nonneg _) hp
      _ = ((∏p∈S,p:ℕ):ℝ) := by simp
      _ ≤ _ := hlevel
  rw [←exp_nat_mul] at hprod
  have he := Real.exp_le_exp.mp hprod
  apply (le_div_iff₀ (mul_pos ha htheta)).mpr
  apply le_of_mul_le_mul_right (a:=L) _ hL
  nlinarith

/-- The number of degree-r absolute CRT lattice-error terms is exactly
the full binomial count, with no cancellation between their error signs. -/
theorem b610_complete_CRT_term_count434 (P : Finset ℕ) (r : ℕ) :
    (P.powersetCard r).card=P.card.choose r := Finset.card_powersetCard _ _
end Green64Analytic.SourceSieveBarrier

end

end

