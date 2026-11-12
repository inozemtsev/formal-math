module

public import Green64.Library.Sieve.Foundation.LargeSieve.Part001
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section

/-!
# Sieve / Foundation / Lemma6 / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma6.DirichletLogDerivativePositivity -/

section

open scoped LSeries.notation

namespace Chen
theorem vonMangoldt_three_four_one_term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) :
    0 ≤ (3 * LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n +
      4 * LSeries.term (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I) n +
      LSeries.term (fun m => (χ ^ 2) m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re := by
  by_cases hn : n = 0
  · subst n
    simp
  let a : ℝ := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)
  let z : ℂ := χ n * dirichletPhase n t
  have ha : 0 ≤ a := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [norm_mul, norm_dirichletPhase n hn t, mul_one]
    exact χ.norm_le_one n
  have hp := real_part_trigonometric_polynomial_nonneg z hz
  rw [vonMangoldt_term_real σ n hn, vonMangoldt_twist_term_phase χ σ t n hn,
    vonMangoldt_twist_term_phase (χ ^ 2) σ (2 * t) n hn,
    MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0), dirichletPhase_twice, ← mul_pow]
  change 0 ≤ (3 * (a : ℂ) + 4 * ((a : ℂ) * z) + (a : ℂ) * z ^ 2).re
  have he : (3 * (a : ℂ) + 4 * ((a : ℂ) * z) + (a : ℂ) * z ^ 2).re =
      a * (3 + 4 * z.re + (z ^ 2).re) := by simp [Complex.mul_re]; ring
  rw [he]
  exact mul_nonneg ha hp
theorem vonMangoldt_three_four_one_series_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (3 * LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) +
      4 * LSeries (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I) +
      LSeries (fun m => (χ ^ 2) m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have h1 := ArithmeticFunction.LSeriesSummable_vonMangoldt (show 1 < (σ : ℂ).re by simpa using hσ)
  have h2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
    (show 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re by simpa using hσ)
  have h3 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2)
    (show 1 < ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re by simpa using hσ)
  change Summable (fun n => LSeries.term
    (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
    ((σ : ℂ) + (t : ℂ) * Complex.I) n) at h2
  change Summable (fun n => LSeries.term
    (fun m => (χ ^ 2) m * (ArithmeticFunction.vonMangoldt m : ℂ))
    ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n) at h3
  have hsum := ((h1.mul_left (3 : ℂ)).add (h2.mul_left (4 : ℂ))).add h3
  have hn : 0 ≤ (∑' n, (3 * LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n +
      4 * LSeries.term (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I) n +
      LSeries.term (fun m => (χ ^ 2) m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n)).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_nonneg (vonMangoldt_three_four_one_term_nonneg χ σ t)
  rw [((h1.mul_left (3 : ℂ)).add (h2.mul_left (4 : ℂ))).tsum_add h3,
    (h1.mul_left (3 : ℂ)).tsum_add (h2.mul_left (4 : ℂ)), tsum_mul_left, tsum_mul_left] at hn
  exact hn
theorem LSeries_twist_vonMangoldt_eq_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ)) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
/-- The classical three-four-one inequality for logarithmic derivatives,
valid uniformly in every Dirichlet character on the half-plane of absolute convergence. -/
theorem Dirichlet_logDeriv_three_four_one_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) +
      4 * (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)) +
      (-deriv (DirichletCharacter.LFunction (χ ^ 2)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) /
        DirichletCharacter.LFunction (χ ^ 2) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I))).re := by
  have h := vonMangoldt_three_four_one_series_nonneg χ σ t hσ
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ),
    LSeries_twist_vonMangoldt_eq_LFunction χ _ (by simpa using hσ),
    LSeries_twist_vonMangoldt_eq_LFunction (χ ^ 2) _ (by simpa using hσ)] at h
  exact h
end Chen

end

/-! ## ChenTheorem.Lemma6.Mollifier -/

section

/-
The finite Möbius mollifier coefficients used before equation (14) in the
proof of Lemma 6.

The coefficient below is that of `1 - L_H(s,χ) S(H,s,χ)`, where both
Dirichlet polynomials are truncated at `H`.  These elementary support and
divisor bounds are the algebraic input for the dyadic large sieve.
-/

open scoped ArithmeticFunction.Moebius Classical
namespace Chen

/-- Chen's coefficient `C_H(n)`: the delta coefficient minus the truncated
convolution of `1` with Möbius. -/
noncomputable def lemma6MollifierCoeff (H n : ℕ) : ℤ :=
  (if n = 1 then 1 else 0) -
    ∑ p ∈ n.divisorsAntidiagonal,
      if p.1 ≤ H ∧ p.2 ≤ H then ArithmeticFunction.moebius p.2 else 0

@[simp]
theorem lemma6MollifierCoeff_one {H : ℕ} (hH : 1 ≤ H) :
    lemma6MollifierCoeff H 1 = 0 := by
  unfold lemma6MollifierCoeff
  simp [hH]
/-- The truncated convolution has no support beyond `H²`. -/
theorem lemma6MollifierCoeff_eq_zero_of_sq_lt
    {H n : ℕ} (hH : 1 ≤ H) (h : H * H < n) :
    lemma6MollifierCoeff H n = 0 := by
  have hn1 : n ≠ 1 := by
    intro hn
    subst n
    have hHH : 1 ≤ H * H := by
      simpa only [one_mul] using Nat.mul_le_mul hH hH
    omega
  unfold lemma6MollifierCoeff
  rw [if_neg hn1, zero_sub]
  have hsum :
      ∑ p ∈ n.divisorsAntidiagonal,
        (if p.1 ≤ H ∧ p.2 ≤ H then
          ArithmeticFunction.moebius p.2 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
    rw [if_neg]
    intro hboth
    have hmul : p.1 * p.2 ≤ H * H :=
      Nat.mul_le_mul hboth.1 hboth.2
    omega
  rw [hsum, neg_zero]
/-- For `n ≤ H`, Möbius inversion makes the coefficient vanish. -/
theorem lemma6MollifierCoeff_eq_zero_of_le
    {H n : ℕ} (hH : 1 ≤ H) (hnpos : 1 ≤ n) (hnH : n ≤ H) :
    lemma6MollifierCoeff H n = 0 := by
  by_cases hn1 : n = 1
  · subst n
    exact lemma6MollifierCoeff_one hH
  have hn0 : n ≠ 0 := by omega
  have hbounds : ∀ p ∈ n.divisorsAntidiagonal,
      p.1 ≤ H ∧ p.2 ≤ H := by
    intro p hp
    have hp1dvd := Nat.dvd_of_mem_divisors
      (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have hp2dvd := Nat.dvd_of_mem_divisors
      (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    exact ⟨(Nat.le_of_dvd (by omega) hp1dvd).trans hnH,
      (Nat.le_of_dvd (by omega) hp2dvd).trans hnH⟩
  have hfiltered :
      (∑ p ∈ n.divisorsAntidiagonal,
        if p.1 ≤ H ∧ p.2 ≤ H then
          ArithmeticFunction.moebius p.2 else 0) =
      ∑ p ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.moebius p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [if_pos (hbounds p hp)]
  have hconv :
      (∑ p ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.moebius p.2) = 0 := by
    have hfun := congrArg (fun f : ArithmeticFunction ℤ => f n)
      (ArithmeticFunction.coe_zeta_mul_moebius :
        ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
          ArithmeticFunction.moebius) = 1)
    rw [ArithmeticFunction.mul_apply] at hfun
    have hfun' :
        (∑ p ∈ n.divisorsAntidiagonal,
          if p.1 = 0 then 0 else ArithmeticFunction.moebius p.2) = 0 := by
      simpa [ArithmeticFunction.zeta_apply, hn0, hn1] using hfun
    calc
      (∑ p ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.moebius p.2) =
        ∑ p ∈ n.divisorsAntidiagonal,
          (if p.1 = 0 then 0 else ArithmeticFunction.moebius p.2) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [if_neg (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)]
      _ = 0 := hfun'
  unfold lemma6MollifierCoeff
  rw [if_neg hn1, hfiltered, hconv, sub_zero]
/-- The paper's elementary `|C_H(n)| ≤ τ(n)` bound, stated using the
equivalent cardinality of the divisor antidiagonal. -/
theorem abs_lemma6MollifierCoeff_le_card
    {H n : ℕ} (hn1 : n ≠ 1) :
    |lemma6MollifierCoeff H n| ≤
      (n.divisorsAntidiagonal.card : ℤ) := by
  let f : ℕ × ℕ → ℤ := fun p =>
    if p.1 ≤ H ∧ p.2 ≤ H then ArithmeticFunction.moebius p.2 else 0
  calc
    |lemma6MollifierCoeff H n| =
        |∑ p ∈ n.divisorsAntidiagonal, f p| := by
      unfold lemma6MollifierCoeff
      rw [if_neg hn1, zero_sub, abs_neg]
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, |f p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp only [f]
      split_ifs
      · exact ArithmeticFunction.abs_moebius_le_one
      · simp
    _ = (n.divisorsAntidiagonal.card : ℤ) := by simp
/-- The pairs in the truncated product whose product is `n` are exactly the
bounded divisor-antidivisor pairs of `n`.  This is the finite fibre used to
regroup the two truncated Dirichlet polynomials in the proof of Lemma 6. -/
theorem lemma6MollifierFiber_eq (H n : ℕ) :
    ((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
        (fun p => p.1 * p.2 = n)) =
      n.divisorsAntidiagonal.filter
        (fun p => p.1 ≤ H ∧ p.2 ≤ H) := by
  ext p
  constructor
  · intro hp
    have hpdata := Finset.mem_filter.mp hp
    have hpmem := Finset.mem_product.mp hpdata.1
    have hp1 := Finset.mem_Icc.mp hpmem.1
    have hp2 := Finset.mem_Icc.mp hpmem.2
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hpdata.2, ?_⟩,
      hp1.2, hp2.2⟩
    intro hn0
    rw [hn0] at hpdata
    have hp1pos : 0 < p.1 := by omega
    have hp2pos : 0 < p.2 := by omega
    have := Nat.mul_pos hp1pos hp2pos
    omega
  · intro hp
    have hpdata := Finset.mem_filter.mp hp
    have hanti := Nat.mem_divisorsAntidiagonal.mp hpdata.1
    have hp1ne := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hpdata.1
    have hp2ne := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hpdata.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hp1ne, hpdata.2.1⟩,
        Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hp2ne, hpdata.2.2⟩⟩,
      hanti.1⟩
/-- The mollifier coefficient as a Kronecker delta minus the fibre of the
truncated product. -/
theorem lemma6MollifierCoeff_eq_delta_sub_fiber (H n : ℕ) :
    lemma6MollifierCoeff H n =
      (if n = 1 then 1 else 0) -
        ∑ p ∈ (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
            (fun p => p.1 * p.2 = n),
          ArithmeticFunction.moebius p.2 := by
  unfold lemma6MollifierCoeff
  rw [← Finset.sum_filter]
  rw [← lemma6MollifierFiber_eq]
/-- The finite truncation of the Dirichlet series playing the role of
`L(ω, χ)` in the exact algebraic part of equation (14). -/
noncomputable def lemma6TruncatedLPolynomial
    {R : Type*} [AddCommMonoid R] (H : ℕ) (a : ℕ → R) : R :=
  ∑ n ∈ Finset.Icc 1 H, a n

/-- The truncated Möbius polynomial `S(H, ω, χ)` in equation (14). -/
noncomputable def lemma6MollifierPolynomial
    {R : Type*} [Ring R] (H : ℕ) (a : ℕ → R) : R :=
  ∑ n ∈ Finset.Icc 1 H,
    (ArithmeticFunction.moebius n : R) * a n
/-- The finite `C_H`-polynomial on the right-hand side of equation (14). -/
noncomputable def lemma6MollifierRemainderPolynomial
    {R : Type*} [Ring R] (H : ℕ) (a : ℕ → R) : R :=
  ∑ n ∈ Finset.Icc 1 (H * H),
    (lemma6MollifierCoeff H n : R) * a n
/-- Regroup the product of the two truncated Dirichlet polynomials by the
value `n = m * d`. -/
theorem lemma6_truncated_product_eq_sum_fibers
    {R : Type*} [CommRing R] (H : ℕ) (a : ℕ → R)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → a (m * n) = a m * a n) :
    lemma6TruncatedLPolynomial H a * lemma6MollifierPolynomial H a =
      ∑ n ∈ Finset.Icc 1 (H * H),
        (∑ p ∈ (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
            (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.2 : R)) * a n := by
  let S := Finset.Icc 1 H
  let P := S ×ˢ S
  let N := Finset.Icc 1 (H * H)
  have hprod_mem (p : ℕ × ℕ) (hp : p ∈ P) : p.1 * p.2 ∈ N := by
    have hpmem := Finset.mem_product.mp hp
    have hp1 := Finset.mem_Icc.mp hpmem.1
    have hp2 := Finset.mem_Icc.mp hpmem.2
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hp1.1 hp2.1, Nat.mul_le_mul hp1.2 hp2.2⟩
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P N
    (fun p : ℕ × ℕ => p.1 * p.2)
    (fun p => (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2))
  rw [Finset.filter_eq_self.mpr hprod_mem] at hfiber
  change (∑ n ∈ S, a n) *
      (∑ n ∈ S, (ArithmeticFunction.moebius n : R) * a n) = _
  calc
    (∑ n ∈ S, a n) *
        (∑ n ∈ S, (ArithmeticFunction.moebius n : R) * a n) =
      ∑ p ∈ P,
        (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      apply Finset.sum_congr rfl
      intro p hp
      have hpmem := Finset.mem_product.mp hp
      have hp1 := (Finset.mem_Icc.mp hpmem.1).1
      have hp2 := (Finset.mem_Icc.mp hpmem.2).1
      rw [hmul p.1 p.2 hp1 hp2]
      ring
    _ = ∑ n ∈ N,
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2) :=
      hfiber.symm
    _ = ∑ n ∈ N,
        (∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.2 : R)) * a n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
/-- Exact finite form of the `C_H` identity used before equation (14):
`1 - L_H(a) S_H(a) = ∑_{n ≤ H²} C_H(n) a(n)` for multiplicative `a`
normalised by `a(1) = 1`. -/
theorem lemma6_one_sub_truncated_product_eq_remainder
    {R : Type*} [CommRing R] {H : ℕ} (hH : 1 ≤ H)
    (a : ℕ → R) (ha1 : a 1 = 1)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → a (m * n) = a m * a n) :
    1 - lemma6TruncatedLPolynomial H a * lemma6MollifierPolynomial H a =
      lemma6MollifierRemainderPolynomial H a := by
  let N := Finset.Icc 1 (H * H)
  let P := Finset.Icc 1 H ×ˢ Finset.Icc 1 H
  have h1mem : 1 ∈ N := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact le_rfl
    · nlinarith
  have hdelta :
      ∑ n ∈ N, (if n = 1 then (1 : R) else 0) * a n = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp [ha1]
    · intro b hb hbne
      simp [hbne]
    · exact fun h => (h h1mem).elim
  rw [lemma6_truncated_product_eq_sum_fibers H a hmul]
  change 1 - (∑ n ∈ N,
      (∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
        (ArithmeticFunction.moebius p.2 : R)) * a n) = _
  rw [← hdelta, ← Finset.sum_sub_distrib]
  unfold lemma6MollifierRemainderPolynomial
  change (∑ n ∈ N,
      ((if n = 1 then (1 : R) else 0) * a n -
        (∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.2 : R)) * a n)) =
    ∑ n ∈ N, (lemma6MollifierCoeff H n : R) * a n
  apply Finset.sum_congr rfl
  intro n hn
  rw [lemma6MollifierCoeff_eq_delta_sub_fiber]
  push_cast
  ring
/-- Equation (16), separated from the analytic meaning of its three
factors.  Once `L` is nonzero, the logarithmic derivative splits into the
mollified remainder term and the derivative--mollifier term:
`L'/L = (L'/L) * (1 - L*S) + L'*S`. -/
theorem lemma6_logDeriv_mollifier_identity
    {K : Type*} [Field K] (L L' S : K) (hL : L ≠ 0) :
    L' / L = (L' / L) * (1 - L * S) + L' * S := by
  have hcancel : L⁻¹ * L = 1 := inv_mul_cancel₀ hL
  have hmiddle : (L' * L⁻¹) * (L * S) = L' * S := by
    calc
      (L' * L⁻¹) * (L * S) = L' * (L⁻¹ * L) * S := by ring
      _ = L' * S := by rw [hcancel, mul_one]
  rw [div_eq_mul_inv, mul_sub, mul_one, hmiddle, sub_add_cancel]
end Chen

end

/-! ## ChenTheorem.Lemma6.AnalyticDecomposition -/

section

/-
The analytic specialization of equation (16) in Chen's proof of Lemma 6.

On the line `α = 1 + 1 / log x`, the Dirichlet L-function is represented
by its absolutely convergent series and is nonzero.  This file instantiates
the algebraic mollifier identity with the actual L-function and records the
pointwise `A + B` norm split used in equation (17).
-/

open Real
open scoped ArithmeticFunction.Moebius Classical
namespace Chen

/-- The vertical point `α + iν`, where `α = 1 + 1 / log x`. -/
noncomputable def lemma6AlphaPoint (x : ℕ) (ν : ℝ) : ℂ :=
  ((1 + 1 / Real.log x : ℝ) : ℂ) + (ν : ℂ) * Complex.I

@[simp]
theorem lemma6AlphaPoint_re (x : ℕ) (ν : ℝ) :
    (lemma6AlphaPoint x ν).re = 1 + 1 / Real.log x := by
  simp only [lemma6AlphaPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
theorem one_lt_lemma6AlphaPoint_re {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    (1 : ℝ) < (lemma6AlphaPoint x ν).re := by
  rw [lemma6AlphaPoint_re]
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hdiv : 0 < (1 : ℝ) / Real.log (x : ℝ) :=
    div_pos zero_lt_one hlog
  linarith
/-- The truncated Möbius polynomial `S(H,s,χ)` from equations (14)--(17). -/
noncomputable def lemma6MollifierAt
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H,
    (ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s
/-- The truncated Möbius mollifier is an entire Dirichlet polynomial in
the complex variable. -/
theorem differentiable_lemma6MollifierAt
    {q : ℕ} (H : ℕ) (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (fun s => lemma6MollifierAt H s χ) := by
  unfold lemma6MollifierAt
  apply Differentiable.fun_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  letI : NeZero (n : ℂ) := ⟨hn0⟩
  have hpow : Differentiable ℂ (fun s : ℂ => (n : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero _
  have hinv : Differentiable ℂ (fun s : ℂ => ((n : ℂ) ^ s)⁻¹) :=
    hpow.inv (fun s => Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))
  have hconst : Differentiable ℂ
      (fun _ : ℂ => (ArithmeticFunction.moebius n : ℂ) * χ n) :=
    differentiable_const _
  change Differentiable ℂ (fun s : ℂ =>
    ((ArithmeticFunction.moebius n : ℂ) * χ n) * ((n : ℂ) ^ s)⁻¹)
  exact hconst.mul hinv
/-- Equation (16) for the actual Dirichlet L-function on Chen's
`α`-line.  Nonvanishing is discharged by absolute convergence in
`Re s > 1`. -/
theorem lemma6_equation16_at_alpha
    {q x H : ℕ} [NeZero q] (hx : 2 ≤ x)
    (ν : ℝ) (χ : DirichletCharacter ℂ q) :
    deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) =
      (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)) *
        (1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
          lemma6MollifierAt H (lemma6AlphaPoint x ν) χ) +
      deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) *
        lemma6MollifierAt H (lemma6AlphaPoint x ν) χ := by
  apply lemma6_logDeriv_mollifier_identity
  have hs := one_lt_lemma6AlphaPoint_re hx ν
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
/-- A character-independent majorant for `L'/L` in the absolutely
convergent half-plane. -/
noncomputable def lemma6LogDerivMajorant (s : ℂ) : ℝ :=
  ∑' n : ℕ,
    ‖LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖
/-- On `Re s > 1`, the logarithmic derivative is bounded termwise by the
untwisted von Mangoldt Dirichlet series.  This isolates the elementary
scalar estimate that supplies Chen's `(log x)^2` loss. -/
theorem lemma6_norm_logDeriv_le_majorant
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ ≤
      lemma6LogDerivMajorant s := by
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let χseq : ℕ → ℂ := fun n => χ n
  let twist : ℕ → ℂ := χseq * Λ
  have htwist : LSeriesSummable twist s := by
    simpa only [twist, χseq, Λ] using
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hΛ : LSeriesSummable Λ s := by
    simpa only [Λ] using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hidentity :
      deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s = -LSeries twist s := by
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs]
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
    change LSeries twist s =
      -deriv (LSeries χseq) s / LSeries χseq s at h
    rw [h]
    ring
  have htwistNorm : Summable (fun n => ‖LSeries.term twist s n‖) := by
    rw [summable_norm_iff]
    exact htwist
  have hΛNorm : Summable (fun n => ‖LSeries.term Λ s n‖) := by
    rw [summable_norm_iff]
    exact hΛ
  have hterm : ∀ n,
      ‖LSeries.term twist s n‖ ≤ ‖LSeries.term Λ s n‖ := by
    intro n
    apply LSeries.norm_term_le
    dsimp only [twist]
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n)
  rw [hidentity, norm_neg, LSeries, lemma6LogDerivMajorant]
  exact (norm_tsum_le_tsum_norm htwistNorm).trans
    (htwistNorm.tsum_le_tsum hterm hΛNorm)
/-- A character-independent absolute-convergence majorant for `L'` on a
vertical line in `Re s > 1`.  The argument is a real number because the
norms of the differentiated Dirichlet-series terms depend only on the real
part of `s`. -/
noncomputable def lemma6LDerivMajorant (sigma : ℝ) : ℝ :=
  ∑' n : ℕ,
    ‖LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) (sigma : ℂ) n‖
/-- In the absolutely convergent half-plane, `L'(s, chi)` is bounded by the
untwisted differentiated Dirichlet series at `Re s`.  In particular this
bound is uniform in the height on every fixed vertical line to the right of
one. -/
theorem lemma6_norm_deriv_LFunction_le_majorant
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (DirichletCharacter.LFunction chi) s‖ ≤
      lemma6LDerivMajorant s.re := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hchiAbs : LSeries.abscissaOfAbsConv (chi ·) < s.re := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one hq0 chi]
    exact_mod_cast hs
  have hchi : LSeriesSummable (LSeries.logMul (chi ·)) s :=
    LSeriesSummable_logMul_of_lt_re hchiAbs
  have hone : LSeriesSummable
      (LSeries.logMul (1 : ℕ → ℂ)) (s.re : ℂ) := by
    apply LSeriesSummable_logMul_of_lt_re
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hs
  have hchiNorm : Summable (fun n : ℕ =>
      ‖LSeries.term (LSeries.logMul (chi ·)) s n‖) := by
    rw [summable_norm_iff]
    exact hchi
  have honeNorm : Summable (fun n : ℕ =>
      ‖LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
        (s.re : ℂ) n‖) := by
    rw [summable_norm_iff]
    exact hone
  have hterm (n : ℕ) :
      ‖LSeries.term (LSeries.logMul (chi ·)) s n‖ ≤
        ‖LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
          (s.re : ℂ) n‖ := by
    calc
      ‖LSeries.term (LSeries.logMul (chi ·)) s n‖ ≤
          ‖LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) s n‖ := by
        apply LSeries.norm_term_le
        simp only [LSeries.logMul, Pi.one_apply, mul_one, norm_mul]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (chi.norm_le_one n) (norm_nonneg _)
      _ = ‖LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
          (s.re : ℂ) n‖ := by
        simp only [LSeries.norm_term_eq, Complex.ofReal_re]
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
    LSeries_deriv hchiAbs, norm_neg, LSeries,
    lemma6LDerivMajorant]
  exact (norm_tsum_le_tsum_norm hchiNorm).trans
    (hchiNorm.tsum_le_tsum hterm honeNorm)
/-- Pointwise `A + B` split in equation (17).  `P` is the prime-pair
Dirichlet polynomial; its precise dyadic support is irrelevant to this
algebraic-norm step. -/
theorem lemma6_pair_mul_logDeriv_norm_le_A_add_B
    {q x H : ℕ} [NeZero q] (hx : 2 ≤ x)
    (ν : ℝ) (χ : DirichletCharacter ℂ q) (P : ℂ) :
    ‖P * (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖ ≤
      ‖P‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)‖ *
          ‖1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
            lemma6MollifierAt H (lemma6AlphaPoint x ν) χ‖ +
        ‖P‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν)‖ *
          ‖lemma6MollifierAt H (lemma6AlphaPoint x ν) χ‖ := by
  let A : ℂ :=
    (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)) *
      (1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
        lemma6MollifierAt H (lemma6AlphaPoint x ν) χ)
  let B : ℂ :=
    deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) *
      lemma6MollifierAt H (lemma6AlphaPoint x ν) χ
  have hid :
      deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) = A + B := by
    simpa only [A, B] using lemma6_equation16_at_alpha hx ν χ
  calc
    ‖P * (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖ =
        ‖P * (A + B)‖ := congrArg (fun z : ℂ => ‖P * z‖) hid
    _ = ‖P * A + P * B‖ := by rw [mul_add]
    _ ≤ ‖P * A‖ + ‖P * B‖ := norm_add_le _ _
    _ = ‖P‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)‖ *
          ‖1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
            lemma6MollifierAt H (lemma6AlphaPoint x ν) χ‖ +
        ‖P‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν)‖ *
          ‖lemma6MollifierAt H (lemma6AlphaPoint x ν) χ‖ := by
      simp only [A, B, norm_mul]
      ring
end Chen

end

/-! ## ChenTheorem.Lemma6.DivisorSquareMean -/

section

/-!
# The divisor-square mean needed in Lemma 6

Chen uses `∑_{n ≤ X} τ(n)² ≪ X (log X)³` immediately before equation (14).
This file isolates that arithmetic input from the character large sieve and
proves its weighted dyadic consequence.
-/

open scoped Classical

namespace Chen

/-- The divisor-square mean estimate used in equation (14).  The separate
arithmetic proof of this proposition is the next elementary input required
by the Lemma 6 argument. -/
def Lemma6DivisorSquareMean : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
    ∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 ≤
      C * (X : ℝ) * (Real.log (X : ℝ)) ^ 3

/-- The divisor-square mean implies the weighted interval estimate that
occurs after applying the large sieve to `C_H(n) / n^ω`. -/
theorem lemma6_divisorSquare_weighted_Ioc_le
    (hmean : Lemma6DivisorSquareMean) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 1 ≤ M → 2 ≤ M + N →
      ∑ n ∈ Finset.Ioc M (M + N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
        C * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 /
          (M : ℝ) ^ 2 := by
  rcases hmean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro M N hM hMN
  let S := Finset.Ioc M (M + N)
  let T := Finset.Icc 1 (M + N)
  have hST : S ⊆ T := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
  have hpoint : ∀ n ∈ S,
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1.le
    have hsq : (M : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMn 2
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hsq
  calc
    ∑ n ∈ S,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
      ∑ n ∈ S,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
      exact Finset.sum_le_sum fun n hn => hpoint n hn
    _ = (∑ n ∈ S, (n.divisorsAntidiagonal.card : ℝ) ^ 2) /
        (M : ℝ) ^ 2 := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ T, (n.divisorsAntidiagonal.card : ℝ) ^ 2) /
        (M : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum_of_subset_of_nonneg hST
        intro n hnT hnS
        positivity
      · positivity
    _ ≤ (C * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3) /
        (M : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right (hmean (M + N) hMN)
      positivity

end Chen

end

/-! ## ChenTheorem.Lemma6.DivisorSquareMeanProof -/

section

/-!
# Proof of the divisor-square mean used in Lemma 6

The proof counts pairs of divisors by their least common multiple, bounds
`⌊X / lcm(d,e)⌋` using `gcd(d,e)`, and evaluates the resulting common-divisor
sum by harmonic sums.
-/

open scoped Classical

namespace Chen

theorem lemma6_card_divisorsAntidiagonal (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors]
  exact Finset.card_map _

theorem lemma6_divisors_eq_Icc_filter {n X : ℕ}
    (hn : n ∈ Finset.Icc 1 X) :
    n.divisors = (Finset.Icc 1 X).filter (fun d => d ∣ n) := by
  have hnrange := Finset.mem_Icc.mp hn
  ext d
  simp only [Finset.mem_filter]
  constructor
  · intro hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hn0 : n ≠ 0 := by omega
    have hdpos := Nat.pos_of_dvd_of_pos hdvd (by omega : 0 < n)
    have hdle := Nat.le_of_dvd (by omega : 0 < n) hdvd
    exact ⟨Finset.mem_Icc.mpr ⟨hdpos, hdle.trans hnrange.2⟩,
      hdvd⟩
  · rintro ⟨hdT, hdvd⟩
    exact Nat.mem_divisors.mpr ⟨hdvd, by omega⟩

theorem lemma6_card_divisors_sq_expand {n X : ℕ}
    (hn : n ∈ Finset.Icc 1 X) :
    (n.divisors.card : ℝ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 X,
        ∑ e ∈ Finset.Icc 1 X,
          if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
  let T := Finset.Icc 1 X
  have hdiv := lemma6_divisors_eq_Icc_filter hn
  calc
    (n.divisors.card : ℝ) ^ 2 =
        (∑ _d ∈ n.divisors, (1 : ℝ)) *
          ∑ _e ∈ n.divisors, (1 : ℝ) := by simp [pow_two]
    _ = ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ) := by
      rw [Finset.sum_mul_sum]
      simp
    _ = ∑ d ∈ T.filter (fun d => d ∣ n),
          ∑ e ∈ T.filter (fun e => e ∣ n), (1 : ℝ) := by rw [hdiv]
    _ = ∑ d ∈ T, ∑ e ∈ T,
          if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdvd : d ∣ n
      · simp [hdvd]
      · simp [hdvd]

theorem lemma6_card_Icc_filter_dvd (X p : ℕ) :
    ((Finset.Icc 1 X).filter (fun n => p ∣ n)).card = X / p := by
  rw [show (Finset.Icc 1 X).filter (fun n => p ∣ n) =
      (Finset.range X.succ).filter (fun n => n ≠ 0 ∧ p ∣ n) by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega]
  exact Nat.card_multiples' X p

theorem lemma6_count_common_multiples (X d e : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        if (d ∣ n ∧ e ∣ n) then (1 : ℝ) else 0) =
      ((X / d.lcm e : ℕ) : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 1 X,
        if (d ∣ n ∧ e ∣ n) then (1 : ℝ) else 0) =
      (((Finset.Icc 1 X).filter
        (fun n => d ∣ n ∧ e ∣ n)).card : ℝ) := by simp
    _ = (((Finset.Icc 1 X).filter
        (fun n => d.lcm e ∣ n)).card : ℝ) := by
      congr 2
      ext n
      simp only [Finset.mem_filter]
      rw [Nat.lcm_dvd_iff]
    _ = ((X / d.lcm e : ℕ) : ℝ) := by
      norm_cast
      exact lemma6_card_Icc_filter_dvd X (d.lcm e)

theorem lemma6_sum_divisor_sq_eq_lcm (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 X,
        ∑ e ∈ Finset.Icc 1 X,
          ((X / d.lcm e : ℕ) : ℝ) := by
  let T := Finset.Icc 1 X
  calc
    (∑ n ∈ T, (n.divisorsAntidiagonal.card : ℝ) ^ 2) =
      ∑ n ∈ T, (n.divisors.card : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [lemma6_card_divisorsAntidiagonal]
    _ = ∑ n ∈ T, ∑ d ∈ T, ∑ e ∈ T,
          if (d ∣ n ∧ e ∣ n) then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        exact lemma6_card_divisors_sq_expand hn
    _ = ∑ d ∈ T, ∑ e ∈ T, ∑ n ∈ T,
          if (d ∣ n ∧ e ∣ n) then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_comm]
    _ = ∑ d ∈ T, ∑ e ∈ T,
          ((X / d.lcm e : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        exact lemma6_count_common_multiples X d e

theorem lemma6_natDiv_lcm_cast_le_gcd
    {X d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    ((X / d.lcm e : ℕ) : ℝ) ≤
      (X : ℝ) * (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  have hlcm : 0 < d.lcm e := Nat.lcm_pos hd he
  calc
    ((X / d.lcm e : ℕ) : ℝ) ≤
        (X : ℝ) / (d.lcm e : ℝ) := Nat.cast_div_le
    _ = (X : ℝ) * (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      have hprod :
          (d.gcd e : ℝ) * (d.lcm e : ℝ) = (d : ℝ) * (e : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d e
      field_simp
      nlinarith

theorem lemma6_sum_inv_multiples (X r : ℕ) (hr : 0 < r) :
    ∑ d ∈ (Finset.Icc 1 X).filter (r ∣ ·), (d : ℝ)⁻¹ =
      (r : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (X / r), (k : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun d _ => d / r) ?_ ?_ ?_ ?_
  · intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdIcc, hrd⟩
    rcases hrd with ⟨k, rfl⟩
    simp only [Finset.mem_Icc] at hdIcc ⊢
    have hkpos : 0 < k := by
      by_contra hk
      simp only [not_lt, nonpos_iff_eq_zero] at hk
      simp [hk] at hdIcc
    rw [Nat.mul_div_cancel_left _ hr]
    constructor
    · exact hkpos
    · exact (Nat.le_div_iff_mul_le hr).2 (by
        simpa [mul_comm] using hdIcc.2)
  · intro d hd e he hde
    rcases (Finset.mem_filter.mp hd).2 with ⟨k, hk⟩
    rcases (Finset.mem_filter.mp he).2 with ⟨l, hl⟩
    subst d
    subst e
    simpa [Nat.mul_div_cancel_left _ hr] using congrArg (r * ·) hde
  · intro k hk
    have hkIcc := Finset.mem_Icc.mp hk
    refine ⟨r * k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero hr.ne' (by omega))
        · simpa [mul_comm] using
            (Nat.le_div_iff_mul_le hr).1 hkIcc.2
      · exact dvd_mul_right r k
    · simp [Nat.mul_div_cancel_left _ hr]
  · intro d hd
    rcases (Finset.mem_filter.mp hd).2 with ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left _ hr]
    rw [Nat.cast_mul, mul_inv]

theorem lemma6_sum_Icc_inv_eq_harmonic (X : ℕ) :
    ∑ k ∈ Finset.Icc 1 X, (k : ℝ)⁻¹ = (harmonic X : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]

theorem lemma6_sum_Icc_inv_le_harmonic {M X : ℕ} (hMX : M ≤ X) :
    ∑ k ∈ Finset.Icc 1 M, (k : ℝ)⁻¹ ≤ (harmonic X : ℝ) := by
  rw [← lemma6_sum_Icc_inv_eq_harmonic X]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_right hMX
  · intro k hkX hkM
    positivity

theorem lemma6_gcd_kernel_le_commonDivisor_sum
    {X d e : ℕ} (hd : d ∈ Finset.Icc 1 X)
    (_he : e ∈ Finset.Icc 1 X) :
    (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) ≤
      ∑ r ∈ Finset.Icc 1 X,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0 := by
  have hdpos := (Finset.mem_Icc.mp hd).1
  have hgpos : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e hdpos
  have hgle : d.gcd e ≤ d :=
    Nat.le_of_dvd hdpos (Nat.gcd_dvd_left d e)
  have hgmem : d.gcd e ∈ Finset.Icc 1 X :=
    Finset.mem_Icc.mpr ⟨hgpos, hgle.trans (Finset.mem_Icc.mp hd).2⟩
  have hsingle := Finset.single_le_sum
    (s := Finset.Icc 1 X)
    (f := fun r => if (r ∣ d ∧ r ∣ e) then
      (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)
    (fun r hr => by split_ifs <;> positivity) hgmem
  simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using hsingle

theorem lemma6_commonDivisor_kernel_eq (X r : ℕ) :
    (∑ d ∈ Finset.Icc 1 X,
      ∑ e ∈ Finset.Icc 1 X,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0) =
      (r : ℝ) *
        (∑ d ∈ (Finset.Icc 1 X).filter (r ∣ ·), (d : ℝ)⁻¹) ^ 2 := by
  let T := Finset.Icc 1 X
  let S := T.filter (r ∣ ·)
  calc
    (∑ d ∈ T, ∑ e ∈ T,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
      ∑ d ∈ S, ∑ e ∈ S,
        (r : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hrd : r ∣ d
      · simp only [hrd, true_and, if_true]
        change (∑ e ∈ T, if r ∣ e then
            (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
          ∑ e ∈ T.filter (r ∣ ·),
            (r : ℝ) / ((d : ℝ) * (e : ℝ))
        rw [Finset.sum_filter]
      · simp [hrd]
    _ = ∑ d ∈ S, ∑ e ∈ S,
        ((r : ℝ) * (d : ℝ)⁻¹) * (e : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      field_simp
    _ = (∑ d ∈ S, (r : ℝ) * (d : ℝ)⁻¹) *
        ∑ e ∈ S, (e : ℝ)⁻¹ := by
      exact (Finset.sum_mul_sum S S
        (fun d => (r : ℝ) * (d : ℝ)⁻¹)
        (fun e => (e : ℝ)⁻¹)).symm
    _ = (r : ℝ) * (∑ d ∈ S, (d : ℝ)⁻¹) *
        ∑ e ∈ S, (e : ℝ)⁻¹ := by
      rw [show (∑ d ∈ S, (r : ℝ) * (d : ℝ)⁻¹) =
          (r : ℝ) * ∑ d ∈ S, (d : ℝ)⁻¹ by
        exact (Finset.mul_sum S (fun d => (d : ℝ)⁻¹) (r : ℝ)).symm]
    _ = (r : ℝ) * (∑ d ∈ S, (d : ℝ)⁻¹) ^ 2 := by ring

theorem lemma6_commonDivisor_kernel_le_harmonic
    {X r : ℕ} (hr : 0 < r) :
    (r : ℝ) *
        (∑ d ∈ (Finset.Icc 1 X).filter (r ∣ ·), (d : ℝ)⁻¹) ^ 2 ≤
      (r : ℝ)⁻¹ * (harmonic X : ℝ) ^ 2 := by
  have hsmall :
      ∑ k ∈ Finset.Icc 1 (X / r), (k : ℝ)⁻¹ ≤
        (harmonic X : ℝ) :=
    lemma6_sum_Icc_inv_le_harmonic (Nat.div_le_self X r)
  have hweighted :
      (r : ℝ)⁻¹ *
          ∑ k ∈ Finset.Icc 1 (X / r), (k : ℝ)⁻¹ ≤
        (r : ℝ)⁻¹ * (harmonic X : ℝ) :=
    mul_le_mul_of_nonneg_left hsmall (by positivity)
  rw [lemma6_sum_inv_multiples X r hr]
  calc
    (r : ℝ) * ((r : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc 1 (X / r), (k : ℝ)⁻¹) ^ 2 ≤
      (r : ℝ) * ((r : ℝ)⁻¹ * (harmonic X : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀ (by positivity) hweighted 2
        · positivity
    _ = (r : ℝ)⁻¹ * (harmonic X : ℝ) ^ 2 := by
      have hr0 : (r : ℝ) ≠ 0 := by positivity
      field_simp

theorem lemma6_gcd_double_sum_le_harmonic_cube (X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X,
      ∑ e ∈ Finset.Icc 1 X,
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) ≤
      (harmonic X : ℝ) ^ 3 := by
  let T := Finset.Icc 1 X
  calc
    (∑ d ∈ T, ∑ e ∈ T,
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) ≤
      ∑ d ∈ T, ∑ e ∈ T, ∑ r ∈ T,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact lemma6_gcd_kernel_le_commonDivisor_sum hd he
    _ = ∑ d ∈ T, ∑ r ∈ T, ∑ e ∈ T,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ r ∈ T, ∑ d ∈ T, ∑ e ∈ T,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ T, (r : ℝ) *
        (∑ d ∈ T.filter (r ∣ ·), (d : ℝ)⁻¹) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact lemma6_commonDivisor_kernel_eq X r
    _ ≤ ∑ r ∈ T, (r : ℝ)⁻¹ * (harmonic X : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact lemma6_commonDivisor_kernel_le_harmonic
        (Finset.mem_Icc.mp hr).1
    _ = (∑ r ∈ T, (r : ℝ)⁻¹) * (harmonic X : ℝ) ^ 2 := by
      rw [Finset.sum_mul]
    _ = (harmonic X : ℝ) ^ 3 := by
      rw [lemma6_sum_Icc_inv_eq_harmonic]
      ring

theorem lemma6_divisorSquare_sum_le_harmonic_cube (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2) ≤
      (X : ℝ) * (harmonic X : ℝ) ^ 3 := by
  let T := Finset.Icc 1 X
  rw [lemma6_sum_divisor_sq_eq_lcm]
  calc
    (∑ d ∈ T, ∑ e ∈ T, ((X / d.lcm e : ℕ) : ℝ)) ≤
      ∑ d ∈ T, ∑ e ∈ T,
        (X : ℝ) * (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact lemma6_natDiv_lcm_cast_le_gcd
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    _ = (X : ℝ) * ∑ d ∈ T, ∑ e ∈ T,
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ ≤ (X : ℝ) * (harmonic X : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (lemma6_gcd_double_sum_le_harmonic_cube X) (by positivity)

theorem lemma6_divisorSquareMean : Lemma6DivisorSquareMean := by
  let C : ℝ := (1 + (Real.log 2)⁻¹) ^ 3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro X hX
  have hXone : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hlogmono : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by positivity))
      (by exact_mod_cast hX)
  have hratio : 1 ≤ Real.log (X : ℝ) / Real.log 2 := by
    exact (le_div_iff₀ hlog2).2 (by simpa using hlogmono)
  have hinv : 1 ≤ (Real.log 2)⁻¹ * Real.log (X : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using hratio
  have hbase :
      1 + Real.log (X : ℝ) ≤
        (1 + (Real.log 2)⁻¹) * Real.log (X : ℝ) := by
    calc
      1 + Real.log (X : ℝ) ≤
          (Real.log 2)⁻¹ * Real.log (X : ℝ) +
            Real.log (X : ℝ) := by linarith
      _ = (1 + (Real.log 2)⁻¹) * Real.log (X : ℝ) := by ring
  have hHnonneg : 0 ≤ (harmonic X : ℝ) := by
    rw [← lemma6_sum_Icc_inv_eq_harmonic]
    positivity
  have hHpow :
      (harmonic X : ℝ) ^ 3 ≤
        ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 3 := by
    calc
      (harmonic X : ℝ) ^ 3 ≤
          (1 + Real.log (X : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hHnonneg (harmonic_le_one_add_log X) 3
      _ ≤ ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hbase 3
  calc
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2) ≤
      (X : ℝ) * (harmonic X : ℝ) ^ 3 :=
        lemma6_divisorSquare_sum_le_harmonic_cube X
    _ ≤ (X : ℝ) *
        ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 3 :=
      mul_le_mul_of_nonneg_left hHpow (by positivity)
    _ = C * (X : ℝ) * (Real.log (X : ℝ)) ^ 3 := by
      dsimp only [C]
      ring

end Chen

end

/-! ## ChenTheorem.Lemma6.DivisorSquareWeighted -/

section

/-!
# Weighted divisor-square mean for Lemma 6

The identity for common multiples is weighted by `1 / n`, producing one
additional harmonic factor and hence the `(log X)^4` bound used in equation
(15).
-/

open scoped Classical

namespace Chen

theorem lemma6_common_multiples_inv
    {X d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (∑ n ∈ Finset.Icc 1 X,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0) =
      (d.lcm e : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc 1 (X / d.lcm e), (k : ℝ)⁻¹ := by
  have hlcm : 0 < d.lcm e := Nat.lcm_pos hd he
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 1 X).filter (fun n => d ∣ n ∧ e ∣ n) =
        (Finset.Icc 1 X).filter (fun n => d.lcm e ∣ n) := by
    ext n
    simp only [Finset.mem_filter]
    rw [Nat.lcm_dvd_iff]
  rw [hfilter]
  exact lemma6_sum_inv_multiples X (d.lcm e) hlcm

theorem lemma6_common_multiples_inv_le
    {X d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (∑ n ∈ Finset.Icc 1 X,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0) ≤
      ((d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) *
        (harmonic X : ℝ) := by
  rw [lemma6_common_multiples_inv hd he]
  have hsmall :
      ∑ k ∈ Finset.Icc 1 (X / d.lcm e), (k : ℝ)⁻¹ ≤
        (harmonic X : ℝ) :=
    lemma6_sum_Icc_inv_le_harmonic (Nat.div_le_self X (d.lcm e))
  calc
    (d.lcm e : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc 1 (X / d.lcm e), (k : ℝ)⁻¹ ≤
      (d.lcm e : ℝ)⁻¹ * (harmonic X : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = ((d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) *
        (harmonic X : ℝ) := by
      have hprod :
          (d.gcd e : ℝ) * (d.lcm e : ℝ) = (d : ℝ) * (e : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d e
      have hlcm0 : (d.lcm e : ℝ) ≠ 0 := by positivity
      have hgcd0 : (d.gcd e : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.gcd_pos_of_pos_left e hd).ne'
      rw [← hprod]
      field_simp

theorem lemma6_card_divisors_sq_div_expand {n X : ℕ}
    (hn : n ∈ Finset.Icc 1 X) :
    (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 X,
        ∑ e ∈ Finset.Icc 1 X,
          if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
  rw [lemma6_card_divisorsAntidiagonal,
    lemma6_card_divisors_sq_expand hn]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp [div_eq_mul_inv]

theorem lemma6_divisorSquare_over_n_eq_commonMultiples (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) =
      ∑ d ∈ Finset.Icc 1 X,
        ∑ e ∈ Finset.Icc 1 X,
          ∑ n ∈ Finset.Icc 1 X,
            if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
  let T := Finset.Icc 1 X
  calc
    (∑ n ∈ T,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) =
      ∑ n ∈ T, ∑ d ∈ T, ∑ e ∈ T,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact lemma6_card_divisors_sq_div_expand hn
    _ = ∑ d ∈ T, ∑ n ∈ T, ∑ e ∈ T,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ T, ∑ e ∈ T, ∑ n ∈ T,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]

theorem lemma6_divisorSquare_over_n_le_harmonic_fourth (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) ≤
      (harmonic X : ℝ) ^ 4 := by
  let T := Finset.Icc 1 X
  rw [lemma6_divisorSquare_over_n_eq_commonMultiples]
  have hHnonneg : 0 ≤ (harmonic X : ℝ) := by
    rw [← lemma6_sum_Icc_inv_eq_harmonic]
    positivity
  calc
    (∑ d ∈ T, ∑ e ∈ T, ∑ n ∈ T,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0) ≤
      ∑ d ∈ T, ∑ e ∈ T,
        ((d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) *
          (harmonic X : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact lemma6_common_multiples_inv_le
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    _ = (∑ d ∈ T, ∑ e ∈ T,
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) *
          (harmonic X : ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]
    _ ≤ (harmonic X : ℝ) ^ 3 * (harmonic X : ℝ) :=
      mul_le_mul_of_nonneg_right
        (lemma6_gcd_double_sum_le_harmonic_cube X) hHnonneg
    _ = (harmonic X : ℝ) ^ 4 := by ring

theorem lemma6_divisorSquare_over_n_le_log_four :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X,
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) ≤
        C * (Real.log (X : ℝ)) ^ 4 := by
  let C : ℝ := (1 + (Real.log 2)⁻¹) ^ 4
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro X hX
  have hXone : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hlogmono : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by positivity))
      (by exact_mod_cast hX)
  have hratio : 1 ≤ Real.log (X : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlogmono)
  have hinv : 1 ≤ (Real.log 2)⁻¹ * Real.log (X : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using hratio
  have hbase :
      1 + Real.log (X : ℝ) ≤
        (1 + (Real.log 2)⁻¹) * Real.log (X : ℝ) := by
    calc
      1 + Real.log (X : ℝ) ≤
          (Real.log 2)⁻¹ * Real.log (X : ℝ) +
            Real.log (X : ℝ) := by linarith
      _ = (1 + (Real.log 2)⁻¹) * Real.log (X : ℝ) := by ring
  have hHnonneg : 0 ≤ (harmonic X : ℝ) := by
    rw [← lemma6_sum_Icc_inv_eq_harmonic]
    positivity
  have hHpow :
      (harmonic X : ℝ) ^ 4 ≤
        ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 4 := by
    calc
      (harmonic X : ℝ) ^ 4 ≤
          (1 + Real.log (X : ℝ)) ^ 4 :=
        pow_le_pow_left₀ hHnonneg (harmonic_le_one_add_log X) 4
      _ ≤ ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase 4
  calc
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) ≤
      (harmonic X : ℝ) ^ 4 :=
        lemma6_divisorSquare_over_n_le_harmonic_fourth X
    _ ≤ ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 4 := hHpow
    _ = C * (Real.log (X : ℝ)) ^ 4 := by
      dsimp only [C]
      ring

end Chen

end

/-! ## ChenTheorem.Lemma3.Polynomial -/

section

/-
The finite Dirichlet-polynomial part of Chen's Lemma 3.

Squaring the truncation of `L(s, chi)` and grouping by `n = a*b` gives a
polynomial of length `N^2`.  Its coefficient is bounded by the divisor
function, so the character large sieve and the weighted divisor-square
estimate give the fourth-moment bound used in the printed proof.
-/

open scoped Classical

namespace Chen

/-- The coefficient `n^{-s}` in the ordinary Dirichlet polynomial.
Kept local to Lemma 3 so that Lemma 6 can depend on the completed result
without creating a circular import. -/
noncomputable def lemma3Phase (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ s)⁻¹

theorem lemma3Phase_norm_sq_le
    {s : ℂ} {n : ℕ} (hn : 1 ≤ n) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖lemma3Phase s n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
  have hnpos : 0 < n := by omega
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(s.re * 2) ≤ (-1 : ℝ) := by linarith
  rw [lemma3Phase, norm_inv, Complex.norm_natCast_cpow_of_pos hnpos]
  calc
    ((n : ℝ) ^ s.re)⁻¹ ^ 2 = (((n : ℝ) ^ s.re) ^ 2)⁻¹ :=
      inv_pow _ _
    _ = ((n : ℝ) ^ (s.re * 2))⁻¹ := by
      rw [Real.rpow_mul hnnonneg]
      norm_num
    _ = (n : ℝ) ^ (-(s.re * 2)) := by
      rw [Real.rpow_neg hnnonneg]
    _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnone hexp
    _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _

/-- The ordinary finite Dirichlet polynomial used in Lemma 3. -/
noncomputable def lemma3TruncatedL
    {q : ℕ} (N : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, lemma3Phase s n * χ n

/-- Number of factor pairs `a*b=n` with both factors at most `N`. -/
noncomputable def lemma3SquareCoeff (N n : ℕ) : ℕ :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun p => p.1 * p.2 = n)).card

theorem lemma3SquareCoeff_le_divisorsAntidiagonal_card (N n : ℕ) :
    lemma3SquareCoeff N n ≤ n.divisorsAntidiagonal.card := by
  unfold lemma3SquareCoeff
  rw [lemma6MollifierFiber_eq]
  exact Finset.card_filter_le _ _

/-- Exact regrouping of the square of the truncated Dirichlet polynomial. -/
theorem lemma3TruncatedL_sq
    {q : ℕ} (N : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma3TruncatedL N s χ ^ 2 =
      ∑ n ∈ Finset.Icc 1 (N * N),
        ((lemma3SquareCoeff N n : ℂ) * lemma3Phase s n) * χ n := by
  let S := Finset.Icc 1 N
  let P := S ×ˢ S
  let T := Finset.Icc 1 (N * N)
  have hprod_mem (p : ℕ × ℕ) (hp : p ∈ P) : p.1 * p.2 ∈ T := by
    have hpmem := Finset.mem_product.mp hp
    have hp1 := Finset.mem_Icc.mp hpmem.1
    have hp2 := Finset.mem_Icc.mp hpmem.2
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hp1.1 hp2.1, Nat.mul_le_mul hp1.2 hp2.2⟩
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P T
    (fun p : ℕ × ℕ => p.1 * p.2)
    (fun p => lemma3Phase s (p.1 * p.2) * χ (p.1 * p.2))
  rw [Finset.filter_eq_self.mpr hprod_mem] at hfiber
  unfold lemma3TruncatedL
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
  calc
    (∑ p ∈ P,
        (lemma3Phase s p.1 * χ p.1) *
          (lemma3Phase s p.2 * χ p.2)) =
      ∑ p ∈ P,
        lemma3Phase s (p.1 * p.2) * χ (p.1 * p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpmem := Finset.mem_product.mp hp
      have hp1 := (Finset.mem_Icc.mp hpmem.1).1
      have hp2 := (Finset.mem_Icc.mp hpmem.2).1
      have hphase : lemma3Phase s (p.1 * p.2) =
          lemma3Phase s p.1 * lemma3Phase s p.2 := by
        unfold lemma3Phase
        have hpow : ((p.1 * p.2 : ℕ) : ℂ) ^ s =
            (p.1 : ℂ) ^ s * (p.2 : ℂ) ^ s := by
          simpa only [Nat.cast_mul] using
            Complex.natCast_mul_natCast_cpow p.1 p.2 s
        rw [hpow, mul_inv]
      have hchar : χ (p.1 * p.2) = χ p.1 * χ p.2 := by
        rw [map_mul]
      rw [hphase, hchar]
      ring
    _ = ∑ n ∈ T,
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          lemma3Phase s (p.1 * p.2) * χ (p.1 * p.2) :=
      hfiber.symm
    _ = ∑ n ∈ T,
        ((lemma3SquareCoeff N n : ℂ) * lemma3Phase s n) * χ n := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
            lemma3Phase s (p.1 * p.2) * χ (p.1 * p.2) =
          ∑ _p ∈ P.filter (fun p => p.1 * p.2 = n),
            lemma3Phase s n * χ n := by
          apply Finset.sum_congr rfl
          intro p hp
          have heq := (Finset.mem_filter.mp hp).2
          have hchar : χ (p.1 * p.2) = χ n := by
            congr 1
            rw [← Nat.cast_mul, heq]
          rw [heq, hchar]
        _ = ((lemma3SquareCoeff N n : ℂ) *
            lemma3Phase s n) * χ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
          unfold lemma3SquareCoeff
          ring

/-- Pointwise square-coefficient estimate at `Re s >= 1/2`. -/
theorem lemma3SquareCoeff_weighted_norm_sq_le
    {N n : ℕ} {s : ℂ} (hn : 1 ≤ n) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖(lemma3SquareCoeff N n : ℂ) * lemma3Phase s n‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
  have hcoeff : ‖(lemma3SquareCoeff N n : ℂ)‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 := by
    rw [Complex.norm_natCast]
    exact pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast lemma3SquareCoeff_le_divisorsAntidiagonal_card N n) 2
  rw [norm_mul, mul_pow]
  calc
    ‖(lemma3SquareCoeff N n : ℂ)‖ ^ 2 *
        ‖lemma3Phase s n‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 * (n : ℝ)⁻¹ :=
        mul_le_mul hcoeff (lemma3Phase_norm_sq_le hn hs)
          (sq_nonneg _) (by positivity)
    _ = (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
      rw [div_eq_mul_inv]

/-- The raw large-sieve estimate for the fourth moment of the truncation. -/
theorem lemma3_truncated_fourth_moment_raw
    (Q N : ℕ) (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) ≤
      ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N * N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
  let a : ℕ → ℂ := fun n =>
    (lemma3SquareCoeff N n : ℂ) * lemma3Phase s n
  have hinterval : Finset.Ioc 0 (N * N) = Finset.Icc 1 (N * N) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsieve := LargeSieve.large_sieve_character Q 0 (N * N) a
  simp only [zero_add, hinterval] at hsieve
  calc
    ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) =
      ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (N * N), a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, a]
        rw [← lemma3TruncatedL_sq]
        rw [norm_pow]
        ring
      · simp [hp]
    _ ≤ ∑ q ∈ Finset.Icc 2 Q, (q : ℝ) / (q.totient : ℝ) *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (N * N), a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq2 := (Finset.mem_Icc.mp hq).1
      have htotpos : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
      have hweight : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
        (le_div_iff₀ htotpos).2 (by
          simpa using (show (q.totient : ℝ) ≤ q by
            exact_mod_cast Nat.totient_le q))
      have hsum : 0 ≤ ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 (N * N), a n * χ n‖ ^ 2 else 0 := by
        positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight hsum
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (q.totient : ℝ) *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (N * N), a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        rcases Finset.mem_Icc.mp hq with ⟨hq2, hqQ⟩
        exact Finset.mem_Icc.mpr ⟨(by omega : 1 ≤ q), hqQ⟩
      · intro q hq hnot
        positivity
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N * N), ‖a n‖ ^ 2 := hsieve
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N * N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
      gcongr with n hn
      exact lemma3SquareCoeff_weighted_norm_sq_le
        (Finset.mem_Icc.mp hn).1 hs

/-- Logarithmic form of the truncated fourth moment. -/
theorem lemma3_truncated_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q N : ℕ) (s : ℂ), 2 ≤ N →
      (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 2 Q,
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) ≤
        C * ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) *
          (Real.log ((N * N : ℕ) : ℝ)) ^ 4 := by
  rcases lemma6_divisorSquare_over_n_le_log_four with ⟨C₀, hC₀, hdiv⟩
  refine ⟨(1 + Real.pi) * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro Q N s hN hs
  have hNN : 2 ≤ N * N := by nlinarith
  calc
    ∑ q ∈ Finset.Icc 2 Q,
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖lemma3TruncatedL N s χ‖ ^ 4 else 0) ≤
      ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N * N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) :=
        lemma3_truncated_fourth_moment_raw Q N s hs
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
        (C₀ * (Real.log ((N * N : ℕ) : ℝ)) ^ 4) := by
      gcongr
      exact hdiv (N * N) hNN
    _ ≤ (1 + Real.pi) * C₀ *
        ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) *
          (Real.log ((N * N : ℕ) : ℝ)) ^ 4 := by
      have hQ : 0 ≤ (Q : ℝ) ^ 2 := by positivity
      have hNN0 : 0 ≤ ((N * N : ℕ) : ℝ) := by positivity
      have hpi : 0 ≤ Real.pi := Real.pi_pos.le
      have hbase : (Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ) ≤
          (1 + Real.pi) * ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) := by
        nlinarith [mul_nonneg hpi hQ]
      have hfactor : 0 ≤ C₀ *
          (Real.log ((N * N : ℕ) : ℝ)) ^ 4 := by positivity
      calc
        ((Q : ℝ) ^ 2 + Real.pi * (N * N : ℕ)) *
            (C₀ * (Real.log ((N * N : ℕ) : ℝ)) ^ 4) ≤
          ((1 + Real.pi) * ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ))) *
            (C₀ * (Real.log ((N * N : ℕ) : ℝ)) ^ 4) :=
              mul_le_mul_of_nonneg_right hbase hfactor
        _ = (1 + Real.pi) * C₀ *
            ((Q : ℝ) ^ 2 + ((N * N : ℕ) : ℝ)) *
              (Real.log ((N * N : ℕ) : ℝ)) ^ 4 := by ring

end Chen

end

/-! ## ChenTheorem.Lemma6.LogDerivBound -/

section

/-
The elementary logarithmic-derivative bound suppressed between equations
(16) and (17) in Chen's proof of Lemma 6.

For `Re s = 1 + δ`, the untwisted von Mangoldt series majorizing `L'/L`
is at most `4 / δ²`.  The proof uses `Λ(n) ≤ log n`, the inequality
`log n ≤ n^(δ/2)/(δ/2)`, and the integral test for the remaining p-series.
-/
open Real Set MeasureTheory
open scoped Classical

namespace Chen
set_option maxHeartbeats 800000 in
/-- If `Re s = 1 + δ`, the von Mangoldt majorant is `O(δ⁻²)`. -/
theorem lemma6LogDerivMajorant_le
    {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsre : s.re = 1 + δ) :
    lemma6LogDerivMajorant s ≤ 4 / δ ^ 2 := by
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let a : ℝ := δ / 2
  let p : ℝ := 1 + δ / 2
  have hone : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
  have ha : 0 < a := by dsimp only [a]; linarith
  have hp : 1 < p := by dsimp only [p]; linarith
  have hs : 1 < s.re := by rw [hsre]; linarith
  have hΛ : LSeriesSummable Λ s := by
    simpa only [Λ] using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hΛnorm : Summable (fun n => ‖LSeries.term Λ s n‖) := by
    rw [summable_norm_iff]
    exact hΛ
  have hsplit := hΛnorm.sum_add_tsum_nat_add 2
  have hmajorEq : lemma6LogDerivMajorant s =
      ∑' n : ℕ, ‖LSeries.term Λ s (n + 2)‖ := by
    unfold lemma6LogDerivMajorant
    change (∑' n : ℕ, ‖LSeries.term Λ s n‖) = _
    rw [← hsplit]
    norm_num [Finset.sum_range_succ, Λ, LSeries.norm_term_eq,
      ArithmeticFunction.vonMangoldt_apply]
  have hlog (n : ℕ) (hn : 2 ≤ n) :
      Real.log (n : ℝ) ≤ (n : ℝ) ^ a / a := by
    have hnpos : 0 < (n : ℝ) := by positivity
    have hpowpos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos _
    have hbasic := Real.log_le_sub_one_of_pos hpowpos
    rw [Real.log_rpow hnpos] at hbasic
    rw [le_div_iff₀ ha]
    nlinarith
  have hterm (n : ℕ) :
      ‖LSeries.term Λ s (n + 2)‖ ≤
        (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p) := by
    have hn : 2 ≤ n + 2 := by omega
    have hn0 : n + 2 ≠ 0 := by omega
    have hnpos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [LSeries.norm_term_eq]
    simp only [hn0, if_false]
    have hΛlog : ‖Λ (n + 2)‖ ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
      simpa only [Λ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
          (ArithmeticFunction.vonMangoldt_le_log (n := n + 2))
    calc
      ‖Λ (n + 2)‖ / ((n + 2 : ℕ) : ℝ) ^ s.re ≤
          Real.log ((n + 2 : ℕ) : ℝ) /
            ((n + 2 : ℕ) : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right hΛlog (Real.rpow_pos_of_pos hnpos _).le
      _ ≤ ((((n + 2 : ℕ) : ℝ) ^ a) / a) /
            ((n + 2 : ℕ) : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right (hlog (n + 2) hn)
          (Real.rpow_pos_of_pos hnpos _).le
      _ = (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p) := by
        calc
          ((((n + 2 : ℕ) : ℝ) ^ a) / a) /
              ((n + 2 : ℕ) : ℝ) ^ s.re =
            (1 / a) * ((((n + 2 : ℕ) : ℝ) ^ a) /
              ((n + 2 : ℕ) : ℝ) ^ s.re) := by ring
          _ = (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (a - s.re) := by
            rw [Real.rpow_sub hnpos]
          _ = (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p) := by
            rw [hsre]
            dsimp only [a, p]
            ring_nf
  have hpowSummable :
      Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-p)) := by
    exact (summable_nat_add_iff 2).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have hscaledSummable :
      Summable (fun n : ℕ => (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p)) :=
    hpowSummable.mul_left _
  have hcompare :
      (∑' n : ℕ, ‖LSeries.term Λ s (n + 2)‖) ≤
        ∑' n : ℕ, (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p) := by
    have htailNorm :
        Summable (fun n : ℕ => ‖LSeries.term Λ s (n + 2)‖) :=
      (summable_nat_add_iff 2).mpr hΛnorm
    exact htailNorm.tsum_le_tsum hterm hscaledSummable
  let f : ℝ → ℝ := fun t => t ^ (-p)
  have hanti : AntitoneOn f (Set.Ici ((1 : ℕ) : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show -p ≤ 0 by linarith)).mono
    intro t ht
    change 0 < t
    rw [Set.mem_Ici] at ht
    exact hone.trans_le ht
  have hint : IntegrableOn f (Set.Ioi ((1 : ℕ) : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hone
  have hnonneg : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ f t := by
    intro t ht
    rw [Set.mem_Ioi] at ht
    exact Real.rpow_nonneg (hone.trans ht).le _
  have htail := AntitoneOn.tsum_comp_add_le_integral
    (f := f) (1 : ℕ) hanti hint hnonneg
  have hintegral :
      (∫ t in Set.Ioi ((1 : ℕ) : ℝ), f t) = 1 / (p - 1) := by
    dsimp only [f]
    rw [integral_Ioi_rpow_of_lt (by linarith) hone]
    norm_num only [Nat.cast_one, one_rpow]
    field_simp
    ring
  have htail' :
      (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-p)) ≤ 1 / (p - 1) := by
    rw [hintegral] at htail
    have hadd :
        (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-p)) =
          (fun n : ℕ => f ((n + 1 + 1 : ℕ) : ℝ)) := by
      funext n
      dsimp only [f]
    rw [hadd]
    exact htail
  rw [hmajorEq]
  apply hcompare.trans
  rw [tsum_mul_left]
  calc
    (1 / a) * (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-p)) ≤
        (1 / a) * (1 / (p - 1)) := by
      gcongr
    _ = 4 / δ ^ 2 := by
      dsimp only [a, p]
      field_simp [hδ.ne']
      ring
/-- On Chen's line `α = 1 + 1/log x`, the majorant costs at most
`4 (log x)²`. -/
theorem lemma6LogDerivMajorant_alpha_le
    {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    lemma6LogDerivMajorant (lemma6AlphaPoint x ν) ≤
      4 * Real.log (x : ℝ) ^ 2 := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hδ : 0 < (1 : ℝ) / Real.log (x : ℝ) :=
    div_pos zero_lt_one hlog
  calc
    lemma6LogDerivMajorant (lemma6AlphaPoint x ν) ≤
        4 / ((1 : ℝ) / Real.log (x : ℝ)) ^ 2 :=
      lemma6LogDerivMajorant_le hδ (lemma6AlphaPoint_re x ν)
    _ = 4 * Real.log (x : ℝ) ^ 2 := by
      field_simp [hlog.ne']
end Chen

end

/-! ## ChenTheorem.Lemma6.MollifierSquare -/

section

/-!
# The square of Chen's truncated Möbius polynomial

These are the coefficients `j(n)` in equation (15), where
`S(H,s,χ)^2 = ∑ j(n)χ(n)n⁻ˢ`.
-/

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- The coefficient of `a(n)` in the square of the truncated Möbius
polynomial. -/
noncomputable def lemma6MollifierSquareCoeff (H n : ℕ) : ℤ :=
  ∑ p ∈ n.divisorsAntidiagonal,
    if p.1 ≤ H ∧ p.2 ≤ H then
      ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2
    else 0

/-- The square coefficient has support in `n ≤ H²`. -/
theorem lemma6MollifierSquareCoeff_eq_zero_of_sq_lt
    {H n : ℕ} (h : H * H < n) :
    lemma6MollifierSquareCoeff H n = 0 := by
  unfold lemma6MollifierSquareCoeff
  apply Finset.sum_eq_zero
  intro p hp
  rw [if_neg]
  intro hboth
  have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
  have hmul : p.1 * p.2 ≤ H * H :=
    Nat.mul_le_mul hboth.1 hboth.2
  omega

/-- The paper's coefficient estimate `|j(n)| ≤ τ(n)`. -/
theorem abs_lemma6MollifierSquareCoeff_le_card (H n : ℕ) :
    |lemma6MollifierSquareCoeff H n| ≤
      (n.divisorsAntidiagonal.card : ℤ) := by
  let f : ℕ × ℕ → ℤ := fun p =>
    if p.1 ≤ H ∧ p.2 ≤ H then
      ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2
    else 0
  calc
    |lemma6MollifierSquareCoeff H n| =
        |∑ p ∈ n.divisorsAntidiagonal, f p| := by
      rfl
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, |f p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp only [f]
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul ArithmeticFunction.abs_moebius_le_one
          ArithmeticFunction.abs_moebius_le_one (abs_nonneg _) (by norm_num)
      · simp
    _ = (n.divisorsAntidiagonal.card : ℤ) := by simp

/-- Fibre form of the square coefficient. -/
theorem lemma6MollifierSquareCoeff_eq_fiber (H n : ℕ) :
    lemma6MollifierSquareCoeff H n =
      ∑ p ∈ (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
          (fun p => p.1 * p.2 = n),
        ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2 := by
  unfold lemma6MollifierSquareCoeff
  rw [← Finset.sum_filter]
  rw [← lemma6MollifierFiber_eq]

/-- Exact finite form of `S(H,a)^2 = ∑_{n≤H²} j_H(n)a(n)`. -/
theorem lemma6_mollifierPolynomial_sq
    {R : Type*} [CommRing R] (H : ℕ) (a : ℕ → R)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → a (m * n) = a m * a n) :
    lemma6MollifierPolynomial H a ^ 2 =
      ∑ n ∈ Finset.Icc 1 (H * H),
        (lemma6MollifierSquareCoeff H n : R) * a n := by
  let S := Finset.Icc 1 H
  let P := S ×ˢ S
  let N := Finset.Icc 1 (H * H)
  have hprod_mem (p : ℕ × ℕ) (hp : p ∈ P) : p.1 * p.2 ∈ N := by
    have hpmem := Finset.mem_product.mp hp
    have hp1 := Finset.mem_Icc.mp hpmem.1
    have hp2 := Finset.mem_Icc.mp hpmem.2
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hp1.1 hp2.1, Nat.mul_le_mul hp1.2 hp2.2⟩
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P N
    (fun p : ℕ × ℕ => p.1 * p.2)
    (fun p => ((ArithmeticFunction.moebius p.1 : ℤ) : R) *
      (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2))
  rw [Finset.filter_eq_self.mpr hprod_mem] at hfiber
  unfold lemma6MollifierPolynomial
  rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
  calc
    (∑ p ∈ P,
        ((ArithmeticFunction.moebius p.1 : R) * a p.1) *
          ((ArithmeticFunction.moebius p.2 : R) * a p.2)) =
      ∑ p ∈ P,
        (ArithmeticFunction.moebius p.1 : R) *
          (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpmem := Finset.mem_product.mp hp
      have hp1 := (Finset.mem_Icc.mp hpmem.1).1
      have hp2 := (Finset.mem_Icc.mp hpmem.2).1
      rw [hmul p.1 p.2 hp1 hp2]
      ring
    _ = ∑ n ∈ N,
        ∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.1 : R) *
            (ArithmeticFunction.moebius p.2 : R) * a (p.1 * p.2) :=
      hfiber.symm
    _ = ∑ n ∈ N,
        (∑ p ∈ P.filter (fun p => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.1 : R) *
            (ArithmeticFunction.moebius p.2 : R)) * a n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ n ∈ N,
        (lemma6MollifierSquareCoeff H n : R) * a n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [lemma6MollifierSquareCoeff_eq_fiber]
      push_cast
      rfl

end Chen

end

/-! ## ChenTheorem.Lemma6.MollifierLargeSieve -/

section

/-!
# The `C_H` polynomial and the dyadic character large sieve

This file packages the exact large-sieve step used in equation (14) of
Chen's proof.  A complex phase of norm at most one represents the factor
`n⁻ⁱᵗ`; the remaining `1 / n` supplies the real part `Re ω ≥ 1`.
-/

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- Complex norm form of `|j_H(n)| ≤ τ(n)`. -/
theorem norm_lemma6MollifierSquareCoeff_le_card (H n : ℕ) :
    ‖(lemma6MollifierSquareCoeff H n : ℂ)‖ ≤
      (n.divisorsAntidiagonal.card : ℝ) := by
  rw [Complex.norm_intCast]
  exact_mod_cast abs_lemma6MollifierSquareCoeff_le_card H n

/-- Pointwise coefficient estimate at `Re s ≥ 1/2` for equation (15). -/
theorem lemma6_mollifierSquare_weighted_coeff_norm_sq_le
    {H n : ℕ} (u : ℕ → ℂ)
    (hu : ‖u n‖ ^ 2 ≤ (n : ℝ)⁻¹) :
    ‖(lemma6MollifierSquareCoeff H n : ℂ) * u n‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
  have hcoeff :
      ‖(lemma6MollifierSquareCoeff H n : ℂ)‖ ^ 2 ≤
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
      (norm_lemma6MollifierSquareCoeff_le_card H n)
  rw [norm_mul, mul_pow]
  calc
    ‖(lemma6MollifierSquareCoeff H n : ℂ)‖ ^ 2 * ‖u n‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 * (n : ℝ)⁻¹ :=
        mul_le_mul hcoeff hu (sq_nonneg _) (by positivity)
    _ = (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
      rw [div_eq_mul_inv]

/-- The raw character-large-sieve estimate for `S(H,s,χ)^2`. -/
theorem lemma6_mollifierSquare_large_sieve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q →
        (∀ n ∈ Finset.Icc 1 (H * H), ‖u n‖ ^ 2 ≤ (n : ℝ)⁻¹) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Icc 1 (H * H),
                ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Icc 1 (H * H),
              (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q H u hD hDQ hu
  let a : ℕ → ℂ := fun n => (lemma6MollifierSquareCoeff H n : ℂ) * u n
  have hinterval :
      Finset.Ioc 0 (H * H) = Finset.Icc 1 (H * H) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsieve := hlarge D Q 0 (H * H) a hD hDQ
  simp only [zero_add, hinterval, a] at hsieve
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (H * H),
            ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
          else 0) ≤
      C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Icc 1 (H * H),
          ‖(lemma6MollifierSquareCoeff H n : ℂ) * u n‖ ^ 2 := hsieve
    _ ≤ C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Icc 1 (H * H),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro n hn
        exact lemma6_mollifierSquare_weighted_coeff_norm_sq_le u (hu n hn)
      · positivity

/-- Equation (15): the fourth moment of the truncated Möbius polynomial,
after expanding its square and applying the dyadic character large sieve. -/
theorem lemma6_mollifierSquare_fourthMoment :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 2 ≤ H →
        (∀ n ∈ Finset.Icc 1 (H * H), ‖u n‖ ^ 2 ≤ (n : ℝ)⁻¹) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Icc 1 (H * H),
                ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
            (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by
  rcases lemma6_mollifierSquare_large_sieve with ⟨A, hA, hlarge⟩
  rcases lemma6_divisorSquare_over_n_le_log_four with ⟨B, hB, hdivisor⟩
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro D Q H u hD hDQ hH hu
  have hHH : 2 ≤ H * H := by nlinarith
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (H * H),
            ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
          else 0) ≤
      A * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Icc 1 (H * H),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) :=
      hlarge D Q H u hD hDQ hu
    _ ≤ A * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        (B * (Real.log ((H * H : ℕ) : ℝ)) ^ 4) := by
      apply mul_le_mul_of_nonneg_left (hdivisor (H * H) hHH)
      positivity
    _ = (A * B) *
        ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by ring

/-- The complex norm of `C_H(n)` is bounded by the cardinality form of
`τ(n)` for `n ≠ 1`. -/
theorem norm_lemma6MollifierCoeff_le_card
    {H n : ℕ} (hn : n ≠ 1) :
    ‖(lemma6MollifierCoeff H n : ℂ)‖ ≤
      (n.divisorsAntidiagonal.card : ℝ) := by
  rw [Complex.norm_intCast]
  exact_mod_cast abs_lemma6MollifierCoeff_le_card (H := H) hn

/-- Pointwise square-norm estimate for the coefficients to which the large
sieve is applied in equation (14). -/
theorem lemma6_weighted_mollifierCoeff_norm_sq_le
    {H M N n : ℕ} (hM : 1 ≤ M) (hn : n ∈ Finset.Ioc M (M + N))
    (u : ℕ → ℂ) (hu : ‖u n‖ ≤ 1) :
    ‖(lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  have hnrange := Finset.mem_Ioc.mp hn
  have hn1 : n ≠ 1 := by omega
  have hnposNat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hnum :
      ‖(lemma6MollifierCoeff H n : ℂ)‖ * ‖u n‖ ≤
        (n.divisorsAntidiagonal.card : ℝ) := by
    calc
      ‖(lemma6MollifierCoeff H n : ℂ)‖ * ‖u n‖ ≤
          ‖(lemma6MollifierCoeff H n : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hu (norm_nonneg _)
      _ = ‖(lemma6MollifierCoeff H n : ℂ)‖ := by ring
      _ ≤ (n.divisorsAntidiagonal.card : ℝ) :=
        norm_lemma6MollifierCoeff_le_card hn1
  have hquot :
      ‖(lemma6MollifierCoeff H n : ℂ)‖ * ‖u n‖ / (n : ℝ) ≤
        (n.divisorsAntidiagonal.card : ℝ) / (n : ℝ) :=
    div_le_div_of_nonneg_right hnum hnpos.le
  rw [norm_div, norm_mul, Complex.norm_natCast, ← div_pow]
  exact (sq_le_sq₀ (by positivity) (by positivity)).2 hquot

/-- Equation (14)'s character-large-sieve input for a dyadic interval.

The phase `u` may depend on the spectral parameter and only needs norm at
most one.  The conclusion is deliberately left in terms of the finite
`τ(n)² / n²` sum; the elementary divisor-sum estimate is a separate step. -/
theorem lemma6_mollifier_large_sieve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ M →
        (∀ n ∈ Finset.Ioc M (M + N), ‖u n‖ ≤ 1) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Ioc M (M + N),
                ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Ioc M (M + N),
              (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N H u hD hDQ hM hu
  let a : ℕ → ℂ := fun n =>
    (lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Ioc M (M + N),
            ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
          else 0) ≤
      C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
      exact hlarge D Q M N a hD hDQ
    _ ≤ C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Ioc M (M + N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro n hn
        exact lemma6_weighted_mollifierCoeff_norm_sq_le hM hn u (hu n hn)
      · positivity

/-- Equation (14), conditional only on the elementary divisor-square mean:
the character large sieve and the `C_H` coefficient bound combine to give
the required weighted dyadic estimate. -/
theorem lemma6_mollifier_large_sieve_of_divisorSquareMean
    (hmean : Lemma6DivisorSquareMean) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ M → 2 ≤ M + N →
        (∀ n ∈ Finset.Ioc M (M + N), ‖u n‖ ≤ 1) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Ioc M (M + N),
                ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
            ((M + N : ℕ) : ℝ) *
            (Real.log ((M + N : ℕ) : ℝ)) ^ 3 /
            (M : ℝ) ^ 2 := by
  rcases lemma6_mollifier_large_sieve with ⟨A, hA, hlarge⟩
  rcases lemma6_divisorSquare_weighted_Ioc_le hmean with
    ⟨B, hB, hweighted⟩
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro D Q M N H u hD hDQ hM hMN hu
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Ioc M (M + N),
            ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
          else 0) ≤
      A * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Ioc M (M + N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
      hlarge D Q M N H u hD hDQ hM hu
    _ ≤ A * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        (B * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 /
          (M : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left (hweighted M N hM hMN)
      positivity
    _ = (A * B) * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        ((M + N : ℕ) : ℝ) *
        (Real.log ((M + N : ℕ) : ℝ)) ^ 3 /
        (M : ℝ) ^ 2 := by ring

/-- The exact `(Q / M + 1 / D) log(2M)^3` dyadic shape used on the right
of equation (14). -/
theorem lemma6_mollifier_large_sieve_dyadic_of_divisorSquareMean
    (hmean : Lemma6DivisorSquareMean) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ M →
        (∀ n ∈ Finset.Ioc M (M + M), ‖u n‖ ≤ 1) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Ioc M (M + M),
                ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) / (M : ℝ) + (D : ℝ)⁻¹) *
            (Real.log ((M + M : ℕ) : ℝ)) ^ 3 := by
  rcases lemma6_mollifier_large_sieve_of_divisorSquareMean hmean with
    ⟨A, hA, hlarge⟩
  refine ⟨2 * A, by positivity, ?_⟩
  intro D Q M H u hD hDQ hM hu
  have hMN : 2 ≤ M + M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Ioc M (M + M),
            ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
          else 0) ≤
      A * ((Q : ℝ) + (M : ℝ) / (D : ℝ)) *
        ((M + M : ℕ) : ℝ) *
        (Real.log ((M + M : ℕ) : ℝ)) ^ 3 /
        (M : ℝ) ^ 2 :=
      hlarge D Q M M H u hD hDQ hM hMN hu
    _ = (2 * A) * ((Q : ℝ) / (M : ℝ) + (D : ℝ)⁻¹) *
        (Real.log ((M + M : ℕ) : ℝ)) ^ 3 := by
      norm_num only [Nat.cast_add]
      field_simp
      ring

/-- Unconditional dyadic `(Q / M + 1 / D) log(2M)^3` form of equation (14). -/
theorem lemma6_mollifier_large_sieve_dyadic :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ M →
        (∀ n ∈ Finset.Ioc M (M + M), ‖u n‖ ≤ 1) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Ioc M (M + M),
                ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) / (M : ℝ) + (D : ℝ)⁻¹) *
            (Real.log ((M + M : ℕ) : ℝ)) ^ 3 :=
  lemma6_mollifier_large_sieve_dyadic_of_divisorSquareMean
    lemma6_divisorSquareMean

end Chen

end

/-! ## ChenTheorem.Lemma6.PolyaVinogradov -/

section

/-
The Fourier--Gauss input for the Pólya--Vinogradov estimate used in
equation (14).  We first establish the exact absolute value of the Gauss
sum of a primitive Dirichlet character for an arbitrary (not necessarily
prime) modulus.  The proof uses finite Fourier inversion on `ZMod q`, so it
also covers the composite moduli occurring in Chen's argument.
-/
open scoped Classical
open Finset AddChar ZMod

namespace Chen
/-- Fourier inversion gives the standard product formula for the Gauss
sums of a primitive character and its inverse. -/
theorem primitive_gaussSum_inv_mul_gaussSum
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    gaussSum χ⁻¹ ZMod.stdAddChar * gaussSum χ ZMod.stdAddChar =
      (q : ℂ) * χ (-1 : ZMod q) := by
  have hχinv : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_inv] using hχ
  have hF : ZMod.dft (χ : ZMod q → ℂ) =
      fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar := by
    funext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hFinv (k : ZMod q) :
      ZMod.dft (fun x : ZMod q => χ⁻¹ x) k =
        χ (-k) * gaussSum χ⁻¹ ZMod.stdAddChar := by
    simpa only [inv_inv] using
      hχinv.fourierTransform_eq_inv_mul_gaussSum k
  have hdft2 := congrFun (ZMod.dft_dft (χ : ZMod q → ℂ)) (1 : ZMod q)
  rw [hF, ZMod.dft_mul_const, ZMod.dft_comp_neg] at hdft2
  change ZMod.dft (fun x : ZMod q => χ⁻¹ x) (-1) *
      gaussSum χ ZMod.stdAddChar = (q : ℂ) • χ (-1) at hdft2
  rw [hFinv] at hdft2
  simpa only [neg_one_mul, neg_neg, map_one, one_mul,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one, mul_comm] using hdft2
/-- Complex conjugation relates the Gauss sum to that of the inverse
character, with the usual `χ(-1)` factor. -/
theorem star_primitive_gaussSum
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    star (gaussSum χ ZMod.stdAddChar) =
      χ (-1 : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  rw [star_gaussSum_eq, AddChar.inv_mulShift]
  have h := gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar
    (-1 : (ZMod q)ˣ)
  simpa only [inv_inv, Units.val_neg, Units.val_one, neg_one_mul] using h
/-- The squared absolute value of the Gauss sum of a primitive Dirichlet
character modulo `q` is exactly `q`. -/
theorem normSq_primitive_gaussSum
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ ZMod.stdAddChar) = q := by
  rw [← Complex.ofReal_inj, Complex.normSq_eq_conj_mul_self]
  change star (gaussSum χ ZMod.stdAddChar) *
      gaussSum χ ZMod.stdAddChar = (q : ℂ)
  rw [star_primitive_gaussSum χ, mul_assoc,
    primitive_gaussSum_inv_mul_gaussSum hχ]
  have hneg : χ (-1 : ZMod q) * χ (-1 : ZMod q) = 1 := by
    rw [← map_mul]
    norm_num
  calc
    χ (-1 : ZMod q) * ((q : ℂ) * χ (-1 : ZMod q)) =
        (q : ℂ) * (χ (-1 : ZMod q) * χ (-1 : ZMod q)) := by ring
    _ = (q : ℂ) := by rw [hneg, mul_one]
/-- Exact square-root size of a primitive Dirichlet-character Gauss sum. -/
theorem norm_primitive_gaussSum
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  rw [Complex.norm_def, normSq_primitive_gaussSum hχ]
/-- Fourier inversion for a primitive Dirichlet character, written in the
normalization used in the Pólya--Vinogradov argument. -/
theorem primitive_character_fourier_expansion
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (q : ℂ)⁻¹ * ∑ k : ZMod q,
      ZMod.stdAddChar (k * n) *
        (χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply
    (χ : ZMod q → ℂ)) n
  rw [ZMod.invDFT_apply] at hinv
  rw [← hinv]
  congr 2 with k
  rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
  rfl
/-- A primitive character of modulus at least two has mean zero over one
complete residue system. -/
theorem primitive_character_sum_one_period
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    ∑ n ∈ Finset.range q, χ n = 0 := by
  have hne : χ ≠ 1 := by
    intro heq
    rw [heq, DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_one] at hχ
    omega
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ i : Fin q, χ (i : ℕ) = ∑ a : ZMod q, χ a := by
      apply Fintype.sum_equiv (ZMod.finEquiv q)
      intro i
      cases q with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q =>
          exact congrArg χ (@ZMod.natCast_zmod_val (q + 1)
            inferInstance ((i : Fin (q + 1)) : ZMod (q + 1)))
    _ = 0 := χ.sum_eq_zero_of_ne_one hne
/-- Dirichlet characters are periodic with their modulus. -/
theorem dirichletCharacter_nat_add_modulus
    (q : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ (q + n) = χ n := by
  congr
  simp
/-- Every character prefix sum reduces to the final incomplete residue
block.  Complete blocks vanish for primitive characters of modulus `q ≥ 2`. -/
theorem primitive_character_prefix_sum_eq_mod
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ∑ n ∈ range N, χ n = ∑ n ∈ range (N % q), χ n := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hN : N < q
      · rw [Nat.mod_eq_of_lt hN]
      · have hqN : q ≤ N := le_of_not_gt hN
        have hqpos : 0 < q := by omega
        have hsub : N - q < N := Nat.sub_lt (by omega) hqpos
        have hsplit : N = q + (N - q) := by omega
        rw [hsplit, Finset.sum_range_add]
        rw [primitive_character_sum_one_period hχ hq, zero_add]
        have htail : ∑ x ∈ range (N - q), χ (q + x) =
            ∑ x ∈ range (N - q), χ x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact dirichletCharacter_nat_add_modulus q χ x
        simp_rw [Nat.cast_add]
        rw [htail, ih (N - q) hsub]
        congr 2
        rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
/-- A finite additive-character prefix sum, the elementary geometric
progression occurring after Fourier inversion. -/
noncomputable def additiveCharacterPrefix
    {q : ℕ} [NeZero q] (k : ZMod q) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, ZMod.stdAddChar (k * (n : ZMod q))
/-- Fourier expansion of a finite character prefix. -/
theorem primitive_character_prefix_fourier
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (N : ℕ) :
    ∑ n ∈ range N, χ n =
      ∑ k : ZMod q, (q : ℂ)⁻¹ * χ⁻¹ (-k) *
        gaussSum χ ZMod.stdAddChar * additiveCharacterPrefix k N := by
  calc
    ∑ n ∈ range N, χ n =
        ∑ n ∈ range N, ∑ k : ZMod q,
          (q : ℂ)⁻¹ * χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar *
            ZMod.stdAddChar (k * (n : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [primitive_character_fourier_expansion hχ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      let a : ℂ := (q : ℂ)⁻¹
      let b : ℂ := ZMod.stdAddChar (k * (n : ZMod q))
      let c : ℂ := χ⁻¹ (-k)
      let d : ℂ := gaussSum χ ZMod.stdAddChar
      change a * (b * (c * d)) = a * c * d * b
      ac_rfl
    _ = _ := (Finset.sum_comm).trans (by
      apply Finset.sum_congr rfl
      intro k hk
      rw [additiveCharacterPrefix, Finset.mul_sum])
/-- The elementary geometric bound for a nontrivial additive-character
prefix. -/
theorem additiveCharacterPrefix_norm_le
    {q : ℕ} [NeZero q] (k : ZMod q) (hk : k ≠ 0) (N : ℕ) :
    ‖additiveCharacterPrefix k N‖ ≤
      2 / ‖ZMod.stdAddChar k - 1‖ := by
  have hchar : ZMod.stdAddChar k ≠ 1 := by
    intro h
    have heq : ZMod.stdAddChar k =
        ZMod.stdAddChar (0 : ZMod q) := by simpa using h
    exact hk (ZMod.injective_stdAddChar heq)
  have hsum : additiveCharacterPrefix k N =
      ∑ n ∈ range N, (ZMod.stdAddChar k) ^ n := by
    unfold additiveCharacterPrefix
    apply Finset.sum_congr rfl
    intro n hn
    rw [show ZMod.stdAddChar (k * (n : ZMod q)) =
      (ZMod.stdAddChar k) ^ n by
        rw [mul_comm]
        have hmul : (n : ZMod q) * k = n • k := by
          simp
        rw [hmul, AddChar.map_nsmul_eq_pow]]
  rw [hsum, geom_sum_eq hchar, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖ZMod.stdAddChar k ^ N - 1‖ ≤
        ‖ZMod.stdAddChar k ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      simp only [norm_pow, AddChar.norm_apply, one_pow, norm_one]
      norm_num
/-- On the first half of a residue system the distance of the standard
additive character from one is bounded below linearly. -/
theorem stdAddChar_sub_one_norm_lower_bound_nat
    {q d : ℕ} [NeZero q] (hd : d ≤ q / 2) :
    4 * (d : ℝ) / q ≤
      ‖ZMod.stdAddChar (d : ZMod q) - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hdq : (d : ℝ) / q ≤ 1 / 2 := by
    rw [div_le_iff₀ hq]
    have hcast : (d : ℝ) * 2 ≤ q := by
      exact_mod_cast
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hd
    nlinarith
  have hangle : |Real.pi * (d : ℝ) / q| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg (by positivity)]
    calc
      Real.pi * (d : ℝ) / q = Real.pi * ((d : ℝ) / q) := by ring
      _ ≤ Real.pi * (1 / 2) :=
        mul_le_mul_of_nonneg_left hdq Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hsin := Real.mul_abs_le_abs_sin hangle
  rw [show (d : ZMod q) = ((d : ℤ) : ZMod q) by norm_cast,
    ZMod.stdAddChar_coe]
  have hexp :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (d : ℤ) / (q : ℕ)) =
        Complex.exp (Complex.I *
          ((2 * Real.pi * d / q : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have harg : |Real.pi * (d : ℝ) / q| =
      Real.pi * d / q := abs_of_nonneg (by positivity)
  rw [show (2 * Real.pi * (d : ℝ) / q) / 2 =
      Real.pi * d / q by ring]
  rw [harg] at hsin
  field_simp at hsin ⊢
  nlinarith [Real.pi_pos]
/-- Replacing a frequency by its negative does not change its distance
from one on the unit circle. -/
theorem stdAddChar_neg_sub_one_norm
    {q : ℕ} [NeZero q] (k : ZMod q) :
    ‖ZMod.stdAddChar (-k) - 1‖ =
      ‖ZMod.stdAddChar k - 1‖ := by
  rw [AddChar.map_neg_eq_inv]
  let z := ZMod.stdAddChar k
  have hzNorm : ‖z‖ = 1 := by simp [z]
  have hz : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzNorm
    norm_num at hzNorm
  calc
    ‖z⁻¹ - 1‖ = ‖z⁻¹ * (1 - z)‖ := by
      congr 1
      field_simp
    _ = ‖z⁻¹‖ * ‖1 - z‖ := norm_mul _ _
    _ = ‖1 - z‖ := by rw [norm_inv, hzNorm, inv_one, one_mul]
    _ = ‖z - 1‖ := norm_sub_rev _ _
/-- The denominator in the geometric estimate is controlled by the
centered representative of the frequency. -/
theorem stdAddChar_sub_one_norm_lower_bound
    {q : ℕ} [NeZero q] (k : ZMod q) :
    4 * (k.valMinAbs.natAbs : ℝ) / q ≤
      ‖ZMod.stdAddChar k - 1‖ := by
  let d := k.valMinAbs.natAbs
  have hd : d ≤ q / 2 := ZMod.natAbs_valMinAbs_le k
  have hbase : 4 * (d : ℝ) / q ≤
      ‖ZMod.stdAddChar (d : ZMod q) - 1‖ :=
    stdAddChar_sub_one_norm_lower_bound_nat hd
  rw [ZMod.natCast_natAbs_valMinAbs] at hbase
  split at hbase
  · simpa only [d] using hbase
  · rw [stdAddChar_neg_sub_one_norm k] at hbase
    simpa only [d] using hbase
/-- The centered geometric-progression estimate used in the
Pólya--Vinogradov argument. -/
theorem additiveCharacterPrefix_norm_le_centered
    {q : ℕ} [NeZero q] (k : ZMod q) (hk : k ≠ 0) (N : ℕ) :
    ‖additiveCharacterPrefix k N‖ ≤
      (q : ℝ) / (2 * k.valMinAbs.natAbs) := by
  let d := k.valMinAbs.natAbs
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by
      rw [Nat.pos_iff_ne_zero]
      intro hd
      have hval : k.valMinAbs = 0 := Int.natAbs_eq_zero.mp hd
      exact hk (ZMod.valMinAbs_eq_zero k |>.mp hval))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hden := stdAddChar_sub_one_norm_lower_bound k
  have hlowerpos : 0 < 4 * (d : ℝ) / q := by positivity
  calc
    ‖additiveCharacterPrefix k N‖ ≤
        2 / ‖ZMod.stdAddChar k - 1‖ :=
      additiveCharacterPrefix_norm_le k hk N
    _ ≤ 2 / (4 * (d : ℝ) / q) := by
      exact div_le_div_of_nonneg_left (by norm_num) hlowerpos hden
    _ = (q : ℝ) / (2 * k.valMinAbs.natAbs) := by
      dsimp only [d]
      field_simp
      ring
/-- The reciprocal centered frequency, extended by zero at frequency
zero. -/
noncomputable def centeredReciprocal
    {q : ℕ} [NeZero q] (k : ZMod q) : ℝ :=
  if k = 0 then 0 else ((k.valMinAbs.natAbs : ℝ)⁻¹)
/-- The sum of centered reciprocal frequencies in a natural residue
system is at most twice the corresponding harmonic number. -/
theorem centered_reciprocal_sum_nat (q : ℕ) (hq : 1 ≤ q) :
    ∑ j ∈ Ico 1 q,
        (((min j (q - j) : ℕ) : ℝ)⁻¹) ≤
      2 * (harmonic (q - 1) : ℝ) := by
  have hpoint : ∀ j ∈ Ico 1 q,
      (((min j (q - j) : ℕ) : ℝ)⁻¹) ≤
        (j : ℝ)⁻¹ + (((q - j : ℕ) : ℝ)⁻¹) := by
    intro j hj
    by_cases h : j ≤ q - j
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (inv_nonneg.mpr (by positivity))
    · rw [min_eq_right (le_of_not_ge h)]
      exact le_add_of_nonneg_left (inv_nonneg.mpr (by positivity))
  calc
    ∑ j ∈ Ico 1 q, (((min j (q - j) : ℕ) : ℝ)⁻¹) ≤
        ∑ j ∈ Ico 1 q,
          ((j : ℝ)⁻¹ + (((q - j : ℕ) : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hpoint j hj
    _ = (∑ j ∈ Ico 1 q, (j : ℝ)⁻¹) +
        ∑ j ∈ Ico 1 q, (((q - j : ℕ) : ℝ)⁻¹) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * ∑ j ∈ Ico 1 q, (j : ℝ)⁻¹ := by
      rw [show (∑ j ∈ Ico 1 q,
          (((q - j : ℕ) : ℝ)⁻¹)) =
          ∑ j ∈ Ico 1 q, ((j : ℝ)⁻¹) by
        apply Finset.sum_bij (fun j _ ↦ q - j)
        · intro j hj
          simp only [mem_Ico] at hj ⊢
          omega
        · intro j₁ hj₁ j₂ hj₂ heq
          simp only [mem_Ico] at hj₁ hj₂
          omega
        · intro b hb
          refine ⟨q - b, ?_, ?_⟩
          · simp only [mem_Ico] at hb ⊢
            omega
          · simp only [mem_Ico] at hb
            omega
        · intro j hj
          rfl]
      ring
    _ = 2 * (harmonic (q - 1) : ℝ) := by
      congr 1
      have hset : Ico 1 q = Icc 1 (q - 1) := by
        ext j
        simp only [mem_Ico, mem_Icc]
        omega
      rw [hset, harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
/-- The centered reciprocal sum over `ZMod q`. -/
theorem centered_reciprocal_sum_zmod (q : ℕ) [NeZero q]
    (hq : 1 ≤ q) :
    ∑ k : ZMod q, centeredReciprocal k ≤
      2 * (harmonic (q - 1) : ℝ) := by
  rw [← show (∑ i : Fin q,
      centeredReciprocal ((i : ℕ) : ZMod q)) =
      ∑ k : ZMod q, centeredReciprocal k by
        apply Fintype.sum_equiv (ZMod.finEquiv q)
        intro i
        cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q =>
            exact congrArg centeredReciprocal
              (@ZMod.natCast_zmod_val (q + 1) inferInstance
                ((i : Fin (q + 1)) : ZMod (q + 1)))]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => centeredReciprocal (j : ZMod q)) q]
  have hpoint (j : ℕ) (hj : j < q) :
      centeredReciprocal (j : ZMod q) =
        if j = 0 then 0 else
          (((min j (q - j) : ℕ) : ℝ)⁻¹) := by
    unfold centeredReciprocal
    have hzero : (j : ZMod q) = 0 ↔ j = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      constructor
      · intro hdvd
        exact Nat.eq_zero_of_dvd_of_lt hdvd hj
      · intro h
        simp [h]
    rw [if_congr hzero (by rfl) (by rfl)]
    split
    · rfl
    · rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast,
        Nat.mod_eq_of_lt hj]
  calc
    ∑ j ∈ range q, centeredReciprocal (j : ZMod q) =
        ∑ j ∈ range q, if j = 0 then 0 else
          (((min j (q - j) : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hpoint j (mem_range.mp hj)
    _ = ∑ j ∈ Ico 1 q,
          (((min j (q - j) : ℕ) : ℝ)⁻¹) := by
      have hrange : range q = insert 0 (Ico 1 q) := by
        ext j
        simp only [mem_range, mem_insert, mem_Ico]
        omega
      rw [hrange, sum_insert (by simp), if_pos rfl, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      have hj0 : j ≠ 0 := by
        intro h
        subst j
        simp at hj
      rw [if_neg hj0]
    _ ≤ 2 * (harmonic (q - 1) : ℝ) :=
      centered_reciprocal_sum_nat q hq
/-- Pólya--Vinogradov in a sharp harmonic-number form.  The estimate is
uniform in the prefix length. -/
theorem primitive_character_prefix_sum_norm_le_harmonic
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ‖∑ n ∈ range N, χ n‖ ≤
      Real.sqrt q * (harmonic (q - 1) : ℝ) := by
  letI : Fact (1 < q) := ⟨by omega⟩
  rw [primitive_character_prefix_fourier hχ]
  calc
    ‖∑ k : ZMod q, (q : ℂ)⁻¹ * χ⁻¹ (-k) *
        gaussSum χ ZMod.stdAddChar * additiveCharacterPrefix k N‖ ≤
        ∑ k : ZMod q, ‖(q : ℂ)⁻¹ * χ⁻¹ (-k) *
          gaussSum χ ZMod.stdAddChar *
            additiveCharacterPrefix k N‖ := norm_sum_le _ _
    _ ≤ ∑ k : ZMod q,
        Real.sqrt q / 2 * centeredReciprocal k := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        rw [MulChar.map_nonunit _ (by
          simpa only [neg_zero] using
            (not_isUnit_zero : ¬IsUnit (0 : ZMod q)))]
        simp [centeredReciprocal]
      · have hprefix :=
          additiveCharacterPrefix_norm_le_centered k hk0 N
        have hchar : ‖χ⁻¹ (-k)‖ ≤ 1 :=
          DirichletCharacter.norm_le_one _ _
        have hqpos : (0 : ℝ) < q := by
          exact_mod_cast NeZero.pos q
        have hdpos : (0 : ℝ) < k.valMinAbs.natAbs := by
          exact_mod_cast (show 0 < k.valMinAbs.natAbs by
            rw [Nat.pos_iff_ne_zero]
            intro hd
            have hval : k.valMinAbs = 0 :=
              Int.natAbs_eq_zero.mp hd
            exact hk0 (ZMod.valMinAbs_eq_zero k |>.mp hval))
        rw [norm_mul, norm_mul, norm_mul, norm_inv,
          Complex.norm_natCast, norm_primitive_gaussSum hχ]
        rw [centeredReciprocal, if_neg hk0]
        calc
          (q : ℝ)⁻¹ * ‖χ⁻¹ (-k)‖ * Real.sqrt q *
              ‖additiveCharacterPrefix k N‖ ≤
              (q : ℝ)⁻¹ * 1 * Real.sqrt q *
                ((q : ℝ) / (2 * k.valMinAbs.natAbs)) := by
            gcongr
          _ = Real.sqrt q / 2 *
                ((k.valMinAbs.natAbs : ℝ)⁻¹) := by
            field_simp
    _ = Real.sqrt q / 2 *
        ∑ k : ZMod q, centeredReciprocal k := by
      rw [Finset.mul_sum]
    _ ≤ Real.sqrt q / 2 *
        (2 * (harmonic (q - 1) : ℝ)) := by
      gcongr
      exact centered_reciprocal_sum_zmod q (by omega)
    _ = Real.sqrt q * (harmonic (q - 1) : ℝ) := by ring
/-- The logarithmic Pólya--Vinogradov form used for partial summation.
The explicit constant is immaterial for Lemma 6. -/
theorem primitive_character_prefix_sum_norm_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ‖∑ n ∈ range N, χ n‖ ≤
      3 * Real.sqrt q * Real.log (2 * q) := by
  have hq1 : 1 ≤ q := by omega
  have hqm1pos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < q - 1)
  have hargpos : (0 : ℝ) < 2 * q := by positivity
  have hlogmono : Real.log (q - 1 : ℕ) ≤
      Real.log (2 * q : ℕ) := by
    exact Real.log_le_log hqm1pos (by exact_mod_cast (show q - 1 ≤ 2 * q by omega))
  have hlogtwo : Real.log 2 ≤ Real.log (2 * q : ℕ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ 2 * q by omega))
  have hone : (1 : ℝ) ≤ 2 * Real.log (2 * q : ℕ) := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (1/2 : ℝ))
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at hl
    nlinarith
  have hharm := harmonic_le_one_add_log (q - 1)
  have hH : (harmonic (q - 1) : ℝ) ≤
      3 * Real.log (2 * q : ℕ) := by
    linarith
  calc
    ‖∑ n ∈ range N, χ n‖ ≤
        Real.sqrt q * (harmonic (q - 1) : ℝ) :=
      primitive_character_prefix_sum_norm_le_harmonic hχ hq N
    _ ≤ Real.sqrt q * (3 * Real.log (2 * q : ℕ)) := by
      gcongr
    _ = 3 * Real.sqrt q * Real.log (2 * q) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring
end Chen

end

/-! ## ChenTheorem.Lemma6.RealCharacterChangeLevelZeros -/

section

namespace Chen

theorem dirichletEulerFactor_ne_zero_of_re_pos {d p : ℕ}
    (χ : DirichletCharacter ℂ d) (hp : 2 ≤ p) (s : ℂ) (hs : 0 < s.re) :
    dirichletEulerFactor χ p s ≠ 0 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hnorm : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p), Complex.neg_re]
    calc
      _ ≤ 1 * (p : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right
        (χ.norm_le_one p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hpR (neg_neg_of_pos hs)
  intro he
  have he' : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
  simp [he'] at hnorm

theorem LFunction_changeLevel_zero_iff {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction (χ.changeLevel hdq) s = 0 ↔
      DirichletCharacter.LFunction χ s = 0 := by
  rw [DirichletCharacter.LFunction_changeLevel hdq χ (Or.inl hχ)]
  have hp : (∏ p ∈ q.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact dirichletEulerFactor_ne_zero_of_re_pos χ (Nat.prime_of_mem_primeFactors hp).two_le s hs
  simp only [mul_eq_zero, hp, or_false]

theorem real_character_changeLevel {d q : ℕ} (hdq : d ∣ q)
    (χ : DirichletCharacter ℂ d) (hχ : χ ^ 2 = 1) :
    (χ.changeLevel hdq) ^ 2 = 1 := by
  rw [← map_pow, hχ, map_one]

theorem real_character_eq_of_mul_eq_one {q : ℕ}
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hprod : χ * ψ = 1) : ψ = χ := by
  calc
    ψ = (χ * χ) * ψ := by rw [← pow_two, hχ, one_mul]
    _ = χ := by rw [mul_assoc, hprod, mul_one]

theorem exists_nonprincipal_one_nonvanishing_ball {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℂ, ‖s - 1‖ < η → DirichletCharacter.LFunction χ s ≠ 0 := by
  have h := (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt.eventually_ne
    (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨η, hη, fun s hs => hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hs)⟩

end Chen

end

/-! ## ChenTheorem.Lemma6.RealCharacterConjugation -/

section

open Set Filter Complex ComplexConjugate
open scoped Topology

namespace Chen
theorem conj_character_apply_of_square_eq_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    conj (χ n) = χ n := by
  have hmul : χ * χ = 1 := by simpa only [pow_two] using hsq
  have hinv : χ⁻¹ = χ := by
    calc
      χ⁻¹ = χ⁻¹ * (χ * χ) := by rw [hmul, mul_one]
      _ = χ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have h := MulChar.star_apply' χ (n : ZMod q)
  rw [hinv] at h
  exact h
theorem conj_LSeries_term_of_real_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (s : ℂ) (n : ℕ) :
    conj (LSeries.term (fun m => χ m) s n) =
      LSeries.term (fun m => χ m) (conj s) n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      conj_character_apply_of_square_eq_one χ hsq]
    have harg : (n : ℂ).arg ≠ Real.pi := by rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]; exact Real.pi_pos.ne
    have he := Complex.cpow_conj (n : ℂ) s harg
    simpa using congrArg (fun z => χ n / z) he.symm
theorem conj_LFunction_of_real_character_re_gt_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (s : ℂ) (hs : 1 < s.re) :
    conj (DirichletCharacter.LFunction χ s) = DirichletCharacter.LFunction χ (conj s) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hs)]
  change conj (∑' n, LSeries.term (fun m => χ m) s n) =
    ∑' n, LSeries.term (fun m => χ m) (conj s) n
  rw [Complex.conj_tsum]
  exact tsum_congr (conj_LSeries_term_of_real_character χ hsq s)
theorem conj_LFunction_of_nonprincipal_real_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) (s : ℂ) :
    conj (DirichletCharacter.LFunction χ s) = DirichletCharacter.LFunction χ (conj s) := by
  let f := DirichletCharacter.LFunction χ
  have hf : Differentiable ℂ f := DirichletCharacter.differentiable_LFunction hχ
  have hg : Differentiable ℂ (conj ∘ f ∘ conj) := by
    intro z
    simpa using (hf (conj z)).conj_conj
  have he : f =ᶠ[𝓝 (2 : ℂ)] (conj ∘ f ∘ conj) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have h := conj_LFunction_of_real_character_re_gt_one χ hsq (conj z) (by simpa using hz)
    simpa [f, Function.comp_apply] using h.symm
  have hall := (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) he
  have h := congrFun hall (conj s)
  simpa [f, Function.comp_apply] using h.symm
theorem real_character_conjugate_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ (conj s) = 0 := by
  rw [← conj_LFunction_of_nonprincipal_real_character χ hχ hsq s, hs, map_zero]

end Chen

end

