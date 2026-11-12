module

public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part033
public import Green64.Library.Sieve.Foundations.Part002
public import Green64.Library.Analysis.Estimates.SourceD64Harmonic
public import Green64.Library.Correlation.Part003
public import Green64.Library.Analysis.Estimates.Part004
public import Green64.Library.Correlation.Part004
public import Green64.Library.Weights.SourceExceptionalScale
public import Mathlib
public import Mathlib.Tactic
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Weights.Part006
public import Green64.Library.Weights.Part001
public import Green64.Library.Weights.Part032
public import Green64.Library.Sieve.Foundation.Lemma9.Part005
public import Green64.Library.Analysis.Estimates.Part006

@[expose] public section

/-!
# Weights / Part035

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceAllIntegerDivisorSecondMoment -/

section

/-!
An unconditional cubic-logarithmic second moment for the natural
(non-squarefree) divisor-count function.  The local inequality
`tau(n)^2 <= d4(n)` is proved in this task; the fully checked fourfold
Dirichlet-convolution harmonic bound is reused from the verified
CRT predecessor (task-3c3850d6ca1c) with its pinned Lean 4.32 Oleans.
-/

namespace Green64Analytic.CorrelationMellin

/-- Crucial source R(t) second moment: no squarefree hypothesis. -/
theorem source_all_integer_divisor_second_moment
    (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z, ((n.divisors.card : ℝ)^2)) ≤
      (Z:ℝ) * (1 + Real.log (Z:ℝ))^3 := by
  classical
  have hCompare :
      (∑ n ∈ Finset.Ioc 0 Z, ((n.divisors.card : ℝ)^2)) ≤
      (∑ n ∈ Finset.Ioc 0 Z,
        (((ArithmeticFunction.sigma 0)*(ArithmeticFunction.sigma 0)) n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1
    exact_mod_cast source_all_integer_divisor_square_le_fourfold n hn0
  have hH := Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_le_one_add_log Z
  have hRecipNonneg := Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_nonneg Z
  have hPow :
      (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Z)^3 ≤
        (1 + Real.log (Z:ℝ))^3 := by
    gcongr
  calc
    _ ≤ (∑ n ∈ Finset.Ioc 0 Z,
        (((ArithmeticFunction.sigma 0)*(ArithmeticFunction.sigma 0)) n : ℝ)) := hCompare
    _ ≤ (Z:ℝ) * (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Z)^3 :=
      Green64Analytic.SourceDivisorMoment.fourfold_divisor_sum_le_harmonic_cube Z
    _ ≤ (Z:ℝ) * (1 + Real.log (Z:ℝ))^3 :=
      mul_le_mul_of_nonneg_left hPow (Nat.cast_nonneg _)
end Green64Analytic.CorrelationMellin

end

/-! ## OriginalShiftTwoCRTRemainder -/

section

set_option maxHeartbeats 4500000
open scoped BigOperators

namespace Green64Analytic.SourceCRT

/-- Actual product-two box count minus its proved CRT main term.
The value outside squarefree sieve moduli is set to zero solely to
form ordinary finite sums; all counted moduli below are squarefree. -/
noncomputable def parityOriginalShiftTwoMaskedRemainder434
    (D d A B C E : ℕ) (rough banned : ℕ → Bool) : ℝ :=
  if hd : Squarefree d then
    ((parityOriginalShiftTwoIntegerBox434 D d
      (parityOriginalShiftTwoSquarefreeBad434 d hd rough banned) A B C E).card : ℝ) -
      ((D.totient * ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) : ℕ) : ℝ) *
        (((B - A : ℕ) : ℝ) * ((E - C : ℕ) : ℝ) / ((D * d : ℕ) : ℝ) ^ 2)
  else 0

/-- Original6.6 for the actual shift-two box, with explicit absolute
constants and all local masks. AssignmentD can have prime powers. -/
theorem parity_original_shift_two_masked_remainder_bound434
    (D d A B C E : ℕ) (hD : 0 < D) (hd : Squarefree d)
    (hDd : D.Coprime d) (h2D : Nat.Coprime 2 D)
    (rough banned : ℕ → Bool) (hBannedTwo : banned 2 = false)
    (hAB : A ≤ B) (hCE : C ≤ E) :
    |parityOriginalShiftTwoMaskedRemainder434 D d A B C E rough banned| ≤
      (d.divisors.card : ℝ) ^ 2 *
        (2 * (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) +
          4 * (D : ℝ) * (d : ℝ)) := by
  rw [parityOriginalShiftTwoMaskedRemainder434, dif_pos hd]
  have hb := parity_original_shift_two_masked_integer_box_error434
    D d A B C E hD hd hDd h2D rough banned hBannedTwo hAB hCE
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hc :
      ((D.totient * ∏ p ∈ d.primeFactors, localNu p (rough p) (banned p) : ℕ) : ℝ) ≤
        (D : ℝ) * (d : ℝ) * (d.divisors.card : ℝ) ^ 2 := by
    calc
      _ ≤ (D : ℝ) * ((d : ℝ) * (d.divisors.card : ℝ) ^ 2) := by
        exact_mod_cast Nat.mul_le_mul (Nat.totient_le D)
          (localNu_product_le_divisorSquare d hd rough banned)
      _ = _ := by ring
  have hfactor :
      0 ≤ 4 + 2 * (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) /
        ((D * d : ℕ) : ℝ) := by positivity
  calc
    _ ≤ _ := hb
    _ ≤ ((D : ℝ) * (d : ℝ) * (d.divisors.card : ℝ) ^ 2) *
        (4 + 2 * (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) /
          ((D * d : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hc hfactor
    _ = _ := by
      push_cast
      field_simp [hDR, hdR]
      <;> ring

/-- Original6.7 finite remainder sum, using the already native
all-integer divisor second moment. The carrier may retain every
squarefree/coprimality/source restriction; only the upper bound is
enlarged to all positive integers up to the exact natural levelZ. -/
theorem parity_original_shift_two_masked_remainder_sum434
    (D Z A B C E : ℕ) (hD : 0 < D) (h2D : Nat.Coprime 2 D)
    (rough banned : ℕ → Bool) (hBannedTwo : banned 2 = false)
    (hAB : A ≤ B) (hCE : C ≤ E)
    (T : Finset ℕ) (hT : T ⊆ Finset.Ioc 0 Z)
    (hSquarefree : ∀ d ∈ T, Squarefree d)
    (hCoprime : ∀ d ∈ T, D.Coprime d) :
    (∑ d ∈ T, |parityOriginalShiftTwoMaskedRemainder434 D d A B C E rough banned|) ≤
      (2 * (((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)) * (Z : ℝ) +
        4 * (D : ℝ) * (Z : ℝ) ^ 2) * (1 + Real.log (Z : ℝ)) ^ 3 := by
  let M : ℝ := ((B - A : ℕ) : ℝ) + ((E - C : ℕ) : ℝ)
  let C0 : ℝ := 2 * M + 4 * (D : ℝ) * (Z : ℝ)
  have hC0 : 0 ≤ C0 := by dsimp [C0, M]; positivity
  have hPoint (d : ℕ) (hd : d ∈ T) :
      |parityOriginalShiftTwoMaskedRemainder434 D d A B C E rough banned| ≤
        (d.divisors.card : ℝ) ^ 2 * C0 := by
    have hle : d ≤ Z := (Finset.mem_Ioc.mp (hT hd)).2
    have hleR : (d : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hle
    have hfactor : 2 * M + 4 * (D : ℝ) * (d : ℝ) ≤ C0 := by
      dsimp [C0]
      nlinarith [mul_le_mul_of_nonneg_left hleR (show 0 ≤ 4 * (D : ℝ) by positivity)]
    exact (parity_original_shift_two_masked_remainder_bound434
      D d A B C E hD (hSquarefree d hd) (hCoprime d hd) h2D
      rough banned hBannedTwo hAB hCE).trans
      (mul_le_mul_of_nonneg_left hfactor (sq_nonneg _))
  have hsum :
      (∑ d ∈ T, (d.divisors.card : ℝ) ^ 2) ≤
        ∑ d ∈ Finset.Ioc 0 Z, (d.divisors.card : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (by intro d _ _; exact sq_nonneg _)
  calc
    _ ≤ ∑ d ∈ T, (d.divisors.card : ℝ) ^ 2 * C0 :=
      Finset.sum_le_sum hPoint
    _ = (∑ d ∈ T, (d.divisors.card : ℝ) ^ 2) * C0 := by rw [Finset.sum_mul]
    _ ≤ (∑ d ∈ Finset.Ioc 0 Z, (d.divisors.card : ℝ) ^ 2) * C0 :=
      mul_le_mul_of_nonneg_right hsum hC0
    _ ≤ ((Z : ℝ) * (1 + Real.log (Z : ℝ)) ^ 3) * C0 :=
      mul_le_mul_of_nonneg_right
        (Green64Analytic.CorrelationMellin.source_all_integer_divisor_second_moment Z) hC0
    _ = _ := by dsimp [C0, M]; ring

end Green64Analytic.SourceCRT

end

/-! ## SourceD64SumPre -/

section

namespace Green64Analytic.CorrelationSquare
open scoped ArithmeticFunction.zeta BigOperators
set_option maxHeartbeats 1200000

/-- The actual d64 partial sum, with exactly 63 harmonic factors
and the original arithmetic zeta convolution. -/
theorem source_d64_summatory_harmonic434 (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z, (sourceD64 n : ℝ)) ≤
      (Z:ℝ) * (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Z)^63 := by
  let f : ArithmeticFunction ℕ :=
    (ArithmeticFunction.zeta : ArithmeticFunction ℕ)^63
  have hfEq : sourceD64 = f * ArithmeticFunction.zeta := by
    change ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^64) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^63) * ArithmeticFunction.zeta
    rw [show (64:ℕ) = 63+1 by norm_num, pow_succ]
  have hb := Green64Analytic.SourceDivisorMoment.sum_mul_zeta_le_reciprocal f Z
  have hh := source_zeta_power_reciprocal_harmonic434 Z 62
  calc
    _ = ∑ n ∈ Finset.Ioc 0 Z, ((f*ArithmeticFunction.zeta) n : ℝ) := by
      rw [hfEq]
    _ ≤ (Z:ℝ) * (∑ n ∈ Finset.Ioc 0 Z, (f n : ℝ)/(n:ℝ)) := hb
    _ ≤ (Z:ℝ) *
        (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Z)^63 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [f, show (62:ℕ)+1=63 by norm_num] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceD64Summatory -/

section

namespace Green64Analytic.CorrelationSquare
open scoped ArithmeticFunction.zeta BigOperators
set_option maxHeartbeats 1000000

/-- Entire all-integer d64 moment, including non-squarefree n. -/
theorem source_d64_summatory_log434 (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z, (sourceD64 n : ℝ)) ≤
      (Z:ℝ) * (1+Real.log (Z:ℝ))^63 := by
  have hb := source_d64_summatory_harmonic434 Z
  have hh := Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_le_one_add_log Z
  have hH : 0 ≤ Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Z :=
    Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_nonneg Z
  have hP : (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Z)^63 ≤
      (1+Real.log (Z:ℝ))^63 := pow_le_pow_left₀ hH hh 63
  exact hb.trans (mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg _))

/-- The source sixth divisor moment has the EXACT universal
X(1+log X)^63 bound, rather than a hypothesis about coefficients. -/
theorem source_tau6_summatory_log434 (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z, ((n.divisors.card : ℝ)^6)) ≤
      (Z:ℝ) * (1+Real.log (Z:ℝ))^63 := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 Z, (sourceD64 n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1
      exact_mod_cast source_tau_six_le_d64_all_integer434 n hn0
    _ ≤ _ := source_d64_summatory_log434 Z
end Green64Analytic.CorrelationSquare

end

/-! ## SourceResidualTrueL2 -/

section

/-! Full source dyadic alpha-character/marked-residual L² coefficient
mass.  Genuine convolution; fixed fourfold divisor moment; no
squarefreeness, no arbitrary replacement coefficient sequence. -/

namespace Green64Analytic.CorrelationMellin

theorem source_residual_product_dyadic_support
    (M R : Finset ℕ) (M0 R0 : ℕ)
    (hM : M ⊆ Finset.Icc M0 (2*M0))
    (hR : R ⊆ Finset.Icc R0 (2*R0)) :
    (M.product R).image (fun z => z.1*z.2) ⊆
      Finset.Icc (M0*R0) (4*(M0*R0)) := by
  classical
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
  have hm := Finset.mem_Icc.mp (hM (Finset.mem_product.mp hz).1)
  have hr := Finset.mem_Icc.mp (hR (Finset.mem_product.mp hz).2)
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.mul_le_mul hm.1 hr.1
  · calc
      z.1*z.2 ≤ (2*M0)*(2*R0) := Nat.mul_le_mul hm.2 hr.2
      _ = 4*(M0*R0) := by ring

/-- The source residual `R(t)` collapsed coefficient L² budget with
all original factor coefficients, character modulus/phase encoded by
`chi` and `sigma0`, marked source `d`, and true dyadic supports.
The bound is explicit, not an assumed divisor-moment estimate. -/
theorem source_residual_true_dyadic_square_norm
    (M R : Finset ℕ) (M0 R0 : ℕ) (alpha chi d : ℕ → ℂ)
    (sigma0 : ℝ) (A D : ℝ)
    (hM0 : 0 < M0) (hR0 : 0 < R0)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hM : M ⊆ Finset.Icc M0 (2*M0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (ha : ∀ m ∈ M, ‖alpha m‖ ≤ A)
    (hchi : ∀ m ∈ M, ‖chi m‖ ≤ 1)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ D) :
    (∑ n ∈ (M.product R).image (fun z => z.1*z.2),
      ‖sourceResidualProductCoeff M R
        (sourceAlphaCharacterCoefficient alpha chi sigma0)
        (sourceMarkedResidualCoefficient d) n‖^2) ≤
      ((A*D)/((M0*R0:ℕ):ℝ))^2 * ((4*(M0*R0):ℕ):ℝ) *
        (1+Real.log ((4*(M0*R0):ℕ):ℝ))^3 := by
  classical
  let U := M0*R0
  let S := (M.product R).image (fun z => z.1*z.2)
  let coeff := sourceResidualProductCoeff M R
    (sourceAlphaCharacterCoefficient alpha chi sigma0)
    (sourceMarkedResidualCoefficient d)
  have hU : 0 < U := mul_pos hM0 hR0
  have hUR : (0:ℝ) < U := by exact_mod_cast hU
  have hMpos (m : ℕ) (hm : m ∈ M) : 0 < m :=
    lt_of_lt_of_le hM0 (Finset.mem_Icc.mp (hM hm)).1
  have hRpos (r : ℕ) (hr : r ∈ R) : 0 < r :=
    lt_of_lt_of_le hR0 (Finset.mem_Icc.mp (hR hr)).1
  have hS : S ⊆ Finset.Icc U (4*U) :=
    source_residual_product_dyadic_support M R M0 R0 hM hR
  have hPoint (n : ℕ) (hn : n ∈ S) :
      ‖coeff n‖ ≤ (n.divisors.card:ℝ)*(A*D)/(n:ℝ) := by
    have hnpos : 0 < n :=
      lt_of_lt_of_le hU (Finset.mem_Icc.mp (hS hn)).1
    exact source_character_residual_coefficient_divisor_bound
      M R alpha chi d sigma0 A D hA hD hMpos hRpos ha hchi hd n hnpos
  have hSq (n : ℕ) (hn : n ∈ S) :
      ‖coeff n‖^2 ≤ ((A*D)/(U:ℝ))^2 * (n.divisors.card:ℝ)^2 := by
    have hnU := (Finset.mem_Icc.mp (hS hn)).1
    have hnR : (0:ℝ) < n := by exact_mod_cast lt_of_lt_of_le hU hnU
    have hnUR : (U:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnU
    have hNum : 0 ≤ (n.divisors.card:ℝ)*(A*D) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hA hD)
    have hDiv :
        (n.divisors.card:ℝ)*(A*D)/(n:ℝ) ≤
        (n.divisors.card:ℝ)*(A*D)/(U:ℝ) := by
      apply (div_le_div_iff₀ hnR hUR).mpr
      exact mul_le_mul_of_nonneg_left hnUR hNum
    calc
      ‖coeff n‖^2 ≤ ((n.divisors.card:ℝ)*(A*D)/(n:ℝ))^2 := by
        apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg hNum hnR.le)).mpr
        exact hPoint n hn
      _ ≤ ((n.divisors.card:ℝ)*(A*D)/(U:ℝ))^2 := by
        apply (sq_le_sq₀ (div_nonneg hNum hnR.le)
          (div_nonneg hNum hUR.le)).mpr
        exact hDiv
      _ = ((A*D)/(U:ℝ))^2*(n.divisors.card:ℝ)^2 := by ring
  have hSqSum :
      (∑ n ∈ S, ‖coeff n‖^2) ≤
        ((A*D)/(U:ℝ))^2 * ∑ n ∈ S, (n.divisors.card:ℝ)^2 := by
    calc
      _ ≤ ∑ n ∈ S,
          ((A*D)/(U:ℝ))^2*(n.divisors.card:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hSq n hn
      _ = _ := by rw [Finset.mul_sum]
  have hSIoc : S ⊆ Finset.Ioc 0 (4*U) := by
    intro n hn
    have hnS := Finset.mem_Icc.mp (hS hn)
    exact Finset.mem_Ioc.mpr ⟨lt_of_lt_of_le hU hnS.1, hnS.2⟩
  have hTau :
      (∑ n ∈ S, (n.divisors.card:ℝ)^2) ≤
        ((4*U:ℕ):ℝ)*(1+Real.log ((4*U:ℕ):ℝ))^3 := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc 0 (4*U), (n.divisors.card:ℝ)^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hSIoc
        intro n hn hnNot
        positivity
      _ ≤ _ := source_all_integer_divisor_second_moment (4*U)
  calc
    _ ≤ ((A*D)/(U:ℝ))^2 * ∑ n ∈ S, (n.divisors.card:ℝ)^2 := hSqSum
    _ ≤ ((A*D)/(U:ℝ))^2 * (((4*U:ℕ):ℝ)*(1+Real.log ((4*U:ℕ):ℝ))^3) :=
      mul_le_mul_of_nonneg_left hTau (sq_nonneg _)
    _ = ((A*D)/((M0*R0:ℕ):ℝ))^2 * ((4*(M0*R0):ℕ):ℝ) *
        (1+Real.log ((4*(M0*R0):ℕ):ℝ))^3 := by
      dsimp [U]
      ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualResidualSparseBound -/

section

/-! Actual source alpha-character / marked-residual sparse-real-time
mean-square theorem.  The only analytic premise is an oscillatory
row sum for the complete integer interval [U,4U]. -/

namespace Green64Analytic.CorrelationMellin

theorem source_actual_residual_sparse_of_complete_gram
    {ι : Type*} [Fintype ι] (times : ι → ℝ)
    (M R : Finset ℕ) (M0 R0 : ℕ) (alpha chi d : ℕ → ℂ)
    (sigma0 : ℝ) (A D B : ℝ)
    (hM0 : 0 < M0) (hR0 : 0 < R0)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hM : M ⊆ Finset.Icc M0 (2*M0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (ha : ∀ m ∈ M, ‖alpha m‖ ≤ A)
    (hchi : ∀ m ∈ M, ‖chi m‖ ≤ 1)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ D)
    (hrows : ∀ i : ι, ∑ k : ι,
      ‖∑ n ∈ Finset.Icc (M0*R0) (4*(M0*R0)),
        sourcePhase n (times i - times k)‖ ≤ B) :
    (∑ i : ι,
      ‖(∑ m ∈ M, alpha m * chi m * (m:ℂ)⁻¹ *
           sourcePhase m (sigma0+times i)) *
         (∑ r ∈ R, d r * (r:ℂ)⁻¹ * sourcePhase r (times i))‖^2) ≤
      B * (((A*D)/((M0*R0:ℕ):ℝ))^2 * ((4*(M0*R0):ℕ):ℝ) *
        (1+Real.log ((4*(M0*R0):ℕ):ℝ))^3) := by
  classical
  let U : ℕ := M0*R0
  let support : Finset ℕ := (M.product R).image (fun z => z.1*z.2)
  let coeff : ℕ → ℂ := sourceResidualProductCoeff M R
    (sourceAlphaCharacterCoefficient alpha chi sigma0)
    (sourceMarkedResidualCoefficient d)
  let padded : ℕ → ℂ := fun n => if n ∈ support then coeff n else 0
  have hPosM (m : ℕ) (hm : m ∈ M) : 0 < m :=
    lt_of_lt_of_le hM0 (Finset.mem_Icc.mp (hM hm)).1
  have hPosR (r : ℕ) (hr : r ∈ R) : 0 < r :=
    lt_of_lt_of_le hR0 (Finset.mem_Icc.mp (hR hr)).1
  have hSupport : support ⊆ Finset.Icc U (4*U) :=
    source_residual_product_dyadic_support M R M0 R0 hM hR
  have hPad (φ : ℕ → ℂ) :
      (∑ n ∈ Finset.Icc U (4*U), padded n * φ n) =
        (∑ n ∈ support, coeff n * φ n) := by
    calc
      _ = ∑ n ∈ support, padded n * φ n := by
        symm
        apply Finset.sum_subset hSupport
        intro n hn hnS
        have hsNot : n ∉ support := hnS
        simp [padded, hsNot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [padded, hn]
  have hPadNorm :
      (∑ n ∈ Finset.Icc U (4*U), ‖padded n‖^2) =
        (∑ n ∈ support, ‖coeff n‖^2) := by
    calc
      _ = ∑ n ∈ support, ‖padded n‖^2 := by
        symm
        apply Finset.sum_subset hSupport
        intro n hn hnS
        have hsNot : n ∉ support := hnS
        simp [padded, hsNot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [padded, hn]
  have hGram := source_full_integer_block_sparse_of_gram_rows
    (ι := ι) U (4*U) times padded B hB hrows
  have hSparse :
      (∑ i : ι,
        ‖∑ n ∈ support, coeff n * sourcePhase n (times i)‖^2) ≤
      B * (∑ n ∈ support, ‖coeff n‖^2) := by
    calc
      _ = ∑ i : ι,
          ‖∑ n ∈ Finset.Icc U (4*U), padded n * sourcePhase n (times i)‖^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hPad]
      _ ≤ B * (∑ n ∈ Finset.Icc U (4*U), ‖padded n‖^2) := hGram
      _ = _ := by rw [hPadNorm]
  have hL2 : (∑ n ∈ support, ‖coeff n‖^2) ≤
      ((A*D)/((M0*R0:ℕ):ℝ))^2 * ((4*(M0*R0):ℕ):ℝ) *
        (1+Real.log ((4*(M0*R0):ℕ):ℝ))^3 :=
    source_residual_true_dyadic_square_norm M R M0 R0 alpha chi d
      sigma0 A D hM0 hR0 hA hD hM hR ha hchi hd
  have hCollapse (i : ι) :
      (∑ m ∈ M, alpha m * chi m * (m:ℂ)⁻¹ *
           sourcePhase m (sigma0+times i)) *
         (∑ r ∈ R, d r * (r:ℂ)⁻¹ * sourcePhase r (times i)) =
      (∑ n ∈ support, coeff n * sourcePhase n (times i)) :=
    source_character_residual_collapse M R alpha chi d sigma0 (times i)
      hPosM hPosR
  calc
    _ = ∑ i : ι, ‖∑ n ∈ support, coeff n * sourcePhase n (times i)‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hCollapse]
    _ ≤ B * (∑ n ∈ support, ‖coeff n‖^2) := hSparse
    _ ≤ B * (((A*D)/((M0*R0:ℕ):ℝ))^2 * ((4*(M0*R0):ℕ):ℝ) *
         (1+Real.log ((4*(M0*R0):ℕ):ℝ))^3) :=
      mul_le_mul_of_nonneg_left hL2 hB
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualResidualUnconditionalGram -/

section

/-! Removes the postulated hrows from the existing four-factor residual
sparse mean-square theorem, using exact one-separated real times. -/
namespace Green64Analytic.CorrelationMellin

theorem source_actual_residual_sparse_unconditional_gram
    {ι : Type*} [Fintype ι] (times : ι → ℝ)
    (M R : Finset ℕ) (M0 R0 : ℕ) (alpha chi d : ℕ → ℂ)
    (sigma0 : ℝ) (A D Y : ℝ)
    (hM0 : 0 < M0) (hR0 : 0 < R0)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hY : 1 ≤ Y) (hUY : ((M0*R0:ℕ):ℝ) ≤ Y)
    (hTimes : ∀ i : ι, |times i| ≤ Y)
    (hSep : ∀ i j : ι, i ≠ j → 1 ≤ |times i-times j|)
    (hM : M ⊆ Finset.Icc M0 (2*M0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (ha : ∀ m ∈ M, ‖alpha m‖ ≤ A)
    (hchi : ∀ m ∈ M, ‖chi m‖ ≤ 1)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ D) :
    (∑ i : ι,
      ‖(∑ m ∈ M, alpha m * chi m * (m:ℂ)⁻¹ *
           sourcePhase m (sigma0+times i)) *
         (∑ r ∈ R, d r * (r:ℂ)⁻¹ * sourcePhase r (times i))‖^2) ≤
      (448*((M0*R0:ℕ):ℝ)*(1+Real.log (2*Y))+
         448*(Fintype.card ι:ℝ)*Real.sqrt Y) *
        (((A*D)/((M0*R0:ℕ):ℝ))^2 *
          ((4*(M0*R0):ℕ):ℝ) *
            (1+Real.log ((4*(M0*R0):ℕ):ℝ))^3) := by
  classical
  have hU : 1 ≤ M0*R0 :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hM0 hR0))
  let B : ℝ := 448*((M0*R0:ℕ):ℝ)*(1+Real.log (2*Y))+
         448*(Fintype.card ι:ℝ)*Real.sqrt Y
  have hLog : 0 ≤ Real.log (2*Y) :=
    Real.log_nonneg (by linarith : 1 ≤ 2*Y)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hrows : ∀ i : ι,
    ∑ k : ι,
      ‖∑ n ∈ Finset.Icc (M0*R0) (4*(M0*R0)),
        sourcePhase n (times i - times k)‖ ≤ B := by
    intro i
    have h := source_complete_gram_row_unconditional
      times (M0*R0) Y hU hY hUY hTimes hSep i
    convert h using 1 <;> ring
  exact source_actual_residual_sparse_of_complete_gram
    times M R M0 R0 alpha chi d sigma0 A D B
      hM0 hR0 hA hD hB hM hR ha hchi hd hrows
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalSparsePolylog -/

section

/-! The missing quantitative absorption in the original source sparse-residual
argument. The number of exceptional points is controlled independently by the
factorial short-prime moment; the residual length absorbs the Gram self term. -/
namespace Green64Analytic.CorrelationMellin

/-- Uniform Schur bound after paying for the self term `#J * sqrt Y`.
No Gram-row or residual bound is assumed as an input. -/
theorem source_sparse_gram_row_absorbed
    (U Y N A D : ℝ)
    (hU : 1 ≤ U) (hY : 1 ≤ Y)
    (hN : N * Real.sqrt Y ≤ U) :
    (448*U*(1+Real.log (2*Y)) +
       448*N*Real.sqrt Y) *
      (((A*D)/U)^2 * (4*U) *
       (1+Real.log (4*U))^3) ≤
    3584*(A*D)^2*(1+Real.log (2*Y))*
       (1+Real.log (4*U))^3 := by
  have hUp : 0 < U := by linarith
  have hYp : 0 < Y := by linarith
  have hlogY : 0 ≤ Real.log (2*Y) :=
    Real.log_nonneg (by linarith)
  have hlogU : 0 ≤ Real.log (4*U) :=
    Real.log_nonneg (by linarith)
  have hRow : 448*U*(1+Real.log (2*Y)) +
       448*N*Real.sqrt Y ≤
       896*U*(1+Real.log (2*Y)) := by
    nlinarith
  have hTail : 0 ≤ (((A*D)/U)^2 * (4*U) *
       (1+Real.log (4*U))^3) := by positivity
  calc
    _ ≤ (896*U*(1+Real.log (2*Y))) *
       (((A*D)/U)^2 * (4*U) *
        (1+Real.log (4*U))^3) :=
        mul_le_mul_of_nonneg_right hRow hTail
    _ = _ := by
      field_simp
      ring

/-- The source range `U ≤ Y` turns the logarithms into one universal
fourth-power budget, independent of the exceptional cardinality. -/
theorem source_sparse_log_budget
    (U Y A D : ℝ)
    (hU : 1 ≤ U) (hY : 1 ≤ Y) (hUY : U ≤ Y) :
    3584*(A*D)^2*(1+Real.log (2*Y))*
      (1+Real.log (4*U))^3 ≤
    3584*(A*D)^2*(1+Real.log (4*Y))^4 := by
  have hLp : 0 ≤ 1+Real.log (2*Y) := by
    have h := Real.log_nonneg (show (1:ℝ) ≤ 2*Y by linarith)
    linarith
  have hUp : 0 ≤ 1+Real.log (4*U) := by
    have h := Real.log_nonneg (show (1:ℝ) ≤ 4*U by linarith)
    linarith
  have hYbudget : 0 ≤ 1+Real.log (4*Y) := by
    have h := Real.log_nonneg (show (1:ℝ) ≤ 4*Y by linarith)
    linarith
  have hL : 1+Real.log (2*Y) ≤ 1+Real.log (4*Y) := by
    gcongr
    linarith
  have hU' : 1+Real.log (4*U) ≤ 1+Real.log (4*Y) := by
    gcongr
  calc
    _ ≤ 3584*(A*D)^2*(1+Real.log (4*Y))*
      (1+Real.log (4*Y))^3 := by gcongr
    _ = _ := by ring

/-- The complete actual alpha-character / residual polynomial, sampled at any
one-separated exceptional times, has a logarithmic fourth-power bound.
The cardinal bound comes from the genuine short-prime moment and is not
a new Gram-row or desired-conclusion hypothesis. -/
theorem source_actual_residual_sparse_polylog
    {ι : Type*} [Fintype ι] (times : ι → ℝ)
    (M R : Finset ℕ) (M0 R0 : ℕ) (alpha chi d : ℕ → ℂ)
    (sigma0 : ℝ) (A D Y ε : ℝ)
    (hM0 : 0 < M0) (hR0 : 0 < R0)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hY : 1 ≤ Y) (hUY : ((M0*R0:ℕ):ℝ) ≤ Y)
    (hcard : (Fintype.card ι:ℝ) ≤ Y^ε)
    (hsize : Y^(ε+(1/2:ℝ)) ≤ ((M0*R0:ℕ):ℝ))
    (hTimes : ∀ i : ι, |times i| ≤ Y)
    (hSep : ∀ i j : ι, i ≠ j → 1 ≤ |times i-times j|)
    (hM : M ⊆ Finset.Icc M0 (2*M0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (ha : ∀ m ∈ M, ‖alpha m‖ ≤ A)
    (hchi : ∀ m ∈ M, ‖chi m‖ ≤ 1)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ D) :
    (∑ i : ι,
      ‖(∑ m ∈ M, alpha m * chi m * (m:ℂ)⁻¹ *
           sourcePhase m (sigma0+times i)) *
         (∑ r ∈ R, d r * (r:ℂ)⁻¹ * sourcePhase r (times i))‖^2) ≤
      3584*(A*D)^2*(1+Real.log (4*Y))^4 := by
  have hU : 1 ≤ ((M0*R0:ℕ):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.mul_pos hM0 hR0))
  have hYpos : 0 < Y := by linarith
  have hcardSqrt :
      (Fintype.card ι:ℝ) * Real.sqrt Y ≤
      ((M0*R0:ℕ):ℝ) := by
    calc
      _ ≤ Y^ε * Real.sqrt Y :=
        mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg Y)
      _ = Y^(ε+(1/2:ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hYpos]
      _ ≤ _ := hsize
  have hGram := source_actual_residual_sparse_unconditional_gram
    times M R M0 R0 alpha chi d sigma0 A D Y
    hM0 hR0 hA hD hY hUY hTimes hSep
    hM hR ha hchi hd
  have hAbs := source_sparse_gram_row_absorbed
    (((M0*R0:ℕ):ℝ)) Y (Fintype.card ι:ℝ) A D
    hU hY hcardSqrt
  have hLog := source_sparse_log_budget
    (((M0*R0:ℕ):ℝ)) Y A D hU hY hUY
  calc
    _ ≤ (448*((M0*R0:ℕ):ℝ)*(1+Real.log (2*Y))+
           448*(Fintype.card ι:ℝ)*Real.sqrt Y) *
           (((A*D)/((M0*R0:ℕ):ℝ))^2 *
            ((4*(M0*R0):ℕ):ℝ) *
            (1+Real.log ((4*(M0*R0):ℕ):ℝ))^3) := hGram
    _ ≤ 3584*(A*D)^2*(1+Real.log (2*Y))*
         (1+Real.log (4*((M0*R0:ℕ):ℝ)))^3 := by
           simpa only [Nat.cast_mul, Nat.cast_ofNat] using hAbs
    _ ≤ 3584*(A*D)^2*(1+Real.log (4*Y))^4 := hLog
end Green64Analytic.CorrelationMellin

namespace Green64Analytic.CorrelationMellin

/-! Directly compose the genuine eventual factorial-moment count with
the unconditional physical-frequency Gram machinery. Fixed epsilon=1/20
leaves a strict gap below the source residual length exponent 3/5. -/
theorem eventually_source_exceptional_residual_sparse_polylog
    (a b As Cs : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ (P Y : ℕ),
      1 ≤ P → 1 ≤ Y →
      Real.exp (L ^ a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L ^ b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {κ : Type*} [Fintype κ] [DecidableEq κ],
      ∀ (witness sample : κ → ℝ) (s : Finset ℕ),
      (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      ∀ (bs : ℕ → ℂ),
      (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
      (∀ i, |witness i| ≤ (Y:ℝ)) →
      (∀ i j, i ≠ j → 1 ≤ |witness i-witness j|) →
      (∀ i, |sample i| ≤ (Y:ℝ)) →
      (∀ i j, i ≠ j → 1 ≤ |sample i-sample j|) →
      (∀ i : κ, L^(-As) ≤
        ‖∑ p : {p : ℕ // p ∈ s},
          (bs p.val * ((p.val:ℂ)⁻¹)) *
             sourcePhase p.val (witness i)‖) →
      ∀ (M R : Finset ℕ) (M0 R0 : ℕ)
        (alpha chi d : ℕ → ℂ) (sigma0 A D : ℝ),
      0 < M0 → 0 < R0 → 0 ≤ A → 0 ≤ D →
      ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →
      (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
      M ⊆ Finset.Icc M0 (2*M0) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ m ∈ M, ‖alpha m‖ ≤ A) →
      (∀ m ∈ M, ‖chi m‖ ≤ 1) →
      (∀ r ∈ R, ‖d r‖ ≤ D) →
      (∑ i : κ,
        ‖(∑ m ∈ M, alpha m * chi m * (m:ℂ)⁻¹ *
             sourcePhase m (sigma0+sample i)) *
           (∑ r ∈ R, d r * (r:ℂ)⁻¹ *
             sourcePhase r (sample i))‖^2) ≤
        3584*(A*D)^2*(1+Real.log (4*(Y:ℝ)))^4 := by
  have hCount := eventually_source_exceptional_count_uniform
    a b As Cs (1/20 : ℝ) ha hab hb hAs hCs (by norm_num)
  filter_upwards [hCount] with L hCL P Y hP hY hPmin hPmax
    hYmin hYmax κ _ _ witness sample s hp hs bs hbs
    hwt hwsep hst hssep hlarge
    M R M0 R0 alpha chi d sigma0 A D hM0 hR0 hA hD
    hUY hUlower hM hR hAlpha hChi hDcoeff
  have hCard : (Fintype.card κ:ℝ) ≤ (Y:ℝ)^(1/20:ℝ) :=
    hCL P Y hP hY hPmin hPmax hYmin hYmax
      witness s hp hs bs hbs hwt hwsep hlarge
  have hY1 : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hPow :
      (Y:ℝ)^((1/20:ℝ)+(1/2:ℝ)) ≤ (Y:ℝ)^(3/5:ℝ) := by
    gcongr
    norm_num
  exact source_actual_residual_sparse_polylog
    sample M R M0 R0 alpha chi d sigma0 A D (Y:ℝ) (1/20:ℝ)
    hM0 hR0 hA hD hY1 hUY hCard
    (hPow.trans hUlower) hst hssep hM hR hAlpha hChi hDcoeff
end Green64Analytic.CorrelationMellin

end

/-! ## SourceSupportedOriginalMoment -/

section

open scoped BigOperators

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 750000

/-- Real sixth divisor moment for any finite sequence whose SOURCE
coefficient support ends at M, independently of the bookkeeping N.
The only input is a true pointwise divisor-cube bound (not an energy
premise). We will next derive it from the original grouped coefficient. -/
theorem source_supported_divisor_cubed_moment434
    (N M : ℕ) (a : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hSupport : ∀ n ∈ Finset.Icc 1 N, M < n → a n = 0)
    (hPoint : ∀ n ∈ Finset.Icc 1 N,
      ‖a n‖ ≤ B * (n.divisors.card : ℝ)^3) :
    (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) ≤
      B^2 * (M:ℝ) * (1+Real.log (M:ℝ))^63 := by
  classical
  let F : Finset ℕ := (Finset.Icc 1 N).filter (fun n => n ≤ M)
  have hF : F ⊆ Finset.Ioc 0 M := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnN,hnM⟩
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Icc.mp hnN).1, hnM⟩
  have hEq :
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) =
      ∑ n ∈ F, ‖a n‖^2 := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 N,
          (if n ≤ M then ‖a n‖^2 else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hnm : n ≤ M
          · simp [hnm]
          · have hvanish := hSupport n hn (Nat.lt_of_not_ge hnm)
            simp [hnm, hvanish]
      _ = ∑ n ∈ F, ‖a n‖^2 := by
          simp only [F, Finset.sum_filter]
  have hTerm (n : ℕ) (hn : n ∈ F) :
      ‖a n‖^2 ≤ B^2 * (n.divisors.card:ℝ)^6 := by
    have hnN : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn).1
    calc
      _ ≤ (B * (n.divisors.card:ℝ)^3)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hPoint n hnN) 2
      _ = _ := by ring
  calc
    _ = ∑ n ∈ F, ‖a n‖^2 := hEq
    _ ≤ ∑ n ∈ F, B^2 * (n.divisors.card:ℝ)^6 :=
      Finset.sum_le_sum hTerm
    _ ≤ ∑ n ∈ Finset.Ioc 0 M,
         B^2 * (n.divisors.card:ℝ)^6 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hF
        (fun n _ _ => mul_nonneg (sq_nonneg _) (by positivity))
    _ = B^2 * (∑ n ∈ Finset.Ioc 0 M,
        (n.divisors.card:ℝ)^6) := by
      rw [Finset.mul_sum]
    _ ≤ B^2 * ((M:ℝ) * (1+Real.log (M:ℝ))^63) :=
      mul_le_mul_of_nonneg_left
        (source_tau6_summatory_log434 M) (sq_nonneg _)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalTailFromMoment -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1100000

/-- Uniform full two-sided REAL-time dyadic tail for a genuine finite
Dirichlet polynomial, controlled solely by a proven divisor-cube
coefficient cap AND its TRUE physical support M, not the huge
bookkeeping index N. No high/low, tail or energy assumptions. -/
theorem source_actual_supported_full_dyadic_tail434
    (N M : ℕ) (a : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hZero : ∀ n ∈ Finset.Icc 1 N, M < n → a n = 0)
    (hPoint : ∀ n ∈ Finset.Icc 1 N,
      ‖a n‖ ≤ B * (n.divisors.card : ℝ)^3)
    (h L : ℝ) (hh : 0 < h) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) :
    Summable (sourceLiteralPairedShellEnergy434 h L j
      (Finset.Icc 1 N) a) ∧
    (∑' r : ℕ, sourceLiteralPairedShellEnergy434 h L j
      (Finset.Icc 1 N) a r) ≤
      (4 * ((L^(j-2))⁻¹ *
        (L/h+16*(M:ℝ)*(1+Real.log M)))) *
        (B^2 * (M:ℝ) * (1+Real.log M)^63) := by
  obtain ⟨hSum,hTail⟩ :=
    source_literal_physical_complete_shell_trunc434
      N M a hZero h L hh hL j hj
  have hF : Finset.Icc 1 (min N M) ⊆
      Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1,
        (Finset.mem_Icc.mp hn).2.trans (min_le_left N M)⟩
  have hSq : (∑ n ∈ Finset.Icc 1 (min N M), ‖a n‖^2) ≤
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hF
      (fun n hn hnnot => sq_nonneg _)
  have hMoment := source_supported_divisor_cubed_moment434
    N M a B hB hZero hPoint
  have hLog : 0 ≤ Real.log (M:ℝ) :=
    Real.log_natCast_nonneg M
  have hFactor : 0 ≤
      4 * ((L^(j-2))⁻¹ *
        (L/h+16*(M:ℝ)*(1+Real.log M))) := by
    positivity
  constructor
  · exact hSum
  · calc
      _ ≤ (4 * ((L^(j-2))⁻¹ *
           (L/h+16*(M:ℝ)*(1+Real.log M)))) *
             (∑ n ∈ Finset.Icc 1 (min N M), ‖a n‖^2) := hTail
      _ ≤ (4 * ((L^(j-2))⁻¹ *
           (L/h+16*(M:ℝ)*(1+Real.log M)))) *
             (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) :=
        mul_le_mul_of_nonneg_left hSq hFactor
      _ ≤ (4 * ((L^(j-2))⁻¹ *
           (L/h+16*(M:ℝ)*(1+Real.log M)))) *
             (B^2 * (M:ℝ) * (1+Real.log M)^63) :=
        mul_le_mul_of_nonneg_left hMoment hFactor
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualCompleteTimeTail -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 750000

/-- The actual full real-time weighted Mellin tail, not merely the
sum of dyadic upper bounds, has a source-verified divisor moment bound.
Every + and - time-frequency shell is integrated over an unbounded
half-line, with the TRUE support M instead of bookkeeping N.
No source tail-saving assumption is introduced. -/
theorem source_actual_full_time_tail_supported434
    (N M : ℕ) (a : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hZero : ∀ n ∈ Finset.Icc 1 N, M < n → a n = 0)
    (hPoint : ∀ n ∈ Finset.Icc 1 N,
      ‖a n‖ ≤ B * (n.divisors.card : ℝ)^3)
    (h L : ℝ) (hh : 0 < h) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) :
    (∫ t in {t : ℝ | L/h ≤ |t|},
      ((1+h*|t|)^j)⁻¹ *
      ‖sourceLiteralFiniteMellin434 (Finset.Icc 1 N) a t‖^2) ≤
      (4 * ((L^(j-2))⁻¹ *
        (L/h+16*(M:ℝ)*(1+Real.log M)))) *
        (B^2 * (M:ℝ) * (1+Real.log M)^63) := by
  have hSame : (Finset.Icc 1 N) ⊆ Finset.Icc 1 N :=
    Finset.Subset.refl _
  have hIntegral := source_literal_real_tail_eq_entire_shell_sum434
    N (Finset.Icc 1 N) a hSame h L hh hL j hj
  have hBound := (source_actual_supported_full_dyadic_tail434
    N M a B hB hZero hPoint h L hh hL j hj).2
  exact hIntegral.trans_le hBound
end Green64Analytic.CorrelationSquare

end

/-! ## TruncatedAggregate -/

section

set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Green64Analytic.LastPrimeErrors

/-- Exact quantitative TOTAL PNT2 error on a fixed positive-margin
prefix region. This is an unconditional arithmetic inequality about
the PNT error *majorant*, not a conjectural simplex limit.

All ordered prefixes, including lists with repeated primes, are allowed.
The only prefix restriction is their genuine natural product. -/
theorem truncated_aggregate_PNT_errors
    (G : Finset (List ℕ)) (b δ L C : ℝ)
    (hb : 0 ≤ b) (hδ : 0 < δ) (hL : 0 < L)
    (hC : 0 ≤ C)
    (hq : ∀ pre ∈ G, 0 < (pre.prod : ℝ))
    (hcap : ∀ pre ∈ G, (pre.prod : ℝ) ≤
      Real.exp ((1-b-δ)*L)) :
    (∑ pre ∈ G,
      (C * (Real.exp L/(pre.prod:ℝ))/
          (Real.log (Real.exp L/(pre.prod:ℝ)))^2 +
       (Real.exp (b*L)+1))) ≤
    (C*Real.exp L/(((b+δ)*L)^2) +
      (Real.exp (b*L)+1)*Real.exp ((1-b-δ)*L)) *
      ∑ pre ∈ G, (pre.prod:ℝ)⁻¹ := by
  have hh := truncated_prefix_error_inputs b δ L hb hδ hL
  apply finite_aggregate_PNT_error G
    (Real.exp L) (Real.exp (b*L)) ((b+δ)*L)
    (Real.exp ((1-b-δ)*L)) C
    (Real.exp_pos _).le hh.2.2 hh.1 hh.2.1 hC
    hq hcap
  intro pre hpre
  exact (truncated_prefix_last_prime_room b δ L (pre.prod:ℝ)
    hb hδ hL (hq pre hpre) (hcap pre hpre)).1

end Green64Analytic.LastPrimeErrors

end

/-! ## NormalizedErrorRate -/

section

set_option maxHeartbeats 1600000
open Filter Topology
namespace Green64Analytic.LastPrimeErrors

/-- The explicit coefficient after normalizing source prime counts
by L/exp(L), with fixed b and δ before the large parameter L. -/
noncomputable def normalizedErrorRate (b δ C L : ℝ) : ℝ :=
    C / ((b+δ)^2 * L) +
      L * Real.exp (-δ*L) +
      L * Real.exp (-(b+δ)*L)

/-- Exact quantitative algebra, no asymptotic handwave or unspecified o(1).
The two exponentials separate excluded-small-prime errors. -/
theorem normalizedErrorRate_identity
    (b δ C L : ℝ)
    (hb : 0 ≤ b) (hδ : 0 < δ) (hL : 0 < L) :
    (L / Real.exp L) *
      (C * Real.exp L / (((b+δ)*L)^2) +
        (Real.exp (b*L)+1) * Real.exp ((1-b-δ)*L)) =
    normalizedErrorRate b δ C L := by
  have hbd : 0 < b+δ := by linarith
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hbd0 : b+δ ≠ 0 := ne_of_gt hbd
  have hexp0 : Real.exp L ≠ 0 := Real.exp_ne_zero _
  have hA :
      (L/Real.exp L) *
        (C*Real.exp L/(((b+δ)*L)^2)) =
      C/((b+δ)^2*L) := by
    field_simp
  have hexp1 :
      Real.exp (b*L)*Real.exp ((1-b-δ)*L) =
        Real.exp L * Real.exp (-δ*L) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp2 :
      Real.exp ((1-b-δ)*L) =
        Real.exp L * Real.exp (-(b+δ)*L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hB :
      (L/Real.exp L) *
        ((Real.exp (b*L)+1) * Real.exp ((1-b-δ)*L)) =
        L*Real.exp (-δ*L) + L*Real.exp (-(b+δ)*L) := by
    calc
      _ = L*(Real.exp (b*L)*Real.exp ((1-b-δ)*L))/Real.exp L +
          L*Real.exp ((1-b-δ)*L)/Real.exp L := by ring
      _ = _ := by
        rw [hexp1,hexp2]
        field_simp
  unfold normalizedErrorRate
  rw [mul_add, hA, hB]
  ring

 
/-- For each fixed positive truncation gap, the exact absolute rate
C/((b+δ)^2 L) + L*exp(-δL) + L*exp(-(b+δ)L)
vanishes. The last two are precisely the accumulated excluded-small-prime
cost rather than a guessed o(1). -/
theorem normalizedErrorRate_tendsto_zero
    (b δ C : ℝ) (hb : 0 ≤ b) (hδ : 0 < δ) :
    Tendsto (fun L : ℝ => normalizedErrorRate b δ C L)
      atTop (𝓝 0) := by
  have hInv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hA :
      Tendsto (fun L : ℝ => C / ((b+δ)^2 * L))
        atTop (𝓝 0) := by
    have hh := hInv.const_mul (C/(b+δ)^2)
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm,
      mul_left_comm, mul_assoc] using hh
  have hB :
      Tendsto (fun L : ℝ => L*Real.exp (-δ*L))
        atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 δ hδ)
  have hbd : 0 < b+δ := by linarith
  have hD :
      Tendsto (fun L : ℝ => L*Real.exp (-(b+δ)*L))
        atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (b+δ) hbd)
  simpa [normalizedErrorRate] using (hA.add hB).add hD

/-- The concrete source TOTAL PNT2 error after multiplying by
log x/x. No upper bound on reciprocal-prefix mass is smuggled in:
the exact finite mass remains visibly on the right. -/
theorem normalized_truncated_aggregate_PNT_errors
    (G : Finset (List ℕ)) (b δ L C : ℝ)
    (hb : 0 ≤ b) (hδ : 0 < δ) (hL : 0 < L)
    (hC : 0 ≤ C)
    (hq : ∀ pre ∈ G, 0 < (pre.prod : ℝ))
    (hcap : ∀ pre ∈ G, (pre.prod : ℝ) ≤
      Real.exp ((1-b-δ)*L)) :
    (L / Real.exp L) *
      (∑ pre ∈ G,
        (C*(Real.exp L/(pre.prod:ℝ)) /
          (Real.log (Real.exp L/(pre.prod:ℝ)))^2 +
          (Real.exp (b*L)+1))) ≤
      normalizedErrorRate b δ C L *
        (∑ pre ∈ G, (pre.prod:ℝ)⁻¹) := by
  have hnorm : 0 ≤ L/Real.exp L :=
    div_nonneg hL.le (Real.exp_pos _).le
  have hbound :=
    truncated_aggregate_PNT_errors G b δ L C hb hδ hL hC hq hcap
  calc
    _ ≤ (L/Real.exp L) *
      ((C*Real.exp L/(((b+δ)*L)^2) +
        (Real.exp (b*L)+1)*Real.exp ((1-b-δ)*L)) *
        ∑ pre ∈ G, (pre.prod:ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hbound hnorm
    _ = normalizedErrorRate b δ C L *
        (∑ pre ∈ G, (pre.prod:ℝ)⁻¹) := by
      rw [← mul_assoc,
        normalizedErrorRate_identity b δ C L hb hδ hL]

end Green64Analytic.LastPrimeErrors

end

/-! ## ReciprocalPrefixMass -/

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Green64Analytic.LastPrimeErrors

/-- An exact product-alphabet inequality for the reciprocal mass of
any subset of ordered prime tuples. Repeated primes are INCLUDED.
No Euler product asymptotic or simplex measure theorem is assumed. -/
theorem ordered_reciprocal_mass_le_power
    (G : Finset (List ℕ)) (P : Finset ℕ) (ell : ℕ)
    (hlen : ∀ l ∈ G, l.length = ell)
    (hP : ∀ l ∈ G, ∀ p ∈ l, p ∈ P) :
    (∑ l ∈ G, (l.prod : ℝ)⁻¹) ≤
      (∑ p ∈ P, (p : ℝ)⁻¹) ^ ell := by
  classical
  let U : Finset (Fin ell → ℕ) :=
    Fintype.piFinset (fun _ : Fin ell => P)
  have hsub : G ⊆ U.image List.ofFn := by
    intro l hl
    have hL : l.length = ell := hlen l hl
    rcases hL with rfl
    let f : Fin l.length → ℕ := fun i => l.get i
    have hmemf : f ∈ U := by
      apply Fintype.mem_piFinset.mpr
      intro i
      exact hP l hl (f i) (List.get_mem l i)
    exact Finset.mem_image.mpr ⟨f,hmemf,List.ofFn_get l⟩
  have hbound :
      (∑ l ∈ G, (l.prod : ℝ)⁻¹) ≤
      ∑ l ∈ U.image List.ofFn, (l.prod : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro l hl hnot
    positivity
  have hfull :
      (∑ l ∈ U.image List.ofFn, (l.prod : ℝ)⁻¹) =
      (∑ p ∈ P, (p : ℝ)⁻¹) ^ ell := by
    calc
      _ = ∑ f ∈ U, ∏ i : Fin ell, ((f i : ℝ)⁻¹) := by
        rw [Finset.sum_image List.ofFn_injective.injOn]
        apply Finset.sum_congr rfl
        intro f hf
        rw [List.prod_ofFn, Nat.cast_prod]
        rw [Finset.prod_inv_distrib]
      _ = (∑ p ∈ P, (p : ℝ)⁻¹) ^ ell := by
        exact (Finset.sum_pow' P (fun p => (p : ℝ)⁻¹) ell).symm
  exact hbound.trans_eq hfull

end Green64Analytic.LastPrimeErrors

end

/-! ## ActualPrimeReciprocalBound -/

section

set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Green64Analytic.LastPrimeErrors

/-- Exactly the natural-prime alphabet between x^b and x, where x=exp L.
Both strict lower and inclusive upper cutoffs are retained. -/
noncomputable def actualPrimeAlphabet (b L : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp (b*L)⌋₊ ⌊Real.exp L⌋₊).filter Nat.Prime

theorem actualPrimeAlphabet_sum_eq_source (b L : ℝ) :
    (∑ p ∈ actualPrimeAlphabet b L, (p:ℝ)⁻¹) =
      Green64Analytic.ReciprocalPrimeGrid.reciprocalPrimeCell L b 1 := by
  classical
  simp only [actualPrimeAlphabet,
    Green64Analytic.ReciprocalPrimeGrid.reciprocalPrimeCell, one_mul]
  rw [Finset.sum_filter]

/-- Replay the actual source prime reciprocal PNT estimate,
and convert the two-sided discrepancy to a one-sided mass bound. -/
theorem actualPrimeAlphabet_PNT2_upper
    (b L C : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hL : 1 ≤ b*L) (hC : 0 ≤ C)
    (hPNT : ∀ t, Real.exp (b*L) ≤ t →
      |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
        C*t/(Real.log t)^2) :
    (∑ p ∈ actualPrimeAlphabet b L, (p:ℝ)⁻¹) ≤
      Real.log (1/b) +
        (C*(2+(1-b)*L)/(b*L)^2 + (b*L)⁻¹) := by
  have hh := Green64Analytic.ReciprocalPrimeGrid.uniform_prime_reciprocal_log_error
    b 1 L C hb hL hC hPNT b 1 le_rfl hb1 le_rfl
  have hh' :
      |(∑ p ∈ actualPrimeAlphabet b L, (p:ℝ)⁻¹) - Real.log (1/b)| ≤
        C*(2+(1-b)*L)/(b*L)^2 + (b*L)⁻¹ := by
    simpa only [actualPrimeAlphabet, Finset.sum_filter, one_mul] using hh
  have hupper := (abs_le.mp hh').2
  linarith

end Green64Analytic.LastPrimeErrors

end

/-! ## ReciprocalMassPNT -/

section

set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Green64Analytic.LastPrimeErrors

/-- Quantitative bounded mass of ANY finite family of ordered prime
prefixes of length ell, with every coordinate belonging to the
actual natural-prime alphabet x^b < p <= x (x=exp L).
The complete PNT2-to-reciprocal-measure proof is replayed, not
assumed from a candidate claim. Repetitions are allowed. -/
theorem ordered_prefix_reciprocal_PNT_upper
    (G : Finset (List ℕ)) (ell : ℕ)
    (b L C : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hL : 1 ≤ b*L) (hC : 0 ≤ C)
    (hlen : ∀ l ∈ G, l.length = ell)
    (hletters : ∀ l ∈ G, ∀ p ∈ l, p ∈ actualPrimeAlphabet b L)
    (hPNT : ∀ t, Real.exp (b*L) ≤ t →
      |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
        C*t/(Real.log t)^2) :
    (∑ l ∈ G, (l.prod:ℝ)⁻¹) ≤
      (Real.log (1/b) +
        (C*(2+(1-b)*L)/(b*L)^2 + (b*L)⁻¹)) ^ ell := by
  let S : ℝ := ∑ p ∈ actualPrimeAlphabet b L, (p:ℝ)⁻¹
  have hS : 0 ≤ S := Finset.sum_nonneg (by intro p hp; positivity)
  have hSupper : S ≤ Real.log (1/b) +
       (C*(2+(1-b)*L)/(b*L)^2 + (b*L)⁻¹) :=
    actualPrimeAlphabet_PNT2_upper b L C hb hb1 hL hC hPNT
  have hpow : S ^ ell ≤
      (Real.log (1/b) +
        (C*(2+(1-b)*L)/(b*L)^2 + (b*L)⁻¹)) ^ ell := by
    exact pow_le_pow_left₀ hS hSupper ell
  exact (ordered_reciprocal_mass_le_power G
    (actualPrimeAlphabet b L) ell hlen hletters).trans hpow

end Green64Analytic.LastPrimeErrors

end

/-! ## UniformPrefixMassLimit -/

section

set_option maxHeartbeats 1700000
open Filter Topology
namespace Green64Analytic.LastPrimeErrors

noncomputable def primeGridError (b C L : ℝ) : ℝ :=
  C*(2+(1-b)*L)/(b*L)^2 + (b*L)⁻¹

theorem primeGridError_tendsto_zero
    (b C : ℝ) (hb : 0 < b) :
    Tendsto (fun L : ℝ => primeGridError b C L) atTop (𝓝 0) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hI : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hI2 : Tendsto (fun L : ℝ => (L⁻¹)^2) atTop (𝓝 0) := by
    simpa using hI.pow 2
  have hsum : Tendsto
      (fun L : ℝ =>
        ((2*C)/b^2)*(L⁻¹)^2 +
        (C*(1-b)/b^2+1/b)*L⁻¹)
      atTop (𝓝 0) := by
    simpa using
      ((hI2.const_mul ((2*C)/b^2)).add
        (hI.const_mul (C*(1-b)/b^2+1/b)))
  have hEq : (fun L : ℝ => primeGridError b C L) =ᶠ[atTop]
      (fun L : ℝ =>
        ((2*C)/b^2)*(L⁻¹)^2 +
        (C*(1-b)/b^2+1/b)*L⁻¹) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    have hL0 : L ≠ 0 := ne_of_gt hL
    unfold primeGridError
    field_simp
    ring
  exact hsum.congr' hEq.symm

end Green64Analytic.LastPrimeErrors

end

/-! ## CompleteAggregatePNT -/

section

set_option maxHeartbeats 1800000
open Filter Topology
namespace Green64Analytic.LastPrimeErrors

/-- Quantitative fully source-exact normalized aggregate error bound.
The PNT2 input is precisely the original quantified classical
prime-remainder theorem; bounded reciprocal mass is now proved
from actual natural-prime sums, not assumed as a premise.
Repeated primes in ordered prefixes are permitted. -/
theorem normalized_aggregate_with_actual_PNT2
    (G : Finset (List ℕ)) (ell : ℕ) (b δ L C : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hδ : 0 < δ) (hL : 0 < L) (hL1 : 1 ≤ b*L)
    (hC : 0 ≤ C)
    (hq : ∀ pre ∈ G, 0 < (pre.prod : ℝ))
    (hcap : ∀ pre ∈ G, (pre.prod : ℝ) ≤
      Real.exp ((1-b-δ)*L))
    (hlen : ∀ pre ∈ G, pre.length = ell)
    (hletters : ∀ pre ∈ G, ∀ p ∈ pre,
      p ∈ actualPrimeAlphabet b L)
    (hPNT : ∀ t, Real.exp (b*L) ≤ t →
      |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
        C*t/(Real.log t)^2) :
    (L / Real.exp L) *
      (∑ pre ∈ G,
        (C*(Real.exp L/(pre.prod:ℝ)) /
          (Real.log (Real.exp L/(pre.prod:ℝ)))^2 +
          (Real.exp (b*L)+1))) ≤
    normalizedErrorRate b δ C L *
      (Real.log (1/b)+primeGridError b C L)^ell := by
  have hbase := normalized_truncated_aggregate_PNT_errors G
    b δ L C hb.le hδ hL hC hq hcap
  have hmass := ordered_prefix_reciprocal_PNT_upper
    G ell b L C hb hb1 hL1 hC hlen hletters hPNT
  have hrate : 0 ≤ normalizedErrorRate b δ C L := by
    dsimp [normalizedErrorRate]
    have hbd : 0 < b+δ := by linarith
    positivity
  have hproduct := mul_le_mul_of_nonneg_left hmass hrate
  exact hbase.trans (by
    simpa only [primeGridError] using hproduct)


-- Preserve the exact historical data definition and its inert delta parameter.
set_option linter.unusedVariables false in
/-- Normalized exact error majorant from the ACTUAL discrete last-prime
PNT bound; the variable G(L) can be any finite family of ordered tuples,
and no squarefree restriction is introduced. -/
noncomputable def normalizedActualAggregate
    (G : ℝ → Finset (List ℕ)) (b δ C L : ℝ) : ℝ :=
  (L/Real.exp L) *
    (∑ pre ∈ G L,
      (C*(Real.exp L/(pre.prod:ℝ)) /
        (Real.log (Real.exp L/(pre.prod:ℝ)))^2 +
        (Real.exp (b*L)+1)))

/-- FINISHED aggregate last-prime error theorem. For fixed b,δ>0
and fixed prefix length ell, a family G_L of legal prefixes
a positive distance δ inside the product boundary has total
PNT2 error o(exp L/L), provided only the precise classical
PNT2 remainder input. The bounded reciprocal-prefix mass is
derived from the replayed prime-grid theorem, not assumed. -/
theorem normalizedActualAggregate_tendsto_zero
    (G : ℝ → Finset (List ℕ)) (ell : ℕ)
    (b δ C : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hlegal : ∀ᶠ L : ℝ in atTop,
       ∀ pre ∈ G L,
         0 < (pre.prod:ℝ) ∧
         (pre.prod:ℝ) ≤ Real.exp ((1-b-δ)*L) ∧
         pre.length = ell ∧
         (∀ p ∈ pre, p ∈ actualPrimeAlphabet b L))
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (b*L) ≤ t →
         |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
           C*t/(Real.log t)^2) :
    Tendsto (fun L : ℝ => normalizedActualAggregate G b δ C L)
      atTop (𝓝 0) := by
  have hR : Tendsto (fun L : ℝ => normalizedErrorRate b δ C L)
      atTop (𝓝 0) :=
    normalizedErrorRate_tendsto_zero b δ C hb.le hδ
  have hE : Tendsto (fun L : ℝ => primeGridError b C L)
      atTop (𝓝 0) :=
    primeGridError_tendsto_zero b C hb
  have hB : Tendsto
      (fun L : ℝ => Real.log (1/b)+primeGridError b C L)
      atTop (𝓝 (Real.log (1/b))) := by
    simpa using (tendsto_const_nhds.add hE)
  have hUp : Tendsto
      (fun L : ℝ => normalizedErrorRate b δ C L *
       (Real.log (1/b)+primeGridError b C L)^ell)
      atTop (𝓝 0) := by
    simpa using hR.mul (hB.pow ell)
  have hNonneg : ∀ᶠ L : ℝ in atTop,
      0 ≤ normalizedActualAggregate G b δ C L := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    unfold normalizedActualAggregate
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro pre hp
      have hmain :
        0 ≤ C*(Real.exp L/(pre.prod:ℝ)) /
         (Real.log (Real.exp L/(pre.prod:ℝ)))^2 := by
           positivity
      have hrest : 0 ≤ Real.exp (b*L)+1 := by positivity
      linarith
  have hUpper : ∀ᶠ L : ℝ in atTop,
      normalizedActualAggregate G b δ C L ≤
      normalizedErrorRate b δ C L *
       (Real.log (1/b)+primeGridError b C L)^ell := by
    filter_upwards [eventually_ge_atTop (max 1 (1/b)),
      hlegal,hPNT] with L hL hleg hPNT'
    have hL0 : 0 < L := by
      have h := (le_max_left (1:ℝ) (1/b)).trans hL
      linarith
    have hLb : 1/b ≤ L :=
      (le_max_right (1:ℝ) (1/b)).trans hL
    have hL1 : 1 ≤ b*L := by
      have hm := mul_le_mul_of_nonneg_left hLb hb.le
      have hbne : b ≠ 0 := ne_of_gt hb
      field_simp at hm
      linarith
    have hq : ∀ pre ∈ G L, 0 < (pre.prod:ℝ) :=
      fun pre hp => (hleg pre hp).1
    have hcap : ∀ pre ∈ G L,
        (pre.prod:ℝ) ≤ Real.exp ((1-b-δ)*L) :=
      fun pre hp => (hleg pre hp).2.1
    have hlen : ∀ pre ∈ G L, pre.length = ell :=
      fun pre hp => (hleg pre hp).2.2.1
    have hletters : ∀ pre ∈ G L, ∀ p ∈ pre,
        p ∈ actualPrimeAlphabet b L :=
      fun pre hp => (hleg pre hp).2.2.2
    simpa only [normalizedActualAggregate] using
      normalized_aggregate_with_actual_PNT2 (G L) ell b δ L C
        hb hb1 hδ hL0 hL1 hC hq hcap hlen hletters hPNT'
  exact squeeze_zero' hNonneg hUpper hUp

end Green64Analytic.LastPrimeErrors

end

/-! ## SourceTruncatedPrefixes -/

section

set_option maxHeartbeats 1800000
open Filter Topology
namespace Green64Analytic.LastPrimeErrors

/-- The literal source ordered prefix family on the frozen truncated
logarithmic region. Only b,δ and the tuple length are frozen before L;
the actual natural primes and their products vary with x=exp L.
Repeated prime factors are included, with no squarefree filter. -/
noncomputable def truncatedSourcePrefixes
    (ell : ℕ) (b δ L : ℝ) : Finset (List ℕ) := by
  classical
  exact (Green64Analytic.OrderedPrimeRough.allPrimeTuples ell
    (Real.exp (b*L)) (Real.exp L)).filter
    (fun pre => (pre.prod:ℝ) ≤ Real.exp ((1-b-δ)*L))

theorem truncatedSourcePrefixes_legal
    (ell : ℕ) (b δ L : ℝ) :
    ∀ pre ∈ truncatedSourcePrefixes ell b δ L,
         0 < (pre.prod:ℝ) ∧
         (pre.prod:ℝ) ≤ Real.exp ((1-b-δ)*L) ∧
         pre.length = ell ∧
         (∀ p ∈ pre, p ∈ actualPrimeAlphabet b L) := by
  classical
  intro pre hpre
  have hh : pre ∈
      Green64Analytic.OrderedPrimeRough.allPrimeTuples ell
        (Real.exp (b*L)) (Real.exp L) ∧
      (pre.prod:ℝ) ≤ Real.exp ((1-b-δ)*L) := by
    simpa only [truncatedSourcePrefixes, Finset.mem_filter] using hpre
  have hinfo :=
    (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff ell
      (Real.exp (b*L)) (Real.exp L) (Real.exp_pos _).le pre).mp hh.1
  have hprod : (0:ℝ) < (pre.prod:ℝ) := by
    exact_mod_cast hinfo.2.2.1
  refine ⟨hprod,hh.2,hinfo.1,?_⟩
  intro p hp
  have hpinfo := hinfo.2.1 p hp
  have hple : p ≤ pre.prod := Nat.le_of_dvd hinfo.2.2.1 (List.dvd_prod hp)
  have hpr : (p:ℝ) ≤ Real.exp L := by
    exact (show (p:ℝ) ≤ (pre.prod:ℝ) by exact_mod_cast hple).trans
      hinfo.2.2.2
  have hpos : Real.exp (b*L) < (p:ℝ) := hpinfo.2
  have hfloorLow : (⌊Real.exp (b*L)⌋₊:ℝ) < p :=
    (Nat.floor_le (Real.exp_pos _).le).trans_lt hpos
  have hlower : ⌊Real.exp (b*L)⌋₊ < p := by
    exact_mod_cast hfloorLow
  have hupper : p ≤ ⌊Real.exp L⌋₊ := Nat.le_floor hpr
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Ioc.mpr ⟨hlower,hupper⟩,hpinfo.1⟩


/-- Exact source truncated tuple instance of the checked aggregate PNT2 error limit.
Repeated primes are allowed, with actual x^b cutoffs and a fixed margin delta. -/
theorem actual_source_aggregate_PNT_error_tendsto_zero
    (ell : ℕ) (b δ C : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hPNT : ∀ᶠ L : ℝ in atTop,
      ∀ t, Real.exp (b*L) ≤ t →
       |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
         C*t/(Real.log t)^2) :
    Tendsto (fun L : ℝ =>
      normalizedActualAggregate
        (fun L => truncatedSourcePrefixes ell b δ L) b δ C L)
      atTop (𝓝 0) := by
  apply normalizedActualAggregate_tendsto_zero
    (fun L => truncatedSourcePrefixes ell b δ L)
    ell b δ C hb hb1 hδ hC
  · exact Filter.Eventually.of_forall
      (fun L => truncatedSourcePrefixes_legal ell b δ L)
  · exact hPNT

end Green64Analytic.LastPrimeErrors

end

/-! ## WeightedGrid -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- A nonnegative frozen cell weight does not amplify mass discrepancy
by more than its uniform bound. The set may be any finite selection. -/
theorem weighted_grid_union_discrepancy {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w f g : ι → ℝ) (W δ : ℝ)
    (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hw0 : ∀ c ∈ s, 0 ≤ w c)
    (hw : ∀ c ∈ s, w c ≤ W)
    (hcell : ∀ c ∈ s, |f c - g c| ≤ δ) :
    |(∑ c ∈ s, w c * f c) - (∑ c ∈ s, w c * g c)| ≤
      (s.card : ℝ) * W * δ := by
  rw [← Finset.sum_sub_distrib]
  have heq : (∑ c ∈ s, (w c * f c - w c * g c)) =
      ∑ c ∈ s, w c * (f c - g c) := by
    apply Finset.sum_congr rfl
    intro c hc
    ring
  rw [heq]
  calc
    |∑ c ∈ s, w c * (f c - g c)| ≤
      ∑ c ∈ s, |w c * (f c - g c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ s, W * δ := by
      apply Finset.sum_le_sum
      intro c hc
      rw [abs_mul, abs_of_nonneg (hw0 c hc)]
      exact (mul_le_mul_of_nonneg_left (hcell c hc) (hw0 c hc)).trans
        (mul_le_mul (hw c hc) (le_refl δ) hδ hW)
    _ = (s.card : ℝ) * W * δ := by simp [mul_assoc]

/-- Arbitrary cell weights, not only indicators, retain a dimension-uniform
finite-grid product estimate. This is the exact weighted counterpart of
the previously checked compact_grid_discrepancy theorem. -/
theorem weighted_fixed_grid_from_interval_errors (d k : ℕ)
    (μ ν : Fin d → Fin k → ℝ) (H ε W : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (hW : 0 ≤ W)
    (hμ0 : ∀ i j, 0 ≤ μ i j)
    (hν0 : ∀ i j, 0 ≤ ν i j) (hν : ∀ i j, ν i j ≤ H)
    (hgap : ∀ i j, |μ i j - ν i j| ≤ ε)
    (S : Finset (Fin d → Fin k)) (w : (Fin d → Fin k) → ℝ)
    (hw0 : ∀ c ∈ S, 0 ≤ w c)
    (hw : ∀ c ∈ S, w c ≤ W) :
    |(∑ c ∈ S, w c * ∏ i : Fin d, μ i (c i)) -
      (∑ c ∈ S, w c * ∏ i : Fin d, ν i (c i))| ≤
      (k : ℝ) ^ d * W *
        ((d : ℝ) * ε * (H + ε) ^ (d - 1)) := by
  let K := H + ε
  let δ := (d : ℝ) * ε * K ^ (d - 1)
  have hK : 0 ≤ K := add_nonneg hH hε
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hμ (i : Fin d) (j : Fin k) : μ i j ≤ K := by
    have hh := (abs_le.mp (hgap i j)).2
    dsimp [K]
    linarith [hν i j]
  have hν' (i : Fin d) (j : Fin k) : ν i j ≤ K := by
    dsimp [K]
    linarith [hν i j]
  have hcell (c : Fin d → Fin k) :
      |(∏ i : Fin d, μ i (c i)) -
        (∏ i : Fin d, ν i (c i))| ≤ δ := by
    simpa only [δ, Finset.card_univ, Fintype.card_fin] using
      product_discrepancy (Finset.univ : Finset (Fin d))
        (fun i => μ i (c i)) (fun i => ν i (c i))
        K ε hK hε
        (by intro i hi; exact hμ0 i (c i))
        (by intro i hi; exact hμ i (c i))
        (by intro i hi; exact hν0 i (c i))
        (by intro i hi; exact hν' i (c i))
        (by intro i hi; exact hgap i (c i))
  have hweighted :=
    weighted_grid_union_discrepancy S w
      (fun c => ∏ i : Fin d, μ i (c i))
      (fun c => ∏ i : Fin d, ν i (c i))
      W δ hW hδ hw0 hw (fun c hc => hcell c)
  have hcard : (S.card : ℝ) ≤ (k : ℝ) ^ d := by
    have hn : S.card ≤ (Finset.univ : Finset (Fin d → Fin k)).card :=
      Finset.card_le_card (Finset.subset_univ S)
    simpa [Fintype.card_fun] using (Nat.cast_le.mpr hn :
      (S.card : ℝ) ≤
      ((Finset.univ : Finset (Fin d → Fin k)).card : ℝ))
  exact hweighted.trans (by
    have hh := mul_le_mul_of_nonneg_right hcard (mul_nonneg hW hδ)
    simpa only [δ, K, mul_assoc] using hh)

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## WeightedPrimeGrid -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Explicit discrepancy from the actual PNT2' input on a fixed
positive logarithmic compact. -/
noncomputable def pntGridError (a M C L : ℝ) : ℝ :=
  C * (2 + (M - a) * L) / (a * L) ^ 2 + (a * L)⁻¹

/-- The PNT2' bound applies to ANY bounded nonnegative cell weights
and ANY cell selection, so the latter can even vary with L.
Only the endpoints u,v and the dimensional grid are frozen. -/
theorem weighted_prime_grid_uniform_bound (d k : ℕ)
    (a M L C W : ℝ) (u v : Fin k → ℝ)
    (ha : 0 < a) (haM : a ≤ M) (hL : 1 ≤ a * L)
    (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hPNT : ∀ t, Real.exp (a * L) ≤ t →
       |primeRemainder t| ≤ C * t / (Real.log t) ^ 2)
    (S : Finset (Fin d → Fin k))
    (w : (Fin d → Fin k) → ℝ)
    (hw0 : ∀ c ∈ S, 0 ≤ w c)
    (hw : ∀ c ∈ S, w c ≤ W) :
    |(∑ c ∈ S, w c *
          ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))) -
      (∑ c ∈ S, w c *
          ∏ i : Fin d, logCell (u (c i)) (v (c i)))| ≤
       (k : ℝ) ^ d * W * ((d : ℝ) * pntGridError a M C L *
         (Real.log (M / a) + pntGridError a M C L) ^ (d - 1)) := by
  let H := Real.log (M / a)
  let ε := pntGridError a M C L
  have hH : 0 ≤ H := by
    dsimp [H]
    apply Real.log_nonneg
    exact (le_div_iff₀ ha).mpr (by simpa using haM)
  have hLp : 0 < L := by
    by_contra hn
    have hn' : L ≤ 0 := le_of_not_gt hn
    have hNonpos : a * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hn'
    linarith
  have hε : 0 ≤ ε := by
    dsimp [ε, pntGridError]
    have hsub : 0 ≤ M - a := sub_nonneg.mpr haM
    positivity
  have hμ0 (i : Fin d) (j : Fin k) :
      0 ≤ reciprocalPrimeCell L (u j) (v j) :=
    reciprocalPrimeCell_nonneg L (u j) (v j)
  have hν0 (i : Fin d) (j : Fin k) :
      0 ≤ logCell (u j) (v j) :=
    (logCell_bounds a M (u j) (v j) ha
      (hcells j).1 (hcells j).2.1 (hcells j).2.2).1
  have hν (i : Fin d) (j : Fin k) :
      logCell (u j) (v j) ≤ H :=
    (logCell_bounds a M (u j) (v j) ha
      (hcells j).1 (hcells j).2.1 (hcells j).2.2).2
  have hgap (i : Fin d) (j : Fin k) :
      |reciprocalPrimeCell L (u j) (v j) -
          logCell (u j) (v j)| ≤ ε := by
    simpa only [ε, pntGridError, reciprocalPrimeCell, logCell] using
      (uniform_prime_reciprocal_log_error a M L C
        ha hL hC hPNT (u j) (v j)
        (hcells j).1 (hcells j).2.1 (hcells j).2.2)
  simpa only [H, ε] using
    (weighted_fixed_grid_from_interval_errors d k
      (fun _ j => reciprocalPrimeCell L (u j) (v j))
      (fun _ j => logCell (u j) (v j))
      H ε W hH hε hW hμ0 hν0 hν hgap S w hw0 hw)

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## WeightedPrimeGridLimit -/

section

open Filter Topology
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Uniform quantitative PNT2' error tends to zero on every fixed
positive logarithmic compact, not only the special source M=1 case. -/
theorem pntGridError_tendsto_zero
    (a M C : ℝ) (ha : 0 < a) :
    Tendsto (fun L : ℝ => pntGridError a M C L)
      atTop (𝓝 0) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hI : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hI2 : Tendsto (fun L : ℝ => (L⁻¹)^2) atTop (𝓝 0) := by
    simpa using hI.pow 2
  have hsum : Tendsto
      (fun L : ℝ =>
        ((2*C)/a^2)*(L⁻¹)^2 +
        (C*(M-a)/a^2+1/a)*L⁻¹)
      atTop (𝓝 0) := by
    simpa using ((hI2.const_mul ((2*C)/a^2)).add
      (hI.const_mul (C*(M-a)/a^2+1/a)))
  have hEq : (fun L : ℝ => pntGridError a M C L) =ᶠ[atTop]
      (fun L : ℝ =>
        ((2*C)/a^2)*(L⁻¹)^2 +
        (C*(M-a)/a^2+1/a)*L⁻¹) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    have hL0 : L ≠ 0 := ne_of_gt hL
    unfold pntGridError
    field_simp
    ring
  exact hsum.congr' hEq.symm

/-- Actual weighted prime grids converge even if BOTH the chosen finite
cell family and its bounded nonnegative cell weights depend on L.
The grid endpoints, exponent dimension, and bound W stay frozen.
This removes any need to assume a moving-family fixed-grid limit. -/
theorem weighted_prime_grid_tendsto_zero
    (d k : ℕ) (a M C W : ℝ) (u v : Fin k → ℝ)
    (ha : 0 < a) (haM : a ≤ M) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (S : ℝ → Finset (Fin d → Fin k))
    (w : ℝ → (Fin d → Fin k) → ℝ)
    (hw0 : ∀ L c, c ∈ S L → 0 ≤ w L c)
    (hw : ∀ L c, c ∈ S L → w L c ≤ W)
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (a * L) ≤ t →
         |primeRemainder t| ≤ C * t / (Real.log t) ^ 2) :
    Tendsto (fun L : ℝ =>
      (∑ c ∈ S L, w L c *
        ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))) -
      (∑ c ∈ S L, w L c *
        ∏ i : Fin d, logCell (u (c i)) (v (c i))))
      atTop (𝓝 0) := by
  let E : ℝ → ℝ := fun L => pntGridError a M C L
  let H : ℝ := Real.log (M / a)
  let B : ℝ → ℝ := fun L =>
    (k : ℝ)^d * W * ((d : ℝ) * E L * (H + E L)^(d-1))
  let F : ℝ → ℝ := fun L =>
    (∑ c ∈ S L, w L c *
      ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))) -
    (∑ c ∈ S L, w L c *
      ∏ i : Fin d, logCell (u (c i)) (v (c i)))
  have hE : Tendsto E atTop (𝓝 0) :=
    pntGridError_tendsto_zero a M C ha
  have hH : Tendsto (fun L : ℝ => H + E L)
      atTop (𝓝 H) := by
    simpa using tendsto_const_nhds.add hE
  have hB : Tendsto B atTop (𝓝 0) := by
    have hh : Tendsto (fun L : ℝ =>
        E L * (H + E L)^(d-1)) atTop (𝓝 0) := by
      simpa using hE.mul (hH.pow (d-1))
    dsimp [B]
    simpa [mul_assoc] using
      (hh.const_mul ((k : ℝ)^d * W * (d : ℝ)))
  have hZero : ∀ᶠ L : ℝ in atTop, (0:ℝ) ≤ |F L| :=
    Filter.Eventually.of_forall (fun L => abs_nonneg _)
  have hUpper : ∀ᶠ L : ℝ in atTop, |F L| ≤ B L := by
    filter_upwards [eventually_ge_atTop (1/a), hPNT] with L hL hPNT'
    have hL1 : 1 ≤ a * L := by
      have := mul_le_mul_of_nonneg_left hL ha.le
      have ha0 : a ≠ 0 := ne_of_gt ha
      field_simp at this
      linarith
    simpa only [F, B, E, H] using
      (weighted_prime_grid_uniform_bound d k a M L C W u v
        ha haM hL1 hC hW hcells hPNT'
        (S L) (w L)
        (fun c hc => hw0 L c hc)
        (fun c hc => hw L c hc))
  have hAbs : Tendsto (fun L : ℝ => |F L|)
      atTop (𝓝 0) :=
    squeeze_zero' hZero hUpper hB
  have hNorm : Tendsto (fun L : ℝ => ‖F L‖)
      atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using hAbs
  have hF : Tendsto F atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hNorm
  exact hF

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## PrimeBoxes -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- A real-logarithmic cell of ACTUAL natural primes; strict lower
boundary and inclusive upper boundary match the source alphabet. -/
noncomputable def actualPrimeCellSet (L u v : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp (u*L)⌋₊ ⌊Real.exp (v*L)⌋₊).filter Nat.Prime

theorem actualPrimeCellSet_reciprocal (L u v : ℝ) :
    (∑ p ∈ actualPrimeCellSet L u v, (p : ℝ)⁻¹) =
      reciprocalPrimeCell L u v := by
  classical
  simp only [actualPrimeCellSet, reciprocalPrimeCell]
  rw [Finset.sum_filter]

/-- A full ordered prime d-tuple box. Coordinate primes may repeat;
the only disjointness restriction concerns the different CELL LABELS. -/
noncomputable def orderedPrimeBox (d k : ℕ)
    (P : Fin k → Finset ℕ) (c : Fin d → Fin k) :
    Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i : Fin d => P (c i))

theorem orderedPrimeBox_mass (d k : ℕ)
    (P : Fin k → Finset ℕ) (c : Fin d → Fin k) :
    (∑ ps ∈ orderedPrimeBox d k P c,
      ∏ i : Fin d, ((ps i : ℕ) : ℝ)⁻¹) =
      ∏ i : Fin d, (∑ p ∈ P (c i), (p : ℝ)⁻¹) := by
  classical
  exact (Finset.prod_univ_sum
    (fun i : Fin d => P (c i))
    (fun (_i : Fin d) (p : ℕ) => (p : ℝ)⁻¹)).symm

theorem orderedPrimeBox_disjoint (d k : ℕ)
    (P : Fin k → Finset ℕ)
    (hP : ∀ a b : Fin k, a ≠ b → Disjoint (P a) (P b))
    (c c' : Fin d → Fin k) (hcc : c ≠ c') :
    Disjoint (orderedPrimeBox d k P c) (orderedPrimeBox d k P c') := by
  classical
  have hcoords : ∃ i : Fin d, c i ≠ c' i := by
    by_contra hn
    push Not at hn
    apply hcc
    funext i
    exact hn i
  obtain ⟨i, hi⟩ := hcoords
  apply Finset.disjoint_left.mpr
  intro ps hp hp'
  have hi1 : ps i ∈ P (c i) := by
    exact (Fintype.mem_piFinset.mp hp) i
  have hi2 : ps i ∈ P (c' i) := by
    exact (Fintype.mem_piFinset.mp hp') i
  exact (Finset.disjoint_left.mp (hP (c i) (c' i) hi)) hi1 hi2

/-- All grid cells selected by S are disjoint ON THE ACTUAL ORDERED
prime tuples, so no repeated-count or squarefree shortcut is needed. -/
noncomputable def orderedPrimeGridTuples (d k : ℕ)
    (P : Fin k → Finset ℕ) (S : Finset (Fin d → Fin k)) :
    Finset (Fin d → ℕ) :=
  S.biUnion (orderedPrimeBox d k P)
theorem orderedPrimeGridTuples_mass (d k : ℕ)
    (P : Fin k → Finset ℕ) (S : Finset (Fin d → Fin k))
    (hP : ∀ a b : Fin k, a ≠ b → Disjoint (P a) (P b)) :
    (∑ ps ∈ orderedPrimeGridTuples d k P S,
      ∏ i : Fin d, ((ps i : ℕ) : ℝ)⁻¹) =
      ∑ c ∈ S, ∏ i : Fin d, (∑ p ∈ P (c i), (p : ℝ)⁻¹) := by
  classical
  have hd : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' →
      Disjoint (orderedPrimeBox d k P c)
        (orderedPrimeBox d k P c') := by
    intro c hc c' hc' hcc
    exact orderedPrimeBox_disjoint d k P hP c c' hcc
  simp only [orderedPrimeGridTuples]
  rw [Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro c hc
  exact orderedPrimeBox_mass d k P c

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## ActualPrimeCells -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Two separated half-open logarithmic prime cells have disjoint
natural primes, including exact endpoint cases. -/
theorem actualPrimeCellSet_disjoint_of_separated
    (L u v u' v' : ℝ) (hL : 0 ≤ L) (hvv' : v ≤ u') :
    Disjoint (actualPrimeCellSet L u v)
      (actualPrimeCellSet L u' v') := by
  classical
  have he : Real.exp (v * L) ≤ Real.exp (u' * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hvv' hL)
  have hfloor : ⌊Real.exp (v * L)⌋₊ ≤ ⌊Real.exp (u' * L)⌋₊ :=
    Nat.floor_mono he
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  have hleft := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have hright := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp').1).1
  omega

/-- A frozen monotone collection of cells is pairwise disjoint. -/
theorem actualPrimeCellSet_pairwise_disjoint
    (k : ℕ) (L : ℝ) (u v : Fin k → ℝ)
    (hL : 0 ≤ L)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j) :
    ∀ i j : Fin k, i ≠ j →
      Disjoint (actualPrimeCellSet L (u i) (v i))
        (actualPrimeCellSet L (u j) (v j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact actualPrimeCellSet_disjoint_of_separated L (u i) (v i)
      (u j) (v j) hL (hsep i j h)
  · exact (actualPrimeCellSet_disjoint_of_separated L
      (u j) (v j) (u i) (v i) hL (hsep j i h)).symm
/-- The exact sum over true ordered natural-prime tuples on a union
of frozen separated cells equals the corresponding product-cell mass. -/
theorem actualPrimeGridTuples_mass (d k : ℕ)
    (L : ℝ) (u v : Fin k → ℝ) (S : Finset (Fin d → Fin k))
    (hL : 0 ≤ L)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j) :
    (∑ ps ∈ orderedPrimeGridTuples d k
      (fun j => actualPrimeCellSet L (u j) (v j)) S,
      ∏ i : Fin d, (ps i : ℝ)⁻¹) =
    ∑ c ∈ S, ∏ i : Fin d, reciprocalPrimeCell L
      (u (c i)) (v (c i)) := by
  have hP := actualPrimeCellSet_pairwise_disjoint k L u v hL hsep
  rw [orderedPrimeGridTuples_mass d k _ S hP]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.prod_congr rfl
  intro i hi
  exact actualPrimeCellSet_reciprocal L (u (c i)) (v (c i))

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## ActualPrimeGridLimit -/

section

open Filter Topology
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Actual ordered prime tuples (including repeated prime factors)
converge to dt/t product mass on ANY selected union of separated frozen
grid cells, even if the selection itself varies with L. Only PNT2'
and exact true natural-prime counting enter the statement. -/
theorem actual_ordered_prime_grid_tendsto_zero
    (d k : ℕ) (a M C : ℝ) (u v : Fin k → ℝ)
    (ha : 0 < a) (haM : a ≤ M) (hC : 0 ≤ C)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (S : ℝ → Finset (Fin d → Fin k))
    (hPNT : ∀ᶠ L : ℝ in atTop,
       ∀ t, Real.exp (a * L) ≤ t →
         |primeRemainder t| ≤ C * t / (Real.log t) ^ 2) :
    Tendsto (fun L : ℝ =>
      (∑ ps ∈ orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L (u j) (v j)) (S L),
        ∏ i : Fin d, (ps i : ℝ)⁻¹) -
      (∑ c ∈ S L, ∏ i : Fin d,
        logCell (u (c i)) (v (c i))))
      atTop (𝓝 0) := by
  have hP : Tendsto (fun L : ℝ =>
      (∑ c ∈ S L,
        ∏ i : Fin d, reciprocalPrimeCell L
          (u (c i)) (v (c i))) -
      (∑ c ∈ S L,
        ∏ i : Fin d, logCell (u (c i)) (v (c i))))
      atTop (𝓝 0) := by
    simpa only [one_mul] using
      (weighted_prime_grid_tendsto_zero d k a M C 1 u v
        ha haM hC (by norm_num) hcells S
        (fun _L _c => 1)
        (fun L c hc => by norm_num)
        (fun L c hc => by norm_num) hPNT)
  have heq : (fun L : ℝ =>
      (∑ ps ∈ orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L (u j) (v j)) (S L),
        ∏ i : Fin d, (ps i : ℝ)⁻¹) -
      (∑ c ∈ S L, ∏ i : Fin d,
        logCell (u (c i)) (v (c i)))) =ᶠ[atTop]
      (fun L : ℝ =>
        (∑ c ∈ S L, ∏ i : Fin d,
          reciprocalPrimeCell L (u (c i)) (v (c i))) -
        (∑ c ∈ S L, ∏ i : Fin d,
          logCell (u (c i)) (v (c i)))) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [actualPrimeGridTuples_mass d k L u v (S L) hL hsep]
  exact hP.congr' heq.symm

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## CellKernelBounds -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- A source last-prime reciprocal kernel is monotone in every one of
the independent logarithmic prime coordinates. This includes the
dependent LAST PRIME, not only ordinary rectangular product measures. -/
theorem lastPrimeKernel_cell_bounds (d : ℕ)
    (b w : ℝ) (u v t : Fin d → ℝ)
    (hb : 0 < b)
    (hcoords : ∀ i, u i ≤ t i ∧ t i ≤ v i)
    (hroom : b ≤ w - ∑ i : Fin d, v i) :
    0 ≤ (w - ∑ i : Fin d, u i)⁻¹ ∧
    (w - ∑ i : Fin d, u i)⁻¹ ≤
      (w - ∑ i : Fin d, t i)⁻¹ ∧
    (w - ∑ i : Fin d, t i)⁻¹ ≤
      (w - ∑ i : Fin d, v i)⁻¹ ∧
    (w - ∑ i : Fin d, v i)⁻¹ ≤ b⁻¹ := by
  have hsumlo : (∑ i : Fin d, u i) ≤ ∑ i : Fin d, t i :=
    Finset.sum_le_sum (fun i _ => (hcoords i).1)
  have hsumhi : (∑ i : Fin d, t i) ≤ ∑ i : Fin d, v i :=
    Finset.sum_le_sum (fun i _ => (hcoords i).2)
  have hbu : 0 < w - ∑ i : Fin d, u i := by linarith
  have hbt : 0 < w - ∑ i : Fin d, t i := by linarith
  have hbv : 0 < w - ∑ i : Fin d, v i := by linarith
  refine ⟨inv_nonneg.mpr hbu.le, ?_, ?_, ?_⟩
  · exact inv_anti₀ hbt (by linarith)
  · exact inv_anti₀ hbv (by linarith)
  · exact inv_anti₀ hb hroom

/-- Frozen lower-corner source kernel has a positive absolute bound
independent of the prime cutoff L and the list of active cells. -/
theorem lowerCornerKernel_bounded (d : ℕ)
    (b w : ℝ) (u v : Fin d → ℝ)
    (hb : 0 < b) (huv : ∀ i, u i ≤ v i)
    (hroom : b ≤ w - ∑ i : Fin d, v i) :
    0 ≤ (w - ∑ i : Fin d, u i)⁻¹ ∧
      (w - ∑ i : Fin d, u i)⁻¹ ≤ b⁻¹ := by
  have h := lastPrimeKernel_cell_bounds d b w u v u hb
    (fun i => ⟨le_rfl, huv i⟩) hroom
  exact ⟨h.1, h.2.1.trans (h.2.2.1.trans h.2.2.2)⟩

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## PrimeCellExponents -/

section

namespace Green64Analytic.ReciprocalPrimeGrid

noncomputable def primeExponent (L : ℝ) (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / L

/-- Actual natural-prime cell endpoints imply the correct logarithmic
exponent bounds, with strictly open lower and closed upper end. -/
theorem actualPrimeCellSet_exponent_bounds
    (L u v : ℝ) (hL : 0 < L) (p : ℕ)
    (hp : p ∈ actualPrimeCellSet L u v) :
    u < primeExponent L p ∧ primeExponent L p ≤ v := by
  have hb := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hlow : Real.exp (u*L) < (p : ℝ) :=
    Nat.lt_of_floor_lt hb.1
  have hhigh : (p : ℝ) ≤ Real.exp (v*L) := by
    have hfloor : (p : ℝ) ≤ (⌊Real.exp (v*L)⌋₊ : ℝ) := by
      exact_mod_cast hb.2
    exact hfloor.trans (Nat.floor_le (Real.exp_pos _).le)
  have hpPos : (0:ℝ) < p := (Real.exp_pos _).trans hlow
  have hleft : u*L < Real.log (p : ℝ) := by
    simpa only [Real.log_exp] using
      (Real.log_lt_log (Real.exp_pos _) hlow)
  have hright : Real.log (p : ℝ) ≤ v*L := by
    simpa only [Real.log_exp] using
      (Real.log_le_log hpPos hhigh)
  refine ⟨?_, ?_⟩
  · exact (lt_div_iff₀ hL).mpr (by simpa [primeExponent, mul_comm] using hleft)
  · exact (div_le_iff₀ hL).mpr (by simpa [primeExponent, mul_comm] using hright)

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceD25FixedGridUpper -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

noncomputable def sourceD25FrozenArithmeticGrid
    (d k : ℕ) (L w : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k)) : ℝ :=
  ∑ c ∈ S,
    (w - ∑ i : Fin d, u (c i))⁻¹ *
      ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))

noncomputable def sourceD25FrozenContinuumGrid
    (d k : ℕ) (w : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k)) : ℝ :=
  ∑ c ∈ S,
    (w - ∑ i : Fin d, u (c i))⁻¹ *
      ∏ i : Fin d, Real.log (v (c i) / u (c i))

lemma sourceD25_frozen_weight_nonneg
    (d k : ℕ) (b w : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i))
    (huv : ∀ j, u j ≤ v j) :
    ∀ c ∈ S, 0 ≤ (w - ∑ i : Fin d, u (c i))⁻¹ := by
  intro c hc
  have hsum : (∑ i : Fin d, u (c i)) ≤ ∑ i : Fin d, v (c i) :=
    Finset.sum_le_sum (fun i _ => huv (c i))
  have hd : b ≤ w - ∑ i : Fin d, u (c i) := by
    linarith [hroom c hc]
  exact inv_nonneg.mpr (hb.le.trans hd)

lemma sourceD25_frozen_weight_le
    (d k : ℕ) (b w : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i))
    (huv : ∀ j, u j ≤ v j) :
    ∀ c ∈ S, (w - ∑ i : Fin d, u (c i))⁻¹ ≤ b⁻¹ := by
  intro c hc
  have hsum : (∑ i : Fin d, u (c i)) ≤ ∑ i : Fin d, v (c i) :=
    Finset.sum_le_sum (fun i _ => huv (c i))
  have hd : b ≤ w - ∑ i : Fin d, u (c i) := by
    linarith [hroom c hc]
  exact inv_anti₀ hb hd

/-- Fixed finite actual reciprocal-prime grid is eventually bounded by
the literal source simplex integral, with arbitrary additive accuracy. -/
theorem sourceD25_actual_fixed_grid_upper
    (d k : ℕ) (b M w ε : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b) (hbM : b ≤ M) (hε : 0 < ε)
    (hcells : ∀ j, b ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i)) :
    ∀ᶠ L : ℝ in atTop,
      sourceD25FrozenArithmeticGrid d k L w u v S ≤
        (∫ t in sourceRegion d b w, sourceKernel d w t) + ε := by
  obtain ⟨C,hC,hPNT⟩ :=
    Green64Analytic.SourcePNT2.source_pnt2_unconditional b hb
  let wt : ℝ → (Fin d → Fin k) → ℝ :=
    fun _L c => (w - ∑ i : Fin d, u (c i))⁻¹
  have hw0 : ∀ L c, c ∈ S → 0 ≤ wt L c := by
    intro L c hc
    exact sourceD25_frozen_weight_nonneg d k b w u v S hb hroom
      (fun j => (hcells j).2.1) c hc
  have hw : ∀ L c, c ∈ S → wt L c ≤ b⁻¹ := by
    intro L c hc
    exact sourceD25_frozen_weight_le d k b w u v S hb hroom
      (fun j => (hcells j).2.1) c hc
  have hW : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have hlim := weighted_prime_grid_tendsto_zero
    d k b M C b⁻¹ u v hb hbM hC hW hcells
    (fun _L => S) wt hw0 hw hPNT
  have hsmall : ∀ᶠ L : ℝ in atTop,
      sourceD25FrozenArithmeticGrid d k L w u v S -
        sourceD25FrozenContinuumGrid d k w u v S < ε := by
    have hh := hlim.eventually (isOpen_Iio.mem_nhds hε)
    simpa only [sourceD25FrozenArithmeticGrid,sourceD25FrozenContinuumGrid,wt,logCell] using hh
  have hcont : sourceD25FrozenContinuumGrid d k w u v S ≤
      ∫ t in sourceRegion d b w, sourceKernel d w t := by
    simpa only [sourceD25FrozenContinuumGrid] using
      finite_source_grid_integral_lower d k b w (M-b) u v S hb
        (sub_nonneg.mpr hbM)
        (fun j => (hcells j).1) (fun j => (hcells j).2.1)
        (fun j => by linarith [(hcells j).1,(hcells j).2.2]) hsep hroom
  filter_upwards [hsmall] with L hL
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD25UpperCornerGrid -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

noncomputable def sourceD25UpperArithmeticGrid
    (d k : ℕ) (L w : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k)) : ℝ :=
  ∑ c ∈ S,
    (w - ∑ i : Fin d, v (c i))⁻¹ *
      ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))

noncomputable def sourceD25UpperContinuumGrid
    (d k : ℕ) (w : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k)) : ℝ :=
  ∑ c ∈ S,
    (w - ∑ i : Fin d, v (c i))⁻¹ *
      ∏ i : Fin d, Real.log (v (c i) / u (c i))

lemma sourceD25_upper_corner_weight_bounds
    (d k : ℕ) (b w : ℝ) (v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i)) :
    ∀ c ∈ S,
      0 ≤ (w - ∑ i : Fin d, v (c i))⁻¹ ∧
      (w - ∑ i : Fin d, v (c i))⁻¹ ≤ b⁻¹ := by
  intro c hc
  have hd := hroom c hc
  have hpos : 0 < w - ∑ i : Fin d, v (c i) := hb.trans_le hd
  exact ⟨inv_nonneg.mpr hpos.le, inv_anti₀ hb hd⟩

lemma sourceD25_upper_continuum_bound
    (d k : ℕ) (b w η : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b) (hη : 0 ≤ η)
    (hbu : ∀ j, b ≤ u j)
    (huv : ∀ j, u j ≤ v j)
    (hwidth : ∀ j, v j - u j ≤ η)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i)) :
    sourceD25UpperContinuumGrid d k w u v S ≤
      (∫ t in sourceRegion d b w, sourceKernel d w t) +
      ((d:ℝ)*η/b^2) *
        (∫ t in sourceRegion d b w, reciprocalProduct d t) := by
  let E : ℝ := (d:ℝ)*η/b^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hfreeze : ∀ c∈S,
      (w - ∑ i : Fin d, v (c i))⁻¹ ≤
        (w - ∑ i : Fin d, u (c i))⁻¹ + E := by
    intro c hc
    have hf := source_last_prime_cell_freeze_bound
      d b w η (fun i => u (c i)) (fun i => v (c i))
      (fun i => v (c i)) hb hη
      (fun i => ⟨huv (c i),le_rfl⟩)
      (fun i => hwidth (c i)) (hroom c hc)
    dsimp only [E]
    linarith [hf.2]
  have hlog0 : ∀ c∈S,
      0 ≤ ∏ i : Fin d, Real.log (v (c i)/u (c i)) := by
    intro c hc
    apply Finset.prod_nonneg
    intro i hi
    have hu0 : 0<u (c i) := hb.trans_le (hbu (c i))
    exact Real.log_nonneg ((one_le_div hu0).mpr (huv (c i)))
  have hsum : sourceD25UpperContinuumGrid d k w u v S ≤
      sourceD25FrozenContinuumGrid d k w u v S +
        E * (∑ c∈S,∏ i : Fin d, Real.log (v (c i)/u (c i))) := by
    unfold sourceD25UpperContinuumGrid sourceD25FrozenContinuumGrid
    calc
      _ ≤ ∑ c∈S,
          ((w - ∑ i : Fin d, u (c i))⁻¹+E) *
            ∏ i : Fin d, Real.log (v (c i)/u (c i)) := by
        apply Finset.sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_right (hfreeze c hc) (hlog0 c hc)
      _ = (∑ c∈S,
          (w - ∑ i : Fin d, u (c i))⁻¹ *
            ∏ i : Fin d, Real.log (v (c i)/u (c i))) +
          E*(∑ c∈S,∏ i : Fin d, Real.log (v (c i)/u (c i))) := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib,Finset.mul_sum]
  have hlow : sourceD25FrozenContinuumGrid d k w u v S ≤
      ∫ t in sourceRegion d b w, sourceKernel d w t := by
    simpa only [sourceD25FrozenContinuumGrid] using
      finite_source_grid_integral_lower d k b w η u v S hb hη hbu huv
        hwidth hsep hroom
  have hmass : (∑ c∈S,∏ i : Fin d, Real.log (v (c i)/u (c i))) ≤
      ∫ t in sourceRegion d b w, reciprocalProduct d t :=
    sourceGrid_reciprocal_mass_le_source d k b w u v S hb hbu huv hsep hroom
  have herr := mul_le_mul_of_nonneg_left hmass hE
  linarith

/-- Actual prime grid with the TRUE upper-corner dependent denominator
is bounded by the literal source integral plus explicit mesh error. -/
theorem sourceD25_actual_upper_corner_grid
    (d k : ℕ) (b M w η ε : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b) (hbM : b ≤ M) (hη : 0 ≤ η) (hε : 0 < ε)
    (hcells : ∀ j, b ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hwidth : ∀ j, v j - u j ≤ η)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i)) :
    ∀ᶠ L : ℝ in atTop,
      sourceD25UpperArithmeticGrid d k L w u v S ≤
        (∫ t in sourceRegion d b w, sourceKernel d w t) +
        ((d:ℝ)*η/b^2) *
          (∫ t in sourceRegion d b w, reciprocalProduct d t) + ε := by
  obtain ⟨C,hC,hPNT⟩ :=
    Green64Analytic.SourcePNT2.source_pnt2_unconditional b hb
  let wt : ℝ → (Fin d → Fin k) → ℝ :=
    fun _L c => (w - ∑ i : Fin d, v (c i))⁻¹
  have hwb := sourceD25_upper_corner_weight_bounds d k b w v S hb hroom
  have hw0 : ∀ L c, c∈S → 0≤wt L c := by
    intro L c hc
    exact (hwb c hc).1
  have hw : ∀ L c, c∈S → wt L c≤b⁻¹ := by
    intro L c hc
    exact (hwb c hc).2
  have hlim := weighted_prime_grid_tendsto_zero
    d k b M C b⁻¹ u v hb hbM hC (inv_nonneg.mpr hb.le)
    hcells (fun _L => S) wt hw0 hw hPNT
  have hsmall : ∀ᶠ L : ℝ in atTop,
      sourceD25UpperArithmeticGrid d k L w u v S -
        sourceD25UpperContinuumGrid d k w u v S < ε := by
    have hh := hlim.eventually (isOpen_Iio.mem_nhds hε)
    simpa only [sourceD25UpperArithmeticGrid,sourceD25UpperContinuumGrid,wt,logCell] using hh
  have hcont := sourceD25_upper_continuum_bound d k b w η u v S hb hη
    (fun j => (hcells j).1) (fun j => (hcells j).2.1) hwidth hsep hroom
  filter_upwards [hsmall] with L hL
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## WeightedBoxLower -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Exact finite transport of any ordered-tuple lower weight through
disjoint product boxes. This is NOT a statement about an abstract
approximation: every term on the right is a true ordered natural-number
tuple, including all repeated coordinates. -/
theorem orderedPrimeGridTuples_weighted_lower (d k : ℕ)
    (P : Fin k → Finset ℕ) (S : Finset (Fin d → Fin k))
    (hP : ∀ a b : Fin k, a ≠ b → Disjoint (P a) (P b))
    (w : (Fin d → Fin k) → ℝ)
    (F : (Fin d → ℕ) → ℝ)
    (hF : ∀ c ∈ S, ∀ ps ∈ orderedPrimeBox d k P c,
      w c ≤ F ps) :
    (∑ c ∈ S, w c *
      ∏ i : Fin d, (∑ p ∈ P (c i), (p : ℝ)⁻¹)) ≤
    (∑ ps ∈ orderedPrimeGridTuples d k P S,
      F ps * ∏ i : Fin d, (ps i : ℝ)⁻¹) := by
  classical
  have hd : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' →
      Disjoint (orderedPrimeBox d k P c)
        (orderedPrimeBox d k P c') := by
    intro c hc c' hc' hcc
    exact orderedPrimeBox_disjoint d k P hP c c' hcc
  calc
    (∑ c ∈ S, w c *
        ∏ i : Fin d, (∑ p ∈ P (c i), (p : ℝ)⁻¹)) =
      ∑ c ∈ S, ∑ ps ∈ orderedPrimeBox d k P c,
        w c * ∏ i : Fin d, (ps i : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← orderedPrimeBox_mass d k P c]
      rw [Finset.mul_sum]
    _ ≤ ∑ c ∈ S, ∑ ps ∈ orderedPrimeBox d k P c,
        F ps * ∏ i : Fin d, (ps i : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro ps hps
      have hmass : 0 ≤ ∏ i : Fin d, (ps i : ℝ)⁻¹ :=
        Finset.prod_nonneg (fun i hi =>
          inv_nonneg.mpr (Nat.cast_nonneg (ps i)))
      exact mul_le_mul_of_nonneg_right (hF c hc ps hps) hmass
    _ = (∑ ps ∈ orderedPrimeGridTuples d k P S,
        F ps * ∏ i : Fin d, (ps i : ℝ)⁻¹) := by
      simp only [orderedPrimeGridTuples]
      rw [Finset.sum_biUnion hd]

/-- The source EXACT last-prime reciprocal kernel on a finite union
of strictly interior frozen prime boxes. Every source term is charged
once; the lower weight is the reciprocal at the cell lower corner. -/
theorem actual_source_last_prime_kernel_box_lower
    (d k : ℕ) (L b w : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hL : 0 < L) (hb : 0 < b)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (huv : ∀ j, u j ≤ v j)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i)) :
    (∑ c ∈ S,
      (w - ∑ i : Fin d, u (c i))⁻¹ *
       ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))) ≤
    (∑ ps ∈ orderedPrimeGridTuples d k
      (fun j => actualPrimeCellSet L (u j) (v j)) S,
      (w - ∑ i : Fin d, primeExponent L (ps i))⁻¹ *
        ∏ i : Fin d, (ps i : ℝ)⁻¹) := by
  have _ := huv
  let P : Fin k → Finset ℕ := fun j =>
    actualPrimeCellSet L (u j) (v j)
  have hP : ∀ a a' : Fin k, a ≠ a' → Disjoint (P a) (P a') :=
    actualPrimeCellSet_pairwise_disjoint k L u v hL.le hsep
  have hF : ∀ c ∈ S, ∀ ps ∈ orderedPrimeBox d k P c,
      (w - ∑ i : Fin d, u (c i))⁻¹ ≤
      (w - ∑ i : Fin d, primeExponent L (ps i))⁻¹ := by
    intro c hc ps hps
    have hcoords (i : Fin d) :
        u (c i) ≤ primeExponent L (ps i) ∧
        primeExponent L (ps i) ≤ v (c i) := by
      have hp : ps i ∈ P (c i) :=
        (Fintype.mem_piFinset.mp hps) i
      have he := actualPrimeCellSet_exponent_bounds L
        (u (c i)) (v (c i)) hL (ps i) hp
      exact ⟨he.1.le, he.2⟩
    exact (lastPrimeKernel_cell_bounds d b w
      (fun i => u (c i))
      (fun i => v (c i))
      (fun i => primeExponent L (ps i))
      hb hcoords (hroom c hc)).2.1
  calc
    (∑ c ∈ S,
      (w - ∑ i : Fin d, u (c i))⁻¹ *
       ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))) =
      ∑ c ∈ S,
      (w - ∑ i : Fin d, u (c i))⁻¹ *
       ∏ i : Fin d, (∑ p ∈ P (c i), (p : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro c hc
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (actualPrimeCellSet_reciprocal L (u (c i)) (v (c i))).symm
    _ ≤ _ := orderedPrimeGridTuples_weighted_lower d k P S hP
      (fun c => (w - ∑ i : Fin d, u (c i))⁻¹)
      (fun ps => (w - ∑ i : Fin d, primeExponent L (ps i))⁻¹)
      hF

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceBoxPrefixes -/

section

set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Inner product-grid tuples embed in the LITERAL source list family.
The only source tail condition is an explicit fixed positive exponent
gap δ, and repeated primes are permitted. -/
theorem actual_box_prefix_in_truncated_source
    (d k : ℕ) (b δ a M L : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hL : 0 < L) (hb : 0 < b) (hδ : 0 < δ)
    (hba : b ≤ a) (hM : M ≤ 1)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hroom : ∀ c ∈ S, (∑ i : Fin d, v (c i)) ≤ 1 - b - δ) :
    ∀ ps ∈ orderedPrimeGridTuples d k
       (fun j => actualPrimeCellSet L (u j) (v j)) S,
       List.ofFn ps ∈ Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes
           d b δ L := by
  have _ := hM
  classical
  intro ps hps
  obtain ⟨c,hc,hbox⟩ := Finset.mem_biUnion.mp hps
  have hp (i : Fin d) :
      ps i ∈ actualPrimeCellSet L (u (c i)) (v (c i)) :=
    (Fintype.mem_piFinset.mp hbox) i
  have hprime (i : Fin d) : Nat.Prime (ps i) :=
    (Finset.mem_filter.mp (hp i)).2
  have hlow (i : Fin d) : Real.exp (b*L) < (ps i : ℝ) := by
    have hbU : b*L ≤ u (c i)*L :=
      mul_le_mul_of_nonneg_right
        (hba.trans (hcells (c i)).1) hL.le
    have hfloor := (Finset.mem_Ioc.mp
      (Finset.mem_filter.mp (hp i)).1).1
    exact (Real.exp_le_exp.mpr hbU).trans_lt
      (Nat.lt_of_floor_lt hfloor)
  have hupper (i : Fin d) :
      (ps i : ℝ) ≤ Real.exp (v (c i)*L) := by
    have hfloor := (Finset.mem_Ioc.mp
      (Finset.mem_filter.mp (hp i)).1).2
    have hh : (ps i : ℝ) ≤ (⌊Real.exp (v (c i)*L)⌋₊ : ℝ) := by
      exact_mod_cast hfloor
    exact hh.trans (Nat.floor_le (Real.exp_pos _).le)
  have hprod :
      (∏ i : Fin d, (ps i : ℝ)) ≤
        Real.exp ((∑ i : Fin d, v (c i))*L) := by
    calc
      (∏ i : Fin d, (ps i : ℝ)) ≤
        (∏ i : Fin d, Real.exp (v (c i)*L)) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact Nat.cast_nonneg _
          · intro i hi
            exact hupper i
      _ = Real.exp ((∑ i : Fin d, v (c i))*L) := by
          rw [← Real.exp_sum]
          congr 1
          rw [Finset.sum_mul]
  have hprodCap :
      (∏ i : Fin d, (ps i : ℝ)) ≤
        Real.exp ((1-b-δ)*L) := by
    exact hprod.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (hroom c hc) hL.le))
  have hpos : 0 < (List.ofFn ps).prod := by
    rw [List.prod_ofFn]
    exact Finset.prod_pos (fun i hi => (hprime i).pos)
  have hbound : ((List.ofFn ps).prod : ℝ) ≤
      Real.exp ((1-b-δ)*L) := by
    simpa only [List.prod_ofFn, Nat.cast_prod] using hprodCap
  have hlen : (List.ofFn ps).length = d := by simp
  have hall : ∀ p ∈ List.ofFn ps,
      Nat.Prime p ∧ Real.exp (b*L) < (p:ℝ) := by
    apply (List.forall_mem_ofFn_iff (f := ps)
      (P := fun p => Nat.Prime p ∧ Real.exp (b*L) < (p:ℝ))).mpr
    intro i
    exact ⟨hprime i,hlow i⟩
  have hboundX : ((List.ofFn ps).prod : ℝ) ≤ Real.exp L := by
    have hbcap : (1-b-δ)*L ≤ L := by
      nlinarith [mul_pos hb hL, mul_pos hδ hL]
    exact hbound.trans (Real.exp_le_exp.mpr hbcap)
  have hpref :
      List.ofFn ps ∈ Green64Analytic.OrderedPrimeRough.allPrimeTuples
        d (Real.exp (b*L)) (Real.exp L) := by
    exact (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      d (Real.exp (b*L)) (Real.exp L) (Real.exp_pos _).le _).mpr
      ⟨hlen,hall,hpos,hboundX⟩
  apply Finset.mem_filter.mpr
  exact ⟨hpref,hbound⟩

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceLastPrimeAlgebra -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Source PNT last-prime main-term algebra. This is not a surrogate
density: the RHS is EXACTLY L/x times the finite last-prime PNT
main term evaluated at x/product of actual natural-prime coordinates. -/
theorem source_last_prime_main_kernel_identity
    (d : ℕ) (L : ℝ) (ps : Fin d → ℕ)
    (hL : L ≠ 0) (hpr : ∀ i, 0 < ps i)
    (hden : L - Real.log (∏ i : Fin d, (ps i : ℝ)) ≠ 0) :
    (1 - ∑ i : Fin d, primeExponent L (ps i))⁻¹ *
      (∏ i : Fin d, (ps i : ℝ)⁻¹) =
    (L / Real.exp L) *
      ((Real.exp L / ∏ i : Fin d, (ps i : ℝ)) /
         Real.log (Real.exp L / ∏ i : Fin d, (ps i : ℝ))) := by
  have _ := hden
  let Q : ℝ := ∏ i : Fin d, (ps i : ℝ)
  have hpos (i : Fin d) : 0 < (ps i : ℝ) := by
    exact_mod_cast hpr i
  have hQ : 0 < Q := Finset.prod_pos (fun i hi => hpos i)
  have hlog : Real.log Q =
      ∑ i : Fin d, Real.log (ps i : ℝ) := by
    exact Real.log_prod (fun i hi => ne_of_gt (hpos i))
  have hsum : (∑ i : Fin d, primeExponent L (ps i)) =
      Real.log Q / L := by
    simp only [primeExponent]
    rw [← Finset.sum_div, ← hlog]
  have hinv : (∏ i : Fin d, (ps i : ℝ)⁻¹) = Q⁻¹ := by
    simpa only [Q] using
      (Finset.prod_inv_distrib (s := Finset.univ)
        (f := fun i : Fin d => (ps i : ℝ)))
  have hlogdiv : Real.log (Real.exp L / Q) = L - Real.log Q := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hQ),
      Real.log_exp]
  have hfrac : 1 - Real.log Q / L = (L - Real.log Q) / L := by
    field_simp
  rw [hsum, hinv]
  change (1 - Real.log Q / L)⁻¹ * Q⁻¹ =
    (L / Real.exp L) * ((Real.exp L / Q) / Real.log (Real.exp L / Q))
  rw [hlogdiv, hfrac]
  have hExp : Real.exp L ≠ 0 := ne_of_gt (Real.exp_pos L)
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  field_simp

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceGridPrefixBridge -/

section

set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

noncomputable def sourceGridPrefixLists (d k : ℕ)
    (L : ℝ) (u v : Fin k → ℝ) (S : Finset (Fin d → Fin k)) :
    Finset (List ℕ) :=
  (orderedPrimeGridTuples d k
    (fun j => actualPrimeCellSet L (u j) (v j)) S).image List.ofFn

/-- Actual selected source prefix lists, not all lists of the same length,
embed in the real δ-truncated source prefix family. -/
theorem sourceGridPrefixLists_subset_truncated
    (d k : ℕ) (b δ a M L : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hL : 0 < L) (hb : 0 < b) (hδ : 0 < δ)
    (hba : b ≤ a) (hM : M ≤ 1)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hroom : ∀ c ∈ S, (∑ i : Fin d, v (c i)) ≤ 1 - b - δ) :
    sourceGridPrefixLists d k L u v S ⊆
      Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes d b δ L := by
  classical
  intro pre hpre
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hpre
  exact actual_box_prefix_in_truncated_source d k b δ a M L
    u v S hL hb hδ hba hM hcells hroom ps hps

/-- Every actual δ-truncated source prefix leaves at least x^(b+δ)
for its last prime, so PNT2' applies with the original y=x/q. -/
theorem truncated_prefix_true_last_prime_room
    (d : ℕ) (b δ L : ℝ) (hL : 0 < L)
    (hδ : 0 < δ)
    (pre : List ℕ)
    (hpre : pre ∈ Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes d b δ L) :
    Real.exp (b*L) ≤ Real.exp L / (pre.prod : ℝ) ∧
      Real.exp ((b+δ)*L) ≤ Real.exp L / (pre.prod : ℝ) := by
  have hlegal :=
    Green64Analytic.LastPrimeErrors.truncatedSourcePrefixes_legal
      d b δ L pre hpre
  have hq : 0 < (pre.prod : ℝ) := hlegal.1
  have hcap : (pre.prod : ℝ) ≤ Real.exp ((1-b-δ)*L) :=
    hlegal.2.1
  have hprodexp : Real.exp ((b+δ)*L) *
      Real.exp ((1-b-δ)*L) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hy : Real.exp ((b+δ)*L) ≤
      Real.exp L / (pre.prod : ℝ) := by
    apply (le_div_iff₀ hq).mpr
    calc
      Real.exp ((b+δ)*L) * (pre.prod : ℝ) ≤
        Real.exp ((b+δ)*L) * Real.exp ((1-b-δ)*L) :=
          mul_le_mul_of_nonneg_left hcap (Real.exp_pos _).le
      _ = Real.exp L := hprodexp
  have hsmall : Real.exp (b*L) ≤ Real.exp ((b+δ)*L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact ⟨hsmall.trans hy,hy⟩

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## SourceD25PrefixGridBridge -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid

lemma sourceD25_log_product_exponents
    (d : ℕ) (L : ℝ) (ps : Fin d → ℕ)
    (hL : 0<L) (hpr : ∀ i, 0<ps i) :
    Real.log (∏ i : Fin d,(ps i:ℝ)) / L =
      ∑ i : Fin d, primeExponent L (ps i) := by
  have _ := hL
  have hlog : Real.log (∏ i : Fin d,(ps i:ℝ)) =
      ∑ i : Fin d,Real.log (ps i:ℝ) := by
    exact Real.log_prod (fun i hi => ne_of_gt (by exact_mod_cast hpr i))
  rw [hlog,Finset.sum_div]
  rfl

lemma sourceD25_prefix_kernel_pointwise
    (d : ℕ) (S γ L w : ℝ) (ps : Fin d → ℕ)
    (hL : 0<L) (hpr : ∀ i,0<ps i)
    (hden : 0<w-∑ i : Fin d,primeExponent L (ps i)) :
    L*sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
        ((Real.exp L)^γ) (List.ofFn ps) ≤
      (w-∑ i : Fin d,primeExponent L (ps i))⁻¹ *
        ∏ i : Fin d,(ps i:ℝ)⁻¹ := by
  let pre := List.ofFn ps
  let Q : ℝ := ∏ i : Fin d,(ps i:ℝ)
  have hQ : 0<Q := Finset.prod_pos (fun i hi => by exact_mod_cast hpr i)
  have hprod : ((pre.prod:ℕ):ℝ)=Q := by
    dsimp [pre,Q]
    rw [List.prod_ofFn,Nat.cast_prod]
  by_cases hne : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^γ) (Real.exp (w*L)/(pre.prod:ℝ)))
      ((Real.exp (L^(-S))*Real.exp (w*L))/(pre.prod:ℝ))).Nonempty
  · rw [sourceD24PrefixKernel,ite_eq_left hne]
    have hlogQ : Real.log Q / L =
        ∑ i : Fin d,primeExponent L (ps i) :=
      sourceD25_log_product_exponents d L ps hL hpr
    have hlogdiv : Real.log (Real.exp (w*L)/Q) =
        L*(w-∑ i : Fin d,primeExponent L (ps i)) := by
      rw [Real.log_div (Real.exp_pos _).ne' hQ.ne',Real.log_exp]
      rw [←hlogQ]
      field_simp [hL.ne']
    rw [hprod,hlogdiv]
    have hden0 : w-∑ i : Fin d,primeExponent L (ps i) ≠ 0 := hden.ne'
    have hL0 : L≠0 := hL.ne'
    have hQ0 : Q≠0 := hQ.ne'
    have hinv : (∏ i : Fin d,(ps i:ℝ)⁻¹)=Q⁻¹ := by
      simpa only [Q] using
        (Finset.prod_inv_distrib (s:=Finset.univ)
          (f:=fun i : Fin d => (ps i:ℝ)))
    rw [hinv]
    field_simp [hL0,hQ0,hden0]
    exact le_rfl
  · rw [sourceD24PrefixKernel,ite_eq_right hne,mul_zero]
    exact mul_nonneg (inv_nonneg.mpr hden.le)
      (Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (by exact_mod_cast (hpr i).le)))

/-- On a selected fixed exponent grid, the D24 prefix kernel is bounded
pointwise by the genuine dependent-last-prime tuple kernel. -/
theorem sourceD25_selected_prefix_kernel_upper
    (d k : ℕ) (S γ L w b : ℝ) (u v : Fin k → ℝ)
    (C : Finset (Fin d → Fin k))
    (hL : 0<L) (hb : 0<b)
    (hroom : ∀ c∈C,b≤w-∑ i : Fin d,v (c i)) :
    L*(∑ pre ∈ sourceGridPrefixLists d k L u v C,
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^γ) pre) ≤
      ∑ ps ∈ orderedPrimeGridTuples d k
        (fun j => actualPrimeCellSet L (u j) (v j)) C,
        (w-∑ i : Fin d,primeExponent L (ps i))⁻¹ *
          ∏ i : Fin d,(ps i:ℝ)⁻¹ := by
  unfold sourceGridPrefixLists
  rw [Finset.sum_image List.ofFn_injective.injOn,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ps hps
  obtain ⟨c,hc,hbox⟩ := Finset.mem_biUnion.mp hps
  have hp (i : Fin d) :
      ps i∈actualPrimeCellSet L (u (c i)) (v (c i)) :=
    (Fintype.mem_piFinset.mp hbox) i
  have hpr (i : Fin d) : 0<ps i :=
    (Finset.mem_filter.mp (hp i)).2.pos
  have hexp (i : Fin d) :
      primeExponent L (ps i)≤v (c i) :=
    (actualPrimeCellSet_exponent_bounds L (u (c i)) (v (c i)) hL (ps i) (hp i)).2
  have hsum : (∑ i : Fin d,primeExponent L (ps i))≤
      ∑ i : Fin d,v (c i) := Finset.sum_le_sum (fun i hi => hexp i)
  have hden : 0<w-∑ i : Fin d,primeExponent L (ps i) := by
    have hh:=hroom c hc
    linarith
  exact sourceD25_prefix_kernel_pointwise d S γ L w ps hL hpr hden


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD25SelectedInteriorUpper -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.ReciprocalPrimeGrid
open Green64Analytic.SourceSimplexGeometry

lemma sourceD25_actual_prime_cells_disjoint
    (L : ℝ) (k : ℕ) (u v : Fin k → ℝ) (hL0 : 0 ≤ L)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j) :
    ∀ a b : Fin k, a ≠ b →
      Disjoint (actualPrimeCellSet L (u a) (v a))
        (actualPrimeCellSet L (u b) (v b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro p hpa hpb
  have ha := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpa).1
  have hb := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpb).1
  rcases lt_or_gt_of_ne hab with hablt|habgt
  · have hv := hsep a b hablt
    have hfloor := Nat.floor_le_floor (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hv hL0))
    omega
  · have hv := hsep b a habgt
    have hfloor := Nat.floor_le_floor (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hv hL0))
    omega

lemma sourceD25_box_true_kernel_upper
    (d k : ℕ) (L b w : ℝ) (u v : Fin k → ℝ)
    (c : Fin d → Fin k)
    (hL : 0<L) (hb : 0<b)
    (hroom : b≤w-∑ i : Fin d,v (c i)) :
    (∑ ps ∈ orderedPrimeBox d k
      (fun j => actualPrimeCellSet L (u j) (v j)) c,
      (w-∑ i : Fin d,primeExponent L (ps i))⁻¹ *
        ∏ i : Fin d,(ps i:ℝ)⁻¹) ≤
      (w-∑ i : Fin d,v (c i))⁻¹ *
        ∏ i : Fin d,reciprocalPrimeCell L (u (c i)) (v (c i)) := by
  have hW : 0<(w-∑ i : Fin d,v (c i)) := hb.trans_le hroom
  calc
    _ ≤ ∑ ps ∈ orderedPrimeBox d k
        (fun j => actualPrimeCellSet L (u j) (v j)) c,
        (w-∑ i : Fin d,v (c i))⁻¹ *
          ∏ i : Fin d,(ps i:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro ps hps
      have hp (i : Fin d) :
          ps i∈actualPrimeCellSet L (u (c i)) (v (c i)) :=
        (Fintype.mem_piFinset.mp hps) i
      have hexp (i : Fin d) :
          primeExponent L (ps i)≤v (c i) :=
        (actualPrimeCellSet_exponent_bounds L (u (c i)) (v (c i))
          hL (ps i) (hp i)).2
      have hsum : (∑ i : Fin d,primeExponent L (ps i))≤
          ∑ i : Fin d,v (c i) := Finset.sum_le_sum (fun i hi => hexp i)
      have hden : 0<w-∑ i : Fin d,primeExponent L (ps i) := by linarith
      have hinv : (w-∑ i : Fin d,primeExponent L (ps i))⁻¹ ≤
          (w-∑ i : Fin d,v (c i))⁻¹ :=
        inv_anti₀ hW (by linarith)
      exact mul_le_mul_of_nonneg_right hinv
        (Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (by
          have hppr := (Finset.mem_filter.mp (hp i)).2
          exact_mod_cast hppr.pos.le)))
    _ = (w-∑ i : Fin d,v (c i))⁻¹ *
        ∏ i : Fin d,(∑ p∈actualPrimeCellSet L (u (c i)) (v (c i)),
          (p:ℝ)⁻¹) := by
      rw [←Finset.mul_sum,orderedPrimeBox_mass]
    _ = _ := by
      apply congrArg (fun z : ℝ => (w-∑ i : Fin d,v (c i))⁻¹*z)
      apply Finset.prod_congr rfl
      intro i hi
      exact actualPrimeCellSet_reciprocal L (u (c i)) (v (c i))

theorem sourceD25_selected_tuple_kernel_upper
    (d k : ℕ) (L b w : ℝ) (u v : Fin k → ℝ)
    (C : Finset (Fin d → Fin k))
    (hL : 0<L) (hb : 0<b)
    (hsep : ∀ i j : Fin k, i<j → v i≤u j)
    (hroom : ∀ c∈C,b≤w-∑ i : Fin d,v (c i)) :
    (∑ ps ∈ orderedPrimeGridTuples d k
      (fun j => actualPrimeCellSet L (u j) (v j)) C,
      (w-∑ i : Fin d,primeExponent L (ps i))⁻¹ *
        ∏ i : Fin d,(ps i:ℝ)⁻¹) ≤
      sourceD25UpperArithmeticGrid d k L w u v C := by
  have hdisj : ∀ c∈C,∀ c'∈C,c≠c' →
      Disjoint
        (orderedPrimeBox d k (fun j => actualPrimeCellSet L (u j) (v j)) c)
        (orderedPrimeBox d k (fun j => actualPrimeCellSet L (u j) (v j)) c') := by
    intro c hc c' hc' hne
    exact orderedPrimeBox_disjoint d k
      (fun j => actualPrimeCellSet L (u j) (v j))
      (sourceD25_actual_prime_cells_disjoint L k u v hL.le hsep) c c' hne
  unfold orderedPrimeGridTuples sourceD25UpperArithmeticGrid
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum
  intro c hc
  exact sourceD25_box_true_kernel_upper d k L b w u v c hL hb (hroom c hc)

/-- Selected interior D24 prefix mass is bounded by the literal source
simplex integral with only explicit mesh error and arbitrary PNT error. -/
theorem sourceD25_selected_prefix_to_simplex
    (d k : ℕ) (S γ b M w η ε : ℝ) (u v : Fin k → ℝ)
    (C : Finset (Fin d → Fin k))
    (hS : 0<S) (hγ : 0<γ)
    (hb : 0<b) (hbM : b≤M) (hη : 0≤η) (hε : 0<ε)
    (hcells : ∀ j,b≤u j ∧ u j≤v j ∧ v j≤M)
    (hwidth : ∀ j,v j-u j≤η)
    (hsep : ∀ i j : Fin k,i<j → v i≤u j)
    (hroom : ∀ c∈C,b≤w-∑ i : Fin d,v (c i)) :
    ∀ᶠ L : ℝ in atTop,
      L*(∑ pre∈sourceGridPrefixLists d k L u v C,
        sourceD24PrefixKernel (Real.exp (w*L)) (L^(-S))
          ((Real.exp L)^γ) pre) ≤
        (∫ t in sourceRegion d b w,sourceKernel d w t) +
        ((d:ℝ)*η/b^2)*
          (∫ t in sourceRegion d b w,reciprocalProduct d t) + ε := by
  have _ := hS
  have _ := hγ
  filter_upwards [sourceD25_actual_upper_corner_grid d k b M w η ε u v C
    hb hbM hη hε hcells hwidth hsep hroom,
    eventually_gt_atTop (0:ℝ)] with L hgrid hL
  exact (sourceD25_selected_prefix_kernel_upper d k S γ L w b u v C
    hL hb hroom).trans
      ((sourceD25_selected_tuple_kernel_upper d k L b w u v C
        hL hb hsep hroom).trans hgrid)


end Green64Analytic.SourceBlockSieve

end

