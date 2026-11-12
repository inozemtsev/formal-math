module

public import Green64.Library.Sieve.Foundation.Lemma6.Part005
public import Green64.Library.ChenTheorem.Lemma6.SmoothingMellin
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Green64.Library.ChenTheorem.Lemma6.StripGrowth

@[expose] public section

/-!
# Sieve / Foundation / Lemma6 / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma6.Integration -/

section

/-
The scalar `ν`-integral common to equations (19) and (20) in Chen's proof.

After the derivative fourth moment is inserted into the `2,4,4` Hölder
bound, both estimates contain

  `(1 + ν²)^(1/4) / (1 + ν⁴)`.

The paper only needs that its integral over `(0, ∞)` is an absolute
constant.  We dominate it by the standard Cauchy kernel.
-/

open Real MeasureTheory Set

namespace Chen

/-- The fourth power of Chen's smoothing scale is bounded by the fifth
integer power of `log x`. -/
theorem lemma6SmoothingScale_four_le_log_five
    {x : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    lemma6SmoothingScale (x : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ 5 := by
  let L : ℝ := Real.log (x : ℝ)
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hL1 : 1 ≤ L := by exact hxlog
  calc
    lemma6SmoothingScale (x : ℝ) ^ 4 =
        (L ^ (1.1 : ℝ)) ^ (4 : ℝ) := by
      unfold lemma6SmoothingScale
      dsimp only [L]
      exact (Real.rpow_natCast _ 4).symm
    _ = L ^ ((1.1 : ℝ) * 4) :=
      (Real.rpow_mul hL0 (1.1 : ℝ) 4).symm
    _ ≤ L ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    _ = Real.log (x : ℝ) ^ 5 := by
      dsimp only [L]
      exact Real.rpow_natCast _ 5

/-- Chen's exact smoothing kernel retains a quartic tail after the contour
is moved to `beta`; the factor `2` bounds the reciprocal real part. -/
theorem norm_lemma6SmoothingMellinKernel_beta_le_two_mul_scale_four
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x nu)‖ ≤
      2 * lemma6SmoothingScale (x : ℝ) ^ 4 / (1 + nu ^ 4) := by
  let L : ℝ := Real.log (x : ℝ)
  let a : ℝ := lemma6SmoothingScale (x : ℝ)
  let sigma : ℝ := 1 / 2 + 1 / L
  have hL : 0 < L := by dsimp only [L]; linarith
  have ha : 0 < a := by
    dsimp only [a, lemma6SmoothingScale]
    exact Real.rpow_pos_of_pos hL _
  have ha1 : 1 ≤ a := by
    dsimp only [a, lemma6SmoothingScale, L]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  have hsigma : 0 < sigma := by dsimp only [sigma]; positivity
  have hpoint : lemma6BetaPoint x nu =
      (sigma : ℂ) + (nu : ℂ) * Complex.I := by
    unfold lemma6BetaPoint
    dsimp only [sigma, L]
  have hk := norm_lemma6SmoothingMellinKernel_le_quartic
    ha hn hsigma nu
  rw [← hpoint] at hk
  apply hk.trans
  have hsigmaHalf : (1 / 2 : ℝ) ≤ sigma := by
    dsimp only [sigma]
    have : 0 ≤ (1 : ℝ) / L := by positivity
    linarith
  have hsigmaInv : sigma⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hsigma (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact hsigmaHalf
  have hdenpos : 0 < (1 + (nu / a) ^ 2) ^ 2 := by positivity
  have htargetpos : 0 < 1 + nu ^ 4 := by positivity
  have hscale :
      ((1 + (nu / a) ^ 2) ^ 2)⁻¹ ≤
        a ^ 4 / (1 + nu ^ 4) := by
    rw [le_div_iff₀ htargetpos]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hdenpos).2
    field_simp [ha.ne']
    nlinarith [sq_nonneg nu, sq_nonneg (nu ^ 2),
      sq_nonneg (a ^ 2 - 1)]
  calc
    sigma⁻¹ * ((1 + (nu / a) ^ 2) ^ 2)⁻¹ ≤
        2 * ((1 + (nu / a) ^ 2) ^ 2)⁻¹ := by gcongr
    _ ≤ 2 * (a ^ 4 / (1 + nu ^ 4)) := by gcongr
    _ = 2 * a ^ 4 / (1 + nu ^ 4) := by ring

/-- Integer-log form of the shifted-line kernel bound. -/
theorem norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x nu)‖ ≤
      2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4) := by
  exact
    (norm_lemma6SmoothingMellinKernel_beta_le_two_mul_scale_four hxlog nu).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (lemma6SmoothingScale_four_le_log_five (by linarith)) (by positivity))
        (by positivity))

/-- The scalar kernel left in the `B` integrals of equations (19) and (20). -/
noncomputable def lemma6BKernel (ν : ℝ) : ℝ :=
  (1 + ν ^ 2) ^ ((1 : ℝ) / 4) / (1 + ν ^ 4)

theorem lemma6BKernel_nonneg (ν : ℝ) : 0 ≤ lemma6BKernel ν := by
  unfold lemma6BKernel
  positivity

theorem continuous_lemma6BKernel : Continuous lemma6BKernel := by
  unfold lemma6BKernel
  exact
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)).comp
        (continuous_const.add (continuous_id.pow 2))).div
      (continuous_const.add (continuous_id.pow 4)) (fun ν => by positivity)

/-- The elementary pointwise comparison used to integrate the kernel:
`(1+ν²)^(1/4)/(1+ν⁴) ≤ 2/(1+ν²)`.
-/
theorem lemma6BKernel_le_cauchy (ν : ℝ) :
    lemma6BKernel ν ≤ 2 * (1 + ν ^ 2)⁻¹ := by
  have hbase : (1 : ℝ) ≤ 1 + ν ^ 2 := by
    nlinarith [sq_nonneg ν]
  have hrpow :
      (1 + ν ^ 2) ^ ((1 : ℝ) / 4) ≤ 1 + ν ^ 2 :=
    Real.rpow_le_self_of_one_le hbase (by norm_num)
  have hden : (0 : ℝ) < 1 + ν ^ 4 := by positivity
  calc
    lemma6BKernel ν ≤ (1 + ν ^ 2) / (1 + ν ^ 4) := by
      exact div_le_div_of_nonneg_right hrpow hden.le
    _ ≤ 2 * (1 + ν ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 1 + ν ^ 2)).2
      nlinarith [sq_nonneg (ν ^ 2 - 1)]

/-- For `log x ≥ 2`, the real part of Chen's `β`-line lies in `[0,1]`, so
its complex norm has the expected scalar bound. -/
theorem lemma6BetaPoint_norm_sq_le
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6BetaPoint x ν‖ ^ 2 ≤ 1 + ν ^ 2 := by
  have hlog : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hxlog
  have hinv : (1 : ℝ) / Real.log x ≤ 1 / 2 := by
    rw [div_le_iff₀ hlog]
    nlinarith
  have hre0 : 0 ≤ (lemma6BetaPoint x ν).re := by
    rw [lemma6BetaPoint_re]
    positivity
  have hre1 : (lemma6BetaPoint x ν).re ≤ 1 := by
    rw [lemma6BetaPoint_re]
    linarith
  rw [Complex.sq_norm, Complex.normSq_apply, lemma6BetaPoint_im]
  nlinarith

/-- The square root of the norm factor supplied by Lemma 3 is exactly
dominated by the numerator of `lemma6BKernel`. -/
theorem lemma6BetaPoint_norm_rpow_half_le
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6BetaPoint x ν‖ ^ ((1 : ℝ) / 2) ≤
      (1 + ν ^ 2) ^ ((1 : ℝ) / 4) := by
  have hsquare := lemma6BetaPoint_norm_sq_le hxlog ν
  have hrpow := Real.rpow_le_rpow (sq_nonneg ‖lemma6BetaPoint x ν‖)
    hsquare (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
  calc
    ‖lemma6BetaPoint x ν‖ ^ ((1 : ℝ) / 2) =
        ‖lemma6BetaPoint x ν‖ ^ ((2 : ℝ) * ((1 : ℝ) / 4)) := by
      congr 1
      ring
    _ = (‖lemma6BetaPoint x ν‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_mul (norm_nonneg _) _ _
    _ = (‖lemma6BetaPoint x ν‖ ^ 2) ^ ((1 : ℝ) / 4) := by
      rw [Real.rpow_two]
    _ ≤ (1 + ν ^ 2) ^ ((1 : ℝ) / 4) := hrpow

theorem lemma6BetaPoint_norm_kernel_le
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6BetaPoint x ν‖ ^ ((1 : ℝ) / 2) / (1 + ν ^ 4) ≤
      lemma6BKernel ν := by
  unfold lemma6BKernel
  exact div_le_div_of_nonneg_right
    (lemma6BetaPoint_norm_rpow_half_le hxlog ν) (by positivity)

/-- The actual scalar kernel produced by taking the fourth root of the
Lemma-3 derivative moment. -/
noncomputable def lemma6DerivativeKernel (x : ℕ) (ν : ℝ) : ℝ :=
  ‖lemma6BetaPoint x ν‖ ^ ((1 : ℝ) / 2) / (1 + ν ^ 4)

theorem continuous_lemma6DerivativeKernel (x : ℕ) :
    Continuous (lemma6DerivativeKernel x) := by
  have hbeta : Continuous (fun ν : ℝ => lemma6BetaPoint x ν) := by
    unfold lemma6BetaPoint
    fun_prop
  unfold lemma6DerivativeKernel
  exact
    ((continuous_norm.comp hbeta).rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2))).div
        (continuous_const.add (continuous_id.pow 4)) (fun ν => by positivity)

theorem lemma6DerivativeKernel_nonneg (x : ℕ) (ν : ℝ) :
    0 ≤ lemma6DerivativeKernel x ν := by
  unfold lemma6DerivativeKernel
  positivity

theorem integrable_lemma6BKernel : Integrable lemma6BKernel := by
  apply (Integrable.const_mul integrable_inv_one_add_sq 2).mono_nonneg
      continuous_lemma6BKernel.aestronglyMeasurable
  · exact ae_of_all _ lemma6BKernel_nonneg
  · exact ae_of_all _ lemma6BKernel_le_cauchy

theorem integrable_lemma6DerivativeKernel
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) :
    Integrable (lemma6DerivativeKernel x) := by
  apply integrable_lemma6BKernel.mono_nonneg
      (continuous_lemma6DerivativeKernel x).aestronglyMeasurable
  · exact ae_of_all _ (lemma6DerivativeKernel_nonneg x)
  · exact ae_of_all _ (lemma6BetaPoint_norm_kernel_le hxlog)

/-- The precise absolute constant needed after equations (19) and (20).
The paper only records convergence; the convenient bound `π` is enough. -/
theorem integral_Ioi_lemma6BKernel_le_pi :
    ∫ ν in Ioi (0 : ℝ), lemma6BKernel ν ≤ Real.pi := by
  calc
    ∫ ν in Ioi (0 : ℝ), lemma6BKernel ν ≤
        ∫ ν in Ioi (0 : ℝ), 2 * (1 + ν ^ 2)⁻¹ := by
      exact setIntegral_mono
        integrable_lemma6BKernel.integrableOn
        (Integrable.const_mul integrable_inv_one_add_sq 2).integrableOn
        lemma6BKernel_le_cauchy
    _ = Real.pi := by
      rw [MeasureTheory.integral_const_mul, integral_Ioi_inv_one_add_sq]
      rw [Real.arctan_zero]
      ring

theorem integral_Ioi_lemma6DerivativeKernel_le_pi
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) :
    ∫ ν in Ioi (0 : ℝ), lemma6DerivativeKernel x ν ≤ Real.pi := by
  exact (setIntegral_mono
      (integrable_lemma6DerivativeKernel hxlog).integrableOn
      integrable_lemma6BKernel.integrableOn
      (lemma6BetaPoint_norm_kernel_le hxlog)).trans
    integral_Ioi_lemma6BKernel_le_pi

/-- The shifted `B` block is nonnegative. -/
theorem lemma6BBlockAtBeta_nonneg
    (x m l k H : ℕ) (nu : ℝ) :
    0 ≤ lemma6BBlockAtBeta x m l k H nu := by
  unfold lemma6BBlockAtBeta
  apply Finset.sum_nonneg
  intro d hd
  apply mul_nonneg (lemma6LinearWeight_nonneg d)
  unfold lemma6BModulusTotal
  split_ifs
  · exact le_rfl
  · unfold lemma6BModulus primSum
    exact tsum_nonneg fun chi => by
      split_ifs
      · positivity
      · exact le_rfl

/-- On a genuine dyadic modulus block the shifted `B` block is continuous
in the height.  Only primitive characters survive, and their `L'` is
entire. -/
theorem continuous_lemma6BBlockAtBeta
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (m k H : ℕ) :
    Continuous (lemma6BBlockAtBeta x m l k H) := by
  let beta : ℝ → ℂ := fun nu => lemma6BetaPoint x nu
  have hbeta : Continuous beta := by
    dsimp only [beta]
    unfold lemma6BetaPoint
    fun_prop
  have heq : lemma6BBlockAtBeta x m l k H = fun nu =>
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (beta nu) i *
          lemma6MollifierNorm H (beta nu) i *
          lemma6LDerivNorm (beta nu) i := by
    funext nu
    simpa only [beta] using
      lemma6BBlockAtBeta_eq_characterBlock_sum x m l k H nu
  rw [heq]
  apply continuous_finsetSum
  intro i hi
  have hid : i.1 ∈ lemma6ModulusBlock x l := by
    rw [lemma6CharacterBlock, Finset.mem_sigma] at hi
    exact hi.1
  have hd2 : 2 ≤ i.1 :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hid)).1
  have hd0 : i.1 ≠ 0 := by omega
  by_cases hp : i.2.IsPrimitive
  · have hpair : Continuous (fun nu =>
        lemma6PairBlockNorm x m k (beta nu) i) := by
      unfold lemma6PairBlockNorm
      exact ((differentiable_lemma6PairBlockPolynomial x m k i.2).continuous.comp
        hbeta).norm
    have hmoll : Continuous (fun nu =>
        lemma6MollifierNorm H (beta nu) i) := by
      unfold lemma6MollifierNorm
      exact ((differentiable_lemma6MollifierAt H i.2).continuous.comp hbeta).norm
    have hderiv : Continuous (fun nu =>
        lemma6LDerivNorm (beta nu) i) := by
      letI : NeZero i.1 := ⟨hd0⟩
      simp only [lemma6LDerivNorm, hd0]
      exact ((primitiveCharacter_differentiable_LFunction_deriv hd2 hp).continuous.comp
        hbeta).norm
    exact ((((continuous_const.mul continuous_const).mul hpair).mul hmoll).mul hderiv)
  · have hweight : lemma6PrimitiveBaseWeight i = 0 := by
      simp [lemma6PrimitiveBaseWeight, hp]
    simp only [hweight, zero_mul]
    exact continuous_const

/-- Any standard fourth-moment height bound for the shifted `B` block is
integrable against Chen's exact smoothing kernel.  This is the analytic
reason the factor `(1+nu^2)^(3/4)` arising from the corrected Lemma 3 is
still harmless. -/
theorem integrable_kernelNorm_mul_lemma6BBlockAtBeta_of_le
    {x l : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ))
    (m k H : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ nu : ℝ,
      lemma6BBlockAtBeta x m l k H nu ≤
        C * (1 + nu ^ 2) ^ ((3 : ℝ) / 4)) :
    Integrable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu) := by
  let A : ℝ := 4 * Real.log (x : ℝ) ^ 5 * C
  have hmajor : Integrable (fun nu : ℝ => A * (1 + nu ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul A
  have hkernel : AEStronglyMeasurable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x nu)‖) := by
    have hlog : 0 < Real.log (x : ℝ) := by linarith
    have ha : 0 < lemma6SmoothingScale (x : ℝ) := by
      unfold lemma6SmoothingScale
      exact Real.rpow_pos_of_pos hlog _
    have hn : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
      unfold lemma6SmoothingOrder
      rw [Nat.one_le_floor_iff]
      linarith
    have hsigma : 0 < (1 / 2 + 1 / Real.log (x : ℝ) : ℝ) := by
      positivity
    have hk := verticalIntegrable_lemma6SmoothingMellinKernel ha hn hsigma
    rw [Complex.VerticalIntegrable] at hk
    have hpoint (nu : ℝ) :
        lemma6BetaPoint x nu =
          ((1 / 2 + 1 / Real.log (x : ℝ) : ℝ) : ℂ) +
            (nu : ℂ) * Complex.I := by
      unfold lemma6BetaPoint
      rfl
    simpa only [hpoint] using hk.norm.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu) :=
    hkernel.mul
      (continuous_lemma6BBlockAtBeta (by linarith) m k H).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards with nu
  have hk := norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five
    hxlog nu
  have hb := hbound nu
  have hB0 := lemma6BBlockAtBeta_nonneg x m l k H nu
  have hbase : (1 : ℝ) ≤ 1 + nu ^ 2 := by nlinarith [sq_nonneg nu]
  have hrpow : (1 + nu ^ 2) ^ ((3 : ℝ) / 4) ≤ 1 + nu ^ 2 :=
    Real.rpow_le_self_of_one_le hbase (by norm_num)
  have hden : (0 : ℝ) < 1 + nu ^ 4 := by positivity
  have hratio : (1 + nu ^ 2) / (1 + nu ^ 4) ≤
      2 * (1 + nu ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 1 + nu ^ 2)).2
    nlinarith [sq_nonneg (nu ^ 2 - 1)]
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hB0)]
  calc
    ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu ≤
      (2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4)) *
        (C * (1 + nu ^ 2) ^ ((3 : ℝ) / 4)) :=
      mul_le_mul hk hb hB0 (by positivity)
    _ ≤ (2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4)) *
        (C * (1 + nu ^ 2)) := by gcongr
    _ = (2 * Real.log (x : ℝ) ^ 5 * C) *
        ((1 + nu ^ 2) / (1 + nu ^ 4)) := by ring
    _ ≤ (2 * Real.log (x : ℝ) ^ 5 * C) *
        (2 * (1 + nu ^ 2)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = A * (1 + nu ^ 2)⁻¹ := by
      unfold A
      ring

end Chen

end

/-! ## ChenTheorem.Lemma6.Parameters -/

section

/-
Parameter choices in equations (19) and (20) of Chen's proof.

We keep the paper's real scales separate from their natural-number cutoffs.
The lemmas below show that `floor` and `ceil` change these scales by at most
an absolute factor once the corresponding block is occupied.  This is the
bookkeeping needed before simplifying the moment majorants.
-/

open Real Filter
open scoped Classical ArithmeticFunction.Moebius

namespace Chen

/-- Every fixed natural power of `log x` is eventually absorbed by an
arbitrarily small positive power of `x`.  Keeping the logarithmic exponent
as a parameter avoids duplicating the same asymptotic argument for the
`100`, `200`, and `400` occurring in equations (19) and (20). -/
theorem eventually_log_pow_nat_le_rpow
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (x : ℝ)) ^ N ≤ (x : ℝ) ^ δ := by
  have hreal :
      ∀ᶠ y : ℝ in atTop,
        ‖Real.log y ^ (N : ℝ)‖ ≤ ‖y ^ δ‖ :=
    (isLittleO_log_rpow_rpow_atTop (N : ℝ) hδ).eventuallyLE
  have hnat :
      ∀ᶠ x : ℕ in atTop,
        ‖Real.log (x : ℝ) ^ (N : ℝ)‖ ≤
          ‖(x : ℝ) ^ δ‖ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_gt_atTop 1] with x hx hx1
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx1)
  simpa [Real.rpow_natCast, norm_eq_abs, abs_of_nonneg hlogpos.le,
    abs_of_nonneg (Real.rpow_nonneg hxpos.le δ)] using hx

/-- Chen's choice `H = D (log x)^100 I_{l,x}` in equation (19). -/
noncomputable def lemma6Equation19HScale (x l : ℕ) : ℝ :=
  lemma6DyadicModulusScale x l * (Real.log x) ^ 100 *
    lemma6ExceptionalFactorAt x l

/-- Natural cutoff corresponding to the real parameter in equation (19). -/
noncomputable def lemma6Equation19HCutoff (x l : ℕ) : ℕ :=
  ⌈lemma6Equation19HScale x l⌉₊

/-- The first entry in Chen's maximum defining `H` in equation (20),
written invariantly as `D² Y⁻¹ (log x)^200 I_{l,x}`. -/
noncomputable def lemma6Equation20HFirstScale (x l k : ℕ) : ℝ :=
  lemma6DyadicModulusScale x l ^ 2 /
      lemma6PairDyadicScale x k *
    (Real.log x) ^ 200 * lemma6ExceptionalFactorAt x l

/-- Chen's real `H` parameter in equation (20). -/
noncomputable def lemma6Equation20HScale
    (x l k : ℕ) (ε : ℝ) : ℝ :=
  max (lemma6Equation20HFirstScale x l k)
    ((x : ℝ) ^ ((1 : ℝ) / 2 - ε))

/-- Natural cutoff corresponding to the real parameter in equation (20). -/
noncomputable def lemma6Equation20HCutoff
    (x l k : ℕ) (ε : ℝ) : ℕ :=
  ⌈lemma6Equation20HScale x l k ε⌉₊

/-! ### Connecting equation (14) to the `A` moment in equation (19) -/

/-- The `1-LS` second moment on the dependent character block is bounded
by the exact dyadic expression occurring on the left of equation (14).

This is the missing bookkeeping connection between the Cauchy--Schwarz
`A` term and the independently proved mollified-remainder estimate.  The
squarefree base weight `|μ(d)|/d` is first enlarged to `1/φ(d)`, and the
actual modulus block is then enlarged to its integer dyadic interval. -/
theorem lemma6_remainderSecond_characterBlock_le_inv_totient
    {x l H : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6RemainderNorm H s i ^ 2) ≤
      ∑ d ∈ Finset.Ioc (lemma6ModulusLowerCutoff x l)
          (lemma6ModulusCutoff x l),
        (Nat.totient d : ℝ)⁻¹ * lemma6Equation14LeftTerm H d s := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  calc
    (∑ d ∈ lemma6ModulusBlock x l,
        ∑ χ : DirichletCharacter ℂ d,
          lemma6PrimitiveBaseWeight ⟨d, χ⟩ *
            lemma6RemainderNorm H s ⟨d, χ⟩ ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6Equation14LeftTerm H d s := by
      apply Finset.sum_le_sum
      intro d hd
      have hd2 : 2 ≤ d :=
        (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
      have hd0 : d ≠ 0 := by omega
      rw [lemma6Equation14LeftTerm_eq hd0]
      simp only [lemma6PrimitiveBaseWeight, lemma6RemainderNorm, hd0,
        ↓reduceDIte]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true]
        rw [mul_one]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        calc
          |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
              1 / (d : ℝ) := by
            apply div_le_div_of_nonneg_right
            · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            · positivity
          _ ≤ (Nat.totient d : ℝ)⁻¹ := by
            simpa only [one_div] using
              (one_div_le_one_div_of_le
                (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
                  (0 : ℝ) < Nat.totient d)
                (by exact_mod_cast Nat.totient_le d :
                  (Nat.totient d : ℝ) ≤ d))
      · simp [hp]
    _ ≤ ∑ d ∈ Finset.Ioc (lemma6ModulusLowerCutoff x l)
          (lemma6ModulusCutoff x l),
        (Nat.totient d : ℝ)⁻¹ * lemma6Equation14LeftTerm H d s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact lemma6ModulusBlock_subset_Ioc_cutoffs
      · intro d hd hnot
        unfold lemma6Equation14LeftTerm
        split_ifs
        · positivity
        · apply mul_nonneg (by positivity)
          apply Finset.sum_nonneg
          intro χ hχ
          split_ifs <;> positivity

/-- The scalar equation-(14) majorant specialized to one modulus block. -/
noncomputable def lemma6RemainderSecondMajorant
    (Cp Ct : ℝ) (x l H : ℕ) (ν : ℝ) : ℝ :=
  2 * (Cp * (Nat.log 2 H + 1) *
      (2 * (lemma6ModulusCutoff x l : ℝ) / H +
        (Nat.log 2 H + 1) *
          (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) *
      (Real.log ((2 * H * H : ℕ) : ℝ)) ^ 3) +
    (lemma6ModulusCutoff x l : ℝ) *
      (2 * ((Ct * ‖lemma6AlphaPoint x ν‖ *
        Real.sqrt (lemma6ModulusCutoff x l) *
        Real.log (2 * lemma6ModulusCutoff x l) / H) ^ 2 *
          (harmonic H : ℝ) ^ 2))

/-- Equation (14), now in the exact weighted character-block form needed
by the `A` part of equation (19). -/
theorem lemma6_remainder_second_moment_characterBlock :
    ∃ Cp Ct : ℝ, 0 < Cp ∧ 0 < Ct ∧
      ∀ (x l H : ℕ) (ν : ℝ),
        1 ≤ Real.log (x : ℝ) → 1 ≤ H →
        (∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6RemainderNorm H (lemma6AlphaPoint x ν) i ^ 2) ≤
          lemma6RemainderSecondMajorant Cp Ct x l H ν := by
  rcases lemma6_equation14 with ⟨Cp, Ct, hCp, hCt, hbound⟩
  refine ⟨Cp, Ct, hCp, hCt, ?_⟩
  intro x l H ν hxlog hH
  have hD : 1 ≤ lemma6ModulusLowerCutoff x l :=
    lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : lemma6ModulusLowerCutoff x l ≤
      lemma6ModulusCutoff x l :=
    lemma6ModulusLowerCutoff_le_cutoff x l
  have hs : 1 < (lemma6AlphaPoint x ν).re := by
    rw [lemma6AlphaPoint_re]
    have hlog : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
    have hinv : 0 < (1 : ℝ) / Real.log (x : ℝ) := one_div_pos.mpr hlog
    linarith
  have h14 := hbound (lemma6ModulusLowerCutoff x l)
    (lemma6ModulusCutoff x l) H (lemma6AlphaPoint x ν)
    hD hDQ hH hs
  exact (lemma6_remainderSecond_characterBlock_le_inv_totient
      hxlog (lemma6AlphaPoint x ν)).trans
    (by simpa only [lemma6RemainderSecondMajorant] using h14)

/-- Equation (19), `A` part, with both of its second moments instantiated:
the pair polynomial is controlled by the character large sieve and the
`1-LS` factor by equation (14). -/
theorem lemma6_equation19_A_with_large_sieve_moments :
    ∃ Cpair CremP CremT : ℝ,
      0 < Cpair ∧ 0 < CremP ∧ 0 < CremT ∧
      ∀ (x l m k H : ℕ) (ν : ℝ),
        Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100 →
        1 ≤ Real.log (x : ℝ) → 1 ≤ H →
        lemma6ABlockAtAlpha x m l k H ν ^ 2 ≤
          (lemma6ExceptionalFactorAt x l *
            (Cpair * lemma6PairSecondMajorant x l m k
              (lemma6AlphaPoint x ν))) *
            lemma6RemainderSecondMajorant CremP CremT x l H ν := by
  rcases lemma6_pair_second_moment_characterBlock with
    ⟨Cpair, hCpair, hpair⟩
  rcases lemma6_remainder_second_moment_characterBlock with
    ⟨CremP, CremT, hCremP, hCremT, hrem⟩
  refine ⟨Cpair, CremP, CremT, hCpair, hCremP, hCremT, ?_⟩
  intro x l m k H ν hxlarge hxlog hH
  rw [lemma6ABlockAtAlpha_eq_characterBlock_sum]
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i *
          lemma6RemainderNorm H (lemma6AlphaPoint x ν) i) ^ 2 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i ^ 2) *
        ∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6RemainderNorm H (lemma6AlphaPoint x ν) i ^ 2 :=
      lemma6_equation19_A_cauchy hxlarge m k H ν
    _ ≤ (lemma6ExceptionalFactorAt x l *
          (Cpair * lemma6PairSecondMajorant x l m k
            (lemma6AlphaPoint x ν))) *
        lemma6RemainderSecondMajorant CremP CremT x l H ν := by
      have hp := hpair x l m k (lemma6AlphaPoint x ν) hxlog
      have hp' :
          (∑ i ∈ lemma6CharacterBlock x l,
              lemma6PrimitiveBaseWeight i *
                lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i ^ 2) ≤
            Cpair * lemma6PairSecondMajorant x l m k
              (lemma6AlphaPoint x ν) := by
        simpa only [lemma6PairSecondMajorant, mul_assoc] using hp
      have hr := hrem x l H ν hxlog hH
      have hE0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
        (lemma6ExceptionalFactor_pos _).le
      have hp0 : 0 ≤
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i ^ 2 := by
        apply Finset.sum_nonneg
        intro i hi
        exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (sq_nonneg _)
      have hr0 : 0 ≤
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6RemainderNorm H (lemma6AlphaPoint x ν) i ^ 2 := by
        apply Finset.sum_nonneg
        intro i hi
        exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (sq_nonneg _)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hp' hE0) hr hr0
        (mul_nonneg hE0 (hp0.trans hp'))

theorem lemma6DyadicModulusScale_nonneg (x l : ℕ) :
    0 ≤ lemma6DyadicModulusScale x l := by
  unfold lemma6DyadicModulusScale
  positivity

theorem lemma6PairDyadicScale_nonneg (x k : ℕ) :
    0 ≤ lemma6PairDyadicScale x k := by
  unfold lemma6PairDyadicScale
  positivity

theorem lemma6PairDyadicScale_pos {x : ℕ} (hx : 1 ≤ x) (k : ℕ) :
    0 < lemma6PairDyadicScale x k := by
  unfold lemma6PairDyadicScale
  positivity

theorem lemma6Equation19HScale_nonneg (x l : ℕ) :
    0 ≤ lemma6Equation19HScale x l := by
  unfold lemma6Equation19HScale
  exact mul_nonneg
    (mul_nonneg (lemma6DyadicModulusScale_nonneg x l) (by positivity))
    (lemma6ExceptionalFactor_pos _).le

theorem lemma6Equation20HFirstScale_nonneg (x l k : ℕ) :
    0 ≤ lemma6Equation20HFirstScale x l k := by
  unfold lemma6Equation20HFirstScale
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (sq_nonneg _) (lemma6PairDyadicScale_nonneg x k))
      (by positivity))
    (lemma6ExceptionalFactor_pos _).le

theorem lemma6Equation20HScale_nonneg
    (x l k : ℕ) (ε : ℝ) :
    0 ≤ lemma6Equation20HScale x l k ε := by
  unfold lemma6Equation20HScale
  exact le_max_of_le_left (lemma6Equation20HFirstScale_nonneg x l k)

/-- The upper modulus cutoff differs from the paper's real endpoint by
less than one. -/
theorem lemma6ModulusCutoff_cast_lt_scale_add_one (x l : ℕ) :
    (lemma6ModulusCutoff x l : ℝ) <
      lemma6DyadicModulusScale x l + 1 := by
  unfold lemma6ModulusCutoff lemma6DyadicModulusScale
  exact Nat.ceil_lt_add_one (by positivity)

theorem lemma6DyadicModulusScale_le_modulusCutoff (x l : ℕ) :
    lemma6DyadicModulusScale x l ≤
      (lemma6ModulusCutoff x l : ℝ) := by
  unfold lemma6ModulusCutoff lemma6DyadicModulusScale
  exact Nat.le_ceil _

/-- For positive blocks, the real lower endpoint is exactly `D/2`. -/
theorem lemma6_modulusLowerReal_eq_half_scale
    {x l : ℕ} (hl : 1 ≤ l) :
    (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100 =
      lemma6DyadicModulusScale x l / 2 := by
  unfold lemma6DyadicModulusScale
  have hpow : (2 : ℝ) ^ l = 2 * (2 : ℝ) ^ (l - 1) := by
    calc
      (2 : ℝ) ^ l = 2 ^ ((l - 1) + 1) := by congr 1; omega
      _ = 2 ^ (l - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (l - 1) := by ring
  rw [hpow]
  ring

theorem lemma6_half_scale_sub_one_lt_modulusLowerCutoff
    {x l : ℕ} (hl : 1 ≤ l) :
    lemma6DyadicModulusScale x l / 2 - 1 <
      (lemma6ModulusLowerCutoff x l : ℝ) := by
  unfold lemma6ModulusLowerCutoff
  rw [← lemma6_modulusLowerReal_eq_half_scale hl]
  exact Nat.sub_one_lt_floor _

/-- Once `D ≥ 4`, the floored lower endpoint is still at least `D/4`. -/
theorem lemma6_quarter_scale_le_modulusLowerCutoff
    {x l : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l) :
    lemma6DyadicModulusScale x l / 4 ≤
      (lemma6ModulusLowerCutoff x l : ℝ) := by
  have hfloor :=
    lemma6_half_scale_sub_one_lt_modulusLowerCutoff (x := x) hl
  have : lemma6DyadicModulusScale x l / 4 ≤
      lemma6DyadicModulusScale x l / 2 - 1 := by linarith
  exact this.trans hfloor.le

theorem lemma6ModulusCutoff_cast_le_five_quarters_scale
    {x l : ℕ} (hD : 4 ≤ lemma6DyadicModulusScale x l) :
    (lemma6ModulusCutoff x l : ℝ) ≤
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l := by
  have hceil := lemma6ModulusCutoff_cast_lt_scale_add_one x l
  linarith

/-- The lower pair-product cutoff differs from `Y` by less than one. -/
theorem lemma6_pairScale_sub_one_lt_pairLowerCutoff (x k : ℕ) :
    lemma6PairDyadicScale x k - 1 <
      (lemma6PairLowerCutoff x k : ℝ) := by
  unfold lemma6PairLowerCutoff
  exact Nat.sub_one_lt_floor _

theorem lemma6PairLowerCutoff_le_pairScale (x k : ℕ) :
    (lemma6PairLowerCutoff x k : ℝ) ≤
      lemma6PairDyadicScale x k := by
  unfold lemma6PairLowerCutoff
  exact Nat.floor_le (lemma6PairDyadicScale_nonneg x k)

theorem lemma6_pairScale_eq_half_next (x k : ℕ) :
    lemma6PairDyadicScale x (k + 1) =
      2 * lemma6PairDyadicScale x k := by
  unfold lemma6PairDyadicScale
  rw [pow_succ]
  ring

theorem lemma6PairUpperCutoff_cast_lt_two_mul_scale_add_one
    (x k : ℕ) :
    (lemma6PairUpperCutoff x k : ℝ) <
      2 * lemma6PairDyadicScale x k + 1 := by
  unfold lemma6PairUpperCutoff
  rw [← lemma6_pairScale_eq_half_next]
  exact Nat.ceil_lt_add_one (lemma6PairDyadicScale_nonneg x (k + 1))

theorem lemma6PairUpperCutoff_cast_le_five_halves_scale
    {x k : ℕ} (hY : 2 ≤ lemma6PairDyadicScale x k) :
    (lemma6PairUpperCutoff x k : ℝ) ≤
      (5 / 2 : ℝ) * lemma6PairDyadicScale x k := by
  have hceil :=
    lemma6PairUpperCutoff_cast_lt_two_mul_scale_add_one x k
  linarith

theorem lemma6PairScale_le_pairUpperCutoff (x k : ℕ) :
    lemma6PairDyadicScale x k ≤
      (lemma6PairUpperCutoff x k : ℝ) := by
  calc
    lemma6PairDyadicScale x k ≤
        lemma6PairDyadicScale x (k + 1) := by
      rw [lemma6_pairScale_eq_half_next]
      have hY := lemma6PairDyadicScale_nonneg x k
      linarith
    _ ≤ (lemma6PairUpperCutoff x k : ℝ) := by
      unfold lemma6PairUpperCutoff
      exact Nat.le_ceil _

/-- Uniform replacement of the natural modulus cutoffs by the real scale
`D`.  This single estimate is used in every moment majorant in (19) and
(20). -/
theorem lemma6_modulus_cutoff_add_div_le_scale
    {x l : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l)
    {N : ℝ} (hN : 0 ≤ N) :
    (lemma6ModulusCutoff x l : ℝ) +
        N / (lemma6ModulusLowerCutoff x l : ℝ) ≤
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * N / lemma6DyadicModulusScale x l := by
  let D := lemma6DyadicModulusScale x l
  let R := (lemma6ModulusLowerCutoff x l : ℝ)
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hRlower : D / 4 ≤ R := by
    simpa only [D, R] using
      lemma6_quarter_scale_le_modulusLowerCutoff hl hD
  have hRpos : 0 < R := (div_pos hDpos (by norm_num)).trans_le hRlower
  have hcoef : 0 ≤ 4 * N / D := by positivity
  have heq : (4 * N / D) * (D / 4) = N := by
    field_simp
  have hquot : N / R ≤ 4 * N / D := by
    apply (div_le_iff₀ hRpos).2
    calc
      N = (4 * N / D) * (D / 4) := heq.symm
      _ ≤ (4 * N / D) * R :=
        mul_le_mul_of_nonneg_left hRlower hcoef
  exact add_le_add
    (lemma6ModulusCutoff_cast_le_five_quarters_scale hD) hquot

/-- Pair-second-moment scale in equation (19), with all floor/ceil effects
absorbed into absolute constants. -/
theorem lemma6_pairSecond_cutoff_factor_le
    {x l k : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) :
    (lemma6ModulusCutoff x l : ℝ) +
        ((lemma6PairUpperCutoff x k -
          lemma6PairLowerCutoff x k : ℕ) : ℝ) /
          (lemma6ModulusLowerCutoff x l : ℝ) ≤
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        10 * lemma6PairDyadicScale x k /
          lemma6DyadicModulusScale x l := by
  let N : ℝ := ((lemma6PairUpperCutoff x k -
    lemma6PairLowerCutoff x k : ℕ) : ℝ)
  have hN : 0 ≤ N := by positivity
  have hbase := lemma6_modulus_cutoff_add_div_le_scale hl hD hN
  have hNle : N ≤ (5 / 2 : ℝ) * lemma6PairDyadicScale x k := by
    calc
      N ≤ (lemma6PairUpperCutoff x k : ℝ) := by
        dsimp only [N]
        exact_mod_cast Nat.sub_le _ _
      _ ≤ (5 / 2 : ℝ) * lemma6PairDyadicScale x k :=
        lemma6PairUpperCutoff_cast_le_five_halves_scale hY
  have hDpos : 0 < lemma6DyadicModulusScale x l :=
    lt_of_lt_of_le (by norm_num) hD
  have hquot :
      4 * N / lemma6DyadicModulusScale x l ≤
        10 * lemma6PairDyadicScale x k /
          lemma6DyadicModulusScale x l := by
    apply div_le_div_of_nonneg_right _ hDpos.le
    nlinarith
  exact hbase.trans (add_le_add_right hquot _)

theorem lemma6PairSecondMajorant_beta_le_scales
    {x l m k : ℕ} (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) :
    lemma6PairSecondMajorant x l m k (lemma6BetaPoint x ν) ≤
      ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        10 * lemma6PairDyadicScale x k /
          lemma6DyadicModulusScale x l) *
        (1 + Real.log (lemma6PairUpperCutoff x k)) := by
  have hlog0 :
      0 ≤ 1 + Real.log (lemma6PairUpperCutoff x k : ℕ) := by
    have hU : (1 : ℝ) ≤ lemma6PairUpperCutoff x k := by
      calc
        (1 : ℝ) ≤ lemma6PairDyadicScale x k := by linarith
        _ ≤ (lemma6PairUpperCutoff x k : ℝ) :=
          lemma6PairScale_le_pairUpperCutoff x k
    exact add_nonneg zero_le_one (Real.log_nonneg hU)
  exact (lemma6PairSecondMajorant_beta_le_log x l m k ν hxlog).trans
    (mul_le_mul_of_nonneg_right
      (lemma6_pairSecond_cutoff_factor_le hl hD hY) hlog0)

theorem lemma6MollifierSecondMajorant_le_scales
    {x l H : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l) :
    lemma6MollifierSecondMajorant x l H ≤
      ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * (H : ℝ) / lemma6DyadicModulusScale x l) *
        (1 + Real.log H) := by
  unfold lemma6MollifierSecondMajorant
  have hfactor := lemma6_modulus_cutoff_add_div_le_scale
    hl hD (show (0 : ℝ) ≤ H by positivity)
  have hlog0 : 0 ≤ 1 + Real.log (H : ℕ) := by
    by_cases hH : H = 0
    · subst H
      norm_num
    · exact add_nonneg zero_le_one
        (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hH)))
  exact mul_le_mul_of_nonneg_right hfactor hlog0

theorem lemma6MollifierFourthMajorant_le_scales
    {x l H : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l) :
    lemma6MollifierFourthMajorant x l H ≤
      ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * ((H * H : ℕ) : ℝ) /
          lemma6DyadicModulusScale x l) *
        (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by
  unfold lemma6MollifierFourthMajorant
  exact mul_le_mul_of_nonneg_right
    (lemma6_modulus_cutoff_add_div_le_scale hl hD
      (show (0 : ℝ) ≤ (H * H : ℕ) by positivity))
    (by positivity)

theorem lemma6_pairFourth_cutoff_factor_le
    {x l k : ℕ} (hl : 1 ≤ l)
    (hD : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) :
    (lemma6ModulusCutoff x l : ℝ) +
        (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
          (lemma6ModulusLowerCutoff x l : ℝ) ≤
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        25 * lemma6PairDyadicScale x k ^ 2 /
          lemma6DyadicModulusScale x l := by
  let U : ℝ := lemma6PairUpperCutoff x k
  have hU0 : 0 ≤ U := by positivity
  have hY0 : 0 ≤ lemma6PairDyadicScale x k :=
    lemma6PairDyadicScale_nonneg x k
  have hUsq : U ^ 2 ≤ (25 / 4 : ℝ) *
      lemma6PairDyadicScale x k ^ 2 := by
    have hU := lemma6PairUpperCutoff_cast_le_five_halves_scale hY
    nlinarith [sq_nonneg
      ((5 / 2 : ℝ) * lemma6PairDyadicScale x k - U)]
  have hbase := lemma6_modulus_cutoff_add_div_le_scale hl hD
    (show 0 ≤ U ^ 2 by positivity)
  have hDpos : 0 < lemma6DyadicModulusScale x l :=
    lt_of_lt_of_le (by norm_num) hD
  have hquot :
      4 * U ^ 2 / lemma6DyadicModulusScale x l ≤
        25 * lemma6PairDyadicScale x k ^ 2 /
          lemma6DyadicModulusScale x l := by
    apply div_le_div_of_nonneg_right _ hDpos.le
    nlinarith
  simpa only [U, Nat.cast_pow] using
    hbase.trans (add_le_add_right hquot _)

theorem lemma6PairFourthMajorant_beta_le_scales :
    ∃ C : ℝ, 0 < C ∧ ∀ (x l m k : ℕ) (ν : ℝ),
      3 ≤ Real.log (x : ℝ) → 1 ≤ l →
      4 ≤ lemma6DyadicModulusScale x l →
      2 ≤ lemma6PairDyadicScale x k →
      lemma6PairFourthMajorant x l m k (lemma6BetaPoint x ν) ≤
        C * ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by
  rcases lemma6PairFourthMajorant_beta_le_log_four with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro x l m k ν hxlog hl hD hY
  have hUreal : (2 : ℝ) ≤ lemma6PairUpperCutoff x k := by
    calc
      (2 : ℝ) ≤ lemma6PairDyadicScale x k := hY
      _ ≤ (lemma6PairUpperCutoff x k : ℝ) :=
        lemma6PairScale_le_pairUpperCutoff x k
  have hU : 2 ≤ lemma6PairUpperCutoff x k := by exact_mod_cast hUreal
  have hU2 : 2 ≤ lemma6PairUpperCutoff x k ^ 2 := by nlinarith
  have hfactor := lemma6_pairFourth_cutoff_factor_le hl hD hY
  calc
    lemma6PairFourthMajorant x l m k (lemma6BetaPoint x ν) ≤
        C * ((lemma6ModulusCutoff x l : ℝ) +
          (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
          (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 :=
      hraw x l m k ν hxlog hU2
    _ ≤ C * ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by
      gcongr

theorem lemma6DerivativeFourthMajorant_le_kernel
    {x l : ℕ} (ν : ℝ) (hxlog : 2 ≤ Real.log (x : ℝ)) :
    lemma6DerivativeFourthMajorant x l ν ≤
      (2 : ℝ) ^ l * (Real.log x) ^ 110 * (1 + ν ^ 2) ^ 3 := by
  unfold lemma6DerivativeFourthMajorant
  have h := lemma6BetaPoint_norm_sq_le hxlog ν
  calc
    (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 110 *
        ‖lemma6BetaPoint x ν‖ ^ 2 * (1 + ν ^ 2) ^ 2 ≤
      (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 110 *
        (1 + ν ^ 2) * (1 + ν ^ 2) ^ 2 := by gcongr
    _ = (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 110 *
        (1 + ν ^ 2) ^ 3 := by ring

theorem lemma6_half_pairScale_le_pairLowerCutoff
    {x k : ℕ} (hY : 2 ≤ lemma6PairDyadicScale x k) :
    lemma6PairDyadicScale x k / 2 ≤
      (lemma6PairLowerCutoff x k : ℝ) := by
  have hfloor := lemma6_pairScale_sub_one_lt_pairLowerCutoff x k
  have : lemma6PairDyadicScale x k / 2 ≤
      lemma6PairDyadicScale x k - 1 := by linarith
  exact this.trans hfloor.le

/-- The `α`-line pair coefficient square sum has the dyadic `1/Y`
decay used in equation (19). -/
theorem lemma6_pairCoefficient_sum_sq_alpha_le_two_div_pairScale
    {x m k : ℕ} (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ))
    (hY : 2 ≤ lemma6PairDyadicScale x k) :
    (∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
        (lemma6PairUpperCutoff x k),
      ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k)
        (lemma6AlphaPoint x ν) n‖ ^ 2) ≤
      2 / lemma6PairDyadicScale x k := by
  let M := lemma6PairLowerCutoff x k
  let U := lemma6PairUpperCutoff x k
  let Y := lemma6PairDyadicScale x k
  have hMU : M ≤ U := by
    dsimp only [M, U]
    exact lemma6PairLowerCutoff_le_upperCutoff x k
  have hMlower : Y / 2 ≤ (M : ℝ) := by
    simpa only [M, Y] using lemma6_half_pairScale_le_pairLowerCutoff hY
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hMposR : 0 < (M : ℝ) := (div_pos hYpos (by norm_num)).trans_le hMlower
  have hM0 : M ≠ 0 := by exact_mod_cast hMposR.ne'
  calc
    (∑ n ∈ Finset.Ioc M U,
      ‖lemma6PairCoefficient x (lemma6AdmissiblePairBlock x m k)
        (lemma6AlphaPoint x ν) n‖ ^ 2) ≤
        ∑ n ∈ Finset.Ioc M U, ((n : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_lemma6PairCoefficient_alpha_sq_le_inv_sq
        x m k ν hxlog n
    _ ≤ (M : ℝ)⁻¹ - (U : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub hM0 hMU
    _ ≤ (M : ℝ)⁻¹ := sub_le_self _ (by positivity)
    _ ≤ (Y / 2)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (div_pos hYpos (by norm_num)) hMlower)
    _ = 2 / Y := by field_simp

/-- The sharper `α`-line pair-second majorant used by the `A` term in
equation (19). -/
theorem lemma6PairSecondMajorant_alpha_le_scales
    {x l m k : ℕ} (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) :
    lemma6PairSecondMajorant x l m k (lemma6AlphaPoint x ν) ≤
      ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        10 * lemma6PairDyadicScale x k /
          lemma6DyadicModulusScale x l) *
        (2 / lemma6PairDyadicScale x k) := by
  unfold lemma6PairSecondMajorant
  exact mul_le_mul
    (lemma6_pairSecond_cutoff_factor_le hl hD hY)
    (lemma6_pairCoefficient_sum_sq_alpha_le_two_div_pairScale
      ν hxlog hY)
    (by positivity)
    (by positivity)

theorem lemma6Equation19HScale_le_cutoff (x l : ℕ) :
    lemma6Equation19HScale x l ≤
      (lemma6Equation19HCutoff x l : ℝ) := by
  unfold lemma6Equation19HCutoff
  exact Nat.le_ceil _

theorem lemma6Equation19HCutoff_cast_lt_scale_add_one (x l : ℕ) :
    (lemma6Equation19HCutoff x l : ℝ) <
      lemma6Equation19HScale x l + 1 := by
  unfold lemma6Equation19HCutoff
  exact Nat.ceil_lt_add_one (lemma6Equation19HScale_nonneg x l)

theorem lemma6Equation20HScale_le_cutoff
    (x l k : ℕ) (ε : ℝ) :
    lemma6Equation20HScale x l k ε ≤
      (lemma6Equation20HCutoff x l k ε : ℝ) := by
  unfold lemma6Equation20HCutoff
  exact Nat.le_ceil _

theorem lemma6Equation20HCutoff_cast_lt_scale_add_one
    (x l k : ℕ) (ε : ℝ) :
    (lemma6Equation20HCutoff x l k ε : ℝ) <
      lemma6Equation20HScale x l k ε + 1 := by
  unfold lemma6Equation20HCutoff
  exact Nat.ceil_lt_add_one (lemma6Equation20HScale_nonneg x l k ε)

theorem lemma6Equation20HFirstScale_le_HScale
    (x l k : ℕ) (ε : ℝ) :
    lemma6Equation20HFirstScale x l k ≤
      lemma6Equation20HScale x l k ε := by
  unfold lemma6Equation20HScale
  exact le_max_left _ _

theorem lemma6_threshold_le_Equation20HScale
    (x l k : ℕ) (ε : ℝ) :
    (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤
      lemma6Equation20HScale x l k ε := by
  unfold lemma6Equation20HScale
  exact le_max_right _ _

/-- Algebraic simplification of the first equation-(20) parameter. -/
theorem lemma6Equation20HFirstScale_eq_paper
    {x : ℕ} (hx : 1 ≤ x) (l k : ℕ) (hk : k ≤ 2 * l) :
    lemma6Equation20HFirstScale x l k =
      (2 : ℝ) ^ (2 * l - k) *
        (x : ℝ) ^ (-(13 : ℝ) / 30) *
        (Real.log x) ^ 400 * lemma6ExceptionalFactorAt x l := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have htwoPow : (2 : ℝ) ^ (2 * l) * ((2 : ℝ) ^ k)⁻¹ =
      (2 : ℝ) ^ (2 * l - k) := by
    field_simp
    rw [← pow_add]
    congr 1
    omega
  have hxpow : ((x : ℝ) ^ ((13 : ℝ) / 30))⁻¹ =
      (x : ℝ) ^ (-(13 : ℝ) / 30) := by
    rw [← Real.rpow_neg hxR.le]
    congr 1
    ring
  have hlogpow : (Real.log (x : ℝ) ^ 100) ^ 2 *
      Real.log (x : ℝ) ^ 200 = Real.log (x : ℝ) ^ 400 := by
    ring
  have hpowTwo : ((2 : ℝ) ^ l) ^ 2 = (2 : ℝ) ^ (2 * l) := by
    rw [← pow_mul]
    congr 1
    omega
  unfold lemma6Equation20HFirstScale lemma6DyadicModulusScale
    lemma6PairDyadicScale
  rw [div_eq_mul_inv, mul_inv_rev, mul_pow, hxpow]
  calc
    ((2 : ℝ) ^ l) ^ 2 * (Real.log (x : ℝ) ^ 100) ^ 2 *
          ((x : ℝ) ^ (-(13 : ℝ) / 30) * ((2 : ℝ) ^ k)⁻¹) *
          Real.log (x : ℝ) ^ 200 * lemma6ExceptionalFactorAt x l =
        (((2 : ℝ) ^ l) ^ 2 * ((2 : ℝ) ^ k)⁻¹) *
          (x : ℝ) ^ (-(13 : ℝ) / 30) *
          ((Real.log (x : ℝ) ^ 100) ^ 2 *
            Real.log (x : ℝ) ^ 200) *
          lemma6ExceptionalFactorAt x l := by
      ring
    _ = (2 : ℝ) ^ (2 * l - k) *
          (x : ℝ) ^ (-(13 : ℝ) / 30) *
          (Real.log (x : ℝ)) ^ 400 *
          lemma6ExceptionalFactorAt x l := by
      rw [hpowTwo, htwoPow, hlogpow]

end Chen

end

/-! ## ChenTheorem.Lemma6.ContourShift -/

section

/-
The finite-height contour shift for the `B` term in equation (17).

The infinite vertical-line identity used by Chen has two logically distinct
parts.  This file proves the Cauchy--Goursat identity on every finite
rectangle.  Passing to infinite height additionally requires the two
horizontal edge integrals to vanish; keeping that limit separate prevents
holomorphy alone from being mistaken for a growth estimate.
-/

open Real Set MeasureTheory Filter Topology
open scoped Classical Interval

namespace Chen

/-- On the shifted line `β = 1/2 + 1 / log x`, the horizontal power has
constant modulus `e x^(1/2)`. -/
theorem norm_nat_cpow_lemma6BetaPoint
    {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    ‖(x : ℂ) ^ lemma6BetaPoint x ν‖ =
      Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
  have hxpos : (0 : ℝ) < x := by positivity
  have hxne : (x : ℝ) ≠ 1 := by
    exact_mod_cast (show x ≠ 1 by omega)
  change ‖((x : ℝ) : ℂ) ^ lemma6BetaPoint x ν‖ =
    Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
    lemma6BetaPoint_re, Real.rpow_add hxpos]
  have hinv : (1 : ℝ) / Real.log (x : ℝ) =
      (Real.log (x : ℝ))⁻¹ := one_div _
  rw [hinv, Real.rpow_inv_log hxpos hxne]
  ring

/-- The complex `B` integrand before taking absolute values. -/
noncomputable def lemma6BContourIntegrand
    {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s * lemma6SmoothingMellinKernel (x : ℝ) s) *
      lemma6PairBlockPolynomial x m k s χ *
      deriv (DirichletCharacter.LFunction χ) s *
      lemma6MollifierAt H s χ)

/-- The complex `A` integrand in equation (16), before absolute values are
taken.  It remains on the original `α`-line. -/
noncomputable def lemma6AContourIntegrand
    {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s * lemma6SmoothingMellinKernel (x : ℝ) s) *
      lemma6PairBlockPolynomial x m k s χ *
      (deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) *
      (1 - DirichletCharacter.LFunction χ s *
        lemma6MollifierAt H s χ))

/-- The unsplit logarithmic-derivative integrand which comes directly from
Mellin inversion. -/
noncomputable def lemma6LogDerivContourIntegrand
    {d : ℕ} [NeZero d] (x m k : ℕ)
    (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s * lemma6SmoothingMellinKernel (x : ℝ) s) *
      lemma6PairBlockPolynomial x m k s χ *
      (deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s))

/-- Exact complex-valued equation-(16) split on the `α`-line.  In
particular, the contour move for `B` occurs before applying the triangle
inequality. -/
theorem lemma6LogDerivContourIntegrand_alpha_eq_A_add_B
    {d x : ℕ} [NeZero d] (hx : 2 ≤ x) (m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (ν : ℝ) :
    lemma6LogDerivContourIntegrand x m k χ (lemma6AlphaPoint x ν) =
      lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν) +
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν) := by
  let C : ℂ :=
    ((x : ℂ) ^ lemma6AlphaPoint x ν *
        lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)) *
      lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ
  let U : ℂ :=
    deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
      DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)
  let A : ℂ := U *
    (1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
      lemma6MollifierAt H (lemma6AlphaPoint x ν) χ)
  let B : ℂ :=
    deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) *
      lemma6MollifierAt H (lemma6AlphaPoint x ν) χ
  have h16 : U = A + B := by
    simpa only [U, A, B] using
      lemma6_equation16_at_alpha (q := d) (H := H) hx ν χ
  have hmul : -(C * U) = -(C * (A + B)) :=
    congrArg (fun z : ℂ => -(C * z)) h16
  unfold lemma6LogDerivContourIntegrand lemma6AContourIntegrand
    lemma6BContourIntegrand
  calc
    -(↑x ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (↑x) (lemma6AlphaPoint x ν) *
          lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))) =
        -(C * U) := by rfl
    _ = -(C * (A + B)) := hmul
    _ = -(↑x ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (↑x) (lemma6AlphaPoint x ν) *
              lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
              (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
                DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)) *
              (1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
                lemma6MollifierAt H (lemma6AlphaPoint x ν) χ)) +
          -(↑x ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (↑x) (lemma6AlphaPoint x ν) *
              lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
              deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) *
              lemma6MollifierAt H (lemma6AlphaPoint x ν) χ) := by
      dsimp only [C, U, A, B]
      ring

/-- Pointwise norm majorant for the shifted complex `B` integrand.  This is
the exact product consumed by the pair, mollifier, and `L'` moment bounds. -/
theorem norm_lemma6BContourIntegrand_beta_le
    {d x : ℕ} [NeZero d] (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (ν : ℝ) :
    ‖lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)‖ ≤
      (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
        (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) *
        ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ *
        ‖deriv (DirichletCharacter.LFunction χ)
          (lemma6BetaPoint x ν)‖ *
        ‖lemma6MollifierAt H (lemma6BetaPoint x ν) χ‖ := by
  unfold lemma6BContourIntegrand
  simp only [norm_neg, norm_mul]
  rw [norm_nat_cpow_lemma6BetaPoint hx ν]
  gcongr
  exact norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five hxlog ν

/-- For a primitive character of modulus at least two, the complete `B`
integrand is holomorphic throughout the right half-plane. -/
theorem differentiableOn_lemma6BContourIntegrand
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (m k H : ℕ) {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    DifferentiableOn ℂ (lemma6BContourIntegrand x m k H χ)
      {s : ℂ | 0 < s.re} := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast (show x ≠ 0 by omega)
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  have hxpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero _
  have hk := differentiableOn_lemma6SmoothingMellinKernel
    (x := (x : ℝ)) (by exact_mod_cast (show 1 < x by omega))
  have hp : DifferentiableOn ℂ
      (fun s => lemma6PairBlockPolynomial x m k s χ) {s : ℂ | 0 < s.re} :=
    (differentiable_lemma6PairBlockPolynomial x m k χ).differentiableOn
  have hL : DifferentiableOn ℂ
      (fun s => deriv (DirichletCharacter.LFunction χ) s) {s : ℂ | 0 < s.re} :=
    (primitiveCharacter_differentiable_LFunction_deriv hd hχ).differentiableOn
  have hM : DifferentiableOn ℂ
      (fun s => lemma6MollifierAt H s χ) {s : ℂ | 0 < s.re} :=
    (differentiable_lemma6MollifierAt H χ).differentiableOn
  unfold lemma6BContourIntegrand
  exact ((((hxpow.differentiableOn.mul hk).mul hp).mul hL).mul hM).neg

/-- Cauchy--Goursat on the finite rectangle with vertical sides `β` and
`α` and heights `[-T,T]`.  This is the rigorous finite precursor of the
contour move in equation (17). -/
theorem lemma6BContour_finite_rectangle
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (T : ℝ) :
    let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
    let α : ℝ := 1 + 1 / Real.log (x : ℝ)
    let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
    (∫ σ : ℝ in β..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ σ : ℝ in β..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • (∫ ν : ℝ in (-T)..T,
        F ((α : ℂ) + (ν : ℂ) * Complex.I)) -
      Complex.I • (∫ ν : ℝ in (-T)..T,
        F ((β : ℂ) + (ν : ℂ) * Complex.I)) = 0 := by
  dsimp only
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let z : ℂ := (β : ℂ) + (-T : ℂ) * Complex.I
  let w : ℂ := (α : ℂ) + (T : ℂ) * Complex.I
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  have hlog : 0 < Real.log (x : ℝ) := by linarith
  have hβpos : 0 < β := by
    dsimp only [β]
    positivity
  have hβα : β ≤ α := by
    dsimp only [β, α]
    norm_num
  have hzre : z.re = β := by
    dsimp only [z]
    simp
  have hwre : w.re = α := by
    dsimp only [w]
    simp
  have hzim : z.im = -T := by
    dsimp only [z]
    simp
  have hwim : w.im = T := by
    dsimp only [w]
    simp
  have hdiff : DifferentiableOn ℂ F
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    apply (differentiableOn_lemma6BContourIntegrand hd hx m k H hχ).mono
    intro s hs
    change 0 < s.re
    have hre := hs.1
    rw [hzre, hwre, uIcc_of_le hβα] at hre
    exact hβpos.trans_le hre.1
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  rw [hzre, hwre, hzim, hwim] at hrect
  dsimp only [F] at hrect
  simpa only [β, α, sub_eq_add_neg, Complex.ofReal_neg, neg_mul] using hrect

/-- The precise growth condition omitted when the paper lets the height of
the finite rectangle tend to infinity.  It is intentionally stated for the
two horizontal integrals themselves, rather than being hidden inside the
phrase "move the contour". -/
def Lemma6BHorizontalEdgesVanish
    {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) : Prop :=
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in β..α, F ((σ : ℂ) - (T : ℂ) * Complex.I))
      atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in β..α, F ((σ : ℂ) + (T : ℂ) * Complex.I))
      atTop (𝓝 0)

/-- A pointwise, uniform-in-the-strip sufficient condition for the two
horizontal edges to disappear.  This is the precise form in which a
vertical-growth estimate for `L'` can be combined with decay of the rational
Mellin kernel. -/
def Lemma6BHorizontalPointwiseDecay
    {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) : Prop :=
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
    ∀ T σ : ℝ, σ ∈ Icc β α →
      ‖F ((σ : ℂ) - (T : ℂ) * Complex.I)‖ ≤ g T ∧
      ‖F ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ g T

/-- Uniform pointwise decay across the compact horizontal segment implies
the horizontal-edge limit needed by the contour shift. -/
theorem lemma6BHorizontalEdgesVanish_of_pointwiseDecay
    {d : ℕ} [NeZero d] {x m k H : ℕ}
    {χ : DirichletCharacter ℂ d}
    (hdecay : Lemma6BHorizontalPointwiseDecay x m k H χ) :
    Lemma6BHorizontalEdgesVanish x m k H χ := by
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  rcases hdecay with ⟨g, hg, hbound⟩
  have hβα : β ≤ α := by
    dsimp only [β, α]
    norm_num
  have hwidth : Tendsto (fun T : ℝ => g T * |α - β|)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hg.mul_const |α - β|
  have hbotBound : ∀ T : ℝ,
      ‖∫ σ : ℝ in β..α,
          F ((σ : ℂ) - (T : ℂ) * Complex.I)‖ ≤
        g T * |α - β| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hσ' : σ ∈ Icc β α := by
      rw [← uIcc_of_le hβα]
      exact uIoc_subset_uIcc hσ
    exact (hbound T σ (by simpa only [β, α] using hσ')).1
  have htopBound : ∀ T : ℝ,
      ‖∫ σ : ℝ in β..α,
          F ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        g T * |α - β| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hσ' : σ ∈ Icc β α := by
      rw [← uIcc_of_le hβα]
      exact uIoc_subset_uIcc hσ
    exact (hbound T σ (by simpa only [β, α] using hσ')).2
  have hbot : Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in β..α,
        F ((σ : ℂ) - (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _)
      hbotBound hwidth
  have htop : Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in β..α,
        F ((σ : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _)
      htopBound hwidth
  simpa only [Lemma6BHorizontalEdgesVanish, β, α, F] using And.intro hbot htop

/-- Once the two horizontal edges vanish and both boundary restrictions
are integrable, the finite rectangle identity gives equality of the two
improper vertical integrals. -/
theorem lemma6BContour_verticalIntegral_eq
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (hhor : Lemma6BHorizontalEdgesVanish x m k H χ)
    (hα : Integrable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)))
    (hβ : Integrable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    (∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) =
      ∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν) := by
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  let bot : ℝ → ℂ := fun T =>
    ∫ σ : ℝ in β..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)
  let top : ℝ → ℂ := fun T =>
    ∫ σ : ℝ in β..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)
  let va : ℝ → ℂ := fun T =>
    ∫ ν : ℝ in (-T)..T, F ((α : ℂ) + (ν : ℂ) * Complex.I)
  let vb : ℝ → ℂ := fun T =>
    ∫ ν : ℝ in (-T)..T, F ((β : ℂ) + (ν : ℂ) * Complex.I)
  have hpointα : (fun ν : ℝ => F ((α : ℂ) + (ν : ℂ) * Complex.I)) =
      fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν) := by
    funext ν
    rfl
  have hpointβ : (fun ν : ℝ => F ((β : ℂ) + (ν : ℂ) * Complex.I)) =
      fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν) := by
    funext ν
    rfl
  have hva : Tendsto va atTop
      (𝓝 (∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν))) := by
    have ht := intervalIntegral_tendsto_integral hα
      tendsto_neg_atTop_atBot
      (show Tendsto (fun T : ℝ => T) atTop atTop from tendsto_id)
    simpa only [va, hpointα, id_eq] using ht
  have hvb : Tendsto vb atTop
      (𝓝 (∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) := by
    have ht := intervalIntegral_tendsto_integral hβ
      tendsto_neg_atTop_atBot
      (show Tendsto (fun T : ℝ => T) atTop atTop from tendsto_id)
    simpa only [vb, hpointβ, id_eq] using ht
  have hhor' : Tendsto bot atTop (𝓝 0) ∧ Tendsto top atTop (𝓝 0) := by
    simpa only [Lemma6BHorizontalEdgesVanish, bot, top, F, β, α] using hhor
  have hcalc := (hhor'.1.sub hhor'.2).add
    ((hva.const_smul Complex.I).sub (hvb.const_smul Complex.I))
  have heq : ∀ T : ℝ,
      bot T - top T + (Complex.I • va T - Complex.I • vb T) = 0 := by
    intro T
    simpa only [bot, top, va, vb, F, β, α, sub_eq_add_neg,
      add_assoc] using
      lemma6BContour_finite_rectangle hd hx hxlog m k H hχ T
  have hzero : Tendsto
      (fun T : ℝ => bot T - top T +
        (Complex.I • va T - Complex.I • vb T))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun T => (heq T).symm)
  have hlim :
      (0 : ℂ) - 0 +
        (Complex.I •
            (∫ ν : ℝ,
              lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) -
          Complex.I •
            (∫ ν : ℝ,
              lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) = 0 :=
    tendsto_nhds_unique hcalc hzero
  have hmul : Complex.I *
      ((∫ ν : ℝ,
          lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) -
        ∫ ν : ℝ,
          lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)) = 0 := by
    simpa only [zero_sub, zero_add, neg_zero, smul_eq_mul, mul_sub] using hlim
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left Complex.I_ne_zero)

/-- The contour shift commutes with the finite primitive-character sum and
with Chen's unit-modulus conjugate character factor.  All analytic limit
hypotheses remain explicit character by character. -/
theorem lemma6BContour_primComplexSum_verticalIntegral_eq
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (hhor : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Lemma6BHorizontalEdgesVanish x m k H χ)
    (hα : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)))
    (hβ : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (x : ZMod d)) *
          ∫ ν : ℝ,
            lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) =
      primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (x : ZMod d)) *
          ∫ ν : ℝ,
            lemma6BContourIntegrand x m k H χ
              (lemma6BetaPoint x ν)) := by
  unfold primComplexSum
  apply tsum_congr
  intro χ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    rw [lemma6BContour_verticalIntegral_eq hd hx hxlog m k H hp
      (hhor χ hp) (hα χ hp) (hβ χ hp)]
  · simp [hp]

end Chen

end

/-! ## ChenTheorem.Lemma6.BIntegrability -/

section

/-
Unconditional validity of the contour shift in equation (17) of Lemma 6.

The two analytic limit hypotheses of
`lemma6BContour_primComplexSum_verticalIntegral_eq` — vanishing of the
horizontal rectangle edges and integrability of the `B` integrand on the
shifted line `β = 1/2 + 1/log x` — are discharged here.  Everything reduces
to the polynomial growth of `L'` in the critical strip
(`norm_deriv_LFunction_le_of_mem_strip`, proved in `StripGrowth.lean` via
Pólya–Vinogradov and partial summation) combined with the super-polynomial
decay of Chen's smoothing kernel.
-/

open Real Set MeasureTheory Filter Topology
open scoped Classical

namespace Chen

/-- Pointwise bound for one summand of the pair Dirichlet polynomial,
depending only on `re s`. -/
theorem norm_pairBlock_summand_le {x m k d : ℕ} (χ : DirichletCharacter ℂ d)
    {q : ℕ × ℕ} (hq : q ∈ lemma6AdmissiblePairBlock x m k) (s : ℂ) :
    ‖χ (q.1 * q.2 : ZMod d) /
        (((q.1 * q.2 : ℕ) : ℂ) ^ s *
          (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ ≤
      ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
        |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  obtain ⟨hq1, hq2⟩ := primes_of_mem_lemma6AdmissiblePairBlock hq
  have hqq : 0 < q.1 * q.2 := Nat.mul_pos hq1.pos hq2.pos
  have hqqR : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) := by positivity
  rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hqq,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖χ (q.1 * q.2 : ZMod d)‖ /
          (((q.1 * q.2 : ℕ) : ℝ) ^ s.re *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|) ≤
        1 / (((q.1 * q.2 : ℕ) : ℝ) ^ s.re *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|) :=
      div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one _ _)
        (by positivity)
    _ = ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
      rw [div_eq_mul_inv, one_mul, mul_inv, ← Real.rpow_neg hqqR.le]

/-- The pair Dirichlet polynomial is bounded by a real sum depending only
on `re s`. -/
theorem norm_lemma6PairBlockPolynomial_le_rpow_sum {x m k d : ℕ}
    (χ : DirichletCharacter ℂ d) (s : ℂ) :
    ‖lemma6PairBlockPolynomial x m k s χ‖ ≤
      ∑ q ∈ lemma6AdmissiblePairBlock x m k,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  unfold lemma6PairBlockPolynomial lemma6PairDirichletPolynomial
  calc
    ‖∑ q ∈ lemma6AdmissiblePairBlock x m k,
          χ (q.1 * q.2 : ZMod d) /
            (((q.1 * q.2 : ℕ) : ℂ) ^ s *
              (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ ≤
        ∑ q ∈ lemma6AdmissiblePairBlock x m k,
          ‖χ (q.1 * q.2 : ZMod d) /
            (((q.1 * q.2 : ℕ) : ℂ) ^ s *
              (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ lemma6AdmissiblePairBlock x m k,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      exact norm_pairBlock_summand_le χ hq s

/-- The real pair-polynomial majorant is antitone in the real part. -/
theorem pairBlock_rpow_sum_antitone {x m k : ℕ} {σ₀ σ₁ : ℝ} (h : σ₀ ≤ σ₁) :
    (∑ q ∈ lemma6AdmissiblePairBlock x m k,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-σ₁) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) ≤
      ∑ q ∈ lemma6AdmissiblePairBlock x m k,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-σ₀) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hq1, hq2⟩ := primes_of_mem_lemma6AdmissiblePairBlock hq
  have hqq : (1 : ℝ) ≤ ((q.1 * q.2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_pos hq1.pos hq2.pos).ne'
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hqq (by linarith)) (by positivity)

/-- On any vertical line with nonnegative real part, the truncated Möbius
mollifier is bounded by its length. -/
theorem norm_lemma6MollifierAt_le_card {q H : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma6MollifierAt H s χ‖ ≤ (H : ℝ) := by
  unfold lemma6MollifierAt
  calc
    ‖∑ n ∈ Finset.Icc 1 H,
        (ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s‖ ≤
        ∑ n ∈ Finset.Icc 1 H,
          ‖(ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : 0 < n := hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hchi : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have hden : (1 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.one_le_rpow hnR hs
      rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
      calc
        ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖χ (n : ZMod q)‖ /
              (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re := by
          apply div_le_div_of_nonneg_right _
            (Real.rpow_nonneg (by positivity) _)
          nlinarith [norm_nonneg (ArithmeticFunction.moebius n : ℂ),
            norm_nonneg (χ (n : ZMod q))]
        _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos (by positivity) _)]
          exact hden
    _ = (H : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp

/-- The elementary comparison
`(1 + |ν|) / (1 + ν⁴) ≤ 4 / (1 + ν²)`. -/
theorem one_add_abs_div_one_add_pow_four_le (ν : ℝ) :
    (1 + |ν|) / (1 + ν ^ 4) ≤ 4 / (1 + ν ^ 2) := by
  have h1 : (0 : ℝ) < 1 + ν ^ 4 := by positivity
  have h2 : (0 : ℝ) < 1 + ν ^ 2 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  set t : ℝ := |ν| with ht
  have ht0 : (0 : ℝ) ≤ t := abs_nonneg ν
  have hν2 : ν ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  have hν4 : ν ^ 4 = t ^ 4 := by
    have hsq : ν ^ 4 = (ν ^ 2) ^ 2 := by ring
    rw [hsq, hν2]
    ring
  rw [hν2, hν4]
  have key : 1 + t + t ^ 2 + t ^ 3 ≤ 4 * (1 + t ^ 4) := by
    rcases le_or_gt t 1 with h | h
    · have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
      have ht3 : t ^ 3 ≤ 1 := by
        calc t ^ 3 = t * t ^ 2 := by ring
          _ ≤ 1 * 1 := mul_le_mul h ht2 (sq_nonneg t) zero_lt_one.le
          _ = 1 := one_mul 1
      nlinarith [ht2, ht3, ht0, pow_nonneg ht0 4]
    · have h1t : (1 : ℝ) ≤ t := h.le
      have ht3 : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ (by linarith)
      have he1 : t ≤ t ^ 4 := by
        calc t = t * 1 := by ring
          _ ≤ t * t ^ 3 := by gcongr
          _ = t ^ 4 := by ring
      have he2 : t ^ 2 ≤ t ^ 4 := by
        calc t ^ 2 = t ^ 2 * 1 := by ring
          _ ≤ t ^ 2 * t ^ 2 := by gcongr; nlinarith
          _ = t ^ 4 := by ring
      have he3 : t ^ 3 ≤ t ^ 4 := by
        calc t ^ 3 = t ^ 3 * 1 := by ring
          _ ≤ t ^ 3 * t := by gcongr
          _ = t ^ 4 := by ring
      nlinarith [he1, he2, he3, ht0]
  nlinarith [key, sq_nonneg t]

/-- The shifted `B` integrand is integrable on Chen's `β`-line,
unconditionally.  The growth of `L'` in the strip is linear in `‖s‖`
(`norm_deriv_LFunction_le_of_mem_strip`), while the smoothing kernel decays
quarticly. -/
theorem integrable_lemma6BContourIntegrand_beta
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    Integrable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)) := by
  have hLpos : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  set β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ) with hβdef
  have hβge : (1 : ℝ) / 2 ≤ β := by
    rw [hβdef]
    have hnn : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hβle : β ≤ 1 := by
    rw [hβdef]
    have h2 : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set Cpair : ℝ := ∑ q ∈ lemma6AdmissiblePairBlock x m k,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-β) *
      |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ with hCpair
  have hCpair0 : 0 ≤ Cpair := by
    rw [hCpair]
    positivity
  set CL : ℝ := 144 * Real.sqrt d * Real.log (2 * d) with hCL
  have hCL0 : 0 ≤ CL := by
    rw [hCL]
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
    have h2 : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  set K : ℝ := (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
    (2 * Real.log (x : ℝ) ^ 5) * Cpair * CL * (H : ℝ) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  have hpoint : ∀ ν : ℝ,
      ‖lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)‖ ≤
        4 * K * (1 + ν ^ 2)⁻¹ := by
    intro ν
    have hmain := norm_lemma6BContourIntegrand_beta_le hx hxlog m k H χ ν
    have hre : (lemma6BetaPoint x ν).re = β := by
      rw [hβdef]
      exact lemma6BetaPoint_re x ν
    have hpair : ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ ≤
        Cpair := by
      calc
        ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ ≤
            ∑ q ∈ lemma6AdmissiblePairBlock x m k,
              ((q.1 * q.2 : ℕ) : ℝ) ^ (-(lemma6BetaPoint x ν).re) *
                |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ :=
          norm_lemma6PairBlockPolynomial_le_rpow_sum χ _
        _ = Cpair := by
          rw [hCpair, hre]
    have hLbound : ‖deriv (DirichletCharacter.LFunction χ)
        (lemma6BetaPoint x ν)‖ ≤ CL * (1 + |ν|) := by
      have hstrip := norm_deriv_LFunction_le_of_mem_strip hχ hd
        (by linarith : (1 : ℝ) / 2 ≤ (lemma6BetaPoint x ν).re)
        (by linarith : (lemma6BetaPoint x ν).re ≤ 2)
      have hnorm : ‖lemma6BetaPoint x ν‖ ≤ 1 + |ν| := by
        calc
          ‖lemma6BetaPoint x ν‖ ≤ |(lemma6BetaPoint x ν).re| +
              |(lemma6BetaPoint x ν).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = β + |ν| := by
            rw [hre, lemma6BetaPoint_im, abs_of_nonneg (by linarith)]
          _ ≤ 1 + |ν| := by linarith
      calc
        ‖deriv (DirichletCharacter.LFunction χ) (lemma6BetaPoint x ν)‖ ≤
            144 * Real.sqrt d * Real.log (2 * d) *
              ‖lemma6BetaPoint x ν‖ := hstrip
        _ = CL * ‖lemma6BetaPoint x ν‖ := by rw [hCL]
        _ ≤ CL * (1 + |ν|) :=
          mul_le_mul_of_nonneg_left hnorm hCL0
    have hmoll : ‖lemma6MollifierAt H (lemma6BetaPoint x ν) χ‖ ≤ (H : ℝ) :=
      norm_lemma6MollifierAt_le_card χ (by linarith)
    have hbase0 : 0 ≤ (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
        (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) := by positivity
    have e1 : (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) *
          ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ ≤
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * Cpair :=
      mul_le_mul_of_nonneg_left hpair hbase0
    have e2 : (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) *
          ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6BetaPoint x ν)‖ ≤
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * Cpair *
          (CL * (1 + |ν|)) :=
      mul_le_mul e1 hLbound (norm_nonneg _) (mul_nonneg hbase0 hCpair0)
    have e3 : (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) *
          ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6BetaPoint x ν)‖ *
          ‖lemma6MollifierAt H (lemma6BetaPoint x ν) χ‖ ≤
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * Cpair *
          (CL * (1 + |ν|)) * (H : ℝ) :=
      mul_le_mul e2 hmoll (norm_nonneg _)
        (mul_nonneg (mul_nonneg hbase0 hCpair0)
          (mul_nonneg hCL0 (by positivity)))
    have h1 := hmain.trans e3
    have h2 : (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * Cpair *
          (CL * (1 + |ν|)) * (H : ℝ) =
        K * ((1 + |ν|) / (1 + ν ^ 4)) := by
      rw [hK]
      ring
    have h3 : K * ((1 + |ν|) / (1 + ν ^ 4)) ≤ 4 * K * (1 + ν ^ 2)⁻¹ := by
      have hcmp := one_add_abs_div_one_add_pow_four_le ν
      calc
        K * ((1 + |ν|) / (1 + ν ^ 4)) ≤ K * (4 / (1 + ν ^ 2)) :=
          mul_le_mul_of_nonneg_left hcmp hK0
        _ = 4 * K * (1 + ν ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          ring
    exact h1.trans (h2.le.trans h3)
  have hmeas : AEStronglyMeasurable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)) := by
    have hbeta : Continuous (lemma6BetaPoint x) := by
      unfold lemma6BetaPoint
      fun_prop
    have hrange : ∀ ν : ℝ, lemma6BetaPoint x ν ∈
        {s : ℂ | 0 < s.re} := by
      intro ν
      have hre : (lemma6BetaPoint x ν).re = β := by
        rw [hβdef]
        exact lemma6BetaPoint_re x ν
      rw [Set.mem_setOf_eq, hre]
      linarith
    exact ((differentiableOn_lemma6BContourIntegrand hd hx m k H
      hχ).continuousOn.comp_continuous hbeta hrange).aestronglyMeasurable
  apply ((integrable_inv_one_add_sq.const_mul (4 * K))).mono' hmeas
  filter_upwards with ν
  exact hpoint ν

/-- The horizontal edges of the rectangle in equation (17) vanish,
unconditionally, for primitive characters of modulus at least two.  The
pointwise decay combines the linear strip growth of `L'` with the quartic
decay of Chen's smoothing kernel. -/
theorem lemma6BHorizontalEdgesVanish_primitive
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    Lemma6BHorizontalEdgesVanish x m k H χ := by
  apply lemma6BHorizontalEdgesVanish_of_pointwiseDecay
  have hLpos : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  set β₀ : ℝ := 1 / 2 + 1 / Real.log (x : ℝ) with hβ₀
  set α₀ : ℝ := 1 + 1 / Real.log (x : ℝ) with hα₀
  have hα₀le : α₀ ≤ 2 := by
    rw [hα₀]
    have h1 : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 / 1 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 := by
      simpa using h1
    linarith
  have hβ₀ge : (1 : ℝ) / 2 ≤ β₀ := by
    rw [hβ₀]
    have hnn : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  set a : ℝ := lemma6SmoothingScale (x : ℝ) with ha
  have hapos : 0 < a := by
    rw [ha]
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hLpos _
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  set Cpair : ℝ := ∑ q ∈ lemma6AdmissiblePairBlock x m k,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-β₀) *
      |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ with hCpair
  have hCpair0 : 0 ≤ Cpair := by rw [hCpair]; positivity
  set CL : ℝ := 144 * Real.sqrt d * Real.log (2 * d) with hCL
  have hCL0 : 0 ≤ CL := by
    rw [hCL]
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
    have h2 : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  set K₁ : ℝ := Real.exp 1 * (x : ℝ) * 2 * Cpair * CL * (H : ℝ) with hK₁
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  refine ⟨fun T : ℝ => K₁ * (α₀ + |T|) * ((1 + (T / a) ^ 2) ^ 2)⁻¹,
    ?_, ?_⟩
  · -- Tendsto g atTop 0
    have htend : Tendsto (fun T : ℝ => 2 * K₁ * a ^ 4 * (T⁻¹) ^ 3)
        atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero.pow 3).const_mul (2 * K₁ * a ^ 4)
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      htend
    · filter_upwards with T
      positivity
    · filter_upwards [eventually_ge_atTop 2] with T hT
      have hTpos : (0 : ℝ) < T := by linarith
      have habs : |T| = T := abs_of_nonneg hTpos.le
      rw [habs]
      have hstep1 : α₀ + T ≤ 2 * T := by linarith
      have hstep2 : ((1 + (T / a) ^ 2) ^ 2)⁻¹ ≤ a ^ 4 / T ^ 4 := by
        have h1 : (T / a) ^ 2 ≤ 1 + (T / a) ^ 2 := by
          linarith [sq_nonneg (T / a)]
        have h2 : ((T / a) ^ 2) ^ 2 ≤ (1 + (T / a) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg _) h1 2
        have h3 : ((T / a) ^ 2) ^ 2 = T ^ 4 / a ^ 4 := by
          rw [div_pow, div_pow]
          ring
        rw [h3] at h2
        have h4 : (0 : ℝ) < (1 + (T / a) ^ 2) ^ 2 := by positivity
        have h5 : (0 : ℝ) < T ^ 4 / a ^ 4 := by positivity
        calc
          ((1 + (T / a) ^ 2) ^ 2)⁻¹ ≤ (T ^ 4 / a ^ 4)⁻¹ := by
            rw [inv_le_inv₀ h4 h5]
            exact h2
          _ = a ^ 4 / T ^ 4 := inv_div _ _
      calc
        K₁ * (α₀ + T) * ((1 + (T / a) ^ 2) ^ 2)⁻¹ ≤
            K₁ * (2 * T) * (a ^ 4 / T ^ 4) := by
          apply mul_le_mul _ hstep2 (by positivity)
            (mul_nonneg hK₁0 (by linarith))
          exact mul_le_mul_of_nonneg_left hstep1 hK₁0
        _ = 2 * K₁ * a ^ 4 * (T⁻¹) ^ 3 := by
          field_simp [hTpos.ne']
  · -- pointwise bound
    intro T σ hσ
    have hσlo : (1 : ℝ) / 2 ≤ σ := hβ₀ge.trans hσ.1
    have hσhi : σ ≤ 2 := hσ.2.trans hα₀le
    have hσpos : (0 : ℝ) < σ := by linarith
    have hσinv : σ⁻¹ ≤ 2 := by
      have h22 : (2 : ℝ) = (1 / 2)⁻¹ := by norm_num
      rw [h22, inv_le_inv₀ hσpos (by norm_num)]
      linarith
    -- the pointwise bound, uniform in the imaginary displacement `τ`
    have hbound : ∀ τ : ℝ,
        ‖lemma6BContourIntegrand x m k H χ
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          K₁ * (α₀ + |τ|) * ((1 + (τ / a) ^ 2) ^ 2)⁻¹ := by
      intro τ
      have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by
        simp [Complex.add_re, Complex.mul_re]
      have him : ((σ : ℂ) + (τ : ℂ) * Complex.I).im = τ := by
        simp [Complex.add_im, Complex.mul_im]
      have hkernel : ‖lemma6SmoothingMellinKernel (x : ℝ)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹ := by
        have hk := norm_lemma6SmoothingMellinKernel_le_quartic
          (x := (x : ℝ)) hapos hn hσpos τ
        exact hk.trans (mul_le_mul_of_nonneg_right hσinv (by positivity))
      have hxpow : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          Real.exp 1 * (x : ℝ) := by
        have hxpos : (0 : ℝ) < x := by positivity
        have hxne : (x : ℝ) ≠ 1 := by
          exact_mod_cast (show x ≠ 1 by omega)
        change ‖((x : ℝ) : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          Real.exp 1 * (x : ℝ)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hre]
        calc
          (x : ℝ) ^ σ ≤ (x : ℝ) ^ α₀ :=
            Real.rpow_le_rpow_of_exponent_le
              (by exact_mod_cast (show 1 ≤ x by omega)) hσ.2
          _ = Real.exp 1 * (x : ℝ) := by
            rw [hα₀, Real.rpow_add hxpos, Real.rpow_one,
              show (1 : ℝ) / Real.log (x : ℝ) = (Real.log (x : ℝ))⁻¹ from
                one_div _, Real.rpow_inv_log hxpos hxne]
            ring
      have hpair : ‖lemma6PairBlockPolynomial x m k
            ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤ Cpair := by
        calc
          ‖lemma6PairBlockPolynomial x m k
                ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
              ∑ q ∈ lemma6AdmissiblePairBlock x m k,
                ((q.1 * q.2 : ℕ) : ℝ) ^ (-(((σ : ℂ) + (τ : ℂ) * Complex.I).re)) *
                  |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ :=
            norm_lemma6PairBlockPolynomial_le_rpow_sum χ _
          _ ≤ Cpair := by
            rw [hCpair]
            apply pairBlock_rpow_sum_antitone
            rw [hre]
            exact hσ.1
      have hLbound : ‖deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          CL * (α₀ + |τ|) := by
        have hstrip := norm_deriv_LFunction_le_of_mem_strip hχ hd
          (by linarith : (1 : ℝ) / 2 ≤
            ((σ : ℂ) + (τ : ℂ) * Complex.I).re)
          (by linarith : ((σ : ℂ) + (τ : ℂ) * Complex.I).re ≤ 2)
        have hnorm : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤ α₀ + |τ| := by
          calc
            ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤
                |((σ : ℂ) + (τ : ℂ) * Complex.I).re| +
                  |((σ : ℂ) + (τ : ℂ) * Complex.I).im| :=
              Complex.norm_le_abs_re_add_abs_im _
            _ = σ + |τ| := by
              rw [hre, him, abs_of_nonneg hσpos.le]
            _ ≤ α₀ + |τ| := by linarith [hσ.2]
        calc
          ‖deriv (DirichletCharacter.LFunction χ)
                ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
              144 * Real.sqrt d * Real.log (2 * d) *
                ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ := hstrip
          _ = CL * ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ := by rw [hCL]
          _ ≤ CL * (α₀ + |τ|) := mul_le_mul_of_nonneg_left hnorm hCL0
      have hmoll : ‖lemma6MollifierAt H ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
          (H : ℝ) :=
        norm_lemma6MollifierAt_le_card χ (by linarith)
      unfold lemma6BContourIntegrand
      simp only [norm_neg, norm_mul]
      have e1 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) :=
        mul_le_mul hxpow hkernel (norm_nonneg _) (by positivity)
      have e2 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6PairBlockPolynomial x m k
              ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) *
            Cpair :=
        mul_le_mul e1 hpair (norm_nonneg _)
          (mul_nonneg (by positivity) (by positivity))
      have e3 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6PairBlockPolynomial x m k
              ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ *
            ‖deriv (DirichletCharacter.LFunction χ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) *
            Cpair * (CL * (α₀ + |τ|)) :=
        mul_le_mul e2 hLbound (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hCpair0)
      have e4 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6PairBlockPolynomial x m k
              ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ *
            ‖deriv (DirichletCharacter.LFunction χ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6MollifierAt H ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) *
            Cpair * (CL * (α₀ + |τ|)) * (H : ℝ) :=
        mul_le_mul e3 hmoll (norm_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
            (by positivity)) hCpair0)
            (mul_nonneg hCL0 (by positivity)))
      apply e4.trans
      apply le_of_eq
      rw [hK₁]
      ring
    constructor
    · have hrewrite : (σ : ℂ) - (T : ℂ) * Complex.I =
          (σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I := by
        rw [Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
      rw [hrewrite]
      have h := hbound (-T)
      rwa [abs_neg, neg_div, neg_sq] at h
    · exact hbound T

end Chen

end

